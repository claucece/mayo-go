package main

import (
	"crypto/aes"
	"crypto/cipher"
	cryptoRand "crypto/rand"
	"encoding/binary"
	"fmt"
	"io"

	"golang.org/x/crypto/sha3"
)

// This implements MAYO_1

// The params of MAYO_1. This is specified in Table 2.1 of https://pqmayo.org/assets/specs/mayo.pdf
// Note that this can slightly change, but the principle remains

// Note that MAYO is an undertermined system so n > m, it is was overdetermined known efficient attacks are known.
const (
	Name = "MAYO_1"

	N = 66 // The number of variables in each of the multiquadratic polynomials of the PK.
	M = 64 // The number of multiquadratic polynimials, which all-together are the PK. Always a multiple of 32.
	O = 8  // The dimension of the oil space. For MAYO, this is < m, which is different than UOV. Note that using this
	// will mean that we have less degrees of freedom to generate signatures, so we will use it with k.
	K = 9 // The whipping parameter, to be used on signing to get enough degrees of freedom. For 8 * 9 = 72, which is closer to M.

	V = N - O // Aux param for the matrices

	// The division by 2 converts the number of nibbles to bytes.
	OSize  = V * O / 2                 // The size of O, the "hidden" oil space. It is a v x o matrix of GF(16)
	P1Size = (V * (V + 1) / 2) * M / 2 // The size of P1. These are m (n-o) x (n-o) upper triangular matrices
	P2Size = V * O * M / 2             // The size of P2. These are m rectangular matrices of (n-o) x o
	P3Size = (O * (O + 1) / 2) * M / 2 // P3 consists of M o x o triangular matrices
	VSize  = (V + 1) / 2               // The size of the vinegar variables

	SKSeedSize = 24 // The size (in bytes) of the seed to generate the sk
	PKSeedSize = 16 // The public key size

	DigestSize = 32
	SaltSize   = 24

	// W denotes the number of uint64 words required to fit m GF_16 elements
	W = M / 16
	F = 16
)

type PublicKey struct {
	pkSeed [PKSeedSize]byte

	// P1 and P2 are expanded from the pk seed
	p1 [P1Size / 8]uint64 // the square upper triangular matrix, which is public
	p2 [P2Size / 8]uint64 // the rectangular matrix, which is public

	p3 [P3Size / 8]uint64 // the square upper triangular matrix, which vanishes on O.
	// Can be calculated as  P_i^{(3)} = -OP_i^{(1)}O^\top - OP_i^{(2)}
}

// The expanded notion of the private key
type PrivateKey struct {
	skSeed [SKSeedSize]byte // compacted

	o_bytes [V * O]byte
	p1      [P1Size / 8]uint64
	l       [M * V * O / F]uint64 // The aux matrix = (P_i^(1) + P_i^(1)T) O + P_i^(2)
}

// decode decodes an N byte-array from src to N*2 nibbles (4-bit values) of dst.
// for src := []byte{0xAB, 0xCD}
// dst := make([]byte, 4)
// decode(dst, src)
// src[0] is 0xAB (10101011 in binary).
// dst[0] = 0xAB & 0x0F = 0x0B (00001011 & 00001111 = 00001011).
// dst[1] = 0xAB >> 4 = 0x0A (10101011 >> 4 = 00001010).
// src[1] is 0xCD (11001101 in binary).
// dst[2] = 0xCD & 0x0F = 0x0D (11001101 & 00001111 = 00001101).
// dst[3] = 0xCD >> 4 = 0x0C (11001101 >> 4 = 00001100).
// result: dst = {0x0B, 0x0A, 0x0D, 0x0C}
func decode(dst []byte, src []byte) {
	i := 0
	for ; i < len(dst)/2; i++ {
		dst[i*2] = src[i] & 0xf  // lower 4 bits
		dst[i*2+1] = src[i] >> 4 // upper 4 bits
	}

	// Account for odd length, by handling the lower
	if len(dst)&1 == 1 {
		dst[i*2] = src[i] & 0xf
	}
}

func encode(dst []byte, src []byte, length int) {
	var i int
	for i = 0; i+1 < length; i += 2 {
		dst[i/2] = (src[i+0] << 0) | (src[i+1] << 4)
	}
	if length&1 == 1 {
		dst[i/2] = (src[i+0] << 0)
	}
}

// if a == b -> 0x0000000000000000, else 0xFFFFFFFFFFFFFFFF
func ctCompare(a, b int) uint64 {
	return uint64((-(int64)(a ^ b)) >> 63)
}

// if a == b -> 0x00, else 0xFF
func ctCompare8(a, b byte) byte {
	return byte((-int32(a ^ b)) >> (31))
}

// a > b -> b - a is negative
// returns 0xFFFFFFFF if true, 0x00000000 if false
func ctIsGreaterThan(a, b int) uint64 {
	diff := int64(b) - int64(a)
	return uint64(diff >> 63)
}

func extract(in []uint64, index int) byte {
	leg := index / 16
	offset := index & 15

	return byte((in[leg] >> (offset * 4)) & 0xF)
}

func inverse(a byte) byte {
	a2 := mul(a, a)
	a4 := mul(a2, a2)
	a8 := mul(a4, a4)
	a6 := mul(a2, a4)
	a14 := mul(a8, a6)

	return a14
}

// Bytes to Uint64 slice in little-endian.
func bytesToUint64Slice(dst []uint64, src []byte) {
	for i := range dst {
		dst[i] = binary.LittleEndian.Uint64(src)
		src = src[8:]
	}
}

// Uint64 slice to Bytes in little-endian.
func uint64SliceToBytes(dst []byte, src []uint64) {
	for _, s := range src {
		binary.LittleEndian.PutUint64(dst, s)
		dst = dst[8:]
	}
}

// Matrix operations functions

// Given b (uint8) in GF(16), packs the 32-bit result of (b*x^3, b*x^2, b*x, b) into
// the returned multiplication table.
func genMultTable(b uint8) uint32 {
	pb := uint32(b) * 0x08040201       // represent the polynomial x^3, x^2, x, 1, and distribute b in it
	hNibble := pb & uint32(0xf0f0f0f0) // isolate the high nibble of each byte

	ret := (pb ^ (hNibble >> 4) ^ (hNibble >> 3)) // mod  by the irreducible x^4+x+1

	return ret
}

func mulAddPackedIn(acc []uint64, in []uint64, table uint32, b int) {
	lsbMask := uint64(0x1111111111111111) // mask to extract the lsb
	for i := 0; i < b; i++ {              // add and mul
		acc[i] ^= (in[i]&lsbMask)*uint64(table&0xff) ^
			((in[i]>>1)&lsbMask)*uint64((table>>8)&0xf) ^
			((in[i]>>2)&lsbMask)*uint64((table>>16)&0xf) ^
			((in[i]>>3)&lsbMask)*uint64((table>>24)&0xf)
	}
}

func mulAddPacked(acc []uint64, inM []uint64, inV byte, w int) {
	table := genMultTable(inV)
	mulAddPackedIn(acc, inM, table, w)
}

func mulAddPackedS(a uint64, b uint8) uint64 {
	msb := uint64(0x8888888888888888)
	a64 := a
	r64 := a64 * uint64(b&1)

	for i := 1; i < 4; i++ {
		b >>= 1
		aMsb := a64 & msb
		a64 ^= aMsb
		a64 = (a64 << 1) ^ ((aMsb >> 3) * 3)
		r64 ^= (a64) * uint64(b&1)
	}

	return r64
}

func mulAddMatVec(acc []byte, m []byte, v []byte, rows, cols int) {
	for i := 0; i < rows; i++ {
		for j := 0; j < cols; j++ {
			acc[i] ^= byte(mulAddPackedS(uint64(m[i*cols+j]), v[j]))
		}
	}
}

func mulAddMat(acc []uint64, p1 []uint64, o_b []uint8) {
	// The ordinary summation order is r -> c -> k, but here it is interchanged to make use of multiplication table
	cols := V
	for k := 0; k < O; k++ {
		for c := 0; c < cols; c++ {
			table := genMultTable(o_b[c*O+k])
			for r := 0; r <= c; r++ {
				pos := r*(cols*2-r+1)/2 + (c - r)
				mulAddPackedIn(acc[W*(r*O+k):], p1[W*pos:], table, W)
			}
		}
	}
}

func mulAddMatTran(acc []uint64, m1 []uint8, m2 []uint64) {
	for r := 0; r < O; r++ {
		for c := 0; c < V; c++ {
			table := genMultTable(m1[c*O+r])
			for k := 0; k < O; k++ {
				mulAddPackedIn(acc[W*(r*O+k):], m2[W*(c*O+k):], table, W)
			}
		}
	}
}

func mulAddMatP(acc []uint64, m1 []uint8, m2 []uint64, rows int, cols int, cols2 int) {
	for r := 0; r < rows; r++ {
		for c := 0; c < cols; c++ {
			table := genMultTable(m1[r*cols+c])
			for k := 0; k < cols2; k++ {
				mulAddPackedIn(acc[W*(r*cols2+k):], m2[W*(c*cols2+k):], table, W)
			}
		}
	}
}

func mulAddMMatPTrans(acc []uint64, m1 []uint64, m2 []uint8) {
	for k := 0; k < K; k++ {
		for c := 0; c < V; c++ {
			rBound := V - 1
			rBound = c

			for r := 0; r <= rBound; r++ {
				table := genMultTable(m2[k*V+c])
				pos := r*V + c
				pos = r*(V*2-r+1)/2 + (c - r)

				mulAddPackedIn(acc[W*(r*K+k):], m1[W*pos:], table, W)
			}
		}
	}
}

// Take the upper of the matrix
func takeUpper(out []uint64, in []uint64, size int) {
	pos := 0
	for r := 0; r < size; r++ {
		for c := r; c < size; c++ {
			copy(out[W*pos:][:W], in[W*(r*size+c):][:W])
			if r != c {
				for p := 0; p < W; p++ {
					out[W*pos+p] ^= in[W*(c*size+r)+p]
				}
			}
			pos++
		}
	}
}

// Aux functions

// Calculate L_i, with the assumption that P_i^2 is set in the passed variable.
// We perform: (P^1_i + P^{1\top}) * O
// Note that (P^1_i + P^{1\top}) forms a symmetric matrix since P^1_i
// is upper triangular and adding its transpose will result in a matrix where the
// the upper and lower triangular parts mirror each other.
func calculateLGivenP2(acc []uint64, p1 []uint64, o_m []uint8) {
	p1Pos := 0
	for r := 0; r < V; r++ {
		for c := r; c < V; c++ {
			if c == r {
				p1Pos += 1
				continue
			}
			for k := 0; k < O; k++ {
				mulAddPacked(acc[W*(r*O+k):], p1[W*p1Pos:], o_m[c*O+k], W)
				mulAddPacked(acc[W*(c*O+k):], p1[W*p1Pos:], o_m[r*O+k], W)
			}
			p1Pos++
		}
	}
}

// GF(16) multiplication mod x^4 + x + 1
func mul(a, b uint8) uint8 {
	// carryless multiply
	p := (a & 1) * b
	p ^= (a & 2) * b
	p ^= (a & 4) * b
	p ^= (a & 8) * b

	// reduce mod x^4 + x + 1
	top := p & 0xf0
	return (p ^ (top >> 4) ^ (top >> 3)) & 0x0f
}

func mulx8(a byte, b uint64) uint64 {
	// carryless multiply
	p := uint64(a&1) * b
	p ^= uint64(a&2) * b
	p ^= uint64(a&4) * b
	p ^= uint64(a&8) * b

	// reduce mod x^4 + x + 1
	top := p & 0xf0f0f0f0f0f0f0f0
	return (p ^ (top >> 4) ^ (top >> 3)) & 0x0f0f0f0f0f0f0f0f
}

func emulsify(u []uint64, y []uint8) {
	var tail = [5]uint8{8, 0, 2, 8, 0}
	var acc [M / F]uint64

	for i := K - 1; i >= 0; i-- {
		for j := i; j < K; j++ {
			top := uint8(acc[M/16-1] >> 60)

			acc[M/16-1] <<= 4
			for k := M/16 - 2; k >= 0; k-- {
				acc[k+1] ^= acc[k] >> 60
				acc[k] <<= 4
			}

			acc[0] ^= uint64(mul(top, tail[0]))
			acc[0] ^= uint64(mul(top, tail[1])) << 4
			acc[0] ^= uint64(mul(top, tail[2])) << 8
			acc[0] ^= uint64(mul(top, tail[3])) << 12
			acc[0] ^= uint64(mul(top, tail[4])) << 16

			for k := 0; k < M/16; k++ {
				acc[k] ^= u[(i*K+j)*(M/16)+k]
				if i != j {
					acc[k] ^= u[(j*K+i)*(M/16)+k]
				}
			}
		}
	}

	for i := 0; i < M; i += 16 {
		a := acc[i/16]
		for k := 0; k < 16; k++ {
			y[i+k] ^= uint8(a & 0xF)
			a >>= 4
		}
	}
}

func transpose16x16Nibbles(m []uint64) {
	const evenNibbles = 0x0f0f0f0f0f0f0f0f
	const evenBytes = 0x00ff00ff00ff00ff
	const even2Bytes = 0x0000ffff0000ffff
	const evenHalf = 0x00000000ffffffff

	for i := 0; i < 16; i += 2 {
		t := ((m[i] >> 4) ^ m[i+1]) & evenNibbles
		m[i] ^= t << 4
		m[i+1] ^= t
	}

	for i := 0; i < 16; i += 4 {
		t0 := ((m[i] >> 8) ^ m[i+2]) & evenBytes
		t1 := ((m[i+1] >> 8) ^ m[i+3]) & evenBytes
		m[i] ^= (t0 << 8)
		m[i+1] ^= (t1 << 8)
		m[i+2] ^= t0
		m[i+3] ^= t1
	}

	for i := 0; i < 4; i++ {
		t0 := ((m[i] >> 16) ^ m[i+4]) & even2Bytes
		t1 := ((m[i+8] >> 16) ^ m[i+12]) & even2Bytes

		m[i] ^= t0 << 16
		m[i+8] ^= t1 << 16
		m[i+4] ^= t0
		m[i+12] ^= t1
	}

	for i := 0; i < 8; i++ {
		t := ((m[i] >> 32) ^ m[i+8]) & evenHalf
		m[i] ^= t << 32
		m[i+8] ^= t
	}
}

func computeA(m []uint64, _a []byte) {
	const OKpadded = (O*K + 15) / 16 * 16
	var a [(M / 8) * OKpadded]uint64
	var tail = [5]uint8{8, 0, 2, 8, 0}

	bitsToShift, wordsToShift := 0, 0
	for i := 0; i < K; i++ {
		for j := K - 1; j >= i; j-- {
			mj := m[j*O*M/16:]

			for c := 0; c < O; c++ {
				for k := 0; k < M/16; k++ { // currently 4
					a[(O*i+c)+(k+wordsToShift)*OKpadded] ^= mj[k+c*M/16] << bitsToShift
					if bitsToShift > 0 {
						a[(O*i+c)+(k+wordsToShift+1)*OKpadded] ^= mj[k+c*M/16] >> (64 - bitsToShift)
					}
				}
			}

			if i != j {
				mi := m[i*O*M/16:]
				for c := 0; c < O; c++ {
					for k := 0; k < M/16; k++ {
						a[(O*j)+c+(k+wordsToShift)*OKpadded] ^= mi[k+c*M/16] << bitsToShift
						if bitsToShift > 0 {
							a[(O*j)+c+(k+wordsToShift+1)*OKpadded] ^= mi[k+c*M/16] >> (64 - bitsToShift)
						}
					}
				}
			}

			bitsToShift += 4
			if bitsToShift == 64 {
				bitsToShift = 0
				wordsToShift++
			}
		}
	}

	for c := 0; c < OKpadded*((M+(K+1)*K/2+15)/16); c += 16 {
		transpose16x16Nibbles(a[c:])
	}

	var tab [len(tail) * 4]byte
	for i := 0; i < len(tail); i++ {
		tab[4*i] = mul(tail[i], 1)
		tab[4*i+1] = mul(tail[i], 2)
		tab[4*i+2] = mul(tail[i], 4)
		tab[4*i+3] = mul(tail[i], 8)
	}

	const lsb = 0x1111111111111111

	for c := 0; c < OKpadded; c += 16 {
		for r := M; r < M+(K+1)*K/2; r++ {
			pos := (r/16)*OKpadded + c + (r & 15)
			t0 := a[pos] & lsb
			t1 := (a[pos] >> 1) & lsb
			t2 := (a[pos] >> 2) & lsb
			t3 := (a[pos] >> 3) & lsb
			for t := 0; t < len(tail); t++ {
				a[((r+t-M)/16)*OKpadded+c+((r+t)&15)] ^= t0*uint64(tab[4*t+0]) ^ t1*uint64(tab[4*t+1]) ^ t2*uint64(tab[4*t+2]) ^ t3*uint64(tab[4*t+3])
			}
		}
	}

	// transform the temporary matrix into the desired form of A matrix
	var aBytes [M * OKpadded]byte
	uint64SliceToBytes(aBytes[:], a[:])

	KO1 := K*O + 1
	for r := 0; r < M; r += 16 {
		for c := 0; c < KO1-1; c += 16 {
			for i := 0; i < 16; i++ {
				src := aBytes[(r/16*OKpadded+c+i)*8:]
				offset := KO1*(r+i) + c
				decode(_a[offset:offset+min(16, KO1-1-c)], src)
			}
		}
	}
}

func ef(A []byte, nrows, ncols int) {
	rowLen := (ncols + 15) / 16

	var pivotRowData [(K*O + 1 + 15) / 16]uint64 // rounds up
	var pivotRowData2 [(K*O + 1 + 15) / 16]uint64

	var packedAbyte [((K*O + 1 + 15) / 16) * M * 8]byte
	for i := 0; i < nrows; i++ {
		encode(packedAbyte[i*rowLen*8:], A[i*ncols:], ncols)
	}

	var packedA [((K*O + 1 + 15) / 16) * M]uint64
	bytesToUint64Slice(packedA[:], packedAbyte[:])

	pivotRow := 0
	for pivotCol := 0; pivotCol < ncols; pivotCol++ {
		pivotRowLowerBound := max(0, pivotCol+nrows-ncols)
		pivotRowUpperBound := min(nrows-1, pivotCol)

		for i := 0; i < rowLen; i++ {
			pivotRowData[i] = 0
			pivotRowData2[i] = 0
		}

		var pivot byte = 0
		var pivotIsZero uint64 = 0xffffffffffffffff
		for row := pivotRowLowerBound; row <= min(nrows-1, pivotRowUpperBound+32); row++ {
			isPivotRow := ^ctCompare(row, pivotRow)
			belowPivotRow := ctIsGreaterThan(row, pivotRow)

			for j := 0; j < rowLen; j++ {
				mask := isPivotRow | (belowPivotRow & pivotIsZero)
				pivotRowData[j] ^= mask & packedA[row*rowLen+j]
			}
			pivot = extract(pivotRowData[:], pivotCol)
			pivotIsZero = ^ctCompare(int(pivot), 0)
		}

		inverse := inverse(pivot)
		mulAddPacked(pivotRowData2[:], pivotRowData[:], inverse, rowLen)

		for row := pivotRowLowerBound; row <= pivotRowUpperBound; row++ {
			doCopy := ^ctCompare(row, pivotRow) & ^pivotIsZero
			doNotCopy := ^doCopy
			for col := 0; col < rowLen; col++ {
				packedA[row*rowLen+col] = (doNotCopy & packedA[row*rowLen+col]) +
					(doCopy & pivotRowData2[col])
			}
		}

		for row := pivotRowLowerBound; row < nrows; row++ {
			belowPivot := byte(0)
			if row > pivotRow {
				belowPivot = 1
			}
			eltToElim := extract(packedA[row*rowLen:], pivotCol)

			mulAddPacked(packedA[row*rowLen:], pivotRowData2[:], belowPivot*eltToElim, rowLen)
		}

		pivotRow += -int(^pivotIsZero)
	}

	var temp [(O*K + 1 + 15)]byte

	uint64SliceToBytes(packedAbyte[:], packedA[:])

	for i := 0; i < nrows; i++ {
		decode(temp[:rowLen*16], packedAbyte[i*rowLen*8:])
		for j := 0; j < ncols; j++ {
			A[i*ncols+j] = temp[j]
		}
	}
}

func sampleSolution(a []byte, y []byte, r []byte, x []byte) bool {
	const aCols = K*O + 1

	copy(x[:], r[:])

	var ar [M]byte
	mulAddMatVec(ar[:], a[:], x[:], M, aCols)

	// move y - Ar to last column of matrix A
	for i := 0; i < M; i++ {
		a[K*O+i*(aCols)] = y[i] ^ ar[i]
	}

	ef(a[:], M, aCols)

	fullRank := byte(0)
	for i := 0; i < aCols-1; i++ {
		fullRank |= a[(M-1)*(aCols)+i]
	}

	if fullRank == 0 {
		return false
	}

	for row := M - 1; row >= 0; row-- {
		finished := byte(0)
		colUpperBound := min(row+(32/(M-row)), K*O)

		for col := row; col <= colUpperBound; col++ {
			correctColumn := ctCompare8((a[row*aCols+col]), 0) & ^finished

			u := correctColumn & a[row*aCols+aCols-1]
			x[col] ^= u

			for i := 0; i < row; i += 8 {
				tmp := (uint64(a[i*aCols+col]) << 0) ^ (uint64(a[(i+1)*aCols+col]) << 8) ^
					(uint64(a[(i+2)*aCols+col]) << 16) ^ (uint64(a[(i+3)*aCols+col]) << 24) ^
					(uint64(a[(i+4)*aCols+col]) << 32) ^ (uint64(a[(i+5)*aCols+col]) << 40) ^
					(uint64(a[(i+6)*aCols+col]) << 48) ^ (uint64(a[(i+7)*aCols+col]) << 56)

				tmp = mulx8(u, tmp)

				a[i*aCols+aCols-1] ^= byte((tmp) & 0xf)
				a[(i+1)*aCols+aCols-1] ^= byte((tmp >> 8) & 0xf)
				a[(i+2)*aCols+aCols-1] ^= byte((tmp >> 16) & 0xf)
				a[(i+3)*aCols+aCols-1] ^= byte((tmp >> 24) & 0xf)
				a[(i+4)*aCols+aCols-1] ^= byte((tmp >> 32) & 0xf)
				a[(i+5)*aCols+aCols-1] ^= byte((tmp >> 40) & 0xf)
				a[(i+6)*aCols+aCols-1] ^= byte((tmp >> 48) & 0xf)
				a[(i+7)*aCols+aCols-1] ^= byte((tmp >> 56) & 0xf)
			}

			finished = finished | correctColumn
		}
	}

	return true
}

// API functions

// Generate the expanded sk. Note that this will be stored in the struct sk.
func (sk *PrivateKey) ExpandSK(buf *[SKSeedSize]byte) {
	copy(sk.skSeed[:], buf[:]) // The seed

	var seedPk [PKSeedSize]byte
	var oBytes [OSize]byte

	// Note that we don't generate the pkSeed
	// but we do OBytes. We can refactor so we don't regenerate
	h := sha3.NewShake256()
	_, _ = h.Write(sk.skSeed[:])
	_, _ = h.Read(seedPk[:])
	_, _ = h.Read(oBytes[:])

	// Derive p_1 and p_2
	var nonce [16]byte
	block, _ := aes.NewCipher(seedPk[:])
	ctr := cipher.NewCTR(block, nonce[:])

	var p_1_2 [P1Size + P2Size]byte
	ctr.XORKeyStream(p_1_2[:], p_1_2[:])

	// Decode as nibbles
	decode(sk.o_bytes[:], oBytes[:])

	bytesToUint64Slice(sk.p1[:P1Size/8], p_1_2[:P1Size])

	// Set L already to P2
	// If failure, this should reset
	bytesToUint64Slice(sk.l[:], p_1_2[P1Size:])

	// compute L_i = (P1 + P1^t)*O + P2
	// Note that sk.l is already set to P2
	calculateLGivenP2(sk.l[:], sk.p1[:], sk.o_bytes[:])
}

// Generate the expanded version of the public key
func GenerateExpPublic(sk *PrivateKey) *PublicKey {
	var pk PublicKey
	var o [OSize]byte

	h := sha3.NewShake256()
	_, _ = h.Write(sk.skSeed[:])
	_, _ = h.Read(pk.pkSeed[:])
	_, _ = h.Read(o[:])

	var nonce [16]byte
	block, _ := aes.NewCipher(pk.pkSeed[:])
	ctr := cipher.NewCTR(block, nonce[:])

	// TODO: refactor as this is all repeated
	// Generate P1 and P2
	var p1 [P1Size]byte
	var p2 [P2Size]byte
	ctr.XORKeyStream(p1[:], p1[:])
	ctr.XORKeyStream(p2[:], p2[:])

	bytesToUint64Slice(pk.p1[:], p1[:])
	bytesToUint64Slice(pk.p2[:], p2[:])

	var o_bytes [V * O]byte
	decode(o_bytes[:], o[:])

	var tmp [P2Size / 8]uint64
	copy(tmp[:], pk.p2[:])

	// Generate P3: -O^T P^(1)_i O − O^T P^(2)_i
	var p3 [M * O * O / F]uint64
	mulAddMat(tmp[:], pk.p1[:], o_bytes[:])
	mulAddMatTran(p3[:], o_bytes[:], tmp[:])

	// Take only the upper part of P3
	takeUpper(pk.p3[:], p3[:], O)

	return &pk
}

func KeyPairExpFromSeed(seed []byte) (*PublicKey, *PrivateKey) {
	if len(seed) != SKSeedSize {
		panic(fmt.Sprintf("Incorrect lenght. It must be %d", SKSeedSize))
	}

	seedBuf := [SKSeedSize]byte{}
	copy(seedBuf[:], seed) // Essentially the compact representation of sk

	var sk PrivateKey

	sk.ExpandSK(&seedBuf) // Expand the sk
	pk := GenerateExpPublic(&sk)

	return pk, &sk
}

// GenerateExpandedKeyPair generates an expanded key pair.
func GenerateExpandedKeyPair(rand io.Reader) (*PublicKey, *PrivateKey, error) {
	var seed [SKSeedSize]byte
	if rand == nil {
		rand = cryptoRand.Reader
	}
	_, err := io.ReadFull(rand, seed[:])
	if err != nil {
		return nil, nil, err
	}

	pk, sk := KeyPairExpFromSeed(seed[:])

	return pk, sk, nil
}

func Sign(msg []byte, sk *PrivateKey, rand io.Reader) ([]byte, error) {
	if rand == nil {
		rand = cryptoRand.Reader
	}

	var dig [DigestSize]byte
	var salt [SaltSize]byte

	// Generate the digest
	h := sha3.NewShake256()
	_, _ = h.Write(msg[:])
	_, _ = h.Read(dig[:])

	// Generate R
	if _, err := io.ReadFull(rand, salt[:]); err != nil {
		return nil, err
	}

	h.Reset()
	// Set the salt
	_, _ = h.Write(dig[:])
	_, _ = h.Write(salt[:])
	_, _ = h.Write(sk.skSeed[:])
	_, _ = h.Read(salt[:])

	h.Reset()
	// Set t and encode
	_, _ = h.Write(dig[:])
	_, _ = h.Write(salt[:])

	var tEnc [M / 2]byte
	_, _ = h.Read(tEnc[:])

	var t [M]byte
	decode(t[:], tEnc[:])

	var v [K * V]byte
	var x [K*O + 1]byte // + 1 for buffer
	for ctr := 0; ctr <= 255; ctr++ {
		ctrByte := []byte{byte(ctr)}

		// Generate V vars, the vinegars, which are random
		h.Reset()
		_, _ = h.Write(dig[:])
		_, _ = h.Write(salt[:])
		_, _ = h.Write(sk.skSeed[:])
		_, _ = h.Write(ctrByte[:])

		var vs [K * VSize]byte
		_, _ = h.Read(vs[:])
		for i := 0; i < K; i++ {
			decode(v[i*V:(i+1)*V], vs[i*VSize:])
		}

		// Generate R vars, to help solve
		var rs [K * O / 2]byte
		_, _ = h.Read(rs[:])
		var r [K * O]byte
		decode(r[:], rs[:])

		// M_i[j, :] = v_i^\top L_j . Set the rows
		var mTmp [M * K * O / F]uint64
		mulAddMatP(mTmp[:], v[:], sk.l[:], K, V, O)

		// Generate u

		// P^1 * V^\top
		var tmpU [M * V * K / F]uint64
		mulAddMMatPTrans(tmpU[:], sk.p1[:], v[:])

		// V * P^1 * V^\top
		var u [M * K * K / F]uint64
		mulAddMatP(u[:], v[:], tmpU[:], K, V, K)

		// Calculate y and emulsify with E
		var y [M]byte
		copy(y[:], t[:])
		emulsify(u[:], y[:])

		// Calculate A
		var A [M * (K*O + 1)]byte
		computeA(mTmp[:], A[:])

		// solve Ax = y
		if sampleSolution(A[:], y[:], r[:], x[:]) {
			break
		}
	}

	var s [K * N]byte
	// compute v + Ox
	// set s = v + Ox || x
	for i := 0; i <= K-1; i++ {
		copy(s[i*N:][:V], v[i*V:])
		mulAddMatVec(s[i*N:], sk.o_bytes[:], x[i*O:], V, O)
		copy(s[i*N+V:][:O], x[i*O:])
	}

	var sig [(K*N+1)/2 + SaltSize]byte
	encode(sig[:], s[:], K*N)
	copy(sig[(K*N+1)/2:], salt[:])

	return sig[:], nil
}

func main() {
	fmt.Println("Hello, MAYO 1!")

	pk, sk, err := GenerateExpandedKeyPair(nil)
	if err != nil {
		panic(err)
	}

	// Prints public and private key
	fmt.Printf("%+v\n", sk)
	fmt.Printf("%+v\n", pk)
}
