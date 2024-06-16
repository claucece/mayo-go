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

	SKSeedSize = 24 // The size (in bytes) of the seed to generate the sk
	PKSeedSize = 16 // The public key size

	DigestSize = 32

	// W denotes the number of uint64 words required to fit m GF_16 elements
	W = M / 16
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
	l       [M * V * O / 16]uint64 // The aux matrix = (P_i^(1) + P_i^(1)T) O + P_i^(2)
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

// Bytes to Uint64 slice in little-endian.
func bytesToUint64Slice(dst []uint64, src []byte) {
	for i := range dst {
		dst[i] = binary.LittleEndian.Uint64(src)
		src = src[8:]
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
	var p3 [M * O * O / 16]uint64
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
