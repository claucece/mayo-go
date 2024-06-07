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
	O = 8  // The dimension of the oil space. For MAYO, this is < m, which is different than UOV.
	K = 9  // The whipping parameter, to be used on signing to get enough degrees of freedom. For 8 * 9 = 72, which is closer to M.

	V = N - O // Aux param for the matrices

	// The division by 2 converts the number of nibbles to bytes.
	OSize  = V * O / 2                 // The size of O, the "hidden" oil space. It is a v x o matrix of GF(16)
	P1Size = (V * (V + 1) / 2) * M / 2 // The size of P1. These are m (n-o) x (n-o) upper triangular matrices
	P2Size = V * O * M / 2             // The size of P2. These are m rectangular matrices of (n-o) x o
	P3Size = (O * (O + 1) / 2) * M / 2 // P3 consists of M o x o triangular matrices

	SKSeedSize = 24 // The size (in bytes) of the seed to generate the sk
	PKSeedSize = 16 // The public key size

	DigestSize = 32

	// W denotes the number of uint64 words required to fit M GF16 elements
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

type PrivateKey struct {
	skSeed [SKSeedSize]byte // compacted

	p1      [P1Size / 8]uint64
	o_bytes [V * O]byte
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

func (sk *PrivateKey) ExpandSK(buf *[SKSeedSize]byte) {
	copy(sk.skSeed[:], buf[:]) // The seed

	var seedPk [PKSeedSize]byte
	var oBytes [OSize]byte

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
	//computeL(sk.l[:], sk.p1[:], sk.o_bytes[:], V, O)
}

func KeyPairFromSeed(seed []byte) PrivateKey {
	if len(seed) != SKSeedSize {
		panic(fmt.Sprintf("Incorrect lenght. It must be %d", SKSeedSize))
	}

	seedBuf := [SKSeedSize]byte{}
	copy(seedBuf[:], seed) // Essentially the compact representation of sk

	var sk PrivateKey

	sk.ExpandSK(&seedBuf)

	return sk
}

// GenerateKeyPair generates a key pair.
func GenerateKeyPair(rand io.Reader) (*PublicKey, *PrivateKey, error) {
	var seed [SKSeedSize]byte
	if rand == nil {
		rand = cryptoRand.Reader
	}
	_, err := io.ReadFull(rand, seed[:])
	if err != nil {
		return nil, nil, err
	}

	sk := KeyPairFromSeed(seed[:])

	return nil, &sk, nil
}

func main() {
	fmt.Println("Hello, MAYO 1!")
}
