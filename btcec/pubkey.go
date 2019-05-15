// Copyright (c) 2013-2014 The btcsuite developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package btcec

import (
	"crypto/ecdsa"
	"errors"
	"fmt"
	"math/big"
)

// These constants define the lengths of serialized public keys.
const (
	PubKeyBytesLenCompressed   = 33
	PubKeyBytesLenUncompressed = 65
	PubKeyBytesLenHybrid       = 65
)

func isOdd(a *big.Int) bool {
	return a.Bit(0) == 1
}

// decompressPoint decompresses a point on the secp256k1 curve given the X point and
// the solution to use.
func decompressPoint(curve *KoblitzCurve, bigX *big.Int, ybit bool) (*big.Int, error) {
	var x fieldVal
	x.SetByteSlice(bigX.Bytes())

	// Compute x^3 + B mod p.
	var x3 fieldVal
	x3.SquareVal(&x)
	x3.Mul(&x).Add(curve.FieldB()).Normalize()

	// Now calculate sqrt mod p of x^3 + B
	// This code used to do a full sqrt based on tonelli/shanks,
	// but this was replaced by the algorithms referenced in
	// https://bitcointalk.org/index.php?topic=162805.msg1712294#msg1712294
	var y fieldVal
	sqrt(curve, &y, &x3)
	if ybit != y.IsOdd() {
		y.Negate(1)
	}
	y.Normalize()

	// Check that y is a square root of x^3 + B.
	var y2 fieldVal
	y2.SquareVal(&y).Normalize()
	if !y2.Equals(&x3) {
		return nil, fmt.Errorf("invalid square root")
	}

	// Verify that y-coord has expected parity.
	if ybit != y.IsOdd() {
		return nil, fmt.Errorf("ybit doesn't match oddness")
	}

	return new(big.Int).SetBytes(y.Bytes()[:]), nil
}

// sqrt computes the square root of x modulo the curve's prime, and stores
// the result in res. The square root is computed via exponentiation of x by the
// value Q = (P+1)/4 using the curve's precomputed big-endian representation of
// the Q.  This method uses a modified version of square-and-multiply
// exponentiation over secp256k1 fieldVals to operate on bytes instead of bits,
// which offers better performance over both big.Int exponentiation and bit-wise
// square-and-multiply.
//
// NOTE: This method only works when P is intended to be the secp256k1 prime and
// is not constant time. The returned value is of magnitude 1, but is
// denormalized.
func sqrt(curve *KoblitzCurve, res, x *fieldVal) {
	// The following computation iteratively computes x^((P+1)/4) = x^Q
	// using the recursive, piece-wise definition:
	//
	//   x^n = (x^2)^(n/2) mod P       if n is even
	//   x^n = x(x^2)^(n-1/2) mod P    if n is odd
	//
	// Given n in its big-endian representation b_k, ..., b_0, x^n can be
	// computed by defining the sequence r_k+1, ..., r_0, where:
	//
	//   r_k+1 = 1
	//   r_i   = (r_i+1)^2 * x^b_i    for i = k, ..., 0
	//
	// The final value r_0 = x^n.
	//
	// See https://en.wikipedia.org/wiki/Exponentiation_by_squaring for more
	// details.
	//
	// This can be further optimized, by observing that the value of Q in
	// secp256k1 has the value:
	//
	//   Q = 3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff0c
	//
	// We can unroll the typical bit-wise interpretation of the
	// exponentiation algorithm above to instead operate on bytes.
	// This reduces the number of comparisons from 256*3 = 768 in the
	// prior bit-wise algorithm, down to (32*2)+1+2+2 = 69, reducing the
	// overhead of failed branch predictions and additional comparisons.
	//
	// Since the there are only 4 unique bytes of Q, this keeps the jump
	// table small without the need to handle all possible 8-bit values.
	// Further, we observe that 29 of the 32 bytes are 0xff; making the
	// first case handle 0xff therefore optimizes the hot path.
	res.SetInt(1)
	for _, b := range curve.QBytes() {
		switch b {

		// Most common case, where all 8 bits are set.
		case 0xff:
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)

		// First byte of Q, where all but the top two bits are set. Note
		// that this case only applies six operations, since the highest
		// bit of Q resides in bit six of the first byte. We ignore the
		// first two bytes, since squaring for these bits will result in
		// an invalid result. We forgo squaring res on the first bit,
		// since 1^2 = 1.
		case 0x3f:
			res.Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)

		// Byte 28 of Q, where only bit 7 is unset.
		case 0xbf:
			res.Square().Mul(x)
			res.Square()
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square().Mul(x)

		// Byte 31 of Q (0x0c), where only bits 3 and 4 are set.
		default:
			res.Square()
			res.Square()
			res.Square()
			res.Square()
			res.Square().Mul(x)
			res.Square().Mul(x)
			res.Square()
			res.Square()
		}
	}
}

const (
	pubkeyCompressed   byte = 0x2 // y_bit + x coord
	pubkeyUncompressed byte = 0x4 // x coord + y coord
	pubkeyHybrid       byte = 0x6 // y_bit + x coord + y coord
)

// IsCompressedPubKey returns true the the passed serialized public key has
// been encoded in compressed format, and false otherwise.
func IsCompressedPubKey(pubKey []byte) bool {
	// The public key is only compressed if it is the correct length and
	// the format (first byte) is one of the compressed pubkey values.
	return len(pubKey) == PubKeyBytesLenCompressed &&
		(pubKey[0]&^byte(0x1) == pubkeyCompressed)
}

// ParsePubKey parses a public key for a koblitz curve from a bytestring into a
// ecdsa.Publickey, verifying that it is valid. It supports compressed,
// uncompressed and hybrid signature formats.
func ParsePubKey(pubKeyStr []byte, curve *KoblitzCurve) (key *PublicKey, err error) {
	pubkey := PublicKey{}
	pubkey.Curve = curve

	if len(pubKeyStr) == 0 {
		return nil, errors.New("pubkey string is empty")
	}

	format := pubKeyStr[0]
	ybit := (format & 0x1) == 0x1
	format &= ^byte(0x1)

	switch len(pubKeyStr) {
	case PubKeyBytesLenUncompressed:
		if format != pubkeyUncompressed && format != pubkeyHybrid {
			return nil, fmt.Errorf("invalid magic in pubkey str: "+
				"%d", pubKeyStr[0])
		}

		pubkey.X = new(big.Int).SetBytes(pubKeyStr[1:33])
		pubkey.Y = new(big.Int).SetBytes(pubKeyStr[33:])
		// hybrid keys have extra information, make use of it.
		if format == pubkeyHybrid && ybit != isOdd(pubkey.Y) {
			return nil, fmt.Errorf("ybit doesn't match oddness")
		}

		if pubkey.X.Cmp(pubkey.Curve.Params().P) >= 0 {
			return nil, fmt.Errorf("pubkey X parameter is >= to P")
		}
		if pubkey.Y.Cmp(pubkey.Curve.Params().P) >= 0 {
			return nil, fmt.Errorf("pubkey Y parameter is >= to P")
		}
		if !pubkey.Curve.IsOnCurve(pubkey.X, pubkey.Y) {
			return nil, fmt.Errorf("pubkey isn't on secp256k1 curve")
		}

	case PubKeyBytesLenCompressed:
		// format is 0x2 | solution, <X coordinate>
		// solution determines which solution of the curve we use.
		/// y^2 = x^3 + Curve.B
		if format != pubkeyCompressed {
			return nil, fmt.Errorf("invalid magic in compressed "+
				"pubkey string: %d", pubKeyStr[0])
		}
		pubkey.X = new(big.Int).SetBytes(pubKeyStr[1:33])
		pubkey.Y, err = decompressPoint(curve, pubkey.X, ybit)
		if err != nil {
			return nil, err
		}

	default: // wrong!
		return nil, fmt.Errorf("invalid pub key length %d",
			len(pubKeyStr))
	}

	return &pubkey, nil
}

// PublicKey is an ecdsa.PublicKey with additional functions to
// serialize in uncompressed, compressed, and hybrid formats.
type PublicKey ecdsa.PublicKey

// ToECDSA returns the public key as a *ecdsa.PublicKey.
func (p *PublicKey) ToECDSA() *ecdsa.PublicKey {
	return (*ecdsa.PublicKey)(p)
}

// SerializeUncompressed serializes a public key in a 65-byte uncompressed
// format.
func (p *PublicKey) SerializeUncompressed() []byte {
	b := make([]byte, 0, PubKeyBytesLenUncompressed)
	b = append(b, pubkeyUncompressed)
	b = paddedAppend(32, b, p.X.Bytes())
	return paddedAppend(32, b, p.Y.Bytes())
}

// SerializeCompressed serializes a public key in a 33-byte compressed format.
func (p *PublicKey) SerializeCompressed() []byte {
	b := make([]byte, 0, PubKeyBytesLenCompressed)
	format := pubkeyCompressed
	if isOdd(p.Y) {
		format |= 0x1
	}
	b = append(b, format)
	return paddedAppend(32, b, p.X.Bytes())
}

// SerializeHybrid serializes a public key in a 65-byte hybrid format.
func (p *PublicKey) SerializeHybrid() []byte {
	b := make([]byte, 0, PubKeyBytesLenHybrid)
	format := pubkeyHybrid
	if isOdd(p.Y) {
		format |= 0x1
	}
	b = append(b, format)
	b = paddedAppend(32, b, p.X.Bytes())
	return paddedAppend(32, b, p.Y.Bytes())
}

// IsEqual compares this PublicKey instance to the one passed, returning true if
// both PublicKeys are equivalent. A PublicKey is equivalent to another, if they
// both have the same X and Y coordinate.
func (p *PublicKey) IsEqual(otherPubKey *PublicKey) bool {
	return p.X.Cmp(otherPubKey.X) == 0 &&
		p.Y.Cmp(otherPubKey.Y) == 0
}

// paddedAppend appends the src byte slice to dst, returning the new slice.
// If the length of the source is smaller than the passed size, leading zero
// bytes are appended to the dst slice before appending src.
func paddedAppend(size uint, dst, src []byte) []byte {
	for i := 0; i < int(size)-len(src); i++ {
		dst = append(dst, 0)
	}
	return append(dst, src...)
}
