package main

import (
	"crypto/sha256"
	"encoding/binary"
)

// tree is an RFC 6962 Merkle tree of size leaves whose leaf hashes come from
// leaf, so a large tree needs no storage. Hashing the root or a path visits
// every leaf once.
type tree struct {
	size uint64
	leaf func(i uint64) []byte
}

func hashLeaf(data []byte) []byte {
	h := sha256.New()
	h.Write([]byte{0x00})
	h.Write(data)
	return h.Sum(nil)
}

func hashChildren(l, r []byte) []byte {
	h := sha256.New()
	h.Write([]byte{0x01})
	h.Write(l)
	h.Write(r)
	return h.Sum(nil)
}

// split returns the largest power of two less than n, for n > 1.
func split(n uint64) uint64 {
	k := uint64(1)
	for k<<1 < n {
		k <<= 1
	}
	return k
}

// root returns MTH(D[0:size]).
func (t tree) root() []byte {
	return t.hash(0, t.size)
}

func (t tree) hash(lo, hi uint64) []byte {
	if hi-lo == 1 {
		return t.leaf(lo)
	}
	k := split(hi - lo)
	return hashChildren(t.hash(lo, lo+k), t.hash(lo+k, hi))
}

// inclusionProof returns PATH(m, D[0:size]), ordered from the leaf toward
// the root.
func (t tree) inclusionProof(m uint64) [][]byte {
	return t.path(m, 0, t.size)
}

func (t tree) path(m, lo, hi uint64) [][]byte {
	if hi-lo == 1 {
		return nil
	}
	k := split(hi - lo)
	if m < lo+k {
		return append(t.path(m, lo, lo+k), t.hash(lo+k, hi))
	}
	return append(t.path(m, lo+k, hi), t.hash(lo, lo+k))
}

// fillerLeaf returns the leaf hash of filler entry i, derived from seed so
// that every tree gets distinct leaves.
func fillerLeaf(seed []byte, i uint64) []byte {
	var idx [8]byte
	binary.BigEndian.PutUint64(idx[:], i)
	return hashLeaf(append(append([]byte("fakestore filler entry\x00"), seed...), idx[:]...))
}
