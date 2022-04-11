// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gabt

import (
	"fmt"
)

const (
	LEAF_HEIGHT = 1
	ZERO_HEIGHT = 0
)

type ComparableStringer interface {
	comparable
	fmt.Stringer
}

type Comparable[T any] interface {
	comparable
	Less(T) bool
}

type T[K Comparable[K], D ComparableStringer] struct {
	root *node32[K, D]
	size int
}

type node32[K Comparable[K], D ComparableStringer] struct {
	// Standard conventions hold for left = smaller, right = larger
	left, right *node32[K, D]
	data        D
	key         K
	height_     int8
}

func makeNode[K Comparable[K], D ComparableStringer](key K) *node32[K, D] {
	return &node32[K, D]{key: key, height_: LEAF_HEIGHT}
}

// IsSingle returns true iff t is empty.
func (t *T[K, D]) IsEmpty() bool {
	return t.root == nil
}

// IsSingle returns true iff t is a singleton (leaf).
func (t *T[K, D]) IsSingle() bool {
	return t.root != nil && t.root.isLeaf()
}

// VisitInOrder applies f to the key and ComparableStringerata pairs in t,
// with keys ordered from smallest to largest.
func (t *T[K, D]) VisitInOrder(f func(K, D)) {
	if t.root == nil {
		return
	}
	t.root.visitInOrder(f)
}

func (n *node32[K, D]) nilOrData() D {
	if n == nil {
		var z D
		return z
	}
	return n.data
}

func (n *node32[K, D]) nilOrKeyAndData() (k K, d D) {
	if n == nil {
		var z K
		k = z
		d = zero[D]()
	} else {
		k = n.key
		d = n.data
	}
	return
}

func (n *node32[K, D]) height() int8 {
	if n == nil {
		return 0
	}
	return n.height_
}

func zero[T any]() T {
	var z T
	return z
}

// Find returns the data associated with x in the tree, or
// nil if x is not in the tree.
func (t *T[K, D]) Find(x K) D {
	return t.root.find(x).nilOrData()
}

// Insert either adds x to the tree if x was not previously
// a key in the tree, or updates the data for x in the tree if
// x was already a key in the tree.  The previous data associated
// with x is returned, and is nil if x was not previously a
// key in the tree.
func (t *T[K, D]) Insert(x K, data D) D {
	n := t.root
	var newroot *node32[K, D]
	var o *node32[K, D]
	if n == nil {
		n = makeNode[K, D](x)
		newroot = n
	} else {
		newroot, n, o = n.aInsert(x)
	}
	var r D
	if o != nil {
		r = o.data
	} else {
		t.size++
	}
	n.data = data
	t.root = newroot
	return r
}

func (t *T[K, D]) Copy() *T[K, D] {
	u := *t
	return &u
}

func (t *T[K, D]) Delete(x K) D {
	n := t.root
	var zero D
	if n == nil {
		return zero
	}
	d, s := n.aDelete(x)
	if d == nil {
		return zero
	}
	t.root = s
	t.size--
	return d.data
}

func (t *T[K, D]) DeleteMin() (K, D) {
	n := t.root
	var zk K
	var zd D
	if n == nil {
		return zk, zd
	}
	d, s := n.aDeleteMin()
	if d == nil {
		return zk, zd
	}
	t.root = s
	t.size--
	return d.key, d.data
}

func (t *T[K, D]) DeleteMax() (K, D) {
	n := t.root
	var zk K
	var zd D
	if n == nil {
		return zk, zd
	}
	d, s := n.aDeleteMax()
	if d == nil {
		return zk, zd
	}
	t.root = s
	t.size--
	return d.key, d.data
}

func (t *T[K, D]) Size() int {
	return t.size
}

// Intersection returns the the intersection of T and U, with data modified
// by the result of f(t.data, u.data); if non-nil/zero, that is the stored value,
// if nil, then the entry is not added.  If f is nil, then the data from the
// smaller set is what will be used (this maximizes sharing, if that result
// is acceptable).
func (t *T[K, D]) Intersection(u *T[K, D], f func(x, y D) D) *T[K, D] {
	if t.Size() == 0 || u.Size() == 0 {
		return &T[K, D]{}
	}

	// For faster execution and less allocation, prefer t smaller, iterate over t.
	if t.Size() <= u.Size() {
		v := t.Copy()
		for it := t.Iterator(); !it.IsEmpty(); {
			k, d := it.Next()
			e := u.Find(k)
			if e == zero[D]() {
				v.Delete(k)
				continue
			}
			if f == nil {
				continue
			}
			if c := f(d, e); c != d {
				if c == zero[D]() {
					v.Delete(k)
				} else {
					v.Insert(k, c)
				}
			}
		}
		return v
	}
	v := u.Copy()
	for it := u.Iterator(); !it.IsEmpty(); {
		k, e := it.Next()
		d := t.Find(k)
		if d == zero[D]() {
			v.Delete(k)
			continue
		}
		if f == nil {
			continue
		}
		if c := f(d, e); c != d {
			if c == zero[D]() {
				v.Delete(k)
			} else {
				v.Insert(k, c)
			}
		}
	}

	return v
}

// Union returns the union of t and u, where the result data for any common keys
// is given by f(t's data, u's data) -- f need not be symmetric.  If f returns nil,
// then the key and data are not added to the result.  If f is nil,
// then wherever the sets overlap, the data from the larger set is used.
func (t *T[K, D]) Union(u *T[K, D], f func(x, y D) D) *T[K, D] {
	if t.Size() == 0 {
		return u
	}
	if u.Size() == 0 {
		return t
	}

	if t.Size() >= u.Size() {
		v := t.Copy()
		for it := u.Iterator(); !it.IsEmpty(); {
			k, e := it.Next()
			d := t.Find(k)
			if d == zero[D]() {
				v.Insert(k, e)
				continue
			}
			if f == nil {
				continue
			}
			if c := f(d, e); c != d {
				if c == zero[D]() {
					v.Delete(k)
				} else {
					v.Insert(k, c)
				}
			}
		}
		return v
	}

	v := u.Copy()
	for it := t.Iterator(); !it.IsEmpty(); {
		k, d := it.Next()
		e := u.Find(k)
		if e == zero[D]() {
			v.Insert(k, d)
			continue
		}
		if f == nil {
			continue
		}
		if c := f(d, e); c != d {
			if c == zero[D]() {
				v.Delete(k)
			} else {
				v.Insert(k, c)
			}
		}
	}
	return v
}

// Difference returns the difference of t and u, except as
// modified by f.  If f is nil, or returns nil, then the usual
// difference results, however if it returns not-nil then 
// the entry is not removed and the new valye is used for the data.
func (t *T[K, D]) Difference(u *T[K, D], f func(x, y D) D) *T[K, D] {
	if t.Size() == 0 {
		return &T[K, D]{}
	}
	if u.Size() == 0 {
		return t
	}
	v := t.Copy()
	for it := t.Iterator(); !it.IsEmpty(); {
		k, d := it.Next()
		e := u.Find(k)
		if e != zero[D]() {
			if f == nil {
				v.Delete(k)
				continue
			}
			c := f(d, e)
			if c == zero[D]() {
				v.Delete(k)
				continue
			}
			if c != d {
				v.Insert(k, c)
			}
		}
	}
	return v
}

func (t *T[K, D]) Iterator() Iterator[K, D] {
	return Iterator[K, D]{it: t.root.iterator()}
}

func (t *T[K, D]) Equals(u *T[K, D]) bool {
	if t == u {
		return true
	}
	if t.Size() != u.Size() {
		return false
	}
	return t.root.equals(u.root)
}

// This doesn't build with go1.4, sigh
// func (t *T[K,D]) String() string {
// 	var b strings.Builder
// 	first := true
// 	for it := t.Iterator(); !it.IsEmpty(); {
// 		k, v := it.Next()
// 		if first {
// 			first = false
// 		} else {
// 			b.WriteString("; ")
// 		}
// 		b.WriteString(strconv.FormatInt(int64(k), 10))
// 		b.WriteString(":")
// 		b.WriteString(v.String())
// 	}
// 	return b.String()
// }

func (t *T[K, D]) String() string {
	var b string
	first := true
	for it := t.Iterator(); !it.IsEmpty(); {
		k, v := it.Next()
		if first {
			first = false
		} else {
			b += ("; ")
		}
		b += fmt.Sprintf("%v", k)
		b += (":")
		b += (v.String())
	}
	return b
}

func (t *node32[K, D]) equals(u *node32[K, D]) bool {
	if t == u {
		return true
	}
	it, iu := t.iterator(), u.iterator()
	for !it.isEmpty() && !iu.isEmpty() {
		nt := it.next()
		nu := iu.next()
		if nt == nu {
			continue
		}
		if nt.key != nu.key {
			return false
		}
		if nt.data.String() != nu.data.String() {
			return false
		}
	}
	return it.isEmpty() == iu.isEmpty()
}

func (t *T[K, D]) Equiv(u *T[K, D], eqv func(x, y D) bool) bool {
	if t == u {
		return true
	}
	if t.Size() != u.Size() {
		return false
	}
	return t.root.equiv(u.root, eqv)
}

func (t *node32[K, D]) equiv(u *node32[K, D], eqv func(x, y D) bool) bool {
	if t == u {
		return true
	}
	it, iu := t.iterator(), u.iterator()
	for !it.isEmpty() && !iu.isEmpty() {
		nt := it.next()
		nu := iu.next()
		if nt == nu {
			continue
		}
		if nt.key != nu.key {
			return false
		}
		if !eqv(nt.data, nu.data) {
			return false
		}
	}
	return it.isEmpty() == iu.isEmpty()
}

type iterator[K Comparable[K], D ComparableStringer] struct {
	parents []*node32[K, D]
}

type Iterator[K Comparable[K], D ComparableStringer] struct {
	it iterator[K, D]
}

func (it *Iterator[K, D]) Next() (K, D) {
	x := it.it.next()
	if x == nil {
		return zero[K](), zero[D]()
	}
	return x.key, x.data
}

func (it *Iterator[K, D]) IsEmpty() bool {
	return len(it.it.parents) == 0
}

func (t *node32[K, D]) iterator() iterator[K, D] {
	if t == nil {
		return iterator[K, D]{}
	}
	it := iterator[K, D]{parents: make([]*node32[K, D], 0, int(t.height()))}
	it.leftmost(t)
	return it
}

func (it *iterator[K, D]) leftmost(t *node32[K, D]) {
	for t != nil {
		it.parents = append(it.parents, t)
		t = t.left
	}
}

func (it *iterator[K, D]) isEmpty() bool {
	return len(it.parents) == 0
}

func (it *iterator[K, D]) next() *node32[K, D] {
	l := len(it.parents)
	if l == 0 {
		return nil
	}
	x := it.parents[l-1] // return value
	if x.right != nil {
		it.leftmost(x.right)
		return x
	}
	// discard visited top of parents
	l--
	it.parents = it.parents[:l]
	y := x // y is known visited/returned
	for l > 0 && y == it.parents[l-1].right {
		y = it.parents[l-1]
		l--
		it.parents = it.parents[:l]
	}

	return x
}

// Min returns the minimum element of t.
// If t is empty, then (nil, nil) is returned.
func (t *T[K, D]) Min() (k K, d D) {
	return t.root.min().nilOrKeyAndData()
}

// Max returns the maximum element of t.
// If t is empty, then (nil, nil) is returned.
func (t *T[K, D]) Max() (k K, d D) {
	return t.root.max().nilOrKeyAndData()
}

// Glb returns the greatest-lower-bound-exclusive of x and the associated
// data.  If x has no glb in the tree, then (nil, nil) is returned.
func (t *T[K, D]) Glb(x K) (k K, d D) {
	return t.root.glb(x, false).nilOrKeyAndData()
}

// GlbEq returns the greatest-lower-bound-inclusive of x and the associated
// data.  If x has no glbEQ in the tree, then (nil, nil) is returned.
func (t *T[K, D]) GlbEq(x K) (k K, d D) {
	return t.root.glb(x, true).nilOrKeyAndData()
}

// Lub returns the least-upper-bound-exclusive of x and the associated
// data.  If x has no lub in the tree, then (nil, nil) is returned.
func (t *T[K, D]) Lub(x K) (k K, d D) {
	return t.root.lub(x, false).nilOrKeyAndData()
}

// LubEq returns the least-upper-bound-inclusive of x and the associated
// data.  If x has no lubEq in the tree, then (nil, nil) is returned.
func (t *T[K, D]) LubEq(x K) (k K, d D) {
	return t.root.lub(x, true).nilOrKeyAndData()
}

func (t *node32[K, D]) isLeaf() bool {
	return t.left == nil && t.right == nil && t.height_ == LEAF_HEIGHT
}

func (t *node32[K, D]) visitInOrder(f func(K, D)) {
	if t.left != nil {
		t.left.visitInOrder(f)
	}
	f(t.key, t.data)
	if t.right != nil {
		t.right.visitInOrder(f)
	}
}

func (t *node32[K, D]) find(key K) *node32[K, D] {
	for t != nil {
		if key.Less(t.key) {
			t = t.left
		} else if t.key.Less(key) {
			t = t.right
		} else {
			return t
		}
	}
	return nil
}

func (t *node32[K, D]) min() *node32[K, D] {
	if t == nil {
		return t
	}
	for t.left != nil {
		t = t.left
	}
	return t
}

func (t *node32[K, D]) max() *node32[K, D] {
	if t == nil {
		return t
	}
	for t.right != nil {
		t = t.right
	}
	return t
}

func (t *node32[K, D]) glb(key K, allow_eq bool) *node32[K, D] {
	var best *node32[K, D] = nil
	for t != nil {
		if !t.key.Less(key) { // key <= t.key == ! key > t.key == !t.key.Less(key)
			if allow_eq && key == t.key {
				return t
			}
			// t is too big, glb is to left.
			t = t.left
		} else {
			// t is a lower bound, record it and seek a better one.
			best = t
			t = t.right
		}
	}
	return best
}

func (t *node32[K, D]) lub(key K, allow_eq bool) *node32[K, D] {
	var best *node32[K, D] = nil
	for t != nil {
		if !key.Less(t.key) { // key >= t.key == !key.Less(t.key)
			if allow_eq && key == t.key {
				return t
			}
			// t is too small, lub is to right.
			t = t.right
		} else {
			// t is a upper bound, record it and seek a better one.
			best = t
			t = t.left
		}
	}
	return best
}

func (t *node32[K, D]) aInsert(x K) (newroot, newnode, oldnode *node32[K, D]) {
	// oldnode default of nil is good, others should be assigned.
	if x == t.key {
		oldnode = t
		newt := *t
		newnode = &newt
		newroot = newnode
		return
	}
	if x.Less(t.key) {
		if t.left == nil {
			t = t.copy()
			n := makeNode[K, D](x)
			t.left = n
			newnode = n
			newroot = t
			t.height_ = 2 // was balanced w/ 0, sibling is height 0 or 1
			return
		}
		var new_l *node32[K, D]
		new_l, newnode, oldnode = t.left.aInsert(x)
		t = t.copy()
		t.left = new_l
		if new_l.height() > 1+t.right.height() {
			newroot = t.aLeftIsHigh(newnode)
		} else {
			t.height_ = 1 + max(t.left.height(), t.right.height())
			newroot = t
		}
	} else { // x > t.key
		if t.right == nil {
			t = t.copy()
			n := makeNode[K, D](x)
			t.right = n
			newnode = n
			newroot = t
			t.height_ = 2 // was balanced w/ 0, sibling is height 0 or 1
			return
		}
		var new_r *node32[K, D]
		new_r, newnode, oldnode = t.right.aInsert(x)
		t = t.copy()
		t.right = new_r
		if new_r.height() > 1+t.left.height() {
			newroot = t.aRightIsHigh(newnode)
		} else {
			t.height_ = 1 + max(t.left.height(), t.right.height())
			newroot = t
		}
	}
	return
}

func (t *node32[K, D]) aDelete(key K) (deleted, newSubTree *node32[K, D]) {
	if t == nil {
		return nil, nil
	}

	if key.Less(t.key) {
		oh := t.left.height()
		d, tleft := t.left.aDelete(key)
		if tleft == t.left {
			return d, t
		}
		return d, t.copy().aRebalanceAfterLeftDeletion(oh, tleft)
	} else if t.key.Less(key) {
		oh := t.right.height()
		d, tright := t.right.aDelete(key)
		if tright == t.right {
			return d, t
		}
		return d, t.copy().aRebalanceAfterRightDeletion(oh, tright)
	}

	if t.height() == LEAF_HEIGHT {
		return t, nil
	}

	// Interior delete by removing left.Max or right.Min,
	// then swapping contents
	if t.left.height() > t.right.height() {
		oh := t.left.height()
		d, tleft := t.left.aDeleteMax()
		r := t
		t = t.copy()
		t.data, t.key = d.data, d.key
		return r, t.aRebalanceAfterLeftDeletion(oh, tleft)
	}

	oh := t.right.height()
	d, tright := t.right.aDeleteMin()
	r := t
	t = t.copy()
	t.data, t.key = d.data, d.key
	return r, t.aRebalanceAfterRightDeletion(oh, tright)
}

func (t *node32[K, D]) aDeleteMin() (deleted, newSubTree *node32[K, D]) {
	if t == nil {
		return nil, nil
	}
	if t.left == nil { // leaf or left-most
		return t, t.right
	}
	oh := t.left.height()
	d, tleft := t.left.aDeleteMin()
	if tleft == t.left {
		return d, t
	}
	return d, t.copy().aRebalanceAfterLeftDeletion(oh, tleft)
}

func (t *node32[K, D]) aDeleteMax() (deleted, newSubTree *node32[K, D]) {
	if t == nil {
		return nil, nil
	}

	if t.right == nil { // leaf or right-most
		return t, t.left
	}

	oh := t.right.height()
	d, tright := t.right.aDeleteMax()
	if tright == t.right {
		return d, t
	}
	return d, t.copy().aRebalanceAfterRightDeletion(oh, tright)
}

func (t *node32[K, D]) aRebalanceAfterLeftDeletion(oldLeftHeight int8, tleft *node32[K, D]) *node32[K, D] {
	t.left = tleft

	if oldLeftHeight == tleft.height() || oldLeftHeight == t.right.height() {
		// this node is still balanced and its height is unchanged
		return t
	}

	if oldLeftHeight > t.right.height() {
		// left was larger
		t.height_--
		return t
	}

	// left height fell by 1 and it was already less than right height
	t.right = t.right.copy()
	return t.aRightIsHigh(nil)
}

func (t *node32[K, D]) aRebalanceAfterRightDeletion(oldRightHeight int8, tright *node32[K, D]) *node32[K, D] {
	t.right = tright

	if oldRightHeight == tright.height() || oldRightHeight == t.left.height() {
		// this node is still balanced and its height is unchanged
		return t
	}

	if oldRightHeight > t.left.height() {
		// left was larger
		t.height_--
		return t
	}

	// right height fell by 1 and it was already less than left height
	t.left = t.left.copy()
	return t.aLeftIsHigh(nil)
}

// aRightIsHigh does rotations necessary to fix a high right child
// assume that t and t.right are already fresh copies.
func (t *node32[K, D]) aRightIsHigh(newnode *node32[K, D]) *node32[K, D] {
	right := t.right
	if right.right.height() < right.left.height() {
		// double rotation
		if newnode != right.left {
			right.left = right.left.copy()
		}
		t.right = right.leftToRoot()
	}
	t = t.rightToRoot()
	return t
}

// aLeftIsHigh does rotations necessary to fix a high left child
// assume that t and t.left are already fresh copies.
func (t *node32[K, D]) aLeftIsHigh(newnode *node32[K, D]) *node32[K, D] {
	left := t.left
	if left.left.height() < left.right.height() {
		// double rotation
		if newnode != left.right {
			left.right = left.right.copy()
		}
		t.left = left.rightToRoot()
	}
	t = t.leftToRoot()
	return t
}

// rightToRoot does that rotation, modifying t and t.right in the process.
func (t *node32[K, D]) rightToRoot() *node32[K, D] {
	//    this
	// left  right
	//      rl   rr
	//
	// becomes
	//
	//       right
	//    this   rr
	// left  rl
	//
	right := t.right
	rl := right.left
	right.left = t
	// parent's child ptr fixed in caller
	t.right = rl
	t.height_ = 1 + max(rl.height(), t.left.height())
	right.height_ = 1 + max(t.height(), right.right.height())
	return right
}

// leftToRoot does that rotation, modifying t and t.left in the process.
func (t *node32[K, D]) leftToRoot() *node32[K, D] {
	//     this
	//  left  right
	// ll  lr
	//
	// becomes
	//
	//    left
	//   ll  this
	//      lr  right
	//
	left := t.left
	lr := left.right
	left.right = t
	// parent's child ptr fixed in caller
	t.left = lr
	t.height_ = 1 + max(lr.height(), t.right.height())
	left.height_ = 1 + max(t.height(), left.left.height())
	return left
}

func max(a, b int8) int8 {
	if a > b {
		return a
	}
	return b
}

func (t *node32[K, D]) copy() *node32[K, D] {
	u := *t
	return &u
}
