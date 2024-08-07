// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gabt

import (
	"fmt"
	"math/rand"
	"strconv"
	"testing"

	"github.com/dr2chase/gabt/abt"
)

type sstring struct {
	s string
}

func (s sstring) String() string {
	return s.s
}

var z sstring

func stringer(s string) sstring {
	return sstring{s}
}

type Int32 int32

func (x Int32) Compare(y Int32) int {
	if x < y {
		return -1
	}
	if x > y {
		return 1
	}
	return 0
}

func makeTree(te *testing.T, x []int32, check bool) (t *T[Int32, sstring], k int, minimum, maximum Int32) {
	t = &T[Int32, sstring]{}
	k = 0
	minimum = Int32(0x7fffffff)
	maximum = Int32(-0x80000000)
	history := []*T[Int32, sstring]{}

	for _, di := range x {
		d := Int32(di + di) // double everything for Glb/Lub testing.

		if check {
			history = append(history, t.Copy())
		}

		t.Insert(Int32(d), stringer(fmt.Sprintf("%v", d)))

		k++
		if d < minimum {
			minimum = d
		}
		if d > maximum {
			maximum = d
		}

		if !check {
			continue
		}

		for j, old := range history {
			s, i := wellFormed(old)
			if s != "" {
				te.Errorf("Old tree consistency problem %v at k=%d, j=%d, old=\n%v, t=\n%v", s, k, j, old.DebugString(), t.DebugString())
				return
			}
			if i != j {
				te.Errorf("Wrong tree size %v, expected %v for old %v", i, j, old.DebugString())
			}
		}
		s, i := wellFormed(t)
		if s != "" {
			te.Errorf("Tree consistency problem at %v", s)
			return
		}
		if i != k {
			te.Errorf("Wrong tree size %v, expected %v for %v", i, k, t.DebugString())
			return
		}
		if t.Size() != k {
			te.Errorf("Wrong t.Size() %v, expected %v for %v", t.Size(), k, t.DebugString())
			return
		}
	}
	return
}

func applicInsert(te *testing.T, x []int32) {
	makeTree(te, x, true)
}

func applicFind(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)

	for _, di := range x {
		d := Int32(di + di) // double everything for Glb/Lub testing.
		s := fmt.Sprintf("%v", d)
		f := t.Find(d)

		// data
		if s != f.String() {
			te.Errorf("s(%v) != f(%v)", s, f)
		}
	}
}

func applicBounds(te *testing.T, x []int32) {
	t, _, minimum, maximum := makeTree(te, x, false)
	for _, di := range x {
		d := Int32(di + di) // double everything for Glb/Lub testing.
		s := fmt.Sprintf("%v", d)

		kg, g := t.Glb(d + 1)
		kge, ge := t.GlbEq(d)
		kl, l := t.Lub(d - 1)
		kle, le := t.LubEq(d)

		// keys
		if d != kg {
			te.Errorf("d(%v) != kg(%v)", d, kg)
		}
		if d != kl {
			te.Errorf("d(%v) != kl(%v)", d, kl)
		}
		if d != kge {
			te.Errorf("d(%v) != kge(%v)", d, kge)
		}
		if d != kle {
			te.Errorf("d(%v) != kle(%v)", d, kle)
		}
		// data
		if s != g.String() {
			te.Errorf("s(%v) != g(%v)", s, g)
		}
		if s != l.String() {
			te.Errorf("s(%v) != l(%v)", s, l)
		}
		if s != ge.String() {
			te.Errorf("s(%v) != ge(%v)", s, ge)
		}
		if s != le.String() {
			te.Errorf("s(%v) != le(%v)", s, le)
		}
	}

	for _, di := range x {
		d := Int32(di + di) // double everything for Glb/Lub testing.
		s := fmt.Sprintf("%v", d)
		kge, ge := t.GlbEq(d + 1)
		kle, le := t.LubEq(d - 1)
		if d != kge {
			te.Errorf("d(%v) != kge(%v)", d, kge)
		}
		if d != kle {
			te.Errorf("d(%v) != kle(%v)", d, kle)
		}
		if s != ge.String() {
			te.Errorf("s(%v) != ge(%v)", s, ge)
		}
		if s != le.String() {
			te.Errorf("s(%v) != le(%v)", s, le)
		}
	}

	_, g := t.Glb(minimum)
	_, ge := t.GlbEq(minimum - 1)
	_, l := t.Lub(maximum)
	_, le := t.LubEq(maximum + 1)
	fmin := t.Find(minimum - 1)
	fmax := t.Find(maximum + 1)

	// if kg != NOT_KEY32 || kge != NOT_KEY32 || kl != NOT_KEY32 || kle != NOT_KEY32 {
	// 	te.Errorf("Got non-error-key for missing query")
	// }

	if g != z || ge != z || l != z || le != z || fmin != z || fmax != z {
		te.Errorf("Got non-error-data for missing query")
	}
}

func applicDeleteMin(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)
	_, size := wellFormed(t)
	history := []*T[Int32, sstring]{}
	for !t.IsEmpty() {
		k, _ := t.Min()
		history = append(history, t.Copy())
		kd, _ := t.DeleteMin()
		if kd != k {
			te.Errorf("Deleted minimum key %v not equal to minimum %v", kd, k)
		}
		for j, old := range history {
			s, i := wellFormed(old)
			if s != "" {
				te.Errorf("Tree consistency problem %s at old after DeleteMin, old=\n%stree=\n%v", s, old.DebugString(), t.DebugString())
				return
			}
			if i != len(x)-j {
				te.Errorf("Wrong old tree size %v, expected %v after DeleteMin, old=\n%vtree\n%v", i, len(x)-j, old.DebugString(), t.DebugString())
				return
			}
		}
		size--
		s, i := wellFormed(t)
		if s != "" {
			te.Errorf("Tree consistency problem at %v after DeleteMin, tree=\n%v", s, t.DebugString())
			return
		}
		if i != size {
			te.Errorf("Wrong tree size %v, expected %v after DeleteMin", i, size)
			return
		}
		if t.Size() != size {
			te.Errorf("Wrong t.Size() %v, expected %v for %v", t.Size(), i, t.DebugString())
			return
		}
	}
}

func applicDeleteMax(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)
	_, size := wellFormed(t)
	history := []*T[Int32, sstring]{}

	for !t.IsEmpty() {
		k, _ := t.Max()
		history = append(history, t.Copy())
		kd, _ := t.DeleteMax()
		if kd != k {
			te.Errorf("Deleted maximum key %v not equal to maximum %v", kd, k)
		}

		for j, old := range history {
			s, i := wellFormed(old)
			if s != "" {
				te.Errorf("Tree consistency problem %s at old after DeleteMin, old=\n%stree=\n%v", s, old.DebugString(), t.DebugString())
				return
			}
			if i != len(x)-j {
				te.Errorf("Wrong old tree size %v, expected %v after DeleteMin, old=\n%vtree\n%v", i, len(x)-j, old.DebugString(), t.DebugString())
				return
			}
		}

		size--
		s, i := wellFormed(t)
		if s != "" {
			te.Errorf("Tree consistency problem at %v after DeleteMax, tree=\n%v", s, t.DebugString())
			return
		}
		if i != size {
			te.Errorf("Wrong tree size %v, expected %v after DeleteMax", i, size)
			return
		}
		if t.Size() != size {
			te.Errorf("Wrong t.Size() %v, expected %v for %v", t.Size(), i, t.DebugString())
			return
		}
	}
}

func applicDelete(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)
	_, size := wellFormed(t)
	history := []*T[Int32, sstring]{}

	missing := t.Delete(11)
	if missing != z {
		te.Errorf("Returned a value when there should have been none, %v", missing)
		return
	}

	s, i := wellFormed(t)
	if s != "" {
		te.Errorf("Tree consistency problem at %v after delete of missing value, tree=\n%v", s, t.DebugString())
		return
	}
	if size != i {
		te.Errorf("Delete of missing data should not change tree size, expected %d, got %d", size, i)
		return
	}

	for _, di := range x {
		d := Int32(di + di) // double
		vWant := fmt.Sprintf("%v", d)
		history = append(history, t.Copy())
		v := t.Delete(d)

		for j, old := range history {
			s, i := wellFormed(old)
			if s != "" {
				te.Errorf("Tree consistency problem %s at old after DeleteMin, old=\n%stree=\n%v", s, old.DebugString(), t.DebugString())
				return
			}
			if i != len(x)-j {
				te.Errorf("Wrong old tree size %v, expected %v after DeleteMin, old=\n%vtree\n%v", i, len(x)-j, old.DebugString(), t.DebugString())
				return
			}
		}

		if v.s != vWant {
			te.Errorf("Deleted %v expected %v but got %v", d, vWant, v)
			return
		}
		size--
		s, i := wellFormed(t)
		if s != "" {
			te.Errorf("Tree consistency problem at %v after Delete %d, tree=\n%v", s, d, t.DebugString())
			return
		}
		if i != size {
			te.Errorf("Wrong tree size %v, expected %v after Delete", i, size)
			return
		}
		if t.Size() != size {
			te.Errorf("Wrong t.Size() %v, expected %v for %v", t.Size(), i, t.DebugString())
			return
		}
	}

}

func applicIterator(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)
	it := t.ToIter()
	for it.More() {
		k0, d0 := it.Next()
		k1, d1 := t.DeleteMin()
		if k0 != k1 || d0 != d1 {
			te.Errorf("Iterator and deleteMin mismatch, k0, k1, d0, d1 = %v, %v, %v, %v", k0, k1, d0, d1)
			return
		}
	}
	if t.Size() != 0 {
		te.Errorf("Iterator ended early, remaining tree = \n%s", t.DebugString())
		return
	}
}

func applicDoAll(te *testing.T, x []int32) {
	t, _, _, _ := makeTree(te, x, false)

	j := 0
	yield := func(i Int32, s sstring) bool {
		j++
		si := stringer(strconv.FormatInt(int64(i), 10))
		if s != si {
			te.Errorf("s(%s) != si(%s) for i (%s)", s.String(), si, strconv.FormatInt(int64(i), 10))
			return false
		}
		if j > 0 {
			fmt.Print(", ")
		}
		fmt.Printf("[%s %s]", strconv.FormatInt(int64(i), 10), s.String())
		return true
	}

	t.DoAll2(yield)
	fmt.Printf("\n")
	if t.Size() != j {
		te.Errorf("t.Size() (%d) != j (%d)", t.Size(), j)
		return
	}
}

func applicEquals(te *testing.T, x, y []int32) {
	t, _, _, _ := makeTree(te, x, false)
	u, _, _, _ := makeTree(te, y, false)
	if !Equals(t, t) {
		te.Errorf("Equals failure, t == t, =\n%v", t.DebugString())
		return
	}
	if !Equals(t, t.Copy()) {
		te.Errorf("Equals failure, t == t.Copy(), =\n%v", t.DebugString())
		return
	}
	if !Equals(t, u) {
		te.Errorf("Equals failure, t == u, =\n%v", t.DebugString())
		return
	}
	v := t.Copy()

	v.DeleteMax()
	if Equals(t, v) {
		te.Errorf("!Equals failure, t != v, =\n%v\nand%v\n", t.DebugString(), v.DebugString())
		return
	}

	if Equals(v, u) {
		te.Errorf("!Equals failure, v != u, =\n%v\nand%v\n", v.DebugString(), u.DebugString())
		return
	}

}

func tree(x []int32) *T[Int32, sstring] {
	t := &T[Int32, sstring]{}
	for _, d := range x {
		t.Insert(Int32(d), stringer(fmt.Sprintf("%v", d)))
	}
	return t
}

func treePlus1(x []int32) *T[Int32, sstring] {
	t := &T[Int32, sstring]{}
	for _, d := range x {
		t.Insert(Int32(d), stringer(fmt.Sprintf("%v", d+1)))
	}
	return t
}
func TestApplicInsert(t *testing.T) {
	applicInsert(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicInsert(t, []int32{1, 2, 3, 4})
	applicInsert(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicInsert(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicInsert(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicInsert(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicInsert(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicInsert(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}

func TestApplicFind(t *testing.T) {
	applicFind(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicFind(t, []int32{1, 2, 3, 4})
	applicFind(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicFind(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicFind(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicFind(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicFind(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicFind(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}

func TestBounds(t *testing.T) {
	applicBounds(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicBounds(t, []int32{1, 2, 3, 4})
	applicBounds(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicBounds(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicBounds(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicBounds(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicBounds(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicBounds(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestDeleteMin(t *testing.T) {
	applicDeleteMin(t, []int32{1, 2, 3, 4})
	applicDeleteMin(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicDeleteMin(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicDeleteMin(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicDeleteMin(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDeleteMin(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDeleteMin(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicDeleteMin(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestDeleteMax(t *testing.T) {
	applicDeleteMax(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicDeleteMax(t, []int32{1, 2, 3, 4})
	applicDeleteMax(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicDeleteMax(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicDeleteMax(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDeleteMax(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDeleteMax(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicDeleteMax(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestDelete(t *testing.T) {
	applicDelete(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicDelete(t, []int32{1, 2, 3, 4})
	applicDelete(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicDelete(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicDelete(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDelete(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDelete(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicDelete(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestIterator(t *testing.T) {
	applicIterator(t, []int32{1, 2, 3, 4})
	applicIterator(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicIterator(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicIterator(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicIterator(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicIterator(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicIterator(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicIterator(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestDoAll2(t *testing.T) {
	applicDoAll(t, []int32{1, 2, 3, 4})
	applicDoAll(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9})
	applicDoAll(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25})
	applicDoAll(t, []int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicDoAll(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDoAll(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicDoAll(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24})
	applicDoAll(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}
func TestEquals(t *testing.T) {
	applicEquals(t, []int32{1, 2, 3, 4}, []int32{4, 3, 2, 1})

	applicEquals(t, []int32{24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25},
		[]int32{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25})
	applicEquals(t, []int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1},
		[]int32{25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1})
	applicEquals(t, []int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24},
		[]int32{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2})
}

func first(x, y sstring) sstring {
	return x
}
func second(x, y sstring) sstring {
	return y
}
func alwaysNil(x, y sstring) sstring {
	return z
}
func smaller(x, y sstring) sstring {
	xi, _ := strconv.Atoi(x.String())
	yi, _ := strconv.Atoi(y.String())
	if xi < yi {
		return x
	}
	return y
}
func assert(t *testing.T, expected, got *T[Int32, sstring], what string) {
	s, _ := wellFormed(got)
	if s != "" {
		t.Errorf("Tree consistency problem %v for 'got' in assert for %s, tree=\n%v", s, what, got.DebugString())
		return
	}

	if !Equals(expected, got) {
		t.Errorf("%s fail, expected\n%vgot\n%v\n", what, expected.DebugString(), got.DebugString())
	}
}

func TestSetOps(t *testing.T) {
	A := tree([]int32{1, 2, 3, 4})
	B := tree([]int32{3, 4, 5, 6, 7})

	AIB := tree([]int32{3, 4})
	ADB := tree([]int32{1, 2})
	BDA := tree([]int32{5, 6, 7})
	AUB := tree([]int32{1, 2, 3, 4, 5, 6, 7})
	AXB := tree([]int32{1, 2, 5, 6, 7})

	aib1 := Intersection(A, B, first)
	assert(t, AIB, aib1, "aib1")
	if A.Find(3) != aib1.Find(3) {
		t.Errorf("Failed aliasing/reuse check, A/aib1")
	}
	aib2 := Intersection(A, B, second)
	assert(t, AIB, aib2, "aib2")
	if B.Find(3) != aib2.Find(3) {
		t.Errorf("Failed aliasing/reuse check, B/aib2")
	}
	aib3 := Intersection(B, A, first)
	assert(t, AIB, aib3, "aib3")
	if A.Find(3) != aib3.Find(3) {
		// A is smaller, intersection favors reuse from smaller when function is "first"
		t.Errorf("Failed aliasing/reuse check, A/aib3")
	}
	aib4 := Intersection(B, A, second)
	assert(t, AIB, aib4, "aib4")
	if A.Find(3) != aib4.Find(3) {
		t.Errorf("Failed aliasing/reuse check, A/aib4")
	}

	aub1 := Union(A, B, first)
	assert(t, AUB, aub1, "aub1")
	if B.Find(3) != aub1.Find(3) {
		// B is larger, union favors reuse from larger when function is "first"
		t.Errorf("Failed aliasing/reuse check, A/aub1")
	}
	aub2 := Union(A, B, second)
	assert(t, AUB, aub2, "aub2")
	if B.Find(3) != aub2.Find(3) {
		t.Errorf("Failed aliasing/reuse check, B/aub2")
	}
	aub3 := Union(B, A, first)
	assert(t, AUB, aub3, "aub3")
	if B.Find(3) != aub3.Find(3) {
		t.Errorf("Failed aliasing/reuse check, B/aub3")
	}
	aub4 := Union(B, A, second)
	assert(t, AUB, aub4, "aub4")
	if A.Find(3) != aub4.Find(3) {
		t.Errorf("Failed aliasing/reuse check, A/aub4")
	}

	axb1 := Union(A, B, alwaysNil)
	assert(t, AXB, axb1, "axb1")
	axb2 := Union(B, A, alwaysNil)
	assert(t, AXB, axb2, "axb2")

	adb := Difference(A, B, alwaysNil)
	assert(t, ADB, adb, "adb")
	bda := Difference(B, A, nil)
	assert(t, BDA, bda, "bda")

	Ap1 := treePlus1([]int32{1, 2, 3, 4})

	ada1_1 := Difference(A, Ap1, smaller)
	assert(t, A, ada1_1, "ada1_1")
	ada1_2 := Difference(Ap1, A, smaller)
	assert(t, A, ada1_2, "ada1_2")

}

// wellFormed ensures that a red-black tree meets
// all of its invariants and returns a string identifying
// the first problem encountered. If there is no problem
// then the returned string is empty. The size is also
// returned to allow comparison of calculated tree size
// with expected.
func wellFormed(t *T[Int32, sstring]) (s string, i int) {
	if t.root == nil {
		s = ""
		i = 0
		return
	}
	return wellFormedSubtree(t.root, nil, -0x80000000, 0x7fffffff)
}

// wellFormedSubtree ensures that a red-black subtree meets
// all of its invariants and returns a string identifying
// the first problem encountered. If there is no problem
// then the returned string is empty. The size is also
// returned to allow comparison of calculated tree size
// with expected.
func wellFormedSubtree(t, parent *node[Int32, sstring], keyMin, keyMax Int32) (s string, i int) {
	i = -1 // initialize to a failing value
	s = "" // s is the reason for failure; empty means okay.

	if keyMin >= t.key {
		s = " keyMin >= t.key"
		return
	}

	if keyMax <= t.key {
		s = " keyMax <= t.key"
		return
	}

	l := t.left
	r := t.right

	lh := l.height()
	rh := r.height()
	mh := max(lh, rh)
	th := t.height()
	dh := lh - rh
	if dh < 0 {
		dh = -dh
	}
	if dh > 1 {
		s = fmt.Sprintf(" dh > 1, t=%d", t.key)
		return
	}

	if l == nil && r == nil {
		if th != LEAF_HEIGHT {
			s = " leaf height wrong"
			return
		}
	}

	if th != mh+1 {
		s = " th != mh + 1"
		return
	}

	if l != nil {
		if th <= lh {
			s = " t.height <= l.height"
		} else if th > 2+lh {
			s = " t.height > 2+l.height"
		} else if t.key <= l.key {
			s = " t.key <= l.key"
		}
		if s != "" {
			return
		}

	}

	if r != nil {
		if th <= rh {
			s = " t.height <= r.height"
		} else if th > 2+rh {
			s = " t.height > 2+r.height"
		} else if t.key >= r.key {
			s = " t.key >= r.key"
		}
		if s != "" {
			return
		}
	}

	ii := 1
	if l != nil {
		res, il := wellFormedSubtree(l, t, keyMin, t.key)
		if res != "" {
			s = ".L" + res
			return
		}
		ii += il
	}
	if r != nil {
		res, ir := wellFormedSubtree(r, t, t.key, keyMax)
		if res != "" {
			s = ".R" + res
			return
		}
		ii += ir
	}
	i = ii
	return
}

func (t *T[K, D]) DebugString() string {
	if t.root == nil {
		return ""
	}
	return t.root.DebugString(0)
}

// DebugString prints the tree with nested information
// to allow an eyeball check on the tree balance.
func (t *node[K, D]) DebugString(indent int) string {
	s := ""
	if t.left != nil {
		s = s + t.left.DebugString(indent+1)
	}
	for i := 0; i < indent; i++ {
		s = s + "    "
	}
	s = s + fmt.Sprintf("%v=%v:%d\n", t.key, t.data, t.height_)
	if t.right != nil {
		s = s + t.right.DebugString(indent+1)
	}
	return s
}

var values []sstring
var random1000Indices []Int32
var ordered []Int32
var gTree T[Int32, sstring]
var aTree abt.T

const N = 1000

func init() {
	for i := Int32(0); i < N; i++ {
		values = append(values, stringer(fmt.Sprintf("v%d", i)))
		ordered = append(ordered, i)
		gTree.Insert(i, values[i])
		aTree.Insert(int32(i), values[i])
	}
	random1000Indices = append(random1000Indices, ordered...)
	rand.Shuffle(N, func(i, j int) {
		random1000Indices[i], random1000Indices[j] = random1000Indices[j], random1000Indices[i]
	})
}

func insertN(N Int32) T[Int32, sstring] {
	if N > Int32(len(values)) {
		for i := Int32(len(values)); i < N; i++ {
			values[i] = stringer(fmt.Sprintf("v%d", i))
			ordered = append(ordered, i)
		}
	}
	tree := T[Int32, sstring]{}
	for j := Int32(0); j < N; j++ {
		jj := ordered[j]
		tree.Insert(jj, values[jj])
	}
	return tree
}

func BenchmarkGInsertSeq1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		t := insertN(1000)
		if t.Size() != 1000 {
			panic("Wrong size!")
		}
	}
}

func BenchmarkGInsertRand1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		tree := T[Int32, sstring]{}
		for j := Int32(0); j < N; j++ {
			jj := random1000Indices[j]
			tree.Insert(jj, values[jj])
		}
		if tree.Size() != 1000 {
			panic("Wrong size!")
		}
	}
}

func BenchmarkGFindSeq1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for j := Int32(0); j < N; j++ {
			jj := ordered[j]
			v := gTree.Find(jj)
			if v.s == "" {
				panic("Unexpected empty result")
			}
		}

	}
}

func BenchmarkGFindRand1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for j := Int32(0); j < N; j++ {
			jj := random1000Indices[j]
			v := gTree.Find(jj)
			if v.s == "" {
				panic("Unexpected empty result")
			}
		}
	}
}

func BenchmarkGIterate1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		sum := int32(0)
		for it := gTree.ToIter(); it.More(); {
			k, _ := it.Next()
			sum += int32(k)
		}
		if sum == -1 {
			panic("Should not happen")
		}
	}
}

// not generic

func BenchmarkNGInsertSeq1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		tree := abt.T{}
		for j := Int32(0); j < N; j++ {
			jj := ordered[j]
			tree.Insert(int32(jj), values[jj])
		}
		if tree.Size() != 1000 {
			panic("Wrong size!")
		}
	}
}

func BenchmarkNGInsertRand1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		tree := abt.T{}
		for j := Int32(0); j < N; j++ {
			jj := random1000Indices[j]
			tree.Insert(int32(jj), values[jj])
		}
		if tree.Size() != 1000 {
			panic("Wrong size!")
		}
	}
}

func BenchmarkNGFindSeq1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for j := Int32(0); j < N; j++ {
			jj := int32(ordered[j])
			v := aTree.Find(jj)
			if v.(sstring).s == "" {
				panic("Unexpected empty result")
			}
		}

	}
}

func BenchmarkNGFindRand1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for j := Int32(0); j < N; j++ {
			jj := random1000Indices[j]
			v := aTree.Find(int32(jj))
			if v.(sstring).s == "" {
				panic("Unexpected empty result")
			}
		}
	}
}

func BenchmarkNGIterate1000(b *testing.B) {
	for i := 0; i < b.N; i++ {
		sum := int32(0)
		for it := aTree.Iterator(); !it.IsEmpty(); {
			k, _ := it.Next()
			sum += k
		}
		if sum == -1 {
			panic("Should not happen")
		}
	}
}
