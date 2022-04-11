# Gabt

This is an experimental use of Go generics with an applicative balanced binary tree that has most of the bells and whistles.
An "applicative" binary tree is one that never modifies the structure of an existing tree, and instead allocates a new spine to reflect any deletions or insertions.  This does use more storage for single insertions and deletions, but also results in sharing, so that the cost to store all N sets generated by N insertions is O(N log(N)), and not O(N<sup>2</sup>).

This was also an experiment of how quickly non-generic code can be
rewritten into generic form, given Go's compiler error messages and
a little bit of experience with generics already.  In this case it
took an hour, with the assistance of a colleague staring over my shoulder
and catching my mistakes.

All of this is in theory subject to change at any moment, however this is a
generic version of relatively well-tested non-generic code that may get used in
the Go compiler, so reasons for change would involve tweaking the interface,
not a wholesale rewrite.

Known flaws:<br>
- Think before you just bang in `x < y` for Less if the type is floating point, NaN is not your friend.  I recommend storing as the integer bit pattern instead in whatever Less-able type you use to wrap it.
- nil won't work as either key or value.
- the generic idiom for an all-types nil value is
  ```
  var nilT T
  ... nilT ...
  ```
- I didn't implement `Split(k K)` which would return the two trees on either side of the key `k`.
