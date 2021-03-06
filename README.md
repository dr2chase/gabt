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

The `abt` subdirectory contains the original, and is there for benchmarking comparison.

Known flaws:<br>
- Think before you just bang in `x - y` for signed int Compare, that is vulnerable to to overflow.  I was tempted to use floating point instead, since that would actually work, and lack branches.
- nil won't work as either key or value.
- the generic idiom for an all-types nil value is
  ```
  var nilT T
  ... nilT ...
  ```
- I didn't implement `Split(k K)` which would return the two trees on either side of the key `k`.
- benchmarking is far from comprehensive.
