# Sum of Squares Computation

This repository contains code in Coq that computes the representation of a prime number as a sum of squares.

The method used is Fermat's descent method which, given a, b such that (a^2 + b^2 | p), outputs a smaller c and d such that (c^2 + d^2 | p).

Because this relies on an initial solution, this can only be done for primes such that x^2 = - y^2 mod p is solvable, which reduces to -1 being a quadratic residue (i.e. there is some x such that x^2 = -1 mod p).  Number theory tells us that -1 is only a quadratic residue to for primes p such that p mod 4 = 1.

## Examples

Let's find a representation for 4349 as a sum of squares.  (A random prime I took from Wikipedia.)

First, we use Sage to discover a number x such that x^2 = -1 mod 4349:

```
sage: Mod(-1, 4349).sqrt()
608
sage: (608 * 608) % 4349
4348
```

Therefore, 4349 divides 608^2 + 1^2.  Using the `descent` function here (representing a single step in the descent), we have:

```
Compute descent 608 1 4349.
   = (2, 93, -7)
```

This result says that 2 * 4349 = 93^2 + 7^2.  To get a representation of 4349 as a sum of squares we apply the descent step again:

```
Compute descent 93 (-7) 4349.
   = (1, 43, -50)
```

Therefore 1 * 4349 = 43^2 + 50^2 and we are finished with the descent.

## Functions In This Repo

* `descent` - single step in the descent.
* `prime_sum_of_squares` - compute for a prime its sum of squares representation

The final type of the term showing correctness of the procedure is:

```
Theorem prime_sum_of_squares_works: forall a b p u v,
    prime p ->
    p > 0 ->
    a * a + b * b > 0 ->
    a * a + b * b < p * p ->
    (p | a*a + b*b) ->
    (u, v) = prime_sum_of_squares a b p ->
    u * u + v * v = p.
```

Thus given appropriate arguments `a`, `b` such that `p | (a * a + b * b = p)`, it outputs numbers `(u, v)` such that `p = u * u + v * v`.  `p` must be prime and the initial arguments must not exceed `p * p`.

## References

* A Friendly Introduction to Number Theory, Silverman 4th Edition (Chapter 26)
