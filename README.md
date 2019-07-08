# Sum of Squares Computation

This repository contains code in Coq that computes the representation of a prime number as a sum of squares.

The method used is Fermat's descent method which, given a, b such that (a^2 + b^2 | p), outputs a smaller c and d such that (c^2 + d^2 | p).

Because this relies on an initial solution, this can only be done for primes such that x^2 = - y^2 mod p is solvable, which reduces to -1 being a quadratic residue.  This is only true for primes p such that p mod 4 = 1.
