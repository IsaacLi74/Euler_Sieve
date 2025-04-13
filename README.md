# Formal proof of the Euler Sieve in Lean 4

This repository contains a Lean 4 proof demonstrating that the Euler Sieve correctly generates:
1. the list of primes between 2 and 𝑛.
2. the least factor function with domain between 2 and 𝑛.


To try out the code:

You can just simply copy the code into https://live.lean-lang.org/ and run it with mathlib stable.


Important Note:

At the end of the file, I only proved the sieve’s correctness, I did not prove that the algorithm runs in linear time—only.
