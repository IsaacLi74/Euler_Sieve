# Formal proof of the Euler Sieve in Lean 4

Paper: https://doi.org/10.5195/pimr.2025.58


This repository contains a Lean 4 proof demonstrating that the Euler Sieve correctly generates:
1. the list of primes between 2 and 𝑛.
2. the least factor function with domain between 2 and 𝑛.


To try out the code:

The code was originally compiled on ran the Lean4 v4.19.0 build for Linux Ubuntu. For now(7/16/2025), You can just simply copy the code into https://live.lean-lang.org/ and run it directly.


Important Note:

At the end of the file, I only proved the sieve’s correctness, I did not prove that the algorithm runs in linear time—only.
