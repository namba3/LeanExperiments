# Arithmetic verification

[Verification catalog](../verification.en.md) | [日本語](arithmetic.md)

## Factorial

Source: `LeanExperiments/Verification/Factorial/Spec.lean`

### General theorems

- The tail-recursive implementation agrees with its mathematical recursive specification for every input.
- The proofs establish positivity, monotone nondecrease, and strict increase when `1 ≤ m < n` (with the `0! = 1!` exception).
- They establish `2^n ≤ (n+1)!`, `n! ≤ n^n` (`0^0 = 1`), `k ∣ n!` when `1 ≤ k ≤ n`, and `m! ∣ n! ↔ m ≤ n ∨ (m = 1 ∧ n = 0)`.
- They also prove that a finite product of factorials divides the factorial of the argument sum, and give the factorial addition identity using a rising factorial.
- They also prove `2 ∣ n! ↔ 2 ≤ n` and `n! % 2 = 1 ↔ n ≤ 1`.

### Verification scope

No separate bounded-domain check is listed. The all-input agreement theorem is the implementation's correctness evidence.

## Fibonacci

Source: `LeanExperiments/Verification/Fibonacci/Spec.lean`

### General theorems

- The fast-doubling implementation agrees at every index with a specification defined by the ordinary recurrence. The implementation recurrence, positivity, monotonicity, and strict increase from index 2 are also proved.
- Positivity and ordering properties of the pair returned by fast doubling are established; the implementation returns zero only at index zero.
- The proofs establish the addition identity `F(m+n+1) = F(m)F(n) + F(m+1)F(n+1)`, both doubling identities, prefix-sum and sum-of-squares identities, and coprimality of adjacent terms.
- They establish the growth bounds `2^n ≤ F(2n+1)`, `2^(n/2) ≤ F(n+1)`, and `F(n) ≤ 2^n`.
- A general periodicity theorem follows from residue conditions immediately before and at a period. A second lemma lifts a finite residue table to an all-index divisibility equivalence.
- Evenness is characterized by `2 ∣ F(n) ↔ 3 ∣ n`. The following divisibility equivalences are also proved:

| Modulus | Residue period | Divisibility condition |
| ---: | ---: | --- |
| 5 | 20 | `5 ∣ F(n) ↔ 5 ∣ n` |
| 7 | 16 | `7 ∣ F(n) ↔ 8 ∣ n` |
| 8 | 12 | `8 ∣ F(n) ↔ 6 ∣ n` |
| 11 | 10 | `11 ∣ F(n) ↔ 10 ∣ n` |
| 13 | 28 | `13 ∣ F(n) ↔ 7 ∣ n` |
| 16 | 24 | `16 ∣ F(n) ↔ 12 ∣ n` |
| 17 | 36 | `17 ∣ F(n) ↔ 9 ∣ n` |
| 19 | 18 | `19 ∣ F(n) ↔ 18 ∣ n` |
| 23 | 48 | `23 ∣ F(n) ↔ 24 ∣ n` |
| 29 | 14 | `29 ∣ F(n) ↔ 14 ∣ n` |
| 31 | 30 | `31 ∣ F(n) ↔ 30 ∣ n` |
| 37 | 76 | `37 ∣ F(n) ↔ 19 ∣ n` |
| 41 | 40 | `41 ∣ F(n) ↔ 20 ∣ n` |
| 47 | 32 | `47 ∣ F(n) ↔ 16 ∣ n` |

The general period and multiple-period theorems cover moduli `5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 47`.

### Finite checks

- The implementation is compared with the specification for every index from 0 through 512.
- It is also checked immediately before, at, and after powers of two from 2 through 65,536.
- The exact values of `F(100)` and `F(1000)` are checked.

## Prime factorization

Source: `LeanExperiments/Verification/PrimeFactors/Spec.lean`

### General theorems

- For every input at most 1, the implementation returns an empty array; the separate theorems for 0 and 1 follow from this general result.
- For trial divisor `d` and remainder `r`, general lemmas prove that the termination measure `r - d` decreases both when division updates the remainder and when the candidate is incremented.
- An invariant proof for the trial-division loop establishes for every input that the product of emitted factors times the remainder equals the input, the candidate remains at least 2, and every emitted factor is at least 2.
- The loop contract is connected to the returned array: for every input at least 2, the product of returned factors equals the input.
- The same invariant proves that every factor in the returned array is at least 2 for inputs at least 2.
- A loop invariant proves for every input that no value from 2 up to the current trial divisor (exclusive) divides the current remainder. On division, it uses that a divisor of the quotient also divides the pre-division remainder; on increment, it uses that the previous candidate did not divide the remainder.
- From this invariant and the fact that the current candidate divides the remainder, a general theorem proves that every factor emitted by the trial-division loop is prime.
- Assuming the remainder after the loop is at most 1 or prime, a general theorem proves that the returned array satisfies the independent `FactorsCorrect` specification for product, ascending order, and primality.
- A loop invariant that distinguishes the exit state proves that the candidate squared exceeds the remainder at termination. If the remainder were composite, Mathlib's bound on the square of its least prime factor would make that factor smaller than the current candidate, contradicting the invariant that excludes smaller divisors. Thus the remainder is prime whenever it exceeds 1.
- Combining these results, `primeFactors_correct` proves that the implementation satisfies the independent `FactorsCorrect` specification for every natural number.
- For two nonzero inputs, factoring their product equals merge-sorting the concatenation of the two implementation outputs. This composes the specification's multiplication closure with uniqueness; zero is explicitly excluded because its factor list is empty.
- For two nonzero inputs, the count of any value in the product's implementation output is the sum of its counts in the two input outputs. This order-independent multiplicity law also holds for values that are not prime.
- The implementation output multiplicity for gcd and lcm is characterized for all inputs. With two nonzero inputs, gcd uses the smaller multiplicity and lcm the larger; cases involving zero follow this specification's empty-factor-list convention.
- For every input and natural exponent, the implementation output for the power equals the specification's repeated merge construction. For input zero, the result is zero or one and both have the specified empty factor list. The multiplicity of every natural number is the exponent times its original multiplicity, including zero multiplicity for nonprime values.
- A single theorem states that every returned factor is at least 2, divides the input, and is no greater than the input for inputs at least 2. Divisibility follows from the product property and product preservation.
- A loop invariant for the increasing candidate and emitted-factor bounds proves that the returned factor list is ascending, including the final remainder when it is appended.
- The finite primality checker is connected to both the absence of proper divisors and a multiplicative primality condition.
- From a correct factor list, the proofs derive primality of each factor, the lower bound 2, divisibility of the input by each factor, and that each factor is no greater than the input.
- For inputs at least 2, the factor list is nonempty and its product equals the input. A list has length one exactly when the input is prime.
- For nonzero inputs, divisibility by the `k`th power of a prime is equivalent to that prime occurring at least `k` times in the implementation's returned array.
- If there are `k` factors, then `2^k ≤ n`. Correct factor lists are unique, and an empty correct list occurs exactly for inputs 0 or 1.
- Two correct factor lists are equal exactly when their inputs are equal or both inputs are at most 1. The same characterization holds for implementation outputs, exposing 0 and 1 as the only distinct inputs that map to the same empty array.
- More generally, divisibility by any nonzero divisor is characterized by comparing each prime exponent of the divisor with its multiplicity in the implementation's returned array.
- For a nonzero input, being squarefree is equivalent to the implementation returning a duplicate-free factor array.
- Being a power with any positive exponent is equivalent to every prime multiplicity in the returned array being divisible by that exponent; this generalizes the even-multiplicity condition for squares.
- For every natural number, its multiplicity in the implementation's output equals its exponent in `Nat.factorization`; nonprime values therefore occur zero times.
- For every input, each returned factor is prime, divides the input, and is at most the input. For inputs at most 1, the returned list is empty, so the per-factor condition holds vacuously.

### Finite checks

- Product, ascending order, and primality are checked for every input from 0 through 20,000.
- Checks cover values around `49²`, `121²`, `961²`, `1009²`, `10007²`, and `1000003²`, as well as large primes, semiprimes, and repeated factors.
- Complete specifications are checked for `2⁶⁴−1 = 3·5·17·257·641·65537·6700417`, `2⁶⁴` as 64 factors of 2, and the factorizations of `2¹²⁸` and `2²⁵⁶`.

### Remaining work

General correctness of the prime-factorization implementation is proved. The specification requires an empty list for inputs at most 1; for larger inputs it requires product preservation, ascending order, and primality of every factor. Finite checks provide additional regression coverage for selected boundary and large values.
