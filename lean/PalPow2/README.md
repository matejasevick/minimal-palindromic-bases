# PalPow2 — Lean 4 formalization for "Minimal palindromic bases of powers of two"

This project formalizes the algebraic and combinatorial results of the paper in Lean 4 with Mathlib.
It contains no `sorry` and no `native_decide`. The computations it needs (the value of `C(41,20)`,
the table `β(a²) = a` for `a ≤ 39`, and a finite check of 36 small cases in
`conjBeta_no_overflow_pal`) are checked by the kernel with `decide`. Every theorem depends only on
the three standard axioms `propext`, `Classical.choice`, `Quot.sound` (see `AXIOMS.txt`, produced by
`Axioms.lean`).

## Build

Tested with Lean `v4.34.1` and Mathlib `v4.34.1` (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`,
pinned in `lake-manifest.json`).

```
lake exe cache get          # download prebuilt Mathlib
lake build                  # builds PalPow2 (about a minute on top of Mathlib)
lake env lean Axioms.lean   # axiom audit, plus the table of b(2^n), β(n) for n ≤ 30
```

## Definitions

| Lean | meaning |
|---|---|
| `IsPal b N` | the base-`b` digit list of `N` is a palindrome |
| `binDigits α k` | the list `[α·C(k,0), …, α·C(k,k)]` |
| `BinomialRep b N` | the base-`b` digits of `N` are `binDigits α k` for some `α ≥ 1`, `k` |
| `M k` | `C(k, ⌊k/2⌋)` |
| `Admissible n x` | `2^(n mod x) · M(⌊n/x⌋) < 2^x − 1` |
| `bmin N` | least `b ≥ 2` with `IsPal b N` (the paper's `b(N)`) |
| `beta n` | least `x ≥ 2` with `Admissible n x` |
| `ConjA` … `ConjE` | conjectures (a)–(e) of Kreher and Stinson |
| `ConjBeta` | `∀ n ≥ 1, bmin (2^n) = 2^(beta n) − 1` (Conjecture β) |
| `NoOverflowPal` | `2^n` is never a palindrome in an overflow base `2^x − 1` |

`PalPow2/Basic.lean` contains the definitions, Lemmas 2.1 and 2.2, Section 4 and the core of
Theorem 5.1; `PalPow2/Results.lean` contains everything else.

## Main theorems

| paper | Lean |
|---|---|
| Lemma 2.1 (binomial forms) | `digits_of_admissible`, `binomialRep_of_admissible`, `admissible_of_binomialRep`, `bmin_le_binomial` |
| Lemma 2.2 (central binomial coefficients) | `M_succ_le`, `M_le_two_pow`, `M_sq_lower`, `centralBinom_sq_lower`, `centralBinom_sq_upper` |
| Lemma 2.3 (conditions for admissibility) | `admissible_of_window`, `admissible_necessary`, `admissible_lt` |
| Theorem 3.1 (conjecture (c) is false) | `admissible_sq_pred`, `bmin_sq_le`, `bmin_sq_ne`, `not_conjC`, `digits_two_pow_1600`, `beta_sq_eq` |
| Proposition 3.2, the value `A₁ = 40` | `two_M_lt`, `admissible_sq_pred`, `beta_sq_eq` |
| Theorem 4.1 (carry lemma) | `carry_lemma`, `isPal_iff_admissible`, `no_overflow`, `no_overflow'` |
| Corollary 4.3 (overflow bases) | `carry_lemma`, `overflow_le`, `overflow_small` |
| Theorem 5.1 | `binomialRep_bmin_iff`, `conjAB_n_iff`, `bmin_eq_iff`, `reduction`, `mersenne_of_isPal_even`, `conjA_n_iff` |
| Corollary 5.2 | `conjB_iff_conjBeta`, `conjA_and_conjB_iff_conjBeta`, `conjBeta_pal_bound`, `conjBeta_imp_conjD`, `conjBeta_imp_conjE` |
| Proposition 5.3 (β ⇔ (a) + no overflow palindromes) | `conjBeta_mersenne_binomial`, `conjBeta_no_overflow_pal`, `conjBeta_iff_conjA_and_noOverflowPal`, `conjBeta_isPal_mersenne_iff` |
| Proposition 5.4 (short and long palindromes) | `short_base_large`, `short_not_minimal`, `long_base_small`, `long_breaks_beta` |
| Theorem 6.1(i) (upper bound on β) | `beta_le`, `sqrt_sqrt_spec` |
| Proposition 8.1 (three-digit families) | `family_one`, `family_two`, `family_one_isPal`, `family_two_isPal` |

Two statements differ slightly in form from the paper: the sufficient condition `k+1 < b ln 2` of
Theorem 4.1 is formalized as the integer conditions `2(k+1) < b` (`no_overflow`) and `n < x·2^(x−1)`
(`no_overflow'`), and Theorem 6.1(i) is stated with `Nat.sqrt (Nat.sqrt n)`, which equals `⌊n^{1/4}⌋`
by `sqrt_sqrt_spec`.

## Not formalized

Theorem 6.1(ii),(iii) (lower bound and limits of β), Theorem 7.1 (density), Proposition 3.2 beyond
`A₁`, Remarks 5.5 and 5.6, the discussions of Sections 9 and 12, and all computer searches of
Section 10 (including the computer-assisted half of Theorem 1.1, that (c) holds for `a ≤ 39`).
