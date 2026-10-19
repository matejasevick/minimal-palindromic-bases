# Minimal palindromic bases of powers of two
This repository accompanies the paper Minimal palindromic bases of powers of two. Kreher and Stinson conjectured that the least base in which 2^n is a palindrome always has the form 2^x − 1, with a representation that is a multiple of a row of Pascal’s triangle. The code here verifies the explicit formula b(2^n) = 2^β(n) − 1 for all n ≤ 1000. It also confirms that the conjecture b(2^{a²}) = 2^a − 1 holds exactly for a ≤ 39 (it fails for all a ≥ 40). Further runs check base 3 up to n = 10^10 and all bases below 2^16 in the tested ranges. The Lean 4 project (Mathlib v4.34.1) formalizes the paper’s combinatorial results with no sorry, using only the standard axioms.
Code, data, computation logs and Lean formalization for the paper

> M. Matijasevick, *Minimal palindromic bases of powers of two*.

| folder | contents |
|---|---|
| `code/` | C and Python programs for Sections 8, 10 and 12, the tables of β(n) (n ≤ 1500 exact, n ≤ 10^6 floating point with exact tie checks), and the n ≤ 60 enumeration. See `code/README.md`. |
| `runs/` | Unedited output logs of the computations (C1)–(C5) and the positive controls. See `runs/README.md`. |
| `lean/PalPow2/` | Lean 4 formalization (Lean v4.34.1 pinned in `lean-toolchain`, Mathlib v4.34.1 pinned by commit in `lake-manifest.json`). No `sorry`, no `native_decide`; only the axioms `propext`, `Classical.choice`, `Quot.sound`. See `lean/PalPow2/README.md`. |

Quick start for the Lean project:

```
cd lean/PalPow2
lake exe cache get
lake build
lake env lean Axioms.lean
```

Section and result numbers in the READMEs refer to the paper.
