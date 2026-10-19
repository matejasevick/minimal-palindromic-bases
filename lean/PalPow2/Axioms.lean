/-
Axiom audit and sanity checks for PalPow2.
Run with `lake env lean Axioms.lean` after `lake build`.
Every theorem below should depend only on `propext`, `Classical.choice`, `Quot.sound`
(no `sorryAx`, no `Lean.ofReduceBool`, i.e. no `native_decide`).
-/
import PalPow2
open PalPow2

-- Section 2: binomial representations and the minimal base
#print axioms digits_of_admissible
#print axioms admissible_of_binomialRep
#print axioms binomialRep_bmin_iff
#print axioms bmin_eq_iff
#print axioms bmin_le_binomial
#print axioms mersenne_of_isPal_even
-- Section 3: conjecture (c) is false
#print axioms admissible_sq_pred
#print axioms bmin_sq_le
#print axioms bmin_sq_ne
#print axioms not_conjC
#print axioms digits_two_pow_1600
#print axioms isPal_two_pow_1600
#print axioms beta_sq_eq
-- Section 4: carry lemma and overflow
#print axioms carry_lemma
#print axioms isPal_iff_admissible
#print axioms no_overflow
#print axioms no_overflow'
#print axioms overflow_le
#print axioms overflow_small
-- Section 5: the single conjecture
#print axioms reduction
#print axioms conjB_iff_conjBeta
#print axioms conjA_and_conjB_iff_conjBeta
#print axioms conjBeta_iff_no_small_pal
#print axioms conjAB_n_iff
#print axioms conjA_n_iff
#print axioms conjBeta_imp_conjD
#print axioms conjBeta_imp_conjE
#print axioms conjBeta_pal_bound
#print axioms conjBeta_mersenne_binomial
#print axioms conjBeta_no_overflow_pal
#print axioms conjBeta_isPal_mersenne_iff
#print axioms conjBeta_iff_conjA_and_noOverflowPal
#print axioms short_not_minimal
#print axioms long_breaks_beta
-- Section 6: size of beta
#print axioms admissible_lt
#print axioms admissible_of_window
#print axioms beta_le
#print axioms two_M_lt
#print axioms sqrt_sqrt_spec
-- Section 8: three-digit families
#print axioms family_one_isPal
#print axioms family_two_isPal

-- Statements of the headline results
#check @carry_lemma
#check @reduction
#check @conjBeta_imp_conjD
#check @conjBeta_imp_conjE
#check @conjBeta_mersenne_binomial
#check @conjBeta_iff_conjA_and_noOverflowPal
#check @conjBeta_no_overflow_pal
#check @beta_le
#check @not_conjC

-- Sanity check against Table 3 of Kreher–Stinson: (n, b(2^n), β(n)) for n ≤ 30
#eval (List.range 30).map fun n => (n + 1, bmin (2 ^ (n + 1)), beta (n + 1))
