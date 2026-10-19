import PalPow2.Basic

/-! # Main results: conjectures, size of β, three-digit families -/

namespace PalPow2

open Finset

/-! ## Size of the binomial exponent `β(n)` -/

theorem sq_two_pow (a : ℕ) : (2 ^ a) ^ 2 = 4 ^ a := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem two_pow_pred_lt {x : ℕ} (hx : 2 ≤ x) : 2 ^ (x - 1) < 2 ^ x - 1 := by
  have h1 : 2 ^ x = 2 * 2 ^ (x - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 2 ≤ 2 ^ (x - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Integer form of the necessary condition: if `x` is admissible then
`4^(n mod x + ⌊n/x⌋) < (2⌊n/x⌋ + 2) · 4^x`. -/
theorem admissible_necessary {n x : ℕ} (h : Admissible n x) :
    4 ^ (n % x + n / x) < (2 * (n / x) + 2) * 4 ^ x := by
  unfold Admissible at h
  have h1 : 2 ^ (n % x) * M (n / x) < 2 ^ x := by omega
  have h2 : (2 ^ (n % x) * M (n / x)) ^ 2 < (2 ^ x) ^ 2 := by
    exact Nat.pow_lt_pow_left h1 (by norm_num)
  rw [mul_pow, sq_two_pow, sq_two_pow] at h2
  have h3 := M_sq_lower (n / x)
  calc 4 ^ (n % x + n / x) = 4 ^ (n % x) * 4 ^ (n / x) := pow_add _ _ _
    _ ≤ 4 ^ (n % x) * ((2 * (n / x) + 2) * M (n / x) ^ 2) := Nat.mul_le_mul_left _ h3
    _ = (2 * (n / x) + 2) * (4 ^ (n % x) * M (n / x) ^ 2) := by ring
    _ < (2 * (n / x) + 2) * 4 ^ x := Nat.mul_lt_mul_of_pos_left h2 (by omega)

theorem two_mul_add_two_le_two_pow {k : ℕ} (hk : 3 ≤ k) : 2 * k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- An admissible `x` satisfies `n < 2 x^2`; in particular `β(n) → ∞`. -/
theorem admissible_lt {n x : ℕ} (hx : 2 ≤ x) (h : Admissible n x) : n < 2 * x ^ 2 := by
  have hnec := admissible_necessary h
  have hk : n / x < 2 * x := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ (n / x) ≤ 4 ^ (n / x - x) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := two_mul_add_two_le_two_pow (k := n / x) (by omega)
    have h3 : (2 * (n / x) + 2) * 4 ^ x ≤ 4 ^ (n % x + n / x) := by
      calc (2 * (n / x) + 2) * 4 ^ x ≤ 4 ^ (n / x - x) * 4 ^ x :=
            Nat.mul_le_mul_right _ (le_trans h2 h1)
        _ = 4 ^ (n / x) := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
        _ ≤ 4 ^ (n % x + n / x) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdiv := Nat.div_add_mod n x
  have hmod := Nat.mod_lt n (show 0 < x by omega)
  nlinarith

/-- The window lemma: if `k·x ≤ n ≤ k·x + (x - k)` with `k ≤ x`, then `x` is admissible. -/
theorem admissible_of_window {n x k : ℕ} (hx : 2 ≤ x) (hk : k ≤ x) (h1 : k * x ≤ n)
    (h2 : n ≤ k * x + (x - k)) : Admissible n x := by
  unfold Admissible
  by_cases hlt : n < (k + 1) * x
  · have hlt' : n < k * x + x := by rw [add_mul, one_mul] at hlt; exact hlt
    have hdm : n / x = k ∧ n % x = n - k * x := by
      rw [Nat.div_mod_unique (by omega)]
      constructor
      · rw [mul_comm x k]; omega
      · omega
    rw [hdm.1, hdm.2]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [M, Nat.zero_div, Nat.choose_self, mul_one, zero_mul, Nat.sub_zero]
      calc 2 ^ n ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 2 ^ x - 1 := two_pow_pred_lt hx
    · calc 2 ^ (n - k * x) * M k ≤ 2 ^ (n - k * x) * 2 ^ (k - 1) :=
            Nat.mul_le_mul_left _ (M_le_two_pow hpos)
        _ = 2 ^ (n - k * x + (k - 1)) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 2 ^ x - 1 := two_pow_pred_lt hx
  · have hk0 : k = 0 := by
      by_contra hne
      have : (k + 1) * x ≤ n := by omega
      have : k * x + x ≤ k * x + (x - k) := by nlinarith
      omega
    subst hk0
    have hnx : n = x := by
      have : x ≤ n := by simpa using hlt
      omega
    subst hnx
    rw [Nat.mod_self, Nat.div_self (by omega)]
    have := one_lt_two_pow_sub_one hx
    simp [M]
    omega

/-- **Upper bound** `β(n) ≤ ⌊√n⌋ + ⌊√⌊√n⌋⌋ + 2`  (note `⌊√⌊√n⌋⌋ = ⌊n^{1/4}⌋`). -/
theorem beta_le (n : ℕ) : beta n ≤ Nat.sqrt n + Nat.sqrt (Nat.sqrt n) + 2 := by
  obtain ⟨a, ha⟩ : ∃ a, Nat.sqrt n = a := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, Nat.sqrt a = s := ⟨_, rfl⟩
  rw [ha, hs]
  have ha1 : a * a ≤ n := ha ▸ Nat.sqrt_le n
  have ha2 : n < (a + 1) * (a + 1) := ha ▸ Nat.lt_succ_sqrt n
  have hs1 : s * s ≤ a := hs ▸ Nat.sqrt_le a
  have hs2 : a < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt a
  have hsa : s ≤ a := hs ▸ Nat.sqrt_le_self a
  have hexp : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
  rcases Nat.lt_or_ge a 2 with hsmall | ha2'
  · have hn3 : n ≤ 3 := by nlinarith
    have : beta n ≤ 2 := beta_le_of_admissible (le_refl 2) (by interval_cases n <;> decide)
    omega
  rcases Nat.lt_or_ge n (a * a + a) with hB | hA
  · -- case `n - a^2 < a`
    obtain ⟨u, hnu⟩ : ∃ u, n + u = a + 1 + a * a := ⟨a + 1 + a * a - n, by omega⟩
    have hex : ∃ m, u < (m + 1) * (m + 2) := ⟨u, by nlinarith⟩
    obtain ⟨m, hm1, hm2⟩ : ∃ m, u < (m + 1) * (m + 2) ∧ m * (m + 1) ≤ u := by
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; omega
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        push Not at this
        rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega,
          show Nat.find hex - 1 + 2 = Nat.find hex + 1 by omega] at this
    have hu1 : u ≤ a + 1 := by omega
    have hmm : m * m ≤ a := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; omega
      · nlinarith
    have hms : m ≤ s := hs ▸ Nat.le_sqrt.2 hmm
    have hma : m + 1 ≤ a := by nlinarith
    have e : (a - 1 - m) * (a + m + 2) + (m * m + 3 * m + 2) = a * a + a := by
      zify [hma, show m ≤ a - 1 by omega, show 1 ≤ a by omega]
      ring
    have hw : Admissible n (a + m + 2) := by
      apply admissible_of_window (k := a - 1 - m) (by omega) (by omega)
      · nlinarith
      · rw [show a + m + 2 - (a - 1 - m) = 2 * m + 3 by omega]
        nlinarith
    have := beta_le_of_admissible (by omega) hw
    omega
  · -- case `n - a^2 ≥ a`
    obtain ⟨t, hnt⟩ : ∃ t, n + t = 2 * a + 2 + a * a := ⟨2 * a + 2 + a * a - n, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, m = min (Nat.sqrt t) s := ⟨_, rfl⟩
    have hms : m ≤ s := hm ▸ min_le_right _ _
    have hmt1 : m * m ≤ t := by
      have h1 : m ≤ Nat.sqrt t := hm ▸ min_le_left _ _
      have h2 := Nat.sqrt_le t
      have h3 : m * m ≤ Nat.sqrt t * Nat.sqrt t := Nat.mul_self_le_mul_self h1
      omega
    have hmt2 : t ≤ (m + 1) * (m + 1) + 1 := by
      rcases le_total (Nat.sqrt t) s with hle | hle
      · have hm' : m = Nat.sqrt t := by rw [hm]; exact min_eq_left hle
        have h' : t < (Nat.sqrt t + 1) * (Nat.sqrt t + 1) := Nat.lt_succ_sqrt t
        rw [hm']
        omega
      · have hm' : m = s := by rw [hm]; exact min_eq_right hle
        have : t ≤ a + 2 := by omega
        rw [hm']
        omega
    have hma : m ≤ a := le_trans hms hsa
    have e : (a - m) * (a + m + 2) + (m * m + 2 * m) = a * a + 2 * a := by
      zify [hma]
      ring
    have hw : Admissible n (a + m + 2) := by
      apply admissible_of_window (k := a - m) (by omega) (by omega)
      · nlinarith
      · rw [show a + m + 2 - (a - m) = 2 * m + 2 by omega]
        nlinarith
    have := beta_le_of_admissible (by omega) hw
    omega

/-! ## The conjectures of Kreher and Stinson -/

/-- Conjecture (a). -/
def ConjA : Prop := ∀ n ≥ 1, ∃ x, bmin (2 ^ n) = 2 ^ x - 1

/-- Conjecture (b). -/
def ConjB : Prop := ∀ n ≥ 1, BinomialRep (bmin (2 ^ n)) (2 ^ n)

/-- Conjecture (c). -/
def ConjC : Prop := ∀ a ≥ 2, bmin (2 ^ (a ^ 2)) = 2 ^ a - 1

/-- Conjecture (d). -/
def ConjD : Prop := ∀ b, {n | bmin (2 ^ n) = b}.Finite

/-- Conjecture (e). -/
def ConjE : Prop := ∀ n ≥ 1, (bmin (2 ^ n) = 3 ↔ n ≤ 4)

/-- The single conjecture (Conjecture β of the paper): `b(2^n) = 2^β(n) - 1` for all `n ≥ 1`. -/
def ConjBeta : Prop := ∀ n ≥ 1, bmin (2 ^ n) = 2 ^ beta n - 1

theorem conjB_iff_conjBeta : ConjB ↔ ConjBeta :=
  ⟨fun h n hn => (binomialRep_bmin_iff hn).1 (h n hn),
    fun h n hn => (binomialRep_bmin_iff hn).2 (h n hn)⟩

theorem conjA_and_conjB_iff_conjBeta : ConjA ∧ ConjB ↔ ConjBeta :=
  ⟨fun h => conjB_iff_conjBeta.1 h.2,
    fun h => ⟨fun n hn => ⟨beta n, h n hn⟩, conjB_iff_conjBeta.2 h⟩⟩

theorem conjBeta_iff_no_small_pal :
    ConjBeta ↔ ∀ n ≥ 1, ∀ b, 2 ≤ b → b < 2 ^ beta n - 1 → ¬ IsPal b (2 ^ n) :=
  ⟨fun h n hn => bmin_eq_iff.1 (h n hn), fun h n hn => bmin_eq_iff.2 (h n hn)⟩

theorem conjBeta_imp_conjD (hM : ConjBeta) : ConjD := by
  intro b
  apply Set.Finite.subset (Set.finite_lt_nat (2 * b ^ 2 + 1))
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · omega
  · have h := hM n hpos
    rw [hn] at h
    have hβ := beta_spec n
    have hlt := admissible_lt hβ.1 hβ.2
    have hβb : beta n ≤ b := by
      have := Nat.lt_two_pow_self (n := beta n)
      omega
    have : beta n ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hβb 2
    omega

/-- Under Conjecture β, a palindrome `2^n` in base `b` forces `2^β(n) ≤ b + 1` and
`n < 2 β(n)^2`; hence `n < 2 (log₂ (b+1))^2`. -/
theorem conjBeta_pal_bound (hB : ConjBeta) {n b : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b)
    (hpal : IsPal b (2 ^ n)) : 2 ^ beta n ≤ b + 1 ∧ n < 2 * beta n ^ 2 := by
  have h1 := bmin_le_of_isPal hb hpal
  rw [hB n hn] at h1
  have hβ := beta_spec n
  exact ⟨by omega, admissible_lt hβ.1 hβ.2⟩

theorem beta_eq_two_iff (n : ℕ) : beta n = 2 ↔ Admissible n 2 := by
  constructor
  · intro h
    have := (beta_spec n).2
    rwa [h] at this
  · intro h
    exact le_antisymm (beta_le_of_admissible (le_refl 2) h) (beta_spec n).1

theorem admissible_two_iff {n : ℕ} (hn : 1 ≤ n) : Admissible n 2 ↔ n ≤ 4 := by
  constructor
  · intro h
    have h8 := admissible_lt (le_refl 2) h
    norm_num at h8
    interval_cases n <;> first | omega | exact absurd h (by decide)
  · intro h
    interval_cases n <;> decide

theorem conjBeta_imp_conjE (hM : ConjBeta) : ConjE := by
  intro n hn
  rw [hM n hn, ← admissible_two_iff hn, ← beta_eq_two_iff]
  constructor
  · intro h
    have h1 : 2 ^ beta n = 2 ^ 2 := by
      have := Nat.one_le_two_pow (n := beta n)
      norm_num
      omega
    exact Nat.pow_right_injective (le_refl 2) h1
  · intro h
    rw [h]
    norm_num

/-- Theorem 5.1, (ii) ⇔ (iii), for a single `n`. -/
theorem conjAB_n_iff {n : ℕ} (hn : 1 ≤ n) :
    ((∃ x, bmin (2 ^ n) = 2 ^ x - 1) ∧ BinomialRep (bmin (2 ^ n)) (2 ^ n)) ↔
      bmin (2 ^ n) = 2 ^ beta n - 1 :=
  ⟨fun h => (binomialRep_bmin_iff hn).1 h.2,
    fun h => ⟨⟨beta n, h⟩, (binomialRep_bmin_iff hn).2 h⟩⟩

/-- Theorem 5.1, last sentence: if `b(2^n)` is not an overflow base, conjecture (a) for `n`
already gives `b(2^n) = 2^β(n) - 1`. -/
theorem conjA_n_iff {n : ℕ}
    (hno : ∀ x, 2 ≤ x → bmin (2 ^ n) = 2 ^ x - 1 → 2 ^ n < (2 ^ x - 1) ^ (n / x + 1)) :
    (∃ x, bmin (2 ^ n) = 2 ^ x - 1) ↔ bmin (2 ^ n) = 2 ^ beta n - 1 := by
  constructor
  · rintro ⟨x, hx⟩
    have h2 := (bmin_spec (2 ^ n)).1
    have hx2 : 2 ≤ x := by
      by_contra h'
      push Not at h'
      interval_cases x <;> simp at hx <;> omega
    have hpal : IsPal (2 ^ x - 1) (2 ^ n) := hx ▸ (bmin_spec (2 ^ n)).2
    have hadm := carry_lemma hx2 (hno x hx2 hx) hpal
    have hle := bmin_le_binomial n
    have : 2 ^ beta n ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (beta_le_of_admissible hx2 hadm)
    omega
  · intro h
    exact ⟨beta n, h⟩

/-- `⌊√⌊√n⌋⌋ = ⌊n^{1/4}⌋`: the integer `s = Nat.sqrt (Nat.sqrt n)` satisfies
`s^4 ≤ n < (s+1)^4`. -/
theorem sqrt_sqrt_spec (n : ℕ) :
    Nat.sqrt (Nat.sqrt n) ^ 4 ≤ n ∧ n < (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := by
  set a := Nat.sqrt n
  set s := Nat.sqrt a
  have ha1 : a * a ≤ n := Nat.sqrt_le n
  have ha2 : n < (a + 1) * (a + 1) := Nat.lt_succ_sqrt n
  have hs1 : s * s ≤ a := Nat.sqrt_le a
  have hs2 : a < (s + 1) * (s + 1) := Nat.lt_succ_sqrt a
  constructor
  · calc s ^ 4 = (s * s) * (s * s) := by ring
      _ ≤ a * a := Nat.mul_le_mul hs1 hs1
      _ ≤ n := ha1
  · have h3 : a + 1 ≤ (s + 1) * (s + 1) := hs2
    calc n < (a + 1) * (a + 1) := ha2
      _ ≤ ((s + 1) * (s + 1)) * ((s + 1) * (s + 1)) := Nat.mul_le_mul h3 h3
      _ = (s + 1) ^ 4 := by ring

theorem two_mul_le_two_pow_pred {x : ℕ} (hx : 4 ≤ x) : 2 * x ≤ 2 ^ (x - 1) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [show x + 1 - 1 = (x - 1) + 1 by omega, pow_succ]
    omega

/-- Under Conjecture β, for `n ≥ 18` every palindrome of `2^n` in a base `2^x - 1` is binomial;
in particular there are no overflow palindromes. -/
theorem conjBeta_mersenne_binomial (hB : ConjBeta) {n x : ℕ} (hx : 2 ≤ x) (hn : 18 ≤ n)
    (hpal : IsPal (2 ^ x - 1) (2 ^ n)) : Admissible n x := by
  by_cases hov : 2 ^ n < (2 ^ x - 1) ^ (n / x + 1)
  · exact carry_lemma hx hov hpal
  · push Not at hov
    exfalso
    have h1 := overflow_le hx hov
    have hb2 : 2 ≤ 2 ^ x - 1 := by have := one_lt_two_pow_sub_one hx; omega
    have hle := bmin_le_of_isPal hb2 hpal
    rw [hB n (by omega)] at hle
    have hβx : beta n ≤ x := by
      by_contra h'
      push Not at h'
      have : 2 ^ x < 2 ^ beta n := Nat.pow_lt_pow_right (by norm_num) h'
      omega
    have hβ := beta_spec n
    have h2 := admissible_lt hβ.1 hβ.2
    have h3 : beta n ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hβx 2
    have hx3 : x ≤ 3 := by
      by_contra h'
      push Not at h'
      have := two_mul_le_two_pow_pred (show 4 ≤ x by omega)
      nlinarith
    have : x ^ 2 ≤ 9 := by nlinarith
    omega

/-- Under Conjecture β, `2^n` is never a palindrome in an overflow base `2^x - 1`:
for `n ≥ 18` by `conjBeta_mersenne_binomial`, for `n < 18` by a finite check
(only `x ∈ {2, 3}` can give an overflow base there). -/
theorem conjBeta_no_overflow_pal (hB : ConjBeta) {n x : ℕ} (hx : 2 ≤ x)
    (hov : (2 ^ x - 1) ^ (n / x + 1) ≤ 2 ^ n) : ¬ IsPal (2 ^ x - 1) (2 ^ n) := by
  intro hpal
  by_cases hn : 18 ≤ n
  · have hadm := conjBeta_mersenne_binomial hB hx hn hpal
    have hlt := Nat.lt_base_pow_length_digits (b := 2 ^ x - 1) (m := 2 ^ n)
      (one_lt_two_pow_sub_one hx)
    rw [digits_of_admissible hx hadm, length_binDigits] at hlt
    omega
  · push Not at hn
    have h1 := overflow_le hx hov
    have hx3 : x ≤ 3 := by
      by_contra h'
      push Not at h'
      have : 4 * 2 ^ 3 ≤ x * 2 ^ (x - 1) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    interval_cases x <;> interval_cases n <;>
      first
      | exact absurd hov (by decide)
      | exact absurd hpal (by decide)

/-- Under Conjecture β, `2^n` is a palindrome in base `2^x - 1` exactly when `x` is admissible
for `n` (so, by `admissible_lt`, only for `n < 2x^2`). -/
theorem conjBeta_isPal_mersenne_iff (hB : ConjBeta) {n x : ℕ} (hx : 2 ≤ x) :
    IsPal (2 ^ x - 1) (2 ^ n) ↔ Admissible n x := by
  constructor
  · intro hpal
    by_cases hov : 2 ^ n < (2 ^ x - 1) ^ (n / x + 1)
    · exact carry_lemma hx hov hpal
    · push Not at hov
      exact absurd hpal (conjBeta_no_overflow_pal hB hx hov)
  · exact isPal_of_admissible hx

/-- No power of two is a palindrome in an overflow base `2^x - 1`. -/
def NoOverflowPal : Prop :=
  ∀ n x : ℕ, 2 ≤ x → (2 ^ x - 1) ^ (n / x + 1) ≤ 2 ^ n → ¬ IsPal (2 ^ x - 1) (2 ^ n)

/-- Conjecture β is equivalent to conjecture (a) together with the absence of overflow
palindromes. -/
theorem conjBeta_iff_conjA_and_noOverflowPal : ConjBeta ↔ ConjA ∧ NoOverflowPal := by
  constructor
  · intro hB
    exact ⟨(conjA_and_conjB_iff_conjBeta.2 hB).1,
      fun n x hx hov => conjBeta_no_overflow_pal hB hx hov⟩
  · rintro ⟨hA, hN⟩ n hn
    refine (conjA_n_iff ?_).1 (hA n hn)
    intro x hx hbx
    by_contra hov
    push Not at hov
    have hpal : IsPal (2 ^ x - 1) (2 ^ n) := by
      rw [← hbx]
      exact (bmin_spec (2 ^ n)).2
    exact hN n x hx hov hpal

/-! ## Conjecture (c) is false -/

theorem M41 : M 41 = 269128937220 := by
  rw [M, show 41 / 2 = 20 by norm_num, Nat.choose_eq_descFactorial_div_factorial]
  decide

theorem two_M_lt : ∀ a, 40 ≤ a → 2 * M (a + 1) < 2 ^ (a - 1) - 1 := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => rw [M41]; norm_num
  | succ a ha ih =>
    have h1 := M_succ_le (a + 1)
    have h2 : 2 ^ (a + 1 - 1) = 2 * 2 ^ (a - 1) := by
      rw [show a + 1 - 1 = (a - 1) + 1 by omega, pow_succ]
      ring
    rw [h2]
    have : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
    omega

/-- For every `a ≥ 40`, `x = a - 1` is admissible for `n = a^2`. -/
theorem admissible_sq_pred {a : ℕ} (ha : 40 ≤ a) : Admissible (a ^ 2) (a - 1) := by
  have hdm : a ^ 2 / (a - 1) = a + 1 ∧ a ^ 2 % (a - 1) = 1 := by
    rw [Nat.div_mod_unique (by omega)]
    refine ⟨?_, by omega⟩
    zify [show 1 ≤ a by omega]
    ring
  unfold Admissible
  rw [hdm.1, hdm.2, pow_one]
  exact two_M_lt a ha

/-- **Conjecture (c) fails for every `a ≥ 40`:** `b(2^{a^2}) ≤ 2^{a-1} - 1 < 2^a - 1`. -/
theorem bmin_sq_le {a : ℕ} (ha : 40 ≤ a) : bmin (2 ^ (a ^ 2)) ≤ 2 ^ (a - 1) - 1 :=
  bmin_le_of_isPal (by have := one_lt_two_pow_sub_one (show 2 ≤ a - 1 by omega); omega)
    (isPal_of_admissible (by omega) (admissible_sq_pred ha))

theorem bmin_sq_ne {a : ℕ} (ha : 40 ≤ a) : bmin (2 ^ (a ^ 2)) ≠ 2 ^ a - 1 := by
  intro h
  have h1 := bmin_sq_le ha
  rw [h] at h1
  have : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  omega

theorem not_conjC : ¬ ConjC := fun h => bmin_sq_ne (le_refl 40) (h 40 (by norm_num))

/-- The smallest counterexample: `2^1600 = 2·(1+b)^41` is a palindrome in base `b = 2^39 - 1`,
with digits `2·C(41,i)`. -/
theorem digits_two_pow_1600 : Nat.digits (2 ^ 39 - 1) (2 ^ 1600) = binDigits 2 41 := by
  have h := admissible_sq_pred (a := 40) le_rfl
  rw [show (40 : ℕ) ^ 2 = 1600 by norm_num, show (40 : ℕ) - 1 = 39 by norm_num] at h
  rw [digits_of_admissible (by norm_num) h]
  norm_num

theorem isPal_two_pow_1600 : IsPal (2 ^ 39 - 1) (2 ^ 1600) := by
  rw [IsPal, digits_two_pow_1600, binDigits_reverse]

/-! ## Short and long palindromes -/

/-- A palindromic representation with `ℓ` digits, `ℓ·β(n) ≤ n`, lies in a base `> 2^β(n)`. -/
theorem short_base_large {n b : ℕ} (hb : 1 < b)
    (hD : (Nat.digits b (2 ^ n)).length * beta n ≤ n) : 2 ^ beta n < b := by
  have h1 : 2 ^ n < b ^ (Nat.digits b (2 ^ n)).length := Nat.lt_base_pow_length_digits hb
  have h2 : (2 ^ beta n) ^ (Nat.digits b (2 ^ n)).length ≤ 2 ^ n := by
    rw [← pow_mul, mul_comm]
    exact Nat.pow_le_pow_right (by norm_num) hD
  exact lt_of_pow_lt_pow_left₀ _ (by positivity) (lt_of_le_of_lt h2 h1)

/-- A palindromic representation with `ℓ` digits, `(ℓ-1)·β(n) > n`, lies in a base `< 2^β(n)`. -/
theorem long_base_small {n b : ℕ} (hb : 1 < b)
    (hD : n < ((Nat.digits b (2 ^ n)).length - 1) * beta n) : b < 2 ^ beta n := by
  have hne : (2 : ℕ) ^ n ≠ 0 := by positivity
  have h1 : b ^ ((Nat.digits b (2 ^ n)).length - 1) ≤ 2 ^ n := by
    have := Nat.base_pow_length_digits_le b (2 ^ n) hb hne
    have hlen : 1 ≤ (Nat.digits b (2 ^ n)).length := by
      rw [Nat.digits_def' hb (by positivity)]
      simp
    calc b ^ ((Nat.digits b (2 ^ n)).length - 1)
        = b ^ (Nat.digits b (2 ^ n)).length / b := by
          rw [← Nat.pow_div hlen (by omega), pow_one]
      _ ≤ b * 2 ^ n / b := Nat.div_le_div_right this
      _ = 2 ^ n := by rw [Nat.mul_div_cancel_left _ (by omega)]
  have h2 : 2 ^ n < (2 ^ beta n) ^ ((Nat.digits b (2 ^ n)).length - 1) := by
    rw [← pow_mul, mul_comm]
    exact Nat.pow_lt_pow_right (by norm_num) hD
  exact lt_of_pow_lt_pow_left₀ _ (by positivity) (lt_of_le_of_lt h1 h2)

/-! ## Three-digit palindromes: two infinite families -/

theorem digits_three {b c : ℕ} (hb : 1 < b) (hc : c < b) :
    Nat.digits b (b ^ 2 + c * b + 1) = [1, c, 1] := by
  have : b ^ 2 + c * b + 1 = Nat.ofDigits b [1, c, 1] := by
    simp [Nat.ofDigits]
    ring
  rw [this]
  apply Nat.digits_ofDigits b hb
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> omega
  · intro _
    simp

theorem not_binomialRep_of_digits_three {b N c : ℕ} (hd : Nat.digits b N = [1, c, 1])
    (hc : c ≠ 2) : ¬ BinomialRep b N := by
  rintro ⟨α, k, hα, h⟩
  rw [hd] at h
  have hlen := congrArg List.length h
  rw [length_binDigits] at hlen
  simp at hlen
  have hk : k = 2 := by omega
  subst hk
  simp [binDigits, List.range_succ] at h
  omega

/-- Family (i): `n = 6m`, `m ≥ 3`. -/
theorem family_one {m : ℕ} (hm : 3 ≤ m) :
    Nat.digits ((2 ^ m - 1) * (2 ^ (2 * m) - 2 ^ m + 1)) (2 ^ (6 * m)) =
      [1, 2 ^ (2 * m + 2) + 2, 1] := by
  set y := 2 ^ m with hy
  have hy8 : 8 ≤ y := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (2 * m) = y ^ 2 := by rw [hy, ← pow_mul, mul_comm]
  have e2 : 2 ^ (6 * m) = y ^ 6 := by rw [hy, ← pow_mul, mul_comm]
  have e3 : 2 ^ (2 * m + 2) = 4 * y ^ 2 := by rw [pow_add, e1]; ring
  rw [e1, e2, e3]
  have hyy : y ≤ y ^ 2 := by nlinarith
  set b := (y - 1) * (y ^ 2 - y + 1) with hb
  have hbZ : (b : ℤ) = ((y : ℤ) - 1) * ((y : ℤ) ^ 2 - y + 1) := by
    rw [hb]; push_cast [show 1 ≤ y by omega, hyy]; ring
  have hcb : 4 * y ^ 2 + 2 < b := by
    zify
    rw [hbZ]
    nlinarith
  have hval : y ^ 6 = b ^ 2 + (4 * y ^ 2 + 2) * b + 1 := by
    zify
    rw [hbZ]
    ring
  rw [hval]
  exact digits_three (by omega) hcb

/-- Family (ii): `n = 8m + 4`, `m ≥ 2` (Aurifeuillian factorisation). -/
theorem family_two {m : ℕ} (hm : 2 ≤ m) :
    Nat.digits ((2 ^ (2 * m + 1) + 1) * (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1)) (2 ^ (8 * m + 4)) =
      [1, 2 ^ (3 * m + 3) - 2 ^ (2 * m + 2) - 2, 1] := by
  set y := 2 ^ m with hy
  have hy4 : 4 ≤ y := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (2 * m + 1) = 2 * y ^ 2 := by rw [hy, pow_succ, ← pow_mul, mul_comm m]; ring
  have e2 : 2 ^ (m + 1) = 2 * y := by rw [hy, pow_succ]; ring
  have e3 : 2 ^ (8 * m + 4) = 16 * y ^ 8 := by rw [hy, pow_add, ← pow_mul, mul_comm m]; ring
  have e4 : 2 ^ (3 * m + 3) = 8 * y ^ 3 := by rw [hy, pow_add, ← pow_mul, mul_comm m]; ring
  have e5 : 2 ^ (2 * m + 2) = 4 * y ^ 2 := by rw [hy, pow_add, ← pow_mul, mul_comm m]; ring
  rw [e1, e2, e3, e4, e5]
  have h1 : 2 * y ≤ 2 * y ^ 2 := by nlinarith
  have h2 : 4 * y ^ 2 + 2 ≤ 8 * y ^ 3 := by nlinarith
  set b := (2 * y ^ 2 + 1) * (2 * y ^ 2 - 2 * y + 1) with hb
  set c := 8 * y ^ 3 - 4 * y ^ 2 - 2 with hc
  have hbZ : (b : ℤ) = (2 * (y : ℤ) ^ 2 + 1) * (2 * (y : ℤ) ^ 2 - 2 * y + 1) := by
    rw [hb]; push_cast [h1]; ring
  have hc1 : 4 * y ^ 2 ≤ 8 * y ^ 3 := by omega
  have hc2 : 2 ≤ 8 * y ^ 3 - 4 * y ^ 2 := by omega
  have hcZ : (c : ℤ) = 8 * (y : ℤ) ^ 3 - 4 * (y : ℤ) ^ 2 - 2 := by
    rw [hc, Nat.cast_sub hc2, Nat.cast_sub hc1]
    push_cast
    ring
  have hcb : c < b := by
    zify
    rw [hbZ, hcZ]
    nlinarith
  have hval : 16 * y ^ 8 = b ^ 2 + c * b + 1 := by
    zify
    rw [hbZ, hcZ]
    ring
  rw [hval]
  exact digits_three (by omega) hcb

theorem family_one_isPal {m : ℕ} (hm : 3 ≤ m) :
    IsPal ((2 ^ m - 1) * (2 ^ (2 * m) - 2 ^ m + 1)) (2 ^ (6 * m)) ∧
      ¬ BinomialRep ((2 ^ m - 1) * (2 ^ (2 * m) - 2 ^ m + 1)) (2 ^ (6 * m)) := by
  have hd := family_one hm
  refine ⟨by rw [IsPal, hd]; rfl, not_binomialRep_of_digits_three hd ?_⟩
  have : 2 ^ 2 ≤ 2 ^ (2 * m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem family_two_isPal {m : ℕ} (hm : 2 ≤ m) :
    IsPal ((2 ^ (2 * m + 1) + 1) * (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1)) (2 ^ (8 * m + 4)) ∧
      ¬ BinomialRep ((2 ^ (2 * m + 1) + 1) * (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1))
        (2 ^ (8 * m + 4)) := by
  have hd := family_two hm
  refine ⟨by rw [IsPal, hd]; rfl, not_binomialRep_of_digits_three hd ?_⟩
  have h1 : 2 ^ 9 ≤ 2 ^ (3 * m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * m + 2) * 2 ^ (m + 1) = 2 ^ (3 * m + 3) := by
    rw [← pow_add]; congr 1; ring
  have h3 : 2 ≤ 2 ^ (m + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 * 2 ^ (2 * m + 2) ≤ 2 ^ (3 * m + 3) := by
    rw [← h2]; exact Nat.mul_le_mul_left _ h3 |>.trans' (by rw [mul_comm])
  omega

/-! ## `β(a^2) = a` for `2 ≤ a ≤ 39` (kernel computation) -/

/-- A kernel-friendly formula for `M`. -/
theorem M_eq_desc (k : ℕ) : M k = Nat.descFactorial k (k / 2) / Nat.factorial (k / 2) :=
  Nat.choose_eq_descFactorial_div_factorial _ _

/-- Boolean version of admissibility, evaluated by the kernel. -/
def admB (n x : ℕ) : Bool :=
  decide (2 ^ (n % x) * (Nat.descFactorial (n / x) (n / x / 2) / Nat.factorial (n / x / 2))
    < 2 ^ x - 1)

theorem admissible_iff_admB (n x : ℕ) : Admissible n x ↔ admB n x = true := by
  simp [Admissible, admB, M_eq_desc]

theorem beta_sq_table :
    (List.range 40).all (fun a => a < 2 || (admB (a ^ 2) a &&
      (List.range a).all (fun x => x < 2 || !admB (a ^ 2) x))) = true := by
  decide +kernel

theorem beta_sq_eq {a : ℕ} (h2 : 2 ≤ a) (h39 : a ≤ 39) : beta (a ^ 2) = a := by
  have ht := beta_sq_table
  rw [List.all_eq_true] at ht
  have ha := ht a (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at ha
  rcases ha with h | ⟨hadm, hnot⟩
  · omega
  apply le_antisymm (beta_le_of_admissible h2 ((admissible_iff_admB _ _).2 hadm))
  by_contra hlt
  push Not at hlt
  have hs := beta_spec (a ^ 2)
  have := hnot (beta (a ^ 2)) hlt
  rcases this with h | h
  · omega
  · exact absurd ((admissible_iff_admB _ _).1 hs.2) (by simp [h])

/-! ## Proposition 5.4 (short and long palindromes) in full -/

/-- Proposition 5.4(i): a palindrome with `ℓ` digits and `ℓ·β(n) ≤ n` is not minimal. -/
theorem short_not_minimal {n b : ℕ} (hb : 1 < b)
    (hD : (Nat.digits b (2 ^ n)).length * beta n ≤ n) : bmin (2 ^ n) < b :=
  lt_of_le_of_lt (bmin_le_binomial n) (lt_of_le_of_lt (Nat.sub_le _ _) (short_base_large hb hD))

/-- Proposition 5.4(ii): a non-binomial palindrome with `ℓ` digits and `(ℓ-1)·β(n) > n`
contradicts `b(2^n) = 2^β(n) - 1`. -/
theorem long_breaks_beta {n b : ℕ} (hb : 1 < b) (hpal : IsPal b (2 ^ n))
    (hnb : ¬ BinomialRep b (2 ^ n))
    (hD : n < ((Nat.digits b (2 ^ n)).length - 1) * beta n) :
    b < 2 ^ beta n - 1 ∧ bmin (2 ^ n) ≠ 2 ^ beta n - 1 := by
  have h1 := long_base_small hb hD
  have hne : b ≠ 2 ^ beta n - 1 := by
    rintro rfl
    exact hnb (binomialRep_of_admissible (beta_spec n).1 (beta_spec n).2)
  have hlt : b < 2 ^ beta n - 1 := by omega
  exact ⟨hlt, fun h => not_isPal_of_lt_bmin (by omega) (h ▸ hlt) hpal⟩

end PalPow2
