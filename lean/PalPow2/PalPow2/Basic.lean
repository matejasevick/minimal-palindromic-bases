/-
Palindromic representations of powers of two: formal verification of the
structural results.

Companion to the paper "Minimal palindromic bases of powers of two" (M. Matijasevick).
Checked with Lean 4.34.1 and Mathlib v4.34.1.  No `sorry`, no `native_decide`.
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Palindrome
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify

namespace PalPow2

open Finset

/-! ## Definitions -/

/-- `IsPal b n`: the base-`b` digits of `n` read the same in both directions. -/
def IsPal (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

instance (b n : ℕ) : Decidable (IsPal b n) := by unfold IsPal; infer_instance

/-- The little-endian digit list `[α·C(k,0), α·C(k,1), …, α·C(k,k)]`. -/
def binDigits (α k : ℕ) : List ℕ := (List.range (k + 1)).map fun i => α * k.choose i

/-- The base-`b` representation of `N` has *binomial form* (Kreher–Stinson). -/
def BinomialRep (b N : ℕ) : Prop := ∃ α k : ℕ, 0 < α ∧ Nat.digits b N = binDigits α k

/-- The largest binomial coefficient of row `k`, `M(k) = C(k, ⌊k/2⌋)`. -/
def M (k : ℕ) : ℕ := k.choose (k / 2)

/-- `x` is *admissible* for `n` when `2^(n mod x) · M(⌊n/x⌋) < 2^x - 1`. -/
def Admissible (n x : ℕ) : Prop := 2 ^ (n % x) * M (n / x) < 2 ^ x - 1

instance (n x : ℕ) : Decidable (Admissible n x) := by unfold Admissible; infer_instance

/-! ## Elementary facts about `M` -/

theorem M_succ_le (m : ℕ) : M (m + 1) ≤ 2 * M m := by
  unfold M
  rcases h : (m + 1) / 2 with _ | j
  · have := Nat.choose_pos (Nat.div_le_self m 2)
    simp only [Nat.choose_zero_right]
    omega
  · rw [Nat.choose_succ_succ']
    have h1 := Nat.choose_le_middle j m
    have h2 := Nat.choose_le_middle (j + 1) m
    omega

theorem M_le_two_pow {k : ℕ} (hk : 1 ≤ k) : M k ≤ 2 ^ (k - 1) := by
  -- odd case: C(2m+1, m) ≤ 4^m
  have hodd : ∀ m, M (2 * m + 1) ≤ 2 ^ (2 * m) := fun m => by
    unfold M
    rw [show (2 * m + 1) / 2 = m by omega, pow_mul]
    simpa using Nat.choose_middle_le_pow m
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have h1 := M_succ_le (2 * j + 1)
    have h2 := hodd j
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    rw [show 2 * j + 1 + 1 - 1 = 2 * j + 1 by omega, pow_succ]
    omega
  · simpa using hodd m

theorem M_pos (k : ℕ) : 0 < M k := Nat.choose_pos (Nat.div_le_self k 2)

/-- `16^m ≤ 4 m · C(2m,m)^2` for `m ≥ 1` (i.e. `C(2m,m) ≥ 4^m / (2√m)`). -/
theorem centralBinom_sq_lower : ∀ m, 1 ≤ m → 16 ^ m ≤ 4 * m * (Nat.centralBinom m) ^ 2
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [Nat.centralBinom, Nat.choose]
  | m + 2, _ => by
    have ih := centralBinom_sq_lower (m + 1) (by omega)
    have hrec := Nat.succ_mul_centralBinom_succ (m + 1)
    set c := Nat.centralBinom (m + 1)
    set c' := Nat.centralBinom (m + 2)
    -- (m+2) c' = 2 (2m+3) c
    have key : (m + 2) * (16 ^ (m + 2)) ≤ (m + 2) * (4 * (m + 2) * c' ^ 2) := by
      have e1 : (m + 2) * (4 * (m + 2) * c' ^ 2) = 4 * ((m + 2) * c') ^ 2 := by ring
      rw [e1, show m + 1 + 1 = m + 2 by ring] at *
      rw [hrec]
      have e2 : (m + 2) * 16 ^ (m + 2) = 16 * ((m + 2) * 16 ^ (m + 1)) := by ring
      rw [e2]
      calc 16 * ((m + 2) * 16 ^ (m + 1))
          ≤ 16 * ((m + 2) * (4 * (m + 1) * c ^ 2)) := by gcongr
        _ ≤ 4 * (2 * (2 * (m + 1) + 1) * c) ^ 2 := by nlinarith [sq_nonneg c]
    exact Nat.le_of_mul_le_mul_left key (by omega)

/-- `(3m+1) · C(2m,m)^2 ≤ 16^m` (i.e. `C(2m,m) ≤ 4^m / √(3m+1)`). -/
theorem centralBinom_sq_upper : ∀ m, (3 * m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := centralBinom_sq_upper m
    have hrec := Nat.succ_mul_centralBinom_succ m
    set c := Nat.centralBinom m
    set c' := Nat.centralBinom (m + 1)
    have key : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2) ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2) = (3 * m + 4) * ((m + 1) * c') ^ 2 := by
        ring
      rw [e, hrec]
      have h1 : (3 * m + 4) * (2 * (2 * m + 1) * c) ^ 2 ≤ 16 * (m + 1) ^ 2 * ((3 * m + 1) * c ^ 2) := by
        nlinarith [Nat.zero_le (m * c ^ 2)]
      calc (3 * m + 4) * (2 * (2 * m + 1) * c) ^ 2
          ≤ 16 * (m + 1) ^ 2 * ((3 * m + 1) * c ^ 2) := h1
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- `4^k ≤ (2k+2) · M(k)^2`, i.e. `M(k) ≥ 2^k / √(2k+2)`. -/
theorem M_sq_lower (k : ℕ) : 4 ^ k ≤ (2 * k + 2) * M k ^ 2 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [M]
    · have h := centralBinom_sq_lower m hm
      have hM : M (2 * m) = Nat.centralBinom m := by
        simp [M, Nat.centralBinom_eq_two_mul_choose]
      rw [hM, pow_mul]
      norm_num
      nlinarith [sq_nonneg (Nat.centralBinom m)]
  · have h := centralBinom_sq_lower (m + 1) (by omega)
    have hM : Nat.centralBinom (m + 1) = 2 * M (2 * m + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
        Nat.choose_succ_succ', M, show (2 * m + 1) / 2 = m by omega]
      have : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
        rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
        congr 1; omega
      omega
    rw [hM, pow_succ] at h
    rw [pow_succ, pow_mul]
    norm_num at h ⊢
    nlinarith [sq_nonneg (M (2 * m + 1))]

/-! ## Binomial expansions in base `2^x - 1` -/

theorem ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    Nat.ofDigits b ((List.range k).map f) = ∑ i ∈ range k, f i * b ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, Finset.sum_range_succ]
    simp
    ring

theorem ofDigits_binDigits (b α k : ℕ) :
    Nat.ofDigits b (binDigits α k) = α * (b + 1) ^ k := by
  rw [binDigits, ofDigits_map_range, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [one_pow, mul_one, Nat.cast_id]
  ring

theorem length_binDigits (α k : ℕ) : (binDigits α k).length = k + 1 := by
  simp [binDigits]

theorem binDigits_reverse (α k : ℕ) : (binDigits α k).reverse = binDigits α k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i ≤ k := by rw [length_binDigits] at h2; omega
  simp only [binDigits, List.getElem_reverse, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range]
  rw [show k + 1 - 1 - i = k - i by omega, Nat.choose_symm hi]

/-- If all binomial digits `α·C(k,i)` are `< b`, they are the base-`b` digits of `α (b+1)^k`. -/
theorem digits_binDigits {b α k : ℕ} (hb : 1 < b) (hα : 0 < α)
    (h : ∀ i ≤ k, α * k.choose i < b) : Nat.digits b (α * (b + 1) ^ k) = binDigits α k := by
  rw [← ofDigits_binDigits]
  apply Nat.digits_ofDigits b hb
  · intro l hl
    simp only [binDigits, List.mem_map, List.mem_range] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    exact h i (by omega)
  · intro _
    simp [binDigits, hα.ne']

theorem two_pow_decomp (n x : ℕ) :
    2 ^ n = 2 ^ (n % x) * ((2 ^ x - 1) + 1) ^ (n / x) := by
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_mul, ← pow_add, Nat.mod_add_div]

theorem one_lt_two_pow_sub_one {x : ℕ} (hx : 2 ≤ x) : 1 < 2 ^ x - 1 := by
  have : 2 ^ 2 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
  omega

theorem digits_of_admissible {n x : ℕ} (hx : 2 ≤ x) (h : Admissible n x) :
    Nat.digits (2 ^ x - 1) (2 ^ n) = binDigits (2 ^ (n % x)) (n / x) := by
  rw [two_pow_decomp n x]
  exact digits_binDigits (one_lt_two_pow_sub_one hx) (by positivity) fun i _ =>
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.choose_le_middle i _)) h

theorem isPal_of_admissible {n x : ℕ} (hx : 2 ≤ x) (h : Admissible n x) :
    IsPal (2 ^ x - 1) (2 ^ n) := by
  rw [IsPal, digits_of_admissible hx h, binDigits_reverse]

theorem binomialRep_of_admissible {n x : ℕ} (hx : 2 ≤ x) (h : Admissible n x) :
    BinomialRep (2 ^ x - 1) (2 ^ n) :=
  ⟨2 ^ (n % x), n / x, by positivity, digits_of_admissible hx h⟩

/-- A binomial representation of `2^n` in a base `2 ≤ b ≤ 2^n` lives in a base `2^x - 1`
with `x` admissible (Kreher–Stinson, Lemma 2.1). -/
theorem admissible_of_binomialRep {n b : ℕ} (hb2 : 2 ≤ b) (hbn : b ≤ 2 ^ n)
    (h : BinomialRep b (2 ^ n)) : ∃ x, 2 ≤ x ∧ b = 2 ^ x - 1 ∧ Admissible n x := by
  obtain ⟨α, k, hα, hd⟩ := h
  have hval : 2 ^ n = α * (b + 1) ^ k := by
    rw [← Nat.ofDigits_digits b (2 ^ n), hd, ofDigits_binDigits]
  have hlt : ∀ d ∈ binDigits α k, d < b := fun d hd' =>
    Nat.digits_lt_base (by omega) (hd ▸ hd')
  have hmem : ∀ i ≤ k, α * k.choose i ∈ binDigits α k := fun i hi =>
    List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
  have hαb : α < b := by simpa using hlt _ (hmem 0 (Nat.zero_le _))
  have hk : 1 ≤ k := by
    by_contra h0
    push Not at h0
    interval_cases k
    simp at hval
    omega
  have hdvd : b + 1 ∣ 2 ^ n := by
    rw [hval]; exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  obtain ⟨x, -, hx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hx2 : 2 ≤ x := by
    by_contra h'
    push Not at h'
    interval_cases x <;> simp at hx <;> omega
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hval.symm)
  have hn : n = s + x * k := by
    rw [hs, hx, ← pow_mul, ← pow_add] at hval
    exact Nat.pow_right_injective (le_refl 2) hval
  have hsx : s < x := by
    by_contra h'
    push Not at h'
    have : 2 ^ x ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h'
    omega
  have hdm : n / x = k ∧ n % x = s := by
    rw [Nat.div_mod_unique (by omega)]
    exact ⟨by omega, hsx⟩
  refine ⟨x, hx2, by omega, ?_⟩
  unfold Admissible
  rw [hdm.1, hdm.2, ← hs, show 2 ^ x - 1 = b by omega]
  exact hlt _ (hmem _ (Nat.div_le_self k 2))

/-! ## The carry lemma -/

section Carry

variable (b : ℕ) (D : ℕ → ℕ)

/-- Carries produced when the pre-digits `D 0, D 1, …` are normalised in base `b`. -/
def carry : ℕ → ℕ
  | 0 => 0
  | i + 1 => (D i + carry i) / b

/-- The digits produced by the normalisation. -/
def dig (i : ℕ) : ℕ := (D i + carry b D i) % b

theorem carry_step (i : ℕ) : D i + carry b D i = dig b D i + b * carry b D (i + 1) := by
  simp only [dig, carry]
  exact (Nat.mod_add_div _ _).symm

theorem sum_eq_digits_add_carry (m : ℕ) :
    ∑ i ∈ range m, D i * b ^ i = ∑ i ∈ range m, dig b D i * b ^ i + carry b D m * b ^ m := by
  induction m with
  | zero => simp [carry]
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have h := carry_step b D m
    calc ∑ i ∈ range m, dig b D i * b ^ i + carry b D m * b ^ m + D m * b ^ m
        = ∑ i ∈ range m, dig b D i * b ^ i + (D m + carry b D m) * b ^ m := by ring
      _ = _ := by rw [h]; ring

end Carry

/-- **Carry lemma.**  Let `b = 2^x - 1` with `x ≥ 2`.  If `2^n` has exactly `⌊n/x⌋ + 1` digits
in base `b` and is a palindrome there, then `x` is admissible for `n`, i.e. the
representation is the binomial one. -/
theorem carry_lemma {n x : ℕ} (hx : 2 ≤ x) (hN : 2 ^ n < (2 ^ x - 1) ^ (n / x + 1))
    (hpal : IsPal (2 ^ x - 1) (2 ^ n)) : Admissible n x := by
  have hb : 1 < 2 ^ x - 1 := one_lt_two_pow_sub_one hx
  set b := 2 ^ x - 1 with hbdef
  set k := n / x with hkdef
  set r := n % x with hrdef
  set D : ℕ → ℕ := fun i => 2 ^ r * k.choose i with hD
  have hsymD : ∀ i ≤ k, D (k - i) = D i := fun i hi => by simp [hD, Nat.choose_symm hi]
  -- `2^n` as a sum of pre-digits
  have hsum : 2 ^ n = ∑ i ∈ range (k + 1), D i * b ^ i := by
    rw [two_pow_decomp n x, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hD, one_pow, mul_one, Nat.cast_id]
    ring
  have hdecomp := sum_eq_digits_add_carry b D (k + 1)
  rw [← hsum] at hdecomp
  -- the top carry vanishes because `2^n < b^(k+1)`
  have hck : carry b D (k + 1) = 0 := by
    by_contra hne
    have : b ^ (k + 1) ≤ carry b D (k + 1) * b ^ (k + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  -- the digits of `2^n`
  set E := (List.range (k + 1)).map (dig b D) with hE
  have hdig_lt : ∀ l ∈ E, l < b := by
    intro l hl
    simp only [hE, List.mem_map] at hl
    obtain ⟨i, _, rfl⟩ := hl
    exact Nat.mod_lt _ (by omega)
  have hofE : Nat.ofDigits b E = 2 ^ n := by
    rw [hE, ofDigits_map_range]
    rw [hck, zero_mul, add_zero] at hdecomp
    exact hdecomp.symm
  have hge : b ^ k ≤ 2 ^ n := by
    rw [two_pow_decomp n x]
    calc b ^ k ≤ (b + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      _ ≤ 2 ^ r * (b + 1) ^ k := Nat.le_mul_of_pos_left _ (by positivity)
  have hdigits : Nat.digits b (2 ^ n) = E := by
    rw [← hofE]
    apply Nat.digits_ofDigits b hb E hdig_lt
    intro hne
    have hlast : E.getLast hne = dig b D k := by simp [hE]
    rw [hlast]
    intro h0
    have hsplit : Nat.ofDigits b E = Nat.ofDigits b ((List.range k).map (dig b D)) := by
      rw [hE, List.range_succ, List.map_append, Nat.ofDigits_append]
      simp [h0]
    have hlt : Nat.ofDigits b ((List.range k).map (dig b D)) < b ^ k := by
      have := Nat.ofDigits_lt_base_pow_length hb
        (l := (List.range k).map (dig b D)) (fun l hl => by
          simp only [List.mem_map] at hl
          obtain ⟨i, _, rfl⟩ := hl
          exact Nat.mod_lt _ (by omega))
      simpa using this
    omega
  -- the palindrome property of the digits
  have hsym : ∀ i ≤ k, dig b D (k - i) = dig b D i := by
    intro i hi
    rw [IsPal, hdigits] at hpal
    have h1 : E.reverse[i]'(by simp [hE]; omega) = E[i]'(by simp [hE]; omega) := by
      simp only [hpal]
    simp only [hE, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range] at h1
    rw [show k + 1 - 1 - i = k - i by omega] at h1
    exact h1
  -- main induction: the pre-digits at positions `≤ k/2` are genuine digits
  have key : ∀ i, 2 * i ≤ k → D i < b := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hfwd : ∀ j ≤ i, carry b D j = 0 := by
        intro j hj
        induction j with
        | zero => rfl
        | succ j ihj =>
          simp only [carry]
          rw [ihj (by omega), add_zero]
          exact Nat.div_eq_of_lt (ih j (by omega) (by omega))
      have hdigeq : ∀ j < i, dig b D j = D j := by
        intro j hj
        simp only [dig, hfwd j (by omega), add_zero]
        exact Nat.mod_eq_of_lt (ih j hj (by omega))
      have hbwd : ∀ j ≤ i, carry b D (k + 1 - j) = 0 := by
        intro j hj
        induction j with
        | zero => simpa using hck
        | succ j ihj =>
          have hc := ihj (by omega)
          have hstep := carry_step b D (k - j)
          rw [show k - j + 1 = k + 1 - j by omega, hc, mul_zero, add_zero,
            hsym j (by omega), hdigeq j (by omega), ← hsymD j (by omega)] at hstep
          rw [show k + 1 - (j + 1) = k - j by omega]
          omega
      have hc := hbwd i le_rfl
      have hstep : carry b D (k + 1 - i) = (D (k - i) + carry b D (k - i)) / b := by
        rw [show k + 1 - i = (k - i) + 1 by omega]
        rfl
      rw [hc] at hstep
      have hlt : D (k - i) < b := by
        by_contra hge'
        push Not at hge'
        have : 1 ≤ (D (k - i) + carry b D (k - i)) / b :=
          (Nat.one_le_div_iff (by omega)).2 (by omega)
        omega
      rwa [hsymD i (by omega)] at hlt
  have := key (k / 2) (by omega)
  simpa [Admissible, M, hD] using this

/-- The carry lemma as an equivalence. -/
theorem isPal_iff_admissible {n x : ℕ} (hx : 2 ≤ x)
    (hN : 2 ^ n < (2 ^ x - 1) ^ (n / x + 1)) :
    IsPal (2 ^ x - 1) (2 ^ n) ↔ Admissible n x :=
  ⟨carry_lemma hx hN, isPal_of_admissible hx⟩

/-- `(b+1)^(m+1) ≤ b^m (b + 2(m+1))` when `2m ≤ b`. -/
theorem succ_pow_le (b : ℕ) : ∀ m, 2 * m ≤ b → (b + 1) ^ (m + 1) ≤ b ^ m * (b + 2 * (m + 1))
  | 0, _ => by simp
  | m + 1, h => by
    have ih := succ_pow_le b m (by omega)
    calc (b + 1) ^ (m + 1 + 1) = (b + 1) * (b + 1) ^ (m + 1) := by ring
      _ ≤ (b + 1) * (b ^ m * (b + 2 * (m + 1))) := Nat.mul_le_mul_left _ ih
      _ = b ^ m * ((b + 1) * (b + 2 * (m + 1))) := by ring
      _ ≤ b ^ m * (b * (b + 2 * (m + 1 + 1))) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = b ^ (m + 1) * (b + 2 * (m + 1 + 1)) := by ring

/-- A simple sufficient condition for the hypothesis of the carry lemma. -/
theorem no_overflow {n x : ℕ} (hx : 2 ≤ x) (hk : 2 * (n / x + 1) < 2 ^ x - 1) :
    2 ^ n < (2 ^ x - 1) ^ (n / x + 1) := by
  have hb : 1 < 2 ^ x - 1 := one_lt_two_pow_sub_one hx
  set b := 2 ^ x - 1 with hbdef
  set k := n / x
  have h1 : (b + 1) ^ (k + 1) ≤ b ^ k * (b + 2 * (k + 1)) := succ_pow_le b k (by omega)
  have h2 : b ^ k * (b + 2 * (k + 1)) < b ^ k * (2 * b) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have h3 : 2 * 2 ^ n ≤ (b + 1) ^ (k + 1) := by
    rw [two_pow_decomp n x, pow_succ]
    have hr : 2 * 2 ^ (n % x) ≤ b + 1 := by
      rw [hbdef, Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (Nat.mod_lt _ (by omega))
    calc 2 * (2 ^ (n % x) * (b + 1) ^ k) = (2 * 2 ^ (n % x)) * (b + 1) ^ k := by ring
      _ ≤ (b + 1) * (b + 1) ^ k := Nat.mul_le_mul_right _ hr
      _ = (b + 1) ^ k * (b + 1) := by ring
  have h4 : b ^ k * (2 * b) = 2 * b ^ (k + 1) := by ring
  omega

/-- Integer Bernoulli inequality: `(b+1)^m (b+1-m) ≤ b^m (b+1)` for `m ≤ b`. -/
theorem bernoulli_nat (b : ℕ) : ∀ m, m ≤ b → (b + 1) ^ m * (b + 1 - m) ≤ b ^ m * (b + 1)
  | 0, _ => by simp
  | m + 1, h => by
    have ih := bernoulli_nat b m (by omega)
    have h1 : (b + 1) * (b + 1 - (m + 1)) ≤ b * (b + 1 - m) := by
      obtain ⟨d, rfl⟩ : ∃ d, b = d + m := ⟨b - m, by omega⟩
      rw [show d + m + 1 - (m + 1) = d by omega, show d + m + 1 - m = d + 1 by omega]
      nlinarith
    calc (b + 1) ^ (m + 1) * (b + 1 - (m + 1))
        = (b + 1) ^ m * ((b + 1) * (b + 1 - (m + 1))) := by ring
      _ ≤ (b + 1) ^ m * (b * (b + 1 - m)) := Nat.mul_le_mul_left _ h1
      _ = b * ((b + 1) ^ m * (b + 1 - m)) := by ring
      _ ≤ b * (b ^ m * (b + 1)) := Nat.mul_le_mul_left _ ih
      _ = b ^ (m + 1) * (b + 1) := by ring

/-- The sufficient condition of the paper: if `n < x·2^(x-1)` then `2^n` has exactly
`⌊n/x⌋ + 1` digits in base `2^x - 1` (no overflow). -/
theorem no_overflow' {n x : ℕ} (hx : 2 ≤ x) (hn : n < x * 2 ^ (x - 1)) :
    2 ^ n < (2 ^ x - 1) ^ (n / x + 1) := by
  have hb : 1 < 2 ^ x - 1 := one_lt_two_pow_sub_one hx
  have hpow : 2 ^ x = 2 * 2 ^ (x - 1) := by
    rw [← pow_succ']; congr 1; omega
  set b := 2 ^ x - 1 with hbdef
  set k := n / x with hkdef
  have hk : k < 2 ^ (x - 1) := by
    rw [hkdef, Nat.div_lt_iff_lt_mul (by omega)]
    linarith [mul_comm x (2 ^ (x - 1))]
  have hkb : 2 * k + 1 ≤ b := by omega
  have hbern := bernoulli_nat b (k + 1) (by omega)
  rw [show b + 1 - (k + 1) = b - k by omega] at hbern
  -- (b+1)^(k+1) ≤ 2 b^(k+1)
  have h2 : (b + 1) ^ (k + 1) ≤ 2 * b ^ (k + 1) := by
    have h3 : (b + 1) ^ (k + 1) * (b + 1) ≤ (b + 1) ^ (k + 1) * (2 * (b - k)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (b + 1) ^ (k + 1) * (b + 1) ≤ (2 * b ^ (k + 1)) * (b + 1) := by nlinarith
    exact Nat.le_of_mul_le_mul_right h4 (by omega)
  -- 2 · 2^n ≤ (b+1)^(k+1)
  have h5 : 2 * 2 ^ n ≤ (b + 1) ^ (k + 1) := by
    rw [two_pow_decomp n x, pow_succ]
    have hr : 2 * 2 ^ (n % x) ≤ b + 1 := by
      rw [hbdef, Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (Nat.mod_lt _ (by omega))
    calc 2 * (2 ^ (n % x) * (b + 1) ^ k) = (2 * 2 ^ (n % x)) * (b + 1) ^ k := by ring
      _ ≤ (b + 1) * (b + 1) ^ k := Nat.mul_le_mul_right _ hr
      _ = (b + 1) ^ k * (b + 1) := by ring
  -- strictness: `b^(k+1)` is odd
  have hodd : Odd (b ^ (k + 1)) := by
    apply Odd.pow
    rw [hbdef]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hle : 2 ^ n ≤ b ^ (k + 1) := by omega
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero]
    exact Nat.one_lt_pow (by omega) hb
  · have heven : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ heven) (Nat.not_even_iff_odd.2 hodd)

/-- Overflow bases are small: if `(2^x-1)^(⌊n/x⌋+1) ≤ 2^n` then `x·2^(x-1) ≤ n`. -/
theorem overflow_le {n x : ℕ} (hx : 2 ≤ x) (h : (2 ^ x - 1) ^ (n / x + 1) ≤ 2 ^ n) :
    x * 2 ^ (x - 1) ≤ n := by
  by_contra hlt
  push Not at hlt
  have := no_overflow' hx hlt
  omega

/-- For each `n` the overflow bases `2^x - 1` satisfy `2^x ≤ n` and `(2^x - 1)·x < 2n`. -/
theorem overflow_small {n x : ℕ} (hx : 2 ≤ x) (h : (2 ^ x - 1) ^ (n / x + 1) ≤ 2 ^ n) :
    2 ^ x ≤ n ∧ (2 ^ x - 1) * x < 2 * n := by
  have h1 := overflow_le hx h
  have hpow : 2 ^ x = 2 * 2 ^ (x - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (x - 1) := by positivity
  constructor
  · nlinarith
  · have : (2 ^ x - 1) * x < 2 ^ x * x := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    nlinarith

/-! ## Even-length palindromes (Kreher–Stinson, Lemma 2.2) -/

theorem succ_dvd_of_isPal_even {b n : ℕ} (hpal : IsPal b n)
    (heven : Even (Nat.digits b n).length) : b + 1 ∣ n := by
  have p : (Nat.digits b n).Palindrome := List.Palindrome.of_reverse_eq hpal
  let dig := (Nat.digits b n).map fun n : ℕ => (n : ℤ)
  have h : Even dig.length := by rwa [List.length_map]
  have t := Nat.dvd_iff_dvd_ofDigits (b + 1) b (-1 : ℤ) (by push_cast; ring_nf; exact dvd_refl _) n
  rw [Nat.ofDigits_neg_one] at t
  refine t.2 ⟨0, ?_⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq, _root_.pow_succ', h.neg_one_pow, mul_one, neg_one_zsmul] at this
  simpa using eq_zero_of_neg_eq this.symm

theorem mersenne_of_isPal_even {b n : ℕ} (hpal : IsPal b (2 ^ n))
    (heven : Even (Nat.digits b (2 ^ n)).length) : ∃ x, b + 1 = 2 ^ x := by
  obtain ⟨x, -, hx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (succ_dvd_of_isPal_even hpal heven)
  exact ⟨x, hx⟩

/-! ## The minimal palindromic base and the binomial exponent `β(n)` -/

theorem exists_pal_base (N : ℕ) : ∃ b, 2 ≤ b ∧ IsPal b N := by
  refine ⟨N + 2, by omega, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [IsPal]
  · rw [IsPal, Nat.digits_of_lt (N + 2) N hN.ne' (by omega)]
    rfl

/-- `bmin N`: the least base `b ≥ 2` in which `N` is a palindrome (`b(N)` in the paper). -/
def bmin (N : ℕ) : ℕ := Nat.find (exists_pal_base N)

theorem bmin_spec (N : ℕ) : 2 ≤ bmin N ∧ IsPal (bmin N) N := Nat.find_spec (exists_pal_base N)

theorem not_isPal_of_lt_bmin {N b : ℕ} (h2 : 2 ≤ b) (hb : b < bmin N) : ¬ IsPal b N :=
  fun hp => Nat.find_min (exists_pal_base N) hb ⟨h2, hp⟩

theorem bmin_le_of_isPal {N b : ℕ} (h2 : 2 ≤ b) (hp : IsPal b N) : bmin N ≤ b :=
  Nat.find_min' (exists_pal_base N) ⟨h2, hp⟩

theorem exists_admissible (n : ℕ) : ∃ x, 2 ≤ x ∧ Admissible n x := by
  refine ⟨n + 2, by omega, ?_⟩
  unfold Admissible
  rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  have : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp [M]
  omega

/-- `β(n)`: the least admissible `x ≥ 2`. -/
def beta (n : ℕ) : ℕ := Nat.find (exists_admissible n)

theorem beta_spec (n : ℕ) : 2 ≤ beta n ∧ Admissible n (beta n) :=
  Nat.find_spec (exists_admissible n)

theorem beta_le_of_admissible {n x : ℕ} (h2 : 2 ≤ x) (h : Admissible n x) : beta n ≤ x :=
  Nat.find_min' (exists_admissible n) ⟨h2, h⟩

theorem not_admissible_of_lt_beta {n x : ℕ} (h2 : 2 ≤ x) (h : x < beta n) : ¬ Admissible n x :=
  fun ha => Nat.find_min (exists_admissible n) h ⟨h2, ha⟩

/-- The binomial upper bound `b(2^n) ≤ 2^β(n) - 1`. -/
theorem bmin_le_binomial (n : ℕ) : bmin (2 ^ n) ≤ 2 ^ beta n - 1 := by
  have hs := beta_spec n
  exact bmin_le_of_isPal (by have := one_lt_two_pow_sub_one hs.1; omega)
    (isPal_of_admissible hs.1 hs.2)

theorem beta_le_self {n : ℕ} (hn : 2 ≤ n) : beta n ≤ n := by
  apply beta_le_of_admissible hn
  unfold Admissible
  rw [Nat.mod_self, Nat.div_self (by omega)]
  have := one_lt_two_pow_sub_one hn
  simp [M]
  omega

/-! ## Reformulation of conjectures (a), (b) -/

theorem digits_two_two : Nat.digits 2 2 = [0, 1] := by
  rw [Nat.digits_def' (by norm_num) (by norm_num), Nat.digits_of_lt 2 1 (by norm_num) (by norm_num)]

theorem bmin_two : bmin 2 = 3 := by
  apply le_antisymm
  · refine bmin_le_of_isPal (by norm_num) ?_
    rw [IsPal, Nat.digits_of_lt 3 2 (by norm_num) (by norm_num)]
    rfl
  · by_contra h
    push Not at h
    have h2 := (bmin_spec 2).1
    have hp := (bmin_spec 2).2
    rw [show bmin 2 = 2 by omega, IsPal, digits_two_two] at hp
    simp at hp

theorem beta_one : beta 1 = 2 :=
  le_antisymm (beta_le_of_admissible (le_refl 2) (by decide)) (beta_spec 1).1

/-- For `n ≥ 1`: the minimal palindromic representation of `2^n` is binomial iff
`b(2^n) = 2^β(n) - 1`. -/
theorem binomialRep_bmin_iff {n : ℕ} (hn : 1 ≤ n) :
    BinomialRep (bmin (2 ^ n)) (2 ^ n) ↔ bmin (2 ^ n) = 2 ^ beta n - 1 := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · rw [pow_one, bmin_two, beta_one]
    refine ⟨fun _ => by norm_num, fun _ => ⟨2, 0, by norm_num, ?_⟩⟩
    rw [Nat.digits_of_lt 3 2 (by norm_num) (by norm_num)]
    rfl
  constructor
  · intro h
    have hle := bmin_le_binomial n
    have h2 := (bmin_spec (2 ^ n)).1
    have hbn : bmin (2 ^ n) ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (beta_le_self hn2)
      omega
    obtain ⟨x, hx2, hbx, hadm⟩ := admissible_of_binomialRep h2 hbn h
    have : 2 ^ beta n ≤ 2 ^ x :=
      Nat.pow_le_pow_right (by norm_num) (beta_le_of_admissible hx2 hadm)
    omega
  · intro h
    rw [h]
    exact binomialRep_of_admissible (beta_spec n).1 (beta_spec n).2

/-- For `n ≥ 1`: `b(2^n) = 2^β(n) - 1` iff `2^n` is a palindrome in no base below `2^β(n) - 1`. -/
theorem bmin_eq_iff {n : ℕ} :
    bmin (2 ^ n) = 2 ^ beta n - 1 ↔ ∀ b, 2 ≤ b → b < 2 ^ beta n - 1 → ¬ IsPal b (2 ^ n) := by
  constructor
  · intro h b h2 hb
    exact not_isPal_of_lt_bmin h2 (h ▸ hb)
  · intro h
    have hle := bmin_le_binomial n
    have hs := bmin_spec (2 ^ n)
    by_contra hne
    exact h _ hs.1 (by omega) hs.2

/-- The reduction: a palindrome of `2^n` below the binomial base is either in a base not of the
form `2^x - 1` with an odd number of digits, or in an overflow base `2^x - 1`. -/
theorem reduction {n b : ℕ} (hb2 : 2 ≤ b) (hb : b < 2 ^ beta n - 1) (hpal : IsPal b (2 ^ n)) :
    ((∀ x, b + 1 ≠ 2 ^ x) ∧ Odd (Nat.digits b (2 ^ n)).length) ∨
      (∃ x, 2 ≤ x ∧ b = 2 ^ x - 1 ∧ (2 ^ x - 1) ^ (n / x + 1) ≤ 2 ^ n) := by
  by_cases hm : ∃ x, b + 1 = 2 ^ x
  · obtain ⟨x, hx⟩ := hm
    right
    have hx2 : 2 ≤ x := by
      by_contra h'
      push Not at h'
      interval_cases x <;> simp at hx <;> omega
    have hxβ : x < beta n := by
      have : 2 ^ x < 2 ^ beta n := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    have hna := not_admissible_of_lt_beta hx2 hxβ
    refine ⟨x, hx2, by omega, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hna (carry_lemma hx2 hlt (by rwa [show 2 ^ x - 1 = b by omega]))
  · left
    push Not at hm
    refine ⟨hm, ?_⟩
    rcases Nat.even_or_odd (Nat.digits b (2 ^ n)).length with he | ho
    · obtain ⟨x, hx⟩ := mersenne_of_isPal_even hpal he
      exact absurd hx (hm x)
    · exact ho

end PalPow2
