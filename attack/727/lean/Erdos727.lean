/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Conditional architecture for Erdos Problem #727.

The active mathematical goal is a full solve of #727, but this file only banks
the elementary and finite-checking side.  In particular, it proves no
unconditional infinite supply theorem for k = 2.
-/

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

namespace Erdos727

/-- The central binomial coefficient `binom(2n,n)`. -/
def centralBinom (n : ℕ) : ℕ :=
  (2 * n).choose n

/-- The window `(n+1) * ... * (n+k)`. -/
def window (n k : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 k, (n + j)

/-- The reversed tail `(2m) * (2m-1) * ... * (2m-2k+1)`. -/
def tail (k m : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (2 * k), (2 * m - i)

/-- The pointwise divisibility assertion in Erdos #727. -/
def erdosAt (k n : ℕ) : Prop :=
  ((n + k).factorial) ^ 2 ∣ (2 * n).factorial

instance (k n : ℕ) : Decidable (erdosAt k n) := by
  unfold erdosAt
  infer_instance

/-- The fixed-`k` infinitude assertion. -/
def erdosFixed (k : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ erdosAt k n

/-- Convenience name for the `k = 2` pointwise assertion. -/
def erdosAt2 (n : ℕ) : Prop :=
  erdosAt 2 n

/-- Convenience name for the `k = 2` infinitude assertion. -/
def erdosK2 : Prop :=
  erdosFixed 2

theorem window_eq_ascFactorial (n k : ℕ) :
    window n k = (n + 1).ascFactorial k := by
  induction k with
  | zero =>
      unfold window
      simp
  | succ k ih =>
      unfold window
      rw [Finset.prod_Icc_succ_top (a := 1) (b := k) (by omega)]
      change window n k * (n + (k + 1)) = (n + 1).ascFactorial (k + 1)
      rw [ih, Nat.ascFactorial_succ]
      rw [mul_comm ((n + 1).ascFactorial k) (n + (k + 1))]
      congr 1
      omega

theorem tail_eq_descFactorial (k m : ℕ) :
    tail k m = (2 * m).descFactorial (2 * k) := by
  unfold tail
  exact (Nat.descFactorial_eq_prod_range (2 * m) (2 * k)).symm

/-- Positivity of the reversed tail when it does not run below zero. -/
theorem tail_pos {k m : ℕ} (hkm : k ≤ m) : 0 < tail k m := by
  rw [tail_eq_descFactorial]
  exact (Nat.descFactorial_pos).2 (by omega : 2 * k ≤ 2 * m)

theorem tail_two (m : ℕ) :
    tail 2 m = (2 * m) * (2 * m - 1) * (2 * m - 2) * (2 * m - 3) := by
  unfold tail
  norm_num [Finset.prod_range_succ]

theorem window_two (n : ℕ) : window n 2 = (n + 1) * (n + 2) := by
  unfold window
  norm_num [Finset.prod_Icc_succ_top]

theorem erdosAt_iff_window_sq_dvd_centralBinom {n k : ℕ} :
    erdosAt k n ↔ (window n k) ^ 2 ∣ centralBinom n := by
  have hfact : (n + k).factorial = n.factorial * window n k := by
    rw [window_eq_ascFactorial]
    exact (Nat.factorial_mul_ascFactorial n k).symm
  have hchoose : centralBinom n * n.factorial ^ 2 = (2 * n).factorial := by
    have hn : n ≤ 2 * n := by omega
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hn
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at h
    simpa [centralBinom, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hleft :
      ((n + k).factorial) ^ 2 =
        (window n k) ^ 2 * n.factorial ^ 2 := by
    rw [hfact]
    ring
  unfold erdosAt
  rw [hleft, ← hchoose]
  simpa [mul_assoc, mul_left_comm, mul_comm]
    using (Nat.mul_dvd_mul_iff_right
      (a := (window n k) ^ 2)
      (b := centralBinom n)
      (c := n.factorial ^ 2)
      (by positivity))

theorem erdosAt2_iff_window_sq_dvd_centralBinom {n : ℕ} (_hn : 2 ≤ n) :
    erdosAt 2 n ↔ ((n + 1) * (n + 2)) ^ 2 ∣ centralBinom n := by
  have hfact : (n + 2).factorial = n.factorial * ((n + 1) * (n + 2)) := by
    rw [← Nat.factorial_mul_ascFactorial n 2]
    norm_num [Nat.ascFactorial, mul_assoc, mul_left_comm, mul_comm]
  have hchoose : centralBinom n * n.factorial ^ 2 = (2 * n).factorial := by
    have hn : n ≤ 2 * n := by omega
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hn
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at h
    simpa [centralBinom, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hleft :
      ((n + 2).factorial) ^ 2 =
        ((n + 1) * (n + 2)) ^ 2 * n.factorial ^ 2 := by
    rw [hfact]
    ring
  unfold erdosAt
  rw [hleft, ← hchoose]
  simpa [mul_assoc, mul_left_comm, mul_comm]
    using (Nat.mul_dvd_mul_iff_right
      (a := ((n + 1) * (n + 2)) ^ 2)
      (b := centralBinom n)
      (c := n.factorial ^ 2)
      (by positivity))

theorem erdosAt2_iff_window_two_sq_dvd_centralBinom {n : ℕ} (hn : 2 ≤ n) :
    erdosAt 2 n ↔ (window n 2) ^ 2 ∣ centralBinom n := by
  rw [window_two]
  exact erdosAt2_iff_window_sq_dvd_centralBinom hn

/-- Legendre valuation of `n!` at `p`, as a finite exact sum. -/
def valFactorial (p n : ℕ) : ℕ :=
  ∑ e ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ e

theorem valFactorial_eq_factorization_factorial {p n : ℕ} (hp : Nat.Prime p) :
    n.factorial.factorization p = valFactorial p n := by
  unfold valFactorial
  exact Nat.factorization_factorial hp (by omega)

/-- Legendre-form central-binomial valuation. -/
def valCentralBinomLegendre (p n : ℕ) : ℕ :=
  valFactorial p (2 * n) - 2 * valFactorial p n

/-- Literal exact checker for the divisibility statement. -/
def verifyDirect (k n : ℕ) : Bool :=
  decide (erdosAt k n)

/-- Exact prime-factorization checker equivalent to `verifyDirect`. -/
def verifyLegendre (k n : ℕ) : Bool :=
  decide (((n + k).factorial ^ 2).factorization ≤ ((2 * n).factorial).factorization)

theorem verifyDirect_sound {k n : ℕ} :
    verifyDirect k n = true → erdosAt k n := by
  intro h
  unfold verifyDirect at h
  exact of_decide_eq_true h

theorem verifyDirect_complete {k n : ℕ} :
    erdosAt k n → verifyDirect k n = true := by
  intro h
  unfold verifyDirect
  exact decide_eq_true h

theorem verifyLegendre_sound {k n : ℕ} :
    verifyLegendre k n = true → erdosAt k n := by
  intro h
  unfold verifyLegendre at h
  have hfac :
      ((n + k).factorial ^ 2).factorization ≤ ((2 * n).factorial).factorization :=
    of_decide_eq_true h
  exact (Nat.factorization_le_iff_dvd
    (by exact pow_ne_zero 2 (Nat.factorial_ne_zero (n + k)))
    (Nat.factorial_ne_zero (2 * n))).1 hfac

theorem verifyLegendre_complete {k n : ℕ} :
    erdosAt k n → verifyLegendre k n = true := by
  intro h
  unfold verifyLegendre
  apply decide_eq_true
  exact (Nat.factorization_le_iff_dvd
    (by exact pow_ne_zero 2 (Nat.factorial_ne_zero (n + k)))
    (Nat.factorial_ne_zero (2 * n))).2 h

theorem verifyLegendre_eq_verifyDirect (k n : ℕ) :
    verifyLegendre k n = verifyDirect k n := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact verifyDirect_complete (verifyLegendre_sound h)
  · intro h
    exact verifyLegendre_complete (verifyDirect_sound h)

/-- Kummer carry condition for adding `n+n` at the `p^e` level. -/
def CarryAt (p n e : ℕ) : Prop :=
  p ^ e ≤ n % p ^ e + n % p ^ e

instance (p n e : ℕ) : Decidable (CarryAt p n e) := by
  unfold CarryAt
  infer_instance

/-- Finite carry count up to bound `B`. -/
def CarryCount (p n B : ℕ) : ℕ :=
  ((Finset.Ico 1 B).filter (fun e => CarryAt p n e)).card

theorem centralBinom_factorization_eq_carryCount
    {p n B : ℕ} (hp : Nat.Prime p)
    (hB : Nat.log p (2 * n) < B) :
    (centralBinom n).factorization p = CarryCount p n B := by
  unfold centralBinom CarryCount CarryAt
  have hn : n ≤ 2 * n := by omega
  have hsub : 2 * n - n = n := by omega
  simpa [hsub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using Nat.factorization_choose (p := p) (n := 2 * n) (k := n) (b := B) hp hn hB

theorem centralBinom_factorization_eq_zero_of_mod_small_of_sq_gt
    {m p rho : ℕ}
    (hp : Nat.Prime p)
    (hmod : m % p = rho)
    (hrho : 2 * rho < p)
    (hsq : 2 * m < p ^ 2) :
    (centralBinom m).factorization p = 0 := by
  have hlog : Nat.log p (2 * m) < 2 :=
    Nat.log_lt_of_lt_pow' (by norm_num : 2 ≠ 0) hsq
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  unfold CarryCount
  have hnot : ¬ CarryAt p m 1 := by
    unfold CarryAt
    simpa [Nat.pow_one, hmod, two_mul] using (not_le_of_gt hrho)
  have hfilter_empty :
      (Finset.Ico 1 2).filter (fun e => CarryAt p m e) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    rw [Finset.mem_Ico] at he
    intro hc
    have heq : e = 1 := by omega
    subst e
    exact hnot hc
  rw [hfilter_empty]
  simp

theorem unbalanced_semiprime_tail_obstruction
    {d a b rho m : ℕ}
    (hb : Nat.Prime b)
    (hm : m = d * a * b + rho)
    (hrho : 2 * rho < b)
    (hsq : 2 * m < b ^ 2) :
    (centralBinom m).factorization b = 0 := by
  have hb_pos : 0 < b := hb.pos
  have hrho_lt : rho < b := by omega
  have hmod : m % b = rho := by
    rw [hm, Nat.add_mod]
    have hzero : d * a * b % b = 0 := by
      simpa [mul_assoc] using Nat.mul_mod_left (d * a) b
    rw [hzero, Nat.mod_eq_of_lt hrho_lt]
    simpa using Nat.mod_eq_of_lt hrho_lt
  exact centralBinom_factorization_eq_zero_of_mod_small_of_sq_gt
    hb hmod hrho hsq

theorem oddTailCarry_of_mod_eq
    {p m i e : ℕ}
    (h2lt : 2 < p ^ e)
    (hiodd : Odd i)
    (hmod : (2 * m) % p ^ e = i) :
    CarryAt p m e := by
  unfold CarryAt
  let q := p ^ e
  let r := m % q
  change q ≤ r + r
  have h2_mod : 2 % q = 2 := Nat.mod_eq_of_lt h2lt
  have hmul : (2 * m) % q = (2 * r) % q := by
    dsimp [r]
    rw [Nat.mul_mod]
    rw [h2_mod]
  by_contra hnot
  have hlt : r + r < q := by omega
  have htwo_r_lt : 2 * r < q := by omega
  have hmod_two_r : (2 * r) % q = 2 * r := Nat.mod_eq_of_lt htwo_r_lt
  have hi_eq : i = 2 * r := by
    rw [← hmod]
    rw [hmul, hmod_two_r]
  have heven : Even i := by
    rw [hi_eq]
    exact ⟨r, by omega⟩
  exact (Nat.not_even_iff_odd.2 hiodd) heven

theorem oddTailCarry_of_dvd_sub
    {p m i e : ℕ}
    (h2lt : 2 < p ^ e)
    (hiodd : Odd i)
    (hi_lt : i < p ^ e)
    (hi_le : i ≤ 2 * m)
    (hdiv : p ^ e ∣ 2 * m - i) :
    CarryAt p m e := by
  have hi_mod : i % p ^ e = i := Nat.mod_eq_of_lt hi_lt
  have hzero : (2 * m - i) % p ^ e = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod : (2 * m) % p ^ e = i := by
    calc
      (2 * m) % p ^ e = ((2 * m - i) + i) % p ^ e := by
        rw [Nat.sub_add_cancel hi_le]
      _ = ((2 * m - i) % p ^ e + i % p ^ e) % p ^ e := by
        rw [Nat.add_mod]
      _ = (0 + i) % p ^ e := by
        rw [hzero, hi_mod]
      _ = i := by simpa using hi_mod
  exact oddTailCarry_of_mod_eq h2lt hiodd hmod

theorem odd_tail_factor_prime_budget
    {p m i : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 3 < p)
    (hiodd : Odd i)
    (hi_lt_p : i < p)
    (hi_lt_m : i < 2 * m) :
    (2 * m - i).factorization p ≤ (centralBinom m).factorization p := by
  let a := (2 * m - i).factorization p
  let B := Nat.log p (2 * m) + 1
  have htail_pos : 0 < 2 * m - i := by omega
  have htail_ne : 2 * m - i ≠ 0 := ne_of_gt htail_pos
  have hpowa_dvd : p ^ a ∣ 2 * m - i :=
    (hp.pow_dvd_iff_le_factorization htail_ne).2 le_rfl
  have hpowa_le_tail : p ^ a ≤ 2 * m - i :=
    Nat.le_of_dvd htail_pos hpowa_dvd
  have hpowa_le : p ^ a ≤ 2 * m := by omega
  have ha_log : a ≤ Nat.log p (2 * m) :=
    Nat.le_log_of_pow_le hp.one_lt hpowa_le
  have hcentral :
      (centralBinom m).factorization p = CarryCount p m B :=
    centralBinom_factorization_eq_carryCount hp (by dsimp [B]; omega)
  rw [hcentral]
  unfold CarryCount
  have hsubset : Finset.Icc 1 a ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p m e) := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_Ico]
    have he_bounds := Finset.mem_Icc.mp he
    have hp_le_pow : p ≤ p ^ e := by
      simpa using Nat.pow_le_pow_right hp.pos he_bounds.1
    have h2lt : 2 < p ^ e := lt_of_lt_of_le (by omega : 2 < p) hp_le_pow
    have hi_lt_pow : i < p ^ e := lt_of_lt_of_le hi_lt_p hp_le_pow
    have hdiv : p ^ e ∣ 2 * m - i :=
      (hp.pow_dvd_iff_le_factorization htail_ne).2 he_bounds.2
    exact ⟨⟨he_bounds.1, by dsimp [B]; omega⟩,
      oddTailCarry_of_dvd_sub h2lt hiodd hi_lt_pow (by omega) hdiv⟩
  have hcard : (Finset.Icc 1 a).card = a := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [Nat.card_Icc]
      omega
  change a ≤ ((Finset.Ico 1 B).filter (fun e => CarryAt p m e)).card
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem tail_two_odd_one_prime_budget
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 3 < p)
    (hm : 1 < 2 * m) :
    (2 * m - 1).factorization p ≤ (centralBinom m).factorization p :=
  odd_tail_factor_prime_budget hp hlarge (by norm_num : Odd 1)
    (by omega) hm

theorem tail_two_odd_three_prime_budget
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 3 < p)
    (hm : 3 < 2 * m) :
    (2 * m - 3).factorization p ≤ (centralBinom m).factorization p :=
  odd_tail_factor_prime_budget hp hlarge (by norm_num : Odd 3)
    (by omega) hm

theorem freeCarry
    {p n k j e : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 2 * k < p)
    (hj0 : 1 ≤ j) (hjk : j ≤ k)
    (he : 1 ≤ e)
    (hdiv : p ^ e ∣ n + j) :
    CarryAt p n e := by
  unfold CarryAt
  let q := p ^ e
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Nat.pow_pos (a := p) (n := e) hp_pos
  have hp_le_q : p ≤ q := by
    dsimp [q]
    simpa using Nat.pow_le_pow_right hp_pos he
  have hj_lt_p : j < p := by omega
  have hj_lt_q : j < q := lt_of_lt_of_le hj_lt_p hp_le_q
  have htwoj_le_q : 2 * j ≤ q := by omega
  have hmod : (n % q + j) % q = 0 := by
    have := Nat.mod_eq_zero_of_dvd hdiv
    rw [← Nat.mod_add_mod] at this
    simpa [q] using this
  have hdvd : q ∣ n % q + j := Nat.dvd_iff_mod_eq_zero.mpr hmod
  rcases hdvd with ⟨a, ha⟩
  have hr_lt : n % q < q := Nat.mod_lt n hq_pos
  have hsum_lt : n % q + j < 2 * q := by omega
  have hsum_pos : 0 < n % q + j := by omega
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    subst a
    omega
  have ha_lt_two : a < 2 := by
    by_contra hnot
    have h2a : 2 ≤ a := by omega
    have hle : 2 * q ≤ q * a := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left q h2a
    omega
  have ha_one : a = 1 := by omega
  have hsum_eq : n % q + j = q := by
    simpa [ha_one] using ha
  have hr_eq : n % q = q - j := by omega
  rw [hr_eq]
  omega

/-- Exact integer sawtooth inequality used for a second carry. -/
def SawtoothInt (p c j : ℕ) : Prop :=
  p ^ 2 + 2 * j ≤ 2 * p * (c % p)

def SawJ (j p c : ℕ) : Prop :=
  SawtoothInt p c j

theorem sawJ_one_left_of_three_two_box
    {p q : ℕ}
    (hpq : p < q)
    (hlo : 3 * p < 2 * q)
    (hhi : q < 2 * p) :
    SawJ 1 p q := by
  unfold SawJ SawtoothInt
  have hmod : q % p = q - p := by
    have h : q % p = (q - p) % p := Nat.mod_eq_sub_mod hpq.le
    rw [h]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  have hp2 : 2 ≤ p := by omega
  have hround : p + 1 ≤ 2 * (q - p) := by omega
  have hmain : p ^ 2 + 2 ≤ p * (p + 1) := by
    nlinarith [show p ^ 2 = p * p by ring]
  have hle : p * (p + 1) ≤ p * (2 * (q - p)) :=
    Nat.mul_le_mul_left p hround
  have hmul : p * (2 * (q - p)) = 2 * p * (q - p) := by ring
  omega

theorem sawJ_one_right_of_two_box
    {p q : ℕ}
    (hpq : p < q)
    (hhi : q < 2 * p) :
    SawJ 1 q p := by
  unfold SawJ SawtoothInt
  have hmod : p % q = p := Nat.mod_eq_of_lt hpq
  rw [hmod]
  have hgap : 1 ≤ 2 * p - q := by omega
  have hprod : 2 ≤ q * (2 * p - q) := by nlinarith
  nlinarith [show q ^ 2 = q * q by ring]

theorem two_mul_right_mod_left_of_four_three_box
    {p q : ℕ}
    (hpq : p < q)
    (hhi : 3 * q < 4 * p) :
    (2 * q) % p = 2 * q - 2 * p := by
  have hp_le_2q : p ≤ 2 * q := by omega
  have hp_le_2q_sub_p : p ≤ 2 * q - p := by omega
  have hlt : 2 * q - 2 * p < p := by omega
  have h1 : (2 * q) % p = (2 * q - p) % p :=
    Nat.mod_eq_sub_mod hp_le_2q
  have h2 : (2 * q - p) % p = (2 * q - p - p) % p :=
    Nat.mod_eq_sub_mod hp_le_2q_sub_p
  rw [h1, h2]
  have hsub : 2 * q - p - p = 2 * q - 2 * p := by omega
  rw [hsub]
  exact Nat.mod_eq_of_lt hlt

theorem sawJ_two_left_of_five_four_box
    {p q : ℕ}
    (hpq : p < q)
    (hlo : 5 * p < 4 * q)
    (hhi : 3 * q < 4 * p) :
    SawJ 2 p (2 * q) := by
  unfold SawJ SawtoothInt
  have hmod : (2 * q) % p = 2 * q - 2 * p :=
    two_mul_right_mod_left_of_four_three_box hpq hhi
  rw [hmod]
  have hround : p + 1 ≤ 2 * (2 * q - 2 * p) := by omega
  have hmain : p ^ 2 + 4 ≤ p * (p + 1) := by
    nlinarith [show p ^ 2 = p * p by ring]
  have hle :
      p * (p + 1) ≤ p * (2 * (2 * q - 2 * p)) :=
    Nat.mul_le_mul_left p hround
  have hmul :
      p * (2 * (2 * q - 2 * p)) =
        2 * p * (2 * q - 2 * p) := by ring
  omega

theorem sawJ_two_right_of_four_three_box
    {p q : ℕ}
    (hpq : p < q)
    (hhi : 3 * q < 4 * p) :
    SawJ 2 q (2 * p) := by
  unfold SawJ SawtoothInt
  have hmod : (2 * p) % q = 2 * p - q := by
    have hq_le : q ≤ 2 * p := by omega
    have hlt : 2 * p - q < q := by omega
    have h : (2 * p) % q = (2 * p - q) % q :=
      Nat.mod_eq_sub_mod hq_le
    rw [h]
    exact Nat.mod_eq_of_lt hlt
  rw [hmod]
  have hq_le : q ≤ 2 * p := by omega
  have h3_le : 3 * q ≤ 4 * p := by omega
  have hgap : 1 ≤ 4 * p - 3 * q := by omega
  have hprod : 4 ≤ q * (4 * p - 3 * q) := by nlinarith
  have hsplit :
      2 * q * (2 * p - q) = q ^ 2 + q * (4 * p - 3 * q) := by
    have htwice : 2 * (2 * p - q) = q + (4 * p - 3 * q) := by omega
    calc
      2 * q * (2 * p - q) = q * (2 * (2 * p - q)) := by ring
      _ = q * (q + (4 * p - 3 * q)) := by rw [htwice]
      _ = q ^ 2 + q * (4 * p - 3 * q) := by ring
  omega

theorem secondCarry_of_SawtoothInt_of_mod_eq
    {p n j c : ℕ}
    (hmod : n % p ^ 2 = p * (c % p) - j)
    (hsaw : SawtoothInt p c j) :
    CarryAt p n 2 := by
  unfold CarryAt SawtoothInt at *
  let a := p * (c % p)
  have hsaw' : p ^ 2 + 2 * j ≤ 2 * a := by
    dsimp [a]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsaw
  have hmod' : n % p ^ 2 = a - j := by
    dsimp [a]
    exact hmod
  rw [hmod']
  omega

theorem secondCarry_of_SawtoothInt
    {p n j c : ℕ}
    (hp : Nat.Prime p)
    (hj0 : 0 < j)
    (hlarge : 2 * j < p)
    (hfac : n + j = p * c)
    (hsaw : SawtoothInt p c j) :
    CarryAt p n 2 := by
  apply secondCarry_of_SawtoothInt_of_mod_eq (c := c)
  · let q := p ^ 2
    let a := p * (c % p)
    have hp_pos : 0 < p := hp.pos
    have hq_pos : 0 < q := by
      dsimp [q]
      exact Nat.pow_pos (a := p) (n := 2) hp_pos
    have hc_lt : c % p < p := Nat.mod_lt c hp_pos
    have ha_lt_q : a < q := by
      dsimp [a, q]
      nlinarith [show p ^ 2 = p * p by ring]
    have hj_lt_q : j < q := by
      dsimp [q]
      nlinarith [show p ^ 2 = p * p by ring]
    have hj_le_a : j ≤ a := by
      unfold SawtoothInt at hsaw
      dsimp [a] at *
      nlinarith [show p ^ 2 = p * p by ring]
    have hpc_decomp : p * c = a + q * (c / p) := by
      have hc : c % p + p * (c / p) = c := Nat.mod_add_div c p
      calc
        p * c = p * (c % p + p * (c / p)) := by rw [hc]
        _ = a + q * (c / p) := by
          dsimp [a, q]
          ring
    have hn_decomp : n = a - j + q * (c / p) := by
      have hnj : n + j = a + q * (c / p) := by
        rw [hfac, hpc_decomp]
      omega
    have ha_sub_lt : a - j < q := by omega
    rw [hn_decomp]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt ha_sub_lt
  · exact hsaw

theorem carryCount_two_le_of_carryAt_one_two
    {p n B : ℕ} (hB : 2 < B)
    (h1 : CarryAt p n 1) (h2 : CarryAt p n 2) :
    2 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({1, 2} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h1⟩
    · exact ⟨⟨by omega, hB⟩, h2⟩
  have hcard : ({1, 2} : Finset ℕ).card = 2 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_two_le_of_carryAt_four_five
    {p n B : ℕ} (hB : 5 < B)
    (h4 : CarryAt p n 4) (h5 : CarryAt p n 5) :
    2 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({4, 5} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h4⟩
    · exact ⟨⟨by omega, hB⟩, h5⟩
  have hcard : ({4, 5} : Finset ℕ).card = 2 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_two_le_of_carryAt_three_four
    {p n B : ℕ} (hB : 4 < B)
    (h3 : CarryAt p n 3) (h4 : CarryAt p n 4) :
    2 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({3, 4} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h3⟩
    · exact ⟨⟨by omega, hB⟩, h4⟩
  have hcard : ({3, 4} : Finset ℕ).card = 2 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_two_le_of_carryAt_three_five
    {p n B : ℕ} (hB : 5 < B)
    (h3 : CarryAt p n 3) (h5 : CarryAt p n 5) :
    2 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({3, 5} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h3⟩
    · exact ⟨⟨by omega, hB⟩, h5⟩
  have hcard : ({3, 5} : Finset ℕ).card = 2 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_three_le_of_carryAt_one_two_three
    {p n B : ℕ} (hB : 3 < B)
    (h1 : CarryAt p n 1) (h2 : CarryAt p n 2) (h3 : CarryAt p n 3) :
    3 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({1, 2, 3} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h1⟩
    · exact ⟨⟨by omega, by omega⟩, h2⟩
    · exact ⟨⟨by omega, hB⟩, h3⟩
  have hcard : ({1, 2, 3} : Finset ℕ).card = 3 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_three_le_of_carryAt_two_four_six
    {p n B : ℕ} (hB : 6 < B)
    (h2 : CarryAt p n 2) (h4 : CarryAt p n 4) (h6 : CarryAt p n 6) :
    3 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({2, 4, 6} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h2⟩
    · exact ⟨⟨by omega, by omega⟩, h4⟩
    · exact ⟨⟨by omega, hB⟩, h6⟩
  have hcard : ({2, 4, 6} : Finset ℕ).card = 3 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_four_le_of_carryAt_three_four_five_six
    {p n B : ℕ} (hB : 6 < B)
    (h3 : CarryAt p n 3) (h4 : CarryAt p n 4)
    (h5 : CarryAt p n 5) (h6 : CarryAt p n 6) :
    4 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({3, 4, 5, 6} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun e => CarryAt p n e) := by
    intro e he
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases he
    · exact ⟨⟨by omega, by omega⟩, h3⟩
    · exact ⟨⟨by omega, by omega⟩, h4⟩
    · exact ⟨⟨by omega, by omega⟩, h5⟩
    · exact ⟨⟨by omega, hB⟩, h6⟩
  have hcard : ({3, 4, 5, 6} : Finset ℕ).card = 4 := by norm_num
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem carryCount_one_le_of_carryAt
    {p n B e : ℕ} (he1 : 1 ≤ e) (heB : e < B)
    (h : CarryAt p n e) :
    1 ≤ CarryCount p n B := by
  unfold CarryCount
  have hsubset : ({e} : Finset ℕ) ⊆
      (Finset.Ico 1 B).filter (fun f => CarryAt p n f) := by
    intro f hf
    rw [Finset.mem_filter]
    rw [Finset.mem_Ico]
    fin_cases hf
    exact ⟨⟨he1, heB⟩, h⟩
  have hcard : ({e} : Finset ℕ).card = 1 := by simp
  rw [← hcard]
  exact Finset.card_le_card hsubset

theorem centralBinom_factorization_ge_two_of_carries
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 2 < B)
    (h1 : CarryAt p n 1) (h2 : CarryAt p n 2) :
    2 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_two_le_of_carryAt_one_two hB h1 h2

theorem centralBinom_factorization_ge_two_of_carries_three_four
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 4 < B)
    (h3 : CarryAt p n 3) (h4 : CarryAt p n 4) :
    2 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_two_le_of_carryAt_three_four hB h3 h4

theorem centralBinom_factorization_ge_two_of_carries_four_five
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 5 < B)
    (h4 : CarryAt p n 4) (h5 : CarryAt p n 5) :
    2 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_two_le_of_carryAt_four_five hB h4 h5

theorem centralBinom_factorization_ge_two_of_carries_three_five
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 5 < B)
    (h3 : CarryAt p n 3) (h5 : CarryAt p n 5) :
    2 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_two_le_of_carryAt_three_five hB h3 h5

theorem centralBinom_factorization_ge_three_of_carries
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 3 < B)
    (h1 : CarryAt p n 1) (h2 : CarryAt p n 2) (h3 : CarryAt p n 3) :
    3 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_three_le_of_carryAt_one_two_three hB h1 h2 h3

theorem centralBinom_factorization_ge_three_of_carries_two_four_six
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 6 < B)
    (h2 : CarryAt p n 2) (h4 : CarryAt p n 4) (h6 : CarryAt p n 6) :
    3 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_three_le_of_carryAt_two_four_six hB h2 h4 h6

theorem centralBinom_factorization_ge_four_of_carries_three_four_five_six
    {p n B : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B) (hB : 6 < B)
    (h3 : CarryAt p n 3) (h4 : CarryAt p n 4)
    (h5 : CarryAt p n 5) (h6 : CarryAt p n 6) :
    4 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_four_le_of_carryAt_three_four_five_six hB h3 h4 h5 h6

theorem centralBinom_factorization_ge_one_of_carry
    {p n B e : ℕ} (hp : Nat.Prime p)
    (hlog : Nat.log p (2 * n) < B)
    (he1 : 1 ≤ e) (heB : e < B)
    (h : CarryAt p n e) :
    1 ≤ (centralBinom n).factorization p := by
  rw [centralBinom_factorization_eq_carryCount hp hlog]
  exact carryCount_one_le_of_carryAt he1 heB h

theorem centralBinom_factorization_ge_two_of_free_and_sawtooth
    {p n k j c B : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 2 * k < p)
    (hj0 : 0 < j) (hjk : j ≤ k)
    (hfac : n + j = p * c)
    (hsaw : SawtoothInt p c j)
    (hlog : Nat.log p (2 * n) < B) (hB : 2 < B) :
    2 ≤ (centralBinom n).factorization p := by
  have hdiv : p ^ 1 ∣ n + j := by
    exact ⟨c, by simpa using hfac⟩
  have h1 : CarryAt p n 1 :=
    freeCarry hp hlarge (Nat.succ_le_of_lt hj0) hjk (by norm_num) hdiv
  have hlargej : 2 * j < p := by omega
  have h2 : CarryAt p n 2 :=
    secondCarry_of_SawtoothInt hp hj0 hlargej hfac hsaw
  exact centralBinom_factorization_ge_two_of_carries hp hlog hB h1 h2

theorem window_two_factorization_le_one_of_left
    {p n : ℕ} (hp : Nat.Prime p)
    (hdiv : p ∣ n + 1) (hsq : ¬ p ^ 2 ∣ n + 1) :
    (window n 2).factorization p ≤ 1 := by
  have hleft_le : (n + 1).factorization p ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ (n + 1).factorization p := by omega
    exact hsq ((hp.pow_dvd_iff_le_factorization (by omega : n + 1 ≠ 0)).2 hge)
  have hnot_right : ¬ p ∣ n + 2 := by
    intro hright
    have hone : p ∣ (n + 2) - (n + 1) := Nat.dvd_sub hright hdiv
    have hdiff : (n + 2) - (n + 1) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hright_zero : (n + 2).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_right
  rw [window_two, Nat.factorization_mul (by omega : n + 1 ≠ 0) (by omega : n + 2 ≠ 0)]
  simp [hright_zero, hleft_le]

theorem window_two_factorization_le_one_of_right
    {p n : ℕ} (hp : Nat.Prime p)
    (hdiv : p ∣ n + 2) (hsq : ¬ p ^ 2 ∣ n + 2) :
    (window n 2).factorization p ≤ 1 := by
  have hright_le : (n + 2).factorization p ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ (n + 2).factorization p := by omega
    exact hsq ((hp.pow_dvd_iff_le_factorization (by omega : n + 2 ≠ 0)).2 hge)
  have hnot_left : ¬ p ∣ n + 1 := by
    intro hleft
    have hone : p ∣ (n + 2) - (n + 1) := Nat.dvd_sub hdiv hleft
    have hdiff : (n + 2) - (n + 1) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hleft_zero : (n + 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_left
  rw [window_two, Nat.factorization_mul (by omega : n + 1 ≠ 0) (by omega : n + 2 ≠ 0)]
  simp [hleft_zero, hright_le]

theorem window_two_left_prime_budget_of_sawtooth
    {p n c B : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 4 < p)
    (hfac : n + 1 = p * c)
    (hsq : ¬ p ^ 2 ∣ n + 1)
    (hsaw : SawtoothInt p c 1)
    (hlog : Nat.log p (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization p ≤ (centralBinom n).factorization p := by
  have hwin_le : (window n 2).factorization p ≤ 1 :=
    window_two_factorization_le_one_of_left hp ⟨c, hfac⟩ hsq
  have hcentral_ge : 2 ≤ (centralBinom n).factorization p :=
    centralBinom_factorization_ge_two_of_free_and_sawtooth
      (p := p) (n := n) (k := 2) (j := 1) (c := c) (B := B)
      hp (by omega) (by omega) (by omega) hfac hsaw hlog hB
  omega

theorem window_two_right_prime_budget_of_sawtooth
    {p n c B : ℕ}
    (hp : Nat.Prime p)
    (hlarge : 4 < p)
    (hfac : n + 2 = p * c)
    (hsq : ¬ p ^ 2 ∣ n + 2)
    (hsaw : SawtoothInt p c 2)
    (hlog : Nat.log p (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization p ≤ (centralBinom n).factorization p := by
  have hwin_le : (window n 2).factorization p ≤ 1 :=
    window_two_factorization_le_one_of_right hp ⟨c, hfac⟩ hsq
  have hcentral_ge : 2 ≤ (centralBinom n).factorization p :=
    centralBinom_factorization_ge_two_of_free_and_sawtooth
      (p := p) (n := n) (k := 2) (j := 2) (c := c) (B := B)
      hp (by omega) (by omega) (by omega) hfac hsaw hlog hB
  omega

theorem window_two_factorization_eq_zero_of_dvd_odd_prime
    {p n : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hdiv : p ∣ n) :
    (window n 2).factorization p = 0 := by
  have hnot_left : ¬ p ∣ n + 1 := by
    intro hleft
    have hone : p ∣ (n + 1) - n := Nat.dvd_sub hleft hdiv
    have hdiff : (n + 1) - n = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hnot_right : ¬ p ∣ n + 2 := by
    intro hright
    have htwo : p ∣ (n + 2) - n := Nat.dvd_sub hright hdiv
    have hdiff : (n + 2) - n = 2 := by omega
    have hp_dvd_two : p ∣ 2 := by simpa [hdiff] using htwo
    have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two
    exact hp2 (le_antisymm hp_le_two hp.two_le)
  have hleft_zero : (n + 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_left
  have hright_zero : (n + 2).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_right
  rw [window_two, Nat.factorization_mul (by omega : n + 1 ≠ 0) (by omega : n + 2 ≠ 0)]
  simp [hleft_zero, hright_zero]

theorem window_two_small_odd_prime_budget
    {p n : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hdiv : p ∣ n) :
    2 * (window n 2).factorization p ≤ (centralBinom n).factorization p := by
  rw [window_two_factorization_eq_zero_of_dvd_odd_prime hp hp2 hdiv]
  omega

theorem mod8_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    n % 8 = 4 := by
  have h : n % 8 = n % (8 * 2) % 8 := (Nat.mod_mul_right_mod n 8 2).symm
  rw [h]
  norm_num [hmod]

theorem mod4_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    n % 4 = 0 := by
  have h : n % 4 = n % (4 * 4) % 4 := (Nat.mod_mul_right_mod n 4 4).symm
  rw [h]
  norm_num [hmod]

theorem mod2_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    n % 2 = 0 := by
  have h : n % 2 = n % (2 * 8) % 2 := (Nat.mod_mul_right_mod n 2 8).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_two_three_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    CarryAt 2 n 3 := by
  unfold CarryAt
  have h8 : n % 8 = 4 := mod8_of_mod16_eq_12 hmod
  norm_num [h8]

theorem carryAt_two_four_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    CarryAt 2 n 4 := by
  unfold CarryAt
  norm_num [hmod]

theorem two_dvd_n_add_two_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    2 ∣ n + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod]
  rw [mod2_of_mod16_eq_12 hmod]

theorem not_four_dvd_n_add_two_of_mod16_eq_12 {n : ℕ} (hmod : n % 16 = 12) :
    ¬ 2 ^ 2 ∣ n + 2 := by
  intro hdiv
  have hzero : (n + 2) % 4 = 0 := by
    simpa using Nat.dvd_iff_mod_eq_zero.mp hdiv
  have htwo : (n + 2) % 4 = 2 := by
    rw [Nat.add_mod]
    rw [mod4_of_mod16_eq_12 hmod]
  omega

theorem window_two_factorization_le_one_at_two_of_mod16_eq_12 {n : ℕ}
    (hmod : n % 16 = 12) :
    (window n 2).factorization 2 ≤ 1 :=
  window_two_factorization_le_one_of_right Nat.prime_two
    (two_dvd_n_add_two_of_mod16_eq_12 hmod)
    (not_four_dvd_n_add_two_of_mod16_eq_12 hmod)

theorem centralBinom_factorization_ge_two_at_two_of_mod16_eq_12
    {n B : ℕ} (hmod : n % 16 = 12)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 4 < B) :
    2 ≤ (centralBinom n).factorization 2 :=
  centralBinom_factorization_ge_two_of_carries_three_four
    Nat.prime_two hlog hB
    (carryAt_two_three_of_mod16_eq_12 hmod)
    (carryAt_two_four_of_mod16_eq_12 hmod)

theorem window_two_two_prime_budget_of_mod16_eq_12
    {n B : ℕ} (hmod : n % 16 = 12)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 4 < B) :
    2 * (window n 2).factorization 2 ≤ (centralBinom n).factorization 2 := by
  have hwin : (window n 2).factorization 2 ≤ 1 :=
    window_two_factorization_le_one_at_two_of_mod16_eq_12 hmod
  have hc : 2 ≤ (centralBinom n).factorization 2 :=
    centralBinom_factorization_ge_two_at_two_of_mod16_eq_12 hmod hlog hB
  omega

theorem mod8_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    n % 8 = 4 := by
  have h : n % 8 = n % (8 * 4) % 8 := (Nat.mod_mul_right_mod n 8 4).symm
  rw [h]
  norm_num [hmod]

theorem mod4_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    n % 4 = 0 := by
  have h : n % 4 = n % (4 * 8) % 4 := (Nat.mod_mul_right_mod n 4 8).symm
  rw [h]
  norm_num [hmod]

theorem mod2_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    n % 2 = 0 := by
  have h : n % 2 = n % (2 * 16) % 2 := (Nat.mod_mul_right_mod n 2 16).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_two_three_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    CarryAt 2 n 3 := by
  unfold CarryAt
  have h8 : n % 8 = 4 := mod8_of_mod32_eq_20 hmod
  norm_num [h8]

theorem carryAt_two_five_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    CarryAt 2 n 5 := by
  unfold CarryAt
  norm_num [hmod]

theorem two_dvd_n_add_two_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    2 ∣ n + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod]
  rw [mod2_of_mod32_eq_20 hmod]

theorem not_four_dvd_n_add_two_of_mod32_eq_20 {n : ℕ} (hmod : n % 32 = 20) :
    ¬ 2 ^ 2 ∣ n + 2 := by
  intro hdiv
  have hzero : (n + 2) % 4 = 0 := by
    simpa using Nat.dvd_iff_mod_eq_zero.mp hdiv
  have htwo : (n + 2) % 4 = 2 := by
    rw [Nat.add_mod]
    rw [mod4_of_mod32_eq_20 hmod]
  omega

theorem window_two_factorization_le_one_at_two_of_mod32_eq_20 {n : ℕ}
    (hmod : n % 32 = 20) :
    (window n 2).factorization 2 ≤ 1 :=
  window_two_factorization_le_one_of_right Nat.prime_two
    (two_dvd_n_add_two_of_mod32_eq_20 hmod)
    (not_four_dvd_n_add_two_of_mod32_eq_20 hmod)

theorem centralBinom_factorization_ge_two_at_two_of_mod32_eq_20
    {n B : ℕ} (hmod : n % 32 = 20)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 5 < B) :
    2 ≤ (centralBinom n).factorization 2 :=
  centralBinom_factorization_ge_two_of_carries_three_five
    Nat.prime_two hlog hB
    (carryAt_two_three_of_mod32_eq_20 hmod)
    (carryAt_two_five_of_mod32_eq_20 hmod)

theorem window_two_two_prime_budget_of_mod32_eq_20
    {n B : ℕ} (hmod : n % 32 = 20)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 5 < B) :
    2 * (window n 2).factorization 2 ≤ (centralBinom n).factorization 2 := by
  have hwin : (window n 2).factorization 2 ≤ 1 :=
    window_two_factorization_le_one_at_two_of_mod32_eq_20 hmod
  have hc : 2 ≤ (centralBinom n).factorization 2 :=
    centralBinom_factorization_ge_two_at_two_of_mod32_eq_20 hmod hlog hB
  omega

theorem mod16_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    n % 16 = 8 := by
  have h : n % 16 = n % (16 * 2) % 16 := (Nat.mod_mul_right_mod n 16 2).symm
  rw [h]
  norm_num [hmod]

theorem mod4_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    n % 4 = 0 := by
  have h : n % 4 = n % (4 * 8) % 4 := (Nat.mod_mul_right_mod n 4 8).symm
  rw [h]
  norm_num [hmod]

theorem mod2_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    n % 2 = 0 := by
  have h : n % 2 = n % (2 * 16) % 2 := (Nat.mod_mul_right_mod n 2 16).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_two_four_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    CarryAt 2 n 4 := by
  unfold CarryAt
  have h16 : n % 16 = 8 := mod16_of_mod32_eq_24 hmod
  norm_num [h16]

theorem carryAt_two_five_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    CarryAt 2 n 5 := by
  unfold CarryAt
  norm_num [hmod]

theorem two_dvd_n_add_two_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    2 ∣ n + 2 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod]
  rw [mod2_of_mod32_eq_24 hmod]

theorem not_four_dvd_n_add_two_of_mod32_eq_24 {n : ℕ} (hmod : n % 32 = 24) :
    ¬ 2 ^ 2 ∣ n + 2 := by
  intro hdiv
  have hzero : (n + 2) % 4 = 0 := by
    simpa using Nat.dvd_iff_mod_eq_zero.mp hdiv
  have htwo : (n + 2) % 4 = 2 := by
    rw [Nat.add_mod]
    rw [mod4_of_mod32_eq_24 hmod]
  omega

theorem window_two_factorization_le_one_at_two_of_mod32_eq_24 {n : ℕ}
    (hmod : n % 32 = 24) :
    (window n 2).factorization 2 ≤ 1 :=
  window_two_factorization_le_one_of_right Nat.prime_two
    (two_dvd_n_add_two_of_mod32_eq_24 hmod)
    (not_four_dvd_n_add_two_of_mod32_eq_24 hmod)

theorem centralBinom_factorization_ge_two_at_two_of_mod32_eq_24
    {n B : ℕ} (hmod : n % 32 = 24)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 5 < B) :
    2 ≤ (centralBinom n).factorization 2 :=
  centralBinom_factorization_ge_two_of_carries_four_five
    Nat.prime_two hlog hB
    (carryAt_two_four_of_mod32_eq_24 hmod)
    (carryAt_two_five_of_mod32_eq_24 hmod)

theorem window_two_two_prime_budget_of_mod32_eq_24
    {n B : ℕ} (hmod : n % 32 = 24)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 5 < B) :
    2 * (window n 2).factorization 2 ≤ (centralBinom n).factorization 2 := by
  have hwin : (window n 2).factorization 2 ≤ 1 :=
    window_two_factorization_le_one_at_two_of_mod32_eq_24 hmod
  have hc : 2 ≤ (centralBinom n).factorization 2 :=
    centralBinom_factorization_ge_two_at_two_of_mod32_eq_24 hmod hlog hB
  omega

theorem mod4_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    m % 4 = 3 := by
  have h : m % 4 = m % (4 * 2) % 4 := (Nat.mod_mul_right_mod m 4 2).symm
  rw [h]
  norm_num [hmod]

theorem mod2_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    m % 2 = 1 := by
  have h : m % 2 = m % (2 * 4) % 2 := (Nat.mod_mul_right_mod m 2 4).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_two_one_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    CarryAt 2 m 1 := by
  unfold CarryAt
  have h2 : m % 2 = 1 := mod2_of_mod8_eq_7 hmod
  norm_num [h2]

theorem carryAt_two_two_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    CarryAt 2 m 2 := by
  unfold CarryAt
  have h4 : m % 4 = 3 := mod4_of_mod8_eq_7 hmod
  norm_num [h4]

theorem carryAt_two_three_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    CarryAt 2 m 3 := by
  unfold CarryAt
  norm_num [hmod]

theorem centralBinom_factorization_ge_three_at_two_of_mod8_eq_7
    {m B : ℕ} (hmod : m % 8 = 7)
    (hlog : Nat.log 2 (2 * m) < B) (hB : 3 < B) :
    3 ≤ (centralBinom m).factorization 2 :=
  centralBinom_factorization_ge_three_of_carries
    Nat.prime_two hlog hB
    (carryAt_two_one_of_mod8_eq_7 hmod)
    (carryAt_two_two_of_mod8_eq_7 hmod)
    (carryAt_two_three_of_mod8_eq_7 hmod)

theorem mul_two_mod16_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    (2 * m) % 16 = 14 := by
  have h := Nat.mul_mod_mul_left 2 m 8
  norm_num at h
  rw [h, hmod]

theorem tail_two_mod16_of_mod8_eq_7 {m : ℕ} (hmod : m % 8 = 7) :
    tail 2 m % 16 = 8 := by
  have h2m : (2 * m) % 16 = 14 := mul_two_mod16_of_mod8_eq_7 hmod
  have h1 : (2 * m - 1) % 16 = 13 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 16 = 12 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 16 = 11 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_factorization_two_le_three_of_mod8_eq_7 {m : ℕ}
    (hmod : m % 8 = 7) :
    (tail 2 m).factorization 2 ≤ 3 := by
  by_contra hnot
  have hge : 4 ≤ (tail 2 m).factorization 2 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 8)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 2 ^ 4 ∣ tail 2 m :=
    (Nat.prime_two.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 16 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 16 = 8 := tail_two_mod16_of_mod8_eq_7 hmod
  omega

theorem tail_two_two_prime_budget_of_mod8_eq_7
    {m B : ℕ} (hmod : m % 8 = 7)
    (hlog : Nat.log 2 (2 * m) < B) (hB : 3 < B) :
    (tail 2 m).factorization 2 ≤ (centralBinom m).factorization 2 := by
  have htail : (tail 2 m).factorization 2 ≤ 3 :=
    tail_two_factorization_two_le_three_of_mod8_eq_7 hmod
  have hc : 3 ≤ (centralBinom m).factorization 2 :=
    centralBinom_factorization_ge_three_at_two_of_mod8_eq_7 hmod hlog hB
  omega

theorem window_pos (n k : ℕ) : 0 < window n k := by
  unfold window
  exact Finset.prod_pos (fun j hj => by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    omega)

theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n := by
  unfold centralBinom
  exact Nat.choose_pos (by omega)

theorem window_sq_dvd_centralBinom_of_prime_budget
    {n k : ℕ}
    (hBudget : ∀ p : ℕ, Nat.Prime p →
      2 * (window n k).factorization p ≤ (centralBinom n).factorization p) :
    (window n k) ^ 2 ∣ centralBinom n := by
  have hfac : ((window n k) ^ 2).factorization ≤ (centralBinom n).factorization := by
    rw [Nat.factorization_pow]
    rw [Finsupp.le_def]
    intro p
    rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : Nat.Prime p
    · simpa [mul_comm] using hBudget p hp
    · have hzero : (window n k).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_prime (window n k) hp
      simp [hzero]
  exact (Nat.factorization_le_iff_dvd
    (by exact pow_ne_zero 2 (ne_of_gt (window_pos n k)))
    (ne_of_gt (centralBinom_pos n))).1 hfac

theorem tail_dvd_centralBinom_of_prime_budget
    {k m : ℕ} (hkm : k ≤ m)
    (hBudget : ∀ p : ℕ, Nat.Prime p →
      (tail k m).factorization p ≤ (centralBinom m).factorization p) :
    tail k m ∣ centralBinom m := by
  have hfac : (tail k m).factorization ≤ (centralBinom m).factorization := by
    rw [Finsupp.le_def]
    intro p
    by_cases hp : Nat.Prime p
    · exact hBudget p hp
    · have hzero : (tail k m).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_prime (tail k m) hp
      simp [hzero]
  exact (Nat.factorization_le_iff_dvd
    (ne_of_gt (tail_pos hkm))
    (ne_of_gt (centralBinom_pos m))).1 hfac

/-- Large-prime governor predicate for one integer. -/
def governorLarge (B u : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → B < p →
    u.factorization p ≤ (centralBinom u).factorization p

/-- Exact small-prime tail budget for the reversed package. -/
def smallPrimeTailBudget (k m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≤ 2 * k →
    (tail k m).factorization p ≤ (centralBinom m).factorization p

/-- Exact large-prime tail budget; this is the finite target of the governor carry transfer. -/
def largePrimeTailBudget (k m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → 2 * k < p →
    (tail k m).factorization p ≤ (centralBinom m).factorization p

/-- The intended block of shifted large-prime governors. -/
def governorBlock (k m : ℕ) : Prop :=
  ∀ r : ℕ, r < k → governorLarge (2 * k) (m - r)

/--
The analytic governor package from the current architecture.  The finite theorem
from this package to `largePrimeTailBudget` is still open in this file.
-/
def reversedGovernorWitness (k m : ℕ) : Prop :=
  smallPrimeTailBudget k m ∧ governorBlock k m

/-- Prime-budget version of the reversed package, separated from the open governor transfer. -/
def reversedGovernorPrimeBudgetWitness (k m : ℕ) : Prop :=
  smallPrimeTailBudget k m ∧ largePrimeTailBudget k m

theorem tail_dvd_centralBinom_of_reversedGovernorPrimeBudgetWitness
    {k m : ℕ} (hkm : k ≤ m)
    (hW : reversedGovernorPrimeBudgetWitness k m) :
    tail k m ∣ centralBinom m := by
  refine tail_dvd_centralBinom_of_prime_budget hkm ?_
  intro p hp
  by_cases hsmall : p ≤ 2 * k
  · exact hW.1 p hp hsmall
  · exact hW.2 p hp (by omega)

theorem centralBinom_shift_mul_window_sq_eq_tail_mul (n k : ℕ) :
    centralBinom (n + k) * (window n k) ^ 2 =
      tail k (n + k) * centralBinom n := by
  have hchooseShift :
      centralBinom (n + k) * (n + k).factorial ^ 2 = (2 * (n + k)).factorial := by
    have hn : n + k ≤ 2 * (n + k) := by omega
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * (n + k)) (k := n + k) hn
    have hsub : 2 * (n + k) - (n + k) = n + k := by omega
    rw [hsub] at h
    simpa [centralBinom, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hchoose : centralBinom n * n.factorial ^ 2 = (2 * n).factorial := by
    have hn : n ≤ 2 * n := by omega
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hn
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at h
    simpa [centralBinom, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hwinFact : (n + k).factorial = n.factorial * window n k := by
    rw [window_eq_ascFactorial]
    exact (Nat.factorial_mul_ascFactorial n k).symm
  have htailFact : (2 * n).factorial * tail k (n + k) = (2 * (n + k)).factorial := by
    rw [tail_eq_descFactorial]
    have hle : 2 * k ≤ 2 * (n + k) := by omega
    have h := Nat.factorial_mul_descFactorial (n := 2 * (n + k)) (k := 2 * k) hle
    have hsub : (n + k) * 2 - k * 2 = n * 2 := by omega
    simpa [hsub, mul_assoc, mul_left_comm, mul_comm] using h
  have hmainFact :
      centralBinom (n + k) * (n.factorial ^ 2 * (window n k) ^ 2) =
        tail k (n + k) * (centralBinom n * n.factorial ^ 2) := by
    calc
      centralBinom (n + k) * (n.factorial ^ 2 * (window n k) ^ 2)
          = centralBinom (n + k) * (n.factorial * window n k) ^ 2 := by ring
      _ = centralBinom (n + k) * (n + k).factorial ^ 2 := by rw [hwinFact]
      _ = (2 * (n + k)).factorial := hchooseShift
      _ = (2 * n).factorial * tail k (n + k) := htailFact.symm
      _ = (centralBinom n * n.factorial ^ 2) * tail k (n + k) := by rw [hchoose]
      _ = tail k (n + k) * (centralBinom n * n.factorial ^ 2) := by ring
  apply Nat.mul_right_cancel (show 0 < n.factorial ^ 2 by positivity)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmainFact

theorem window_sq_dvd_centralBinom_iff_tail_dvd (n k : ℕ) :
    (window n k) ^ 2 ∣ centralBinom n ↔
      tail k (n + k) ∣ centralBinom (n + k) := by
  constructor
  · intro hwin
    rcases hwin with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Nat.mul_right_cancel (pow_pos (window_pos n k) 2)
    simpa [hq, mul_assoc, mul_left_comm, mul_comm]
      using centralBinom_shift_mul_window_sq_eq_tail_mul n k
  · intro htail
    rcases htail with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hcancel : q * (window n k) ^ 2 = centralBinom n := by
      apply Nat.mul_left_cancel (tail_pos (k := k) (m := n + k) (by omega))
      simpa [hq, mul_assoc, mul_left_comm, mul_comm]
        using centralBinom_shift_mul_window_sq_eq_tail_mul n k
    simpa [mul_comm] using hcancel.symm

theorem erdosAt2_sub_two_of_tail_dvd
    {m : ℕ} (hm : 2 ≤ m)
    (htail : tail 2 m ∣ centralBinom m) :
    erdosAt 2 (m - 2) := by
  let n := m - 2
  have hm_eq : n + 2 = m := by
    dsimp [n]
    omega
  have htail' : tail 2 (n + 2) ∣ centralBinom (n + 2) := by
    simpa [hm_eq] using htail
  have hwin : (window n 2) ^ 2 ∣ centralBinom n :=
    (window_sq_dvd_centralBinom_iff_tail_dvd n 2).2 htail'
  exact erdosAt_iff_window_sq_dvd_centralBinom.2 hwin

/-- Still-open infinite supply of AP-local governor blocks for a fixed `k`. -/
def ReversedGovernorSupply (k : ℕ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ,
    N ≤ m ∧ k ≤ m ∧ reversedGovernorWitness k m

/-- Prime-budget supply strong enough for the currently banked finite tail divisibility theorem. -/
def ReversedGovernorPrimeBudgetSupply (k : ℕ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ,
    N ≤ m ∧ k ≤ m ∧ reversedGovernorPrimeBudgetWitness k m

theorem erdosFixed_of_reversedGovernorPrimeBudgetSupply
    {k : ℕ}
    (_hk : 2 ≤ k)
    (hSupply : ReversedGovernorPrimeBudgetSupply k) :
    erdosFixed k := by
  intro N
  rcases hSupply (N + k) with ⟨m, hmN, hkm, hW⟩
  let n := m - k
  have hnN : N ≤ n := by
    dsimp [n]
    omega
  have hm_eq : n + k = m := by
    dsimp [n]
    omega
  have htail : tail k m ∣ centralBinom m :=
    tail_dvd_centralBinom_of_reversedGovernorPrimeBudgetWitness hkm hW
  have htail' : tail k (n + k) ∣ centralBinom (n + k) := by
    simpa [hm_eq] using htail
  have hwin : (window n k) ^ 2 ∣ centralBinom n :=
    (window_sq_dvd_centralBinom_iff_tail_dvd n k).2 htail'
  exact ⟨n, hnN, erdosAt_iff_window_sq_dvd_centralBinom.2 hwin⟩

def smallPrimeExponent (k p : ℕ) : ℕ :=
  if p = 2 then
    k + k.factorial.factorization 2 + 2
  else
    ((2 * k + 1).factorial.factorization p) + 2

def smallPrimeModulus (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (2 * k + 1)).filter Nat.Prime,
    p ^ smallPrimeExponent k p

/-- AP-local governor supply; the AP-to-small-prime-budget constructor remains open here. -/
def APGovernorSupply (k : ℕ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ,
    N ≤ m ∧ k ≤ m ∧
    m % smallPrimeModulus k = smallPrimeModulus k - 1 ∧
    governorBlock k m

def badResidueAt (k X p r u : ℕ) : Prop :=
  let L := Nat.log p (2 * X)
  let a := (u - r).factorization p
  r < k ∧ Nat.Prime p ∧ 2 * k < p ∧
    0 < a ∧
    (((Finset.Icc 1 L).filter
      (fun e => CarryAt p u e)).card < a)

def Small23Only (D : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p → ¬ p ∣ D

theorem small23Only_one : Small23Only 1 := by
  intro p hp _ hdiv
  exact hp.not_dvd_one hdiv

theorem small23Only_two : Small23Only 2 := by
  intro p hp hp3 hdiv
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
  omega

theorem small23Only_three : Small23Only 3 := by
  intro p hp hp3 hdiv
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) hdiv
  omega

theorem small23Only_four : Small23Only 4 := by
  intro p hp hp3 hdiv
  have hp_even : p ∣ 2 * 2 := by simpa using hdiv
  rcases (hp.dvd_mul).1 hp_even with hp2 | hp2
  · have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
    omega
  · have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
    omega

theorem semiprime_large_factorization_left
    {D a b : ℕ}
    (hD : Small23Only D)
    (ha : Nat.Prime a)
    (hb : Nat.Prime b)
    (ha3 : 3 < a)
    (hab : a ≠ b) :
    (D * a * b).factorization a = 1 := by
  have hD_ne : D ≠ 0 := by
    intro hzero
    exact hD a ha ha3 (by rw [hzero]; exact dvd_zero a)
  have hnot_a_dvd_D : ¬ a ∣ D := hD a ha ha3
  have hD_zero : D.factorization a = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_a_dvd_D
  have hnot_a_dvd_b : ¬ a ∣ b := by
    intro hdiv
    have hba : b = a := (Nat.Prime.dvd_iff_eq hb ha.ne_one).1 hdiv
    exact hab hba.symm
  have hb_zero : b.factorization a = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_a_dvd_b
  rw [Nat.factorization_mul (mul_ne_zero hD_ne ha.ne_zero) hb.ne_zero]
  rw [Nat.factorization_mul hD_ne ha.ne_zero]
  simp [hD_zero, hb_zero, Nat.Prime.factorization_self ha]

theorem semiprime_large_factorization_right
    {D a b : ℕ}
    (hD : Small23Only D)
    (ha : Nat.Prime a)
    (hb : Nat.Prime b)
    (hb3 : 3 < b)
    (hab : a ≠ b) :
    (D * a * b).factorization b = 1 := by
  have hD_ne : D ≠ 0 := by
    intro hzero
    exact hD b hb hb3 (by rw [hzero]; exact dvd_zero b)
  have hnot_b_dvd_D : ¬ b ∣ D := hD b hb hb3
  have hD_zero : D.factorization b = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_b_dvd_D
  have hnot_b_dvd_a : ¬ b ∣ a := by
    intro hdiv
    have hab' : a = b := (Nat.Prime.dvd_iff_eq ha hb.ne_one).1 hdiv
    exact hab hab'
  have ha_zero : a.factorization b = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_b_dvd_a
  rw [Nat.factorization_mul (mul_ne_zero hD_ne ha.ne_zero) hb.ne_zero]
  rw [Nat.factorization_mul hD_ne ha.ne_zero]
  simp [hD_zero, ha_zero, Nat.Prime.factorization_self hb]

theorem large_budget_m_of_semiprime
    {m D a b : ℕ}
    (hD : Small23Only D)
    (ha : Nat.Prime a)
    (hb : Nat.Prime b)
    (ha3 : 3 < a)
    (hb3 : 3 < b)
    (hab : a ≠ b)
    (hm : m = D * a * b)
    (hcarry_a : CarryAt a m 2)
    (hcarry_b : CarryAt b m 2) :
    ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ m →
      m.factorization p ≤ (centralBinom m).factorization p := by
  intro p hp hp3 hdiv
  have hdiv_prod : p ∣ D * a * b := by simpa [hm] using hdiv
  rcases (hp.dvd_mul).1 hdiv_prod with hdiv_left | hpb
  · rcases (hp.dvd_mul).1 hdiv_left with hpD | hpa
    · exact (hD p hp hp3 hpD).elim
    · have hap : a = p := (Nat.Prime.dvd_iff_eq ha hp.ne_one).1 hpa
      subst p
      have hfac : m.factorization a = 1 := by
        rw [hm]
        exact semiprime_large_factorization_left hD ha hb ha3 hab
      have hc : 1 ≤ (centralBinom m).factorization a :=
        centralBinom_factorization_ge_one_of_carry
          (p := a) (n := m) (B := Nat.log a (2 * m) + 3) (e := 2)
          ha (by omega) (by omega) (by omega) hcarry_a
      omega
  · have hbp : b = p := (Nat.Prime.dvd_iff_eq hb hp.ne_one).1 hpb
    subst p
    have hfac : m.factorization b = 1 := by
      rw [hm]
      exact semiprime_large_factorization_right hD ha hb hb3 hab
    have hc : 1 ≤ (centralBinom m).factorization b :=
      centralBinom_factorization_ge_one_of_carry
        (p := b) (n := m) (B := Nat.log b (2 * m) + 3) (e := 2)
        hb (by omega) (by omega) (by omega) hcarry_b
    omega

theorem large_budget_m_sub_one_of_semiprime
    {m D a b : ℕ}
    (hD : Small23Only D)
    (ha : Nat.Prime a)
    (hb : Nat.Prime b)
    (ha3 : 3 < a)
    (hb3 : 3 < b)
    (hab : a ≠ b)
    (hm1 : m - 1 = D * a * b)
    (hcarry_a : CarryAt a m 2)
    (hcarry_b : CarryAt b m 2) :
    ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ m - 1 →
      (m - 1).factorization p ≤ (centralBinom m).factorization p := by
  intro p hp hp3 hdiv
  have hdiv_prod : p ∣ D * a * b := by simpa [hm1] using hdiv
  rcases (hp.dvd_mul).1 hdiv_prod with hdiv_left | hpb
  · rcases (hp.dvd_mul).1 hdiv_left with hpD | hpa
    · exact (hD p hp hp3 hpD).elim
    · have hap : a = p := (Nat.Prime.dvd_iff_eq ha hp.ne_one).1 hpa
      subst p
      have hfac : (m - 1).factorization a = 1 := by
        rw [hm1]
        exact semiprime_large_factorization_left hD ha hb ha3 hab
      have hc : 1 ≤ (centralBinom m).factorization a :=
        centralBinom_factorization_ge_one_of_carry
          (p := a) (n := m) (B := Nat.log a (2 * m) + 3) (e := 2)
          ha (by omega) (by omega) (by omega) hcarry_a
      omega
  · have hbp : b = p := (Nat.Prime.dvd_iff_eq hb hp.ne_one).1 hpb
    subst p
    have hfac : (m - 1).factorization b = 1 := by
      rw [hm1]
      exact semiprime_large_factorization_right hD ha hb hb3 hab
    have hc : 1 ≤ (centralBinom m).factorization b :=
      centralBinom_factorization_ge_one_of_carry
        (p := b) (n := m) (B := Nat.log b (2 * m) + 3) (e := 2)
        hb (by omega) (by omega) (by omega) hcarry_b
    omega

theorem tail_two_factorization_eq_m_of_large_dvd_m
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hp3 : 3 < p)
    (hm2 : 2 ≤ m)
    (hdiv : p ∣ m) :
    (tail 2 m).factorization p = m.factorization p := by
  have hp_not_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hp_not_three : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) h
    omega
  have htwo_zero : (2 : ℕ).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_not_two
  have h2m_eq : (2 * m).factorization p = m.factorization p := by
    rw [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (by omega : m ≠ 0)]
    simp [htwo_zero]
  have h2mdiv : p ∣ 2 * m := dvd_mul_of_dvd_right hdiv 2
  have hnot1 : ¬ p ∣ 2 * m - 1 := by
    intro h
    have hone : p ∣ (2 * m) - (2 * m - 1) := Nat.dvd_sub h2mdiv h
    have hdiff : (2 * m) - (2 * m - 1) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hnot2 : ¬ p ∣ 2 * m - 2 := by
    intro h
    have htwo : p ∣ (2 * m) - (2 * m - 2) := Nat.dvd_sub h2mdiv h
    have hdiff : (2 * m) - (2 * m - 2) = 2 := by omega
    exact hp_not_two (by simpa [hdiff] using htwo)
  have hnot3 : ¬ p ∣ 2 * m - 3 := by
    intro h
    have hthree : p ∣ (2 * m) - (2 * m - 3) := Nat.dvd_sub h2mdiv h
    have hdiff : (2 * m) - (2 * m - 3) = 3 := by omega
    exact hp_not_three (by simpa [hdiff] using hthree)
  have hzero1 : (2 * m - 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot1
  have hzero2 : (2 * m - 2).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot2
  have hzero3 : (2 * m - 3).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot3
  rw [tail_two]
  rw [Nat.factorization_mul
    (mul_ne_zero (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
      (by omega : 2 * m - 2 ≠ 0))
    (by omega : 2 * m - 3 ≠ 0)]
  rw [Nat.factorization_mul
    (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
    (by omega : 2 * m - 2 ≠ 0)]
  rw [Nat.factorization_mul (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0)]
  simp [h2m_eq, hzero1, hzero2, hzero3]

theorem tail_two_factorization_eq_m_sub_one_of_large_dvd_m_sub_one
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hp3 : 3 < p)
    (hm2 : 2 ≤ m)
    (hdiv : p ∣ m - 1) :
    (tail 2 m).factorization p = (m - 1).factorization p := by
  have hp_not_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hp_not_three : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) h
    omega
  have htwo_zero : (2 : ℕ).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_not_two
  have h2m2_eq_factor :
      (2 * m - 2).factorization p = (m - 1).factorization p := by
    have hsub : 2 * m - 2 = 2 * (m - 1) := by omega
    rw [hsub]
    rw [Nat.factorization_mul
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : m - 1 ≠ 0)]
    simp [htwo_zero]
  have h2m2div : p ∣ 2 * m - 2 := by
    have hsub : 2 * m - 2 = 2 * (m - 1) := by omega
    rw [hsub]
    exact dvd_mul_of_dvd_right hdiv 2
  have hnot0 : ¬ p ∣ 2 * m := by
    intro h
    have htwo : p ∣ (2 * m) - (2 * m - 2) := Nat.dvd_sub h h2m2div
    have hdiff : (2 * m) - (2 * m - 2) = 2 := by omega
    exact hp_not_two (by simpa [hdiff] using htwo)
  have hnot1 : ¬ p ∣ 2 * m - 1 := by
    intro h
    have hone : p ∣ (2 * m - 1) - (2 * m - 2) := Nat.dvd_sub h h2m2div
    have hdiff : (2 * m - 1) - (2 * m - 2) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hnot3 : ¬ p ∣ 2 * m - 3 := by
    intro h
    have hone : p ∣ (2 * m - 2) - (2 * m - 3) := Nat.dvd_sub h2m2div h
    have hdiff : (2 * m - 2) - (2 * m - 3) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hzero0 : (2 * m).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot0
  have hzero1 : (2 * m - 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot1
  have hzero3 : (2 * m - 3).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot3
  rw [tail_two]
  rw [Nat.factorization_mul
    (mul_ne_zero (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
      (by omega : 2 * m - 2 ≠ 0))
    (by omega : 2 * m - 3 ≠ 0)]
  rw [Nat.factorization_mul
    (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
    (by omega : 2 * m - 2 ≠ 0)]
  rw [Nat.factorization_mul (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0)]
  simp [hzero0, hzero1, h2m2_eq_factor, hzero3]

theorem tail_two_factorization_eq_odd_one_of_large_dvd_odd_one
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hp3 : 3 < p)
    (hm2 : 2 ≤ m)
    (hdiv : p ∣ 2 * m - 1) :
    (tail 2 m).factorization p = (2 * m - 1).factorization p := by
  have hp_not_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hnot0 : ¬ p ∣ 2 * m := by
    intro h
    have hone : p ∣ (2 * m) - (2 * m - 1) := Nat.dvd_sub h hdiv
    have hdiff : (2 * m) - (2 * m - 1) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hnot2 : ¬ p ∣ 2 * m - 2 := by
    intro h
    have hone : p ∣ (2 * m - 1) - (2 * m - 2) := Nat.dvd_sub hdiv h
    have hdiff : (2 * m - 1) - (2 * m - 2) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hnot3 : ¬ p ∣ 2 * m - 3 := by
    intro h
    have htwo : p ∣ (2 * m - 1) - (2 * m - 3) := Nat.dvd_sub hdiv h
    have hdiff : (2 * m - 1) - (2 * m - 3) = 2 := by omega
    exact hp_not_two (by simpa [hdiff] using htwo)
  have hzero0 : (2 * m).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot0
  have hzero2 : (2 * m - 2).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot2
  have hzero3 : (2 * m - 3).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot3
  rw [tail_two]
  rw [Nat.factorization_mul
    (mul_ne_zero (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
      (by omega : 2 * m - 2 ≠ 0))
    (by omega : 2 * m - 3 ≠ 0)]
  rw [Nat.factorization_mul
    (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
    (by omega : 2 * m - 2 ≠ 0)]
  rw [Nat.factorization_mul (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0)]
  simp [hzero0, hzero2, hzero3]

theorem tail_two_factorization_eq_odd_three_of_large_dvd_odd_three
    {p m : ℕ}
    (hp : Nat.Prime p)
    (hp3 : 3 < p)
    (hm2 : 2 ≤ m)
    (hdiv : p ∣ 2 * m - 3) :
    (tail 2 m).factorization p = (2 * m - 3).factorization p := by
  have hp_not_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hp_not_three : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) h
    omega
  have hnot0 : ¬ p ∣ 2 * m := by
    intro h
    have hthree : p ∣ (2 * m) - (2 * m - 3) := Nat.dvd_sub h hdiv
    have hdiff : (2 * m) - (2 * m - 3) = 3 := by omega
    exact hp_not_three (by simpa [hdiff] using hthree)
  have hnot1 : ¬ p ∣ 2 * m - 1 := by
    intro h
    have htwo : p ∣ (2 * m - 1) - (2 * m - 3) := Nat.dvd_sub h hdiv
    have hdiff : (2 * m - 1) - (2 * m - 3) = 2 := by omega
    exact hp_not_two (by simpa [hdiff] using htwo)
  have hnot2 : ¬ p ∣ 2 * m - 2 := by
    intro h
    have hone : p ∣ (2 * m - 2) - (2 * m - 3) := Nat.dvd_sub h hdiv
    have hdiff : (2 * m - 2) - (2 * m - 3) = 1 := by omega
    exact hp.not_dvd_one (by simpa [hdiff] using hone)
  have hzero0 : (2 * m).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot0
  have hzero1 : (2 * m - 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot1
  have hzero2 : (2 * m - 2).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot2
  rw [tail_two]
  rw [Nat.factorization_mul
    (mul_ne_zero (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
      (by omega : 2 * m - 2 ≠ 0))
    (by omega : 2 * m - 3 ≠ 0)]
  rw [Nat.factorization_mul
    (mul_ne_zero (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0))
    (by omega : 2 * m - 2 ≠ 0)]
  rw [Nat.factorization_mul (by omega : 2 * m ≠ 0) (by omega : 2 * m - 1 ≠ 0)]
  simp [hzero0, hzero1, hzero2]

theorem tail_two_dvd_of_even_large_budgets
    {m : ℕ}
    (hm2 : 2 ≤ m)
    (h2 : (tail 2 m).factorization 2 ≤ (centralBinom m).factorization 2)
    (h3 : (tail 2 m).factorization 3 ≤ (centralBinom m).factorization 3)
    (hm : ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ m →
      m.factorization p ≤ (centralBinom m).factorization p)
    (hm1 : ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ m - 1 →
      (m - 1).factorization p ≤ (centralBinom m).factorization p) :
    tail 2 m ∣ centralBinom m := by
  refine tail_dvd_centralBinom_of_prime_budget (k := 2) (m := m) hm2 ?_
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    exact h2
  by_cases hp3eq : p = 3
  · subst p
    exact h3
  have hpgt : 3 < p := by
    have hp_two_le : 2 ≤ p := hp.two_le
    omega
  by_cases hpm : p ∣ m
  · rw [tail_two_factorization_eq_m_of_large_dvd_m hp hpgt hm2 hpm]
    exact hm p hp hpgt hpm
  by_cases hpm1 : p ∣ m - 1
  · rw [tail_two_factorization_eq_m_sub_one_of_large_dvd_m_sub_one hp hpgt hm2 hpm1]
    exact hm1 p hp hpgt hpm1
  by_cases hpodd1 : p ∣ 2 * m - 1
  · rw [tail_two_factorization_eq_odd_one_of_large_dvd_odd_one hp hpgt hm2 hpodd1]
    exact tail_two_odd_one_prime_budget hp hpgt (by omega)
  by_cases hpodd3 : p ∣ 2 * m - 3
  · rw [tail_two_factorization_eq_odd_three_of_large_dvd_odd_three hp hpgt hm2 hpodd3]
    exact tail_two_odd_three_prime_budget hp hpgt (by omega)
  have hp_not_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hnot_tail : ¬ p ∣ tail 2 m := by
    intro htail
    have hprod : p ∣ (2 * m) * (2 * m - 1) * (2 * m - 2) * (2 * m - 3) := by
      simpa [tail_two] using htail
    rcases (hp.dvd_mul).1 hprod with hleft | hright3
    · rcases (hp.dvd_mul).1 hleft with hleft' | hdiv2
      · rcases (hp.dvd_mul).1 hleft' with hdiv0 | hdiv1
        · rcases (hp.dvd_mul).1 hdiv0 with htwo | hm'
          · exact hp_not_two htwo
          · exact hpm hm'
        · exact hpodd1 hdiv1
      · have htwo_m1 : p ∣ 2 * (m - 1) := by
          have hsub : 2 * m - 2 = 2 * (m - 1) := by omega
          simpa [hsub] using hdiv2
        rcases (hp.dvd_mul).1 htwo_m1 with htwo | hm1'
        · exact hp_not_two htwo
        · exact hpm1 hm1'
    · exact hpodd3 hright3
  have hzero : (tail 2 m).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_tail
  simp [hzero]

theorem carryAt_two_of_mod_eq_mul
    {p m r : ℕ}
    (hmod : m % p ^ 2 = p * r)
    (hhalf : p ≤ 2 * r) :
    CarryAt p m 2 := by
  unfold CarryAt
  rw [hmod]
  have hcarry : p ^ 2 ≤ 2 * (p * r) := by
    calc
      p ^ 2 = p * p := by ring
      _ ≤ p * (2 * r) := Nat.mul_le_mul_left p hhalf
      _ = 2 * (p * r) := by ring
  simpa [two_mul] using hcarry

theorem carryAt_two_of_mod_eq_mul_add_one
    {p m r : ℕ}
    (hmod : m % p ^ 2 = p * r + 1)
    (hhalf : p ≤ 2 * r) :
    CarryAt p m 2 := by
  unfold CarryAt
  rw [hmod]
  have hcarry : p ^ 2 ≤ 2 * (p * r + 1) := by
    calc
      p ^ 2 = p * p := by ring
      _ ≤ p * (2 * r) := Nat.mul_le_mul_left p hhalf
      _ = 2 * (p * r) := by ring
      _ ≤ 2 * (p * r + 1) := by omega
  simpa [two_mul] using hcarry

/-- Boxed semiprime pattern for the current sharp `k = 2` analytic target. -/
structure BoxedE2K2 (t a b c d : ℕ) : Prop where
  ha : Nat.Prime a
  hb : Nat.Prime b
  hc : Nat.Prime c
  hd : Nat.Prime d
  hx : 36 * t + 35 = c * d
  hm : 72 * t + 71 = a * b
  hcd_lo : 5 * c < 4 * d
  hcd_hi : 3 * d < 4 * c
  hab_lo : 3 * a < 2 * b
  hab_hi : b < 2 * a

theorem boxedE2_x_mod2 (t : ℕ) :
    (36 * t + 35) % 2 = 1 := by
  have h : 36 * t + 35 = 2 * (18 * t + 17) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem boxedE2_x_mod3 (t : ℕ) :
    (36 * t + 35) % 3 = 2 := by
  have h : 36 * t + 35 = 3 * (12 * t + 11) + 2 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem boxedE2_m_mod2 (t : ℕ) :
    (72 * t + 71) % 2 = 1 := by
  have h : 72 * t + 71 = 2 * (36 * t + 35) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem boxedE2_m_mod3 (t : ℕ) :
    (72 * t + 71) % 3 = 2 := by
  have h : 72 * t + 71 = 3 * (24 * t + 23) + 2 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem boxedE2_ab_primes_large
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    3 < a ∧ 3 < b := by
  have ha_dvd : a ∣ 72 * t + 71 := ⟨b, h.hm⟩
  have hb_dvd : b ∣ 72 * t + 71 := ⟨a, by rw [h.hm]; ring⟩
  have hnot_two : ∀ q : ℕ, q ∣ 72 * t + 71 → q ≠ 2 := by
    intro q hq hq2
    have hzero : (72 * t + 71) % 2 = 0 := by
      simpa [hq2] using Nat.dvd_iff_mod_eq_zero.mp hq
    have hone : (72 * t + 71) % 2 = 1 := boxedE2_m_mod2 t
    omega
  have hnot_three : ∀ q : ℕ, q ∣ 72 * t + 71 → q ≠ 3 := by
    intro q hq hq3
    have hzero : (72 * t + 71) % 3 = 0 := by
      simpa [hq3] using Nat.dvd_iff_mod_eq_zero.mp hq
    have htwo : (72 * t + 71) % 3 = 2 := boxedE2_m_mod3 t
    omega
  constructor
  · have ha_ge : 2 ≤ a := h.ha.two_le
    by_contra hle
    have ha_cases : a = 2 ∨ a = 3 := by omega
    cases ha_cases with
    | inl ha2 => exact hnot_two a ha_dvd ha2
    | inr ha3 => exact hnot_three a ha_dvd ha3
  · have hb_ge : 2 ≤ b := h.hb.two_le
    by_contra hle
    have hb_cases : b = 2 ∨ b = 3 := by omega
    cases hb_cases with
    | inl hb2 => exact hnot_two b hb_dvd hb2
    | inr hb3 => exact hnot_three b hb_dvd hb3

theorem boxedE2_cd_primes_large
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    3 < c ∧ 3 < d := by
  have hc_dvd : c ∣ 36 * t + 35 := ⟨d, h.hx⟩
  have hd_dvd : d ∣ 36 * t + 35 := ⟨c, by rw [h.hx]; ring⟩
  have hnot_two : ∀ q : ℕ, q ∣ 36 * t + 35 → q ≠ 2 := by
    intro q hq hq2
    have hzero : (36 * t + 35) % 2 = 0 := by
      simpa [hq2] using Nat.dvd_iff_mod_eq_zero.mp hq
    have hone : (36 * t + 35) % 2 = 1 := boxedE2_x_mod2 t
    omega
  have hnot_three : ∀ q : ℕ, q ∣ 36 * t + 35 → q ≠ 3 := by
    intro q hq hq3
    have hzero : (36 * t + 35) % 3 = 0 := by
      simpa [hq3] using Nat.dvd_iff_mod_eq_zero.mp hq
    have htwo : (36 * t + 35) % 3 = 2 := boxedE2_x_mod3 t
    omega
  constructor
  · have hc_ge : 2 ≤ c := h.hc.two_le
    by_contra hle
    have hc_cases : c = 2 ∨ c = 3 := by omega
    cases hc_cases with
    | inl hc2 => exact hnot_two c hc_dvd hc2
    | inr hc3 => exact hnot_three c hc_dvd hc3
  · have hd_ge : 2 ≤ d := h.hd.two_le
    by_contra hle
    have hd_cases : d = 2 ∨ d = 3 := by omega
    cases hd_cases with
    | inl hd2 => exact hnot_two d hd_dvd hd2
    | inr hd3 => exact hnot_three d hd_dvd hd3

theorem boxedE2_ab_order
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    a < b ∧ b < 2 * a := by
  constructor
  · by_contra hba
    have ha_pos : 0 < a := h.ha.pos
    have hlo : 3 * a < 2 * b := h.hab_lo
    omega
  · exact h.hab_hi

theorem boxedE2_cd_order
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    c < d ∧ d < 2 * c := by
  constructor
  · by_contra hdc
    have hc_pos : 0 < c := h.hc.pos
    have hlo : 5 * c < 4 * d := h.hcd_lo
    omega
  · have hhi : 3 * d < 4 * c := h.hcd_hi
    omega

theorem boxedE2_carry_a
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    CarryAt a (72 * t + 71) 2 := by
  have horder := boxedE2_ab_order h
  have ha_pos : 0 < a := h.ha.pos
  have hb_decomp : a + (b - a) = b := by omega
  have hdiff_lt : b - a < a := by omega
  have hres_lt : a * (b - a) < a ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hdiff_lt ha_pos
  have hprod : a * b = a ^ 2 + a * (b - a) := by
    conv_lhs => rw [← hb_decomp]
    ring
  have hmod : (72 * t + 71) % a ^ 2 = a * (b - a) := by
    rw [h.hm, hprod, Nat.add_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hdiff : a ≤ 2 * (b - a) := by
    have hlo : 3 * a < 2 * b := h.hab_lo
    omega
  have hcarry : a ^ 2 ≤ 2 * (a * (b - a)) := by
    calc
      a ^ 2 = a * a := by ring
      _ ≤ a * (2 * (b - a)) := Nat.mul_le_mul_left a hdiff
      _ = 2 * (a * (b - a)) := by ring
  unfold CarryAt
  rw [hmod]
  simpa [two_mul] using hcarry

theorem boxedE2_carry_b
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    CarryAt b (72 * t + 71) 2 := by
  have horder := boxedE2_ab_order h
  have hb_pos : 0 < b := h.hb.pos
  have hres_lt : a * b < b ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_lt_mul_of_pos_right horder.1 hb_pos
  have hmod : (72 * t + 71) % b ^ 2 = a * b := by
    rw [h.hm]
    exact Nat.mod_eq_of_lt hres_lt
  have hcarry : b ^ 2 ≤ 2 * (a * b) := by
    calc
      b ^ 2 = b * b := by ring
      _ ≤ (2 * a) * b := Nat.mul_le_mul_right b (le_of_lt horder.2)
      _ = 2 * (a * b) := by ring
  unfold CarryAt
  rw [hmod]
  simpa [two_mul] using hcarry

theorem boxedE2_m_eq_two_cd_add_one
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    72 * t + 71 = 2 * c * d + 1 := by
  calc
    72 * t + 71 = 2 * (36 * t + 35) + 1 := by ring
    _ = 2 * (c * d) + 1 := by rw [h.hx]
    _ = 2 * c * d + 1 := by ring

theorem boxedE2_carry_c
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    CarryAt c (72 * t + 71) 2 := by
  have horder := boxedE2_cd_order h
  have hlarge := boxedE2_cd_primes_large h
  have hc_pos : 0 < c := h.hc.pos
  let r := 2 * d - 2 * c
  have hr_pos : 0 < r := by
    dsimp [r]
    omega
  have hr_lt : r < c := by
    dsimp [r]
    have hhi : 3 * d < 4 * c := h.hcd_hi
    omega
  have hres_lt : c * r + 1 < c ^ 2 := by
    have hc_gt_one : 1 < c := by omega
    nlinarith
  have hd_decomp : 2 * d = 2 * c + r := by
    dsimp [r]
    omega
  have hm_decomp : 2 * c * d + 1 = 2 * c ^ 2 + (c * r + 1) := by
    calc
      2 * c * d + 1 = c * (2 * d) + 1 := by ring
      _ = c * (2 * c + r) + 1 := by rw [hd_decomp]
      _ = 2 * c ^ 2 + (c * r + 1) := by ring
  have hmod : (72 * t + 71) % c ^ 2 = c * r + 1 := by
    rw [boxedE2_m_eq_two_cd_add_one h, hm_decomp]
    rw [Nat.add_mod]
    have hzero : (2 * c ^ 2) % c ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (c ^ 2) 2
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hsmall : c ≤ 2 * r := by
    dsimp [r]
    have hlo : 5 * c < 4 * d := h.hcd_lo
    omega
  have hcarry : c ^ 2 ≤ 2 * (c * r + 1) := by
    nlinarith
  unfold CarryAt
  rw [hmod]
  simpa [two_mul] using hcarry

theorem boxedE2_carry_d
    {t a b c d : ℕ} (h : BoxedE2K2 t a b c d) :
    CarryAt d (72 * t + 71) 2 := by
  have horder := boxedE2_cd_order h
  have hlarge := boxedE2_cd_primes_large h
  have hd_pos : 0 < d := h.hd.pos
  let r := 2 * c - d
  have hr_pos : 0 < r := by
    dsimp [r]
    omega
  have hr_lt : r < d := by
    dsimp [r]
    omega
  have hres_lt : d * r + 1 < d ^ 2 := by
    have hd_gt_one : 1 < d := by omega
    nlinarith
  have hc_decomp : 2 * c = d + r := by
    dsimp [r]
    omega
  have hm_decomp : 2 * c * d + 1 = d ^ 2 + (d * r + 1) := by
    calc
      2 * c * d + 1 = d * (2 * c) + 1 := by ring
      _ = d * (d + r) + 1 := by rw [hc_decomp]
      _ = d ^ 2 + (d * r + 1) := by ring
  have hmod : (72 * t + 71) % d ^ 2 = d * r + 1 := by
    rw [boxedE2_m_eq_two_cd_add_one h, hm_decomp]
    rw [Nat.add_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hsmall : d ≤ 2 * r := by
    dsimp [r]
    have hhi : 3 * d < 4 * c := h.hcd_hi
    omega
  have hcarry : d ^ 2 ≤ 2 * (d * r + 1) := by
    nlinarith
  unfold CarryAt
  rw [hmod]
  simpa [two_mul] using hcarry

def BoxedE2SupplyK2 : Prop :=
  ∀ N : ℕ, ∃ t : ℕ, ∃ a : ℕ, ∃ b : ℕ, ∃ c : ℕ, ∃ d : ℕ,
    N ≤ t ∧ BoxedE2K2 t a b c d

theorem boxedE2_m_mod8 (t : ℕ) :
    (72 * t + 71) % 8 = 7 := by
  have h : 72 * t + 71 = 8 * (9 * t + 8) + 7 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem boxedE2_m_mod9 (t : ℕ) :
    (72 * t + 71) % 9 = 8 := by
  have h : 72 * t + 71 = 9 * (8 * t + 7) + 8 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem erdosK2_of_boxedE2Supply_of_pointwise
    (hPoint :
      ∀ {t a b c d : ℕ}, BoxedE2K2 t a b c d → erdosAt 2 (72 * t + 69))
    (hSupply : BoxedE2SupplyK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨t, a, b, c, d, htN, hbox⟩
  refine ⟨72 * t + 69, ?_, hPoint hbox⟩
  omega

/-- First member of the boxed admissible triangle target. -/
def L2 (s : ℕ) : ℕ :=
  20736 * s + 565

/-- Second member of the boxed admissible triangle target. -/
def L3 (s : ℕ) : ℕ :=
  31104 * s + 847

/-- Third member of the boxed admissible triangle target. -/
def L4 (s : ℕ) : ℕ :=
  41472 * s + 1129

/-- Witness `m` in the `L2,L3` boxed-triangle case. -/
def m23 (s : ℕ) : ℕ :=
  3 * L2 s

/-- Witness `m` in the `L2,L4` boxed-triangle case. -/
def m24 (s : ℕ) : ℕ :=
  2 * L2 s

/-- Witness `m` in the `L3,L4` boxed-triangle case. -/
def m34 (s : ℕ) : ℕ :=
  4 * L3 s

def ratioBox2 (a b : ℕ) : Prop :=
  13 * a < 4 * b ∧ 3 * b < 10 * a

def ratioBox3 (a b : ℕ) : Prop :=
  19 * a < 8 * b ∧ 2 * b < 5 * a

def ratioBox4 (a b : ℕ) : Prop :=
  3 * a < 2 * b ∧ 3 * b < 5 * a

/-- Boxed `E_2` certificate for `L2 s`. -/
structure BoxedL2 (s a b : ℕ) : Prop where
  ha : Nat.Prime a
  hb : Nat.Prime b
  hlt : a < b
  hfac : L2 s = a * b
  hbox : ratioBox2 a b

/-- Boxed `E_2` certificate for `L3 s`. -/
structure BoxedL3 (s a b : ℕ) : Prop where
  ha : Nat.Prime a
  hb : Nat.Prime b
  hlt : a < b
  hfac : L3 s = a * b
  hbox : ratioBox3 a b

/-- Boxed `E_2` certificate for `L4 s`. -/
structure BoxedL4 (s a b : ℕ) : Prop where
  ha : Nat.Prime a
  hb : Nat.Prime b
  hlt : a < b
  hfac : L4 s = a * b
  hbox : ratioBox4 a b

theorem L2_mod2 (s : ℕ) :
    L2 s % 2 = 1 := by
  unfold L2
  have h : 20736 * s + 565 = 2 * (10368 * s + 282) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L2_mod3 (s : ℕ) :
    L2 s % 3 = 1 := by
  unfold L2
  have h : 20736 * s + 565 = 3 * (6912 * s + 188) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L3_mod2 (s : ℕ) :
    L3 s % 2 = 1 := by
  unfold L3
  have h : 31104 * s + 847 = 2 * (15552 * s + 423) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L3_mod3 (s : ℕ) :
    L3 s % 3 = 1 := by
  unfold L3
  have h : 31104 * s + 847 = 3 * (10368 * s + 282) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L4_mod2 (s : ℕ) :
    L4 s % 2 = 1 := by
  unfold L4
  have h : 41472 * s + 1129 = 2 * (20736 * s + 564) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L4_mod3 (s : ℕ) :
    L4 s % 3 = 1 := by
  unfold L4
  have h : 41472 * s + 1129 = 3 * (13824 * s + 376) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem prime_factor_large_of_mod2_mod3_one
    {x p : ℕ}
    (hp : Nat.Prime p)
    (hdiv : p ∣ x)
    (hmod2 : x % 2 = 1)
    (hmod3 : x % 3 = 1) :
    3 < p := by
  by_contra hnot
  have hp2le : 2 ≤ p := hp.two_le
  have hcases : p = 2 ∨ p = 3 := by omega
  cases hcases with
  | inl hp2 =>
      have hzero : x % 2 = 0 := by
        simpa [hp2] using Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega
  | inr hp3 =>
      have hzero : x % 3 = 0 := by
        simpa [hp3] using Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega

theorem boxedL2_primes_large
    {s a b : ℕ} (h : BoxedL2 s a b) :
    3 < a ∧ 3 < b := by
  have ha_dvd : a ∣ L2 s := ⟨b, h.hfac⟩
  have hb_dvd : b ∣ L2 s := ⟨a, by rw [h.hfac]; ring⟩
  exact ⟨
    prime_factor_large_of_mod2_mod3_one h.ha ha_dvd (L2_mod2 s) (L2_mod3 s),
    prime_factor_large_of_mod2_mod3_one h.hb hb_dvd (L2_mod2 s) (L2_mod3 s)⟩

theorem boxedL3_primes_large
    {s a b : ℕ} (h : BoxedL3 s a b) :
    3 < a ∧ 3 < b := by
  have ha_dvd : a ∣ L3 s := ⟨b, h.hfac⟩
  have hb_dvd : b ∣ L3 s := ⟨a, by rw [h.hfac]; ring⟩
  exact ⟨
    prime_factor_large_of_mod2_mod3_one h.ha ha_dvd (L3_mod2 s) (L3_mod3 s),
    prime_factor_large_of_mod2_mod3_one h.hb hb_dvd (L3_mod2 s) (L3_mod3 s)⟩

theorem boxedL4_primes_large
    {s a b : ℕ} (h : BoxedL4 s a b) :
    3 < a ∧ 3 < b := by
  have ha_dvd : a ∣ L4 s := ⟨b, h.hfac⟩
  have hb_dvd : b ∣ L4 s := ⟨a, by rw [h.hfac]; ring⟩
  exact ⟨
    prime_factor_large_of_mod2_mod3_one h.ha ha_dvd (L4_mod2 s) (L4_mod3 s),
    prime_factor_large_of_mod2_mod3_one h.hb hb_dvd (L4_mod2 s) (L4_mod3 s)⟩

theorem boxedL2_m23_carry_a
    {s a b : ℕ} (h : BoxedL2 s a b) :
    CarryAt a (3 * L2 s) 2 := by
  let r := 3 * b - 9 * a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 3 * b < 10 * a := h.hbox.2
    omega
  have hthreeb : 3 * b = 9 * a + r := by
    dsimp [r]
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  have hres_lt : a * r < a ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hr_lt h.ha.pos
  have hm_decomp : 3 * L2 s = 9 * a ^ 2 + a * r := by
    rw [h.hfac]
    calc
      3 * (a * b) = a * (3 * b) := by ring
      _ = a * (9 * a + r) := by rw [hthreeb]
      _ = 9 * a ^ 2 + a * r := by ring
  have hmod : (3 * L2 s) % a ^ 2 = a * r := by
    rw [hm_decomp, Nat.add_mod]
    have hzero : (9 * a ^ 2) % a ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (a ^ 2) 9
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL2_m23_carry_b
    {s a b : ℕ} (h : BoxedL2 s a b) :
    CarryAt b (3 * L2 s) 2 := by
  have h3a_lt_b : 3 * a < b := by
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  have hres_lt : 3 * a * b < b ^ 2 := by
    calc
      3 * a * b = (3 * a) * b := by ring
      _ < b * b := Nat.mul_lt_mul_of_pos_right h3a_lt_b h.hb.pos
      _ = b ^ 2 := by ring
  have hmod : (3 * L2 s) % b ^ 2 = b * (3 * a) := by
    rw [h.hfac]
    simpa [mul_assoc, mul_left_comm, mul_comm]
      using Nat.mod_eq_of_lt (a := 3 * (a * b)) (by simpa [mul_assoc] using hres_lt)
  have hhalf : b ≤ 2 * (3 * a) := by
    have hhi : 3 * b < 10 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL2_m24_carry_a
    {s a b : ℕ} (h : BoxedL2 s a b) :
    CarryAt a (2 * L2 s) 2 := by
  let r := 2 * b - 6 * a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 3 * b < 10 * a := h.hbox.2
    omega
  have htwob : 2 * b = 6 * a + r := by
    dsimp [r]
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  have hres_lt : a * r < a ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hr_lt h.ha.pos
  have hm_decomp : 2 * L2 s = 6 * a ^ 2 + a * r := by
    rw [h.hfac]
    calc
      2 * (a * b) = a * (2 * b) := by ring
      _ = a * (6 * a + r) := by rw [htwob]
      _ = 6 * a ^ 2 + a * r := by ring
  have hmod : (2 * L2 s) % a ^ 2 = a * r := by
    rw [hm_decomp, Nat.add_mod]
    have hzero : (6 * a ^ 2) % a ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (a ^ 2) 6
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL2_m24_carry_b
    {s a b : ℕ} (h : BoxedL2 s a b) :
    CarryAt b (2 * L2 s) 2 := by
  have h2a_lt_b : 2 * a < b := by
    have hlo : 13 * a < 4 * b := h.hbox.1
    omega
  have hres_lt : 2 * a * b < b ^ 2 := by
    calc
      2 * a * b = (2 * a) * b := by ring
      _ < b * b := Nat.mul_lt_mul_of_pos_right h2a_lt_b h.hb.pos
      _ = b ^ 2 := by ring
  have hmod : (2 * L2 s) % b ^ 2 = b * (2 * a) := by
    rw [h.hfac]
    simpa [mul_assoc, mul_left_comm, mul_comm]
      using Nat.mod_eq_of_lt (a := 2 * (a * b)) (by simpa [mul_assoc] using hres_lt)
  have hhalf : b ≤ 2 * (2 * a) := by
    have hhi : 3 * b < 10 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL3_m23_carry_a
    {s a b : ℕ} (h : BoxedL3 s a b) :
    CarryAt a (3 * L2 s) 2 := by
  let r := 2 * b - 4 * a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 2 * b < 5 * a := h.hbox.2
    omega
  have htwob : 2 * b = 4 * a + r := by
    dsimp [r]
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  have hres_lt : a * r + 1 < a ^ 2 := by
    have ha_gt_one : 1 < a := h.ha.one_lt
    nlinarith
  have hm_eq : 3 * L2 s = 2 * a * b + 1 := by
    have htri : 3 * L2 s = 2 * L3 s + 1 := by
      unfold L2 L3
      ring
    rw [h.hfac] at htri
    simpa [mul_assoc, mul_left_comm, mul_comm] using htri
  have hm_decomp : 3 * L2 s = 4 * a ^ 2 + (a * r + 1) := by
    rw [hm_eq]
    calc
      2 * a * b + 1 = a * (2 * b) + 1 := by ring
      _ = a * (4 * a + r) + 1 := by rw [htwob]
      _ = 4 * a ^ 2 + (a * r + 1) := by ring
  have hmod : (3 * L2 s) % a ^ 2 = a * r + 1 := by
    rw [hm_decomp, Nat.add_mod]
    have hzero : (4 * a ^ 2) % a ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (a ^ 2) 4
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

theorem boxedL3_m23_carry_b
    {s a b : ℕ} (h : BoxedL3 s a b) :
    CarryAt b (3 * L2 s) 2 := by
  have h2a_lt_b : 2 * a < b := by
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  have hres_lt : 2 * a * b + 1 < b ^ 2 := by
    have hb_gt_one : 1 < b := h.hb.one_lt
    nlinarith
  have hm_eq : 3 * L2 s = 2 * a * b + 1 := by
    have htri : 3 * L2 s = 2 * L3 s + 1 := by
      unfold L2 L3
      ring
    rw [h.hfac] at htri
    simpa [mul_assoc, mul_left_comm, mul_comm] using htri
  have hmod : (3 * L2 s) % b ^ 2 = b * (2 * a) + 1 := by
    rw [hm_eq]
    simpa [mul_assoc, mul_left_comm, mul_comm]
      using Nat.mod_eq_of_lt hres_lt
  have hhalf : b ≤ 2 * (2 * a) := by
    have hhi : 2 * b < 5 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

theorem boxedL3_m34_carry_a
    {s a b : ℕ} (h : BoxedL3 s a b) :
    CarryAt a (4 * L3 s) 2 := by
  let r := 4 * b - 9 * a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 2 * b < 5 * a := h.hbox.2
    omega
  have hfourb : 4 * b = 9 * a + r := by
    dsimp [r]
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  have hres_lt : a * r < a ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hr_lt h.ha.pos
  have hm_decomp : 4 * L3 s = 9 * a ^ 2 + a * r := by
    rw [h.hfac]
    calc
      4 * (a * b) = a * (4 * b) := by ring
      _ = a * (9 * a + r) := by rw [hfourb]
      _ = 9 * a ^ 2 + a * r := by ring
  have hmod : (4 * L3 s) % a ^ 2 = a * r := by
    rw [hm_decomp, Nat.add_mod]
    have hzero : (9 * a ^ 2) % a ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (a ^ 2) 9
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL3_m34_carry_b
    {s a b : ℕ} (h : BoxedL3 s a b) :
    CarryAt b (4 * L3 s) 2 := by
  let r := 4 * a - b
  have hr_lt : r < b := by
    dsimp [r]
    have hlo : 19 * a < 8 * b := h.hbox.1
    omega
  have hfoura : 4 * a = b + r := by
    dsimp [r]
    have hhi : 2 * b < 5 * a := h.hbox.2
    omega
  have hres_lt : b * r < b ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hr_lt h.hb.pos
  have hm_decomp : 4 * L3 s = b ^ 2 + b * r := by
    rw [h.hfac]
    calc
      4 * (a * b) = b * (4 * a) := by ring
      _ = b * (b + r) := by rw [hfoura]
      _ = b ^ 2 + b * r := by ring
  have hmod : (4 * L3 s) % b ^ 2 = b * r := by
    rw [hm_decomp, Nat.add_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : b ≤ 2 * r := by
    dsimp [r]
    have hhi : 2 * b < 5 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul hmod hhalf

theorem boxedL4_m24_carry_a
    {s a b : ℕ} (h : BoxedL4 s a b) :
    CarryAt a (2 * L2 s) 2 := by
  let r := b - a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 3 * b < 5 * a := h.hbox.2
    omega
  have hb : b = a + r := by
    dsimp [r]
    have hlt : a < b := h.hlt
    omega
  have hres_lt : a * r + 1 < a ^ 2 := by
    have ha_gt_one : 1 < a := h.ha.one_lt
    nlinarith
  have hm_eq : 2 * L2 s = a * b + 1 := by
    have htri : 2 * L2 s = L4 s + 1 := by
      unfold L2 L4
      ring
    rw [h.hfac] at htri
    omega
  have hm_decomp : 2 * L2 s = a ^ 2 + (a * r + 1) := by
    rw [hm_eq]
    calc
      a * b + 1 = a * (a + r) + 1 := by rw [hb]
      _ = a ^ 2 + (a * r + 1) := by ring
  have hmod : (2 * L2 s) % a ^ 2 = a * r + 1 := by
    rw [hm_decomp, Nat.add_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 3 * a < 2 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

theorem boxedL4_m24_carry_b
    {s a b : ℕ} (h : BoxedL4 s a b) :
    CarryAt b (2 * L2 s) 2 := by
  have hres_lt : a * b + 1 < b ^ 2 := by
    have hb_gt_one : 1 < b := h.hb.one_lt
    have hab : a < b := h.hlt
    nlinarith
  have hm_eq : 2 * L2 s = a * b + 1 := by
    have htri : 2 * L2 s = L4 s + 1 := by
      unfold L2 L4
      ring
    rw [h.hfac] at htri
    omega
  have hmod : (2 * L2 s) % b ^ 2 = b * a + 1 := by
    rw [hm_eq]
    simpa [mul_comm] using Nat.mod_eq_of_lt hres_lt
  have hhalf : b ≤ 2 * a := by
    have hhi : 3 * b < 5 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

theorem boxedL4_m34_carry_a
    {s a b : ℕ} (h : BoxedL4 s a b) :
    CarryAt a (4 * L3 s) 2 := by
  let r := 3 * b - 4 * a
  have hr_lt : r < a := by
    dsimp [r]
    have hhi : 3 * b < 5 * a := h.hbox.2
    omega
  have hthreeb : 3 * b = 4 * a + r := by
    dsimp [r]
    have hlo : 3 * a < 2 * b := h.hbox.1
    omega
  have hres_lt : a * r + 1 < a ^ 2 := by
    have ha_gt_one : 1 < a := h.ha.one_lt
    nlinarith
  have hm_eq : 4 * L3 s = 3 * a * b + 1 := by
    have htri : 4 * L3 s = 3 * L4 s + 1 := by
      unfold L3 L4
      ring
    rw [h.hfac] at htri
    simpa [mul_assoc, mul_left_comm, mul_comm] using htri
  have hm_decomp : 4 * L3 s = 4 * a ^ 2 + (a * r + 1) := by
    rw [hm_eq]
    calc
      3 * a * b + 1 = a * (3 * b) + 1 := by ring
      _ = a * (4 * a + r) + 1 := by rw [hthreeb]
      _ = 4 * a ^ 2 + (a * r + 1) := by ring
  have hmod : (4 * L3 s) % a ^ 2 = a * r + 1 := by
    rw [hm_decomp, Nat.add_mod]
    have hzero : (4 * a ^ 2) % a ^ 2 = 0 := by
      rw [mul_comm]
      exact Nat.mul_mod_right (a ^ 2) 4
    rw [hzero]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : a ≤ 2 * r := by
    dsimp [r]
    have hlo : 3 * a < 2 * b := h.hbox.1
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

theorem boxedL4_m34_carry_b
    {s a b : ℕ} (h : BoxedL4 s a b) :
    CarryAt b (4 * L3 s) 2 := by
  let r := 3 * a - b
  have hr_lt : r < b := by
    dsimp [r]
    have hlo : 3 * a < 2 * b := h.hbox.1
    omega
  have hthreea : 3 * a = b + r := by
    dsimp [r]
    have hhi : 3 * b < 5 * a := h.hbox.2
    have ha_pos : 0 < a := h.ha.pos
    omega
  have hres_lt : b * r + 1 < b ^ 2 := by
    have hb_gt_one : 1 < b := h.hb.one_lt
    nlinarith
  have hm_eq : 4 * L3 s = 3 * a * b + 1 := by
    have htri : 4 * L3 s = 3 * L4 s + 1 := by
      unfold L3 L4
      ring
    rw [h.hfac] at htri
    simpa [mul_assoc, mul_left_comm, mul_comm] using htri
  have hm_decomp : 4 * L3 s = b ^ 2 + (b * r + 1) := by
    rw [hm_eq]
    calc
      3 * a * b + 1 = b * (3 * a) + 1 := by ring
      _ = b * (b + r) + 1 := by rw [hthreea]
      _ = b ^ 2 + (b * r + 1) := by ring
  have hmod : (4 * L3 s) % b ^ 2 = b * r + 1 := by
    rw [hm_decomp, Nat.add_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt hres_lt]
  have hhalf : b ≤ 2 * r := by
    dsimp [r]
    have hhi : 3 * b < 5 * a := h.hbox.2
    omega
  exact carryAt_two_of_mod_eq_mul_add_one hmod hhalf

/-- At least two boxed members of the admissible triangle occur at `s`. -/
def BoxedTriangleAt (s : ℕ) : Prop :=
  (∃ a2 : ℕ, ∃ b2 : ℕ, ∃ a3 : ℕ, ∃ b3 : ℕ,
    BoxedL2 s a2 b2 ∧ BoxedL3 s a3 b3) ∨
  (∃ a2 : ℕ, ∃ b2 : ℕ, ∃ a4 : ℕ, ∃ b4 : ℕ,
    BoxedL2 s a2 b2 ∧ BoxedL4 s a4 b4) ∨
  (∃ a3 : ℕ, ∃ b3 : ℕ, ∃ a4 : ℕ, ∃ b4 : ℕ,
    BoxedL3 s a3 b3 ∧ BoxedL4 s a4 b4)

/-- The currently open boxed-triangle supply theorem for the `k = 2` route. -/
def BoxedTriangleSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ BoxedTriangleAt s

theorem triangle_L2_L3_identity (s : ℕ) :
    3 * L2 s = 2 * L3 s + 1 := by
  unfold L2 L3
  ring

theorem triangle_L2_L4_identity (s : ℕ) :
    2 * L2 s = L4 s + 1 := by
  unfold L2 L4
  ring

theorem triangle_L3_L4_identity (s : ℕ) :
    4 * L3 s = 3 * L4 s + 1 := by
  unfold L3 L4
  ring

theorem m23_eq_two_L3_add_one (s : ℕ) :
    m23 s = 2 * L3 s + 1 := by
  simpa [m23] using triangle_L2_L3_identity s

theorem m24_eq_L4_add_one (s : ℕ) :
    m24 s = L4 s + 1 := by
  simpa [m24] using triangle_L2_L4_identity s

theorem m34_eq_three_L4_add_one (s : ℕ) :
    m34 s = 3 * L4 s + 1 := by
  simpa [m34] using triangle_L3_L4_identity s

theorem s_le_m23_sub_two (s : ℕ) :
    s ≤ m23 s - 2 := by
  unfold m23 L2
  omega

theorem s_le_m24_sub_two (s : ℕ) :
    s ≤ m24 s - 2 := by
  unfold m24 L2
  omega

theorem s_le_m34_sub_two (s : ℕ) :
    s ≤ m34 s - 2 := by
  unfold m34 L3
  omega

theorem m23_mod64 (s : ℕ) :
    m23 s % 64 = 31 := by
  unfold m23 L2
  have h : 3 * (20736 * s + 565) = 64 * (972 * s + 26) + 31 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem m23_mod81 (s : ℕ) :
    m23 s % 81 = 75 := by
  unfold m23 L2
  have h : 3 * (20736 * s + 565) = 81 * (768 * s + 20) + 75 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem m24_mod64 (s : ℕ) :
    m24 s % 64 = 42 := by
  unfold m24 L2
  have h : 2 * (20736 * s + 565) = 64 * (648 * s + 17) + 42 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem m24_mod81 (s : ℕ) :
    m24 s % 81 = 77 := by
  unfold m24 L2
  have h : 2 * (20736 * s + 565) = 81 * (512 * s + 13) + 77 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem m34_mod64 (s : ℕ) :
    m34 s % 64 = 60 := by
  unfold m34 L3
  have h : 4 * (31104 * s + 847) = 64 * (1944 * s + 52) + 60 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem m34_mod81 (s : ℕ) :
    m34 s % 81 = 67 := by
  unfold m34 L3
  have h : 4 * (31104 * s + 847) = 81 * (1536 * s + 41) + 67 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem mod27_of_mod81_eq_75 {m : ℕ} (hmod : m % 81 = 75) :
    m % 27 = 21 := by
  have h : m % 27 = m % (27 * 3) % 27 := (Nat.mod_mul_right_mod m 27 3).symm
  rw [h]
  norm_num [hmod]

theorem mod9_of_mod81_eq_77 {m : ℕ} (hmod : m % 81 = 77) :
    m % 9 = 5 := by
  have h : m % 9 = m % (9 * 9) % 9 := (Nat.mod_mul_right_mod m 9 9).symm
  rw [h]
  norm_num [hmod]

theorem mod3_of_mod81_eq_77 {m : ℕ} (hmod : m % 81 = 77) :
    m % 3 = 2 := by
  have h : m % 3 = m % (3 * 27) % 3 := (Nat.mod_mul_right_mod m 3 27).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_three_three_of_mod81_eq_75 {m : ℕ} (hmod : m % 81 = 75) :
    CarryAt 3 m 3 := by
  unfold CarryAt
  have h27 : m % 27 = 21 := mod27_of_mod81_eq_75 hmod
  norm_num [h27]

theorem carryAt_three_four_of_mod81_eq_75 {m : ℕ} (hmod : m % 81 = 75) :
    CarryAt 3 m 4 := by
  unfold CarryAt
  norm_num [hmod]

theorem carryAt_three_one_of_mod81_eq_77 {m : ℕ} (hmod : m % 81 = 77) :
    CarryAt 3 m 1 := by
  unfold CarryAt
  have h3 : m % 3 = 2 := mod3_of_mod81_eq_77 hmod
  norm_num [h3]

theorem carryAt_three_two_of_mod81_eq_77 {m : ℕ} (hmod : m % 81 = 77) :
    CarryAt 3 m 2 := by
  unfold CarryAt
  have h9 : m % 9 = 5 := mod9_of_mod81_eq_77 hmod
  norm_num [h9]

theorem carryAt_three_four_of_mod81_eq_67 {m : ℕ} (hmod : m % 81 = 67) :
    CarryAt 3 m 4 := by
  unfold CarryAt
  norm_num [hmod]

theorem tail_two_mod27_of_mod81_eq_75 {m : ℕ} (hmod : m % 81 = 75) :
    tail 2 m % 27 = 9 := by
  have h27 : m % 27 = 21 := mod27_of_mod81_eq_75 hmod
  have h2m : (2 * m) % 27 = 15 := by
    rw [Nat.mul_mod, h27]
  have h1 : (2 * m - 1) % 27 = 14 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 27 = 13 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 27 = 12 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_mod27_of_mod81_eq_77 {m : ℕ} (hmod : m % 81 = 77) :
    tail 2 m % 27 = 9 := by
  have h27 : m % 27 = 23 := by
    have h : m % 27 = m % (27 * 3) % 27 := (Nat.mod_mul_right_mod m 27 3).symm
    rw [h]
    norm_num [hmod]
  have h2m : (2 * m) % 27 = 19 := by
    rw [Nat.mul_mod, h27]
  have h1 : (2 * m - 1) % 27 = 18 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 27 = 17 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 27 = 16 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 27) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_mod9_of_mod81_eq_67 {m : ℕ} (hmod : m % 81 = 67) :
    tail 2 m % 9 = 6 := by
  have h9 : m % 9 = 4 := by
    have h : m % 9 = m % (9 * 9) % 9 := (Nat.mod_mul_right_mod m 9 9).symm
    rw [h]
    norm_num [hmod]
  have h2m : (2 * m) % 9 = 8 := by
    rw [Nat.mul_mod, h9]
  have h1 : (2 * m - 1) % 9 = 7 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 9) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 9 = 6 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 9) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 9 = 5 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 9) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_factorization_three_le_two_of_mod81_eq_75 {m : ℕ}
    (hmod : m % 81 = 75) :
    (tail 2 m).factorization 3 ≤ 2 := by
  by_contra hnot
  have hge : 3 ≤ (tail 2 m).factorization 3 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 81)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 3 ^ 3 ∣ tail 2 m :=
    (Nat.prime_three.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 27 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 27 = 9 := tail_two_mod27_of_mod81_eq_75 hmod
  omega

theorem tail_two_factorization_three_le_two_of_mod81_eq_77 {m : ℕ}
    (hmod : m % 81 = 77) :
    (tail 2 m).factorization 3 ≤ 2 := by
  by_contra hnot
  have hge : 3 ≤ (tail 2 m).factorization 3 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 81)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 3 ^ 3 ∣ tail 2 m :=
    (Nat.prime_three.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 27 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 27 = 9 := tail_two_mod27_of_mod81_eq_77 hmod
  omega

theorem tail_two_factorization_three_le_one_of_mod81_eq_67 {m : ℕ}
    (hmod : m % 81 = 67) :
    (tail 2 m).factorization 3 ≤ 1 := by
  by_contra hnot
  have hge : 2 ≤ (tail 2 m).factorization 3 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 81)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 3 ^ 2 ∣ tail 2 m :=
    (Nat.prime_three.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 9 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 9 = 6 := tail_two_mod9_of_mod81_eq_67 hmod
  omega

theorem tail_two_three_prime_budget_m23 {s : ℕ} :
    (tail 2 (m23 s)).factorization 3 ≤
      (centralBinom (m23 s)).factorization 3 := by
  have htail : (tail 2 (m23 s)).factorization 3 ≤ 2 :=
    tail_two_factorization_three_le_two_of_mod81_eq_75 (m23_mod81 s)
  have hc : 2 ≤ (centralBinom (m23 s)).factorization 3 :=
    centralBinom_factorization_ge_two_of_carries_three_four
      Nat.prime_three (B := Nat.log 3 (2 * m23 s) + 5)
      (by omega) (by omega)
      (carryAt_three_three_of_mod81_eq_75 (m23_mod81 s))
      (carryAt_three_four_of_mod81_eq_75 (m23_mod81 s))
  omega

theorem tail_two_three_prime_budget_m24 {s : ℕ} :
    (tail 2 (m24 s)).factorization 3 ≤
      (centralBinom (m24 s)).factorization 3 := by
  have htail : (tail 2 (m24 s)).factorization 3 ≤ 2 :=
    tail_two_factorization_three_le_two_of_mod81_eq_77 (m24_mod81 s)
  have hc : 2 ≤ (centralBinom (m24 s)).factorization 3 :=
    centralBinom_factorization_ge_two_of_carries
      Nat.prime_three (B := Nat.log 3 (2 * m24 s) + 3)
      (by omega) (by omega)
      (carryAt_three_one_of_mod81_eq_77 (m24_mod81 s))
      (carryAt_three_two_of_mod81_eq_77 (m24_mod81 s))
  omega

theorem tail_two_three_prime_budget_m34 {s : ℕ} :
    (tail 2 (m34 s)).factorization 3 ≤
      (centralBinom (m34 s)).factorization 3 := by
  have htail : (tail 2 (m34 s)).factorization 3 ≤ 1 :=
    tail_two_factorization_three_le_one_of_mod81_eq_67 (m34_mod81 s)
  have hc : 1 ≤ (centralBinom (m34 s)).factorization 3 :=
    centralBinom_factorization_ge_one_of_carry
      (p := 3) (n := m34 s) (B := Nat.log 3 (2 * m34 s) + 5) (e := 4)
      Nat.prime_three (by omega) (by omega) (by omega)
      (carryAt_three_four_of_mod81_eq_67 (m34_mod81 s))
  omega

theorem mod8_of_mod64_eq_31 {m : ℕ} (hmod : m % 64 = 31) :
    m % 8 = 7 := by
  have h : m % 8 = m % (8 * 8) % 8 := (Nat.mod_mul_right_mod m 8 8).symm
  rw [h]
  norm_num [hmod]

theorem mod16_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    m % 16 = 10 := by
  have h : m % 16 = m % (16 * 4) % 16 := (Nat.mod_mul_right_mod m 16 4).symm
  rw [h]
  norm_num [hmod]

theorem mod4_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    m % 4 = 2 := by
  have h : m % 4 = m % (4 * 16) % 4 := (Nat.mod_mul_right_mod m 4 16).symm
  rw [h]
  norm_num [hmod]

theorem mod32_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    m % 32 = 28 := by
  have h : m % 32 = m % (32 * 2) % 32 := (Nat.mod_mul_right_mod m 32 2).symm
  rw [h]
  norm_num [hmod]

theorem mod16_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    m % 16 = 12 := by
  have h : m % 16 = m % (16 * 4) % 16 := (Nat.mod_mul_right_mod m 16 4).symm
  rw [h]
  norm_num [hmod]

theorem mod8_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    m % 8 = 4 := by
  have h : m % 8 = m % (8 * 8) % 8 := (Nat.mod_mul_right_mod m 8 8).symm
  rw [h]
  norm_num [hmod]

theorem carryAt_two_two_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    CarryAt 2 m 2 := by
  unfold CarryAt
  have h4 : m % 4 = 2 := mod4_of_mod64_eq_42 hmod
  norm_num [h4]

theorem carryAt_two_four_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    CarryAt 2 m 4 := by
  unfold CarryAt
  have h16 : m % 16 = 10 := mod16_of_mod64_eq_42 hmod
  norm_num [h16]

theorem carryAt_two_six_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    CarryAt 2 m 6 := by
  unfold CarryAt
  norm_num [hmod]

theorem carryAt_two_three_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    CarryAt 2 m 3 := by
  unfold CarryAt
  have h8 : m % 8 = 4 := mod8_of_mod64_eq_60 hmod
  norm_num [h8]

theorem carryAt_two_four_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    CarryAt 2 m 4 := by
  unfold CarryAt
  have h16 : m % 16 = 12 := mod16_of_mod64_eq_60 hmod
  norm_num [h16]

theorem carryAt_two_five_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    CarryAt 2 m 5 := by
  unfold CarryAt
  have h32 : m % 32 = 28 := mod32_of_mod64_eq_60 hmod
  norm_num [h32]

theorem carryAt_two_six_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    CarryAt 2 m 6 := by
  unfold CarryAt
  norm_num [hmod]

theorem tail_two_mod16_of_mod64_eq_42 {m : ℕ} (hmod : m % 64 = 42) :
    tail 2 m % 16 = 8 := by
  have h16 : m % 16 = 10 := mod16_of_mod64_eq_42 hmod
  have h2m : (2 * m) % 16 = 4 := by
    rw [Nat.mul_mod, h16]
  have h1 : (2 * m - 1) % 16 = 3 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 16 = 2 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 16 = 1 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 16) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_mod32_of_mod64_eq_60 {m : ℕ} (hmod : m % 64 = 60) :
    tail 2 m % 32 = 16 := by
  have h32 : m % 32 = 28 := mod32_of_mod64_eq_60 hmod
  have h2m : (2 * m) % 32 = 24 := by
    rw [Nat.mul_mod, h32]
  have h1 : (2 * m - 1) % 32 = 23 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 1) (n := 32) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h2 : (2 * m - 2) % 32 = 22 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 2) (n := 32) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  have h3 : (2 * m - 3) % 32 = 21 := by
    have h := Nat.mod_sub_of_le (a := 2 * m) (b := 3) (n := 32) (by rw [h2m]; norm_num)
    rw [h2m] at h
    norm_num at h
    exact h.symm
  rw [tail_two]
  norm_num [Nat.mul_mod, h2m, h1, h2, h3]

theorem tail_two_factorization_two_le_three_of_mod64_eq_42 {m : ℕ}
    (hmod : m % 64 = 42) :
    (tail 2 m).factorization 2 ≤ 3 := by
  by_contra hnot
  have hge : 4 ≤ (tail 2 m).factorization 2 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 64)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 2 ^ 4 ∣ tail 2 m :=
    (Nat.prime_two.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 16 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 16 = 8 := tail_two_mod16_of_mod64_eq_42 hmod
  omega

theorem tail_two_factorization_two_le_four_of_mod64_eq_60 {m : ℕ}
    (hmod : m % 64 = 60) :
    (tail 2 m).factorization 2 ≤ 4 := by
  by_contra hnot
  have hge : 5 ≤ (tail 2 m).factorization 2 := by omega
  have hmge : 2 ≤ m := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 64)
    omega
  have htail_ne : tail 2 m ≠ 0 := ne_of_gt (tail_pos (k := 2) (m := m) hmge)
  have hdiv : 2 ^ 5 ∣ tail 2 m :=
    (Nat.prime_two.pow_dvd_iff_le_factorization htail_ne).2 hge
  have hzero : tail 2 m % 32 = 0 := by
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hdiv)
  have htail_mod : tail 2 m % 32 = 16 := tail_two_mod32_of_mod64_eq_60 hmod
  omega

theorem tail_two_two_prime_budget_m23 {s : ℕ} :
    (tail 2 (m23 s)).factorization 2 ≤
      (centralBinom (m23 s)).factorization 2 :=
  tail_two_two_prime_budget_of_mod8_eq_7
    (mod8_of_mod64_eq_31 (m23_mod64 s))
    (B := Nat.log 2 (2 * m23 s) + 4) (by omega) (by omega)

theorem tail_two_two_prime_budget_m24 {s : ℕ} :
    (tail 2 (m24 s)).factorization 2 ≤
      (centralBinom (m24 s)).factorization 2 := by
  have htail : (tail 2 (m24 s)).factorization 2 ≤ 3 :=
    tail_two_factorization_two_le_three_of_mod64_eq_42 (m24_mod64 s)
  have hc : 3 ≤ (centralBinom (m24 s)).factorization 2 :=
    centralBinom_factorization_ge_three_of_carries_two_four_six
      Nat.prime_two (B := Nat.log 2 (2 * m24 s) + 7)
      (by omega) (by omega)
      (carryAt_two_two_of_mod64_eq_42 (m24_mod64 s))
      (carryAt_two_four_of_mod64_eq_42 (m24_mod64 s))
      (carryAt_two_six_of_mod64_eq_42 (m24_mod64 s))
  omega

theorem tail_two_two_prime_budget_m34 {s : ℕ} :
    (tail 2 (m34 s)).factorization 2 ≤
      (centralBinom (m34 s)).factorization 2 := by
  have htail : (tail 2 (m34 s)).factorization 2 ≤ 4 :=
    tail_two_factorization_two_le_four_of_mod64_eq_60 (m34_mod64 s)
  have hc : 4 ≤ (centralBinom (m34 s)).factorization 2 :=
    centralBinom_factorization_ge_four_of_carries_three_four_five_six
      Nat.prime_two (B := Nat.log 2 (2 * m34 s) + 7)
      (by omega) (by omega)
      (carryAt_two_three_of_mod64_eq_60 (m34_mod64 s))
      (carryAt_two_four_of_mod64_eq_60 (m34_mod64 s))
      (carryAt_two_five_of_mod64_eq_60 (m34_mod64 s))
      (carryAt_two_six_of_mod64_eq_60 (m34_mod64 s))
  omega

theorem boxedTriangle23_tail_dvd
    {s a b c d : ℕ}
    (h2 : BoxedL2 s a b)
    (h3 : BoxedL3 s c d) :
    tail 2 (3 * L2 s) ∣ centralBinom (3 * L2 s) := by
  have hm2 : 2 ≤ 3 * L2 s := by
    unfold L2
    omega
  have hsmall2 :
      (tail 2 (3 * L2 s)).factorization 2 ≤
        (centralBinom (3 * L2 s)).factorization 2 := by
    simpa [m23] using tail_two_two_prime_budget_m23 (s := s)
  have hsmall3 :
      (tail 2 (3 * L2 s)).factorization 3 ≤
        (centralBinom (3 * L2 s)).factorization 3 := by
    simpa [m23] using tail_two_three_prime_budget_m23 (s := s)
  have h2large := boxedL2_primes_large h2
  have h3large := boxedL3_primes_large h3
  have hm_eq : 3 * L2 s = 3 * a * b := by
    rw [h2.hfac]
    ring
  have hm_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 3 * L2 s →
        (3 * L2 s).factorization p ≤ (centralBinom (3 * L2 s)).factorization p :=
    large_budget_m_of_semiprime
      (m := 3 * L2 s) (D := 3) (a := a) (b := b)
      small23Only_three h2.ha h2.hb h2large.1 h2large.2
      (ne_of_lt h2.hlt) hm_eq
      (boxedL2_m23_carry_a h2) (boxedL2_m23_carry_b h2)
  have hm1_eq : 3 * L2 s - 1 = 2 * c * d := by
    have htri : 3 * L2 s = 2 * L3 s + 1 := by
      unfold L2 L3
      ring
    have htri' : 3 * L2 s = 2 * c * d + 1 := by
      rw [h3.hfac] at htri
      simpa [mul_assoc, mul_left_comm, mul_comm] using htri
    rw [htri']
    omega
  have hm1_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 3 * L2 s - 1 →
        (3 * L2 s - 1).factorization p ≤
          (centralBinom (3 * L2 s)).factorization p :=
    large_budget_m_sub_one_of_semiprime
      (m := 3 * L2 s) (D := 2) (a := c) (b := d)
      small23Only_two h3.ha h3.hb h3large.1 h3large.2
      (ne_of_lt h3.hlt) hm1_eq
      (boxedL3_m23_carry_a h3) (boxedL3_m23_carry_b h3)
  exact tail_two_dvd_of_even_large_budgets hm2 hsmall2 hsmall3 hm_budget hm1_budget

theorem boxedTriangle24_tail_dvd
    {s a b c d : ℕ}
    (h2 : BoxedL2 s a b)
    (h4 : BoxedL4 s c d) :
    tail 2 (2 * L2 s) ∣ centralBinom (2 * L2 s) := by
  have hm2 : 2 ≤ 2 * L2 s := by
    unfold L2
    omega
  have hsmall2 :
      (tail 2 (2 * L2 s)).factorization 2 ≤
        (centralBinom (2 * L2 s)).factorization 2 := by
    simpa [m24] using tail_two_two_prime_budget_m24 (s := s)
  have hsmall3 :
      (tail 2 (2 * L2 s)).factorization 3 ≤
        (centralBinom (2 * L2 s)).factorization 3 := by
    simpa [m24] using tail_two_three_prime_budget_m24 (s := s)
  have h2large := boxedL2_primes_large h2
  have h4large := boxedL4_primes_large h4
  have hm_eq : 2 * L2 s = 2 * a * b := by
    rw [h2.hfac]
    ring
  have hm_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 2 * L2 s →
        (2 * L2 s).factorization p ≤ (centralBinom (2 * L2 s)).factorization p :=
    large_budget_m_of_semiprime
      (m := 2 * L2 s) (D := 2) (a := a) (b := b)
      small23Only_two h2.ha h2.hb h2large.1 h2large.2
      (ne_of_lt h2.hlt) hm_eq
      (boxedL2_m24_carry_a h2) (boxedL2_m24_carry_b h2)
  have hm1_eq : 2 * L2 s - 1 = 1 * c * d := by
    have htri : 2 * L2 s = L4 s + 1 := by
      unfold L2 L4
      ring
    have htri' : 2 * L2 s = c * d + 1 := by
      rw [h4.hfac] at htri
      simpa [mul_assoc, mul_left_comm, mul_comm] using htri
    rw [htri']
    simp [one_mul]
  have hm1_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 2 * L2 s - 1 →
        (2 * L2 s - 1).factorization p ≤
          (centralBinom (2 * L2 s)).factorization p :=
    large_budget_m_sub_one_of_semiprime
      (m := 2 * L2 s) (D := 1) (a := c) (b := d)
      small23Only_one h4.ha h4.hb h4large.1 h4large.2
      (ne_of_lt h4.hlt) hm1_eq
      (boxedL4_m24_carry_a h4) (boxedL4_m24_carry_b h4)
  exact tail_two_dvd_of_even_large_budgets hm2 hsmall2 hsmall3 hm_budget hm1_budget

theorem boxedTriangle34_tail_dvd
    {s a b c d : ℕ}
    (h3 : BoxedL3 s a b)
    (h4 : BoxedL4 s c d) :
    tail 2 (4 * L3 s) ∣ centralBinom (4 * L3 s) := by
  have hm2 : 2 ≤ 4 * L3 s := by
    unfold L3
    omega
  have hsmall2 :
      (tail 2 (4 * L3 s)).factorization 2 ≤
        (centralBinom (4 * L3 s)).factorization 2 := by
    simpa [m34] using tail_two_two_prime_budget_m34 (s := s)
  have hsmall3 :
      (tail 2 (4 * L3 s)).factorization 3 ≤
        (centralBinom (4 * L3 s)).factorization 3 := by
    simpa [m34] using tail_two_three_prime_budget_m34 (s := s)
  have h3large := boxedL3_primes_large h3
  have h4large := boxedL4_primes_large h4
  have hm_eq : 4 * L3 s = 4 * a * b := by
    rw [h3.hfac]
    ring
  have hm_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 4 * L3 s →
        (4 * L3 s).factorization p ≤ (centralBinom (4 * L3 s)).factorization p :=
    large_budget_m_of_semiprime
      (m := 4 * L3 s) (D := 4) (a := a) (b := b)
      small23Only_four h3.ha h3.hb h3large.1 h3large.2
      (ne_of_lt h3.hlt) hm_eq
      (boxedL3_m34_carry_a h3) (boxedL3_m34_carry_b h3)
  have hm1_eq : 4 * L3 s - 1 = 3 * c * d := by
    have htri : 4 * L3 s = 3 * L4 s + 1 := by
      unfold L3 L4
      ring
    have htri' : 4 * L3 s = 3 * c * d + 1 := by
      rw [h4.hfac] at htri
      simpa [mul_assoc, mul_left_comm, mul_comm] using htri
    rw [htri']
    omega
  have hm1_budget :
      ∀ p : ℕ, Nat.Prime p → 3 < p → p ∣ 4 * L3 s - 1 →
        (4 * L3 s - 1).factorization p ≤
          (centralBinom (4 * L3 s)).factorization p :=
    large_budget_m_sub_one_of_semiprime
      (m := 4 * L3 s) (D := 3) (a := c) (b := d)
      small23Only_three h4.ha h4.hb h4large.1 h4large.2
      (ne_of_lt h4.hlt) hm1_eq
      (boxedL4_m34_carry_a h4) (boxedL4_m34_carry_b h4)
  exact tail_two_dvd_of_even_large_budgets hm2 hsmall2 hsmall3 hm_budget hm1_budget

theorem L2_mod8 (s : ℕ) :
    L2 s % 8 = 5 := by
  unfold L2
  have h : 20736 * s + 565 = 8 * (2592 * s + 70) + 5 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L3_mod8 (s : ℕ) :
    L3 s % 8 = 7 := by
  unfold L3
  have h : 31104 * s + 847 = 8 * (3888 * s + 105) + 7 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem L4_mod8 (s : ℕ) :
    L4 s % 8 = 1 := by
  unfold L4
  have h : 41472 * s + 1129 = 8 * (5184 * s + 141) + 1 := by ring
  rw [h, Nat.add_mod, Nat.mul_mod_right]

theorem erdosK2_of_boxedTriangleSupply_of_pointwise
    (hPoint : ∀ {s : ℕ}, BoxedTriangleAt s → ∃ n : ℕ, s ≤ n ∧ erdosAt 2 n)
    (hSupply : BoxedTriangleSupplyK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨s, hNs, htri⟩
  rcases hPoint htri with ⟨n, hsn, hn⟩
  exact ⟨n, le_trans hNs hsn, hn⟩

theorem boxedTriangleAt_pointwise_of_tail_dvd
    (h23 : ∀ {s a b c d : ℕ},
      BoxedL2 s a b → BoxedL3 s c d →
        tail 2 (m23 s) ∣ centralBinom (m23 s))
    (h24 : ∀ {s a b c d : ℕ},
      BoxedL2 s a b → BoxedL4 s c d →
        tail 2 (m24 s) ∣ centralBinom (m24 s))
    (h34 : ∀ {s a b c d : ℕ},
      BoxedL3 s a b → BoxedL4 s c d →
        tail 2 (m34 s) ∣ centralBinom (m34 s))
    {s : ℕ}
    (h : BoxedTriangleAt s) :
    ∃ n : ℕ, s ≤ n ∧ erdosAt 2 n := by
  rcases h with h23case | hrest
  · rcases h23case with ⟨a, b, c, d, h2, h3⟩
    refine ⟨m23 s - 2, s_le_m23_sub_two s, ?_⟩
    have hm : 2 ≤ m23 s := by
      unfold m23 L2
      omega
    exact erdosAt2_sub_two_of_tail_dvd hm (h23 h2 h3)
  · rcases hrest with h24case | h34case
    · rcases h24case with ⟨a, b, c, d, h2, h4⟩
      refine ⟨m24 s - 2, s_le_m24_sub_two s, ?_⟩
      have hm : 2 ≤ m24 s := by
        unfold m24 L2
        omega
      exact erdosAt2_sub_two_of_tail_dvd hm (h24 h2 h4)
    · rcases h34case with ⟨a, b, c, d, h3, h4⟩
      refine ⟨m34 s - 2, s_le_m34_sub_two s, ?_⟩
      have hm : 2 ≤ m34 s := by
        unfold m34 L3
        omega
      exact erdosAt2_sub_two_of_tail_dvd hm (h34 h3 h4)

theorem erdosK2_of_boxedTriangleSupply_of_tail_dvd
    (h23 : ∀ {s a b c d : ℕ},
      BoxedL2 s a b → BoxedL3 s c d →
        tail 2 (m23 s) ∣ centralBinom (m23 s))
    (h24 : ∀ {s a b c d : ℕ},
      BoxedL2 s a b → BoxedL4 s c d →
        tail 2 (m24 s) ∣ centralBinom (m24 s))
    (h34 : ∀ {s a b c d : ℕ},
      BoxedL3 s a b → BoxedL4 s c d →
        tail 2 (m34 s) ∣ centralBinom (m34 s))
    (hSupply : BoxedTriangleSupplyK2) :
    erdosFixed 2 := by
  refine erdosK2_of_boxedTriangleSupply_of_pointwise ?_ hSupply
  intro s htri
  exact boxedTriangleAt_pointwise_of_tail_dvd h23 h24 h34 htri

theorem boxedTriangleAt_pointwise
    {s : ℕ}
    (h : BoxedTriangleAt s) :
    ∃ n : ℕ, s ≤ n ∧ erdosAt 2 n := by
  refine boxedTriangleAt_pointwise_of_tail_dvd ?_ ?_ ?_ h
  · intro s a b c d h2 h3
    simpa [m23] using boxedTriangle23_tail_dvd h2 h3
  · intro s a b c d h2 h4
    simpa [m24] using boxedTriangle24_tail_dvd h2 h4
  · intro s a b c d h3 h4
    simpa [m34] using boxedTriangle34_tail_dvd h3 h4

theorem erdosK2_of_boxedTriangleSupply
    (hSupply : BoxedTriangleSupplyK2) :
    erdosFixed 2 := by
  exact erdosK2_of_boxedTriangleSupply_of_pointwise
    (fun h => boxedTriangleAt_pointwise h) hSupply

/-- Integer parameters for a finite `k = 2` pattern certificate. -/
structure K2Params where
  x : ℕ
  P0 : ℕ
  pLo : ℕ
  pHi : ℕ
  qLo : ℕ
  qHi : ℕ
  sMax : ℕ
  x_ge_2 : 2 ≤ x
  P0_ge_3 : 3 ≤ P0
  sMax_lt_pLo : sMax < pLo
  P0_lt_sMax : P0 < sMax
  four_lt_pLo : 4 < pLo
  four_lt_qLo : 4 < qLo
  qHi_sq_le_two_x : qHi ^ 2 ≤ 2 * x
  four_x_lt_pLo_cube : 4 * x < pLo ^ 3

def InBand (lo hi p : ℕ) : Prop :=
  lo < p ∧ p ≤ hi

/--
Exact same-band specialization for the near-square-root bilinear target.

This is deliberately optional: the finite carry implication only needs concrete
integer bands, while the still-open supply theorem may choose coincident
`p`/`q` bands at the balanced edge.
-/
def SameLargePrimeBandK2 (cfg : K2Params) : Prop :=
  cfg.pLo = cfg.qLo ∧ cfg.pHi = cfg.qHi

structure PQSWitnessK2 where
  p1 : ℕ
  q1 : ℕ
  s1 : ℕ
  p2 : ℕ
  q2 : ℕ
  s2 : ℕ

/-- Tuple form used only for exact finite counting over a rectangular box. -/
structure CountTupleK2 where
  n : ℕ
  p1 : ℕ
  q1 : ℕ
  s1 : ℕ
  p2 : ℕ
  q2 : ℕ
  s2 : ℕ
  deriving DecidableEq

def CountTupleK2.toWitness (t : CountTupleK2) : PQSWitnessK2 :=
  { p1 := t.p1, q1 := t.q1, s1 := t.s1,
    p2 := t.p2, q2 := t.q2, s2 := t.s2 }

/--
Finite rectangular search box for the balanced bilinear target.

The filter below carries the mathematical predicate; this box only supplies an
exact finite support for the future analytic count.
-/
def candidateTupleBoxK2 (cfg : K2Params) : Finset CountTupleK2 :=
  let S0 := (Finset.Icc cfg.x (2 * cfg.x)).product (Finset.Icc 0 cfg.pHi)
  let S1 := S0.product (Finset.Icc 0 cfg.qHi)
  let S2 := S1.product (Finset.Icc 0 cfg.sMax)
  let S3 := S2.product (Finset.Icc 0 cfg.pHi)
  let S4 := S3.product (Finset.Icc 0 cfg.qHi)
  let S5 := S4.product (Finset.Icc 0 cfg.sMax)
  S5.image
    (fun t =>
      match t with
      | ((((((n, p1), q1), s1), p2), q2), s2) =>
          { n := n, p1 := p1, q1 := q1, s1 := s1,
            p2 := p2, q2 := q2, s2 := s2 })

/-- Single-side `p*q*s` tuple used for restricted divisor weights. -/
structure PQSTripleK2 where
  p : ℕ
  q : ℕ
  s : ℕ
  deriving DecidableEq

def pqsTripleBoxK2 (cfg : K2Params) : Finset PQSTripleK2 :=
  let S0 := (Finset.Icc 0 cfg.pHi).product (Finset.Icc 0 cfg.qHi)
  let S1 := S0.product (Finset.Icc 0 cfg.sMax)
  S1.image
    (fun t =>
      match t with
      | ((p, q), s) => { p := p, q := q, s := s })

def RestrictedPQSAnatomyK2
    (cfg : K2Params) (m : ℕ) (t : PQSTripleK2) : Prop :=
  m = t.p * t.q * t.s ∧
  Nat.Prime t.p ∧ Nat.Prime t.q ∧
  InBand cfg.pLo cfg.pHi t.p ∧
  InBand cfg.qLo cfg.qHi t.q ∧
  0 < t.s ∧ t.s ≤ cfg.sMax ∧
  ¬ t.p ^ 2 ∣ m ∧
  ¬ t.q ^ 2 ∣ m

instance (cfg : K2Params) (m : ℕ) :
    DecidablePred (RestrictedPQSAnatomyK2 cfg m) := by
  intro t
  unfold RestrictedPQSAnatomyK2 InBand
  infer_instance

def RestrictedPQSWeightK2 (cfg : K2Params) (m : ℕ) : ℕ :=
  ((pqsTripleBoxK2 cfg).filter (RestrictedPQSAnatomyK2 cfg m)).card

def SawtoothPQSAnatomyK2
    (cfg : K2Params) (m j coeff : ℕ) (t : PQSTripleK2) : Prop :=
  RestrictedPQSAnatomyK2 cfg m t ∧
  SawJ j t.p (coeff * t.q * t.s) ∧
  SawJ j t.q (coeff * t.p * t.s)

instance (cfg : K2Params) (m j coeff : ℕ) :
    DecidablePred (SawtoothPQSAnatomyK2 cfg m j coeff) := by
  intro t
  unfold SawtoothPQSAnatomyK2 RestrictedPQSAnatomyK2 InBand SawJ SawtoothInt
  infer_instance

def SawtoothPQSWeightWithK2
    (cfg : K2Params) (m j coeff : ℕ) : ℤ :=
  (((pqsTripleBoxK2 cfg).filter
    (SawtoothPQSAnatomyK2 cfg m j coeff)).card : ℤ)

def SawtoothPQSWeightK2 (cfg : K2Params) (m : ℕ) : ℤ :=
  SawtoothPQSWeightWithK2 cfg m 1 1

def SawtoothPQSWeightRightK2 (cfg : K2Params) (m : ℕ) : ℤ :=
  SawtoothPQSWeightWithK2 cfg m 2 2

def CarryAwareShiftedDivisorSummandK2
    (cfg : K2Params) (n : ℕ) : ℤ :=
  SawtoothPQSWeightK2 cfg (n + 1) *
    SawtoothPQSWeightRightK2 cfg ((n + 2) / 2)

/-- Prime-pair support for the switched small-cofactor formulation. -/
structure SemiprimePairK2 where
  p : ℕ
  q : ℕ
  deriving DecidableEq

def semiprimePairBoxK2 (cfg : K2Params) : Finset SemiprimePairK2 :=
  ((Finset.Icc 0 cfg.pHi).product (Finset.Icc 0 cfg.qHi)).image
    (fun t => { p := t.1, q := t.2 })

/--
Marked semiprime weight at a fixed small cofactor and semiprime value.

`coeff` is `1` on the `n+1` side and `2` on the `n+2` side.  Positivity of
the finite weights is a witness-extraction condition, not an analytic theorem.
-/
def MarkedSemiprimePairK2
    (cfg : K2Params) (s M j coeff : ℕ) (a : SemiprimePairK2) : Prop :=
  M = a.p * a.q ∧
  Nat.Prime a.p ∧ Nat.Prime a.q ∧
  InBand cfg.pLo cfg.pHi a.p ∧
  InBand cfg.qLo cfg.qHi a.q ∧
  ¬ a.p ^ 2 ∣ coeff * s * M ∧
  ¬ a.q ^ 2 ∣ coeff * s * M ∧
  SawJ j a.p (coeff * a.q * s) ∧
  SawJ j a.q (coeff * a.p * s)

instance (cfg : K2Params) (s M j coeff : ℕ) :
    DecidablePred (MarkedSemiprimePairK2 cfg s M j coeff) := by
  intro a
  unfold MarkedSemiprimePairK2 InBand SawJ SawtoothInt
  infer_instance

def MarkedSemiprimeWeightWithK2
    (cfg : K2Params) (s M j coeff : ℕ) : ℕ :=
  ((semiprimePairBoxK2 cfg).filter
    (MarkedSemiprimePairK2 cfg s M j coeff)).card

def MarkedSemiprimeWeightK2 (cfg : K2Params) (s M : ℕ) : ℕ :=
  MarkedSemiprimeWeightWithK2 cfg s M 1 1

def MarkedSemiprimeWeightRightK2 (cfg : K2Params) (s M : ℕ) : ℕ :=
  MarkedSemiprimeWeightWithK2 cfg s M 2 2

/--
Variable-`s` boxed semiprime mark.

The ratio constraint is written without division as `q ≤ 2*s*p`.  This is the
finite Lean side of the current analytic target: the box widens with the small
cofactor `s`, while the same Kummer/sawtooth marks remain explicit.
-/
def SBoxedSemiprimePairK2
    (cfg : K2Params) (s M j coeff : ℕ) (a : SemiprimePairK2) : Prop :=
  MarkedSemiprimePairK2 cfg s M j coeff a ∧
  a.p < a.q ∧
  a.q ≤ 2 * s * a.p

instance (cfg : K2Params) (s M j coeff : ℕ) :
    DecidablePred (SBoxedSemiprimePairK2 cfg s M j coeff) := by
  intro a
  unfold SBoxedSemiprimePairK2 MarkedSemiprimePairK2 InBand SawJ SawtoothInt
  infer_instance

def SBoxedSemiprimeWeightWithK2
    (cfg : K2Params) (s M j coeff : ℕ) : ℕ :=
  ((semiprimePairBoxK2 cfg).filter
    (SBoxedSemiprimePairK2 cfg s M j coeff)).card

def SBoxedSemiprimeWeightK2 (cfg : K2Params) (s M : ℕ) : ℕ :=
  SBoxedSemiprimeWeightWithK2 cfg s M 1 1

def SBoxedSemiprimeWeightRightK2 (cfg : K2Params) (s M : ℕ) : ℕ :=
  SBoxedSemiprimeWeightWithK2 cfg s M 2 2

theorem semiprimePair_mem_box_of_sBoxed
    {cfg : K2Params} {s M j coeff : ℕ} {a : SemiprimePairK2}
    (hPair : SBoxedSemiprimePairK2 cfg s M j coeff a) :
    a ∈ semiprimePairBoxK2 cfg := by
  rcases hPair with
    ⟨⟨_hM, _hp, _hq, hpBand, hqBand, _hpSq, _hqSq,
        _hpSaw, _hqSaw⟩, _horder, _hratio⟩
  unfold semiprimePairBoxK2
  refine Finset.mem_image.mpr ?_
  refine ⟨(a.p, a.q), ?_, rfl⟩
  simp [hpBand.2, hqBand.2]

theorem sBoxedSemiprimeWeightWith_pos_of_pair
    {cfg : K2Params} {s M j coeff : ℕ} {a : SemiprimePairK2}
    (hPair : SBoxedSemiprimePairK2 cfg s M j coeff a) :
    0 < SBoxedSemiprimeWeightWithK2 cfg s M j coeff := by
  unfold SBoxedSemiprimeWeightWithK2
  exact Finset.card_pos.mpr
    ⟨a, Finset.mem_filter.mpr
      ⟨semiprimePair_mem_box_of_sBoxed hPair, hPair⟩⟩

theorem markedSemiprimeWeightWith_pos_of_sBoxed
    {cfg : K2Params} {s M j coeff : ℕ}
    (hpos : 0 < SBoxedSemiprimeWeightWithK2 cfg s M j coeff) :
    0 < MarkedSemiprimeWeightWithK2 cfg s M j coeff := by
  unfold SBoxedSemiprimeWeightWithK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
  rcases Finset.mem_filter.mp ha with ⟨hbox, hmarked, _horder, _hratio⟩
  unfold MarkedSemiprimeWeightWithK2
  exact Finset.card_pos.mpr
    ⟨a, Finset.mem_filter.mpr ⟨hbox, hmarked⟩⟩

def PQSEquationK2 (w : PQSWitnessK2) : Prop :=
  w.p1 * w.q1 * w.s1 + 1 = 2 * w.p2 * w.q2 * w.s2

def PQSLeftK2 (w : PQSWitnessK2) : ℕ :=
  w.p1 * w.s1 * w.q1

def PQSRightK2 (w : PQSWitnessK2) : ℕ :=
  2 * w.p2 * w.s2 * w.q2

def PQSEquationOrderedK2 (w : PQSWitnessK2) : Prop :=
  PQSLeftK2 w + 1 = PQSRightK2 w

theorem pqsEquationK2_iff_ordered {w : PQSWitnessK2} :
    PQSEquationK2 w ↔ PQSEquationOrderedK2 w := by
  unfold PQSEquationK2 PQSEquationOrderedK2 PQSLeftK2 PQSRightK2
  constructor <;> intro h <;>
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

def BandedAnatomyK2 (cfg : K2Params) (n : ℕ) : Prop :=
  cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧
  n % 16 = 12 ∧
  (∀ r : ℕ, Nat.Prime r → r ≤ cfg.P0 → r ≠ 2 → r ∣ n) ∧
  ∃ p1 : ℕ, ∃ q1 : ℕ, ∃ s1 : ℕ,
  ∃ p2 : ℕ, ∃ q2 : ℕ, ∃ s2 : ℕ,
    n + 1 = p1 * q1 * s1 ∧
    n + 2 = 2 * p2 * q2 * s2 ∧
    Nat.Prime p1 ∧ Nat.Prime q1 ∧
    Nat.Prime p2 ∧ Nat.Prime q2 ∧
    InBand cfg.pLo cfg.pHi p1 ∧
    InBand cfg.qLo cfg.qHi q1 ∧
    InBand cfg.pLo cfg.pHi p2 ∧
    InBand cfg.qLo cfg.qHi q2 ∧
    0 < s1 ∧ 0 < s2 ∧
    s1 ≤ cfg.sMax ∧ s2 ≤ cfg.sMax ∧
    ¬ p1 ^ 2 ∣ n + 1 ∧
    ¬ q1 ^ 2 ∣ n + 1 ∧
    ¬ p2 ^ 2 ∣ n + 2 ∧
    ¬ q2 ^ 2 ∣ n + 2

def SawtoothK2 (_cfg : K2Params) (n : ℕ) : Prop :=
  ∃ p1 : ℕ, ∃ q1 : ℕ, ∃ s1 : ℕ,
  ∃ p2 : ℕ, ∃ q2 : ℕ, ∃ s2 : ℕ,
    n + 1 = p1 * q1 * s1 ∧
    n + 2 = 2 * p2 * q2 * s2 ∧
    SawJ 1 p1 (q1 * s1) ∧
    SawJ 1 q1 (p1 * s1) ∧
    SawJ 2 p2 (2 * q2 * s2) ∧
    SawJ 2 q2 (2 * p2 * s2)

def MediumHygieneK2 (cfg : K2Params) (n : ℕ) : Prop :=
  ∀ r : ℕ, Nat.Prime r →
    cfg.P0 < r → r ≤ cfg.sMax →
      2 * (window n 2).factorization r ≤ (centralBinom n).factorization r

def FiniteMediumHygieneK2 (cfg : K2Params) (n : ℕ) : Prop :=
  ∀ r ∈ Finset.Icc (cfg.P0 + 1) cfg.sMax,
    Nat.Prime r →
      2 * (window n 2).factorization r ≤ (centralBinom n).factorization r

theorem mediumHygiene_of_finiteMediumHygiene
    {cfg : K2Params} {n : ℕ}
    (hFinite : FiniteMediumHygieneK2 cfg n) :
    MediumHygieneK2 cfg n := by
  intro r hr hP0 hrs
  exact hFinite r (Finset.mem_Icc.mpr ⟨by omega, hrs⟩) hr

def BandedAnatomyWitnessK2 (cfg : K2Params) (n : ℕ) (w : PQSWitnessK2) : Prop :=
  cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧
  n % 16 = 12 ∧
  (∀ r : ℕ, Nat.Prime r → r ≤ cfg.P0 → r ≠ 2 → r ∣ n) ∧
  n + 1 = w.p1 * w.q1 * w.s1 ∧
  n + 2 = 2 * w.p2 * w.q2 * w.s2 ∧
  Nat.Prime w.p1 ∧ Nat.Prime w.q1 ∧
  Nat.Prime w.p2 ∧ Nat.Prime w.q2 ∧
  InBand cfg.pLo cfg.pHi w.p1 ∧
  InBand cfg.qLo cfg.qHi w.q1 ∧
  InBand cfg.pLo cfg.pHi w.p2 ∧
  InBand cfg.qLo cfg.qHi w.q2 ∧
  0 < w.s1 ∧ 0 < w.s2 ∧
  w.s1 ≤ cfg.sMax ∧ w.s2 ≤ cfg.sMax ∧
  ¬ w.p1 ^ 2 ∣ n + 1 ∧
  ¬ w.q1 ^ 2 ∣ n + 1 ∧
  ¬ w.p2 ^ 2 ∣ n + 2 ∧
  ¬ w.q2 ^ 2 ∣ n + 2

def FiniteSmallOddK2 (cfg : K2Params) (n : ℕ) : Prop :=
  ∀ r ∈ Finset.Icc 0 cfg.P0, Nat.Prime r → r ≠ 2 → r ∣ n

theorem smallOdd_of_finiteSmallOdd
    {cfg : K2Params} {n : ℕ}
    (hFinite : FiniteSmallOddK2 cfg n) :
    ∀ r : ℕ, Nat.Prime r → r ≤ cfg.P0 → r ≠ 2 → r ∣ n := by
  intro r hr hr_le hr_ne_two
  exact hFinite r (Finset.mem_Icc.mpr ⟨by omega, hr_le⟩) hr hr_ne_two

def FiniteBandedAnatomyWitnessK2
    (cfg : K2Params) (n : ℕ) (w : PQSWitnessK2) : Prop :=
  cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧
  n % 16 = 12 ∧
  FiniteSmallOddK2 cfg n ∧
  n + 1 = w.p1 * w.q1 * w.s1 ∧
  n + 2 = 2 * w.p2 * w.q2 * w.s2 ∧
  Nat.Prime w.p1 ∧ Nat.Prime w.q1 ∧
  Nat.Prime w.p2 ∧ Nat.Prime w.q2 ∧
  InBand cfg.pLo cfg.pHi w.p1 ∧
  InBand cfg.qLo cfg.qHi w.q1 ∧
  InBand cfg.pLo cfg.pHi w.p2 ∧
  InBand cfg.qLo cfg.qHi w.q2 ∧
  0 < w.s1 ∧ 0 < w.s2 ∧
  w.s1 ≤ cfg.sMax ∧ w.s2 ≤ cfg.sMax ∧
  ¬ w.p1 ^ 2 ∣ n + 1 ∧
  ¬ w.q1 ^ 2 ∣ n + 1 ∧
  ¬ w.p2 ^ 2 ∣ n + 2 ∧
  ¬ w.q2 ^ 2 ∣ n + 2

theorem bandedAnatomyWitness_of_finite
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hFinite : FiniteBandedAnatomyWitnessK2 cfg n w) :
    BandedAnatomyWitnessK2 cfg n w := by
  rcases hFinite with
    ⟨hxLo, hxHi, hmod2, hSmallOdd, h1, h2,
      hp1, hq1, hp2, hq2, hp1Band, hq1Band, hp2Band, hq2Band,
      hs1Pos, hs2Pos, hs1, hs2, hp1sq, hq1sq, hp2sq, hq2sq⟩
  exact ⟨hxLo, hxHi, hmod2, smallOdd_of_finiteSmallOdd hSmallOdd,
    h1, h2, hp1, hq1, hp2, hq2, hp1Band, hq1Band, hp2Band, hq2Band,
    hs1Pos, hs2Pos, hs1, hs2, hp1sq, hq1sq, hp2sq, hq2sq⟩

def SawtoothWitnessK2 (n : ℕ) (w : PQSWitnessK2) : Prop :=
  n + 1 = w.p1 * w.q1 * w.s1 ∧
  n + 2 = 2 * w.p2 * w.q2 * w.s2 ∧
  SawJ 1 w.p1 (w.q1 * w.s1) ∧
  SawJ 1 w.q1 (w.p1 * w.s1) ∧
  SawJ 2 w.p2 (2 * w.q2 * w.s2) ∧
  SawJ 2 w.q2 (2 * w.p2 * w.s2)

def PatternWitnessK2 (cfg : K2Params) (n : ℕ) (w : PQSWitnessK2) : Prop :=
  BandedAnatomyWitnessK2 cfg n w ∧
  SawtoothWitnessK2 n w ∧
  MediumHygieneK2 cfg n

def CarryAwarePQSK2 (cfg : K2Params) (n : ℕ) (w : PQSWitnessK2) : Prop :=
  PQSEquationOrderedK2 w ∧
  BandedAnatomyWitnessK2 cfg n w ∧
  SawtoothWitnessK2 n w ∧
  MediumHygieneK2 cfg n

def CarryAwareCountedTupleK2 (cfg : K2Params) (t : CountTupleK2) : Prop :=
  cfg.x ≤ t.n ∧ t.n ≤ 2 * cfg.x ∧
  SameLargePrimeBandK2 cfg ∧
  PQSEquationOrderedK2 t.toWitness ∧
  FiniteBandedAnatomyWitnessK2 cfg t.n t.toWitness ∧
  SawtoothWitnessK2 t.n t.toWitness ∧
  FiniteMediumHygieneK2 cfg t.n

instance (cfg : K2Params) : DecidablePred (CarryAwareCountedTupleK2 cfg) := by
  intro t
  unfold CarryAwareCountedTupleK2 SameLargePrimeBandK2
    PQSEquationOrderedK2 PQSLeftK2 PQSRightK2
    FiniteBandedAnatomyWitnessK2 FiniteSmallOddK2
    SawtoothWitnessK2 FiniteMediumHygieneK2 InBand SawJ SawtoothInt
  infer_instance

/-- Exact finite support for the near-square-root bilinear count. -/
def sameBandCarryAwarePQSBoxK2 (cfg : K2Params) : Finset CountTupleK2 :=
  (candidateTupleBoxK2 cfg).filter (CarryAwareCountedTupleK2 cfg)

/-- Exact count of carry-aware same-band `pqs` witnesses in one finite box. -/
def sameBandCarryAwarePQSCountK2 (cfg : K2Params) : ℕ :=
  (sameBandCarryAwarePQSBoxK2 cfg).card

/-- The finite positivity assertion an analytic dispersion estimate should imply. -/
def PositiveSameBandCarryAwarePQSBoxK2 (cfg : K2Params) : Prop :=
  0 < sameBandCarryAwarePQSCountK2 cfg

/--
Exact rational lower-bound form of the bilinear dispersion target.

`num / den` is represented without division: `num * x <= den * count`.
The only positivity needed for nonemptiness is `0 < num`.
-/
def PositiveDensitySameBandCarryAwarePQSBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧
    num * cfg.x ≤ den * sameBandCarryAwarePQSCountK2 cfg

/--
Finite `k = 2` pattern package.

The supply theorem still has to produce infinitely many packages of this form.
Everything below this structure is the finite carry/divisibility verification
from such a package to the Erdos #727 divisibility assertion.
-/
structure PatternK2 (cfg : K2Params) (n : ℕ) where
  hxLo : cfg.x ≤ n
  hxHi : n ≤ 2 * cfg.x
  hmod2 : n % 16 = 12
  hSmallOdd :
    ∀ r : ℕ, Nat.Prime r → r ≤ cfg.P0 → r ≠ 2 → r ∣ n
  p1 : ℕ
  q1 : ℕ
  s1 : ℕ
  p2 : ℕ
  q2 : ℕ
  s2 : ℕ
  h1 : n + 1 = p1 * q1 * s1
  h2 : n + 2 = 2 * p2 * q2 * s2
  hp1 : Nat.Prime p1
  hq1 : Nat.Prime q1
  hp2 : Nat.Prime p2
  hq2 : Nat.Prime q2
  hp1Band : InBand cfg.pLo cfg.pHi p1
  hq1Band : InBand cfg.qLo cfg.qHi q1
  hp2Band : InBand cfg.pLo cfg.pHi p2
  hq2Band : InBand cfg.qLo cfg.qHi q2
  hs1Pos : 0 < s1
  hs2Pos : 0 < s2
  hs1 : s1 ≤ cfg.sMax
  hs2 : s2 ≤ cfg.sMax
  hp1sq : ¬ p1 ^ 2 ∣ n + 1
  hq1sq : ¬ q1 ^ 2 ∣ n + 1
  hp2sq : ¬ p2 ^ 2 ∣ n + 2
  hq2sq : ¬ q2 ^ 2 ∣ n + 2
  saw_p1 : SawJ 1 p1 (q1 * s1)
  saw_q1 : SawJ 1 q1 (p1 * s1)
  saw_p2 : SawJ 2 p2 (2 * q2 * s2)
  saw_q2 : SawJ 2 q2 (2 * p2 * s2)
  medium :
    ∀ r : ℕ, Nat.Prime r →
      cfg.P0 < r → r ≤ cfg.sMax →
        2 * (window n 2).factorization r ≤ (centralBinom n).factorization r

theorem PatternK2_bandedAnatomy
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    BandedAnatomyK2 cfg n := by
  refine ⟨hP.hxLo, hP.hxHi, hP.hmod2, hP.hSmallOdd, ?_⟩
  refine ⟨hP.p1, hP.q1, hP.s1, hP.p2, hP.q2, hP.s2, ?_⟩
  exact ⟨hP.h1, hP.h2, hP.hp1, hP.hq1, hP.hp2, hP.hq2,
    hP.hp1Band, hP.hq1Band, hP.hp2Band, hP.hq2Band,
    hP.hs1Pos, hP.hs2Pos, hP.hs1, hP.hs2,
    hP.hp1sq, hP.hq1sq, hP.hp2sq, hP.hq2sq⟩

theorem PatternK2_sawtooth
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    SawtoothK2 cfg n := by
  refine ⟨hP.p1, hP.q1, hP.s1, hP.p2, hP.q2, hP.s2, ?_⟩
  exact ⟨hP.h1, hP.h2, hP.saw_p1, hP.saw_q1, hP.saw_p2, hP.saw_q2⟩

theorem PatternK2_mediumHygiene
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    MediumHygieneK2 cfg n :=
  hP.medium

theorem PatternK2_bookkeeping
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    BandedAnatomyK2 cfg n ∧ SawtoothK2 cfg n ∧ MediumHygieneK2 cfg n :=
  ⟨PatternK2_bandedAnatomy hP,
    PatternK2_sawtooth hP,
    PatternK2_mediumHygiene hP⟩

theorem PatternWitnessK2_pqsEquation
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    PQSEquationK2 w := by
  rcases hW with ⟨hBand, _hSaw, _hMedium⟩
  rcases hBand with
    ⟨_hxLo, _hxHi, _hmod2, _hSmallOdd, h1, h2,
      _hp1, _hq1, _hp2, _hq2, _hp1Band, _hq1Band, _hp2Band, _hq2Band,
      _hs1Pos, _hs2Pos, _hs1, _hs2, _hp1sq, _hq1sq, _hp2sq, _hq2sq⟩
  unfold PQSEquationK2
  rw [← h1]
  omega

theorem PatternWitnessK2_leftForm
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    n + 1 = PQSLeftK2 w := by
  rcases hW with ⟨hBand, _hSaw, _hMedium⟩
  rcases hBand with
    ⟨_hxLo, _hxHi, _hmod2, _hSmallOdd, h1, _h2,
      _hp1, _hq1, _hp2, _hq2, _hp1Band, _hq1Band, _hp2Band, _hq2Band,
      _hs1Pos, _hs2Pos, _hs1, _hs2, _hp1sq, _hq1sq, _hp2sq, _hq2sq⟩
  simpa [PQSLeftK2, mul_assoc, mul_left_comm, mul_comm] using h1

theorem PatternWitnessK2_rightForm
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    n + 2 = PQSRightK2 w := by
  rcases hW with ⟨hBand, _hSaw, _hMedium⟩
  rcases hBand with
    ⟨_hxLo, _hxHi, _hmod2, _hSmallOdd, _h1, h2,
      _hp1, _hq1, _hp2, _hq2, _hp1Band, _hq1Band, _hp2Band, _hq2Band,
      _hs1Pos, _hs2Pos, _hs1, _hs2, _hp1sq, _hq1sq, _hp2sq, _hq2sq⟩
  simpa [PQSRightK2, mul_assoc, mul_left_comm, mul_comm] using h2

theorem PatternWitnessK2_orderedPqsEquation
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    PQSEquationOrderedK2 w :=
  (pqsEquationK2_iff_ordered).1 (PatternWitnessK2_pqsEquation hW)

theorem PatternWitnessK2_carryAwarePQS
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    CarryAwarePQSK2 cfg n w := by
  exact ⟨PatternWitnessK2_orderedPqsEquation hW, hW.1, hW.2.1, hW.2.2⟩

theorem PatternWitnessK2_of_carryAwarePQS
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hC : CarryAwarePQSK2 cfg n w) :
    PatternWitnessK2 cfg n w := by
  exact ⟨hC.2.1, hC.2.2.1, hC.2.2.2⟩

theorem patternWitnessK2_iff_carryAwarePQS
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2} :
    PatternWitnessK2 cfg n w ↔ CarryAwarePQSK2 cfg n w :=
  ⟨PatternWitnessK2_carryAwarePQS,
    PatternWitnessK2_of_carryAwarePQS⟩

theorem PatternK2_witness
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    ∃ w : PQSWitnessK2, PatternWitnessK2 cfg n w := by
  let w : PQSWitnessK2 :=
    { p1 := hP.p1, q1 := hP.q1, s1 := hP.s1,
      p2 := hP.p2, q2 := hP.q2, s2 := hP.s2 }
  refine ⟨w, ?_⟩
  refine ⟨?_, ?_, hP.medium⟩
  · exact ⟨hP.hxLo, hP.hxHi, hP.hmod2, hP.hSmallOdd,
      hP.h1, hP.h2, hP.hp1, hP.hq1, hP.hp2, hP.hq2,
      hP.hp1Band, hP.hq1Band, hP.hp2Band, hP.hq2Band,
      hP.hs1Pos, hP.hs2Pos, hP.hs1, hP.hs2,
      hP.hp1sq, hP.hq1sq, hP.hp2sq, hP.hq2sq⟩
  · exact ⟨hP.h1, hP.h2, hP.saw_p1, hP.saw_q1, hP.saw_p2, hP.saw_q2⟩

def PatternK2_of_witness
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    PatternK2 cfg n := by
  rcases hW with ⟨hBand, hSaw, hMedium⟩
  rcases hBand with
    ⟨hxLo, hxHi, hmod2, hSmallOdd,
      h1, h2, hp1, hq1, hp2, hq2,
      hp1Band, hq1Band, hp2Band, hq2Band,
      hs1Pos, hs2Pos, hs1, hs2,
      hp1sq, hq1sq, hp2sq, hq2sq⟩
  rcases hSaw with ⟨_, _, saw_p1, saw_q1, saw_p2, saw_q2⟩
  exact
    { hxLo := hxLo
      hxHi := hxHi
      hmod2 := hmod2
      hSmallOdd := hSmallOdd
      p1 := w.p1
      q1 := w.q1
      s1 := w.s1
      p2 := w.p2
      q2 := w.q2
      s2 := w.s2
      h1 := h1
      h2 := h2
      hp1 := hp1
      hq1 := hq1
      hp2 := hp2
      hq2 := hq2
      hp1Band := hp1Band
      hq1Band := hq1Band
      hp2Band := hp2Band
      hq2Band := hq2Band
      hs1Pos := hs1Pos
      hs2Pos := hs2Pos
      hs1 := hs1
      hs2 := hs2
      hp1sq := hp1sq
      hq1sq := hq1sq
      hp2sq := hp2sq
      hq2sq := hq2sq
      saw_p1 := saw_p1
      saw_q1 := saw_q1
      saw_p2 := saw_p2
      saw_q2 := saw_q2
      medium := hMedium }

theorem PatternK2_pqsEquation
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    PQSEquationK2
      { p1 := hP.p1, q1 := hP.q1, s1 := hP.s1,
        p2 := hP.p2, q2 := hP.q2, s2 := hP.s2 } := by
  unfold PQSEquationK2
  rw [← hP.h1]
  have h2 := hP.h2
  omega

theorem PatternK2_orderedPqsEquation
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    PQSEquationOrderedK2
      { p1 := hP.p1, q1 := hP.q1, s1 := hP.s1,
        p2 := hP.p2, q2 := hP.q2, s2 := hP.s2 } :=
  (pqsEquationK2_iff_ordered).1 (PatternK2_pqsEquation hP)

theorem PatternK2_p1_primeBudget
    {cfg : K2Params} {n B : ℕ} (hP : PatternK2 cfg n)
    (hlog : Nat.log hP.p1 (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization hP.p1 ≤ (centralBinom n).factorization hP.p1 := by
  have hlarge : 4 < hP.p1 := by
    have hpLo : cfg.pLo < hP.p1 := hP.hp1Band.1
    exact lt_trans cfg.four_lt_pLo hpLo
  have hfac : n + 1 = hP.p1 * (hP.q1 * hP.s1) := by
    rw [hP.h1]
    ring
  exact window_two_left_prime_budget_of_sawtooth hP.hp1 hlarge hfac hP.hp1sq hP.saw_p1 hlog hB

theorem PatternK2_q1_primeBudget
    {cfg : K2Params} {n B : ℕ} (hP : PatternK2 cfg n)
    (hlog : Nat.log hP.q1 (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization hP.q1 ≤ (centralBinom n).factorization hP.q1 := by
  have hlarge : 4 < hP.q1 := by
    exact lt_trans cfg.four_lt_qLo hP.hq1Band.1
  have hfac : n + 1 = hP.q1 * (hP.p1 * hP.s1) := by
    rw [hP.h1]
    ring
  exact window_two_left_prime_budget_of_sawtooth hP.hq1 hlarge hfac hP.hq1sq hP.saw_q1 hlog hB

theorem PatternK2_p2_primeBudget
    {cfg : K2Params} {n B : ℕ} (hP : PatternK2 cfg n)
    (hlog : Nat.log hP.p2 (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization hP.p2 ≤ (centralBinom n).factorization hP.p2 := by
  have hlarge : 4 < hP.p2 := by
    have hpLo : cfg.pLo < hP.p2 := hP.hp2Band.1
    exact lt_trans cfg.four_lt_pLo hpLo
  have hfac : n + 2 = hP.p2 * (2 * hP.q2 * hP.s2) := by
    rw [hP.h2]
    ring
  exact window_two_right_prime_budget_of_sawtooth hP.hp2 hlarge hfac hP.hp2sq hP.saw_p2 hlog hB

theorem PatternK2_q2_primeBudget
    {cfg : K2Params} {n B : ℕ} (hP : PatternK2 cfg n)
    (hlog : Nat.log hP.q2 (2 * n) < B) (hB : 2 < B) :
    2 * (window n 2).factorization hP.q2 ≤ (centralBinom n).factorization hP.q2 := by
  have hlarge : 4 < hP.q2 := by
    exact lt_trans cfg.four_lt_qLo hP.hq2Band.1
  have hfac : n + 2 = hP.q2 * (2 * hP.p2 * hP.s2) := by
    rw [hP.h2]
    ring
  exact window_two_right_prime_budget_of_sawtooth hP.hq2 hlarge hfac hP.hq2sq hP.saw_q2 hlog hB

theorem PatternK2_smallOdd_primeBudget
    {cfg : K2Params} {n r : ℕ} (hP : PatternK2 cfg n)
    (hr : Nat.Prime r) (hr_le : r ≤ cfg.P0) (hr2 : r ≠ 2) :
    2 * (window n 2).factorization r ≤ (centralBinom n).factorization r :=
  window_two_small_odd_prime_budget hr hr2 (hP.hSmallOdd r hr hr_le hr2)

theorem PatternK2_two_primeBudget
    {cfg : K2Params} {n B : ℕ} (hP : PatternK2 cfg n)
    (hlog : Nat.log 2 (2 * n) < B) (hB : 4 < B) :
    2 * (window n 2).factorization 2 ≤ (centralBinom n).factorization 2 :=
  window_two_two_prime_budget_of_mod16_eq_12 hP.hmod2 hlog hB

theorem PatternK2_medium_primeBudget
    {cfg : K2Params} {n r : ℕ} (hP : PatternK2 cfg n)
    (hr : Nat.Prime r) (hP0 : cfg.P0 < r) (hrs : r ≤ cfg.sMax) :
    2 * (window n 2).factorization r ≤ (centralBinom n).factorization r :=
  hP.medium r hr hP0 hrs

theorem PatternK2_large_primeBudget
    {cfg : K2Params} {n r : ℕ} (hP : PatternK2 cfg n)
    (hr : Nat.Prime r) (hsMax_lt : cfg.sMax < r) :
    2 * (window n 2).factorization r ≤ (centralBinom n).factorization r := by
  by_cases hdiv_window : r ∣ window n 2
  · have hdiv_prod : r ∣ (n + 1) * (n + 2) := by
      simpa [window_two] using hdiv_window
    rcases (hr.dvd_mul).1 hdiv_prod with hleft | hright
    · have hleft_prod : r ∣ hP.p1 * hP.q1 * hP.s1 := by
        simpa [hP.h1] using hleft
      rcases (hr.dvd_mul).1 hleft_prod with hpq | hs
      · rcases (hr.dvd_mul).1 hpq with hp1 | hq1
        · have hp1eq : hP.p1 = r :=
            (Nat.Prime.dvd_iff_eq hP.hp1 hr.ne_one).1 hp1
          rw [← hp1eq]
          exact PatternK2_p1_primeBudget hP
            (B := Nat.log hP.p1 (2 * n) + 3) (by omega) (by omega)
        · have hq1eq : hP.q1 = r :=
            (Nat.Prime.dvd_iff_eq hP.hq1 hr.ne_one).1 hq1
          rw [← hq1eq]
          exact PatternK2_q1_primeBudget hP
            (B := Nat.log hP.q1 (2 * n) + 3) (by omega) (by omega)
      · have hr_le_s1 : r ≤ hP.s1 := Nat.le_of_dvd hP.hs1Pos hs
        have hs1_le : hP.s1 ≤ cfg.sMax := hP.hs1
        exfalso
        omega
    · have hright_prod : r ∣ 2 * hP.p2 * hP.q2 * hP.s2 := by
        simpa [hP.h2] using hright
      rcases (hr.dvd_mul).1 hright_prod with hpq | hs
      · rcases (hr.dvd_mul).1 hpq with h2p | hq2
        · rcases (hr.dvd_mul).1 h2p with htwo | hp2
          · have hr_le_two : r ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
            have hP0_ge : 3 ≤ cfg.P0 := cfg.P0_ge_3
            have hP0_lt : cfg.P0 < cfg.sMax := cfg.P0_lt_sMax
            exfalso
            omega
          · have hp2eq : hP.p2 = r :=
              (Nat.Prime.dvd_iff_eq hP.hp2 hr.ne_one).1 hp2
            rw [← hp2eq]
            exact PatternK2_p2_primeBudget hP
              (B := Nat.log hP.p2 (2 * n) + 3) (by omega) (by omega)
        · have hq2eq : hP.q2 = r :=
            (Nat.Prime.dvd_iff_eq hP.hq2 hr.ne_one).1 hq2
          rw [← hq2eq]
          exact PatternK2_q2_primeBudget hP
            (B := Nat.log hP.q2 (2 * n) + 3) (by omega) (by omega)
      · have hr_le_s2 : r ≤ hP.s2 := Nat.le_of_dvd hP.hs2Pos hs
        have hs2_le : hP.s2 ≤ cfg.sMax := hP.hs2
        exfalso
        omega
  · have hzero : (window n 2).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdiv_window
    simp [hzero]

theorem PatternK2_primeBudget
    {cfg : K2Params} {n r : ℕ} (hP : PatternK2 cfg n)
    (hr : Nat.Prime r) :
    2 * (window n 2).factorization r ≤ (centralBinom n).factorization r := by
  by_cases hr2 : r = 2
  · subst r
    exact PatternK2_two_primeBudget hP
      (B := Nat.log 2 (2 * n) + 5) (by omega) (by omega)
  · by_cases hrP0 : r ≤ cfg.P0
    · exact PatternK2_smallOdd_primeBudget hP hr hrP0 hr2
    · by_cases hrsMax : r ≤ cfg.sMax
      · exact PatternK2_medium_primeBudget hP hr (by omega) hrsMax
      · exact PatternK2_large_primeBudget hP hr (by omega)

theorem PatternK2_implies_window_sq_dvd
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    (window n 2) ^ 2 ∣ centralBinom n :=
  window_sq_dvd_centralBinom_of_prime_budget
    (fun p hp => PatternK2_primeBudget (r := p) hP hp)

theorem PatternK2_implies_erdosAt2
    {cfg : K2Params} {n : ℕ}
    (hP : PatternK2 cfg n) :
    erdosAt 2 n := by
  have hn : 2 ≤ n := le_trans cfg.x_ge_2 hP.hxLo
  exact (erdosAt2_iff_window_two_sq_dvd_centralBinom hn).2
    (PatternK2_implies_window_sq_dvd hP)

theorem PatternWitnessK2_implies_erdosAt2
    {cfg : K2Params} {n : ℕ} {w : PQSWitnessK2}
    (hW : PatternWitnessK2 cfg n w) :
    erdosAt 2 n :=
  PatternK2_implies_erdosAt2 (PatternK2_of_witness hW)

/-- The still-open infinite supply theorem for the finite `k = 2` pattern. -/
def InfinitelyManyPatternK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ,
    N ≤ n ∧ Nonempty (PatternK2 cfg n)

/-- Shared-witness form of the still-open positive-density `pqs` supply theorem. -/
def InfinitelyManyPatternWitnessK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ, ∃ w : PQSWitnessK2,
    N ≤ n ∧ PatternWitnessK2 cfg n w

/-- Exact carry-aware `pqs` supply theorem left open by this finite architecture. -/
def InfinitelyManyCarryAwarePQSK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ, ∃ w : PQSWitnessK2,
    N ≤ n ∧ CarryAwarePQSK2 cfg n w

/--
Near-square-root same-band version of the open carry-aware `pqs` supply.

This captures the balanced-edge analytic target without declaring any supply
assumption: both large primes are drawn from the same finite band, and the
theorem still has to produce infinitely many such carry-aware witnesses.
-/
def InfinitelyManySameBandCarryAwarePQSK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ, ∃ w : PQSWitnessK2,
    N ≤ n ∧ SameLargePrimeBandK2 cfg ∧ CarryAwarePQSK2 cfg n w

/--
Box-counting version of the open same-band supply target.

This is the Lean-facing form of the remaining bilinear dispersion theorem: it
asks for arbitrarily large finite boxes with at least one counted witness.
-/
def InfinitelyManyPositiveSameBandCarryAwarePQSBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveSameBandCarryAwarePQSBoxK2 cfg

/--
Positive-density version of the open same-band supply target.

This is closer to the intended analytic theorem: a fixed exact rational lower
bound for the counted witnesses in arbitrarily large boxes.
-/
def InfinitelyManyPositiveDensitySameBandCarryAwarePQSBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveDensitySameBandCarryAwarePQSBoxK2 num den cfg

/--
Shifted-divisor formulation of the remaining analytic supply theorem.

The finite weights above expose the restricted `pqs` shifted-convolution shape.
This Prop is intentionally only a conditional supply target.
-/
def CarryAwareShiftedDivisorSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensitySameBandCarryAwarePQSBoxesK2 num den

/--
One switched small-cofactor witness.

This packages the corrected relation as
`n + 1 = s1 * M1` and `n + 2 = 2 * s2 * M2`, then asks the finite marked
semiprime weights to expose carry-aware factorizations of `M1` and `M2`.
-/
def SwitchedSupplyWitnessK2
    (cfg : K2Params) (n s1 s2 M1 M2 : ℕ) : Prop :=
  cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧
  n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg n ∧
  FiniteMediumHygieneK2 cfg n ∧
  0 < s1 ∧ 0 < s2 ∧
  s1 ≤ cfg.sMax ∧ s2 ≤ cfg.sMax ∧
  n + 1 = s1 * M1 ∧
  n + 2 = 2 * s2 * M2 ∧
  0 < MarkedSemiprimeWeightK2 cfg s1 M1 ∧
  0 < MarkedSemiprimeWeightRightK2 cfg s2 M2

/--
Switched semiprime formulation of the remaining open supply theorem.

This is intentionally conditional: no proof of this proposition is provided.
-/
def SwitchedSemiprimeSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ,
  ∃ s1 : ℕ, ∃ s2 : ℕ, ∃ M1 : ℕ, ∃ M2 : ℕ,
    N ≤ n ∧ SwitchedSupplyWitnessK2 cfg n s1 s2 M1 M2

theorem SwitchedSupplyWitnessK2_equation
    {cfg : K2Params} {n s1 s2 M1 M2 : ℕ}
    (hW : SwitchedSupplyWitnessK2 cfg n s1 s2 M1 M2) :
    s1 * M1 + 1 = 2 * s2 * M2 := by
  rcases hW with
    ⟨_hxLo, _hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      _hs1Pos, _hs2Pos, _hs1Le, _hs2Le, hn1, hn2, _hLeftPos, _hRightPos⟩
  rw [← hn1, ← hn2]

theorem SwitchedSupplyWitnessK2_smallMod
    {cfg : K2Params} {n s1 s2 M1 M2 : ℕ}
    (hW : SwitchedSupplyWitnessK2 cfg n s1 s2 M1 M2) :
    (2 * s2 * M2) % s1 = 1 % s1 := by
  have heq := SwitchedSupplyWitnessK2_equation hW
  calc
    (2 * s2 * M2) % s1 = (s1 * M1 + 1) % s1 := by rw [← heq]
    _ = ((s1 * M1) % s1 + 1 % s1) % s1 := by
      rw [Nat.add_mod]
    _ = (0 + 1 % s1) % s1 := by
      rw [Nat.mul_mod_right]
    _ = 1 % s1 := by
      simp

/--
Variable-`s` boxed version of the switched witness.

The coprimality and congruence shape are analytic bookkeeping; the finite
carry implication only needs the stronger S-boxed weights to imply the marked
semiprime weights used by `SwitchedSupplyWitnessK2`.
-/
def SwitchedSBoxedSupplyWitnessK2
    (cfg : K2Params) (n s1 s2 M1 M2 : ℕ) : Prop :=
  cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧
  n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg n ∧
  FiniteMediumHygieneK2 cfg n ∧
  0 < s1 ∧ 0 < s2 ∧
  s1 ≤ cfg.sMax ∧ s2 ≤ cfg.sMax ∧
  Nat.Coprime s1 (2 * s2) ∧
  n + 1 = s1 * M1 ∧
  n + 2 = 2 * s2 * M2 ∧
  0 < SBoxedSemiprimeWeightK2 cfg s1 M1 ∧
  0 < SBoxedSemiprimeWeightRightK2 cfg s2 M2

/--
Open variable-`s` boxed supply theorem.

This is the current sharp conditional target, not an asserted analytic result.
-/
def SwitchedSBoxedSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ n : ℕ,
  ∃ s1 : ℕ, ∃ s2 : ℕ, ∃ M1 : ℕ, ∃ M2 : ℕ,
    N ≤ n ∧ SwitchedSBoxedSupplyWitnessK2 cfg n s1 s2 M1 M2

theorem switchedSupplyWitness_of_switchedSBoxedSupplyWitness
    {cfg : K2Params} {n s1 s2 M1 M2 : ℕ}
    (hW : SwitchedSBoxedSupplyWitnessK2 cfg n s1 s2 M1 M2) :
    SwitchedSupplyWitnessK2 cfg n s1 s2 M1 M2 := by
  rcases hW with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hs1Pos, hs2Pos, hs1Le, hs2Le, _hcoprime, hn1, hn2,
      hLeftPos, hRightPos⟩
  have hLeftMarked : 0 < MarkedSemiprimeWeightK2 cfg s1 M1 := by
    unfold MarkedSemiprimeWeightK2
    exact markedSemiprimeWeightWith_pos_of_sBoxed
      (by simpa [SBoxedSemiprimeWeightK2] using hLeftPos)
  have hRightMarked : 0 < MarkedSemiprimeWeightRightK2 cfg s2 M2 := by
    unfold MarkedSemiprimeWeightRightK2
    exact markedSemiprimeWeightWith_pos_of_sBoxed
      (by simpa [SBoxedSemiprimeWeightRightK2] using hRightPos)
  exact ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
    hs1Pos, hs2Pos, hs1Le, hs2Le, hn1, hn2, hLeftMarked, hRightMarked⟩

theorem switchedSupply_of_switchedSBoxedSupply
    (hSupply : SwitchedSBoxedSupplyK2) :
    SwitchedSemiprimeSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, s1, s2, M1, M2, hnN, hW⟩
  exact ⟨cfg, n, s1, s2, M1, M2, hnN,
    switchedSupplyWitness_of_switchedSBoxedSupplyWitness hW⟩

/--
Finite tuple support for the switched affine-correlation target.

The two semiprime values are stored explicitly.  This avoids any partial
division in the finite checker while still recording the affine equation and
small-modulus congruence in the predicate below.
-/
structure SBoxedAffineCorrelationTupleK2 where
  n : ℕ
  s1 : ℕ
  s2 : ℕ
  M1 : ℕ
  M2 : ℕ
  deriving DecidableEq

def sBoxedAffineCorrelationTupleBoxK2
    (cfg : K2Params) : Finset SBoxedAffineCorrelationTupleK2 :=
  let MHi := 2 * cfg.x + 2
  let S0 := (Finset.Icc cfg.x (2 * cfg.x)).product (Finset.Icc 0 cfg.sMax)
  let S1 := S0.product (Finset.Icc 0 cfg.sMax)
  let S2 := S1.product (Finset.Icc 0 MHi)
  let S3 := S2.product (Finset.Icc 0 MHi)
  S3.image
    (fun t =>
      match t with
      | ((((n, s1), s2), M1), M2) =>
          { n := n, s1 := s1, s2 := s2, M1 := M1, M2 := M2 })

def SBoxedAffineCorrelationK2
    (cfg : K2Params) (t : SBoxedAffineCorrelationTupleK2) : Prop :=
  SwitchedSBoxedSupplyWitnessK2 cfg t.n t.s1 t.s2 t.M1 t.M2 ∧
  t.s1 * t.M1 + 1 = 2 * t.s2 * t.M2 ∧
  (2 * t.s2 * t.M2) % t.s1 = 1 % t.s1

instance (cfg : K2Params) :
    DecidablePred (SBoxedAffineCorrelationK2 cfg) := by
  intro t
  unfold SBoxedAffineCorrelationK2 SwitchedSBoxedSupplyWitnessK2
    SameLargePrimeBandK2 FiniteSmallOddK2 FiniteMediumHygieneK2
  infer_instance

def sBoxedAffineCorrelationBoxK2
    (cfg : K2Params) : Finset SBoxedAffineCorrelationTupleK2 :=
  (sBoxedAffineCorrelationTupleBoxK2 cfg).filter
    (SBoxedAffineCorrelationK2 cfg)

def sBoxedAffineCorrelationCountK2 (cfg : K2Params) : ℕ :=
  (sBoxedAffineCorrelationBoxK2 cfg).card

def SBoxedAffineCorrelationWeightK2
    (cfg : K2Params) (t : SBoxedAffineCorrelationTupleK2) : ℕ :=
  SBoxedSemiprimeWeightK2 cfg t.s1 t.M1 *
    SBoxedSemiprimeWeightRightK2 cfg t.s2 t.M2

def sBoxedAffineCorrelationWeightedSumK2 (cfg : K2Params) : ℕ :=
  (sBoxedAffineCorrelationBoxK2 cfg).sum
    (fun t => SBoxedAffineCorrelationWeightK2 cfg t)

/--
Fixed-`s1,s2` slice of the switched affine-correlation box.

This is the finite Lean target corresponding to a fixed-box marked pair theorem
for one prescribed small-cofactor pair.
-/
def fixedSBoxedAffineCorrelationBoxK2
    (cfg : K2Params) (s1 s2 : ℕ) :
    Finset SBoxedAffineCorrelationTupleK2 :=
  (sBoxedAffineCorrelationBoxK2 cfg).filter
    (fun t => t.s1 = s1 ∧ t.s2 = s2)

def fixedSBoxedAffineCorrelationCountK2
    (cfg : K2Params) (s1 s2 : ℕ) : ℕ :=
  (fixedSBoxedAffineCorrelationBoxK2 cfg s1 s2).card

def fixedSBoxedAffineCorrelationWeightedSumK2
    (cfg : K2Params) (s1 s2 : ℕ) : ℕ :=
  (fixedSBoxedAffineCorrelationBoxK2 cfg s1 s2).sum
    (fun t => SBoxedAffineCorrelationWeightK2 cfg t)

/-- Finite nonemptiness form of the switched affine-correlation target. -/
def PositiveSBoxedAffineCorrelationBoxK2 (cfg : K2Params) : Prop :=
  0 < sBoxedAffineCorrelationCountK2 cfg

def PositiveWeightedSBoxedAffineCorrelationBoxK2 (cfg : K2Params) : Prop :=
  0 < sBoxedAffineCorrelationWeightedSumK2 cfg

def PositiveFixedSBoxedAffineCorrelationBoxK2
    (cfg : K2Params) (s1 s2 : ℕ) : Prop :=
  0 < fixedSBoxedAffineCorrelationCountK2 cfg s1 s2

def PositiveWeightedFixedSBoxedAffineCorrelationBoxK2
    (cfg : K2Params) (s1 s2 : ℕ) : Prop :=
  0 < fixedSBoxedAffineCorrelationWeightedSumK2 cfg s1 s2

/--
Exact rational lower-bound form of the switched affine-correlation target.

This is the finite Lean shadow of a `≫ x` analytic estimate, written without
division or real constants as `num * x <= den * count`.
-/
def PositiveDensitySBoxedAffineCorrelationBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧
    num * cfg.x ≤ den * sBoxedAffineCorrelationCountK2 cfg

/--
Exact weighted lower-bound form of the switched affine-correlation target.

This is the finite aggregate product-sum version of the analytic target.  It
does not assert a pointwise fixed-`(s1,s2)` correlation theorem; it remains a
conditional supply interface rather than an established estimate.
-/
def PositiveDensityWeightedSBoxedAffineCorrelationBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧
    num * cfg.x ≤ den * sBoxedAffineCorrelationWeightedSumK2 cfg

/--
Exact lower-bound form for one fixed small-cofactor pair.

This is the formal target for a fixed-box marked pair theorem; no such
analytic theorem is asserted here.
-/
def PositiveDensityFixedSBoxedAffineCorrelationBoxK2
    (num den : ℕ) (cfg : K2Params) (s1 s2 : ℕ) : Prop :=
  0 < num ∧
    num * cfg.x ≤ den * fixedSBoxedAffineCorrelationCountK2 cfg s1 s2

def PositiveDensityWeightedFixedSBoxedAffineCorrelationBoxK2
    (num den : ℕ) (cfg : K2Params) (s1 s2 : ℕ) : Prop :=
  0 < num ∧
    num * cfg.x ≤
      den * fixedSBoxedAffineCorrelationWeightedSumK2 cfg s1 s2

def InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveSBoxedAffineCorrelationBoxK2 cfg

def InfinitelyManyPositiveWeightedSBoxedAffineCorrelationBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveWeightedSBoxedAffineCorrelationBoxK2 cfg

def InfinitelyManyPositiveFixedSBoxedAffineCorrelationBoxesK2
    (s1 s2 : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2

def InfinitelyManyPositiveWeightedFixedSBoxedAffineCorrelationBoxesK2
    (s1 s2 : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveWeightedFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2

def InfinitelyManyPositiveDensitySBoxedAffineCorrelationBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveDensitySBoxedAffineCorrelationBoxK2 num den cfg

def InfinitelyManyPositiveDensityWeightedSBoxedAffineCorrelationBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityWeightedSBoxedAffineCorrelationBoxK2 num den cfg

def InfinitelyManyPositiveDensityFixedSBoxedAffineCorrelationBoxesK2
    (num den : ℕ) (s1 s2 : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityFixedSBoxedAffineCorrelationBoxK2 num den cfg s1 s2

def InfinitelyManyPositiveDensityWeightedFixedSBoxedAffineCorrelationBoxesK2
    (num den : ℕ) (s1 s2 : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityWeightedFixedSBoxedAffineCorrelationBoxK2
        num den cfg s1 s2

/--
Existential form of the sharp remaining analytic supply theorem.

Proving this proposition unconditionally would close the current `k = 2`
route; this file only proves its finite consequence.
-/
def SBoxedAffineCorrelationSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensitySBoxedAffineCorrelationBoxesK2 num den

/--
Weighted product-sum form of the sharp remaining analytic supply theorem.

This is the current finite Lean interface for an aggregate/average-over-`s`
correlation estimate for variable-`s` boxed, sawtooth-marked semiprime weights.
No theorem in this file proves this supply unconditionally.
-/
def WeightedSBoxedAffineCorrelationSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityWeightedSBoxedAffineCorrelationBoxesK2 num den

/--
Positive aggregate-over-`s` supply.

This is weaker than the density-weighted supply: it asks only that the finite
weighted aggregate over all admitted small cofactors be positive arbitrarily far
out.  It matches the "average-over-s supply" analytic downgrade without
claiming such an estimate is known.
-/
def AverageOverSBoxedAffineCorrelationSupplyK2 : Prop :=
  InfinitelyManyPositiveWeightedSBoxedAffineCorrelationBoxesK2

/-- Fixed small-cofactor version of the marked affine-correlation supply. -/
def FixedSBoxedAffineCorrelationSupplyK2 (s1 s2 : ℕ) : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityFixedSBoxedAffineCorrelationBoxesK2
      num den s1 s2

/-- Weighted fixed small-cofactor version of the marked supply. -/
def FixedWeightedSBoxedAffineCorrelationSupplyK2 (s1 s2 : ℕ) : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityWeightedFixedSBoxedAffineCorrelationBoxesK2
      num den s1 s2

/-- Convenience name for the fixed `s1 = s2 = 1` marked pair target. -/
def FixedOneOneWeightedSBoxedAffineCorrelationSupplyK2 : Prop :=
  FixedWeightedSBoxedAffineCorrelationSupplyK2 1 1

/--
Explicit prime-quadruple support for the fixed `s1 = s2 = 1` marked pair
target.  The semiprime values are `left.p * left.q` and `right.p * right.q`.
-/
structure FixedOneOnePrimeQuadrupleK2 where
  n : ℕ
  left : SemiprimePairK2
  right : SemiprimePairK2
  deriving DecidableEq

def fixedOneOnePrimeQuadrupleTupleBoxK2
    (cfg : K2Params) : Finset FixedOneOnePrimeQuadrupleK2 :=
  let S0 := (Finset.Icc cfg.x (2 * cfg.x)).product (semiprimePairBoxK2 cfg)
  let S1 := S0.product (semiprimePairBoxK2 cfg)
  S1.image
    (fun t =>
      match t with
      | ((n, left), right) => { n := n, left := left, right := right })

/--
Finite predicate for the fixed `s1 = s2 = 1` prime-quadruple theorem.

This is the direct Lean shadow of
`p1*q1 + 1 = 2*p2*q2`, with all finite Kummer, band, and sawtooth marks
visible.
-/
def FixedOneOnePrimeQuadrupleGoodK2
    (cfg : K2Params) (u : FixedOneOnePrimeQuadrupleK2) : Prop :=
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  u.n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  u.n + 1 = u.left.p * u.left.q ∧
  u.n + 2 = 2 * (u.right.p * u.right.q) ∧
  SBoxedSemiprimePairK2 cfg 1 (u.left.p * u.left.q) 1 1 u.left ∧
  SBoxedSemiprimePairK2 cfg 1 (u.right.p * u.right.q) 2 2 u.right

instance (cfg : K2Params) :
    DecidablePred (FixedOneOnePrimeQuadrupleGoodK2 cfg) := by
  intro u
  unfold FixedOneOnePrimeQuadrupleGoodK2 SBoxedSemiprimePairK2
    MarkedSemiprimePairK2 SameLargePrimeBandK2 FiniteSmallOddK2
    FiniteMediumHygieneK2 InBand SawJ SawtoothInt
  infer_instance

def fixedOneOnePrimeQuadrupleBoxK2
    (cfg : K2Params) : Finset FixedOneOnePrimeQuadrupleK2 :=
  (fixedOneOnePrimeQuadrupleTupleBoxK2 cfg).filter
    (FixedOneOnePrimeQuadrupleGoodK2 cfg)

def fixedOneOnePrimeQuadrupleCountK2 (cfg : K2Params) : ℕ :=
  (fixedOneOnePrimeQuadrupleBoxK2 cfg).card

def PositiveFixedOneOnePrimeQuadrupleBoxK2 (cfg : K2Params) : Prop :=
  0 < fixedOneOnePrimeQuadrupleCountK2 cfg

def PositiveDensityFixedOneOnePrimeQuadrupleBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧ num * cfg.x ≤ den * fixedOneOnePrimeQuadrupleCountK2 cfg

def InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveFixedOneOnePrimeQuadrupleBoxK2 cfg

def InfinitelyManyPositiveDensityFixedOneOnePrimeQuadrupleBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveDensityFixedOneOnePrimeQuadrupleBoxK2 num den cfg

/--
Fixed `s1 = s2 = 1` prime-quadruple supply theorem.

This is not proved here.  It is a precise conditional analytic target whose
finite consequence is proved below.
-/
def FixedOneOnePrimeQuadrupleSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityFixedOneOnePrimeQuadrupleBoxesK2 num den

/--
Ratio-box version of the fixed `s1 = s2 = 1` prime-quadruple target.

The inequalities are the exact integer form of
`3/2 < q1/p1 < 2` and `5/4 < q2/p2 < 4/3`.  They make the four sawtooth
marks automatic by the lemmas above.  The no-square clauses are still explicit
finite hygiene, not an analytic input.
-/
def FixedOneOneRatioPrimeQuadrupleGoodK2
    (cfg : K2Params) (u : FixedOneOnePrimeQuadrupleK2) : Prop :=
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  u.n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  u.n + 1 = u.left.p * u.left.q ∧
  u.n + 2 = 2 * (u.right.p * u.right.q) ∧
  Nat.Prime u.left.p ∧ Nat.Prime u.left.q ∧
  Nat.Prime u.right.p ∧ Nat.Prime u.right.q ∧
  InBand cfg.pLo cfg.pHi u.left.p ∧
  InBand cfg.qLo cfg.qHi u.left.q ∧
  InBand cfg.pLo cfg.pHi u.right.p ∧
  InBand cfg.qLo cfg.qHi u.right.q ∧
  ¬ u.left.p ^ 2 ∣ u.left.p * u.left.q ∧
  ¬ u.left.q ^ 2 ∣ u.left.p * u.left.q ∧
  ¬ u.right.p ^ 2 ∣ 2 * (u.right.p * u.right.q) ∧
  ¬ u.right.q ^ 2 ∣ 2 * (u.right.p * u.right.q) ∧
  u.left.p < u.left.q ∧
  3 * u.left.p < 2 * u.left.q ∧
  u.left.q < 2 * u.left.p ∧
  u.right.p < u.right.q ∧
  5 * u.right.p < 4 * u.right.q ∧
  3 * u.right.q < 4 * u.right.p

instance (cfg : K2Params) :
    DecidablePred (FixedOneOneRatioPrimeQuadrupleGoodK2 cfg) := by
  intro u
  unfold FixedOneOneRatioPrimeQuadrupleGoodK2 SameLargePrimeBandK2
    FiniteSmallOddK2 FiniteMediumHygieneK2 InBand
  infer_instance

def fixedOneOneRatioPrimeQuadrupleBoxK2
    (cfg : K2Params) : Finset FixedOneOnePrimeQuadrupleK2 :=
  (fixedOneOnePrimeQuadrupleTupleBoxK2 cfg).filter
    (FixedOneOneRatioPrimeQuadrupleGoodK2 cfg)

def fixedOneOneRatioPrimeQuadrupleCountK2 (cfg : K2Params) : ℕ :=
  (fixedOneOneRatioPrimeQuadrupleBoxK2 cfg).card

def PositiveFixedOneOneRatioPrimeQuadrupleBoxK2 (cfg : K2Params) : Prop :=
  0 < fixedOneOneRatioPrimeQuadrupleCountK2 cfg

def PositiveDensityFixedOneOneRatioPrimeQuadrupleBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧ num * cfg.x ≤ den * fixedOneOneRatioPrimeQuadrupleCountK2 cfg

def InfinitelyManyPositiveFixedOneOneRatioPrimeQuadrupleBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveFixedOneOneRatioPrimeQuadrupleBoxK2 cfg

def InfinitelyManyPositiveDensityFixedOneOneRatioPrimeQuadrupleBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityFixedOneOneRatioPrimeQuadrupleBoxK2 num den cfg

/--
Fixed-box ratio supply theorem suggested by the analytic obstruction analysis.

This is still not proved here.  It is a sharper conditional theorem: a
positive-density supply of the displayed fixed ratio boxes would imply the
already marked fixed prime-quadruple supply.
-/
def FixedOneOneRatioPrimeQuadrupleSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityFixedOneOneRatioPrimeQuadrupleBoxesK2 num den

/--
Clean fixed-ratio target with squarefreeness removed from the analytic
hypotheses.  For fixed `s1 = s2 = 1`, the no-square facts are consequences of
the prime/order/band hypotheses and are proved below.
-/
def FixedOneOneCleanRatioPrimeQuadrupleGoodK2
    (cfg : K2Params) (u : FixedOneOnePrimeQuadrupleK2) : Prop :=
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  u.n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  u.n + 1 = u.left.p * u.left.q ∧
  u.n + 2 = 2 * (u.right.p * u.right.q) ∧
  Nat.Prime u.left.p ∧ Nat.Prime u.left.q ∧
  Nat.Prime u.right.p ∧ Nat.Prime u.right.q ∧
  InBand cfg.pLo cfg.pHi u.left.p ∧
  InBand cfg.qLo cfg.qHi u.left.q ∧
  InBand cfg.pLo cfg.pHi u.right.p ∧
  InBand cfg.qLo cfg.qHi u.right.q ∧
  u.left.p < u.left.q ∧
  3 * u.left.p < 2 * u.left.q ∧
  u.left.q < 2 * u.left.p ∧
  u.right.p < u.right.q ∧
  5 * u.right.p < 4 * u.right.q ∧
  3 * u.right.q < 4 * u.right.p

instance (cfg : K2Params) :
    DecidablePred (FixedOneOneCleanRatioPrimeQuadrupleGoodK2 cfg) := by
  intro u
  unfold FixedOneOneCleanRatioPrimeQuadrupleGoodK2 SameLargePrimeBandK2
    FiniteSmallOddK2 FiniteMediumHygieneK2 InBand
  infer_instance

def fixedOneOneCleanRatioPrimeQuadrupleBoxK2
    (cfg : K2Params) : Finset FixedOneOnePrimeQuadrupleK2 :=
  (fixedOneOnePrimeQuadrupleTupleBoxK2 cfg).filter
    (FixedOneOneCleanRatioPrimeQuadrupleGoodK2 cfg)

def fixedOneOneCleanRatioPrimeQuadrupleCountK2 (cfg : K2Params) : ℕ :=
  (fixedOneOneCleanRatioPrimeQuadrupleBoxK2 cfg).card

def PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2
    (cfg : K2Params) : Prop :=
  0 < fixedOneOneCleanRatioPrimeQuadrupleCountK2 cfg

def PositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧ num * cfg.x ≤
    den * fixedOneOneCleanRatioPrimeQuadrupleCountK2 cfg

def InfinitelyManyPositiveFixedOneOneCleanRatioPrimeQuadrupleBoxesK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2 cfg

def InfinitelyManyPositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxK2 num den cfg

/--
Clean fixed-box ratio supply theorem.

This is the current sharpest Lean-facing analytic target for the `s1=s2=1`
route.  It still asserts a fixed prescribed semiprime correlation and is not
proved in this file.
-/
def FixedOneOneCleanRatioPrimeQuadrupleSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxesK2
      num den

/--
Raw four-prime support for the fixed-box target.

This removes the bookkeeping field `n`; the associated witness is recovered as
`p1*q1 - 1`.
-/
structure FixedOneOneRawPrimeQuadrupleK2 where
  left : SemiprimePairK2
  right : SemiprimePairK2
  deriving DecidableEq

def FixedOneOneRawPrimeQuadrupleK2.n
    (u : FixedOneOneRawPrimeQuadrupleK2) : ℕ :=
  u.left.p * u.left.q - 1

def FixedOneOneRawPrimeQuadrupleK2.toPrimeQuadruple
    (u : FixedOneOneRawPrimeQuadrupleK2) : FixedOneOnePrimeQuadrupleK2 :=
  { n := u.n, left := u.left, right := u.right }

def fixedOneOneRawPrimeQuadrupleTupleBoxK2
    (cfg : K2Params) : Finset FixedOneOneRawPrimeQuadrupleK2 :=
  ((semiprimePairBoxK2 cfg).product (semiprimePairBoxK2 cfg)).image
    (fun t => { left := t.1, right := t.2 })

/--
Clean raw fixed-ratio target in the literal four-prime form
`p1*q1 + 1 = 2*(p2*q2)`.
-/
def FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2
    (cfg : K2Params) (u : FixedOneOneRawPrimeQuadrupleK2) : Prop :=
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  u.n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  u.left.p * u.left.q + 1 = 2 * (u.right.p * u.right.q) ∧
  Nat.Prime u.left.p ∧ Nat.Prime u.left.q ∧
  Nat.Prime u.right.p ∧ Nat.Prime u.right.q ∧
  InBand cfg.pLo cfg.pHi u.left.p ∧
  InBand cfg.qLo cfg.qHi u.left.q ∧
  InBand cfg.pLo cfg.pHi u.right.p ∧
  InBand cfg.qLo cfg.qHi u.right.q ∧
  u.left.p < u.left.q ∧
  3 * u.left.p < 2 * u.left.q ∧
  u.left.q < 2 * u.left.p ∧
  u.right.p < u.right.q ∧
  5 * u.right.p < 4 * u.right.q ∧
  3 * u.right.q < 4 * u.right.p

instance (cfg : K2Params) :
    DecidablePred (FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg) := by
  intro u
  unfold FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2
    FixedOneOneRawPrimeQuadrupleK2.n SameLargePrimeBandK2
    FiniteSmallOddK2 FiniteMediumHygieneK2 InBand
  infer_instance

def fixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    (cfg : K2Params) : Finset FixedOneOneRawPrimeQuadrupleK2 :=
  (fixedOneOneRawPrimeQuadrupleTupleBoxK2 cfg).filter
    (FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg)

def fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 (cfg : K2Params) : ℕ :=
  (fixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 cfg).card

def PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    (cfg : K2Params) : Prop :=
  0 < fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 cfg

def PositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    (num den : ℕ) (cfg : K2Params) : Prop :=
  0 < num ∧ num * cfg.x ≤
    den * fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 cfg

def InfinitelyManyPositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2 :
    Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧ PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 cfg

def InfinitelyManyPositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2
    (num den : ℕ) : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params,
    N ≤ cfg.x ∧
      PositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 num den cfg

/--
Weakest pointwise raw fixed-box target isolated by the Lean development: for
arbitrarily large lower bounds, produce one literal four-prime witness satisfying
the clean ratio windows and finite Kummer hygiene.
-/
def FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ u : FixedOneOneRawPrimeQuadrupleK2,
    N ≤ u.n ∧ FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u

/--
Literal four-prime fixed-box supply target.

This is still a conditional analytic input, but it is now stated directly in
terms of the fixed affine semiprime correlation.
-/
def FixedOneOneRawCleanRatioPrimeQuadrupleSupplyK2 : Prop :=
  ∃ num : ℕ, ∃ den : ℕ,
    InfinitelyManyPositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2
      num den

/-- A natural-number affine linear form `coeff * u + offset`. -/
structure LinearFormK2 where
  coeff : ℕ
  offset : ℕ
  deriving DecidableEq

def LinearFormK2.eval (L : LinearFormK2) (u : ℕ) : ℕ :=
  L.coeff * u + L.offset

/-- All forms in a finite list are prime at one parameter. -/
def LinearFormsPrimeTupleAtK2
    (forms : List LinearFormK2) (u : ℕ) : Prop :=
  ∀ L : LinearFormK2, L ∈ forms → Nat.Prime (L.eval u)

/--
Qualitative prime-tuple supply for a finite list of linear forms.

This is the Lean-facing Dickson-style supply interface: for every lower bound
on the parameter, all listed forms are prime simultaneously.
-/
def LinearFormsPrimeTupleSupplyK2 (forms : List LinearFormK2) : Prop :=
  ∀ U : ℕ, ∃ u : ℕ,
    U ≤ u ∧ ∀ L : LinearFormK2, L ∈ forms → Nat.Prime (L.eval u)

/--
Local admissibility for a finite list of linear forms: no prime divides the
product of all listed forms for every parameter.
-/
def LinearFormsLocallyAdmissibleK2 (forms : List LinearFormK2) : Prop :=
  ∀ r : ℕ, Nat.Prime r → ∃ u : ℕ,
    ∀ L : LinearFormK2, L ∈ forms → ¬ r ∣ L.eval u

/--
Dickson-style prime-tuple conjecture for finite lists of natural affine forms.

This is a conjectural interface, not an axiom.  The file proves consequences
from this proposition when it is supplied as a hypothesis.
-/
def DicksonConjectureK2 : Prop :=
  ∀ forms : List LinearFormK2,
    LinearFormsLocallyAdmissibleK2 forms →
      LinearFormsPrimeTupleSupplyK2 forms

/--
The explicit Dickson-family skeleton isolated by the fixed-box downgrade:

`(48*m + 29) * (76*m + 65) + 1 =
  2 * ((38*m + 23) * (48*m + 41))`.

The arithmetic identity and ratio windows below are proved in Lean.  The
remaining supply statement still has to provide infinitely many parameters
where these four linear forms are prime and the finite Kummer hygiene holds.
-/
def dicksonP1K2 (m : ℕ) : ℕ := 48 * m + 29

def dicksonQ1K2 (m : ℕ) : ℕ := 76 * m + 65

def dicksonP2K2 (m : ℕ) : ℕ := 38 * m + 23

def dicksonQ2K2 (m : ℕ) : ℕ := 48 * m + 41

def dicksonRawQuadrupleK2 (m : ℕ) :
    FixedOneOneRawPrimeQuadrupleK2 :=
  { left := { p := dicksonP1K2 m, q := dicksonQ1K2 m },
    right := { p := dicksonP2K2 m, q := dicksonQ2K2 m } }

def dicksonFamilyEquationValueK2 (m : ℕ) : ℕ :=
  3648 * m ^ 2 + 5324 * m + 1886

def dicksonFamilyNK2 (m : ℕ) : ℕ :=
  3648 * m ^ 2 + 5324 * m + 1884

def dicksonAP12RawQuadrupleK2 (u : ℕ) :
    FixedOneOneRawPrimeQuadrupleK2 :=
  dicksonRawQuadrupleK2 (12 * u)

/--
The unscaled Dickson tuple restricted to the admissible progression `m = 12u`.

This is the same closed-form prime-tuple supply as the AP3 interface below,
but stated in the original `(48m+29, 76m+65, 38m+23, 48m+41)` variables.
-/
def DicksonAP12ClosedFormsSupplyK2 : Prop :=
  ∀ U : ℕ, ∃ u : ℕ,
    U ≤ u ∧
    Nat.Prime (dicksonP1K2 (12 * u)) ∧
    Nat.Prime (dicksonQ1K2 (12 * u)) ∧
    Nat.Prime (dicksonP2K2 (12 * u)) ∧
    Nat.Prime (dicksonQ2K2 (12 * u))

/--
Literal closed-form supply for the single Dickson tuple on the admissible
progression `m = 12u`, written without the `dicksonP*` abbreviations.

This is the exact prime-tuple infinitude hypothesis isolated by the latest
fixed-box downgrade.  It is a proposition, not an axiom.
-/
def ExplicitDicksonAP12PrimeTupleSupplyK2 : Prop :=
  ∀ U : ℕ, ∃ u : ℕ,
    U ≤ u ∧
    Nat.Prime (48 * (12 * u) + 29) ∧
    Nat.Prime (76 * (12 * u) + 65) ∧
    Nat.Prime (38 * (12 * u) + 23) ∧
    Nat.Prime (48 * (12 * u) + 41)

/--
The four primality conditions for the unscaled Dickson tuple, in the original
`m` variable from the analytic reduction.
-/
def ExplicitDicksonPrimeTupleAtK2 (m : ℕ) : Prop :=
  Nat.Prime (48 * m + 29) ∧
  Nat.Prime (76 * m + 65) ∧
  Nat.Prime (38 * m + 23) ∧
  Nat.Prime (48 * m + 41)

/--
The same explicit Dickson supply target, stated directly in the original
parameter `m` with the finite Kummer hygiene progression `12 ∣ m`.

This is still a conjectural supply proposition, not an axiom.
-/
def ExplicitDicksonMod12PrimeTupleSupplyK2 : Prop :=
  ∀ M : ℕ, ∃ m : ℕ,
    M ≤ m ∧ 12 ∣ m ∧ ExplicitDicksonPrimeTupleAtK2 m

theorem explicitDicksonMod12PrimeTupleSupply_of_AP12
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    ExplicitDicksonMod12PrimeTupleSupplyK2 := by
  intro M
  rcases hSupply M with ⟨u, hMu, hp1, hq1, hp2, hq2⟩
  refine ⟨12 * u, ?_, ?_, ?_⟩
  · omega
  · exact ⟨u, rfl⟩
  · exact ⟨hp1, hq1, hp2, hq2⟩

theorem explicitDicksonAP12PrimeTupleSupply_of_mod12
    (hSupply : ExplicitDicksonMod12PrimeTupleSupplyK2) :
    ExplicitDicksonAP12PrimeTupleSupplyK2 := by
  intro U
  rcases hSupply (12 * U) with ⟨m, hM, h12, hp1, hq1, hp2, hq2⟩
  rcases h12 with ⟨u, rfl⟩
  have hU : U ≤ u := by omega
  exact ⟨u, hU, hp1, hq1, hp2, hq2⟩

theorem explicitDicksonMod12PrimeTupleSupply_iff_AP12 :
    ExplicitDicksonMod12PrimeTupleSupplyK2 ↔
      ExplicitDicksonAP12PrimeTupleSupplyK2 := by
  constructor
  · exact explicitDicksonAP12PrimeTupleSupply_of_mod12
  · exact explicitDicksonMod12PrimeTupleSupply_of_AP12

def dicksonAPRawQuadrupleK2 (t : ℕ) :
    FixedOneOneRawPrimeQuadrupleK2 :=
  dicksonRawQuadrupleK2 (4 * t)

def DicksonFamilyRawSideConditionsK2
    (cfg : K2Params) (m : ℕ) : Prop :=
  let u := dicksonRawQuadrupleK2 m
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  u.n % 16 = 12 ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  Nat.Prime u.left.p ∧ Nat.Prime u.left.q ∧
  Nat.Prime u.right.p ∧ Nat.Prime u.right.q ∧
  InBand cfg.pLo cfg.pHi u.left.p ∧
  InBand cfg.qLo cfg.qHi u.left.q ∧
  InBand cfg.pLo cfg.pHi u.right.p ∧
  InBand cfg.qLo cfg.qHi u.right.q

def DicksonFamilySupplyK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ m : ℕ,
    N ≤ (dicksonRawQuadrupleK2 m).n ∧
    4 ≤ m ∧
    DicksonFamilyRawSideConditionsK2 cfg m

def DicksonAPFamilyRawSideConditionsK2
    (cfg : K2Params) (t : ℕ) : Prop :=
  let u := dicksonAPRawQuadrupleK2 t
  cfg.x ≤ u.n ∧ u.n ≤ 2 * cfg.x ∧
  SameLargePrimeBandK2 cfg ∧
  FiniteSmallOddK2 cfg u.n ∧
  FiniteMediumHygieneK2 cfg u.n ∧
  Nat.Prime u.left.p ∧ Nat.Prime u.left.q ∧
  Nat.Prime u.right.p ∧ Nat.Prime u.right.q ∧
  InBand cfg.pLo cfg.pHi u.left.p ∧
  InBand cfg.qLo cfg.qHi u.left.q ∧
  InBand cfg.pLo cfg.pHi u.right.p ∧
  InBand cfg.qLo cfg.qHi u.right.q

def DicksonAPFamilySupplyK2 : Prop :=
  ∀ N : ℕ, ∃ cfg : K2Params, ∃ t : ℕ,
    N ≤ (dicksonAPRawQuadrupleK2 t).n ∧
    1 ≤ t ∧
    DicksonAPFamilyRawSideConditionsK2 cfg t

theorem dicksonFamilyK2_equation (m : ℕ) :
    dicksonP1K2 m * dicksonQ1K2 m + 1 =
      2 * (dicksonP2K2 m * dicksonQ2K2 m) := by
  unfold dicksonP1K2 dicksonQ1K2 dicksonP2K2 dicksonQ2K2
  ring

theorem dicksonFamilyK2_left_product_add_one_eq_closed (m : ℕ) :
    dicksonP1K2 m * dicksonQ1K2 m + 1 =
      dicksonFamilyEquationValueK2 m := by
  unfold dicksonP1K2 dicksonQ1K2 dicksonFamilyEquationValueK2
  ring

theorem dicksonFamilyK2_right_twice_product_eq_closed (m : ℕ) :
    2 * (dicksonP2K2 m * dicksonQ2K2 m) =
      dicksonFamilyEquationValueK2 m := by
  unfold dicksonP2K2 dicksonQ2K2 dicksonFamilyEquationValueK2
  ring

theorem dicksonFamilyK2_n_eq_closed (m : ℕ) :
    (dicksonRawQuadrupleK2 m).n = dicksonFamilyNK2 m := by
  dsimp [FixedOneOneRawPrimeQuadrupleK2.n, dicksonRawQuadrupleK2,
    dicksonP1K2, dicksonQ1K2, dicksonFamilyNK2]
  have hprod :
      (48 * m + 29) * (76 * m + 65) =
        3648 * m ^ 2 + 5324 * m + 1885 := by
    ring
  rw [hprod]
  omega

theorem dicksonAP12ClosedForms_equation (u : ℕ) :
    dicksonP1K2 (12 * u) * dicksonQ1K2 (12 * u) + 1 =
      2 * (dicksonP2K2 (12 * u) * dicksonQ2K2 (12 * u)) :=
  dicksonFamilyK2_equation (12 * u)

theorem dicksonFamilyK2_q2_eq_p1_add_twelve (m : ℕ) :
    dicksonQ2K2 m = dicksonP1K2 m + 12 := by
  unfold dicksonQ2K2 dicksonP1K2
  ring

theorem dicksonFamilyK2_left_ratio {m : ℕ} (hm : 1 ≤ m) :
    dicksonP1K2 m < dicksonQ1K2 m ∧
    3 * dicksonP1K2 m < 2 * dicksonQ1K2 m ∧
    dicksonQ1K2 m < 2 * dicksonP1K2 m := by
  unfold dicksonP1K2 dicksonQ1K2
  constructor
  · omega
  constructor
  · omega
  · omega

theorem dicksonFamilyK2_right_ratio {m : ℕ} (hm : 4 ≤ m) :
    dicksonP2K2 m < dicksonQ2K2 m ∧
    5 * dicksonP2K2 m < 4 * dicksonQ2K2 m ∧
    3 * dicksonQ2K2 m < 4 * dicksonP2K2 m := by
  unfold dicksonP2K2 dicksonQ2K2
  constructor
  · omega
  constructor
  · omega
  · omega

theorem dicksonFamilyK2_n_mod16 (m : ℕ) :
    (dicksonRawQuadrupleK2 m).n % 16 = (12 * m + 12) % 16 := by
  dsimp [FixedOneOneRawPrimeQuadrupleK2.n, dicksonRawQuadrupleK2,
    dicksonP1K2, dicksonQ1K2]
  have hprod :
      (48 * m + 29) * (76 * m + 65) =
        16 * (228 * m ^ 2 + 332 * m + 117) + (12 * m + 13) := by
    ring
  rw [hprod]
  have hsub :
      16 * (228 * m ^ 2 + 332 * m + 117) + (12 * m + 13) - 1 =
        16 * (228 * m ^ 2 + 332 * m + 117) + (12 * m + 12) := by
    omega
  rw [hsub, Nat.add_mod, Nat.mul_mod_right]
  simp

theorem dicksonFamilyK2_n_mod3 (m : ℕ) :
    (dicksonRawQuadrupleK2 m).n % 3 = (2 * m) % 3 := by
  dsimp [FixedOneOneRawPrimeQuadrupleK2.n, dicksonRawQuadrupleK2,
    dicksonP1K2, dicksonQ1K2]
  have hprod :
      (48 * m + 29) * (76 * m + 65) =
        3 * (1216 * m ^ 2 + 1774 * m + 628) + (2 * m + 1) := by
    ring
  rw [hprod]
  have hsub :
      3 * (1216 * m ^ 2 + 1774 * m + 628) + (2 * m + 1) - 1 =
        3 * (1216 * m ^ 2 + 1774 * m + 628) + 2 * m := by
    omega
  rw [hsub, Nat.add_mod, Nat.mul_mod_right]
  simp

theorem four_dvd_m_of_dicksonFamilyK2_n_mod16_eq_12
    {m : ℕ}
    (hmod : (dicksonRawQuadrupleK2 m).n % 16 = 12) :
    4 ∣ m := by
  have h : (12 * m + 12) % 16 = 12 := by
    simpa [dicksonFamilyK2_n_mod16 m] using hmod
  omega

theorem three_dvd_m_of_dicksonFamilyK2_three_dvd_n
    {m : ℕ}
    (hdiv : 3 ∣ (dicksonRawQuadrupleK2 m).n) :
    3 ∣ m := by
  have hzero : (2 * m) % 3 = 0 := by
    have hnzero : (dicksonRawQuadrupleK2 m).n % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdiv
    simpa [dicksonFamilyK2_n_mod3 m] using hnzero
  omega

theorem twelve_dvd_m_of_dicksonFamilyRawCleanRatioGood
    {cfg : K2Params} {m : ℕ}
    (hgood : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg
      (dicksonRawQuadrupleK2 m)) :
    12 ∣ m := by
  rcases hgood with
    ⟨_hxLo, _hxHi, hmod, _hSame, hSmall, _hMedium, _hEq,
      _hp1, _hq1, _hp2, _hq2, _hp1Band, _hq1Band, _hp2Band,
      _hq2Band, _hleftOrder, _hleftLo, _hleftHi, _hrightOrder,
      _hrightLo, _hrightHi⟩
  have hthree_mem : 3 ∈ Finset.Icc 0 cfg.P0 :=
    Finset.mem_Icc.mpr ⟨by norm_num, cfg.P0_ge_3⟩
  have hthree_n : 3 ∣ (dicksonRawQuadrupleK2 m).n :=
    hSmall 3 hthree_mem (by norm_num) (by norm_num)
  have h3 : 3 ∣ m :=
    three_dvd_m_of_dicksonFamilyK2_three_dvd_n hthree_n
  have h4 : 4 ∣ m :=
    four_dvd_m_of_dicksonFamilyK2_n_mod16_eq_12 hmod
  have hcop : Nat.Coprime 3 4 := by norm_num
  have h12 : 3 * 4 ∣ m :=
    hcop.mul_dvd_of_dvd_of_dvd h3 h4
  simpa using h12

theorem dicksonAPRawQuadrupleK2_eq (t : ℕ) :
    dicksonAPRawQuadrupleK2 t = dicksonRawQuadrupleK2 (4 * t) := rfl

theorem dicksonAPFamilyK2_equation (t : ℕ) :
    (dicksonAPRawQuadrupleK2 t).left.p *
        (dicksonAPRawQuadrupleK2 t).left.q + 1 =
      2 * ((dicksonAPRawQuadrupleK2 t).right.p *
        (dicksonAPRawQuadrupleK2 t).right.q) := by
  simpa [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2]
    using dicksonFamilyK2_equation (4 * t)

theorem dicksonAPFamilyK2_mod16 (t : ℕ) :
    (dicksonAPRawQuadrupleK2 t).n % 16 = 12 := by
  dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
    FixedOneOneRawPrimeQuadrupleK2.n, dicksonP1K2, dicksonQ1K2]
  have hprod :
      (48 * (4 * t) + 29) * (76 * (4 * t) + 65) =
        16 * (3648 * t ^ 2 + 1331 * t + 117) + 13 := by
    ring
  rw [hprod]
  have hsub :
      16 * (3648 * t ^ 2 + 1331 * t + 117) + 13 - 1 =
        16 * (3648 * t ^ 2 + 1331 * t + 117) + 12 := by
    omega
  rw [hsub]
  omega

theorem dicksonAPFamilyK2_left_ratio {t : ℕ} (ht : 1 ≤ t) :
    (dicksonAPRawQuadrupleK2 t).left.p <
        (dicksonAPRawQuadrupleK2 t).left.q ∧
    3 * (dicksonAPRawQuadrupleK2 t).left.p <
        2 * (dicksonAPRawQuadrupleK2 t).left.q ∧
    (dicksonAPRawQuadrupleK2 t).left.q <
        2 * (dicksonAPRawQuadrupleK2 t).left.p := by
  simpa [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2]
    using dicksonFamilyK2_left_ratio (by omega : 1 ≤ 4 * t)

theorem dicksonAPFamilyK2_right_ratio {t : ℕ} (ht : 1 ≤ t) :
    (dicksonAPRawQuadrupleK2 t).right.p <
        (dicksonAPRawQuadrupleK2 t).right.q ∧
    5 * (dicksonAPRawQuadrupleK2 t).right.p <
        4 * (dicksonAPRawQuadrupleK2 t).right.q ∧
    3 * (dicksonAPRawQuadrupleK2 t).right.q <
        4 * (dicksonAPRawQuadrupleK2 t).right.p := by
  simpa [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2]
    using dicksonFamilyK2_right_ratio (by omega : 4 ≤ 4 * t)

def dicksonAPFamilyLocalGoodK2 (r t : ℕ) : Prop :=
  ¬ r ∣ (dicksonAPRawQuadrupleK2 t).left.p ∧
  ¬ r ∣ (dicksonAPRawQuadrupleK2 t).left.q ∧
  ¬ r ∣ (dicksonAPRawQuadrupleK2 t).right.p ∧
  ¬ r ∣ (dicksonAPRawQuadrupleK2 t).right.q

theorem prime_not_dvd_prime_const
    {r c : ℕ} (hr : Nat.Prime r) (hc : Nat.Prime c) (hne : r ≠ c) :
    ¬ r ∣ c := by
  intro hdiv
  rcases (Nat.dvd_prime hc).mp hdiv with h_one | h_eq
  · exact hr.ne_one h_one
  · exact hne h_eq

theorem prime_dvd_65_cases
    {r : ℕ} (hr : Nat.Prime r) (hdiv : r ∣ 65) :
    r = 5 ∨ r = 13 := by
  have hmul : r ∣ 5 * 13 := by
    simpa using hdiv
  rcases (Nat.Prime.dvd_mul hr).mp hmul with h5 | h13
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with h_one | h_eq
    · exact False.elim (hr.ne_one h_one)
    · exact Or.inl h_eq
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp h13 with h_one | h_eq
    · exact False.elim (hr.ne_one h_one)
    · exact Or.inr h_eq

theorem dicksonAPFamilyLocalGoodK2_at_zero
    {r : ℕ} (hr : Nat.Prime r)
    (h5 : r ≠ 5) (h13 : r ≠ 13) (h23 : r ≠ 23)
    (h29 : r ≠ 29) (h41 : r ≠ 41) :
    dicksonAPFamilyLocalGoodK2 r 0 := by
  unfold dicksonAPFamilyLocalGoodK2 dicksonAPRawQuadrupleK2
    dicksonRawQuadrupleK2 dicksonP1K2 dicksonQ1K2 dicksonP2K2
    dicksonQ2K2
  norm_num
  constructor
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 29) h29
  constructor
  · intro hdiv
    rcases prime_dvd_65_cases hr hdiv with h_eq | h_eq
    · exact h5 h_eq
    · exact h13 h_eq
  constructor
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 23) h23
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 41) h41

theorem dicksonAPFamilyLocalGoodK2_exceptional :
    dicksonAPFamilyLocalGoodK2 5 4 ∧
    dicksonAPFamilyLocalGoodK2 13 2 ∧
    dicksonAPFamilyLocalGoodK2 23 1 ∧
    dicksonAPFamilyLocalGoodK2 29 1 ∧
    dicksonAPFamilyLocalGoodK2 41 2 := by
  norm_num [dicksonAPFamilyLocalGoodK2, dicksonAPRawQuadrupleK2,
    dicksonRawQuadrupleK2, dicksonP1K2, dicksonQ1K2, dicksonP2K2,
    dicksonQ2K2]

theorem dicksonAPFamily_admissible :
    ∀ r : ℕ, Nat.Prime r → ∃ t : ℕ,
      dicksonAPFamilyLocalGoodK2 r t := by
  intro r hr
  rcases dicksonAPFamilyLocalGoodK2_exceptional with
    ⟨h5Good, h13Good, h23Good, h29Good, h41Good⟩
  by_cases h5 : r = 5
  · subst r
    exact ⟨4, h5Good⟩
  by_cases h13 : r = 13
  · subst r
    exact ⟨2, h13Good⟩
  by_cases h23 : r = 23
  · subst r
    exact ⟨1, h23Good⟩
  by_cases h29 : r = 29
  · subst r
    exact ⟨1, h29Good⟩
  by_cases h41 : r = 41
  · subst r
    exact ⟨2, h41Good⟩
  exact ⟨0, dicksonAPFamilyLocalGoodK2_at_zero
    hr h5 h13 h23 h29 h41⟩

def dicksonAP4P1K2 (t : ℕ) : ℕ := 192 * t + 29

def dicksonAP4Q1K2 (t : ℕ) : ℕ := 304 * t + 65

def dicksonAP4P2K2 (t : ℕ) : ℕ := 152 * t + 23

def dicksonAP4Q2K2 (t : ℕ) : ℕ := 192 * t + 41

def dicksonAP4NK2 (t : ℕ) : ℕ :=
  58368 * t ^ 2 + 21296 * t + 1884

theorem dicksonAP4NK2_ge_parameter (t : ℕ) :
    t ≤ dicksonAP4NK2 t := by
  unfold dicksonAP4NK2
  nlinarith [sq_nonneg (t : ℤ)]

theorem dicksonAP4_n_eq (t : ℕ) :
    (dicksonAPRawQuadrupleK2 t).n = dicksonAP4NK2 t := by
  dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
    FixedOneOneRawPrimeQuadrupleK2.n, dicksonP1K2, dicksonQ1K2,
    dicksonAP4NK2]
  have hprod :
      (48 * (4 * t) + 29) * (76 * (4 * t) + 65) =
        58368 * t ^ 2 + 21296 * t + 1885 := by
    ring
  rw [hprod]
  omega

theorem dicksonAP4ClosedForms_equation (t : ℕ) :
    dicksonAP4P1K2 t * dicksonAP4Q1K2 t + 1 =
      2 * (dicksonAP4P2K2 t * dicksonAP4Q2K2 t) := by
  unfold dicksonAP4P1K2 dicksonAP4Q1K2 dicksonAP4P2K2
    dicksonAP4Q2K2
  ring

theorem dicksonAP4ClosedForms_left_product_eq_n_add_one (t : ℕ) :
    dicksonAP4P1K2 t * dicksonAP4Q1K2 t =
      dicksonAP4NK2 t + 1 := by
  unfold dicksonAP4P1K2 dicksonAP4Q1K2 dicksonAP4NK2
  ring

theorem dicksonAP4ClosedForms_right_twice_product_eq_n_add_two (t : ℕ) :
    2 * (dicksonAP4P2K2 t * dicksonAP4Q2K2 t) =
      dicksonAP4NK2 t + 2 := by
  unfold dicksonAP4P2K2 dicksonAP4Q2K2 dicksonAP4NK2
  ring

theorem dicksonAP4Q2_eq_p1_add_twelve (t : ℕ) :
    dicksonAP4Q2K2 t = dicksonAP4P1K2 t + 12 := by
  unfold dicksonAP4Q2K2 dicksonAP4P1K2
  ring

theorem dicksonAP4_left_ratio {t : ℕ} (ht : 1 ≤ t) :
    dicksonAP4P1K2 t < dicksonAP4Q1K2 t ∧
    3 * dicksonAP4P1K2 t < 2 * dicksonAP4Q1K2 t ∧
    dicksonAP4Q1K2 t < 2 * dicksonAP4P1K2 t := by
  unfold dicksonAP4P1K2 dicksonAP4Q1K2
  constructor
  · omega
  constructor
  · omega
  · omega

theorem dicksonAP4_right_ratio {t : ℕ} (ht : 1 ≤ t) :
    dicksonAP4P2K2 t < dicksonAP4Q2K2 t ∧
    5 * dicksonAP4P2K2 t < 4 * dicksonAP4Q2K2 t ∧
    3 * dicksonAP4Q2K2 t < 4 * dicksonAP4P2K2 t := by
  unfold dicksonAP4P2K2 dicksonAP4Q2K2
  constructor
  · omega
  constructor
  · omega
  · omega

theorem dicksonAP4RawQuadrupleK2_closed (t : ℕ) :
    (dicksonAPRawQuadrupleK2 t).left.p = dicksonAP4P1K2 t ∧
    (dicksonAPRawQuadrupleK2 t).left.q = dicksonAP4Q1K2 t ∧
    (dicksonAPRawQuadrupleK2 t).right.p = dicksonAP4P2K2 t ∧
    (dicksonAPRawQuadrupleK2 t).right.q = dicksonAP4Q2K2 t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dicksonAPRawQuadrupleK2 dicksonRawQuadrupleK2
      dicksonP1K2 dicksonAP4P1K2
    ring
  · unfold dicksonAPRawQuadrupleK2 dicksonRawQuadrupleK2
      dicksonQ1K2 dicksonAP4Q1K2
    ring
  · unfold dicksonAPRawQuadrupleK2 dicksonRawQuadrupleK2
      dicksonP2K2 dicksonAP4P2K2
    ring
  · unfold dicksonAPRawQuadrupleK2 dicksonRawQuadrupleK2
      dicksonQ2K2 dicksonAP4Q2K2
    ring

def dicksonAP4ParamsK2 (t : ℕ) (ht : 1 ≤ t) : K2Params :=
  { x := (dicksonAPRawQuadrupleK2 t).n
    P0 := 3
    pLo := 151 * t + 22
    pHi := 304 * t + 65
    qLo := 151 * t + 22
    qHi := 304 * t + 65
    sMax := 4
    x_ge_2 := by
      rw [dicksonAP4_n_eq]
      unfold dicksonAP4NK2
      nlinarith [sq_nonneg (t : ℤ), ht]
    P0_ge_3 := by norm_num
    sMax_lt_pLo := by omega
    P0_lt_sMax := by norm_num
    four_lt_pLo := by omega
    four_lt_qLo := by omega
    qHi_sq_le_two_x := by
      rw [dicksonAP4_n_eq]
      unfold dicksonAP4NK2
      nlinarith [sq_nonneg (t : ℤ), ht]
    four_x_lt_pLo_cube := by
      rw [dicksonAP4_n_eq]
      unfold dicksonAP4NK2
      nlinarith [sq_nonneg (t : ℤ), ht] }

theorem three_dvd_t_of_dicksonAP4_primes
    {t : ℕ}
    (hq1 : Nat.Prime (dicksonAPRawQuadrupleK2 t).left.q)
    (hp2 : Nat.Prime (dicksonAPRawQuadrupleK2 t).right.p) :
    3 ∣ t := by
  have hcases : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by
    have hlt : t % 3 < 3 := Nat.mod_lt t (by norm_num)
    omega
  rcases hcases with h0 | h1 | h2
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · have hdiv : 3 ∣ (dicksonAPRawQuadrupleK2 t).left.q := by
      rw [Nat.dvd_iff_mod_eq_zero]
      dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
        dicksonQ1K2]
      omega
    have hq_eq :
        (dicksonAPRawQuadrupleK2 t).left.q = 3 :=
      (Nat.Prime.dvd_iff_eq hq1 (by norm_num : 3 ≠ 1)).1 hdiv
    dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
      dicksonQ1K2] at hq_eq
    omega
  · have hdiv : 3 ∣ (dicksonAPRawQuadrupleK2 t).right.p := by
      rw [Nat.dvd_iff_mod_eq_zero]
      dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
        dicksonP2K2]
      omega
    have hp_eq :
        (dicksonAPRawQuadrupleK2 t).right.p = 3 :=
      (Nat.Prime.dvd_iff_eq hp2 (by norm_num : 3 ≠ 1)).1 hdiv
    dsimp [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2,
      dicksonP2K2] at hp_eq
    omega

theorem dicksonAP4_finiteSmallOdd_of_primes
    {t : ℕ} (ht : 1 ≤ t)
    (hq1 : Nat.Prime (dicksonAPRawQuadrupleK2 t).left.q)
    (hp2 : Nat.Prime (dicksonAPRawQuadrupleK2 t).right.p) :
    FiniteSmallOddK2 (dicksonAP4ParamsK2 t ht)
      (dicksonAPRawQuadrupleK2 t).n := by
  intro r hrange hrprime hrne_two
  have hr_le : r ≤ 3 := (Finset.mem_Icc.mp hrange).2
  have hr_two_le : 2 ≤ r := hrprime.two_le
  have hcases : r = 2 ∨ r = 3 := by omega
  rcases hcases with htwo | hthree
  · exact False.elim (hrne_two htwo)
  · subst r
    have ht3 : 3 ∣ t := three_dvd_t_of_dicksonAP4_primes hq1 hp2
    rcases ht3 with ⟨u, rfl⟩
    rw [dicksonAP4_n_eq]
    unfold dicksonAP4NK2
    exact ⟨175104 * u ^ 2 + 21296 * u + 628, by ring⟩

theorem dicksonAP4_finiteMediumHygiene
    {t : ℕ} (ht : 1 ≤ t) :
    FiniteMediumHygieneK2 (dicksonAP4ParamsK2 t ht)
      (dicksonAPRawQuadrupleK2 t).n := by
  intro r hrange hrprime
  have hr_ge : 4 ≤ r := (Finset.mem_Icc.mp hrange).1
  have hr_le : r ≤ 4 := (Finset.mem_Icc.mp hrange).2
  have hr_eq : r = 4 := by omega
  subst r
  norm_num at hrprime

def DicksonAP4PrimeSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ t : ℕ,
    N ≤ (dicksonAPRawQuadrupleK2 t).n ∧
    1 ≤ t ∧
    Nat.Prime (dicksonAPRawQuadrupleK2 t).left.p ∧
    Nat.Prime (dicksonAPRawQuadrupleK2 t).left.q ∧
    Nat.Prime (dicksonAPRawQuadrupleK2 t).right.p ∧
    Nat.Prime (dicksonAPRawQuadrupleK2 t).right.q

/--
Closed-form AP4 version of the explicit Dickson supply target.

This is the weakest current Lean-facing tuple supply: the AP4 restriction gives
the required mod-16 condition, while the four prime conditions force the
remaining mod-3 small-prime hygiene.
-/
def DicksonAP4ClosedPrimeSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ t : ℕ,
    N ≤ dicksonAP4NK2 t ∧
    1 ≤ t ∧
    Nat.Prime (dicksonAP4P1K2 t) ∧
    Nat.Prime (dicksonAP4Q1K2 t) ∧
    Nat.Prime (dicksonAP4P2K2 t) ∧
    Nat.Prime (dicksonAP4Q2K2 t)

def dicksonAP4PrefixBoundK2 (U : ℕ) : ℕ :=
  (Finset.range U).sum dicksonAP4NK2 + 1

theorem dicksonAP4NK2_lt_prefixBound_of_lt
    {t U : ℕ} (ht : t < U) :
    dicksonAP4NK2 t < dicksonAP4PrefixBoundK2 U := by
  unfold dicksonAP4PrefixBoundK2
  have hmem : t ∈ Finset.range U := Finset.mem_range.mpr ht
  have hle :
      dicksonAP4NK2 t ≤ (Finset.range U).sum dicksonAP4NK2 := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  exact Nat.lt_succ_of_le hle

/--
The explicit AP4 Dickson tuple isolated by the fixed-box downgrade.

This is the single locally admissible prime-tuple instance whose infinitude
would supply the current conditional `k = 2` architecture.
-/
def dicksonAP4LinearFormsK2 : List LinearFormK2 :=
  [{ coeff := 192, offset := 29 },
    { coeff := 304, offset := 65 },
    { coeff := 152, offset := 23 },
    { coeff := 192, offset := 41 }]

def DicksonAP4ConjectureK2 : Prop :=
  LinearFormsPrimeTupleSupplyK2 dicksonAP4LinearFormsK2

/--
Qualitative prime-tuple form for the AP4 tuple.

This is equivalent to the closed supply below, but its lower bound is on the
tuple parameter `t` rather than on the resulting Erdős witness size.
-/
def DicksonAP4QualitativePrimeTupleK2 : Prop :=
  ∀ U : ℕ, ∃ t : ℕ,
    U ≤ t ∧
    1 ≤ t ∧
    Nat.Prime (dicksonAP4P1K2 t) ∧
    Nat.Prime (dicksonAP4Q1K2 t) ∧
    Nat.Prime (dicksonAP4P2K2 t) ∧
    Nat.Prime (dicksonAP4Q2K2 t)

theorem dicksonAP4LinearForms_admissible :
    LinearFormsLocallyAdmissibleK2 dicksonAP4LinearFormsK2 := by
  intro r hr
  rcases dicksonAPFamily_admissible r hr with ⟨t, hgood⟩
  unfold dicksonAPFamilyLocalGoodK2 at hgood
  rcases hgood with ⟨hp1, hq1, hp2, hq2⟩
  rcases dicksonAP4RawQuadrupleK2_closed t with
    ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
  refine ⟨t, ?_⟩
  intro L hL
  have hCases :
      L = { coeff := 192, offset := 29 } ∨
      L = { coeff := 304, offset := 65 } ∨
      L = { coeff := 152, offset := 23 } ∨
      L = { coeff := 192, offset := 41 } := by
    simpa [dicksonAP4LinearFormsK2] using hL
  rcases hCases with rfl | rfl | rfl | rfl
  · simpa [LinearFormK2.eval, dicksonAP4P1K2, hp1eq] using hp1
  · simpa [LinearFormK2.eval, dicksonAP4Q1K2, hq1eq] using hq1
  · simpa [LinearFormK2.eval, dicksonAP4P2K2, hp2eq] using hp2
  · simpa [LinearFormK2.eval, dicksonAP4Q2K2, hq2eq] using hq2

theorem dicksonAP4Conjecture_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP4ConjectureK2 :=
  hDickson dicksonAP4LinearFormsK2 dicksonAP4LinearForms_admissible

theorem dicksonAP4ClosedPrimeSupply_of_qualitative
    (hSupply : DicksonAP4QualitativePrimeTupleK2) :
    DicksonAP4ClosedPrimeSupplyK2 := by
  intro N
  rcases hSupply N with ⟨t, hNt, ht, hp1, hq1, hp2, hq2⟩
  exact ⟨t, le_trans hNt (dicksonAP4NK2_ge_parameter t),
    ht, hp1, hq1, hp2, hq2⟩

theorem dicksonAP4QualitativePrimeTuple_of_closedSupply
    (hSupply : DicksonAP4ClosedPrimeSupplyK2) :
    DicksonAP4QualitativePrimeTupleK2 := by
  intro U
  rcases hSupply (dicksonAP4PrefixBoundK2 U) with
    ⟨t, hN, ht1, hp1, hq1, hp2, hq2⟩
  have hU : U ≤ t := by
    by_contra hnot
    have hlt : t < U := Nat.lt_of_not_ge hnot
    have hsmall :
        dicksonAP4NK2 t < dicksonAP4PrefixBoundK2 U :=
      dicksonAP4NK2_lt_prefixBound_of_lt hlt
    exact (Nat.not_lt_of_ge hN) hsmall
  exact ⟨t, hU, ht1, hp1, hq1, hp2, hq2⟩

theorem dicksonAP4ClosedPrimeSupply_iff_qualitative :
    DicksonAP4ClosedPrimeSupplyK2 ↔
      DicksonAP4QualitativePrimeTupleK2 := by
  constructor
  · exact dicksonAP4QualitativePrimeTuple_of_closedSupply
  · exact dicksonAP4ClosedPrimeSupply_of_qualitative

theorem dicksonAP4QualitativePrimeTuple_iff_linearForms :
    DicksonAP4QualitativePrimeTupleK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP4LinearFormsK2 := by
  constructor
  · intro hSupply U
    rcases hSupply U with ⟨t, hU, _ht1, hp1, hq1, hp2, hq2⟩
    refine ⟨t, hU, ?_⟩
    intro L hL
    have hCases :
        L = { coeff := 192, offset := 29 } ∨
        L = { coeff := 304, offset := 65 } ∨
        L = { coeff := 152, offset := 23 } ∨
        L = { coeff := 192, offset := 41 } := by
      simpa [dicksonAP4LinearFormsK2] using hL
    rcases hCases with rfl | rfl | rfl | rfl
    · simpa [LinearFormK2.eval, dicksonAP4P1K2] using hp1
    · simpa [LinearFormK2.eval, dicksonAP4Q1K2] using hq1
    · simpa [LinearFormK2.eval, dicksonAP4P2K2] using hp2
    · simpa [LinearFormK2.eval, dicksonAP4Q2K2] using hq2
  · intro hSupply U
    rcases hSupply (max U 1) with ⟨t, hmax, hprime⟩
    have hU : U ≤ t := le_trans (le_max_left U 1) hmax
    have ht1 : 1 ≤ t := le_trans (le_max_right U 1) hmax
    have hp1 : Nat.Prime (dicksonAP4P1K2 t) := by
      have hmem :
          ({ coeff := 192, offset := 29 } : LinearFormK2) ∈
            dicksonAP4LinearFormsK2 := by
        simp [dicksonAP4LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP4P1K2]
        using hprime { coeff := 192, offset := 29 } hmem
    have hq1 : Nat.Prime (dicksonAP4Q1K2 t) := by
      have hmem :
          ({ coeff := 304, offset := 65 } : LinearFormK2) ∈
            dicksonAP4LinearFormsK2 := by
        simp [dicksonAP4LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP4Q1K2]
        using hprime { coeff := 304, offset := 65 } hmem
    have hp2 : Nat.Prime (dicksonAP4P2K2 t) := by
      have hmem :
          ({ coeff := 152, offset := 23 } : LinearFormK2) ∈
            dicksonAP4LinearFormsK2 := by
        simp [dicksonAP4LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP4P2K2]
        using hprime { coeff := 152, offset := 23 } hmem
    have hq2 : Nat.Prime (dicksonAP4Q2K2 t) := by
      have hmem :
          ({ coeff := 192, offset := 41 } : LinearFormK2) ∈
            dicksonAP4LinearFormsK2 := by
        simp [dicksonAP4LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP4Q2K2]
        using hprime { coeff := 192, offset := 41 } hmem
    exact ⟨t, hU, ht1, hp1, hq1, hp2, hq2⟩

theorem dicksonAP4Conjecture_iff_qualitative :
    DicksonAP4ConjectureK2 ↔ DicksonAP4QualitativePrimeTupleK2 := by
  simpa [DicksonAP4ConjectureK2]
    using (dicksonAP4QualitativePrimeTuple_iff_linearForms).symm

theorem dicksonAP4ClosedPrimeSupply_iff_linearFormsPrimeTuple :
    DicksonAP4ClosedPrimeSupplyK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP4LinearFormsK2 := by
  calc
    DicksonAP4ClosedPrimeSupplyK2 ↔
        DicksonAP4QualitativePrimeTupleK2 :=
      dicksonAP4ClosedPrimeSupply_iff_qualitative
    _ ↔ LinearFormsPrimeTupleSupplyK2 dicksonAP4LinearFormsK2 :=
      dicksonAP4QualitativePrimeTuple_iff_linearForms

theorem dicksonAP4Conjecture_iff_closedPrimeSupply :
    DicksonAP4ConjectureK2 ↔ DicksonAP4ClosedPrimeSupplyK2 := by
  simpa [DicksonAP4ConjectureK2]
    using (dicksonAP4ClosedPrimeSupply_iff_linearFormsPrimeTuple).symm

theorem dicksonAP4ClosedPrimeSupply_of_dicksonAP4Conjecture
    (hSupply : DicksonAP4ConjectureK2) :
    DicksonAP4ClosedPrimeSupplyK2 := by
  intro N
  rcases hSupply (max N 1) with ⟨t, htBound, hprime⟩
  have hN : N ≤ t := le_trans (le_max_left N 1) htBound
  have ht : 1 ≤ t := le_trans (le_max_right N 1) htBound
  refine ⟨t, le_trans hN (dicksonAP4NK2_ge_parameter t), ht,
    ?_, ?_, ?_, ?_⟩
  · have hmem :
        ({ coeff := 192, offset := 29 } : LinearFormK2) ∈
          dicksonAP4LinearFormsK2 := by
      simp [dicksonAP4LinearFormsK2]
    simpa [LinearFormK2.eval, dicksonAP4P1K2] using hprime _ hmem
  · have hmem :
        ({ coeff := 304, offset := 65 } : LinearFormK2) ∈
          dicksonAP4LinearFormsK2 := by
      simp [dicksonAP4LinearFormsK2]
    simpa [LinearFormK2.eval, dicksonAP4Q1K2] using hprime _ hmem
  · have hmem :
        ({ coeff := 152, offset := 23 } : LinearFormK2) ∈
          dicksonAP4LinearFormsK2 := by
      simp [dicksonAP4LinearFormsK2]
    simpa [LinearFormK2.eval, dicksonAP4P2K2] using hprime _ hmem
  · have hmem :
        ({ coeff := 192, offset := 41 } : LinearFormK2) ∈
          dicksonAP4LinearFormsK2 := by
      simp [dicksonAP4LinearFormsK2]
    simpa [LinearFormK2.eval, dicksonAP4Q2K2] using hprime _ hmem

theorem dicksonAP4ClosedPrimeSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP4ClosedPrimeSupplyK2 :=
  dicksonAP4ClosedPrimeSupply_of_dicksonAP4Conjecture
    (dicksonAP4Conjecture_of_dicksonConjectureK2 hDickson)

theorem dicksonAP4PrimeSupply_iff_closed :
    DicksonAP4PrimeSupplyK2 ↔ DicksonAP4ClosedPrimeSupplyK2 := by
  constructor
  · intro hSupply N
    rcases hSupply N with ⟨t, hN, ht, hp1, hq1, hp2, hq2⟩
    rcases dicksonAP4RawQuadrupleK2_closed t with
      ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
    refine ⟨t, ?_, ht, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonAP4_n_eq] using hN
    · simpa [hp1eq] using hp1
    · simpa [hq1eq] using hq1
    · simpa [hp2eq] using hp2
    · simpa [hq2eq] using hq2
  · intro hSupply N
    rcases hSupply N with ⟨t, hN, ht, hp1, hq1, hp2, hq2⟩
    rcases dicksonAP4RawQuadrupleK2_closed t with
      ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
    refine ⟨t, ?_, ht, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonAP4_n_eq] using hN
    · simpa [hp1eq] using hp1
    · simpa [hq1eq] using hq1
    · simpa [hp2eq] using hp2
    · simpa [hq2eq] using hq2

theorem dicksonAP4FamilyRawSideConditions_of_primes
    {t : ℕ} (ht : 1 ≤ t)
    (hp1 : Nat.Prime (dicksonAPRawQuadrupleK2 t).left.p)
    (hq1 : Nat.Prime (dicksonAPRawQuadrupleK2 t).left.q)
    (hp2 : Nat.Prime (dicksonAPRawQuadrupleK2 t).right.p)
    (hq2 : Nat.Prime (dicksonAPRawQuadrupleK2 t).right.q) :
    DicksonAPFamilyRawSideConditionsK2
      (dicksonAP4ParamsK2 t ht) t := by
  unfold DicksonAPFamilyRawSideConditionsK2
  dsimp [dicksonAP4ParamsK2, SameLargePrimeBandK2, InBand,
    dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2, dicksonP1K2,
    dicksonQ1K2, dicksonP2K2, dicksonQ2K2]
  refine ⟨?_, ?_, ?_, ?_, ?_, hp1, hq1, hp2, hq2,
    ?_, ?_, ?_, ?_⟩
  · exact le_rfl
  · omega
  · exact ⟨rfl, rfl⟩
  · exact dicksonAP4_finiteSmallOdd_of_primes ht hq1 hp2
  · exact dicksonAP4_finiteMediumHygiene ht
  · omega
  · omega
  · omega
  · omega

theorem dicksonAPFamilySupply_of_dicksonAP4PrimeSupply
    (hSupply : DicksonAP4PrimeSupplyK2) :
    DicksonAPFamilySupplyK2 := by
  intro N
  rcases hSupply N with ⟨t, hN, ht, hp1, hq1, hp2, hq2⟩
  refine ⟨dicksonAP4ParamsK2 t ht, t, hN, ht, ?_⟩
  exact dicksonAP4FamilyRawSideConditions_of_primes ht hp1 hq1 hp2 hq2

def dicksonAP3RawQuadrupleK2 (u : ℕ) :
    FixedOneOneRawPrimeQuadrupleK2 :=
  dicksonAPRawQuadrupleK2 (3 * u)

theorem dicksonAP12RawQuadrupleK2_eq_AP3 (u : ℕ) :
    dicksonAP12RawQuadrupleK2 u = dicksonAP3RawQuadrupleK2 u := by
  unfold dicksonAP12RawQuadrupleK2 dicksonAP3RawQuadrupleK2
    dicksonAPRawQuadrupleK2
  rw [show 12 * u = 4 * (3 * u) by ring]

def dicksonAP3P1K2 (u : ℕ) : ℕ := 576 * u + 29

def dicksonAP3Q1K2 (u : ℕ) : ℕ := 912 * u + 65

def dicksonAP3P2K2 (u : ℕ) : ℕ := 456 * u + 23

def dicksonAP3Q2K2 (u : ℕ) : ℕ := 576 * u + 41

theorem dicksonAP3ClosedForms_equation (u : ℕ) :
    (576 * u + 29) * (912 * u + 65) + 1 =
      2 * ((456 * u + 23) * (576 * u + 41)) := by
  ring

def dicksonAP3NK2 (u : ℕ) : ℕ :=
  525312 * u ^ 2 + 63888 * u + 1884

theorem dicksonAP3NK2_eq_dicksonFamilyNK2 (u : ℕ) :
    dicksonAP3NK2 u = dicksonFamilyNK2 (12 * u) := by
  unfold dicksonAP3NK2 dicksonFamilyNK2
  ring

theorem dicksonAP12_n_eq (u : ℕ) :
    (dicksonAP12RawQuadrupleK2 u).n = dicksonAP3NK2 u := by
  calc
    (dicksonAP12RawQuadrupleK2 u).n =
        (dicksonRawQuadrupleK2 (12 * u)).n := rfl
    _ = dicksonFamilyNK2 (12 * u) :=
        dicksonFamilyK2_n_eq_closed (12 * u)
    _ = dicksonAP3NK2 u :=
        (dicksonAP3NK2_eq_dicksonFamilyNK2 u).symm

theorem dicksonAP12ClosedForms_left_product_eq_n_add_one (u : ℕ) :
    dicksonP1K2 (12 * u) * dicksonQ1K2 (12 * u) =
      dicksonAP3NK2 u + 1 := by
  unfold dicksonP1K2 dicksonQ1K2 dicksonAP3NK2
  ring

theorem dicksonAP12ClosedForms_right_twice_product_eq_n_add_two (u : ℕ) :
    2 * (dicksonP2K2 (12 * u) * dicksonQ2K2 (12 * u)) =
      dicksonAP3NK2 u + 2 := by
  unfold dicksonP2K2 dicksonQ2K2 dicksonAP3NK2
  ring

def dicksonAP3LinearFormsK2 : List LinearFormK2 :=
  [{ coeff := 576, offset := 29 },
    { coeff := 912, offset := 65 },
    { coeff := 456, offset := 23 },
    { coeff := 576, offset := 41 }]

/--
Linear-form spelling of the unscaled tuple restricted to `m = 12u`.

The coefficients are deliberately written as products with `12` to make the
connection to `(48m+29, 76m+65, 38m+23, 48m+41)` explicit.
-/
def dicksonAP12LinearFormsK2 : List LinearFormK2 :=
  [{ coeff := 48 * 12, offset := 29 },
    { coeff := 76 * 12, offset := 65 },
    { coeff := 38 * 12, offset := 23 },
    { coeff := 48 * 12, offset := 41 }]

/--
The AP3-specific Dickson target left open by this development.

It asks for infinitely many parameters `u` for which the four displayed
linear forms are simultaneously prime.
-/
def DicksonAP3ConjectureK2 : Prop :=
  LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2

/--
The same AP3-specific target, stated as Dickson for the original tuple on the
progression `m = 12u`.
-/
def DicksonAP12ConjectureK2 : Prop :=
  LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2

/--
Closed-form spelling of the AP3-specific Dickson supply target.

This is the exact remaining infinitude theorem for the `m = 12u`
progression of the tuple `(48m+29, 76m+65, 38m+23, 48m+41)`.
-/
def DicksonAP3ClosedFormsSupplyK2 : Prop :=
  ∀ U : ℕ, ∃ u : ℕ,
    U ≤ u ∧
    Nat.Prime (576 * u + 29) ∧
    Nat.Prime (912 * u + 65) ∧
    Nat.Prime (456 * u + 23) ∧
    Nat.Prime (576 * u + 41)

def dicksonAP3PrefixBoundK2 (U : ℕ) : ℕ :=
  (Finset.range U).sum dicksonAP3NK2 + 1

theorem dicksonAP3NK2_ge_parameter (u : ℕ) :
    u ≤ dicksonAP3NK2 u := by
  unfold dicksonAP3NK2
  nlinarith [sq_nonneg (u : ℤ)]

theorem dicksonAP3NK2_lt_prefixBound_of_lt
    {u U : ℕ} (hu : u < U) :
    dicksonAP3NK2 u < dicksonAP3PrefixBoundK2 U := by
  unfold dicksonAP3PrefixBoundK2
  have hmem : u ∈ Finset.range U := Finset.mem_range.mpr hu
  have hle :
      dicksonAP3NK2 u ≤ (Finset.range U).sum dicksonAP3NK2 := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  exact Nat.lt_succ_of_le hle

theorem dicksonAP3_n_eq (u : ℕ) :
    (dicksonAP3RawQuadrupleK2 u).n = dicksonAP3NK2 u := by
  dsimp [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
    dicksonRawQuadrupleK2, FixedOneOneRawPrimeQuadrupleK2.n,
    dicksonP1K2, dicksonQ1K2, dicksonAP3NK2]
  have hprod :
      (48 * (4 * (3 * u)) + 29) * (76 * (4 * (3 * u)) + 65) =
        525312 * u ^ 2 + 63888 * u + 1885 := by
    ring
  rw [hprod]
  omega

theorem dicksonAP3K2_q2_eq_p1_add_twelve (u : ℕ) :
    dicksonAP3Q2K2 u = dicksonAP3P1K2 u + 12 := by
  unfold dicksonAP3Q2K2 dicksonAP3P1K2
  ring

theorem dicksonAP3RawQuadrupleK2_closed (u : ℕ) :
    (dicksonAP3RawQuadrupleK2 u).left.p = dicksonAP3P1K2 u ∧
    (dicksonAP3RawQuadrupleK2 u).left.q = dicksonAP3Q1K2 u ∧
    (dicksonAP3RawQuadrupleK2 u).right.p = dicksonAP3P2K2 u ∧
    (dicksonAP3RawQuadrupleK2 u).right.q = dicksonAP3Q2K2 u := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dicksonAP3RawQuadrupleK2 dicksonAPRawQuadrupleK2
      dicksonRawQuadrupleK2 dicksonP1K2 dicksonAP3P1K2
    ring
  · unfold dicksonAP3RawQuadrupleK2 dicksonAPRawQuadrupleK2
      dicksonRawQuadrupleK2 dicksonQ1K2 dicksonAP3Q1K2
    ring
  · unfold dicksonAP3RawQuadrupleK2 dicksonAPRawQuadrupleK2
      dicksonRawQuadrupleK2 dicksonP2K2 dicksonAP3P2K2
    ring
  · unfold dicksonAP3RawQuadrupleK2 dicksonAPRawQuadrupleK2
      dicksonRawQuadrupleK2 dicksonQ2K2 dicksonAP3Q2K2
    ring

def dicksonAP3ParamsK2 (u : ℕ) (hu : 1 ≤ u) : K2Params :=
  { x := (dicksonAP3RawQuadrupleK2 u).n
    P0 := 3
    pLo := 455 * u + 22
    pHi := 912 * u + 65
    qLo := 455 * u + 22
    qHi := 912 * u + 65
    sMax := 4
    x_ge_2 := by
      rw [dicksonAP3_n_eq]
      unfold dicksonAP3NK2
      nlinarith [sq_nonneg (u : ℤ), hu]
    P0_ge_3 := by norm_num
    sMax_lt_pLo := by omega
    P0_lt_sMax := by norm_num
    four_lt_pLo := by omega
    four_lt_qLo := by omega
    qHi_sq_le_two_x := by
      rw [dicksonAP3_n_eq]
      unfold dicksonAP3NK2
      nlinarith [sq_nonneg (u : ℤ), hu]
    four_x_lt_pLo_cube := by
      rw [dicksonAP3_n_eq]
      unfold dicksonAP3NK2
      nlinarith [sq_nonneg (u : ℤ), hu] }

theorem dicksonAP3_finiteSmallOdd
    {u : ℕ} (hu : 1 ≤ u) :
    FiniteSmallOddK2 (dicksonAP3ParamsK2 u hu)
      (dicksonAP3RawQuadrupleK2 u).n := by
  intro r hrange hrprime hrne_two
  rw [dicksonAP3_n_eq]
  unfold dicksonAP3NK2
  have hr_le : r ≤ 3 := (Finset.mem_Icc.mp hrange).2
  have hr_two_le : 2 ≤ r := hrprime.two_le
  have hcases : r = 2 ∨ r = 3 := by omega
  rcases hcases with htwo | hthree
  · exact False.elim (hrne_two htwo)
  · subst r
    exact ⟨175104 * u ^ 2 + 21296 * u + 628, by ring⟩

theorem dicksonAP3_finiteMediumHygiene
    {u : ℕ} (hu : 1 ≤ u) :
    FiniteMediumHygieneK2 (dicksonAP3ParamsK2 u hu)
      (dicksonAP3RawQuadrupleK2 u).n := by
  intro r hrange hrprime
  have hr_ge : 4 ≤ r := (Finset.mem_Icc.mp hrange).1
  have hr_le : r ≤ 4 := (Finset.mem_Icc.mp hrange).2
  have hr_eq : r = 4 := by omega
  subst r
  norm_num at hrprime

def DicksonAP3PrimeSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ u : ℕ,
    N ≤ (dicksonAP3RawQuadrupleK2 u).n ∧
    1 ≤ u ∧
    Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.p ∧
    Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.q ∧
    Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.p ∧
    Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.q

/--
Closed-form version of the remaining Dickson-prime supply target.

This is a restatement of `DicksonAP3PrimeSupplyK2` for the four explicit
linear forms `576u+29`, `912u+65`, `456u+23`, and `576u+41`.
-/
def DicksonAP3ClosedPrimeSupplyK2 : Prop :=
  ∀ N : ℕ, ∃ u : ℕ,
    N ≤ dicksonAP3NK2 u ∧
    1 ≤ u ∧
    Nat.Prime (dicksonAP3P1K2 u) ∧
    Nat.Prime (dicksonAP3Q1K2 u) ∧
    Nat.Prime (dicksonAP3P2K2 u) ∧
    Nat.Prime (dicksonAP3Q2K2 u)

/--
Qualitative Dickson-prime-tuple form for the AP3 tuple.

This is the natural parameter-unbounded statement: for every lower bound on
`u`, the four explicit linear forms are simultaneously prime.
-/
def DicksonAP3QualitativePrimeTupleK2 : Prop :=
  ∀ U : ℕ, ∃ u : ℕ,
    U ≤ u ∧
    1 ≤ u ∧
    Nat.Prime (dicksonAP3P1K2 u) ∧
    Nat.Prime (dicksonAP3Q1K2 u) ∧
    Nat.Prime (dicksonAP3P2K2 u) ∧
    Nat.Prime (dicksonAP3Q2K2 u)

theorem dicksonAP3ClosedPrimeSupply_of_qualitative
    (hSupply : DicksonAP3QualitativePrimeTupleK2) :
    DicksonAP3ClosedPrimeSupplyK2 := by
  intro N
  rcases hSupply N with ⟨u, hNu, hu, hp1, hq1, hp2, hq2⟩
  exact ⟨u, le_trans hNu (dicksonAP3NK2_ge_parameter u),
    hu, hp1, hq1, hp2, hq2⟩

theorem dicksonAP3QualitativePrimeTuple_of_closedSupply
    (hSupply : DicksonAP3ClosedPrimeSupplyK2) :
    DicksonAP3QualitativePrimeTupleK2 := by
  intro U
  rcases hSupply (dicksonAP3PrefixBoundK2 U) with
    ⟨u, hN, hu1, hp1, hq1, hp2, hq2⟩
  have hU : U ≤ u := by
    by_contra hnot
    have hlt : u < U := Nat.lt_of_not_ge hnot
    have hsmall :
        dicksonAP3NK2 u < dicksonAP3PrefixBoundK2 U :=
      dicksonAP3NK2_lt_prefixBound_of_lt hlt
    exact (Nat.not_lt_of_ge hN) hsmall
  exact ⟨u, hU, hu1, hp1, hq1, hp2, hq2⟩

theorem dicksonAP3ClosedPrimeSupply_iff_qualitative :
    DicksonAP3ClosedPrimeSupplyK2 ↔
      DicksonAP3QualitativePrimeTupleK2 := by
  constructor
  · exact dicksonAP3QualitativePrimeTuple_of_closedSupply
  · exact dicksonAP3ClosedPrimeSupply_of_qualitative

theorem dicksonAP3QualitativePrimeTuple_iff_linearForms :
    DicksonAP3QualitativePrimeTupleK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 := by
  constructor
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, _hu1, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_⟩
    intro L hL
    have hCases :
        L = { coeff := 576, offset := 29 } ∨
        L = { coeff := 912, offset := 65 } ∨
        L = { coeff := 456, offset := 23 } ∨
        L = { coeff := 576, offset := 41 } := by
      simpa [dicksonAP3LinearFormsK2] using hL
    rcases hCases with rfl | rfl | rfl | rfl
    · simpa [LinearFormK2.eval, dicksonAP3P1K2] using hp1
    · simpa [LinearFormK2.eval, dicksonAP3Q1K2] using hq1
    · simpa [LinearFormK2.eval, dicksonAP3P2K2] using hp2
    · simpa [LinearFormK2.eval, dicksonAP3Q2K2] using hq2
  · intro hSupply U
    rcases hSupply (max U 1) with ⟨u, hmax, hprime⟩
    have hU : U ≤ u := le_trans (le_max_left U 1) hmax
    have hu1 : 1 ≤ u := le_trans (le_max_right U 1) hmax
    have hp1 : Nat.Prime (dicksonAP3P1K2 u) := by
      have hmem :
          ({ coeff := 576, offset := 29 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP3P1K2]
        using hprime { coeff := 576, offset := 29 } hmem
    have hq1 : Nat.Prime (dicksonAP3Q1K2 u) := by
      have hmem :
          ({ coeff := 912, offset := 65 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP3Q1K2]
        using hprime { coeff := 912, offset := 65 } hmem
    have hp2 : Nat.Prime (dicksonAP3P2K2 u) := by
      have hmem :
          ({ coeff := 456, offset := 23 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP3P2K2]
        using hprime { coeff := 456, offset := 23 } hmem
    have hq2 : Nat.Prime (dicksonAP3Q2K2 u) := by
      have hmem :
          ({ coeff := 576, offset := 41 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval, dicksonAP3Q2K2]
        using hprime { coeff := 576, offset := 41 } hmem
    exact ⟨u, hU, hu1, hp1, hq1, hp2, hq2⟩

theorem dicksonAP3Conjecture_iff_qualitative :
    DicksonAP3ConjectureK2 ↔ DicksonAP3QualitativePrimeTupleK2 := by
  simpa [DicksonAP3ConjectureK2]
    using (dicksonAP3QualitativePrimeTuple_iff_linearForms).symm

theorem dicksonAP3Conjecture_iff_closedForms :
    DicksonAP3ConjectureK2 ↔
      ∀ U : ℕ, ∃ u : ℕ,
        U ≤ u ∧
        Nat.Prime (576 * u + 29) ∧
        Nat.Prime (912 * u + 65) ∧
        Nat.Prime (456 * u + 23) ∧
        Nat.Prime (576 * u + 41) := by
  constructor
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hprime⟩
    have hp1 : Nat.Prime (576 * u + 29) := by
      have hmem :
          ({ coeff := 576, offset := 29 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval]
        using hprime { coeff := 576, offset := 29 } hmem
    have hq1 : Nat.Prime (912 * u + 65) := by
      have hmem :
          ({ coeff := 912, offset := 65 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval]
        using hprime { coeff := 912, offset := 65 } hmem
    have hp2 : Nat.Prime (456 * u + 23) := by
      have hmem :
          ({ coeff := 456, offset := 23 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval]
        using hprime { coeff := 456, offset := 23 } hmem
    have hq2 : Nat.Prime (576 * u + 41) := by
      have hmem :
          ({ coeff := 576, offset := 41 } : LinearFormK2) ∈
            dicksonAP3LinearFormsK2 := by
        simp [dicksonAP3LinearFormsK2]
      simpa [LinearFormK2.eval]
        using hprime { coeff := 576, offset := 41 } hmem
    exact ⟨u, hU, hp1, hq1, hp2, hq2⟩
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_⟩
    intro L hL
    have hCases :
        L = { coeff := 576, offset := 29 } ∨
        L = { coeff := 912, offset := 65 } ∨
        L = { coeff := 456, offset := 23 } ∨
        L = { coeff := 576, offset := 41 } := by
      simpa [dicksonAP3LinearFormsK2] using hL
    rcases hCases with rfl | rfl | rfl | rfl
    · simpa [LinearFormK2.eval] using hp1
    · simpa [LinearFormK2.eval] using hq1
    · simpa [LinearFormK2.eval] using hp2
    · simpa [LinearFormK2.eval] using hq2

theorem dicksonAP3ClosedFormsSupply_iff_conjecture :
    DicksonAP3ClosedFormsSupplyK2 ↔ DicksonAP3ConjectureK2 := by
  simpa [DicksonAP3ClosedFormsSupplyK2]
    using (dicksonAP3Conjecture_iff_closedForms).symm

theorem dicksonAP3Conjecture_iff_linearFormsPrimeTuple :
    DicksonAP3ConjectureK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 := by
  rfl

theorem dicksonAP3LinearFormsPrimeTuple_of_dicksonAP3Conjecture
    (hSupply : DicksonAP3ConjectureK2) :
    LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 :=
  (dicksonAP3Conjecture_iff_linearFormsPrimeTuple).1 hSupply

theorem dicksonAP3Conjecture_of_dicksonAP3LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2) :
    DicksonAP3ConjectureK2 :=
  (dicksonAP3Conjecture_iff_linearFormsPrimeTuple).2 hSupply

theorem dicksonAP3ClosedFormsSupply_iff_linearFormsPrimeTuple :
    DicksonAP3ClosedFormsSupplyK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 := by
  calc
    DicksonAP3ClosedFormsSupplyK2 ↔ DicksonAP3ConjectureK2 :=
      dicksonAP3ClosedFormsSupply_iff_conjecture
    _ ↔ LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 :=
      dicksonAP3Conjecture_iff_linearFormsPrimeTuple

theorem dicksonAP3LinearFormsPrimeTuple_of_dicksonAP3ClosedFormsSupply
    (hSupply : DicksonAP3ClosedFormsSupplyK2) :
    LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2 :=
  (dicksonAP3ClosedFormsSupply_iff_linearFormsPrimeTuple).1 hSupply

theorem dicksonAP3ClosedFormsSupply_of_dicksonAP3LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2) :
    DicksonAP3ClosedFormsSupplyK2 :=
  (dicksonAP3ClosedFormsSupply_iff_linearFormsPrimeTuple).2 hSupply

theorem dicksonAP3ClosedFormsSupply_of_dicksonAP3Conjecture
    (hSupply : DicksonAP3ConjectureK2) :
    DicksonAP3ClosedFormsSupplyK2 :=
  (dicksonAP3ClosedFormsSupply_iff_conjecture).2 hSupply

theorem dicksonAP3Conjecture_of_dicksonAP3ClosedFormsSupply
    (hSupply : DicksonAP3ClosedFormsSupplyK2) :
    DicksonAP3ConjectureK2 :=
  (dicksonAP3ClosedFormsSupply_iff_conjecture).1 hSupply

theorem dicksonAP12ClosedFormsSupply_iff_AP3ClosedFormsSupply :
    DicksonAP12ClosedFormsSupplyK2 ↔ DicksonAP3ClosedFormsSupplyK2 := by
  constructor
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_, ?_, ?_, ?_⟩
    · convert hp1 using 1
      unfold dicksonP1K2
      ring
    · convert hq1 using 1
      unfold dicksonQ1K2
      ring
    · convert hp2 using 1
      unfold dicksonP2K2
      ring
    · convert hq2 using 1
      unfold dicksonQ2K2
      ring
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_, ?_, ?_, ?_⟩
    · convert hp1 using 1
      unfold dicksonP1K2
      ring
    · convert hq1 using 1
      unfold dicksonQ1K2
      ring
    · convert hp2 using 1
      unfold dicksonP2K2
      ring
    · convert hq2 using 1
      unfold dicksonQ2K2
      ring

theorem dicksonAP3ClosedFormsSupply_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    DicksonAP3ClosedFormsSupplyK2 :=
  (dicksonAP12ClosedFormsSupply_iff_AP3ClosedFormsSupply).1 hSupply

theorem dicksonAP12ClosedFormsSupply_of_dicksonAP3ClosedFormsSupply
    (hSupply : DicksonAP3ClosedFormsSupplyK2) :
    DicksonAP12ClosedFormsSupplyK2 :=
  (dicksonAP12ClosedFormsSupply_iff_AP3ClosedFormsSupply).2 hSupply

theorem dicksonAP12LinearForms_eq_AP3 :
    dicksonAP12LinearFormsK2 = dicksonAP3LinearFormsK2 := by
  norm_num [dicksonAP12LinearFormsK2, dicksonAP3LinearFormsK2]

theorem dicksonAP12Conjecture_iff_AP3Conjecture :
    DicksonAP12ConjectureK2 ↔ DicksonAP3ConjectureK2 := by
  rw [DicksonAP12ConjectureK2, DicksonAP3ConjectureK2,
    dicksonAP12LinearForms_eq_AP3]

theorem dicksonAP12Conjecture_iff_closedFormsSupply :
    DicksonAP12ConjectureK2 ↔ DicksonAP12ClosedFormsSupplyK2 := by
  rw [dicksonAP12Conjecture_iff_AP3Conjecture,
    ← dicksonAP3ClosedFormsSupply_iff_conjecture,
    ← dicksonAP12ClosedFormsSupply_iff_AP3ClosedFormsSupply]

theorem dicksonAP12Conjecture_iff_closedForms :
    DicksonAP12ConjectureK2 ↔
      ∀ U : ℕ, ∃ u : ℕ,
        U ≤ u ∧
        Nat.Prime (dicksonP1K2 (12 * u)) ∧
        Nat.Prime (dicksonQ1K2 (12 * u)) ∧
        Nat.Prime (dicksonP2K2 (12 * u)) ∧
        Nat.Prime (dicksonQ2K2 (12 * u)) := by
  simpa [DicksonAP12ClosedFormsSupplyK2]
    using dicksonAP12Conjecture_iff_closedFormsSupply

theorem dicksonAP12ClosedFormsSupply_iff_linearFormsPrimeTuple :
    DicksonAP12ClosedFormsSupplyK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 := by
  calc
    DicksonAP12ClosedFormsSupplyK2 ↔ DicksonAP12ConjectureK2 :=
      (dicksonAP12Conjecture_iff_closedFormsSupply).symm
    _ ↔ LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 :=
      Iff.rfl

theorem dicksonAP12LinearFormsPrimeTuple_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 :=
  (dicksonAP12ClosedFormsSupply_iff_linearFormsPrimeTuple).1 hSupply

theorem dicksonAP12ClosedFormsSupply_of_dicksonAP12LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2) :
    DicksonAP12ClosedFormsSupplyK2 :=
  (dicksonAP12ClosedFormsSupply_iff_linearFormsPrimeTuple).2 hSupply

theorem explicitDicksonAP12PrimeTupleSupply_iff_closedFormsSupply :
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔
      DicksonAP12ClosedFormsSupplyK2 := by
  constructor
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonP1K2] using hp1
    · simpa [dicksonQ1K2] using hq1
    · simpa [dicksonP2K2] using hp2
    · simpa [dicksonQ2K2] using hq2
  · intro hSupply U
    rcases hSupply U with ⟨u, hU, hp1, hq1, hp2, hq2⟩
    refine ⟨u, hU, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonP1K2] using hp1
    · simpa [dicksonQ1K2] using hq1
    · simpa [dicksonP2K2] using hp2
    · simpa [dicksonQ2K2] using hq2

theorem explicitDicksonAP12PrimeTupleSupply_iff_linearFormsPrimeTuple :
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 := by
  calc
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔
        DicksonAP12ClosedFormsSupplyK2 :=
      explicitDicksonAP12PrimeTupleSupply_iff_closedFormsSupply
    _ ↔ LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 :=
      dicksonAP12ClosedFormsSupply_iff_linearFormsPrimeTuple

theorem explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP12Conjecture :
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔
      DicksonAP12ConjectureK2 := by
  calc
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔
        LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 :=
      explicitDicksonAP12PrimeTupleSupply_iff_linearFormsPrimeTuple
    _ ↔ DicksonAP12ConjectureK2 :=
      Iff.rfl

theorem explicitDicksonAP12PrimeTupleSupply_of_dicksonAP12Conjecture
    (hSupply : DicksonAP12ConjectureK2) :
    ExplicitDicksonAP12PrimeTupleSupplyK2 :=
  (explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP12Conjecture).2 hSupply

theorem dicksonAP12Conjecture_of_explicitDicksonAP12PrimeTupleSupply
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    DicksonAP12ConjectureK2 :=
  (explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP12Conjecture).1 hSupply

theorem explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP3Conjecture :
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔ DicksonAP3ConjectureK2 := by
  calc
    ExplicitDicksonAP12PrimeTupleSupplyK2 ↔ DicksonAP12ConjectureK2 :=
      explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP12Conjecture
    _ ↔ DicksonAP3ConjectureK2 :=
      dicksonAP12Conjecture_iff_AP3Conjecture

theorem explicitDicksonAP12PrimeTupleSupply_of_dicksonAP3Conjecture
    (hSupply : DicksonAP3ConjectureK2) :
    ExplicitDicksonAP12PrimeTupleSupplyK2 :=
  (explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP3Conjecture).2 hSupply

theorem dicksonAP3Conjecture_of_explicitDicksonAP12PrimeTupleSupply
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    DicksonAP3ConjectureK2 :=
  (explicitDicksonAP12PrimeTupleSupply_iff_dicksonAP3Conjecture).1 hSupply

theorem dicksonAP12Conjecture_iff_linearFormsPrimeTuple :
    DicksonAP12ConjectureK2 ↔
      LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 := by
  rfl

theorem dicksonAP12LinearFormsPrimeTuple_of_dicksonAP12Conjecture
    (hSupply : DicksonAP12ConjectureK2) :
    LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2 :=
  (dicksonAP12Conjecture_iff_linearFormsPrimeTuple).1 hSupply

theorem dicksonAP12Conjecture_of_dicksonAP12LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2) :
    DicksonAP12ConjectureK2 :=
  (dicksonAP12Conjecture_iff_linearFormsPrimeTuple).2 hSupply

theorem dicksonAP12ClosedFormsSupply_of_dicksonAP12Conjecture
    (hSupply : DicksonAP12ConjectureK2) :
    DicksonAP12ClosedFormsSupplyK2 :=
  (dicksonAP12Conjecture_iff_closedFormsSupply).1 hSupply

theorem dicksonAP12Conjecture_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    DicksonAP12ConjectureK2 :=
  (dicksonAP12Conjecture_iff_closedFormsSupply).2 hSupply

theorem dicksonAP3PrimeSupply_iff_closed :
    DicksonAP3PrimeSupplyK2 ↔ DicksonAP3ClosedPrimeSupplyK2 := by
  constructor
  · intro hSupply N
    rcases hSupply N with ⟨u, hN, hu, hp1, hq1, hp2, hq2⟩
    rcases dicksonAP3RawQuadrupleK2_closed u with
      ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
    refine ⟨u, ?_, hu, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonAP3_n_eq] using hN
    · simpa [hp1eq] using hp1
    · simpa [hq1eq] using hq1
    · simpa [hp2eq] using hp2
    · simpa [hq2eq] using hq2
  · intro hSupply N
    rcases hSupply N with ⟨u, hN, hu, hp1, hq1, hp2, hq2⟩
    rcases dicksonAP3RawQuadrupleK2_closed u with
      ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
    refine ⟨u, ?_, hu, ?_, ?_, ?_, ?_⟩
    · simpa [dicksonAP3_n_eq] using hN
    · simpa [hp1eq] using hp1
    · simpa [hq1eq] using hq1
    · simpa [hp2eq] using hp2
    · simpa [hq2eq] using hq2

theorem dicksonAP3PrimeSupply_of_dicksonAP4PrimeSupply
    (hSupply : DicksonAP4PrimeSupplyK2) :
    DicksonAP3PrimeSupplyK2 := by
  intro N
  rcases hSupply N with ⟨t, hN, ht, hp1, hq1, hp2, hq2⟩
  rcases three_dvd_t_of_dicksonAP4_primes hq1 hp2 with ⟨u, rfl⟩
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [dicksonAP3RawQuadrupleK2] using hN
  · omega
  · simpa [dicksonAP3RawQuadrupleK2] using hp1
  · simpa [dicksonAP3RawQuadrupleK2] using hq1
  · simpa [dicksonAP3RawQuadrupleK2] using hp2
  · simpa [dicksonAP3RawQuadrupleK2] using hq2

theorem dicksonAP4PrimeSupply_of_dicksonAP3PrimeSupply
    (hSupply : DicksonAP3PrimeSupplyK2) :
    DicksonAP4PrimeSupplyK2 := by
  intro N
  rcases hSupply N with ⟨u, hN, hu, hp1, hq1, hp2, hq2⟩
  refine ⟨3 * u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [dicksonAP3RawQuadrupleK2] using hN
  · omega
  · simpa [dicksonAP3RawQuadrupleK2] using hp1
  · simpa [dicksonAP3RawQuadrupleK2] using hq1
  · simpa [dicksonAP3RawQuadrupleK2] using hp2
  · simpa [dicksonAP3RawQuadrupleK2] using hq2

theorem dicksonAP4PrimeSupply_iff_AP3PrimeSupply :
    DicksonAP4PrimeSupplyK2 ↔ DicksonAP3PrimeSupplyK2 := by
  constructor
  · exact dicksonAP3PrimeSupply_of_dicksonAP4PrimeSupply
  · exact dicksonAP4PrimeSupply_of_dicksonAP3PrimeSupply

def dicksonAP3FamilyLocalGoodK2 (r u : ℕ) : Prop :=
  ¬ r ∣ (dicksonAP3RawQuadrupleK2 u).left.p ∧
  ¬ r ∣ (dicksonAP3RawQuadrupleK2 u).left.q ∧
  ¬ r ∣ (dicksonAP3RawQuadrupleK2 u).right.p ∧
  ¬ r ∣ (dicksonAP3RawQuadrupleK2 u).right.q

def dicksonAP3ClosedFamilyLocalGoodK2 (r u : ℕ) : Prop :=
  ¬ r ∣ dicksonAP3P1K2 u ∧
  ¬ r ∣ dicksonAP3Q1K2 u ∧
  ¬ r ∣ dicksonAP3P2K2 u ∧
  ¬ r ∣ dicksonAP3Q2K2 u

theorem dicksonAP3ClosedFamilyLocalGoodK2_iff_raw
    (r u : ℕ) :
    dicksonAP3ClosedFamilyLocalGoodK2 r u ↔
      dicksonAP3FamilyLocalGoodK2 r u := by
  rcases dicksonAP3RawQuadrupleK2_closed u with
    ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
  unfold dicksonAP3ClosedFamilyLocalGoodK2
    dicksonAP3FamilyLocalGoodK2
  simp [hp1eq, hq1eq, hp2eq, hq2eq]

theorem dicksonAP3FamilyLocalGoodK2_at_zero
    {r : ℕ} (hr : Nat.Prime r)
    (h5 : r ≠ 5) (h13 : r ≠ 13) (h23 : r ≠ 23)
    (h29 : r ≠ 29) (h41 : r ≠ 41) :
    dicksonAP3FamilyLocalGoodK2 r 0 := by
  unfold dicksonAP3FamilyLocalGoodK2 dicksonAP3RawQuadrupleK2
    dicksonAPRawQuadrupleK2 dicksonRawQuadrupleK2 dicksonP1K2
    dicksonQ1K2 dicksonP2K2 dicksonQ2K2
  norm_num
  constructor
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 29) h29
  constructor
  · intro hdiv
    rcases prime_dvd_65_cases hr hdiv with h_eq | h_eq
    · exact h5 h_eq
    · exact h13 h_eq
  constructor
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 23) h23
  · exact prime_not_dvd_prime_const hr (by norm_num : Nat.Prime 41) h41

theorem dicksonAP3FamilyLocalGoodK2_exceptional :
    dicksonAP3FamilyLocalGoodK2 5 3 ∧
    dicksonAP3FamilyLocalGoodK2 13 1 ∧
    dicksonAP3FamilyLocalGoodK2 23 1 ∧
    dicksonAP3FamilyLocalGoodK2 29 1 ∧
    dicksonAP3FamilyLocalGoodK2 41 1 := by
  norm_num [dicksonAP3FamilyLocalGoodK2, dicksonAP3RawQuadrupleK2,
    dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2, dicksonP1K2,
    dicksonQ1K2, dicksonP2K2, dicksonQ2K2]

theorem dicksonAP3Family_admissible :
    ∀ r : ℕ, Nat.Prime r → ∃ u : ℕ,
      dicksonAP3FamilyLocalGoodK2 r u := by
  intro r hr
  rcases dicksonAP3FamilyLocalGoodK2_exceptional with
    ⟨h5Good, h13Good, h23Good, h29Good, h41Good⟩
  by_cases h5 : r = 5
  · subst r
    exact ⟨3, h5Good⟩
  by_cases h13 : r = 13
  · subst r
    exact ⟨1, h13Good⟩
  by_cases h23 : r = 23
  · subst r
    exact ⟨1, h23Good⟩
  by_cases h29 : r = 29
  · subst r
    exact ⟨1, h29Good⟩
  by_cases h41 : r = 41
  · subst r
    exact ⟨1, h41Good⟩
  exact ⟨0, dicksonAP3FamilyLocalGoodK2_at_zero
    hr h5 h13 h23 h29 h41⟩

theorem dicksonAP3ClosedFamily_admissible :
    ∀ r : ℕ, Nat.Prime r → ∃ u : ℕ,
      dicksonAP3ClosedFamilyLocalGoodK2 r u := by
  intro r hr
  rcases dicksonAP3Family_admissible r hr with ⟨u, hraw⟩
  exact ⟨u, (dicksonAP3ClosedFamilyLocalGoodK2_iff_raw r u).2 hraw⟩

theorem dicksonAP3ClosedForms_locallyAdmissible :
    ∀ r : ℕ, Nat.Prime r → ∃ u : ℕ,
      ¬ r ∣ 576 * u + 29 ∧
      ¬ r ∣ 912 * u + 65 ∧
      ¬ r ∣ 456 * u + 23 ∧
      ¬ r ∣ 576 * u + 41 := by
  intro r hr
  rcases dicksonAP3ClosedFamily_admissible r hr with ⟨u, hgood⟩
  refine ⟨u, ?_⟩
  simpa [dicksonAP3ClosedFamilyLocalGoodK2, dicksonAP3P1K2,
    dicksonAP3Q1K2, dicksonAP3P2K2, dicksonAP3Q2K2] using hgood

theorem dicksonAP12ClosedForms_locallyAdmissible :
    ∀ r : ℕ, Nat.Prime r → ∃ u : ℕ,
      ¬ r ∣ dicksonP1K2 (12 * u) ∧
      ¬ r ∣ dicksonQ1K2 (12 * u) ∧
      ¬ r ∣ dicksonP2K2 (12 * u) ∧
      ¬ r ∣ dicksonQ2K2 (12 * u) := by
  intro r hr
  rcases dicksonAP3ClosedForms_locallyAdmissible r hr with
    ⟨u, hp1, hq1, hp2, hq2⟩
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · have hEq : dicksonP1K2 (12 * u) = 576 * u + 29 := by
      unfold dicksonP1K2
      ring
    simpa [hEq] using hp1
  · have hEq : dicksonQ1K2 (12 * u) = 912 * u + 65 := by
      unfold dicksonQ1K2
      ring
    simpa [hEq] using hq1
  · have hEq : dicksonP2K2 (12 * u) = 456 * u + 23 := by
      unfold dicksonP2K2
      ring
    simpa [hEq] using hp2
  · have hEq : dicksonQ2K2 (12 * u) = 576 * u + 41 := by
      unfold dicksonQ2K2
      ring
    simpa [hEq] using hq2

theorem dicksonAP3LinearForms_admissible :
    LinearFormsLocallyAdmissibleK2 dicksonAP3LinearFormsK2 := by
  intro r hr
  rcases dicksonAP3ClosedFamily_admissible r hr with ⟨u, hgood⟩
  unfold dicksonAP3ClosedFamilyLocalGoodK2 at hgood
  rcases hgood with ⟨hp1, hq1, hp2, hq2⟩
  refine ⟨u, ?_⟩
  intro L hL
  have hCases :
      L = { coeff := 576, offset := 29 } ∨
      L = { coeff := 912, offset := 65 } ∨
      L = { coeff := 456, offset := 23 } ∨
      L = { coeff := 576, offset := 41 } := by
    simpa [dicksonAP3LinearFormsK2] using hL
  rcases hCases with rfl | rfl | rfl | rfl
  · simpa [LinearFormK2.eval, dicksonAP3P1K2] using hp1
  · simpa [LinearFormK2.eval, dicksonAP3Q1K2] using hq1
  · simpa [LinearFormK2.eval, dicksonAP3P2K2] using hp2
  · simpa [LinearFormK2.eval, dicksonAP3Q2K2] using hq2

theorem dicksonAP12LinearForms_admissible :
    LinearFormsLocallyAdmissibleK2 dicksonAP12LinearFormsK2 := by
  simpa [dicksonAP12LinearForms_eq_AP3]
    using dicksonAP3LinearForms_admissible

theorem dicksonAP3Conjecture_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP3ConjectureK2 :=
  hDickson dicksonAP3LinearFormsK2 dicksonAP3LinearForms_admissible

theorem dicksonAP12Conjecture_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP12ConjectureK2 :=
  hDickson dicksonAP12LinearFormsK2 dicksonAP12LinearForms_admissible

theorem explicitDicksonAP12PrimeTupleSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    ExplicitDicksonAP12PrimeTupleSupplyK2 :=
  explicitDicksonAP12PrimeTupleSupply_of_dicksonAP12Conjecture
    (dicksonAP12Conjecture_of_dicksonConjectureK2 hDickson)

theorem explicitDicksonMod12PrimeTupleSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    ExplicitDicksonMod12PrimeTupleSupplyK2 :=
  explicitDicksonMod12PrimeTupleSupply_of_AP12
    (explicitDicksonAP12PrimeTupleSupply_of_dicksonConjectureK2 hDickson)

theorem dicksonAP3ClosedForms_supply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    ∀ U : ℕ, ∃ u : ℕ,
      U ≤ u ∧
      Nat.Prime (576 * u + 29) ∧
      Nat.Prime (912 * u + 65) ∧
      Nat.Prime (456 * u + 23) ∧
      Nat.Prime (576 * u + 41) :=
  (dicksonAP3Conjecture_iff_closedForms).1
    (dicksonAP3Conjecture_of_dicksonConjectureK2 hDickson)

theorem dicksonAP3ClosedFormsSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP3ClosedFormsSupplyK2 :=
  (dicksonAP3ClosedFormsSupply_iff_conjecture).2
    (dicksonAP3Conjecture_of_dicksonConjectureK2 hDickson)

theorem dicksonAP12ClosedForms_supply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP12ClosedFormsSupplyK2 :=
  (dicksonAP12Conjecture_iff_closedFormsSupply).1
    (dicksonAP12Conjecture_of_dicksonConjectureK2 hDickson)

theorem dicksonAP12ClosedFormsSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    DicksonAP12ClosedFormsSupplyK2 :=
  dicksonAP12ClosedFormsSupply_of_dicksonAP12Conjecture
    (dicksonAP12Conjecture_of_dicksonConjectureK2 hDickson)

theorem dicksonAP3FamilyRawSideConditions_of_primes
    {u : ℕ} (hu : 1 ≤ u)
    (hp1 : Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.p)
    (hq1 : Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.q)
    (hp2 : Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.p)
    (hq2 : Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.q) :
    DicksonAPFamilyRawSideConditionsK2
      (dicksonAP3ParamsK2 u hu) (3 * u) := by
  unfold DicksonAPFamilyRawSideConditionsK2
  dsimp [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
    dicksonRawQuadrupleK2, dicksonAP3ParamsK2, SameLargePrimeBandK2,
    InBand, dicksonP1K2, dicksonQ1K2, dicksonP2K2, dicksonQ2K2]
  refine ⟨?_, ?_, ?_, ?_, ?_, hp1, hq1, hp2, hq2,
    ?_, ?_, ?_, ?_⟩
  · exact le_rfl
  · omega
  · exact ⟨rfl, rfl⟩
  · exact dicksonAP3_finiteSmallOdd hu
  · exact dicksonAP3_finiteMediumHygiene hu
  · omega
  · omega
  · omega
  · omega

theorem dicksonAPFamilySupply_of_dicksonAP3PrimeSupply
    (hSupply : DicksonAP3PrimeSupplyK2) :
    DicksonAPFamilySupplyK2 := by
  intro N
  rcases hSupply N with ⟨u, hN, hu, hp1, hq1, hp2, hq2⟩
  refine ⟨dicksonAP3ParamsK2 u hu, 3 * u, ?_, ?_, ?_⟩
  · simpa [dicksonAP3RawQuadrupleK2] using hN
  · omega
  · exact dicksonAP3FamilyRawSideConditions_of_primes
      hu hp1 hq1 hp2 hq2

theorem dicksonFamilyRawCleanRatioGood_of_sideConditions
    {cfg : K2Params} {m : ℕ}
    (hm : 4 ≤ m)
    (hSide : DicksonFamilyRawSideConditionsK2 cfg m) :
    FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg
      (dicksonRawQuadrupleK2 m) := by
  unfold DicksonFamilyRawSideConditionsK2 at hSide
  dsimp only [dicksonRawQuadrupleK2] at hSide ⊢
  rcases hSide with
    ⟨hxLo, hxHi, hmod, hSame, hSmall, hMedium,
      hp1, hq1, hp2, hq2, hp1Band, hq1Band, hp2Band, hq2Band⟩
  rcases dicksonFamilyK2_left_ratio (by omega : 1 ≤ m) with
    ⟨hleftOrder, hleftLo, hleftHi⟩
  rcases dicksonFamilyK2_right_ratio hm with
    ⟨hrightOrder, hrightLo, hrightHi⟩
  exact ⟨hxLo, hxHi, hmod, hSame, hSmall, hMedium,
    dicksonFamilyK2_equation m,
    hp1, hq1, hp2, hq2,
    hp1Band, hq1Band, hp2Band, hq2Band,
    hleftOrder, hleftLo, hleftHi,
    hrightOrder, hrightLo, hrightHi⟩

theorem dicksonFamilyRawSideConditions_twelve_dvd_parameter
    {cfg : K2Params} {m : ℕ}
    (hm : 4 ≤ m)
    (hSide : DicksonFamilyRawSideConditionsK2 cfg m) :
    12 ∣ m :=
  twelve_dvd_m_of_dicksonFamilyRawCleanRatioGood
    (dicksonFamilyRawCleanRatioGood_of_sideConditions hm hSide)

theorem dicksonAP12PrimesAt_of_dicksonFamilyRawSideConditions
    {cfg : K2Params} {m : ℕ}
    (hm : 4 ≤ m)
    (hSide : DicksonFamilyRawSideConditionsK2 cfg m) :
    ∃ u : ℕ,
      m = 12 * u ∧
      Nat.Prime (dicksonP1K2 (12 * u)) ∧
      Nat.Prime (dicksonQ1K2 (12 * u)) ∧
      Nat.Prime (dicksonP2K2 (12 * u)) ∧
      Nat.Prime (dicksonQ2K2 (12 * u)) := by
  have h12 : 12 ∣ m :=
    dicksonFamilyRawSideConditions_twelve_dvd_parameter hm hSide
  rcases h12 with ⟨u, hm_eq⟩
  unfold DicksonFamilyRawSideConditionsK2 at hSide
  dsimp only [dicksonRawQuadrupleK2] at hSide
  rcases hSide with
    ⟨_hxLo, _hxHi, _hmod, _hSame, _hSmall, _hMedium,
      hp1, hq1, hp2, hq2, _hp1Band, _hq1Band, _hp2Band, _hq2Band⟩
  refine ⟨u, hm_eq, ?_, ?_, ?_, ?_⟩
  · simpa [hm_eq] using hp1
  · simpa [hm_eq] using hq1
  · simpa [hm_eq] using hp2
  · simpa [hm_eq] using hq2

theorem dicksonAP12ClosedFormsSupply_of_dicksonFamilySupply
    (hSupply : DicksonFamilySupplyK2) :
    DicksonAP12ClosedFormsSupplyK2 := by
  intro U
  rcases hSupply (dicksonAP3PrefixBoundK2 U) with
    ⟨cfg, m, hN, hm, hSide⟩
  have h12 : 12 ∣ m :=
    dicksonFamilyRawSideConditions_twelve_dvd_parameter hm hSide
  rcases h12 with ⟨u, rfl⟩
  have hn_eq :
      (dicksonRawQuadrupleK2 (12 * u)).n = dicksonAP3NK2 u := by
    calc
      (dicksonRawQuadrupleK2 (12 * u)).n =
          (dicksonAP12RawQuadrupleK2 u).n := rfl
      _ = (dicksonAP3RawQuadrupleK2 u).n := by
        rw [dicksonAP12RawQuadrupleK2_eq_AP3]
      _ = dicksonAP3NK2 u := dicksonAP3_n_eq u
  have hN' : dicksonAP3PrefixBoundK2 U ≤ dicksonAP3NK2 u := by
    simpa [hn_eq] using hN
  have hU : U ≤ u := by
    by_contra hnot
    have hlt : u < U := Nat.lt_of_not_ge hnot
    have hsmall :
        dicksonAP3NK2 u < dicksonAP3PrefixBoundK2 U :=
      dicksonAP3NK2_lt_prefixBound_of_lt hlt
    exact (Nat.not_lt_of_ge hN') hsmall
  unfold DicksonFamilyRawSideConditionsK2 at hSide
  dsimp only [dicksonRawQuadrupleK2] at hSide
  rcases hSide with
    ⟨_hxLo, _hxHi, _hmod, _hSame, _hSmall, _hMedium,
      hp1, hq1, hp2, hq2, _hp1Band, _hq1Band, _hp2Band, _hq2Band⟩
  refine ⟨u, hU, ?_, ?_, ?_, ?_⟩
  · simpa [dicksonRawQuadrupleK2] using hp1
  · simpa [dicksonRawQuadrupleK2] using hq1
  · simpa [dicksonRawQuadrupleK2] using hp2
  · simpa [dicksonRawQuadrupleK2] using hq2

theorem dicksonFamilyRawSideConditions_of_dicksonAP12_primes
    {u : ℕ} (hu : 1 ≤ u)
    (hp1 : Nat.Prime (dicksonP1K2 (12 * u)))
    (hq1 : Nat.Prime (dicksonQ1K2 (12 * u)))
    (hp2 : Nat.Prime (dicksonP2K2 (12 * u)))
    (hq2 : Nat.Prime (dicksonQ2K2 (12 * u))) :
    DicksonFamilyRawSideConditionsK2
      (dicksonAP3ParamsK2 u hu) (12 * u) := by
  have hm_eq : 4 * (3 * u) = 12 * u := by ring
  have hp1raw : Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.p := by
    simpa [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      hm_eq, dicksonRawQuadrupleK2] using hp1
  have hq1raw : Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.q := by
    simpa [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      hm_eq, dicksonRawQuadrupleK2] using hq1
  have hp2raw : Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.p := by
    simpa [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      hm_eq, dicksonRawQuadrupleK2] using hp2
  have hq2raw : Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.q := by
    simpa [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      hm_eq, dicksonRawQuadrupleK2] using hq2
  have hAP : DicksonAPFamilyRawSideConditionsK2
      (dicksonAP3ParamsK2 u hu) (3 * u) :=
    dicksonAP3FamilyRawSideConditions_of_primes
      hu hp1raw hq1raw hp2raw hq2raw
  unfold DicksonAPFamilyRawSideConditionsK2 at hAP
  dsimp [dicksonAPRawQuadrupleK2] at hAP
  rcases hAP with
    ⟨hxLo, hxHi, hSame, hSmall, hMedium,
      hp1r, hq1r, hp2r, hq2r, hp1Band, hq1Band, hp2Band, hq2Band⟩
  unfold DicksonFamilyRawSideConditionsK2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa [hm_eq] using hxLo
  · simpa [hm_eq] using hxHi
  · have hmod : (12 * (12 * u) + 12) % 16 = 12 := by
      omega
    simpa [dicksonFamilyK2_n_mod16 (12 * u)] using hmod
  · simpa [hm_eq] using hSame
  · simpa [hm_eq] using hSmall
  · simpa [hm_eq] using hMedium
  · simpa [hm_eq] using hp1r
  · simpa [hm_eq] using hq1r
  · simpa [hm_eq] using hp2r
  · simpa [hm_eq] using hq2r
  · simpa [hm_eq] using hp1Band
  · simpa [hm_eq] using hq1Band
  · simpa [hm_eq] using hp2Band
  · simpa [hm_eq] using hq2Band

theorem dicksonFamilySupply_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    DicksonFamilySupplyK2 := by
  intro N
  rcases hSupply (max N 1) with ⟨u, hmax, hp1, hq1, hp2, hq2⟩
  have hNu : N ≤ u := le_trans (le_max_left N 1) hmax
  have hu : 1 ≤ u := le_trans (le_max_right N 1) hmax
  refine ⟨dicksonAP3ParamsK2 u hu, 12 * u, ?_, ?_, ?_⟩
  · have hraw_eq :
        (dicksonRawQuadrupleK2 (12 * u)).n = dicksonAP3NK2 u := by
      calc
        (dicksonRawQuadrupleK2 (12 * u)).n =
            (dicksonAP12RawQuadrupleK2 u).n := rfl
        _ = (dicksonAP3RawQuadrupleK2 u).n := by
          rw [dicksonAP12RawQuadrupleK2_eq_AP3]
        _ = dicksonAP3NK2 u := dicksonAP3_n_eq u
    exact le_trans hNu (by simpa [hraw_eq] using dicksonAP3NK2_ge_parameter u)
  · omega
  · exact dicksonFamilyRawSideConditions_of_dicksonAP12_primes
      hu hp1 hq1 hp2 hq2

theorem dicksonFamilySupply_iff_dicksonAP12ClosedFormsSupply :
    DicksonFamilySupplyK2 ↔ DicksonAP12ClosedFormsSupplyK2 := by
  constructor
  · exact dicksonAP12ClosedFormsSupply_of_dicksonFamilySupply
  · exact dicksonFamilySupply_of_dicksonAP12ClosedFormsSupply

theorem dicksonFamilySupply_iff_dicksonAP12Conjecture :
    DicksonFamilySupplyK2 ↔ DicksonAP12ConjectureK2 := by
  rw [dicksonFamilySupply_iff_dicksonAP12ClosedFormsSupply,
    dicksonAP12Conjecture_iff_closedFormsSupply]

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonFamilySupply
    (hSupply : DicksonFamilySupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, m, hN, hm, hSide⟩
  exact ⟨cfg, dicksonRawQuadrupleK2 m, hN,
    dicksonFamilyRawCleanRatioGood_of_sideConditions hm hSide⟩

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonFamilySupply
    (dicksonFamilySupply_of_dicksonAP12ClosedFormsSupply hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12Conjecture
    (hSupply : DicksonAP12ConjectureK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12ClosedFormsSupply
    ((dicksonAP12Conjecture_iff_closedFormsSupply).1 hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12Conjecture
    (dicksonAP12Conjecture_of_dicksonAP12LinearFormsPrimeTuple hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12ClosedForms
    (hSupply :
      ∀ U : ℕ, ∃ u : ℕ,
        U ≤ u ∧
        Nat.Prime (dicksonP1K2 (12 * u)) ∧
        Nat.Prime (dicksonQ1K2 (12 * u)) ∧
        Nat.Prime (dicksonP2K2 (12 * u)) ∧
        Nat.Prime (dicksonQ2K2 (12 * u))) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 := by
  have hClosed : DicksonAP12ClosedFormsSupplyK2 := by
    simpa [DicksonAP12ClosedFormsSupplyK2] using hSupply
  exact
    fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12ClosedFormsSupply
      hClosed

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_explicitDicksonAP12PrimeTupleSupply
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP12ClosedFormsSupply
    ((explicitDicksonAP12PrimeTupleSupply_iff_closedFormsSupply).1 hSupply)

theorem dicksonAPFamilyRawCleanRatioGood_of_sideConditions
    {cfg : K2Params} {t : ℕ}
    (ht : 1 ≤ t)
    (hSide : DicksonAPFamilyRawSideConditionsK2 cfg t) :
    FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg
      (dicksonAPRawQuadrupleK2 t) := by
  unfold DicksonAPFamilyRawSideConditionsK2 at hSide
  dsimp only [dicksonAPRawQuadrupleK2, dicksonRawQuadrupleK2] at hSide ⊢
  rcases hSide with
    ⟨hxLo, hxHi, hSame, hSmall, hMedium,
      hp1, hq1, hp2, hq2, hp1Band, hq1Band, hp2Band, hq2Band⟩
  rcases dicksonAPFamilyK2_left_ratio ht with
    ⟨hleftOrder, hleftLo, hleftHi⟩
  rcases dicksonAPFamilyK2_right_ratio ht with
    ⟨hrightOrder, hrightLo, hrightHi⟩
  exact ⟨hxLo, hxHi, dicksonAPFamilyK2_mod16 t,
    hSame, hSmall, hMedium,
    dicksonAPFamilyK2_equation t,
    hp1, hq1, hp2, hq2,
    hp1Band, hq1Band, hp2Band, hq2Band,
    hleftOrder, hleftLo, hleftHi,
    hrightOrder, hrightLo, hrightHi⟩

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAPFamilySupply
    (hSupply : DicksonAPFamilySupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, t, hN, ht, hSide⟩
  exact ⟨cfg, dicksonAPRawQuadrupleK2 t, hN,
    dicksonAPFamilyRawCleanRatioGood_of_sideConditions ht hSide⟩

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3PrimeSupply
    (hSupply : DicksonAP3PrimeSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAPFamilySupply
    (dicksonAPFamilySupply_of_dicksonAP3PrimeSupply hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3ClosedPrimeSupply
    (hSupply : DicksonAP3ClosedPrimeSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3PrimeSupply
    ((dicksonAP3PrimeSupply_iff_closed).2 hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3QualitativePrimeTuple
    (hSupply : DicksonAP3QualitativePrimeTupleK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3ClosedPrimeSupply
    (dicksonAP3ClosedPrimeSupply_of_qualitative hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3Conjecture
    (hSupply : DicksonAP3ConjectureK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3QualitativePrimeTuple
    ((dicksonAP3Conjecture_iff_qualitative).1 hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3ClosedFormsSupply
    (hSupply : DicksonAP3ClosedFormsSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3Conjecture
    ((dicksonAP3ClosedFormsSupply_iff_conjecture).1 hSupply)

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 :=
  fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAP3Conjecture
    (dicksonAP3Conjecture_of_dicksonConjectureK2 hDickson)

theorem switchedSBoxedSupplyWitness_of_affineCorrelationTuple
    {cfg : K2Params} {t : SBoxedAffineCorrelationTupleK2}
    (hCorr : SBoxedAffineCorrelationK2 cfg t) :
    SwitchedSBoxedSupplyWitnessK2 cfg t.n t.s1 t.s2 t.M1 t.M2 :=
  hCorr.1

theorem positiveSBoxedAffineCorrelationBox_of_positiveFixed
    {cfg : K2Params} {s1 s2 : ℕ}
    (hFixed : PositiveFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2) :
    PositiveSBoxedAffineCorrelationBoxK2 cfg := by
  unfold PositiveFixedSBoxedAffineCorrelationBoxK2
    fixedSBoxedAffineCorrelationCountK2 at hFixed
  unfold PositiveSBoxedAffineCorrelationBoxK2
    sBoxedAffineCorrelationCountK2
  rcases Finset.card_pos.mp hFixed with ⟨t, ht⟩
  unfold fixedSBoxedAffineCorrelationBoxK2 at ht
  exact Finset.card_pos.mpr ⟨t, (Finset.mem_filter.mp ht).1⟩

theorem positiveFixedSBoxedAffineCorrelationBox_of_positiveWeighted
    {cfg : K2Params} {s1 s2 : ℕ}
    (hWeighted :
      PositiveWeightedFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2) :
    PositiveFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2 := by
  unfold PositiveWeightedFixedSBoxedAffineCorrelationBoxK2 at hWeighted
  unfold PositiveFixedSBoxedAffineCorrelationBoxK2
    fixedSBoxedAffineCorrelationCountK2
  by_contra hnot
  have hcard :
      (fixedSBoxedAffineCorrelationBoxK2 cfg s1 s2).card = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hempty : fixedSBoxedAffineCorrelationBoxK2 cfg s1 s2 = ∅ :=
    Finset.card_eq_zero.mp hcard
  have hsum_zero :
      fixedSBoxedAffineCorrelationWeightedSumK2 cfg s1 s2 = 0 := by
    simp [fixedSBoxedAffineCorrelationWeightedSumK2, hempty]
  omega

theorem positiveSBoxedAffineCorrelationBox_of_positiveWeighted
    {cfg : K2Params}
    (hWeighted : PositiveWeightedSBoxedAffineCorrelationBoxK2 cfg) :
    PositiveSBoxedAffineCorrelationBoxK2 cfg := by
  unfold PositiveWeightedSBoxedAffineCorrelationBoxK2 at hWeighted
  unfold PositiveSBoxedAffineCorrelationBoxK2
    sBoxedAffineCorrelationCountK2
  by_contra hnot
  have hcard : (sBoxedAffineCorrelationBoxK2 cfg).card = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hempty : sBoxedAffineCorrelationBoxK2 cfg = ∅ :=
    Finset.card_eq_zero.mp hcard
  have hsum_zero : sBoxedAffineCorrelationWeightedSumK2 cfg = 0 := by
    simp [sBoxedAffineCorrelationWeightedSumK2, hempty]
  omega

theorem positiveSBoxedAffineCorrelationBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity : PositiveDensitySBoxedAffineCorrelationBoxK2 num den cfg) :
    PositiveSBoxedAffineCorrelationBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveSBoxedAffineCorrelationBoxK2
  by_contra hnot
  have hzero : sBoxedAffineCorrelationCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveFixedSBoxedAffineCorrelationBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params} {s1 s2 : ℕ}
    (hDensity :
      PositiveDensityFixedSBoxedAffineCorrelationBoxK2 num den cfg s1 s2) :
    PositiveFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2 := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveFixedSBoxedAffineCorrelationBoxK2
  by_contra hnot
  have hzero : fixedSBoxedAffineCorrelationCountK2 cfg s1 s2 = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveWeightedSBoxedAffineCorrelationBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity :
      PositiveDensityWeightedSBoxedAffineCorrelationBoxK2 num den cfg) :
    PositiveWeightedSBoxedAffineCorrelationBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveWeightedSBoxedAffineCorrelationBoxK2
  by_contra hnot
  have hzero : sBoxedAffineCorrelationWeightedSumK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveWeightedFixedSBoxedAffineCorrelationBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params} {s1 s2 : ℕ}
    (hDensity :
      PositiveDensityWeightedFixedSBoxedAffineCorrelationBoxK2
        num den cfg s1 s2) :
    PositiveWeightedFixedSBoxedAffineCorrelationBoxK2 cfg s1 s2 := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveWeightedFixedSBoxedAffineCorrelationBoxK2
  by_contra hnot
  have hzero :
      fixedSBoxedAffineCorrelationWeightedSumK2 cfg s1 s2 = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem switchedSBoxedSupply_of_positiveSBoxedAffineCorrelationBoxSupply
    (hSupply : InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2) :
    SwitchedSBoxedSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  unfold PositiveSBoxedAffineCorrelationBoxK2
    sBoxedAffineCorrelationCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨t, ht⟩
  unfold sBoxedAffineCorrelationBoxK2 at ht
  have hCorr : SBoxedAffineCorrelationK2 cfg t :=
    (Finset.mem_filter.mp ht).2
  have hW : SwitchedSBoxedSupplyWitnessK2 cfg t.n t.s1 t.s2 t.M1 t.M2 :=
    switchedSBoxedSupplyWitness_of_affineCorrelationTuple hCorr
  have hxLo : cfg.x ≤ t.n := by
    rcases hW with
      ⟨hxLo, _hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
        _hs1Pos, _hs2Pos, _hs1Le, _hs2Le, _hcoprime, _hn1, _hn2,
        _hLeftPos, _hRightPos⟩
    exact hxLo
  exact ⟨cfg, t.n, t.s1, t.s2, t.M1, t.M2, le_trans hNx hxLo, hW⟩

theorem positiveSBoxedAffineCorrelationBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensitySBoxedAffineCorrelationBoxesK2 num den) :
    InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveSBoxedAffineCorrelationBox_of_positiveDensity hDensity⟩

theorem positiveSBoxedAffineCorrelationBoxSupply_of_positiveWeighted
    (hSupply :
      InfinitelyManyPositiveWeightedSBoxedAffineCorrelationBoxesK2) :
    InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hWeighted⟩
  exact ⟨cfg, hNx,
    positiveSBoxedAffineCorrelationBox_of_positiveWeighted hWeighted⟩

theorem positiveSBoxedAffineCorrelationBoxSupply_of_averageOverSBoxedAffineCorrelationSupply
    (hSupply : AverageOverSBoxedAffineCorrelationSupplyK2) :
    InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2 :=
  positiveSBoxedAffineCorrelationBoxSupply_of_positiveWeighted hSupply

theorem positiveSBoxedAffineCorrelationBoxSupply_of_positiveFixed
    {s1 s2 : ℕ}
    (hSupply :
      InfinitelyManyPositiveFixedSBoxedAffineCorrelationBoxesK2 s1 s2) :
    InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hFixed⟩
  exact ⟨cfg, hNx,
    positiveSBoxedAffineCorrelationBox_of_positiveFixed hFixed⟩

theorem positiveFixedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
    {num den s1 s2 : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityFixedSBoxedAffineCorrelationBoxesK2
        num den s1 s2) :
    InfinitelyManyPositiveFixedSBoxedAffineCorrelationBoxesK2 s1 s2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveFixedSBoxedAffineCorrelationBox_of_positiveDensity hDensity⟩

theorem positiveFixedSBoxedAffineCorrelationBoxSupply_of_positiveWeighted
    {s1 s2 : ℕ}
    (hSupply :
      InfinitelyManyPositiveWeightedFixedSBoxedAffineCorrelationBoxesK2
        s1 s2) :
    InfinitelyManyPositiveFixedSBoxedAffineCorrelationBoxesK2 s1 s2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hWeighted⟩
  exact ⟨cfg, hNx,
    positiveFixedSBoxedAffineCorrelationBox_of_positiveWeighted hWeighted⟩

theorem positiveWeightedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityWeightedSBoxedAffineCorrelationBoxesK2
        num den) :
    InfinitelyManyPositiveWeightedSBoxedAffineCorrelationBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveWeightedSBoxedAffineCorrelationBox_of_positiveDensity hDensity⟩

theorem averageOverSBoxedAffineCorrelationSupply_of_weightedSBoxedAffineCorrelationSupply
    (hSupply : WeightedSBoxedAffineCorrelationSupplyK2) :
    AverageOverSBoxedAffineCorrelationSupplyK2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact positiveWeightedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
    hDensitySupply

theorem positiveWeightedFixedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
    {num den s1 s2 : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityWeightedFixedSBoxedAffineCorrelationBoxesK2
        num den s1 s2) :
    InfinitelyManyPositiveWeightedFixedSBoxedAffineCorrelationBoxesK2
      s1 s2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveWeightedFixedSBoxedAffineCorrelationBox_of_positiveDensity
      hDensity⟩

theorem fixedOneOnePrimeQuadruple_good_to_switchedSBoxedWitness
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u) :
    SwitchedSBoxedSupplyWitnessK2 cfg u.n 1 1
      (u.left.p * u.left.q) (u.right.p * u.right.q) := by
  rcases hGood with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hn1, hn2, hLeftPair, hRightPair⟩
  have hsMax : 1 ≤ cfg.sMax := by
    have hP0 : 3 ≤ cfg.P0 := cfg.P0_ge_3
    have hP0lt : cfg.P0 < cfg.sMax := cfg.P0_lt_sMax
    omega
  have hLeftPos :
      0 < SBoxedSemiprimeWeightK2 cfg 1 (u.left.p * u.left.q) := by
    unfold SBoxedSemiprimeWeightK2
    exact sBoxedSemiprimeWeightWith_pos_of_pair hLeftPair
  have hRightPos :
      0 < SBoxedSemiprimeWeightRightK2 cfg 1
        (u.right.p * u.right.q) := by
    unfold SBoxedSemiprimeWeightRightK2
    exact sBoxedSemiprimeWeightWith_pos_of_pair hRightPair
  exact ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
    by norm_num, by norm_num, hsMax, hsMax, by norm_num,
    by simpa [one_mul] using hn1, by simpa [one_mul] using hn2,
    hLeftPos, hRightPos⟩

theorem fixedOneOnePrimeQuadruple_good_mem_affineCorrelationTupleBox
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u) :
    ({ n := u.n, s1 := 1, s2 := 1,
       M1 := u.left.p * u.left.q,
       M2 := u.right.p * u.right.q } :
      SBoxedAffineCorrelationTupleK2) ∈
        sBoxedAffineCorrelationTupleBoxK2 cfg := by
  rcases hGood with
    ⟨hxLo, hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      hn1, hn2, _hLeftPair, _hRightPair⟩
  have hsMax : 1 ≤ cfg.sMax := by
    have hP0 : 3 ≤ cfg.P0 := cfg.P0_ge_3
    have hP0lt : cfg.P0 < cfg.sMax := cfg.P0_lt_sMax
    omega
  have hM1Hi : u.left.p * u.left.q ≤ 2 * cfg.x + 2 := by
    omega
  have hM2Hi : u.right.p * u.right.q ≤ 2 * cfg.x + 2 := by
    omega
  unfold sBoxedAffineCorrelationTupleBoxK2
  refine Finset.mem_image.mpr ?_
  refine ⟨(((((u.n, 1), 1), u.left.p * u.left.q),
      u.right.p * u.right.q)), ?_, rfl⟩
  simp [hxLo, hxHi, hsMax, hM1Hi, hM2Hi]

theorem fixedOneOnePrimeQuadruple_good_to_affineCorrelationTuple
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u) :
    SBoxedAffineCorrelationK2 cfg
      ({ n := u.n, s1 := 1, s2 := 1,
         M1 := u.left.p * u.left.q,
         M2 := u.right.p * u.right.q } :
        SBoxedAffineCorrelationTupleK2) := by
  rcases hGood with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hn1, hn2, hLeftPair, hRightPair⟩
  have hGood' : FixedOneOnePrimeQuadrupleGoodK2 cfg u :=
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hn1, hn2, hLeftPair, hRightPair⟩
  have hW :
      SwitchedSBoxedSupplyWitnessK2 cfg u.n 1 1
        (u.left.p * u.left.q) (u.right.p * u.right.q) :=
    fixedOneOnePrimeQuadruple_good_to_switchedSBoxedWitness hGood'
  have heq :
      1 * (u.left.p * u.left.q) + 1 =
        2 * 1 * (u.right.p * u.right.q) := by
    omega
  exact ⟨hW, heq, by simp [Nat.mod_one]⟩

theorem fixedOneOnePrimeQuadruple_good_mem_fixedAffineCorrelationBox
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u) :
    ({ n := u.n, s1 := 1, s2 := 1,
       M1 := u.left.p * u.left.q,
       M2 := u.right.p * u.right.q } :
      SBoxedAffineCorrelationTupleK2) ∈
        fixedSBoxedAffineCorrelationBoxK2 cfg 1 1 := by
  unfold fixedSBoxedAffineCorrelationBoxK2 sBoxedAffineCorrelationBoxK2
  refine Finset.mem_filter.mpr ?_
  constructor
  · refine Finset.mem_filter.mpr ?_
    exact ⟨fixedOneOnePrimeQuadruple_good_mem_affineCorrelationTupleBox hGood,
      fixedOneOnePrimeQuadruple_good_to_affineCorrelationTuple hGood⟩
  · simp

theorem positiveFixedOneOnePrimeQuadrupleBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity : PositiveDensityFixedOneOnePrimeQuadrupleBoxK2 num den cfg) :
    PositiveFixedOneOnePrimeQuadrupleBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveFixedOneOnePrimeQuadrupleBoxK2
  by_contra hnot
  have hzero : fixedOneOnePrimeQuadrupleCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveWeightedFixedSBoxedAffineCorrelationBox_of_positiveFixedOneOnePrimeQuadrupleBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOnePrimeQuadrupleBoxK2 cfg) :
    PositiveWeightedFixedSBoxedAffineCorrelationBoxK2 cfg 1 1 := by
  unfold PositiveFixedOneOnePrimeQuadrupleBoxK2
    fixedOneOnePrimeQuadrupleCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOnePrimeQuadrupleBoxK2 at hu
  have hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u :=
    (Finset.mem_filter.mp hu).2
  let t : SBoxedAffineCorrelationTupleK2 :=
    { n := u.n, s1 := 1, s2 := 1,
      M1 := u.left.p * u.left.q,
      M2 := u.right.p * u.right.q }
  have ht : t ∈ fixedSBoxedAffineCorrelationBoxK2 cfg 1 1 := by
    dsimp [t]
    exact fixedOneOnePrimeQuadruple_good_mem_fixedAffineCorrelationBox hGood
  have hLeftPair : SBoxedSemiprimePairK2 cfg 1
      (u.left.p * u.left.q) 1 1 u.left := by
    rcases hGood with
      ⟨_hxLo, _hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
        _hn1, _hn2, hLeftPair, _hRightPair⟩
    exact hLeftPair
  have hRightPair : SBoxedSemiprimePairK2 cfg 1
      (u.right.p * u.right.q) 2 2 u.right := by
    rcases hGood with
      ⟨_hxLo, _hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
        _hn1, _hn2, _hLeftPair, hRightPair⟩
    exact hRightPair
  have hLeftPos :
      0 < SBoxedSemiprimeWeightK2 cfg 1 (u.left.p * u.left.q) := by
    unfold SBoxedSemiprimeWeightK2
    exact sBoxedSemiprimeWeightWith_pos_of_pair hLeftPair
  have hRightPos :
      0 < SBoxedSemiprimeWeightRightK2 cfg 1
        (u.right.p * u.right.q) := by
    unfold SBoxedSemiprimeWeightRightK2
    exact sBoxedSemiprimeWeightWith_pos_of_pair hRightPair
  have hWeightPos : 0 < SBoxedAffineCorrelationWeightK2 cfg t := by
    dsimp [t, SBoxedAffineCorrelationWeightK2]
    exact Nat.mul_pos hLeftPos hRightPos
  unfold PositiveWeightedFixedSBoxedAffineCorrelationBoxK2
    fixedSBoxedAffineCorrelationWeightedSumK2
  exact lt_of_lt_of_le hWeightPos
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht)

theorem switchedSBoxedSupply_of_positiveFixedOneOnePrimeQuadrupleSupply
    (hSupply : InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2) :
    SwitchedSBoxedSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  unfold PositiveFixedOneOnePrimeQuadrupleBoxK2
    fixedOneOnePrimeQuadrupleCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOnePrimeQuadrupleBoxK2 at hu
  have hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u :=
    (Finset.mem_filter.mp hu).2
  have hW :
      SwitchedSBoxedSupplyWitnessK2 cfg u.n 1 1
        (u.left.p * u.left.q) (u.right.p * u.right.q) :=
    fixedOneOnePrimeQuadruple_good_to_switchedSBoxedWitness hGood
  have hxLo : cfg.x ≤ u.n := by
    rcases hW with
      ⟨hxLo, _hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
        _hs1Pos, _hs2Pos, _hs1Le, _hs2Le, _hcoprime, _hn1, _hn2,
        _hLeftPos, _hRightPos⟩
    exact hxLo
  exact ⟨cfg, u.n, 1, 1, u.left.p * u.left.q, u.right.p * u.right.q,
    le_trans hNx hxLo, hW⟩

theorem positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityFixedOneOnePrimeQuadrupleBoxesK2 num den) :
    InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOnePrimeQuadrupleBox_of_positiveDensity hDensity⟩

theorem positiveWeightedFixedSBoxedAffineCorrelationBoxSupply_of_positiveFixedOneOnePrimeQuadrupleSupply
    (hSupply : InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2) :
    InfinitelyManyPositiveWeightedFixedSBoxedAffineCorrelationBoxesK2 1 1 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  exact ⟨cfg, hNx,
    positiveWeightedFixedSBoxedAffineCorrelationBox_of_positiveFixedOneOnePrimeQuadrupleBox
      hpos⟩

theorem switchedSBoxedSupply_of_fixedOneOnePrimeQuadrupleSupply
    (hSupply : FixedOneOnePrimeQuadrupleSupplyK2) :
    SwitchedSBoxedSupplyK2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact switchedSBoxedSupply_of_positiveFixedOneOnePrimeQuadrupleSupply
    (positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveDensity
      hDensitySupply)

theorem patternWitnessSupply_of_patternSupply
    (hSupply : InfinitelyManyPatternK2) :
    InfinitelyManyPatternWitnessK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, hnN, ⟨hP⟩⟩
  rcases PatternK2_witness hP with ⟨w, hW⟩
  exact ⟨cfg, n, w, hnN, hW⟩

theorem patternSupply_of_patternWitnessSupply
    (hSupply : InfinitelyManyPatternWitnessK2) :
    InfinitelyManyPatternK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, w, hnN, hW⟩
  exact ⟨cfg, n, hnN, ⟨PatternK2_of_witness hW⟩⟩

theorem patternWitnessSupply_iff_patternSupply :
    InfinitelyManyPatternWitnessK2 ↔ InfinitelyManyPatternK2 :=
  ⟨patternSupply_of_patternWitnessSupply,
    patternWitnessSupply_of_patternSupply⟩

theorem carryAwarePQSSupply_of_patternWitnessSupply
    (hSupply : InfinitelyManyPatternWitnessK2) :
    InfinitelyManyCarryAwarePQSK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, w, hnN, hW⟩
  exact ⟨cfg, n, w, hnN, PatternWitnessK2_carryAwarePQS hW⟩

theorem patternWitnessSupply_of_carryAwarePQSSupply
    (hSupply : InfinitelyManyCarryAwarePQSK2) :
    InfinitelyManyPatternWitnessK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, w, hnN, hC⟩
  exact ⟨cfg, n, w, hnN, PatternWitnessK2_of_carryAwarePQS hC⟩

theorem carryAwarePQSSupply_iff_patternWitnessSupply :
    InfinitelyManyCarryAwarePQSK2 ↔ InfinitelyManyPatternWitnessK2 :=
  ⟨patternWitnessSupply_of_carryAwarePQSSupply,
    carryAwarePQSSupply_of_patternWitnessSupply⟩

theorem carryAwarePQSSupply_of_sameBandCarryAwarePQSSupply
    (hSupply : InfinitelyManySameBandCarryAwarePQSK2) :
    InfinitelyManyCarryAwarePQSK2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, w, hnN, _hSameBand, hC⟩
  exact ⟨cfg, n, w, hnN, hC⟩

theorem carryAwarePQS_of_countedTuple
    {cfg : K2Params} {t : CountTupleK2}
    (hCounted : CarryAwareCountedTupleK2 cfg t) :
    CarryAwarePQSK2 cfg t.n t.toWitness := by
  rcases hCounted with
    ⟨_htxLo, _htxHi, _hSameBand, hEq, hBand, hSaw, hFiniteMedium⟩
  exact ⟨hEq, bandedAnatomyWitness_of_finite hBand, hSaw,
    mediumHygiene_of_finiteMediumHygiene hFiniteMedium⟩

theorem erdosAt2_of_countedTuple
    {cfg : K2Params} {t : CountTupleK2}
    (hCounted : CarryAwareCountedTupleK2 cfg t) :
    erdosAt 2 t.n :=
  PatternWitnessK2_implies_erdosAt2
    (PatternWitnessK2_of_carryAwarePQS
      (carryAwarePQS_of_countedTuple hCounted))

theorem exists_erdosAt2_in_box_of_positiveSameBandCarryAwarePQSBox
    {cfg : K2Params}
    (hpos : PositiveSameBandCarryAwarePQSBoxK2 cfg) :
    ∃ n : ℕ, cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧ erdosAt 2 n := by
  unfold PositiveSameBandCarryAwarePQSBoxK2 sameBandCarryAwarePQSCountK2 at hpos
  rcases (Finset.card_pos.mp hpos) with ⟨t, ht⟩
  unfold sameBandCarryAwarePQSBoxK2 at ht
  have hCounted : CarryAwareCountedTupleK2 cfg t :=
    (Finset.mem_filter.mp ht).2
  have hAt : erdosAt 2 t.n :=
    erdosAt2_of_countedTuple hCounted
  rcases hCounted with
    ⟨hxLo, hxHi, _hSameBand, _hEq, _hBand, _hSaw, _hFiniteMedium⟩
  exact ⟨t.n, hxLo, hxHi, hAt⟩

theorem positiveSameBandCarryAwarePQSBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity : PositiveDensitySameBandCarryAwarePQSBoxK2 num den cfg) :
    PositiveSameBandCarryAwarePQSBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveSameBandCarryAwarePQSBoxK2
  by_contra hnot
  have hzero : sameBandCarryAwarePQSCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem erdosAt2_of_switchedSupplyWitness
    {cfg : K2Params} {n s1 s2 M1 M2 : ℕ}
    (hW : SwitchedSupplyWitnessK2 cfg n s1 s2 M1 M2) :
    erdosAt 2 n := by
  rcases hW with
    ⟨hxLo, hxHi, hmod2, _hSameBand, hSmallOdd, hFiniteMedium,
      hs1Pos, hs2Pos, hs1Le, hs2Le, hn1, hn2, hLeftPos, hRightPos⟩
  unfold MarkedSemiprimeWeightK2 MarkedSemiprimeWeightWithK2 at hLeftPos
  rcases Finset.card_pos.mp hLeftPos with ⟨left, hleftMem⟩
  have hLeftMarked : MarkedSemiprimePairK2 cfg s1 M1 1 1 left :=
    (Finset.mem_filter.mp hleftMem).2
  unfold MarkedSemiprimeWeightRightK2
    MarkedSemiprimeWeightWithK2 at hRightPos
  rcases Finset.card_pos.mp hRightPos with ⟨right, hrightMem⟩
  have hRightMarked : MarkedSemiprimePairK2 cfg s2 M2 2 2 right :=
    (Finset.mem_filter.mp hrightMem).2
  rcases hLeftMarked with
    ⟨hM1, hp1, hq1, hp1Band, hq1Band,
      hp1sqMarked, hq1sqMarked, hsawp1Marked, hsawq1Marked⟩
  rcases hRightMarked with
    ⟨hM2, hp2, hq2, hp2Band, hq2Band,
      hp2sqMarked, hq2sqMarked, hsawp2Marked, hsawq2Marked⟩
  let w : PQSWitnessK2 :=
    { p1 := left.p, q1 := left.q, s1 := s1,
      p2 := right.p, q2 := right.q, s2 := s2 }
  have h1 : n + 1 = w.p1 * w.q1 * w.s1 := by
    dsimp [w]
    calc
      n + 1 = s1 * M1 := hn1
      _ = left.p * left.q * s1 := by
        rw [hM1]
        ring
  have h2 : n + 2 = 2 * w.p2 * w.q2 * w.s2 := by
    dsimp [w]
    calc
      n + 2 = 2 * s2 * M2 := hn2
      _ = 2 * right.p * right.q * s2 := by
        rw [hM2]
        ring
  have hp1sq : ¬ w.p1 ^ 2 ∣ n + 1 := by
    dsimp [w]
    intro hdiv
    exact hp1sqMarked
      (by
        simpa [hn1, one_mul, mul_assoc, mul_left_comm, mul_comm]
          using hdiv)
  have hq1sq : ¬ w.q1 ^ 2 ∣ n + 1 := by
    dsimp [w]
    intro hdiv
    exact hq1sqMarked
      (by
        simpa [hn1, one_mul, mul_assoc, mul_left_comm, mul_comm]
          using hdiv)
  have hp2sq : ¬ w.p2 ^ 2 ∣ n + 2 := by
    dsimp [w]
    intro hdiv
    exact hp2sqMarked
      (by
        simpa [hn2, mul_assoc, mul_left_comm, mul_comm] using hdiv)
  have hq2sq : ¬ w.q2 ^ 2 ∣ n + 2 := by
    dsimp [w]
    intro hdiv
    exact hq2sqMarked
      (by
        simpa [hn2, mul_assoc, mul_left_comm, mul_comm] using hdiv)
  have hsawp1 : SawJ 1 w.p1 (w.q1 * w.s1) := by
    dsimp [w]
    simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hsawp1Marked
  have hsawq1 : SawJ 1 w.q1 (w.p1 * w.s1) := by
    dsimp [w]
    simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hsawq1Marked
  have hsawp2 : SawJ 2 w.p2 (2 * w.q2 * w.s2) := by
    dsimp [w]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsawp2Marked
  have hsawq2 : SawJ 2 w.q2 (2 * w.p2 * w.s2) := by
    dsimp [w]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsawq2Marked
  have hFiniteBand : FiniteBandedAnatomyWitnessK2 cfg n w := by
    exact ⟨hxLo, hxHi, hmod2, hSmallOdd, h1, h2,
      hp1, hq1, hp2, hq2, hp1Band, hq1Band, hp2Band, hq2Band,
      hs1Pos, hs2Pos, hs1Le, hs2Le, hp1sq, hq1sq, hp2sq, hq2sq⟩
  have hSaw : SawtoothWitnessK2 n w :=
    ⟨h1, h2, hsawp1, hsawq1, hsawp2, hsawq2⟩
  exact PatternWitnessK2_implies_erdosAt2
    ⟨bandedAnatomyWitness_of_finite hFiniteBand,
      hSaw, mediumHygiene_of_finiteMediumHygiene hFiniteMedium⟩

theorem erdosAt2_of_sBoxedAffineCorrelationTuple
    {cfg : K2Params} {t : SBoxedAffineCorrelationTupleK2}
    (hCorr : SBoxedAffineCorrelationK2 cfg t) :
    erdosAt 2 t.n :=
  erdosAt2_of_switchedSupplyWitness
    (switchedSupplyWitness_of_switchedSBoxedSupplyWitness
      (switchedSBoxedSupplyWitness_of_affineCorrelationTuple hCorr))

theorem exists_erdosAt2_in_sBoxedAffineCorrelationBox
    {cfg : K2Params}
    (hpos : PositiveSBoxedAffineCorrelationBoxK2 cfg) :
    ∃ n : ℕ, cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧ erdosAt 2 n := by
  unfold PositiveSBoxedAffineCorrelationBoxK2
    sBoxedAffineCorrelationCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨t, ht⟩
  unfold sBoxedAffineCorrelationBoxK2 at ht
  have hCorr : SBoxedAffineCorrelationK2 cfg t :=
    (Finset.mem_filter.mp ht).2
  have hW : SwitchedSBoxedSupplyWitnessK2 cfg t.n t.s1 t.s2 t.M1 t.M2 :=
    switchedSBoxedSupplyWitness_of_affineCorrelationTuple hCorr
  have hAt : erdosAt 2 t.n :=
    erdosAt2_of_sBoxedAffineCorrelationTuple hCorr
  rcases hW with
    ⟨hxLo, hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      _hs1Pos, _hs2Pos, _hs1Le, _hs2Le, _hcoprime, _hn1, _hn2,
      _hLeftPos, _hRightPos⟩
  exact ⟨t.n, hxLo, hxHi, hAt⟩

theorem erdosAt2_of_fixedOneOnePrimeQuadrupleGood
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u) :
    erdosAt 2 u.n :=
  erdosAt2_of_switchedSupplyWitness
    (switchedSupplyWitness_of_switchedSBoxedSupplyWitness
      (fixedOneOnePrimeQuadruple_good_to_switchedSBoxedWitness hGood))

theorem exists_erdosAt2_in_fixedOneOnePrimeQuadrupleBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOnePrimeQuadrupleBoxK2 cfg) :
    ∃ n : ℕ, cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧ erdosAt 2 n := by
  unfold PositiveFixedOneOnePrimeQuadrupleBoxK2
    fixedOneOnePrimeQuadrupleCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOnePrimeQuadrupleBoxK2 at hu
  have hGood : FixedOneOnePrimeQuadrupleGoodK2 cfg u :=
    (Finset.mem_filter.mp hu).2
  have hAt : erdosAt 2 u.n :=
    erdosAt2_of_fixedOneOnePrimeQuadrupleGood hGood
  rcases hGood with
    ⟨hxLo, hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      _hn1, _hn2, _hLeftPair, _hRightPair⟩
  exact ⟨u.n, hxLo, hxHi, hAt⟩

theorem not_left_prime_sq_dvd_prime_mul_prime_of_lt
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) :
    ¬ p ^ 2 ∣ p * q := by
  intro h
  have hp_dvd_q : p ∣ q := by
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos (by
      simpa [pow_two, mul_assoc] using h)
  have hq_eq_p : q = p := (hq.dvd_iff_eq hp.ne_one).mp hp_dvd_q
  omega

theorem not_right_prime_sq_dvd_prime_mul_prime_of_lt
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) :
    ¬ q ^ 2 ∣ p * q := by
  intro h
  have hq_dvd_p : q ∣ p := by
    exact Nat.dvd_of_mul_dvd_mul_left hq.pos (by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h)
  have hp_eq_q : p = q := (hp.dvd_iff_eq hq.ne_one).mp hq_dvd_p
  omega

theorem not_left_prime_sq_dvd_two_mul_prime_mul_prime_of_band
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hfour : 4 < p) (hpq : p < q) :
    ¬ p ^ 2 ∣ 2 * (p * q) := by
  intro h
  have hp_dvd_twoq : p ∣ 2 * q := by
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos (by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h)
  rcases (hp.dvd_mul.mp hp_dvd_twoq) with hp_dvd_two | hp_dvd_q
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hp_dvd_two
    omega
  · have hq_eq_p : q = p := (hq.dvd_iff_eq hp.ne_one).mp hp_dvd_q
    omega

theorem not_right_prime_sq_dvd_two_mul_prime_mul_prime_of_band
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hfour : 4 < p) (hpq : p < q) :
    ¬ q ^ 2 ∣ 2 * (p * q) := by
  intro h
  have hq_dvd_twop : q ∣ 2 * p := by
    exact Nat.dvd_of_mul_dvd_mul_left hq.pos (by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h)
  rcases (hq.dvd_mul.mp hq_dvd_twop) with hq_dvd_two | hq_dvd_p
  · have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hq_dvd_two
    omega
  · have hp_eq_q : p = q := (hp.dvd_iff_eq hq.ne_one).mp hq_dvd_p
    omega

theorem fixedOneOnePrimeQuadruple_ratioGood_to_good
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hRatio : FixedOneOneRatioPrimeQuadrupleGoodK2 cfg u) :
    FixedOneOnePrimeQuadrupleGoodK2 cfg u := by
  rcases hRatio with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hn1, hn2, hleftP, hleftQ, hrightP, hrightQ,
      hleftPBand, hleftQBand, hrightPBand, hrightQBand,
      hleftPSq, hleftQSq, hrightPSq, hrightQSq,
      hleftOrder, hleftLo, hleftHi, hrightOrder, hrightLo, hrightHi⟩
  have hLeftSawP : SawJ 1 u.left.p u.left.q :=
    sawJ_one_left_of_three_two_box hleftOrder hleftLo hleftHi
  have hLeftSawQ : SawJ 1 u.left.q u.left.p :=
    sawJ_one_right_of_two_box hleftOrder hleftHi
  have hRightSawP : SawJ 2 u.right.p (2 * u.right.q) :=
    sawJ_two_left_of_five_four_box hrightOrder hrightLo hrightHi
  have hRightSawQ : SawJ 2 u.right.q (2 * u.right.p) :=
    sawJ_two_right_of_four_three_box hrightOrder hrightHi
  have hLeftPair :
      SBoxedSemiprimePairK2 cfg 1
        (u.left.p * u.left.q) 1 1 u.left := by
    refine ⟨?_, hleftOrder, by omega⟩
    refine ⟨rfl, hleftP, hleftQ, hleftPBand, hleftQBand, ?_, ?_, ?_, ?_⟩
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hleftPSq
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hleftQSq
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hLeftSawP
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hLeftSawQ
  have hRightPair :
      SBoxedSemiprimePairK2 cfg 1
        (u.right.p * u.right.q) 2 2 u.right := by
    refine ⟨?_, hrightOrder, by omega⟩
    refine ⟨rfl, hrightP, hrightQ, hrightPBand, hrightQBand,
      ?_, ?_, ?_, ?_⟩
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hrightPSq
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hrightQSq
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hRightSawP
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hRightSawQ
  exact ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
    hn1, hn2, hLeftPair, hRightPair⟩

theorem fixedOneOnePrimeQuadruple_cleanRatioGood_to_ratioGood
    {cfg : K2Params} {u : FixedOneOnePrimeQuadrupleK2}
    (hClean : FixedOneOneCleanRatioPrimeQuadrupleGoodK2 cfg u) :
    FixedOneOneRatioPrimeQuadrupleGoodK2 cfg u := by
  rcases hClean with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hn1, hn2, hleftP, hleftQ, hrightP, hrightQ,
      hleftPBand, hleftQBand, hrightPBand, hrightQBand,
      hleftOrder, hleftLo, hleftHi, hrightOrder, hrightLo, hrightHi⟩
  have hrightPFour : 4 < u.right.p :=
    lt_trans cfg.four_lt_pLo hrightPBand.1
  have hleftPSq : ¬ u.left.p ^ 2 ∣ u.left.p * u.left.q :=
    not_left_prime_sq_dvd_prime_mul_prime_of_lt
      hleftP hleftQ hleftOrder
  have hleftQSq : ¬ u.left.q ^ 2 ∣ u.left.p * u.left.q :=
    not_right_prime_sq_dvd_prime_mul_prime_of_lt
      hleftP hleftQ hleftOrder
  have hrightPSq :
      ¬ u.right.p ^ 2 ∣ 2 * (u.right.p * u.right.q) :=
    not_left_prime_sq_dvd_two_mul_prime_mul_prime_of_band
      hrightP hrightQ hrightPFour hrightOrder
  have hrightQSq :
      ¬ u.right.q ^ 2 ∣ 2 * (u.right.p * u.right.q) :=
    not_right_prime_sq_dvd_two_mul_prime_mul_prime_of_band
      hrightP hrightQ hrightPFour hrightOrder
  exact ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
    hn1, hn2, hleftP, hleftQ, hrightP, hrightQ,
    hleftPBand, hleftQBand, hrightPBand, hrightQBand,
    hleftPSq, hleftQSq, hrightPSq, hrightQSq,
    hleftOrder, hleftLo, hleftHi, hrightOrder, hrightLo, hrightHi⟩

theorem positiveFixedOneOnePrimeQuadrupleBox_of_positiveRatioBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOneRatioPrimeQuadrupleBoxK2 cfg) :
    PositiveFixedOneOnePrimeQuadrupleBoxK2 cfg := by
  unfold PositiveFixedOneOneRatioPrimeQuadrupleBoxK2
    fixedOneOneRatioPrimeQuadrupleCountK2 at hpos
  unfold PositiveFixedOneOnePrimeQuadrupleBoxK2
    fixedOneOnePrimeQuadrupleCountK2
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOneRatioPrimeQuadrupleBoxK2 at hu
  rcases Finset.mem_filter.mp hu with ⟨hmem, hRatio⟩
  exact Finset.card_pos.mpr
    ⟨u, Finset.mem_filter.mpr
      ⟨hmem, fixedOneOnePrimeQuadruple_ratioGood_to_good hRatio⟩⟩

theorem positiveFixedOneOneRatioPrimeQuadrupleBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity :
      PositiveDensityFixedOneOneRatioPrimeQuadrupleBoxK2 num den cfg) :
    PositiveFixedOneOneRatioPrimeQuadrupleBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveFixedOneOneRatioPrimeQuadrupleBoxK2
  by_contra hnot
  have hzero : fixedOneOneRatioPrimeQuadrupleCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveRatioSupply
    (hSupply : InfinitelyManyPositiveFixedOneOneRatioPrimeQuadrupleBoxesK2) :
    InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOnePrimeQuadrupleBox_of_positiveRatioBox hpos⟩

theorem positiveFixedOneOneRatioPrimeQuadrupleBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityFixedOneOneRatioPrimeQuadrupleBoxesK2
        num den) :
    InfinitelyManyPositiveFixedOneOneRatioPrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOneRatioPrimeQuadrupleBox_of_positiveDensity hDensity⟩

theorem positiveFixedOneOneRatioPrimeQuadrupleBox_of_positiveCleanRatioBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2 cfg) :
    PositiveFixedOneOneRatioPrimeQuadrupleBoxK2 cfg := by
  unfold PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2
    fixedOneOneCleanRatioPrimeQuadrupleCountK2 at hpos
  unfold PositiveFixedOneOneRatioPrimeQuadrupleBoxK2
    fixedOneOneRatioPrimeQuadrupleCountK2
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOneCleanRatioPrimeQuadrupleBoxK2 at hu
  rcases Finset.mem_filter.mp hu with ⟨hmem, hClean⟩
  exact Finset.card_pos.mpr
    ⟨u, Finset.mem_filter.mpr
      ⟨hmem, fixedOneOnePrimeQuadruple_cleanRatioGood_to_ratioGood hClean⟩⟩

theorem positiveFixedOneOneCleanRatioPrimeQuadrupleBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity :
      PositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxK2 num den cfg) :
    PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2
  by_contra hnot
  have hzero : fixedOneOneCleanRatioPrimeQuadrupleCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveFixedOneOneRatioPrimeQuadrupleBoxSupply_of_positiveCleanRatioSupply
    (hSupply :
      InfinitelyManyPositiveFixedOneOneCleanRatioPrimeQuadrupleBoxesK2) :
    InfinitelyManyPositiveFixedOneOneRatioPrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOneRatioPrimeQuadrupleBox_of_positiveCleanRatioBox hpos⟩

theorem positiveFixedOneOneCleanRatioPrimeQuadrupleBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityFixedOneOneCleanRatioPrimeQuadrupleBoxesK2
        num den) :
    InfinitelyManyPositiveFixedOneOneCleanRatioPrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOneCleanRatioPrimeQuadrupleBox_of_positiveDensity
      hDensity⟩

theorem fixedOneOneRawPrimeQuadruple_good_mem_cleanRatioTupleBox
    {cfg : K2Params} {u : FixedOneOneRawPrimeQuadrupleK2}
    (hRaw : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u) :
    u.toPrimeQuadruple ∈ fixedOneOnePrimeQuadrupleTupleBoxK2 cfg := by
  rcases hRaw with
    ⟨hxLo, hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      _hEq, _hleftP, _hleftQ, _hrightP, _hrightQ,
      hleftPBand, hleftQBand, hrightPBand, hrightQBand,
      _hleftOrder, _hleftLo, _hleftHi, _hrightOrder,
      _hrightLo, _hrightHi⟩
  have hLeftMem : u.left ∈ semiprimePairBoxK2 cfg := by
    unfold semiprimePairBoxK2
    refine Finset.mem_image.mpr ?_
    refine ⟨(u.left.p, u.left.q), ?_, rfl⟩
    simp [hleftPBand.2, hleftQBand.2]
  have hRightMem : u.right ∈ semiprimePairBoxK2 cfg := by
    unfold semiprimePairBoxK2
    refine Finset.mem_image.mpr ?_
    refine ⟨(u.right.p, u.right.q), ?_, rfl⟩
    simp [hrightPBand.2, hrightQBand.2]
  unfold fixedOneOnePrimeQuadrupleTupleBoxK2
  refine Finset.mem_image.mpr ?_
  refine ⟨((u.n, u.left), u.right), ?_, rfl⟩
  simp [hxLo, hxHi, hLeftMem, hRightMem]

theorem fixedOneOneRawPrimeQuadruple_good_to_cleanRatioGood
    {cfg : K2Params} {u : FixedOneOneRawPrimeQuadrupleK2}
    (hRaw : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u) :
    FixedOneOneCleanRatioPrimeQuadrupleGoodK2 cfg u.toPrimeQuadruple := by
  rcases hRaw with
    ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
      hEq, hleftP, hleftQ, hrightP, hrightQ,
      hleftPBand, hleftQBand, hrightPBand, hrightQBand,
      hleftOrder, hleftLo, hleftHi, hrightOrder, hrightLo, hrightHi⟩
  have hn1 :
      u.toPrimeQuadruple.n + 1 = u.left.p * u.left.q := by
    dsimp [FixedOneOneRawPrimeQuadrupleK2.toPrimeQuadruple,
      FixedOneOneRawPrimeQuadrupleK2.n]
    omega
  have hn2 :
      u.toPrimeQuadruple.n + 2 = 2 * (u.right.p * u.right.q) := by
    dsimp [FixedOneOneRawPrimeQuadrupleK2.toPrimeQuadruple,
      FixedOneOneRawPrimeQuadrupleK2.n]
    omega
  exact ⟨hxLo, hxHi, hmod2, hSameBand, hSmallOdd, hFiniteMedium,
    hn1, hn2, hleftP, hleftQ, hrightP, hrightQ,
    hleftPBand, hleftQBand, hrightPBand, hrightQBand,
    hleftOrder, hleftLo, hleftHi, hrightOrder, hrightLo, hrightHi⟩

theorem erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood
    {cfg : K2Params} {u : FixedOneOneRawPrimeQuadrupleK2}
    (hRaw : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u) :
    erdosAt 2 u.n :=
  erdosAt2_of_fixedOneOnePrimeQuadrupleGood
    (fixedOneOnePrimeQuadruple_ratioGood_to_good
      (fixedOneOnePrimeQuadruple_cleanRatioGood_to_ratioGood
        (fixedOneOneRawPrimeQuadruple_good_to_cleanRatioGood hRaw)))

theorem exists_erdosAt2_in_fixedOneOneRawCleanRatioPrimeQuadrupleBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 cfg) :
    ∃ n : ℕ, cfg.x ≤ n ∧ n ≤ 2 * cfg.x ∧ erdosAt 2 n := by
  unfold PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 at hu
  have hRaw : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u :=
    (Finset.mem_filter.mp hu).2
  have hAt : erdosAt 2 u.n :=
    erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood hRaw
  rcases hRaw with
    ⟨hxLo, hxHi, _hmod2, _hSameBand, _hSmallOdd, _hFiniteMedium,
      _hEq, _hleftP, _hleftQ, _hrightP, _hrightQ,
      _hleftPBand, _hleftQBand, _hrightPBand, _hrightQBand,
      _hleftOrder, _hleftLo, _hleftHi, _hrightOrder,
      _hrightLo, _hrightHi⟩
  exact ⟨u.n, hxLo, hxHi, hAt⟩

theorem positiveFixedOneOneCleanRatioPrimeQuadrupleBox_of_positiveRawCleanRatioBox
    {cfg : K2Params}
    (hpos : PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 cfg) :
    PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2 cfg := by
  unfold PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 at hpos
  unfold PositiveFixedOneOneCleanRatioPrimeQuadrupleBoxK2
    fixedOneOneCleanRatioPrimeQuadrupleCountK2
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 at hu
  rcases Finset.mem_filter.mp hu with ⟨_hmem, hRaw⟩
  exact Finset.card_pos.mpr
    ⟨u.toPrimeQuadruple, Finset.mem_filter.mpr
      ⟨fixedOneOneRawPrimeQuadruple_good_mem_cleanRatioTupleBox hRaw,
        fixedOneOneRawPrimeQuadruple_good_to_cleanRatioGood hRaw⟩⟩

theorem positiveFixedOneOneRawCleanRatioPrimeQuadrupleBox_of_positiveDensity
    {num den : ℕ} {cfg : K2Params}
    (hDensity :
      PositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 num den cfg) :
    PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 cfg := by
  rcases hDensity with ⟨hnum, hle⟩
  unfold PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
  by_contra hnot
  have hzero : fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 cfg = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hxpos : 0 < cfg.x :=
    lt_of_lt_of_le (by norm_num : 0 < 2) cfg.x_ge_2
  have hle_zero : num * cfg.x ≤ 0 := by
    simpa [hzero] using hle
  have hprod_zero : num * cfg.x = 0 :=
    Nat.eq_zero_of_le_zero hle_zero
  rcases Nat.mul_eq_zero.mp hprod_zero with hnum_zero | hx_zero
  · omega
  · omega

theorem positiveFixedOneOneCleanRatioPrimeQuadrupleBoxSupply_of_positiveRawCleanRatioSupply
    (hSupply :
      InfinitelyManyPositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2) :
    InfinitelyManyPositiveFixedOneOneCleanRatioPrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOneCleanRatioPrimeQuadrupleBox_of_positiveRawCleanRatioBox
      hpos⟩

theorem positiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxSupply_of_positiveDensity
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensityFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2
        num den) :
    InfinitelyManyPositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx,
    positiveFixedOneOneRawCleanRatioPrimeQuadrupleBox_of_positiveDensity
      hDensity⟩

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_positiveBoxSupply
    (hSupply :
      InfinitelyManyPositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  unfold PositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxK2
    fixedOneOneRawCleanRatioPrimeQuadrupleCountK2 at hpos
  rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
  unfold fixedOneOneRawCleanRatioPrimeQuadrupleBoxK2 at hu
  have hRaw : FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg u :=
    (Finset.mem_filter.mp hu).2
  exact ⟨cfg, u, le_trans hNx hRaw.1, hRaw⟩

theorem fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_densitySupply
    (hSupply : FixedOneOneRawCleanRatioPrimeQuadrupleSupplyK2) :
    FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_positiveBoxSupply
    (positiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxSupply_of_positiveDensity
      hDensitySupply)

theorem sameBandCarryAwarePQSSupply_of_positiveBoxSupply
    (hSupply : InfinitelyManyPositiveSameBandCarryAwarePQSBoxesK2) :
    InfinitelyManySameBandCarryAwarePQSK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hpos⟩
  unfold PositiveSameBandCarryAwarePQSBoxK2 sameBandCarryAwarePQSCountK2 at hpos
  rcases (Finset.card_pos.mp hpos) with ⟨t, ht⟩
  unfold sameBandCarryAwarePQSBoxK2 at ht
  have hCounted : CarryAwareCountedTupleK2 cfg t :=
    (Finset.mem_filter.mp ht).2
  have hCarry : CarryAwarePQSK2 cfg t.n t.toWitness :=
    carryAwarePQS_of_countedTuple hCounted
  rcases hCounted with
    ⟨htxLo, _htxHi, hSameBand, _hEq, _hBand, _hSaw, _hFiniteMedium⟩
  exact ⟨cfg, t.n, t.toWitness, le_trans hNx htxLo, hSameBand, hCarry⟩

theorem positiveBoxSupply_of_positiveDensityBoxSupply
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensitySameBandCarryAwarePQSBoxesK2 num den) :
    InfinitelyManyPositiveSameBandCarryAwarePQSBoxesK2 := by
  intro N
  rcases hSupply N with ⟨cfg, hNx, hDensity⟩
  exact ⟨cfg, hNx, positiveSameBandCarryAwarePQSBox_of_positiveDensity hDensity⟩

theorem conditional_k2_from_pattern_supply
    (hSupply : InfinitelyManyPatternK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, hnN, ⟨hP⟩⟩
  exact ⟨n, hnN, PatternK2_implies_erdosAt2 hP⟩

theorem conditional_k2_from_pattern_witness_supply
    (hSupply : InfinitelyManyPatternWitnessK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, w, hnN, hW⟩
  exact ⟨n, hnN, PatternWitnessK2_implies_erdosAt2 hW⟩

theorem conditional_k2_from_carryAwarePQS_supply
    (hSupply : InfinitelyManyCarryAwarePQSK2) :
    erdosFixed 2 :=
  conditional_k2_from_pattern_witness_supply
    (patternWitnessSupply_of_carryAwarePQSSupply hSupply)

theorem conditional_k2_from_sameBandCarryAwarePQS_supply
    (hSupply : InfinitelyManySameBandCarryAwarePQSK2) :
    erdosFixed 2 :=
  conditional_k2_from_carryAwarePQS_supply
    (carryAwarePQSSupply_of_sameBandCarryAwarePQSSupply hSupply)

theorem conditional_k2_from_positiveSameBandCarryAwarePQSBox_supply
    (hSupply : InfinitelyManyPositiveSameBandCarryAwarePQSBoxesK2) :
    erdosFixed 2 :=
  conditional_k2_from_sameBandCarryAwarePQS_supply
    (sameBandCarryAwarePQSSupply_of_positiveBoxSupply hSupply)

theorem conditional_k2_from_positiveDensitySameBandCarryAwarePQSBox_supply
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensitySameBandCarryAwarePQSBoxesK2 num den) :
    erdosFixed 2 :=
  conditional_k2_from_positiveSameBandCarryAwarePQSBox_supply
    (positiveBoxSupply_of_positiveDensityBoxSupply hSupply)

theorem erdosK2_from_pattern_supply
    (hSupply : InfinitelyManyPatternK2) :
    erdosK2 :=
  conditional_k2_from_pattern_supply hSupply

theorem erdosK2_from_pattern_witness_supply
    (hSupply : InfinitelyManyPatternWitnessK2) :
    erdosK2 :=
  conditional_k2_from_pattern_witness_supply hSupply

theorem erdosK2_from_carryAwarePQS_supply
    (hSupply : InfinitelyManyCarryAwarePQSK2) :
    erdosK2 :=
  conditional_k2_from_carryAwarePQS_supply hSupply

theorem erdosK2_from_sameBandCarryAwarePQS_supply
    (hSupply : InfinitelyManySameBandCarryAwarePQSK2) :
    erdosK2 :=
  conditional_k2_from_sameBandCarryAwarePQS_supply hSupply

theorem erdosK2_from_positiveSameBandCarryAwarePQSBox_supply
    (hSupply : InfinitelyManyPositiveSameBandCarryAwarePQSBoxesK2) :
    erdosK2 :=
  conditional_k2_from_positiveSameBandCarryAwarePQSBox_supply hSupply

theorem erdosK2_from_positiveDensitySameBandCarryAwarePQSBox_supply
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensitySameBandCarryAwarePQSBoxesK2 num den) :
    erdosK2 :=
  conditional_k2_from_positiveDensitySameBandCarryAwarePQSBox_supply hSupply

theorem erdosK2_of_carryAwareShiftedDivisorSupply
    (hSupply : CarryAwareShiftedDivisorSupplyK2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact conditional_k2_from_positiveDensitySameBandCarryAwarePQSBox_supply
    hDensitySupply

theorem erdosK2_of_switchedSupply
    (hSupply : SwitchedSemiprimeSupplyK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨cfg, n, s1, s2, M1, M2, hnN, hW⟩
  exact ⟨n, hnN, erdosAt2_of_switchedSupplyWitness hW⟩

theorem erdosK2_of_switchedSBoxedSupply
    (hSupply : SwitchedSBoxedSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_switchedSupply
    (switchedSupply_of_switchedSBoxedSupply hSupply)

theorem erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (hSupply : InfinitelyManyPositiveSBoxedAffineCorrelationBoxesK2) :
    erdosFixed 2 :=
  erdosK2_of_switchedSBoxedSupply
    (switchedSBoxedSupply_of_positiveSBoxedAffineCorrelationBoxSupply hSupply)

theorem erdosK2_of_positiveDensitySBoxedAffineCorrelationBoxSupply
    {num den : ℕ}
    (hSupply :
      InfinitelyManyPositiveDensitySBoxedAffineCorrelationBoxesK2 num den) :
    erdosFixed 2 :=
  erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (positiveSBoxedAffineCorrelationBoxSupply_of_positiveDensity hSupply)

theorem erdosK2_of_sBoxedAffineCorrelationSupply
    (hSupply : SBoxedAffineCorrelationSupplyK2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveDensitySBoxedAffineCorrelationBoxSupply
    hDensitySupply

theorem erdosK2_of_averageOverSBoxedAffineCorrelationSupply
    (hSupply : AverageOverSBoxedAffineCorrelationSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (positiveSBoxedAffineCorrelationBoxSupply_of_averageOverSBoxedAffineCorrelationSupply
      hSupply)

theorem erdosK2_of_weightedSBoxedAffineCorrelationSupply
    (hSupply : WeightedSBoxedAffineCorrelationSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_averageOverSBoxedAffineCorrelationSupply
    (averageOverSBoxedAffineCorrelationSupply_of_weightedSBoxedAffineCorrelationSupply
      hSupply)

theorem erdosK2_of_fixedSBoxedAffineCorrelationSupply
    {s1 s2 : ℕ}
    (hSupply : FixedSBoxedAffineCorrelationSupplyK2 s1 s2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (positiveSBoxedAffineCorrelationBoxSupply_of_positiveFixed
      (positiveFixedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
        hDensitySupply))

theorem erdosK2_of_fixedWeightedSBoxedAffineCorrelationSupply
    {s1 s2 : ℕ}
    (hSupply : FixedWeightedSBoxedAffineCorrelationSupplyK2 s1 s2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (positiveSBoxedAffineCorrelationBoxSupply_of_positiveFixed
      (positiveFixedSBoxedAffineCorrelationBoxSupply_of_positiveWeighted
        (positiveWeightedFixedSBoxedAffineCorrelationBoxSupply_of_positiveDensity
          hDensitySupply)))

theorem erdosK2_of_fixedOneOneWeightedSBoxedAffineCorrelationSupply
    (hSupply : FixedOneOneWeightedSBoxedAffineCorrelationSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_fixedWeightedSBoxedAffineCorrelationSupply hSupply

theorem erdosK2_of_positiveFixedOneOnePrimeQuadrupleSupply
    (hSupply : InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2) :
    erdosFixed 2 :=
  erdosK2_of_switchedSBoxedSupply
    (switchedSBoxedSupply_of_positiveFixedOneOnePrimeQuadrupleSupply hSupply)

theorem erdosK2_of_positiveFixedOneOnePrimeQuadrupleSupply_via_weightedAffine
    (hSupply : InfinitelyManyPositiveFixedOneOnePrimeQuadrupleBoxesK2) :
    erdosFixed 2 :=
  erdosK2_of_positiveSBoxedAffineCorrelationBoxSupply
    (positiveSBoxedAffineCorrelationBoxSupply_of_positiveFixed
      (positiveFixedSBoxedAffineCorrelationBoxSupply_of_positiveWeighted
        (positiveWeightedFixedSBoxedAffineCorrelationBoxSupply_of_positiveFixedOneOnePrimeQuadrupleSupply
          hSupply)))

theorem erdosK2_of_fixedOneOnePrimeQuadrupleSupply
    (hSupply : FixedOneOnePrimeQuadrupleSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_switchedSBoxedSupply
    (switchedSBoxedSupply_of_fixedOneOnePrimeQuadrupleSupply hSupply)

theorem erdosK2_of_fixedOneOnePrimeQuadrupleSupply_via_weightedAffine
    (hSupply : FixedOneOnePrimeQuadrupleSupplyK2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveFixedOneOnePrimeQuadrupleSupply_via_weightedAffine
    (positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveDensity
      hDensitySupply)

theorem erdosK2_of_fixedOneOneRatioPrimeQuadrupleSupply
    (hSupply : FixedOneOneRatioPrimeQuadrupleSupplyK2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveFixedOneOnePrimeQuadrupleSupply
    (positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveRatioSupply
      (positiveFixedOneOneRatioPrimeQuadrupleBoxSupply_of_positiveDensity
        hDensitySupply))

theorem erdosK2_of_fixedOneOneCleanRatioPrimeQuadrupleSupply
    (hSupply : FixedOneOneCleanRatioPrimeQuadrupleSupplyK2) :
    erdosFixed 2 := by
  rcases hSupply with ⟨num, den, hDensitySupply⟩
  exact erdosK2_of_positiveFixedOneOnePrimeQuadrupleSupply
    (positiveFixedOneOnePrimeQuadrupleBoxSupply_of_positiveRatioSupply
      (positiveFixedOneOneRatioPrimeQuadrupleBoxSupply_of_positiveCleanRatioSupply
        (positiveFixedOneOneCleanRatioPrimeQuadrupleBoxSupply_of_positiveDensity
          hDensitySupply)))

theorem erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply
    (hSupply : FixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupplyK2) :
    erdosFixed 2 := by
  intro N
  rcases hSupply N with ⟨_cfg, u, hNu, hRaw⟩
  exact ⟨u.n, hNu,
    erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood hRaw⟩

theorem erdosK2_of_positiveFixedOneOneRawCleanRatioPrimeQuadrupleSupply
    (hSupply :
      InfinitelyManyPositiveFixedOneOneRawCleanRatioPrimeQuadrupleBoxesK2) :
    erdosFixed 2 :=
  erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply
    (fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_positiveBoxSupply
      hSupply)

theorem erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadrupleSupply
    (hSupply : FixedOneOneRawCleanRatioPrimeQuadrupleSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply
    (fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_densitySupply
      hSupply)

theorem erdosK2_of_dicksonFamilySupply
    (hSupply : DicksonFamilySupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply
    (fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonFamilySupply
      hSupply)

theorem erdosK2_of_dicksonAPFamilySupply
    (hSupply : DicksonAPFamilySupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply
    (fixedOneOneRawCleanRatioPrimeQuadruplePointwiseSupply_of_dicksonAPFamilySupply
      hSupply)

theorem erdosK2_of_dicksonAP4PrimeSupply
    (hSupply : DicksonAP4PrimeSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAPFamilySupply
    (dicksonAPFamilySupply_of_dicksonAP4PrimeSupply hSupply)

theorem erdosK2_of_dicksonAP4ClosedPrimeSupply
    (hSupply : DicksonAP4ClosedPrimeSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP4PrimeSupply
    ((dicksonAP4PrimeSupply_iff_closed).2 hSupply)

theorem erdosK2_of_dicksonAP4LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP4LinearFormsK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP4ClosedPrimeSupply
    ((dicksonAP4ClosedPrimeSupply_iff_linearFormsPrimeTuple).2 hSupply)

theorem erdosK2_of_dicksonAP4Conjecture
    (hSupply : DicksonAP4ConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP4LinearFormsPrimeTuple hSupply

theorem erdosK2_of_dicksonAP3PrimeSupply
    (hSupply : DicksonAP3PrimeSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAPFamilySupply
    (dicksonAPFamilySupply_of_dicksonAP3PrimeSupply hSupply)

theorem erdosK2_of_dicksonAP3ClosedPrimeSupply
    (hSupply : DicksonAP3ClosedPrimeSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3PrimeSupply
    ((dicksonAP3PrimeSupply_iff_closed).2 hSupply)

theorem erdosK2_of_dicksonAP3QualitativePrimeTuple
    (hSupply : DicksonAP3QualitativePrimeTupleK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3ClosedPrimeSupply
    (dicksonAP3ClosedPrimeSupply_of_qualitative hSupply)

theorem erdosK2_of_dicksonAP3LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP3LinearFormsK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3QualitativePrimeTuple
    ((dicksonAP3QualitativePrimeTuple_iff_linearForms).2 hSupply)

theorem erdosK2_of_dicksonAP3Conjecture
    (hSupply : DicksonAP3ConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3LinearFormsPrimeTuple hSupply

theorem erdosK2_of_dicksonAP3ClosedForms
    (hSupply :
      ∀ U : ℕ, ∃ u : ℕ,
        U ≤ u ∧
        Nat.Prime (576 * u + 29) ∧
        Nat.Prime (912 * u + 65) ∧
        Nat.Prime (456 * u + 23) ∧
        Nat.Prime (576 * u + 41)) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3Conjecture
    ((dicksonAP3Conjecture_iff_closedForms).2 hSupply)

theorem erdosK2_of_dicksonAP3ClosedFormsSupply
    (hSupply : DicksonAP3ClosedFormsSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3Conjecture
    ((dicksonAP3ClosedFormsSupply_iff_conjecture).1 hSupply)

theorem erdosK2_of_dicksonAP12ClosedFormsSupply
    (hSupply : DicksonAP12ClosedFormsSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3ClosedFormsSupply
    ((dicksonAP12ClosedFormsSupply_iff_AP3ClosedFormsSupply).1 hSupply)

theorem erdosK2_of_dicksonAP12ClosedForms
    (hSupply :
      ∀ U : ℕ, ∃ u : ℕ,
        U ≤ u ∧
        Nat.Prime (dicksonP1K2 (12 * u)) ∧
        Nat.Prime (dicksonQ1K2 (12 * u)) ∧
        Nat.Prime (dicksonP2K2 (12 * u)) ∧
        Nat.Prime (dicksonQ2K2 (12 * u))) :
    erdosFixed 2 := by
  have hClosed : DicksonAP12ClosedFormsSupplyK2 := by
    simpa [DicksonAP12ClosedFormsSupplyK2] using hSupply
  exact erdosK2_of_dicksonAP12ClosedFormsSupply hClosed

theorem erdosK2_of_explicitDicksonAP12PrimeTupleSupply
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP12ClosedFormsSupply
    ((explicitDicksonAP12PrimeTupleSupply_iff_closedFormsSupply).1 hSupply)

theorem erdosK2_of_explicitDicksonMod12PrimeTupleSupply
    (hSupply : ExplicitDicksonMod12PrimeTupleSupplyK2) :
    erdosFixed 2 :=
  erdosK2_of_explicitDicksonAP12PrimeTupleSupply
    (explicitDicksonAP12PrimeTupleSupply_of_mod12 hSupply)

theorem erdosK2_of_dicksonAP12Conjecture
    (hSupply : DicksonAP12ConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP12ClosedFormsSupply
    ((dicksonAP12Conjecture_iff_closedFormsSupply).1 hSupply)

theorem erdosK2_of_dicksonAP12LinearFormsPrimeTuple
    (hSupply : LinearFormsPrimeTupleSupplyK2 dicksonAP12LinearFormsK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP12Conjecture
    (dicksonAP12Conjecture_of_dicksonAP12LinearFormsPrimeTuple hSupply)

theorem erdosK2_of_dicksonConjectureK2_via_explicitMod12
    (hDickson : DicksonConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_explicitDicksonMod12PrimeTupleSupply
    (explicitDicksonMod12PrimeTupleSupply_of_dicksonConjectureK2 hDickson)

theorem erdosK2_of_dicksonConjectureK2_via_AP4
    (hDickson : DicksonConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP4ClosedPrimeSupply
    (dicksonAP4ClosedPrimeSupply_of_dicksonConjectureK2 hDickson)

theorem erdosK2_of_dicksonConjectureK2
    (hDickson : DicksonConjectureK2) :
    erdosFixed 2 :=
  erdosK2_of_dicksonAP3LinearFormsPrimeTuple
    (hDickson dicksonAP3LinearFormsK2 dicksonAP3LinearForms_admissible)

theorem dicksonAP4_1329_coordinates :
    dicksonAP4P1K2 1329 = 255197 ∧
    dicksonAP4Q1K2 1329 = 404081 ∧
    dicksonAP4P2K2 1329 = 202031 ∧
    dicksonAP4Q2K2 1329 = 255209 := by
  norm_num [dicksonAP4P1K2, dicksonAP4Q1K2, dicksonAP4P2K2,
    dicksonAP4Q2K2]

theorem dicksonAP4LinearForms_1329_primeTupleAt :
    LinearFormsPrimeTupleAtK2 dicksonAP4LinearFormsK2 1329 := by
  intro L hL
  have hCases :
      L = { coeff := 192, offset := 29 } ∨
      L = { coeff := 304, offset := 65 } ∨
      L = { coeff := 152, offset := 23 } ∨
      L = { coeff := 192, offset := 41 } := by
    simpa [dicksonAP4LinearFormsK2] using hL
  rcases hCases with rfl | rfl | rfl | rfl
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]

theorem dicksonAP4LinearForms_has_primeTupleAt :
    ∃ t : ℕ, LinearFormsPrimeTupleAtK2 dicksonAP4LinearFormsK2 t :=
  ⟨1329, dicksonAP4LinearForms_1329_primeTupleAt⟩

theorem dicksonAP4_1329_n_eq :
    dicksonAP4NK2 1329 = 103120258956 := by
  norm_num [dicksonAP4NK2]

theorem dicksonAP3LinearForms_443_primeTupleAt :
    LinearFormsPrimeTupleAtK2 dicksonAP3LinearFormsK2 443 := by
  intro L hL
  have hCases :
      L = { coeff := 576, offset := 29 } ∨
      L = { coeff := 912, offset := 65 } ∨
      L = { coeff := 456, offset := 23 } ∨
      L = { coeff := 576, offset := 41 } := by
    simpa [dicksonAP3LinearFormsK2] using hL
  rcases hCases with rfl | rfl | rfl | rfl
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]
  · norm_num [LinearFormK2.eval]

theorem dicksonAP3LinearForms_has_primeTupleAt :
    ∃ u : ℕ, LinearFormsPrimeTupleAtK2 dicksonAP3LinearFormsK2 u :=
  ⟨443, dicksonAP3LinearForms_443_primeTupleAt⟩

theorem dicksonAP12LinearForms_443_primeTupleAt :
    LinearFormsPrimeTupleAtK2 dicksonAP12LinearFormsK2 443 := by
  rw [dicksonAP12LinearForms_eq_AP3]
  exact dicksonAP3LinearForms_443_primeTupleAt

theorem dicksonAP12LinearForms_has_primeTupleAt :
    ∃ u : ℕ, LinearFormsPrimeTupleAtK2 dicksonAP12LinearFormsK2 u :=
  ⟨443, dicksonAP12LinearForms_443_primeTupleAt⟩

theorem dicksonAP3ClosedForms_443_primeTupleAt :
    Nat.Prime (576 * 443 + 29) ∧
    Nat.Prime (912 * 443 + 65) ∧
    Nat.Prime (456 * 443 + 23) ∧
    Nat.Prime (576 * 443 + 41) := by
  norm_num

theorem dicksonAP3ClosedForms_has_primeTupleAt :
    ∃ u : ℕ,
      Nat.Prime (576 * u + 29) ∧
      Nat.Prime (912 * u + 65) ∧
      Nat.Prime (456 * u + 23) ∧
      Nat.Prime (576 * u + 41) :=
  ⟨443, dicksonAP3ClosedForms_443_primeTupleAt⟩

theorem dicksonAP12ClosedForms_443_primeTupleAt :
    Nat.Prime (dicksonP1K2 (12 * 443)) ∧
    Nat.Prime (dicksonQ1K2 (12 * 443)) ∧
    Nat.Prime (dicksonP2K2 (12 * 443)) ∧
    Nat.Prime (dicksonQ2K2 (12 * 443)) := by
  norm_num [dicksonP1K2, dicksonQ1K2, dicksonP2K2, dicksonQ2K2]

theorem dicksonAP12ClosedForms_has_primeTupleAt :
    ∃ u : ℕ,
      Nat.Prime (dicksonP1K2 (12 * u)) ∧
      Nat.Prime (dicksonQ1K2 (12 * u)) ∧
      Nat.Prime (dicksonP2K2 (12 * u)) ∧
      Nat.Prime (dicksonQ2K2 (12 * u)) :=
  ⟨443, dicksonAP12ClosedForms_443_primeTupleAt⟩

theorem erdosAt2_of_dicksonAP3ClosedFormsPrimeAt
    {u : ℕ} (hu : 1 ≤ u)
    (hp1 : Nat.Prime (576 * u + 29))
    (hq1 : Nat.Prime (912 * u + 65))
    (hp2 : Nat.Prime (456 * u + 23))
    (hq2 : Nat.Prime (576 * u + 41)) :
    erdosAt 2 (dicksonAP3NK2 u) := by
  rcases dicksonAP3RawQuadrupleK2_closed u with
    ⟨hp1eq, hq1eq, hp2eq, hq2eq⟩
  have hp1raw :
      Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.p := by
    simpa [hp1eq, dicksonAP3P1K2] using hp1
  have hq1raw :
      Nat.Prime (dicksonAP3RawQuadrupleK2 u).left.q := by
    simpa [hq1eq, dicksonAP3Q1K2] using hq1
  have hp2raw :
      Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.p := by
    simpa [hp2eq, dicksonAP3P2K2] using hp2
  have hq2raw :
      Nat.Prime (dicksonAP3RawQuadrupleK2 u).right.q := by
    simpa [hq2eq, dicksonAP3Q2K2] using hq2
  have hgood :
      FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2
        (dicksonAP3ParamsK2 u hu) (dicksonAP3RawQuadrupleK2 u) := by
    simpa [dicksonAP3RawQuadrupleK2] using
      dicksonAPFamilyRawCleanRatioGood_of_sideConditions
        (cfg := dicksonAP3ParamsK2 u hu) (t := 3 * u)
        (by nlinarith [hu] : 1 ≤ 3 * u)
        (dicksonAP3FamilyRawSideConditions_of_primes
          (u := u) (hu := hu) hp1raw hq1raw hp2raw hq2raw)
  simpa [dicksonAP3_n_eq] using
    erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood hgood

theorem erdosAt2_dicksonAP3ClosedForms_443 :
    erdosAt 2 (dicksonAP3NK2 443) := by
  rcases dicksonAP3ClosedForms_443_primeTupleAt with
    ⟨hp1, hq1, hp2, hq2⟩
  exact erdosAt2_of_dicksonAP3ClosedFormsPrimeAt
    (u := 443) (by norm_num) hp1 hq1 hp2 hq2

theorem erdosAt2_of_dicksonAP12ClosedFormsPrimeAt
    {u : ℕ} (hu : 1 ≤ u)
    (hp1 : Nat.Prime (dicksonP1K2 (12 * u)))
    (hq1 : Nat.Prime (dicksonQ1K2 (12 * u)))
    (hp2 : Nat.Prime (dicksonP2K2 (12 * u)))
    (hq2 : Nat.Prime (dicksonQ2K2 (12 * u))) :
    erdosAt 2 (dicksonAP3NK2 u) := by
  apply erdosAt2_of_dicksonAP3ClosedFormsPrimeAt (u := u) hu
  · convert hp1 using 1
    unfold dicksonP1K2
    ring
  · convert hq1 using 1
    unfold dicksonQ1K2
    ring
  · convert hp2 using 1
    unfold dicksonP2K2
    ring
  · convert hq2 using 1
    unfold dicksonQ2K2
    ring

theorem erdosAt2_of_explicitDicksonAP12PrimeTupleAt
    {u : ℕ} (hu : 1 ≤ u)
    (hp1 : Nat.Prime (48 * (12 * u) + 29))
    (hq1 : Nat.Prime (76 * (12 * u) + 65))
    (hp2 : Nat.Prime (38 * (12 * u) + 23))
    (hq2 : Nat.Prime (48 * (12 * u) + 41)) :
    erdosAt 2 (dicksonAP3NK2 u) := by
  apply erdosAt2_of_dicksonAP12ClosedFormsPrimeAt (u := u) hu
  · simpa [dicksonP1K2] using hp1
  · simpa [dicksonQ1K2] using hq1
  · simpa [dicksonP2K2] using hp2
  · simpa [dicksonQ2K2] using hq2

theorem erdosAt2_of_explicitDicksonMod12PrimeTupleAt
    {m : ℕ} (hm_pos : 1 ≤ m) (hm12 : 12 ∣ m)
    (hprime : ExplicitDicksonPrimeTupleAtK2 m) :
    erdosAt 2 (dicksonFamilyNK2 m) := by
  rcases hm12 with ⟨u, rfl⟩
  rcases hprime with ⟨hp1, hq1, hp2, hq2⟩
  have hu : 1 ≤ u := by omega
  have hAt :
      erdosAt 2 (dicksonAP3NK2 u) :=
    erdosAt2_of_explicitDicksonAP12PrimeTupleAt
      (u := u) hu hp1 hq1 hp2 hq2
  simpa [dicksonAP3NK2_eq_dicksonFamilyNK2] using hAt

theorem explicitDicksonAP12PrimeTupleSupply_has_quadratic_erdos_witnesses
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    ∀ N : ℕ, ∃ u : ℕ,
      N ≤ dicksonAP3NK2 u ∧ erdosAt 2 (dicksonAP3NK2 u) := by
  intro N
  rcases hSupply (max N 1) with ⟨u, hmax, hp1, hq1, hp2, hq2⟩
  have hNu : N ≤ u := le_trans (le_max_left N 1) hmax
  have hu : 1 ≤ u := le_trans (le_max_right N 1) hmax
  exact ⟨u, le_trans hNu (dicksonAP3NK2_ge_parameter u),
    erdosAt2_of_explicitDicksonAP12PrimeTupleAt hu hp1 hq1 hp2 hq2⟩

theorem explicitDicksonMod12PrimeTupleSupply_has_original_parameter_erdos_witnesses
    (hSupply : ExplicitDicksonMod12PrimeTupleSupplyK2) :
    ∀ N : ℕ, ∃ m : ℕ,
      N ≤ dicksonFamilyNK2 m ∧ erdosAt 2 (dicksonFamilyNK2 m) := by
  intro N
  rcases hSupply (max N 1) with ⟨m, hmax, hm12, hprime⟩
  have hNm : N ≤ m := le_trans (le_max_left N 1) hmax
  have hm_pos : 1 ≤ m := le_trans (le_max_right N 1) hmax
  have hm_le_n : m ≤ dicksonFamilyNK2 m := by
    unfold dicksonFamilyNK2
    nlinarith [sq_nonneg (m : ℤ)]
  exact ⟨m, le_trans hNm hm_le_n,
    erdosAt2_of_explicitDicksonMod12PrimeTupleAt hm_pos hm12 hprime⟩

theorem erdosK2_of_explicitDicksonAP12PrimeTupleSupply_via_quadratic_witnesses
    (hSupply : ExplicitDicksonAP12PrimeTupleSupplyK2) :
    erdosFixed 2 := by
  intro N
  rcases explicitDicksonAP12PrimeTupleSupply_has_quadratic_erdos_witnesses
      hSupply N with ⟨u, hN, hAt⟩
  exact ⟨dicksonAP3NK2 u, hN, hAt⟩

theorem erdosAt2_dicksonAP12ClosedForms_443 :
    erdosAt 2 (dicksonAP3NK2 443) := by
  rcases dicksonAP12ClosedForms_443_primeTupleAt with
    ⟨hp1, hq1, hp2, hq2⟩
  exact erdosAt2_of_dicksonAP12ClosedFormsPrimeAt
    (u := 443) (by norm_num) hp1 hq1 hp2 hq2

/--
Small fixed-box four-prime witness reported by the fixed-correlation search.

The associated Erdos witness is `2646036`, since
`2646036 + 1 = 1229 * 2153` and
`2646036 + 2 = 2 * (997 * 1327)`.
-/
theorem fixedBox_2646036_primeQuadruple :
    Nat.Prime 1229 ∧
    Nat.Prime 2153 ∧
    Nat.Prime 997 ∧
    Nat.Prime 1327 ∧
    1229 * 2153 + 1 = 2 * (997 * 1327) ∧
    1229 < 2153 ∧
    3 * 1229 < 2 * 2153 ∧
    2153 < 2 * 1229 ∧
    997 < 1327 ∧
    5 * 997 < 4 * 1327 ∧
    3 * 1327 < 4 * 997 := by
  norm_num

theorem erdosAt2_2646036 : erdosAt 2 2646036 := by
  have hp1 : Nat.Prime 1229 := fixedBox_2646036_primeQuadruple.1
  have hq1 : Nat.Prime 2153 := fixedBox_2646036_primeQuadruple.2.1
  have hp2 : Nat.Prime 997 := fixedBox_2646036_primeQuadruple.2.2.1
  have hq2 : Nat.Prime 1327 := fixedBox_2646036_primeQuadruple.2.2.2.1
  have hBudget1229 :
      2 * (window 2646036 2).factorization 1229 ≤
        (centralBinom 2646036).factorization 1229 := by
    exact window_two_left_prime_budget_of_sawtooth
      (p := 1229) (n := 2646036) (c := 2153)
      (B := Nat.log 1229 (2 * 2646036) + 3)
      hp1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget2153 :
      2 * (window 2646036 2).factorization 2153 ≤
        (centralBinom 2646036).factorization 2153 := by
    exact window_two_left_prime_budget_of_sawtooth
      (p := 2153) (n := 2646036) (c := 1229)
      (B := Nat.log 2153 (2 * 2646036) + 3)
      hq1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget997 :
      2 * (window 2646036 2).factorization 997 ≤
        (centralBinom 2646036).factorization 997 := by
    exact window_two_right_prime_budget_of_sawtooth
      (p := 997) (n := 2646036) (c := 2 * 1327)
      (B := Nat.log 997 (2 * 2646036) + 3)
      hp2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget1327 :
      2 * (window 2646036 2).factorization 1327 ≤
        (centralBinom 2646036).factorization 1327 := by
    exact window_two_right_prime_budget_of_sawtooth
      (p := 1327) (n := 2646036) (c := 2 * 997)
      (B := Nat.log 1327 (2 * 2646036) + 3)
      hq2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hwin : (window 2646036 2) ^ 2 ∣ centralBinom 2646036 := by
    refine window_sq_dvd_centralBinom_of_prime_budget ?_
    intro p hp
    by_cases hpTwo : p = 2
    · subst p
      exact window_two_two_prime_budget_of_mod32_eq_20
        (n := 2646036)
        (B := Nat.log 2 (2 * 2646036) + 6)
        (by norm_num) (by omega) (by omega)
    by_cases hpEqP1 : p = 1229
    · subst p
      exact hBudget1229
    by_cases hpEqQ1 : p = 2153
    · subst p
      exact hBudget2153
    by_cases hpEqP2 : p = 997
    · subst p
      exact hBudget997
    by_cases hpEqQ2 : p = 1327
    · subst p
      exact hBudget1327
    have hnot_window : ¬ p ∣ window 2646036 2 := by
      intro hdiv
      have hprod : p ∣ (2646036 + 1) * (2646036 + 2) := by
        simpa [window_two] using hdiv
      rcases (hp.dvd_mul).1 hprod with hleft | hright
      · have hleft' : p ∣ 1229 * 2153 := by
          norm_num at hleft
          exact hleft
        rcases (hp.dvd_mul).1 hleft' with hP1 | hQ1
        · have heq : 1229 = p :=
            (Nat.Prime.dvd_iff_eq hp1 hp.ne_one).1 hP1
          exact hpEqP1 heq.symm
        · have heq : 2153 = p :=
            (Nat.Prime.dvd_iff_eq hq1 hp.ne_one).1 hQ1
          exact hpEqQ1 heq.symm
      · have hright' : p ∣ 2 * (997 * 1327) := by
          norm_num at hright
          exact hright
        rcases (hp.dvd_mul).1 hright' with hTwo | hP2Q2
        · have heq : 2 = p :=
            (Nat.Prime.dvd_iff_eq Nat.prime_two hp.ne_one).1 hTwo
          exact hpTwo heq.symm
        · rcases (hp.dvd_mul).1 hP2Q2 with hP2 | hQ2
          · have heq : 997 = p :=
              (Nat.Prime.dvd_iff_eq hp2 hp.ne_one).1 hP2
            exact hpEqP2 heq.symm
          · have heq : 1327 = p :=
              (Nat.Prime.dvd_iff_eq hq2 hp.ne_one).1 hQ2
            exact hpEqQ2 heq.symm
    have hzero : (window 2646036 2).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot_window
    simp [hzero]
  exact (erdosAt2_iff_window_two_sq_dvd_centralBinom
    (n := 2646036) (by norm_num)).2 hwin

/--
First fixed-box prime quadruple reported by the unscaled Dickson-family search.

This is a fixed-box sanity witness only.  Its recovered `n` is `8 mod 16`, so it
does not pass the `FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2` sufficient
condition used for the AP12/AP3 bridge below.
-/
theorem dicksonFamily_1701_coordinates :
    dicksonP1K2 1701 = 81677 ∧
    dicksonQ1K2 1701 = 129341 ∧
    dicksonP2K2 1701 = 64661 ∧
    dicksonQ2K2 1701 = 81689 := by
  norm_num [dicksonP1K2, dicksonQ1K2, dicksonP2K2, dicksonQ2K2]

theorem dicksonFamily_1701_primeTupleAt :
    Nat.Prime (dicksonP1K2 1701) ∧
    Nat.Prime (dicksonQ1K2 1701) ∧
    Nat.Prime (dicksonP2K2 1701) ∧
    Nat.Prime (dicksonQ2K2 1701) := by
  norm_num [dicksonP1K2, dicksonQ1K2, dicksonP2K2, dicksonQ2K2]

theorem dicksonFamily_1701_fixedBoxPrimeQuadruple :
    Nat.Prime (dicksonRawQuadrupleK2 1701).left.p ∧
    Nat.Prime (dicksonRawQuadrupleK2 1701).left.q ∧
    Nat.Prime (dicksonRawQuadrupleK2 1701).right.p ∧
    Nat.Prime (dicksonRawQuadrupleK2 1701).right.q ∧
    (dicksonRawQuadrupleK2 1701).left.p *
        (dicksonRawQuadrupleK2 1701).left.q + 1 =
      2 * ((dicksonRawQuadrupleK2 1701).right.p *
        (dicksonRawQuadrupleK2 1701).right.q) ∧
    (dicksonRawQuadrupleK2 1701).left.p <
      (dicksonRawQuadrupleK2 1701).left.q ∧
    3 * (dicksonRawQuadrupleK2 1701).left.p <
      2 * (dicksonRawQuadrupleK2 1701).left.q ∧
    (dicksonRawQuadrupleK2 1701).left.q <
      2 * (dicksonRawQuadrupleK2 1701).left.p ∧
    (dicksonRawQuadrupleK2 1701).right.p <
      (dicksonRawQuadrupleK2 1701).right.q ∧
    5 * (dicksonRawQuadrupleK2 1701).right.p <
      4 * (dicksonRawQuadrupleK2 1701).right.q ∧
    3 * (dicksonRawQuadrupleK2 1701).right.q <
      4 * (dicksonRawQuadrupleK2 1701).right.p := by
  norm_num [dicksonRawQuadrupleK2, dicksonP1K2, dicksonQ1K2,
    dicksonP2K2, dicksonQ2K2]

theorem dicksonFamily_1701_n_eq :
    (dicksonRawQuadrupleK2 1701).n = 10564184856 := by
  norm_num [FixedOneOneRawPrimeQuadrupleK2.n, dicksonRawQuadrupleK2,
    dicksonP1K2, dicksonQ1K2]

theorem dicksonFamily_1701_n_mod16 :
    (dicksonRawQuadrupleK2 1701).n % 16 = 8 := by
  rw [dicksonFamily_1701_n_eq]

theorem dicksonFamily_1701_not_rawCleanRatioGood
    (cfg : K2Params) :
    ¬ FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2 cfg
      (dicksonRawQuadrupleK2 1701) := by
  intro hgood
  rcases hgood with ⟨_hxLo, _hxHi, hmod, _hrest⟩
  rw [dicksonFamily_1701_n_mod16] at hmod
  norm_num at hmod

theorem dicksonFamily_1701_n_mod32 :
    (dicksonRawQuadrupleK2 1701).n % 32 = 24 := by
  rw [dicksonFamily_1701_n_eq]

theorem erdosAt2_10564184856 : erdosAt 2 10564184856 := by
  have hp1 : Nat.Prime 81677 := by norm_num
  have hq1 : Nat.Prime 129341 := by norm_num
  have hp2 : Nat.Prime 64661 := by norm_num
  have hq2 : Nat.Prime 81689 := by norm_num
  have hBudget81677 :
      2 * (window 10564184856 2).factorization 81677 ≤
        (centralBinom 10564184856).factorization 81677 := by
    exact window_two_left_prime_budget_of_sawtooth
      (p := 81677) (n := 10564184856) (c := 129341)
      (B := Nat.log 81677 (2 * 10564184856) + 3)
      hp1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget129341 :
      2 * (window 10564184856 2).factorization 129341 ≤
        (centralBinom 10564184856).factorization 129341 := by
    exact window_two_left_prime_budget_of_sawtooth
      (p := 129341) (n := 10564184856) (c := 81677)
      (B := Nat.log 129341 (2 * 10564184856) + 3)
      hq1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget64661 :
      2 * (window 10564184856 2).factorization 64661 ≤
        (centralBinom 10564184856).factorization 64661 := by
    exact window_two_right_prime_budget_of_sawtooth
      (p := 64661) (n := 10564184856) (c := 2 * 81689)
      (B := Nat.log 64661 (2 * 10564184856) + 3)
      hp2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hBudget81689 :
      2 * (window 10564184856 2).factorization 81689 ≤
        (centralBinom 10564184856).factorization 81689 := by
    exact window_two_right_prime_budget_of_sawtooth
      (p := 81689) (n := 10564184856) (c := 2 * 64661)
      (B := Nat.log 81689 (2 * 10564184856) + 3)
      hq2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [SawtoothInt]) (by omega) (by omega)
  have hwin : (window 10564184856 2) ^ 2 ∣
      centralBinom 10564184856 := by
    refine window_sq_dvd_centralBinom_of_prime_budget ?_
    intro p hp
    by_cases hpTwo : p = 2
    · subst p
      exact window_two_two_prime_budget_of_mod32_eq_24
        (n := 10564184856)
        (B := Nat.log 2 (2 * 10564184856) + 6)
        (by norm_num) (by omega) (by omega)
    by_cases hpEqP1 : p = 81677
    · subst p
      exact hBudget81677
    by_cases hpEqQ1 : p = 129341
    · subst p
      exact hBudget129341
    by_cases hpEqP2 : p = 64661
    · subst p
      exact hBudget64661
    by_cases hpEqQ2 : p = 81689
    · subst p
      exact hBudget81689
    have hnot_window : ¬ p ∣ window 10564184856 2 := by
      intro hdiv
      have hprod : p ∣ (10564184856 + 1) * (10564184856 + 2) := by
        simpa [window_two] using hdiv
      rcases (hp.dvd_mul).1 hprod with hleft | hright
      · have hleft' : p ∣ 81677 * 129341 := by
          norm_num at hleft
          exact hleft
        rcases (hp.dvd_mul).1 hleft' with hP1 | hQ1
        · have heq : 81677 = p :=
            (Nat.Prime.dvd_iff_eq hp1 hp.ne_one).1 hP1
          exact hpEqP1 heq.symm
        · have heq : 129341 = p :=
            (Nat.Prime.dvd_iff_eq hq1 hp.ne_one).1 hQ1
          exact hpEqQ1 heq.symm
      · have hright' : p ∣ 2 * (64661 * 81689) := by
          norm_num at hright
          exact hright
        rcases (hp.dvd_mul).1 hright' with hTwo | hP2Q2
        · have heq : 2 = p :=
            (Nat.Prime.dvd_iff_eq Nat.prime_two hp.ne_one).1 hTwo
          exact hpTwo heq.symm
        · rcases (hp.dvd_mul).1 hP2Q2 with hP2 | hQ2
          · have heq : 64661 = p :=
              (Nat.Prime.dvd_iff_eq hp2 hp.ne_one).1 hP2
            exact hpEqP2 heq.symm
          · have heq : 81689 = p :=
              (Nat.Prime.dvd_iff_eq hq2 hp.ne_one).1 hQ2
            exact hpEqQ2 heq.symm
    have hzero : (window 10564184856 2).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot_window
    simp [hzero]
  exact (erdosAt2_iff_window_two_sq_dvd_centralBinom
    (n := 10564184856) (by norm_num)).2 hwin

theorem erdosAt2_dicksonFamily_1701 :
    erdosAt 2 (dicksonRawQuadrupleK2 1701).n := by
  rw [dicksonFamily_1701_n_eq]
  exact erdosAt2_10564184856

/--
Concrete sanity witness inside the AP3 Dickson family.

This is a finite certificate only; it does not provide the still-open infinite
prime-tuple supply.
-/
theorem dicksonAP3_443_rawGood :
    FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2
      (dicksonAP3ParamsK2 443 (by norm_num))
      (dicksonAP3RawQuadrupleK2 443) := by
  have hp1 : Nat.Prime (dicksonAP3RawQuadrupleK2 443).left.p := by
    norm_num [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      dicksonRawQuadrupleK2, dicksonP1K2]
  have hq1 : Nat.Prime (dicksonAP3RawQuadrupleK2 443).left.q := by
    norm_num [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      dicksonRawQuadrupleK2, dicksonQ1K2]
  have hp2 : Nat.Prime (dicksonAP3RawQuadrupleK2 443).right.p := by
    norm_num [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      dicksonRawQuadrupleK2, dicksonP2K2]
  have hq2 : Nat.Prime (dicksonAP3RawQuadrupleK2 443).right.q := by
    norm_num [dicksonAP3RawQuadrupleK2, dicksonAPRawQuadrupleK2,
      dicksonRawQuadrupleK2, dicksonQ2K2]
  simpa [dicksonAP3RawQuadrupleK2] using
    dicksonAPFamilyRawCleanRatioGood_of_sideConditions
      (cfg := dicksonAP3ParamsK2 443 (by norm_num)) (t := 3 * 443)
      (by norm_num : 1 ≤ 3 * 443)
      (dicksonAP3FamilyRawSideConditions_of_primes
        (u := 443) (hu := by norm_num) hp1 hq1 hp2 hq2)

theorem dicksonAP3_443_n_eq :
    (dicksonAP3RawQuadrupleK2 443).n = 103120258956 := by
  rw [dicksonAP3_n_eq]
  unfold dicksonAP3NK2
  norm_num

theorem dicksonAP12_443_rawGood :
    FixedOneOneRawCleanRatioPrimeQuadrupleGoodK2
      (dicksonAP3ParamsK2 443 (by norm_num))
      (dicksonAP12RawQuadrupleK2 443) := by
  rw [dicksonAP12RawQuadrupleK2_eq_AP3]
  exact dicksonAP3_443_rawGood

theorem dicksonAP12_443_n_eq :
    (dicksonAP12RawQuadrupleK2 443).n = 103120258956 := by
  rw [dicksonAP12RawQuadrupleK2_eq_AP3]
  exact dicksonAP3_443_n_eq

theorem erdosAt2_dicksonAP3_443 :
    erdosAt 2 (dicksonAP3RawQuadrupleK2 443).n :=
  erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood
    dicksonAP3_443_rawGood

theorem erdosAt2_dicksonAP12_443 :
    erdosAt 2 (dicksonAP12RawQuadrupleK2 443).n :=
  erdosAt2_of_fixedOneOneRawCleanRatioPrimeQuadrupleGood
    dicksonAP12_443_rawGood

theorem erdosAt2_103120258956 : erdosAt 2 103120258956 := by
  simpa [dicksonAP3_443_n_eq] using erdosAt2_dicksonAP3_443

theorem erdosAt2_dicksonAP4_1329 :
    erdosAt 2 (dicksonAP4NK2 1329) := by
  rw [dicksonAP4_1329_n_eq]
  exact erdosAt2_103120258956

end Erdos727
