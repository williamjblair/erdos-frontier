/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/

import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.NormNum.Prime

namespace Erdos699

/-- The base-`p` digit at level `r`, with level zero the units digit. -/
def digit (k p r : ℕ) : ℕ :=
  k / p ^ r % p

/-- Digitwise domination of `k` by `n` in base `p`, checked on a finite safe range. -/
def dominated (k n p : ℕ) : Prop :=
  (Finset.range (max k n + 1)).filter (fun r => digit n p r < digit k p r) = ∅

instance (k n p : ℕ) : Decidable (dominated k n p) :=
  inferInstanceAs
    (Decidable ((Finset.range (max k n + 1)).filter
      (fun r => digit n p r < digit k p r) = ∅))

theorem dominated_iff_forall_mem_range (k n p : ℕ) :
    dominated k n p ↔
      ∀ r ∈ Finset.range (max k n + 1), digit k p r ≤ digit n p r := by
  classical
  unfold dominated
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h r hr
    exact Nat.not_lt.mp (h hr)
  · intro h r hr
    exact Nat.not_lt.mpr (h r hr)

theorem dominated_iff_forall_digits {k n p : ℕ} (hp : 2 ≤ p) :
    dominated k n p ↔ ∀ r : ℕ, digit k p r ≤ digit n p r := by
  classical
  constructor
  · intro h r
    by_cases hr : r ∈ Finset.range (max k n + 1)
    · exact (dominated_iff_forall_mem_range k n p).mp h r hr
    · have hle : max k n + 1 ≤ r := by
        exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hr)
      have hm_lt_r : max k n < r := Nat.lt_of_succ_le hle
      have hp_one : 1 < p := Nat.lt_of_lt_of_le one_lt_two hp
      have hr_lt_pow : r < p ^ r := Nat.lt_pow_self hp_one
      have hk_lt : k < p ^ r := (le_max_left k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      have hn_lt : n < p ^ r := (le_max_right k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      simp [digit, Nat.div_eq_of_lt hk_lt, Nat.div_eq_of_lt hn_lt]
  · intro h
    exact (dominated_iff_forall_mem_range k n p).mpr fun r _ => h r

theorem prime_not_dvd_small_choose_of_le {p a b : ℕ} (hp : p.Prime) (ha : a < p)
    (hb : b ≤ a) :
    ¬ p ∣ Nat.choose a b := by
  have hchoose_ne : Nat.choose a b ≠ 0 := Nat.choose_ne_zero hb
  intro hdiv
  have hfac_pos : 0 < (Nat.choose a b).factorization p :=
    hp.factorization_pos_of_dvd hchoose_ne hdiv
  have hfac_zero : (Nat.choose a b).factorization p = 0 :=
    Nat.factorization_choose_eq_zero_of_lt ha
  omega

theorem prime_not_dvd_finset_prod {α : Type*} {s : Finset α} {f : α → ℕ} {p : ℕ}
    (hp : p.Prime) (h : ∀ a ∈ s, ¬ p ∣ f a) :
    ¬ p ∣ s.prod f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hp.not_dvd_one
  | insert a s ha ih =>
      intro hdiv
      rw [Finset.prod_insert ha] at hdiv
      rcases hp.dvd_mul.mp hdiv with hpa | hps
      · exact h a (Finset.mem_insert_self a s) hpa
      · exact ih (fun x hx => h x (Finset.mem_insert_of_mem hx)) hps

theorem lucas_nonzero_mod_prime_iff_dominated {n k p : ℕ} (hp : p.Prime) :
    Nat.choose n k % p ≠ 0 ↔ dominated k n p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let a := max k n + 1
  have hp_one : 1 < p := hp.one_lt
  have hn_bound : n < p ^ a := by
    have hn_lt_a : n < a := (le_max_right k n).trans_lt (Nat.lt_succ_self _)
    exact hn_lt_a.trans (Nat.lt_pow_self hp_one)
  have hk_bound : k < p ^ a := by
    have hk_lt_a : k < a := (le_max_left k n).trans_lt (Nat.lt_succ_self _)
    exact hk_lt_a.trans (Nat.lt_pow_self hp_one)
  have hlucas :
      Nat.choose n k ≡
        ∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] :=
    Choose.lucas_theorem_nat (n := n) (k := k) (p := p) (a := a) hn_bound hk_bound
  constructor
  · intro hnonzero
    by_contra hdom
    rw [dominated_iff_forall_mem_range k n p] at hdom
    push Not at hdom
    obtain ⟨r, hr, hbad⟩ := hdom
    have hfactor_zero : Nat.choose (n / p ^ r % p) (k / p ^ r % p) = 0 :=
      Nat.choose_eq_zero_of_lt hbad
    have hprod_zero :
        (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) = 0 :=
      Finset.prod_eq_zero hr hfactor_zero
    rw [Nat.ModEq] at hlucas
    exact hnonzero (by simpa [hprod_zero] using hlucas)
  · intro hdom
    have hprod_not_dvd :
        ¬ p ∣ (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) := by
      refine prime_not_dvd_finset_prod hp ?_
      intro r hr
      apply prime_not_dvd_small_choose_of_le hp
      · exact Nat.mod_lt _ hp.pos
      · exact (dominated_iff_forall_mem_range k n p).mp hdom r hr
    rw [Nat.ModEq] at hlucas
    intro hzero
    have hprod_zero :
        (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) % p = 0 := by
      simpa [hlucas] using hzero
    exact hprod_not_dvd (Nat.dvd_iff_mod_eq_zero.mpr hprod_zero)

theorem prime_dvd_choose_of_not_dominated {n k p : ℕ} (hp : p.Prime)
    (hnd : ¬ dominated k n p) :
    p ∣ Nat.choose n k := by
  by_contra hnot_dvd
  have hnonzero : Nat.choose n k % p ≠ 0 := by
    intro hzero
    exact hnot_dvd (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  exact hnd ((lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero)

theorem not_dominated_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    ¬ dominated k n p := by
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_mod : n % p = n - p := by
    have hsub_lt : n - p < p := by
      rw [Nat.sub_lt_iff_lt_add hpn]
      simpa [two_mul, Nat.add_comm] using hn2p
    rw [Nat.mod_eq_sub_mod hpn]
    exact Nat.mod_eq_of_lt hsub_lt
  have hk_mod : k % p = k := Nat.mod_eq_of_lt hhigh
  have hle : k ≤ n - p := by
    simpa [digit, hn_mod, hk_mod] using hdigits
  omega

theorem prime_dvd_choose_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    p ∣ Nat.choose n k :=
  prime_dvd_choose_of_not_dominated hp
    (not_dominated_of_units_digit_lt hp hpn hn2p hlow hhigh)

/-- A prime `p` that is large enough for row `i` and divides both binomial coefficients. -/
def commonPrimeDivisor (n i j p : ℕ) : Prop :=
  p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j

theorem not_dominated_of_digit_lt {n k p r : ℕ} (hp : 2 ≤ p)
    (hbad : digit n p r < digit k p r) :
    ¬ dominated k n p := by
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp).mp hdom r
  omega

theorem commonPrimeDivisor_of_digit_failures {n i j p ri rj : ℕ}
    (hp : p.Prime) (hip : i ≤ p)
    (hi_bad : digit n p ri < digit i p ri)
    (hj_bad : digit n p rj < digit j p rj) :
    commonPrimeDivisor n i j p := by
  refine ⟨hp, hip, ?_, ?_⟩
  · exact prime_dvd_choose_of_not_dominated hp
      (not_dominated_of_digit_lt hp.two_le hi_bad)
  · exact prime_dvd_choose_of_not_dominated hp
      (not_dominated_of_digit_lt hp.two_le hj_bad)

/-- The consecutive-divisor kernel: two fixed divisors packed into products of
one, then two, consecutive gaps from `t`. -/
def consecutiveDivisorKernel (N1 N2 t : ℕ) : Prop :=
  N1 ∣ t * (t - 1) ∧ N2 ∣ t * (t - 1) * (t - 2)

/-- The same kernel with the problem's half-row bound. -/
def consecutiveDivisorKernelBelow (N1 N2 bound t : ℕ) : Prop :=
  2 * t ≤ bound ∧ consecutiveDivisorKernel N1 N2 t

theorem consecutiveDivisorKernelBelow_zero (N1 N2 bound : ℕ) :
    consecutiveDivisorKernelBelow N1 N2 bound 0 := by
  simp [consecutiveDivisorKernelBelow, consecutiveDivisorKernel]

theorem consecutiveDivisorKernelBelow_one (N1 N2 bound : ℕ) (hbound : 2 ≤ bound) :
    consecutiveDivisorKernelBelow N1 N2 bound 1 := by
  simp [consecutiveDivisorKernelBelow, consecutiveDivisorKernel, hbound]

/-- The same kernel with both the problem's lower row bound and half-row bound.
This is the formal target for compute certificates that use `min_t`. -/
def consecutiveDivisorKernelInRange (N1 N2 minT bound t : ℕ) : Prop :=
  minT ≤ t ∧ 2 * t ≤ bound ∧ consecutiveDivisorKernel N1 N2 t

/-- A row-one divisor split: one factor of `N1` is assigned to `t`, and the
other to `t - 1`. This is the formal version of the `{0,1}` choices used by
the CRT kernel scanner. -/
def rowOneDivisorSplit (N1 zeroPart onePart t : ℕ) : Prop :=
  zeroPart * onePart = N1 ∧ zeroPart ∣ t ∧ onePart ∣ t - 1

theorem rowOneDivisorSplit_dvd_mul_sub_one {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    N1 ∣ t * (t - 1) := by
  rcases hsplit with ⟨hprod, hzero, hone⟩
  rw [← hprod]
  exact Nat.mul_dvd_mul hzero hone

theorem primePow_dvd_mul_sub_one_iff {d t : ℕ} (hd : IsPrimePow d) (ht : 1 ≤ t) :
    d ∣ t * (t - 1) ↔ d ∣ t ∨ d ∣ t - 1 := by
  have hcop : t.Coprime (t - 1) := (Nat.coprime_self_sub_right ht).mpr (by simp)
  exact Nat.Coprime.isPrimePow_dvd_mul hcop hd

theorem eq_mul_add_one_of_sub_one_eq_mul {t k a : ℕ} (ht : 1 ≤ t)
    (h : t - 1 = k * a) :
    t = k * a + 1 := by
  omega

theorem coprime_mul_dvd_of_dvd_of_dvd {a b n : ℕ} (hcop : a.Coprime b)
    (ha : a ∣ n) (hb : b ∣ n) : a * b ∣ n := by
  rcases ha with ⟨x, rfl⟩
  have hbax : b ∣ a * x := by simpa [mul_comm] using hb
  have hbx : b ∣ x := hcop.symm.dvd_of_dvd_mul_left hbax
  rcases hbx with ⟨y, rfl⟩
  exact ⟨y, by ring⟩

theorem rowOneDivisorSplit_modEq_zero {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    t ≡ 0 [MOD zeroPart] := by
  exact Nat.modEq_zero_iff_dvd.mpr hsplit.2.1

theorem rowOneDivisorSplit_modEq_one_of_one_le {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    t ≡ 1 [MOD onePart] := by
  exact ((Nat.modEq_iff_dvd' ht).mpr hsplit.2.2).symm

theorem rowOneDivisorSplit_of_modEq {N1 zeroPart onePart t : ℕ}
    (hprod : zeroPart * onePart = N1) (hzero : t ≡ 0 [MOD zeroPart])
    (hone : t ≡ 1 [MOD onePart]) (ht : 1 ≤ t) :
    rowOneDivisorSplit N1 zeroPart onePart t := by
  exact
    ⟨hprod, Nat.modEq_zero_iff_dvd.mp hzero,
      (Nat.modEq_iff_dvd' ht).mp hone.symm⟩

theorem rowOneDivisorSplit_iff_modEq_of_one_le {N1 zeroPart onePart t : ℕ}
    (hprod : zeroPart * onePart = N1) (ht : 1 ≤ t) :
    rowOneDivisorSplit N1 zeroPart onePart t ↔
      t ≡ 0 [MOD zeroPart] ∧ t ≡ 1 [MOD onePart] := by
  constructor
  · intro hsplit
    exact
      ⟨rowOneDivisorSplit_modEq_zero hsplit,
        rowOneDivisorSplit_modEq_one_of_one_le hsplit ht⟩
  · intro hmods
    exact rowOneDivisorSplit_of_modEq hprod hmods.1 hmods.2 ht

theorem rowOneDivisorSplit_coprime_of_one_le {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    zeroPart.Coprime onePart := by
  exact Nat.Coprime.of_dvd hsplit.2.1 hsplit.2.2
    ((Nat.coprime_self_sub_right ht).mpr (by simp))

theorem rowOneDivisorSplit_modEq_chineseRemainder_of_coprime
    {N1 zeroPart onePart t : ℕ} (hcop : zeroPart.Coprime onePart)
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] := by
  have hcrt :
      t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD zeroPart * onePart] :=
    Nat.chineseRemainder_modEq_unique hcop
      (rowOneDivisorSplit_modEq_zero hsplit)
      (rowOneDivisorSplit_modEq_one_of_one_le hsplit ht)
  simpa [hsplit.1] using hcrt

theorem rowOneDivisorSplit_modEq_unique_of_coprime
    {N1 zeroPart onePart t u : ℕ} (hcop : zeroPart.Coprime onePart)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) :
    t ≡ u [MOD N1] := by
  have htcrt :
      t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] :=
    rowOneDivisorSplit_modEq_chineseRemainder_of_coprime hcop htsplit ht
  have hucrt :
      u ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] :=
    rowOneDivisorSplit_modEq_chineseRemainder_of_coprime hcop husplit hu
  exact htcrt.trans hucrt.symm

theorem rowOneDivisorSplit_modEq_unique
    {N1 zeroPart onePart t u : ℕ}
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) :
    t ≡ u [MOD N1] := by
  exact rowOneDivisorSplit_modEq_unique_of_coprime
    (rowOneDivisorSplit_coprime_of_one_le htsplit ht) htsplit husplit ht hu

theorem rowOneDivisorSplit_eq_of_lt
    {N1 zeroPart onePart t u : ℕ}
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htlt : t < N1) (hult : u < N1) :
    t = u := by
  exact Nat.ModEq.eq_of_lt_of_lt
    (rowOneDivisorSplit_modEq_unique htsplit husplit ht hu) htlt hult

theorem rowOneDivisorSplit_eq_of_half_bound
    {N1 bound zeroPart onePart t u : ℕ} (hbound : bound < 2 * N1)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htbound : 2 * t ≤ bound) (hubound : 2 * u ≤ bound) :
    t = u := by
  have ht_double_lt : 2 * t < 2 * N1 := lt_of_le_of_lt htbound hbound
  have hu_double_lt : 2 * u < 2 * N1 := lt_of_le_of_lt hubound hbound
  exact rowOneDivisorSplit_eq_of_lt htsplit husplit ht hu
    (Nat.lt_of_mul_lt_mul_left ht_double_lt)
    (Nat.lt_of_mul_lt_mul_left hu_double_lt)

theorem rowOneDivisorSplit_eq_of_consecutiveDivisorKernelBelow_short
    {N1 N2 bound zeroPart onePart t u : ℕ} (hbound : bound < 2 * N1)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htkernel : consecutiveDivisorKernelBelow N1 N2 bound t)
    (hukernel : consecutiveDivisorKernelBelow N1 N2 bound u) :
    t = u :=
  rowOneDivisorSplit_eq_of_half_bound hbound htsplit husplit ht hu
    htkernel.1 hukernel.1

theorem sub_one_short_bound_of_two_lt {n : ℕ} (hn : 2 < n) :
    n < 2 * (n - 1) := by
  omega

theorem rowOneDivisorSplit_eq_of_sub_one_consecutiveDivisorKernelBelow
    {n N2 zeroPart onePart t u : ℕ} (hn : 2 < n)
    (htsplit : rowOneDivisorSplit (n - 1) zeroPart onePart t)
    (husplit : rowOneDivisorSplit (n - 1) zeroPart onePart u)
    (ht : 1 ≤ t) (hu : 1 ≤ u)
    (htkernel : consecutiveDivisorKernelBelow (n - 1) N2 n t)
    (hukernel : consecutiveDivisorKernelBelow (n - 1) N2 n u) :
    t = u :=
  rowOneDivisorSplit_eq_of_consecutiveDivisorKernelBelow_short
    (sub_one_short_bound_of_two_lt hn) htsplit husplit ht hu htkernel hukernel

theorem rowOneDivisorSplit_gcdDiv_of_dvd_mul_sub_one {N1 t : ℕ}
    (hN1 : 0 < N1) (hrow : N1 ∣ t * (t - 1)) :
    rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t := by
  have hgcd_dvd : Nat.gcd N1 t ∣ N1 := Nat.gcd_dvd_left N1 t
  have hprod : Nat.gcd N1 t * (N1 / Nat.gcd N1 t) = N1 :=
    Nat.mul_div_cancel' hgcd_dvd
  have hzero : Nat.gcd N1 t ∣ t := Nat.gcd_dvd_right N1 t
  have hprod_mod : t * (t - 1) ≡ t * 0 [MOD N1] := by
    simpa using (Nat.modEq_zero_iff_dvd.mpr hrow : t * (t - 1) ≡ 0 [MOD N1])
  have hone_mod : t - 1 ≡ 0 [MOD N1 / Nat.gcd N1 t] := by
    simpa using (Nat.ModEq.cancel_left_div_gcd (m := N1) (c := t)
      (a := t - 1) (b := 0) hN1 hprod_mod)
  exact ⟨hprod, hzero, Nat.modEq_zero_iff_dvd.mp hone_mod⟩

theorem rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernel {N1 N2 t : ℕ}
    (hN1 : 0 < N1) (hkernel : consecutiveDivisorKernel N1 N2 t) :
    rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t :=
  rowOneDivisorSplit_gcdDiv_of_dvd_mul_sub_one hN1 hkernel.1

theorem rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernelBelow
    {N1 N2 bound t : ℕ} (hN1 : 0 < N1)
    (hkernel : consecutiveDivisorKernelBelow N1 N2 bound t) :
    rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t :=
  rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernel hN1 hkernel.2

theorem rowOneDivisorSplit_gcd_eq_zeroPart_of_one_le
    {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    Nat.gcd N1 t = zeroPart := by
  apply Nat.dvd_antisymm
  · have hgcd_dvd_prod : Nat.gcd N1 t ∣ zeroPart * onePart := by
      simpa [hsplit.1] using (Nat.gcd_dvd_left N1 t)
    have hcop : (Nat.gcd N1 t).Coprime onePart :=
      Nat.Coprime.of_dvd (Nat.gcd_dvd_right N1 t) hsplit.2.2
        ((Nat.coprime_self_sub_right ht).mpr (by simp))
    exact hcop.dvd_of_dvd_mul_right hgcd_dvd_prod
  · apply Nat.dvd_gcd
    · exact ⟨onePart, hsplit.1.symm⟩
    · exact hsplit.2.1

theorem rowOneDivisorSplit_div_gcd_eq_onePart_of_one_le
    {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    N1 / Nat.gcd N1 t = onePart := by
  have hgcd : Nat.gcd N1 t = zeroPart :=
    rowOneDivisorSplit_gcd_eq_zeroPart_of_one_le hsplit ht
  have ht_pos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
  have hzero_pos : 0 < zeroPart := Nat.pos_of_dvd_of_pos hsplit.2.1 ht_pos
  rw [hgcd, ← hsplit.1]
  exact Nat.mul_div_right onePart hzero_pos

theorem rowOneDivisorSplit_eq_gcdDiv_parts_of_one_le
    {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    Nat.gcd N1 t = zeroPart ∧ N1 / Nat.gcd N1 t = onePart :=
  ⟨rowOneDivisorSplit_gcd_eq_zeroPart_of_one_le hsplit ht,
    rowOneDivisorSplit_div_gcd_eq_onePart_of_one_le hsplit ht⟩

theorem rowOneDivisorSplit_kernel_iff_row_two {N1 N2 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    consecutiveDivisorKernel N1 N2 t ↔ N2 ∣ t * (t - 1) * (t - 2) := by
  constructor
  · intro hkernel
    exact hkernel.2
  · intro hrowTwo
    exact ⟨rowOneDivisorSplit_dvd_mul_sub_one hsplit, hrowTwo⟩

theorem rowTwo_dvd_iff_gcd_eq_right {N2 t : ℕ} :
    N2 ∣ t * (t - 1) * (t - 2) ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hrowTwo
    exact Nat.gcd_eq_right hrowTwo
  · intro hgcd
    simpa [hgcd] using Nat.gcd_dvd_left (t * (t - 1) * (t - 2)) N2

theorem consecutiveDivisorKernel_iff_row_two_gcd_eq_of_row_one {N1 N2 t : ℕ}
    (hrowOne : N1 ∣ t * (t - 1)) :
    consecutiveDivisorKernel N1 N2 t ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact rowTwo_dvd_iff_gcd_eq_right.mp hkernel.2
  · intro hgcd
    exact ⟨hrowOne, rowTwo_dvd_iff_gcd_eq_right.mpr hgcd⟩

theorem rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq
    {N1 N2 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    consecutiveDivisorKernel N1 N2 t ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 :=
  consecutiveDivisorKernel_iff_row_two_gcd_eq_of_row_one
    (rowOneDivisorSplit_dvd_mul_sub_one hsplit)

theorem rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_bound_and_row_two_gcd_eq
    {N1 N2 bound zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    consecutiveDivisorKernelBelow N1 N2 bound t ↔
      2 * t ≤ bound ∧ Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact ⟨hkernel.1,
      (rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq hsplit).mp hkernel.2⟩
  · intro h
    exact ⟨h.1,
      (rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq hsplit).mpr h.2⟩

theorem rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_row_two_gcd_eq_of_bound
    {N1 N2 bound zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hbound : 2 * t ≤ bound) :
    consecutiveDivisorKernelBelow N1 N2 bound t ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact
      ((rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_bound_and_row_two_gcd_eq
        hsplit).mp hkernel).2
  · intro hgcd
    exact
      (rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_bound_and_row_two_gcd_eq
        hsplit).mpr ⟨hbound, hgcd⟩

theorem rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_iff_row_two_gcd_ne_of_bound
    {N1 N2 bound zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hbound : 2 * t ≤ bound) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 ≠ N2 := by
  rw [rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_row_two_gcd_eq_of_bound
    hsplit hbound]

theorem rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_iff_row_two_gcd_lt_of_bound
    {N1 N2 bound zeroPart onePart t : ℕ} (hN2 : 0 < N2)
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hbound : 2 * t ≤ bound) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t ↔
      Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2 := by
  have hle : Nat.gcd (t * (t - 1) * (t - 2)) N2 ≤ N2 :=
    Nat.gcd_le_right _ hN2
  rw [rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_iff_row_two_gcd_ne_of_bound
    hsplit hbound]
  constructor
  · intro hne
    exact lt_of_le_of_ne hle hne
  · intro hlt
    exact ne_of_lt hlt

theorem consecutiveDivisorKernel_iff_gcdDiv_split_and_row_two_gcd_eq
    {N1 N2 t : ℕ} (hN1 : 0 < N1) :
    consecutiveDivisorKernel N1 N2 t ↔
      rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t ∧
        Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact
      ⟨rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernel hN1 hkernel,
        rowTwo_dvd_iff_gcd_eq_right.mp hkernel.2⟩
  · intro h
    exact (rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq h.1).mpr h.2

theorem consecutiveDivisorKernelBelow_iff_bound_gcdDiv_split_and_row_two_gcd_eq
    {N1 N2 bound t : ℕ} (hN1 : 0 < N1) :
    consecutiveDivisorKernelBelow N1 N2 bound t ↔
      2 * t ≤ bound ∧
        rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t ∧
          Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact
      ⟨hkernel.1,
        ⟨rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernelBelow hN1 hkernel,
          rowTwo_dvd_iff_gcd_eq_right.mp hkernel.2.2⟩⟩
  · intro h
    exact
      ⟨h.1,
        (rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq h.2.1).mpr h.2.2⟩

theorem consecutiveDivisorKernelInRange_iff_bounds_gcdDiv_split_and_row_two_gcd_eq
    {N1 N2 minT bound t : ℕ} (hN1 : 0 < N1) :
    consecutiveDivisorKernelInRange N1 N2 minT bound t ↔
      minT ≤ t ∧ 2 * t ≤ bound ∧
        rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t ∧
          Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hkernel
    exact
      ⟨hkernel.1, hkernel.2.1,
        (consecutiveDivisorKernel_iff_gcdDiv_split_and_row_two_gcd_eq
          hN1).mp hkernel.2.2⟩
  · intro h
    exact
      ⟨h.1, h.2.1,
        (consecutiveDivisorKernel_iff_gcdDiv_split_and_row_two_gcd_eq
          hN1).mpr h.2.2⟩

theorem exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq
    {N1 N2 bound : ℕ} (hN1 : 0 < N1) :
    (∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∃ t : ℕ,
        2 * t ≤ bound ∧
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t ∧
            Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · rintro ⟨t, hkernel⟩
    exact
      ⟨t,
        (consecutiveDivisorKernelBelow_iff_bound_gcdDiv_split_and_row_two_gcd_eq
          hN1).mp hkernel⟩
  · rintro ⟨t, hcert⟩
    exact
      ⟨t,
        (consecutiveDivisorKernelBelow_iff_bound_gcdDiv_split_and_row_two_gcd_eq
          hN1).mpr hcert⟩

theorem not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_ne
    {N1 N2 bound : ℕ} (hN1 : 0 < N1)
    (hfail :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            Nat.gcd (t * (t - 1) * (t - 2)) N2 ≠ N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t := by
  intro hexists
  rcases
      (exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq
        hN1).mp hexists with
    ⟨t, hbound, hsplit, hgcd⟩
  exact hfail t hbound hsplit hgcd

theorem not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_lt
    {N1 N2 bound : ℕ} (hN1 : 0 < N1)
    (hfail :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_ne
    hN1 fun t hbound hsplit => ne_of_lt (hfail t hbound hsplit)

theorem not_exists_consecutiveDivisorKernelBelow_of_list_covers_bound_gcdDiv_split_row_two_gcd_ne
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hfail :
      ∀ t : ℕ,
        t ∈ candidates →
          Nat.gcd (t * (t - 1) * (t - 2)) N2 ≠ N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_ne
    hN1 fun t hbound hsplit => hfail t (hcover t hbound hsplit)

theorem not_exists_consecutiveDivisorKernelBelow_of_list_covers_bound_gcdDiv_split_row_two_gcd_lt
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hfail :
      ∀ t : ℕ,
        t ∈ candidates →
          Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_exists_consecutiveDivisorKernelBelow_of_list_covers_bound_gcdDiv_split_row_two_gcd_ne
    hN1 hcover fun t htmem => ne_of_lt (hfail t htmem)

theorem exists_kernelBelow_iff_exists_mem_cert_of_list_covers
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates) :
    (∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∃ t : ℕ,
        t ∈ candidates ∧
          2 * t ≤ bound ∧
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t ∧
              Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hexists
    rcases
        (exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq
          hN1).mp hexists with
      ⟨t, hbound, hsplit, hgcd⟩
    exact ⟨t, hcover t hbound hsplit, hbound, hsplit, hgcd⟩
  · rintro ⟨t, _htmem, hbound, hsplit, hgcd⟩
    exact
      (exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq
        hN1).mpr ⟨t, hbound, hsplit, hgcd⟩

theorem exists_kernelBelow_iff_exists_mem_row_two_gcd_eq_of_list_exact
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hsound :
      ∀ t : ℕ,
        t ∈ candidates →
          2 * t ≤ bound ∧
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t) :
    (∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∃ t : ℕ,
        t ∈ candidates ∧ Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 := by
  constructor
  · intro hexists
    rcases
        (exists_kernelBelow_iff_exists_mem_cert_of_list_covers
          hN1 hcover).mp hexists with
      ⟨t, htmem, _hbound, _hsplit, hgcd⟩
    exact ⟨t, htmem, hgcd⟩
  · rintro ⟨t, htmem, hgcd⟩
    rcases hsound t htmem with ⟨hbound, hsplit⟩
    exact
      (exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq
        hN1).mpr ⟨t, hbound, hsplit, hgcd⟩

theorem not_exists_kernelBelow_iff_forall_mem_gcd_ne_of_list_exact
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hsound :
      ∀ t : ℕ,
        t ∈ candidates →
          2 * t ≤ bound ∧
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t) :
    (¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∀ t : ℕ,
        t ∈ candidates → Nat.gcd (t * (t - 1) * (t - 2)) N2 ≠ N2 := by
  rw [exists_kernelBelow_iff_exists_mem_row_two_gcd_eq_of_list_exact
    hN1 hcover hsound]
  constructor
  · intro hnone t htmem hgcd
    exact hnone ⟨t, htmem, hgcd⟩
  · intro hfail
    rintro ⟨t, htmem, hgcd⟩
    exact hfail t htmem hgcd

theorem not_exists_kernelBelow_iff_forall_mem_gcd_lt_of_list_exact
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hsound :
      ∀ t : ℕ,
        t ∈ candidates →
          2 * t ≤ bound ∧
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t) :
    (¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∀ t : ℕ,
        t ∈ candidates → Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2 := by
  rw [not_exists_kernelBelow_iff_forall_mem_gcd_ne_of_list_exact
    hN1 hcover hsound]
  constructor
  · intro hfail t htmem
    have hle : Nat.gcd (t * (t - 1) * (t - 2)) N2 ≤ N2 :=
      Nat.gcd_le_right _ hN2
    exact lt_of_le_of_ne hle (hfail t htmem)
  · intro hfail t htmem
    exact ne_of_lt (hfail t htmem)

theorem odd_eq_one_of_dvd_two {c : ℕ} (hcOdd : Odd c) (hc : c ∣ 2) :
    c = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hc with h | h
  · exact h
  · subst c
    contradiction

theorem dvd_two_of_dvd_sub_two_and_dvd_mul_pred {c t : ℕ}
    (ht : 2 ≤ t) (hgap : c ∣ t - 2) (hprod : c ∣ t * (t - 1)) :
    c ∣ 2 := by
  have htmod : t ≡ 2 [MOD c] := by
    have h0 : t - 2 ≡ 0 [MOD c] := Nat.modEq_zero_iff_dvd.mpr hgap
    have h2 := Nat.ModEq.add_right 2 h0
    have ht_eq : t - 2 + 2 = t := by omega
    simpa [ht_eq] using h2
  have hpredmod : t - 1 ≡ 1 [MOD c] := by
    have h := Nat.ModEq.sub_right (n := c) (a := 1) (b := t) (c := 2)
      (by omega) (by omega) htmod
    simpa using h
  have hprodmod : t * (t - 1) ≡ 2 * 1 [MOD c] := Nat.ModEq.mul htmod hpredmod
  have hprod0 : t * (t - 1) ≡ 0 [MOD c] := Nat.modEq_zero_iff_dvd.mpr hprod
  have h20 : 2 ≡ 0 [MOD c] := by
    simpa using hprodmod.symm.trans hprod0
  exact Nat.modEq_zero_iff_dvd.mp h20

theorem gcd_mul_left_cancel_of_coprime {a b n : ℕ} (h : a.Coprime n) :
    Nat.gcd (a * b) n = Nat.gcd b n := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hd_left : Nat.gcd (a * b) n ∣ a * b := Nat.gcd_dvd_left (a * b) n
      have hd_right : Nat.gcd (a * b) n ∣ n := Nat.gcd_dvd_right (a * b) n
      have hcop : (Nat.gcd (a * b) n).Coprime a :=
        (Nat.Coprime.of_dvd_right hd_right h).symm
      exact hcop.dvd_of_dvd_mul_left hd_left
    · exact Nat.gcd_dvd_right (a * b) n
  · apply Nat.dvd_gcd
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left b n) a
    · exact Nat.gcd_dvd_right b n

theorem gcd_mul_eq_mul_gcd_of_coprime_gcds {a b n : ℕ}
    (h : (Nat.gcd a n).Coprime (Nat.gcd b n)) :
    Nat.gcd (a * b) n = Nat.gcd a n * Nat.gcd b n := by
  let D := Nat.gcd a n
  let E := Nat.gcd b n
  apply Nat.dvd_antisymm
  · let q := Nat.gcd (a * b) n
    have hq_ab : q ∣ a * b := Nat.gcd_dvd_left (a * b) n
    have hq_n : q ∣ n := Nat.gcd_dvd_right (a * b) n
    have hDq : Nat.gcd q a = D := by
      apply Nat.dvd_antisymm
      · apply Nat.dvd_gcd
        · exact Nat.gcd_dvd_right q a
        · exact Nat.dvd_trans (Nat.gcd_dvd_left q a) hq_n
      · apply Nat.dvd_gcd
        · exact Nat.dvd_gcd
            (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a n) b)
            (Nat.gcd_dvd_right a n)
        · exact Nat.gcd_dvd_left a n
    have hEq : Nat.gcd q b = E := by
      apply Nat.dvd_antisymm
      · apply Nat.dvd_gcd
        · exact Nat.gcd_dvd_right q b
        · exact Nat.dvd_trans (Nat.gcd_dvd_left q b) hq_n
      · apply Nat.dvd_gcd
        · exact Nat.dvd_gcd
            (dvd_mul_of_dvd_right (Nat.gcd_dvd_left b n) a)
            (Nat.gcd_dvd_right b n)
        · exact Nat.gcd_dvd_left b n
    have hq_de : q ∣ D * E := by
      have htmp :=
        (Nat.dvd_gcd_mul_gcd_iff_dvd_mul (k := q) (n := a) (m := b)).mpr hq_ab
      simpa [D, E, hDq, hEq] using htmp
    exact hq_de
  · apply Nat.dvd_gcd
    · exact h.mul_dvd_of_dvd_of_dvd
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a n) b)
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_left b n) a)
    · exact h.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right a n) (Nat.gcd_dvd_right b n)

theorem rowTwo_gcd_eq_rowOneQuotient_gap_gcd_mul_of_odd
    {N1 N2 t : ℕ}
    (_hN1 : 0 < N1)
    (_hN2 : 0 < N2)
    (hcop : N1.Coprime N2)
    (hodd : Odd N2)
    (ht : 2 ≤ t)
    (hrow1 : N1 ∣ t * (t - 1)) :
    Nat.gcd (t * (t - 1) * (t - 2)) N2 =
      Nat.gcd ((t * (t - 1)) / N1) N2 * Nat.gcd (t - 2) N2 := by
  let g := (t * (t - 1)) / N1
  have hprod_eq : N1 * g = t * (t - 1) := by
    simpa [g] using (Nat.mul_div_cancel' hrow1)
  have hDEcop : (Nat.gcd g N2).Coprime (Nat.gcd (t - 2) N2) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    let c := Nat.gcd (Nat.gcd g N2) (Nat.gcd (t - 2) N2)
    have hcD : c ∣ Nat.gcd g N2 := Nat.gcd_dvd_left _ _
    have hcE : c ∣ Nat.gcd (t - 2) N2 := Nat.gcd_dvd_right _ _
    have hcg : c ∣ g := Nat.dvd_trans hcD (Nat.gcd_dvd_left g N2)
    have hcgap : c ∣ t - 2 := Nat.dvd_trans hcE (Nat.gcd_dvd_left (t - 2) N2)
    have hcN2 : c ∣ N2 := Nat.dvd_trans hcD (Nat.gcd_dvd_right g N2)
    have hcprod : c ∣ t * (t - 1) := by
      rw [← hprod_eq]
      exact dvd_mul_of_dvd_right hcg N1
    exact odd_eq_one_of_dvd_two
      (hodd.of_dvd_nat hcN2)
      (dvd_two_of_dvd_sub_two_and_dvd_mul_pred ht hcgap hcprod)
  calc
    Nat.gcd (t * (t - 1) * (t - 2)) N2
        = Nat.gcd ((N1 * g) * (t - 2)) N2 := by rw [hprod_eq]
    _ = Nat.gcd (N1 * (g * (t - 2))) N2 := by rw [mul_assoc]
    _ = Nat.gcd (g * (t - 2)) N2 := gcd_mul_left_cancel_of_coprime hcop
    _ = Nat.gcd g N2 * Nat.gcd (t - 2) N2 :=
        gcd_mul_eq_mul_gcd_of_coprime_gcds hDEcop
    _ = Nat.gcd ((t * (t - 1)) / N1) N2 * Nat.gcd (t - 2) N2 := by rfl

theorem rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
    {N1 N2 t : ℕ}
    (hN1 : 0 < N1)
    (hN2 : 0 < N2)
    (hcop : N1.Coprime N2)
    (hodd : Odd N2)
    (ht : 2 ≤ t)
    (hrow1 : N1 ∣ t * (t - 1))
    (hH :
      Nat.gcd ((t * (t - 1)) / N1) N2 *
        Nat.gcd (t - 2) N2 < N2) :
    Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2 := by
  rw [rowTwo_gcd_eq_rowOneQuotient_gap_gcd_mul_of_odd
    hN1 hN2 hcop hodd ht hrow1]
  exact hH

theorem rowOneDivisorSplit_rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
    {N1 N2 zeroPart onePart t : ℕ}
    (hN1 : 0 < N1)
    (hN2 : 0 < N2)
    (hcop : N1.Coprime N2)
    (hodd : Odd N2)
    (ht : 2 ≤ t)
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hH :
      Nat.gcd ((t * (t - 1)) / N1) N2 *
        Nat.gcd (t - 2) N2 < N2) :
    Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2 :=
  rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
    hN1 hN2 hcop hodd ht (rowOneDivisorSplit_dvd_mul_sub_one hsplit) hH

theorem not_exists_kernelBelow_of_forall_bound_quotient_gap_gcd_mul_lt_odd
    {N1 N2 bound : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hcop : N1.Coprime N2) (hodd : Odd N2)
    (hge2 :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            2 ≤ t)
    (hfail :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            Nat.gcd ((t * (t - 1)) / N1) N2 * Nat.gcd (t - 2) N2 < N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_lt
    hN1 fun t hbound hsplit =>
      rowOneDivisorSplit_rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
        hN1 hN2 hcop hodd (hge2 t hbound hsplit) hsplit
        (hfail t hbound hsplit)

theorem not_exists_kernelBelow_iff_forall_mem_quotient_gap_gcd_mul_lt_of_list_exact_odd
    {N1 N2 bound : ℕ} {candidates : List ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hcop : N1.Coprime N2) (hodd : Odd N2)
    (hcover :
      ∀ t : ℕ,
        2 * t ≤ bound →
          rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
            t ∈ candidates)
    (hsound :
      ∀ t : ℕ,
        t ∈ candidates →
          2 * t ≤ bound ∧
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t)
    (hge2 : ∀ t : ℕ, t ∈ candidates → 2 ≤ t) :
    (¬ ∃ t : ℕ, consecutiveDivisorKernelBelow N1 N2 bound t) ↔
      ∀ t : ℕ,
        t ∈ candidates →
          Nat.gcd ((t * (t - 1)) / N1) N2 * Nat.gcd (t - 2) N2 < N2 := by
  rw [not_exists_kernelBelow_iff_forall_mem_gcd_lt_of_list_exact
    hN1 hN2 hcover hsound]
  constructor
  · intro hfail t htmem
    have hsplit := (hsound t htmem).2
    have hrow1 : N1 ∣ t * (t - 1) :=
      rowOneDivisorSplit_dvd_mul_sub_one hsplit
    have heq :=
      rowTwo_gcd_eq_rowOneQuotient_gap_gcd_mul_of_odd
        hN1 hN2 hcop hodd (hge2 t htmem) hrow1
    simpa [heq] using hfail t htmem
  · intro hfail t htmem
    have hsplit := (hsound t htmem).2
    exact
      rowOneDivisorSplit_rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
        hN1 hN2 hcop hodd (hge2 t htmem) hsplit (hfail t htmem)

theorem not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
    {N1 N2 minT bound : ℕ} {candidates : List ℕ}
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hcop : N1.Coprime N2) (hodd : Odd N2)
    (hcover :
      ∀ t : ℕ,
        minT ≤ t →
          2 * t ≤ bound →
            rowOneDivisorSplit N1 (Nat.gcd N1 t) (N1 / Nat.gcd N1 t) t →
              t ∈ candidates)
    (hge2 : ∀ t : ℕ, t ∈ candidates → 2 ≤ t)
    (hfail :
      ∀ t : ℕ,
        t ∈ candidates →
          Nat.gcd ((t * (t - 1)) / N1) N2 * Nat.gcd (t - 2) N2 < N2) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange N1 N2 minT bound t := by
  rintro ⟨t, hkernel⟩
  rcases
      (consecutiveDivisorKernelInRange_iff_bounds_gcdDiv_split_and_row_two_gcd_eq
        hN1).mp hkernel with
    ⟨hmin, hbound, hsplit, hgcd_eq⟩
  have hmem : t ∈ candidates := hcover t hmin hbound hsplit
  have hgcd_lt : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2 :=
    rowOneDivisorSplit_rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd
      hN1 hN2 hcop hodd (hge2 t hmem) hsplit (hfail t hmem)
  omega

theorem not_exists_kernelInRange_of_prime_row_one_short {N1 N2 minT bound : ℕ}
    (hp : N1.Prime) (hminT : 2 ≤ minT) (hshort : bound < 2 * (N1 - 1)) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange N1 N2 minT bound t := by
  rintro ⟨t, hmin, hbound, hrow, _hrowTwo⟩
  have ht_ge_two : 2 ≤ t := hminT.trans hmin
  have ht_pos : 0 < t := by omega
  have htm1_pos : 0 < t - 1 := by omega
  have ht_lt_N1 : t < N1 := by omega
  have htm1_lt_N1 : t - 1 < N1 := by omega
  rcases hp.dvd_mul.mp hrow with ht_dvd | htm1_dvd
  · have hN1_le_t : N1 ≤ t := Nat.le_of_dvd ht_pos ht_dvd
    omega
  · have hN1_le_tm1 : N1 ≤ t - 1 := Nat.le_of_dvd htm1_pos htm1_dvd
    omega

theorem not_exists_kernelInRange_6143_3071_4_6144_of_prime
    (hp : Nat.Prime 6143) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 6143 3071 4 6144 t :=
  not_exists_kernelInRange_of_prime_row_one_short hp (by norm_num) (by norm_num)

theorem prime_6143 : Nat.Prime 6143 := by
  norm_num

theorem not_exists_kernelInRange_6143_3071_4_6144 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 6143 3071 4 6144 t :=
  not_exists_kernelInRange_6143_3071_4_6144_of_prime prime_6143

theorem not_exists_kernelInRange_95_47_4_96 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 95 47 4 96 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 95) (N2 := 47) (minT := 4) (bound := 96) (candidates := [20])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨23, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 48 := by omega
        interval_cases t <;> simp [rowOneDivisorSplit, Nat.gcd] at hsplit ⊢)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_767_383_4_768 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 767 383 4 768 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 767) (N2 := 383) (minT := 4) (bound := 768) (candidates := [118])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨191, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 384 := by omega
        interval_cases t <;> simp [rowOneDivisorSplit, Nat.gcd] at hsplit ⊢)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_1535_767_4_1536 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 1535 767 4 1536 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 1535) (N2 := 767) (minT := 4) (bound := 1536) (candidates := [615])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨383, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 768 := by omega
        have hrow : 1535 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h5prod : 5 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h307prod : 307 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp307 : Nat.Prime 307 := by decide +kernel
        rcases Nat.prime_five.dvd_mul.mp h5prod with h5t | h5tm1
        · rcases hp307.dvd_mul.mp h307prod with
            h307t | h307tm1
          · exfalso
            rcases h5t with ⟨a, ha⟩
            rcases h307t with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega
          · have ht_eq : t = 615 := by
              rcases h5t with ⟨a, ha⟩
              rcases h307tm1 with ⟨b, hb⟩
              have hb_le : b ≤ 2 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
        · rcases hp307.dvd_mul.mp h307prod with
            h307t | h307tm1
          · exfalso
            rcases h5tm1 with ⟨a, ha⟩
            rcases h307t with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h5tm1 with ⟨a, ha⟩
            rcases h307tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_3071_1535_4_3072 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 3071 1535 4 3072 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 3071) (N2 := 1535) (minT := 4) (bound := 3072) (candidates := [333])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨767, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 1536 := by omega
        have hrow : 3071 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h37prod : 37 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h83prod : 83 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp37 : Nat.Prime 37 := by decide +kernel
        have hp83 : Nat.Prime 83 := by decide +kernel
        rcases hp37.dvd_mul.mp h37prod with h37t | h37tm1
        · rcases hp83.dvd_mul.mp h83prod with h83t | h83tm1
          · exfalso
            rcases h37t with ⟨a, ha⟩
            rcases h83t with ⟨b, hb⟩
            have hb_le : b ≤ 18 := by omega
            interval_cases b <;> omega
          · have ht_eq : t = 333 := by
              rcases h37t with ⟨a, ha⟩
              rcases h83tm1 with ⟨b, hb⟩
              have hb_le : b ≤ 18 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
        · rcases hp83.dvd_mul.mp h83prod with h83t | h83tm1
          · exfalso
            rcases h37tm1 with ⟨a, ha⟩
            rcases h83t with ⟨b, hb⟩
            have hb_le : b ≤ 18 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h37tm1 with ⟨a, ha⟩
            rcases h83tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 18 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_12287_6143_4_12288 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 12287 6143 4 12288 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 12287) (N2 := 6143) (minT := 4) (bound := 12288) (candidates := [2234])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨3071, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 6144 := by omega
        have hrow : 12287 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h11prod : 11 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h1117prod : 1117 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp11 : Nat.Prime 11 := by decide +kernel
        have hp1117 : Nat.Prime 1117 := by decide +kernel
        rcases hp11.dvd_mul.mp h11prod with h11t | h11tm1
        · rcases hp1117.dvd_mul.mp h1117prod with h1117t | h1117tm1
          · exfalso
            rcases h11t with ⟨a, ha⟩
            rcases h1117t with ⟨b, hb⟩
            have hb_le : b ≤ 5 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h11t with ⟨a, ha⟩
            rcases h1117tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 5 := by omega
            interval_cases b <;> omega
        · rcases hp1117.dvd_mul.mp h1117prod with h1117t | h1117tm1
          · have ht_eq : t = 2234 := by
              rcases h11tm1 with ⟨a, ha⟩
              rcases h1117t with ⟨b, hb⟩
              have hb_le : b ≤ 5 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h11tm1 with ⟨a, ha⟩
            rcases h1117tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 5 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_24575_12287_4_24576 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 24575 12287 4 24576 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 24575) (N2 := 12287) (minT := 4) (bound := 24576) (candidates := [2950])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨6143, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 12288 := by omega
        have hrow : 24575 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h25prod : 25 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h983prod : 983 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp983 : Nat.Prime 983 := by norm_num
        rcases hp983.dvd_mul.mp h983prod with h983t | h983tm1
        · exfalso
          rcases h983t with ⟨b, hb⟩
          have hb_le : b ≤ 12 := by omega
          interval_cases b <;> subst t <;> omega
        · have ht_eq : t = 2950 := by
            rcases h983tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 12 := by omega
            have ht_expr : t = 983 * b + 1 := by omega
            interval_cases b <;> subst t <;> omega
          simp [ht_eq])
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_49151_24575_4_49152 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 49151 24575 4 49152 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 49151) (N2 := 24575) (minT := 4) (bound := 49152) (candidates := [23507])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨12287, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 24576 := by omega
        have hrow : 49151 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h23prod : 23 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h2137prod : 2137 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp23 : Nat.Prime 23 := by decide +kernel
        have hp2137 : Nat.Prime 2137 := by decide +kernel
        rcases hp23.dvd_mul.mp h23prod with h23t | h23tm1
        · rcases hp2137.dvd_mul.mp h2137prod with h2137t | h2137tm1
          · exfalso
            rcases h23t with ⟨a, ha⟩
            rcases h2137t with ⟨b, hb⟩
            have hb_le : b ≤ 11 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h23t with ⟨a, ha⟩
            rcases h2137tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 11 := by omega
            interval_cases b <;> omega
        · rcases hp2137.dvd_mul.mp h2137prod with h2137t | h2137tm1
          · have ht_eq : t = 23507 := by
              rcases h23tm1 with ⟨a, ha⟩
              rcases h2137t with ⟨b, hb⟩
              have hb_le : b ≤ 11 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h23tm1 with ⟨a, ha⟩
            rcases h2137tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 11 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_98303_49151_4_98304 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 98303 49151 4 98304 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 98303) (N2 := 49151) (minT := 4) (bound := 98304) (candidates := [7486])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨24575, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 49152 := by omega
        have hrow : 98303 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h197prod : 197 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h499prod : 499 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp197 : Nat.Prime 197 := by decide +kernel
        have hp499 : Nat.Prime 499 := by decide +kernel
        rcases hp197.dvd_mul.mp h197prod with h197t | h197tm1
        · rcases hp499.dvd_mul.mp h499prod with h499t | h499tm1
          · exfalso
            rcases h197t with ⟨a, ha⟩
            rcases h499t with ⟨b, hb⟩
            have hb_le : b ≤ 98 := by omega
            interval_cases b <;> omega
          · have ht_eq : t = 7486 := by
              rcases h197t with ⟨a, ha⟩
              rcases h499tm1 with ⟨b, hb⟩
              have hb_le : b ≤ 98 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
        · rcases hp499.dvd_mul.mp h499prod with h499t | h499tm1
          · exfalso
            rcases h197tm1 with ⟨a, ha⟩
            rcases h499t with ⟨b, hb⟩
            have hb_le : b ≤ 98 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h197tm1 with ⟨a, ha⟩
            rcases h499tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 98 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_196607_98303_4_196608 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 196607 98303 4 196608 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 196607) (N2 := 98303) (minT := 4) (bound := 196608) (candidates := [55573])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨49151, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 98304 := by omega
        have h421prod : 421 ∣ t * (t - 1) := by
          have hrow : 196607 ∣ t * (t - 1) :=
            rowOneDivisorSplit_dvd_mul_sub_one hsplit
          exact Nat.dvd_trans (by norm_num) hrow
        have h467prod : 467 ∣ t * (t - 1) := by
          have hrow : 196607 ∣ t * (t - 1) :=
            rowOneDivisorSplit_dvd_mul_sub_one hsplit
          exact Nat.dvd_trans (by norm_num) hrow
        have hp421 : Nat.Prime 421 := by decide +kernel
        have hp467 : Nat.Prime 467 := by decide +kernel
        rcases hp421.dvd_mul.mp h421prod with h421t | h421tm1
        · rcases hp467.dvd_mul.mp h467prod with h467t | h467tm1
          · exfalso
            rcases h421t with ⟨a, ha⟩
            rcases h467t with ⟨b, hb⟩
            have hb_le : b ≤ 210 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h421t with ⟨a, ha⟩
            rcases h467tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 210 := by omega
            interval_cases b <;> omega
        · rcases hp467.dvd_mul.mp h467prod with h467t | h467tm1
          · have ht_eq : t = 55573 := by
              rcases h421tm1 with ⟨a, ha⟩
              rcases h467t with ⟨b, hb⟩
              have hb_le : b ≤ 210 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h421tm1 with ⟨a, ha⟩
            rcases h467tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 210 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_393215_196607_4_393216 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 393215 196607 4 393216 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 393215) (N2 := 196607) (minT := 4) (bound := 393216) (candidates := [157286])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨98303, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 196608 := by omega
        have hrow : 393215 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h5prod : 5 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h78643prod : 78643 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp78643 : Nat.Prime 78643 := by norm_num
        rcases Nat.prime_five.dvd_mul.mp h5prod with h5t | h5tm1
        · rcases hp78643.dvd_mul.mp h78643prod with h78643t | h78643tm1
          · exfalso
            rcases h5t with ⟨a, ha⟩
            rcases h78643t with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h5t with ⟨a, ha⟩
            rcases h78643tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega
        · rcases hp78643.dvd_mul.mp h78643prod with h78643t | h78643tm1
          · have ht_eq : t = 157286 := by
              rcases h5tm1 with ⟨a, ha⟩
              rcases h78643t with ⟨b, hb⟩
              have hb_le : b ≤ 2 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h5tm1 with ⟨a, ha⟩
            rcases h78643tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 2 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_786431_393215_4_786432_of_prime
    (hp : Nat.Prime 786431) :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 786431 393215 4 786432 t :=
  not_exists_kernelInRange_of_prime_row_one_short hp (by norm_num) (by norm_num)

theorem prime_786431 : Nat.Prime 786431 := by
  norm_num

theorem not_exists_kernelInRange_786431_393215_4_786432 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 786431 393215 4 786432 t :=
  not_exists_kernelInRange_786431_393215_4_786432_of_prime prime_786431

theorem not_exists_kernelInRange_1572863_786431_4_1572864 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 1572863 786431 4 1572864 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 1572863) (N2 := 786431) (minT := 4) (bound := 1572864) (candidates := [22153])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨393215, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 786432 := by omega
        have hrow : 1572863 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h71prod : 71 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h22153prod : 22153 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp71 : Nat.Prime 71 := by norm_num
        have hp22153 : Nat.Prime 22153 := by norm_num
        rcases hp71.dvd_mul.mp h71prod with h71t | h71tm1
        · rcases hp22153.dvd_mul.mp h22153prod with h22153t | h22153tm1
          · exfalso
            rcases h71t with ⟨a, ha⟩
            rcases h22153t with ⟨b, hb⟩
            have hb_le : b ≤ 35 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h71t with ⟨a, ha⟩
            rcases h22153tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 35 := by omega
            interval_cases b <;> omega
        · rcases hp22153.dvd_mul.mp h22153prod with h22153t | h22153tm1
          · have ht_eq : t = 22153 := by
              rcases h71tm1 with ⟨a, ha⟩
              rcases h22153t with ⟨b, hb⟩
              have hb_le : b ≤ 35 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h71tm1 with ⟨a, ha⟩
            rcases h22153tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 35 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_3145727_1572863_4_3145728 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 3145727 1572863 4 3145728 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 3145727) (N2 := 1572863) (minT := 4) (bound := 3145728) (candidates := [967916])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨786431, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_le : t ≤ 1572864 := by omega
        have hrow : 3145727 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h13prod : 13 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have h241979prod : 241979 ∣ t * (t - 1) := by
          exact Nat.dvd_trans (by norm_num) hrow
        have hp13 : Nat.Prime 13 := by norm_num
        have hp241979 : Nat.Prime 241979 := by norm_num
        rcases hp13.dvd_mul.mp h13prod with h13t | h13tm1
        · rcases hp241979.dvd_mul.mp h241979prod with h241979t | h241979tm1
          · exfalso
            rcases h13t with ⟨a, ha⟩
            rcases h241979t with ⟨b, hb⟩
            have hb_le : b ≤ 6 := by omega
            interval_cases b <;> omega
          · exfalso
            rcases h13t with ⟨a, ha⟩
            rcases h241979tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 6 := by omega
            interval_cases b <;> omega
        · rcases hp241979.dvd_mul.mp h241979prod with h241979t | h241979tm1
          · have ht_eq : t = 967916 := by
              rcases h13tm1 with ⟨a, ha⟩
              rcases h241979t with ⟨b, hb⟩
              have hb_le : b ≤ 6 := by omega
              interval_cases b <;> omega
            simp [ht_eq]
          · exfalso
            rcases h13tm1 with ⟨a, ha⟩
            rcases h241979tm1 with ⟨b, hb⟩
            have hb_le : b ≤ 6 := by omega
            interval_cases b <;> omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_6291455_3145727_4_6291456 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 6291455 3145727 4 6291456 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 6291455) (N2 := 3145727) (minT := 4) (bound := 6291456)
      (candidates := [1258291])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨1572863, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_le : t ≤ 3145728 := by omega
        have hrow : 6291455 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h5 : 5 ∣ t ∨ 5 ∣ t - 1 := by
          exact
            (primePow_dvd_mul_sub_one_iff
                (Nat.Prime.isPrimePow Nat.prime_five) ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h1258291 : 1258291 ∣ t ∨ 1258291 ∣ t - 1 := by
          have hpp : IsPrimePow 1258291 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1258291)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        rcases h5 with h5t | h5tm1
        · rcases h1258291 with h1258291t | h1258291tm1
          · exfalso
            rcases h5t with ⟨a, ha⟩
            rcases h1258291t with ⟨b, hb⟩
            omega
          · exfalso
            rcases h5t with ⟨a, ha⟩
            rcases h1258291tm1 with ⟨b, hb⟩
            omega
        · rcases h1258291 with h1258291t | h1258291tm1
          · have ht_eq : t = 1258291 := by
              rcases h5tm1 with ⟨a, ha⟩
              rcases h1258291t with ⟨b, hb⟩
              omega
            simp [ht_eq]
          · exfalso
            rcases h5tm1 with ⟨a, ha⟩
            rcases h1258291tm1 with ⟨b, hb⟩
            omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_12582911_6291455_4_12582912 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 12582911 6291455 4 12582912 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 12582911) (N2 := 6291455) (minT := 4) (bound := 12582912)
      (candidates := [727937])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨3145727, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_le : t ≤ 6291456 := by omega
        have hrow : 12582911 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h121 : 121 ∣ t ∨ 121 ∣ t - 1 := by
          have hpp : IsPrimePow 121 := by
            rw [show 121 = 11 ^ 2 by norm_num]
            rw [isPrimePow_pow_iff (by norm_num : 2 ≠ 0)]
            exact Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h103991 : 103991 ∣ t ∨ 103991 ∣ t - 1 := by
          have hpp : IsPrimePow 103991 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 103991)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        rcases h121 with h121t | h121tm1
        · rcases h103991 with h103991t | h103991tm1
          · exfalso
            rcases h121t with ⟨a, ha⟩
            rcases h103991t with ⟨b, hb⟩
            omega
          · exfalso
            rcases h121t with ⟨a, ha⟩
            rcases h103991tm1 with ⟨b, hb⟩
            omega
        · rcases h103991 with h103991t | h103991tm1
          · have ht_eq : t = 727937 := by
              rcases h121tm1 with ⟨a, ha⟩
              rcases h103991t with ⟨b, hb⟩
              omega
            simp [ht_eq]
          · exfalso
            rcases h121tm1 with ⟨a, ha⟩
            rcases h103991tm1 with ⟨b, hb⟩
            omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_25165823_12582911_4_25165824 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 25165823 12582911 4 25165824 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 25165823) (N2 := 12582911) (minT := 4) (bound := 25165824)
      (candidates := [4612973, 9271620, 11281232])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨6291455, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_le : t ≤ 12582912 := by omega
        have hrow : 25165823 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h19 : 19 ∣ t ∨ 19 ∣ t - 1 := by
          have hpp : IsPrimePow 19 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 19)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h29 : 29 ∣ t ∨ 29 ∣ t - 1 := by
          have hpp : IsPrimePow 29 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 29)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h45673 : 45673 ∣ t ∨ 45673 ∣ t - 1 := by
          have hpp : IsPrimePow 45673 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 45673)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h000 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a → t = 29 * b → t = 45673 * c → False := by
          intro t a b c hmin ht ha hb hc
          omega
        have h001 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a → t = 29 * b → t = 45673 * c + 1 → False := by
          intro t a b c hmin ht ha hb hc
          omega
        have h010 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a → t = 29 * b + 1 → t = 45673 * c → False := by
          intro t a b c hmin ht ha hb hc
          omega
        have h011 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a → t = 29 * b + 1 → t = 45673 * c + 1 →
                t = 9271620 := by
          intro t a b c hmin ht ha hb hc
          omega
        have h100 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a + 1 → t = 29 * b → t = 45673 * c → False := by
          intro t a b c hmin ht ha hb hc
          omega
        have h101 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a + 1 → t = 29 * b → t = 45673 * c + 1 →
                t = 11281232 := by
          intro t a b c hmin ht ha hb hc
          omega
        have h110 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a + 1 → t = 29 * b + 1 → t = 45673 * c →
                t = 4612973 := by
          intro t a b c hmin ht ha hb hc
          omega
        have h111 :
            ∀ {t a b c : ℕ}, 4 ≤ t → t ≤ 12582912 →
              t = 19 * a + 1 → t = 29 * b + 1 → t = 45673 * c + 1 → False := by
          intro t a b c hmin ht ha hb hc
          omega
        rcases h19 with h19t | h19tm1
        · rcases h29 with h29t | h29tm1
          · rcases h45673 with h45673t | h45673tm1
            · exfalso
              rcases h19t with ⟨a, ha⟩
              rcases h29t with ⟨b, hb⟩
              rcases h45673t with ⟨c, hc⟩
              exact h000 hmin ht_le ha hb hc
            · exfalso
              rcases h19t with ⟨a, ha⟩
              rcases h29t with ⟨b, hb⟩
              rcases h45673tm1 with ⟨c, hc⟩
              have hc' : t = 45673 * c + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one hc
              exact h001 hmin ht_le ha hb hc'
          · rcases h45673 with h45673t | h45673tm1
            · exfalso
              rcases h19t with ⟨a, ha⟩
              rcases h29tm1 with ⟨b, hb⟩
              rcases h45673t with ⟨c, hc⟩
              have hb' : t = 29 * b + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one hb
              exact h010 hmin ht_le ha hb' hc
            · have ht_eq : t = 9271620 := by
                rcases h19t with ⟨a, ha⟩
                rcases h29tm1 with ⟨b, hb⟩
                rcases h45673tm1 with ⟨c, hc⟩
                have hb' : t = 29 * b + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one hb
                have hc' : t = 45673 * c + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one hc
                exact h011 hmin ht_le ha hb' hc'
              simp [ht_eq]
        · rcases h29 with h29t | h29tm1
          · rcases h45673 with h45673t | h45673tm1
            · exfalso
              rcases h19tm1 with ⟨a, ha⟩
              rcases h29t with ⟨b, hb⟩
              rcases h45673t with ⟨c, hc⟩
              have ha' : t = 19 * a + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one ha
              exact h100 hmin ht_le ha' hb hc
            · have ht_eq : t = 11281232 := by
                rcases h19tm1 with ⟨a, ha⟩
                rcases h29t with ⟨b, hb⟩
                rcases h45673tm1 with ⟨c, hc⟩
                have ha' : t = 19 * a + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one ha
                have hc' : t = 45673 * c + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one hc
                exact h101 hmin ht_le ha' hb hc'
              simp [ht_eq]
          · rcases h45673 with h45673t | h45673tm1
            · have ht_eq : t = 4612973 := by
                rcases h19tm1 with ⟨a, ha⟩
                rcases h29tm1 with ⟨b, hb⟩
                rcases h45673t with ⟨c, hc⟩
                have ha' : t = 19 * a + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one ha
                have hb' : t = 29 * b + 1 :=
                  eq_mul_add_one_of_sub_one_eq_mul ht_one hb
                exact h110 hmin ht_le ha' hb' hc
              simp [ht_eq]
            · exfalso
              rcases h19tm1 with ⟨a, ha⟩
              rcases h29tm1 with ⟨b, hb⟩
              rcases h45673tm1 with ⟨c, hc⟩
              have ha' : t = 19 * a + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one ha
              have hb' : t = 29 * b + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one hb
              have hc' : t = 45673 * c + 1 :=
                eq_mul_add_one_of_sub_one_eq_mul ht_one hc
              exact h111 hmin ht_le ha' hb' hc')
      (by
        intro t htmem
        have htmem' : t = 4612973 ∨ t = 9271620 ∨ t = 11281232 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        omega)
      (by
        intro t htmem
        have htmem' : t = 4612973 ∨ t = 9271620 ∨ t = 11281232 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        rcases htmem' with rfl | rfl | rfl
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd])

theorem not_exists_kernelInRange_50331647_25165823_4_50331648 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 50331647 25165823 4 50331648 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 50331647) (N2 := 25165823) (minT := 4) (bound := 50331648)
      (candidates := [13788863])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨12582911, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_le : t ≤ 25165824 := by omega
        have hrow : 50331647 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have h6563 : 6563 ∣ t ∨ 6563 ∣ t - 1 := by
          have hpp : IsPrimePow 6563 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 6563)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h7669 : 7669 ∣ t ∨ 7669 ∣ t - 1 := by
          have hpp : IsPrimePow 7669 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 7669)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        rcases h6563 with h6563t | h6563tm1
        · rcases h7669 with h7669t | h7669tm1
          · exfalso
            rcases h6563t with ⟨a, ha⟩
            rcases h7669t with ⟨b, hb⟩
            omega
          · have ht_eq : t = 13788863 := by
              rcases h6563t with ⟨a, ha⟩
              rcases h7669tm1 with ⟨b, hb⟩
              omega
            simp [ht_eq]
        · rcases h7669 with h7669t | h7669tm1
          · exfalso
            rcases h6563tm1 with ⟨a, ha⟩
            rcases h7669t with ⟨b, hb⟩
            omega
          · exfalso
            rcases h6563tm1 with ⟨a, ha⟩
            rcases h7669tm1 with ⟨b, hb⟩
            omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_100663295_50331647_4_100663296 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 100663295 50331647 4 100663296 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 100663295) (N2 := 50331647) (minT := 4) (bound := 100663296)
      (candidates := [19257326, 20132660, 39389985])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨25165823, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_lt_N1 : t < 100663295 := by omega
        have hrow : 100663295 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have hbranch_eq :
            ∀ {zeroPart onePart u : ℕ},
              rowOneDivisorSplit 100663295 zeroPart onePart t →
              rowOneDivisorSplit 100663295 zeroPart onePart u →
              1 ≤ u → u < 100663295 → t = u := by
          intro zeroPart onePart u htsp husp hu_one hu_lt
          exact rowOneDivisorSplit_eq_of_lt htsp husp ht_one hu_one ht_lt_N1 hu_lt
        have h5 : 5 ∣ t ∨ 5 ∣ t - 1 := by
          exact
            (primePow_dvd_mul_sub_one_iff
                (Nat.Prime.isPrimePow Nat.prime_five) ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h23 : 23 ∣ t ∨ 23 ∣ t - 1 := by
          have hpp : IsPrimePow 23 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 23)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h875333 : 875333 ∣ t ∨ 875333 ∣ t - 1 := by
          have hpp : IsPrimePow 875333 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 875333)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h5cop23 : (5 : ℕ).Coprime 23 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h5cop875333 : (5 : ℕ).Coprime 875333 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h23cop875333 : (23 : ℕ).Coprime 875333 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h115cop875333 : (5 * 23 : ℕ).Coprime 875333 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        rcases h5 with h5t | h5tm1
        · rcases h23 with h23t | h23tm1
          · rcases h875333 with h875333t | h875333tm1
            · exfalso
              have h115t : 5 * 23 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop23 h5t h23t
              have hN1t : 100663295 ∣ t := by
                have hprod : (5 * 23) * 875333 ∣ t :=
                  coprime_mul_dvd_of_dvd_of_dvd h115cop875333 h115t h875333t
                simpa [show (5 * 23) * 875333 = 100663295 by norm_num] using hprod
              have hN1_le_t : 100663295 ≤ t := Nat.le_of_dvd (by omega : 0 < t) hN1t
              omega
            · exfalso
              have h115t : 5 * 23 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop23 h5t h23t
              have htsplit : rowOneDivisorSplit 100663295 115 875333 t := by
                exact ⟨by norm_num, by simpa using h115t, h875333tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 115 875333 81405970 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 81405970 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              omega
          · rcases h875333 with h875333t | h875333tm1
            · have h4376665t : 5 * 875333 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop875333 h5t h875333t
              have htsplit : rowOneDivisorSplit 100663295 4376665 23 t := by
                exact ⟨by norm_num, by simpa using h4376665t, h23tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 4376665 23 39389985 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 39389985 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
            · have h20132659tm1 : 23 * 875333 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h23cop875333 h23tm1 h875333tm1
              have htsplit : rowOneDivisorSplit 100663295 5 20132659 t := by
                exact ⟨by norm_num, h5t, by simpa using h20132659tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 5 20132659 20132660 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 20132660 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
        · rcases h23 with h23t | h23tm1
          · rcases h875333 with h875333t | h875333tm1
            · exfalso
              have h20132659t : 23 * 875333 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h23cop875333 h23t h875333t
              have htsplit : rowOneDivisorSplit 100663295 20132659 5 t := by
                exact ⟨by norm_num, by simpa using h20132659t, h5tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 20132659 5 80530636 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 80530636 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              omega
            · exfalso
              have h4376665tm1 : 5 * 875333 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop875333 h5tm1 h875333tm1
              have htsplit : rowOneDivisorSplit 100663295 23 4376665 t := by
                exact ⟨by norm_num, h23t, by simpa using h4376665tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 23 4376665 61273311 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 61273311 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              omega
          · rcases h875333 with h875333t | h875333tm1
            · have h115tm1 : 5 * 23 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop23 h5tm1 h23tm1
              have htsplit : rowOneDivisorSplit 100663295 875333 115 t := by
                exact ⟨by norm_num, h875333t, by simpa using h115tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 875333 115 19257326 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 19257326 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
            · exfalso
              have h115tm1 : 5 * 23 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h5cop23 h5tm1 h23tm1
              have hN1tm1 : 100663295 ∣ t - 1 := by
                have hprod : (5 * 23) * 875333 ∣ t - 1 :=
                  coprime_mul_dvd_of_dvd_of_dvd h115cop875333 h115tm1 h875333tm1
                simpa [show (5 * 23) * 875333 = 100663295 by norm_num] using hprod
              have htsplit : rowOneDivisorSplit 100663295 1 100663295 t := by
                exact ⟨by norm_num, one_dvd t, hN1tm1⟩
              have husplit :
                  rowOneDivisorSplit 100663295 1 100663295 1 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 1 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              omega)
      (by
        intro t htmem
        have htmem' : t = 19257326 ∨ t = 20132660 ∨ t = 39389985 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        omega)
      (by
        intro t htmem
        have htmem' : t = 19257326 ∨ t = 20132660 ∨ t = 39389985 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        rcases htmem' with rfl | rfl | rfl
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd])

theorem not_exists_kernelInRange_201326591_100663295_4_201326592 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 201326591 100663295 4 201326592 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 201326591) (N2 := 100663295) (minT := 4) (bound := 201326592)
      (candidates := [33417252])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨50331647, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_lt_N1 : t < 201326591 := by omega
        have hrow : 201326591 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have hbranch_eq :
            ∀ {zeroPart onePart u : ℕ},
              rowOneDivisorSplit 201326591 zeroPart onePart t →
              rowOneDivisorSplit 201326591 zeroPart onePart u →
              1 ≤ u → u < 201326591 → t = u := by
          intro zeroPart onePart u htsp husp hu_one hu_lt
          exact rowOneDivisorSplit_eq_of_lt htsp husp ht_one hu_one ht_lt_N1 hu_lt
        have h1223 : 1223 ∣ t ∨ 1223 ∣ t - 1 := by
          have hpp : IsPrimePow 1223 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1223)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h164617 : 164617 ∣ t ∨ 164617 ∣ t - 1 := by
          have hpp : IsPrimePow 164617 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 164617)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        rcases h1223 with h1223t | h1223tm1
        · rcases h164617 with h164617t | h164617tm1
          · exfalso
            have hcop : (1223 : ℕ).Coprime 164617 := by
              rw [Nat.coprime_iff_gcd_eq_one]
              norm_num [Nat.gcd]
            have hN1t : 201326591 ∣ t := by
              have hprod : 1223 * 164617 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd hcop h1223t h164617t
              simpa [show 1223 * 164617 = 201326591 by norm_num] using hprod
            have hN1_le_t : 201326591 ≤ t := Nat.le_of_dvd (by omega : 0 < t) hN1t
            omega
          · have htsplit : rowOneDivisorSplit 201326591 1223 164617 t := by
              exact ⟨by norm_num, h1223t, h164617tm1⟩
            have husplit :
                rowOneDivisorSplit 201326591 1223 164617 33417252 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 33417252 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            simp [ht_eq]
        · rcases h164617 with h164617t | h164617tm1
          · exfalso
            have htsplit : rowOneDivisorSplit 201326591 164617 1223 t := by
              exact ⟨by norm_num, h164617t, h1223tm1⟩
            have husplit :
                rowOneDivisorSplit 201326591 164617 1223 167909340 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 167909340 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            omega
          · exfalso
            have hcop : (1223 : ℕ).Coprime 164617 := by
              rw [Nat.coprime_iff_gcd_eq_one]
              norm_num [Nat.gcd]
            have hN1tm1 : 201326591 ∣ t - 1 := by
              have hprod : 1223 * 164617 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd hcop h1223tm1 h164617tm1
              simpa [show 1223 * 164617 = 201326591 by norm_num] using hprod
            have htsplit : rowOneDivisorSplit 201326591 1 201326591 t := by
              exact ⟨by norm_num, one_dvd t, hN1tm1⟩
            have husplit :
                rowOneDivisorSplit 201326591 1 201326591 1 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 1 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            omega)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_exists_kernelInRange_402653183_201326591_4_402653184 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 402653183 201326591 4 402653184 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 402653183) (N2 := 201326591) (minT := 4) (bound := 402653184)
      (candidates := [17134179, 24038997, 41173175])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨100663295, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_pos : 0 < t := Nat.lt_of_lt_of_le (by norm_num : 0 < 4) hmin
        have ht_lt_N1 : t < 402653183 := by omega
        have hrow : 402653183 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have hbranch_eq :
            ∀ {zeroPart onePart u : ℕ},
              rowOneDivisorSplit 402653183 zeroPart onePart t →
              rowOneDivisorSplit 402653183 zeroPart onePart u →
              1 ≤ u → u < 402653183 → t = u := by
          intro zeroPart onePart u htsp husp hu_one hu_lt
          exact rowOneDivisorSplit_eq_of_lt htsp husp ht_one hu_one ht_lt_N1 hu_lt
        have h47 : 47 ∣ t ∨ 47 ∣ t - 1 := by
          have hpp : IsPrimePow 47 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 47)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h67 : 67 ∣ t ∨ 67 ∣ t - 1 := by
          have hpp : IsPrimePow 67 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 67)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h127867 : 127867 ∣ t ∨ 127867 ∣ t - 1 := by
          have hpp : IsPrimePow 127867 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 127867)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h47cop67 : (47 : ℕ).Coprime 67 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h47cop127867 : (47 : ℕ).Coprime 127867 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h67cop127867 : (67 : ℕ).Coprime 127867 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        have h3149cop127867 : (47 * 67 : ℕ).Coprime 127867 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          norm_num [Nat.gcd]
        rcases h47 with h47t | h47tm1
        · rcases h67 with h67t | h67tm1
          · rcases h127867 with h127867t | h127867tm1
            · exfalso
              have h3149t : 47 * 67 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop67 h47t h67t
              have hN1t : 402653183 ∣ t := by
                have hprod : (47 * 67) * 127867 ∣ t :=
                  coprime_mul_dvd_of_dvd_of_dvd h3149cop127867 h3149t h127867t
                simpa [show (47 * 67) * 127867 = 402653183 by norm_num] using hprod
              exact (not_lt_of_ge (Nat.le_of_dvd ht_pos hN1t)) ht_lt_N1
            · have h3149t : 47 * 67 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop67 h47t h67t
              have htsplit : rowOneDivisorSplit 402653183 3149 127867 t := by
                exact ⟨by norm_num, by simpa using h3149t, h127867tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 3149 127867 41173175 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 41173175 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
          · rcases h127867 with h127867t | h127867tm1
            · exfalso
              have h6009749t : 47 * 127867 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop127867 h47t h127867t
              have htsplit : rowOneDivisorSplit 402653183 6009749 67 t := by
                exact ⟨by norm_num, by simpa using h6009749t, h67tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 6009749 67 378614187 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 378614187 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              have hbound' := hbound
              rw [ht_eq] at hbound'
              norm_num at hbound'
            · have h8567089tm1 : 67 * 127867 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h67cop127867 h67tm1 h127867tm1
              have htsplit : rowOneDivisorSplit 402653183 47 8567089 t := by
                exact ⟨by norm_num, h47t, by simpa using h8567089tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 47 8567089 17134179 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 17134179 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
        · rcases h67 with h67t | h67tm1
          · rcases h127867 with h127867t | h127867tm1
            · exfalso
              have h8567089t : 67 * 127867 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd h67cop127867 h67t h127867t
              have htsplit : rowOneDivisorSplit 402653183 8567089 47 t := by
                exact ⟨by norm_num, by simpa using h8567089t, h47tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 8567089 47 385519005 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 385519005 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              have hbound' := hbound
              rw [ht_eq] at hbound'
              norm_num at hbound'
            · have h6009749tm1 : 47 * 127867 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop127867 h47tm1 h127867tm1
              have htsplit : rowOneDivisorSplit 402653183 67 6009749 t := by
                exact ⟨by norm_num, h67t, by simpa using h6009749tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 67 6009749 24038997 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 24038997 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              simp [ht_eq]
          · rcases h127867 with h127867t | h127867tm1
            · exfalso
              have h3149tm1 : 47 * 67 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop67 h47tm1 h67tm1
              have htsplit : rowOneDivisorSplit 402653183 127867 3149 t := by
                exact ⟨by norm_num, h127867t, by simpa using h3149tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 127867 3149 361480009 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 361480009 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              have hbound' := hbound
              rw [ht_eq] at hbound'
              norm_num at hbound'
            · exfalso
              have h3149tm1 : 47 * 67 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd h47cop67 h47tm1 h67tm1
              have hN1tm1 : 402653183 ∣ t - 1 := by
                have hprod : (47 * 67) * 127867 ∣ t - 1 :=
                  coprime_mul_dvd_of_dvd_of_dvd h3149cop127867 h3149tm1 h127867tm1
                simpa [show (47 * 67) * 127867 = 402653183 by norm_num] using hprod
              have htsplit : rowOneDivisorSplit 402653183 1 402653183 t := by
                exact ⟨by norm_num, one_dvd t, hN1tm1⟩
              have husplit :
                  rowOneDivisorSplit 402653183 1 402653183 1 := by
                norm_num [rowOneDivisorSplit]
              have ht_eq : t = 1 :=
                hbranch_eq htsplit husplit (by norm_num) (by norm_num)
              have hmin' := hmin
              rw [ht_eq] at hmin'
              norm_num at hmin')
      (by
        intro t htmem
        have htmem' : t = 17134179 ∨ t = 24038997 ∨ t = 41173175 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        omega)
      (by
        intro t htmem
        have htmem' : t = 17134179 ∨ t = 24038997 ∨ t = 41173175 := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using htmem
        rcases htmem' with rfl | rfl | rfl
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd]
        · norm_num [Nat.gcd])

theorem not_exists_kernelInRange_805306367_402653183_4_805306368 :
    ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange 805306367 402653183 4 805306368 t := by
  exact
    not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd
      (N1 := 805306367) (N2 := 402653183) (minT := 4) (bound := 805306368)
      (candidates := [365758927])
      (by norm_num)
      (by norm_num)
      (by
        rw [Nat.coprime_iff_gcd_eq_one]
        norm_num [Nat.gcd])
      (by exact ⟨201326591, by norm_num⟩)
      (by
        intro t hmin hbound hsplit
        have ht_one : 1 ≤ t := by omega
        have ht_pos : 0 < t := Nat.lt_of_lt_of_le (by norm_num : 0 < 4) hmin
        have ht_lt_N1 : t < 805306367 := by omega
        have hrow : 805306367 ∣ t * (t - 1) :=
          rowOneDivisorSplit_dvd_mul_sub_one hsplit
        have hbranch_eq :
            ∀ {zeroPart onePart u : ℕ},
              rowOneDivisorSplit 805306367 zeroPart onePart t →
              rowOneDivisorSplit 805306367 zeroPart onePart u →
              1 ≤ u → u < 805306367 → t = u := by
          intro zeroPart onePart u htsp husp hu_one hu_lt
          exact rowOneDivisorSplit_eq_of_lt htsp husp ht_one hu_one ht_lt_N1 hu_lt
        have h51349 : 51349 ∣ t ∨ 51349 ∣ t - 1 := by
          have hpp : IsPrimePow 51349 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 51349)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        have h15683 : 15683 ∣ t ∨ 15683 ∣ t - 1 := by
          have hpp : IsPrimePow 15683 :=
            Nat.Prime.isPrimePow (by norm_num : Nat.Prime 15683)
          exact
            (primePow_dvd_mul_sub_one_iff hpp ht_one).mp
              (Nat.dvd_trans (by norm_num) hrow)
        rcases h51349 with h51349t | h51349tm1
        · rcases h15683 with h15683t | h15683tm1
          · exfalso
            have hcop : (51349 : ℕ).Coprime 15683 := by
              rw [Nat.coprime_iff_gcd_eq_one]
              norm_num [Nat.gcd]
            have hN1t : 805306367 ∣ t := by
              have hprod : 51349 * 15683 ∣ t :=
                coprime_mul_dvd_of_dvd_of_dvd hcop h51349t h15683t
              simpa [show 51349 * 15683 = 805306367 by norm_num] using hprod
            exact (not_lt_of_ge (Nat.le_of_dvd ht_pos hN1t)) ht_lt_N1
          · have htsplit : rowOneDivisorSplit 805306367 51349 15683 t := by
              exact ⟨by norm_num, h51349t, h15683tm1⟩
            have husplit :
                rowOneDivisorSplit 805306367 51349 15683 365758927 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 365758927 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            simp [ht_eq]
        · rcases h15683 with h15683t | h15683tm1
          · exfalso
            have htsplit : rowOneDivisorSplit 805306367 15683 51349 t := by
              exact ⟨by norm_num, h15683t, h51349tm1⟩
            have husplit :
                rowOneDivisorSplit 805306367 15683 51349 439547441 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 439547441 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            have hbound' := hbound
            rw [ht_eq] at hbound'
            norm_num at hbound'
          · exfalso
            have hcop : (51349 : ℕ).Coprime 15683 := by
              rw [Nat.coprime_iff_gcd_eq_one]
              norm_num [Nat.gcd]
            have hN1tm1 : 805306367 ∣ t - 1 := by
              have hprod : 51349 * 15683 ∣ t - 1 :=
                coprime_mul_dvd_of_dvd_of_dvd hcop h51349tm1 h15683tm1
              simpa [show 51349 * 15683 = 805306367 by norm_num] using hprod
            have htsplit : rowOneDivisorSplit 805306367 1 805306367 t := by
              exact ⟨by norm_num, one_dvd t, hN1tm1⟩
            have husplit :
                rowOneDivisorSplit 805306367 1 805306367 1 := by
              norm_num [rowOneDivisorSplit]
            have ht_eq : t = 1 :=
              hbranch_eq htsplit husplit (by norm_num) (by norm_num)
            have hmin' := hmin
            rw [ht_eq] at hmin'
            norm_num at hmin')
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num)
      (by
        intro t htmem
        simp at htmem
        subst t
        norm_num [Nat.gcd])

theorem not_consecutiveDivisorKernel_of_row_two_gcd_lt {N1 N2 t : ℕ}
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernel N1 N2 t := by
  intro hkernel
  have hgcd_eq :
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 :=
    Nat.gcd_eq_right hkernel.2
  omega

theorem rowOneDivisorSplit_not_consecutiveDivisorKernel_of_row_two_gcd_lt
    {N1 N2 zeroPart onePart t : ℕ}
    (_hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernel N1 N2 t :=
  not_consecutiveDivisorKernel_of_row_two_gcd_lt hgcd

theorem not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt {N1 N2 bound t : ℕ}
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t := by
  intro hkernel
  exact not_consecutiveDivisorKernel_of_row_two_gcd_lt hgcd hkernel.2

theorem rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt
    {N1 N2 zeroPart onePart bound t : ℕ}
    (_hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt hgcd

theorem commonPrimeDivisor_of_prime_in_top_interval {n i j p : ℕ}
    (hp : p.Prime) (hij : i < j) (hjn : 2 * j ≤ n) (hleft : n - i < p)
    (hright : p ≤ n) :
    commonPrimeDivisor n i j p := by
  have hi_lt_p : i < p := by omega
  have hj_lt_p : j < p := by omega
  have hn_lt_2p : n < 2 * p := by omega
  have hlow_i : n - p < i := by omega
  have hlow_j : n - p < j := by omega
  exact
    ⟨hp, hi_lt_p.le,
      prime_dvd_choose_of_units_digit_lt hp hright hn_lt_2p hlow_i hi_lt_p,
      prime_dvd_choose_of_units_digit_lt hp hright hn_lt_2p hlow_j hj_lt_p⟩

/-- The numerator window `n(n-1)...(n-i+1)` for `C(n,i)`. -/
def fallingWindowProduct (n i : ℕ) : ℕ :=
  ∏ r ∈ Finset.range i, (n - r)

theorem t3_top_interval_prime_free_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) :
    ¬ (n - i < p ∧ p ≤ n) := by
  intro hinterval
  exact hnone p
    (commonPrimeDivisor_of_prime_in_top_interval hp hij hjn hinterval.1 hinterval.2)

theorem t3_no_large_prime_dvd_fallingWindowProduct_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) (hp_large : n < 2 * p) :
    ¬ p ∣ fallingWindowProduct n i := by
  intro hprod
  have hexists : ∃ r ∈ Finset.range i, p ∣ n - r := by
    by_contra hnone_factor
    rw [not_exists] at hnone_factor
    have hno_factor : ∀ r ∈ Finset.range i, ¬ p ∣ n - r := by
      intro r hr hdiv
      exact hnone_factor r ⟨hr, hdiv⟩
    exact (prime_not_dvd_finset_prod hp hno_factor) hprod
  obtain ⟨r, hr, hpdiv⟩ := hexists
  have hrlt : r < i := by simpa [Finset.mem_range] using hr
  have hrn : r < n := by omega
  have hfactor_ne_zero : n - r ≠ 0 := by omega
  have hfactor_lt : n - r < 2 * p := by omega
  have hfactor_eq : n - r = p := Nat.eq_of_dvd_of_lt_two_mul hfactor_ne_zero hpdiv hfactor_lt
  have hinterval : n - i < p ∧ p ≤ n := by
    constructor <;> omega
  exact (t3_top_interval_prime_free_of_no_common hnone hij hjn hp) hinterval

/-- A natural number that is exactly a power of two. -/
def twoPower (m : ℕ) : Prop :=
  ∃ a : ℕ, m = 2 ^ a

theorem twoPower_eq_one_of_odd {m : ℕ} (hm : twoPower m) (hodd : Odd m) :
    m = 1 := by
  rcases hm with ⟨a, rfl⟩
  by_cases ha : a = 0
  · simp [ha]
  · rcases Nat.exists_eq_succ_of_ne_zero ha with ⟨b, rfl⟩
    have heven : Even (2 ^ (b + 1)) := by
      rw [pow_succ]
      exact even_iff_two_dvd.mpr ⟨2 ^ b, by rw [mul_comm]⟩
    have hnot_odd : ¬ Odd (2 ^ (b + 1)) := Nat.not_odd_iff_even.mpr heven
    exact False.elim (hnot_odd hodd)

theorem eq_three_of_sub_one_sub_two_twoPowers {n : ℕ}
    (h1 : twoPower (n - 1)) (h2 : twoPower (n - 2)) :
    n = 3 := by
  rcases h2 with ⟨b, hb⟩
  by_cases hb0 : b = 0
  · have hn2 : n - 2 = 1 := by simpa [hb0] using hb
    omega
  · have heven_n2 : Even (n - 2) := by
      rcases Nat.exists_eq_succ_of_ne_zero hb0 with ⟨c, rfl⟩
      rw [hb, pow_succ]
      exact even_iff_two_dvd.mpr ⟨2 ^ c, by rw [mul_comm]⟩
    have hmod_n2 : (n - 2) % 2 = 0 := Nat.even_iff.mp heven_n2
    have hsucc : n - 1 = n - 2 + 1 := by
      have hpos : 0 < n - 2 := by
        rw [hb]
        exact pow_pos (by decide : 0 < 2) b
      omega
    have hmod_n1 : (n - 1) % 2 = 1 := by
      rw [hsucc, Nat.add_mod, hmod_n2]
    have hodd_n1 : Odd (n - 1) := Nat.odd_iff.mpr hmod_n1
    have hn1 : n - 1 = 1 := twoPower_eq_one_of_odd h1 hodd_n1
    have hpos : 0 < n - 2 := by
      rw [hb]
      exact pow_pos (by decide : 0 < 2) b
    omega

theorem i_three_window_one_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    j % p ≤ 1 := by
  have hn_mod : n % p = 1 := by
    rcases hpdvd with ⟨a, ha⟩
    have hEq : n = p * a + 1 := by omega
    rw [hEq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hdomj : dominated j n p := (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdomj 0
  simpa [digit, hn_mod] using hdigitsj

theorem i_three_window_two_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    j % p ≤ 2 := by
  have hn_mod : n % p = 2 := by
    rcases hpdvd with ⟨a, ha⟩
    have hEq : n = p * a + 2 := by omega
    rw [hEq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < p)]
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hdomj : dominated j n p := (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdomj 0
  simpa [digit, hn_mod] using hdigitsj

private theorem dvd_sub_of_mod_eq {j p r : ℕ} (hmod : j % p = r) : p ∣ j - r := by
  refine ⟨j / p, ?_⟩
  have h := Nat.div_add_mod j p
  rw [hmod] at h
  omega

theorem mod_eq_of_dvd_sub {j p r : ℕ} (hrj : r ≤ j) (hrp : r < p)
    (hpdvd : p ∣ j - r) :
    j % p = r := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : j = p * a + r := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrp]

theorem prime_dvd_of_pow_dvd {p e m : ℕ} (he : 0 < e) (h : p ^ e ∣ m) :
    p ∣ m := by
  rcases h with ⟨a, ha⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨c, hc⟩
  refine ⟨p ^ c * a, ?_⟩
  rw [ha, hc, pow_succ']
  ac_rfl

/-- If `p^e` divides `n`, then all base-`p` digits of `n` below level `e`
are zero. -/
theorem digit_eq_zero_of_pow_dvd {n p e r : ℕ}
    (hp_pos : 0 < p) (hr_lt : r < e) (hpdvd : p ^ e ∣ n) :
    digit n p r = 0 := by
  have hle : r + 1 ≤ e := Nat.succ_le_of_lt hr_lt
  have hsucc_dvd : p ^ (r + 1) ∣ n :=
    Nat.dvd_trans (pow_dvd_pow p hle) hpdvd
  rcases hsucc_dvd with ⟨a, ha⟩
  have hpowr_pos : 0 < p ^ r := pow_pos hp_pos r
  have hpow_succ_mul : p ^ (r + 1) * a = p ^ r * (p * a) := by
    rw [pow_succ']
    ring
  have hdiv : n / p ^ r = p * a := by
    rw [ha, hpow_succ_mul]
    exact Nat.mul_div_cancel_left (p * a) hpowr_pos
  rw [digit, hdiv]
  exact Nat.dvd_iff_mod_eq_zero.mp ⟨a, rfl⟩

theorem digit_zero_eq_one_of_pow_dvd_sub_one {n p e : ℕ}
    (hp : p.Prime) (hn_pos : 0 < n) (he_pos : 0 < e) (hpdvd : p ^ e ∣ n - 1) :
    digit n p 0 = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 1 := by omega
  have hp_dvd_pow : p ∣ p ^ e := prime_dvd_of_pow_dvd he_pos dvd_rfl
  have hp_dvd_left : p ∣ p ^ e * a := dvd_mul_of_dvd_left hp_dvd_pow a
  have hmod_left : p ^ e * a % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hp_dvd_left
  rw [digit, hn_eq]
  simp [Nat.add_mod, hmod_left, Nat.mod_eq_of_lt hp.one_lt]

theorem digit_eq_zero_of_pow_dvd_sub_one {n p e r : ℕ}
    (hp : p.Prime) (hn_pos : 0 < n) (hr_pos : 1 ≤ r) (hr_lt : r < e)
    (hpdvd : p ^ e ∣ n - 1) :
    digit n p r = 0 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 1 := by omega
  have hre : r ≤ e := Nat.le_of_lt hr_lt
  have hpow_split : p ^ e = p ^ r * p ^ (e - r) := by
    rw [← pow_add, Nat.add_sub_of_le hre]
  have hdiv :
      (p ^ e * a + 1) / p ^ r = p ^ (e - r) * a := by
    rw [hpow_split]
    have hpow_pos : 0 < p ^ r := pow_pos hp.pos r
    have hrem_lt : 1 < p ^ r := Nat.one_lt_pow (by omega : r ≠ 0) hp.one_lt
    rw [mul_assoc]
    have hbase : (p ^ r * (p ^ (e - r) * a) + 1) / p ^ r =
        p ^ (e - r) * a := by
      rw [Nat.add_comm]
      rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
      simp
    exact hbase
  have hfactor : p ∣ p ^ (e - r) * a := by
    have hexp_pos : 0 < e - r := Nat.sub_pos_of_lt hr_lt
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hexp_pos) with ⟨c, hc⟩
    rw [hc, pow_succ']
    exact dvd_mul_of_dvd_left (dvd_mul_right p (p ^ c)) a
  rw [digit, hn_eq, hdiv]
  exact Nat.dvd_iff_mod_eq_zero.mp hfactor

theorem i_three_window_one_dominated_of_prime_pow_dvd_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 1) :
    dominated j n p := by
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have hn_mod : n % p = 1 :=
      by simpa [digit] using
        digit_zero_eq_one_of_pow_dvd_sub_one hp (by omega : 0 < n) he_pos hpdvd
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  exact (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero

theorem i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 1) :
    digit j p 0 ≤ 1 := by
  have hdom : dominated j n p :=
    i_three_window_one_dominated_of_prime_pow_dvd_sub_one hnone hp hp5 hn he_pos hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_digit : digit n p 0 = 1 :=
    digit_zero_eq_one_of_pow_dvd_sub_one hp (by omega : 0 < n) he_pos hpdvd
  simpa [hn_digit] using hdigitsj

theorem i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one {n j p e r : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n)
    (hr_pos : 1 ≤ r) (hr_lt : r < e) (hpdvd : p ^ e ∣ n - 1) :
    digit j p r = 0 := by
  have hdom : dominated j n p :=
    i_three_window_one_dominated_of_prime_pow_dvd_sub_one hnone hp hp5 hn
      (by omega : 0 < e) hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom r
  have hn_digit : digit n p r = 0 :=
    digit_eq_zero_of_pow_dvd_sub_one hp (by omega : 0 < n) hr_pos hr_lt hpdvd
  have hle : digit j p r ≤ 0 := by simpa [hn_digit] using hdigitsj
  omega

theorem pow_dvd_of_forall_digit_eq_zero {j p e : ℕ}
    (hp_pos : 0 < p) (hzero : ∀ r : ℕ, r < e → digit j p r = 0) :
    p ^ e ∣ j := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      have hlow : p ^ e ∣ j :=
        ih fun r hr => hzero r (Nat.lt_trans hr (Nat.lt_succ_self e))
      rcases hlow with ⟨a, ha⟩
      have hpow_pos : 0 < p ^ e := pow_pos hp_pos e
      have hdiv : j / p ^ e = a := by
        rw [ha]
        exact Nat.mul_div_cancel_left a hpow_pos
      have hdigit : digit j p e = 0 := hzero e (Nat.lt_succ_self e)
      have hpa : p ∣ a := by
        rw [digit, hdiv] at hdigit
        exact Nat.dvd_iff_mod_eq_zero.mpr hdigit
      rcases hpa with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [ha, hb, pow_succ']
      ac_rfl

/-- Digit domination transfers a prime-power divisor of `n` to the dominated
number. -/
theorem pow_dvd_of_dominated_and_pow_dvd {j n p e : ℕ}
    (hp : Nat.Prime p) (hdom : dominated j n p) (hpdvd : p ^ e ∣ n) :
    p ^ e ∣ j := by
  refine pow_dvd_of_forall_digit_eq_zero hp.pos ?_
  intro r hr
  have hj_le_n : digit j p r ≤ digit n p r :=
    (dominated_iff_forall_digits hp.two_le).mp hdom r
  have hn_zero : digit n p r = 0 :=
    digit_eq_zero_of_pow_dvd hp.pos hr hpdvd
  have hj_le_zero : digit j p r ≤ 0 := by
    simpa [hn_zero] using hj_le_n
  omega

theorem pow_dvd_sub_one_of_unit_digit_one_high_zero {j p e : ℕ}
    (hp : p.Prime) (hunit : digit j p 0 = 1)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j - 1 := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      by_cases he0 : e = 0
      · subst e
        have hjmod : j % p = 1 := by
          simpa [digit] using hunit
        refine ⟨j / p, ?_⟩
        have hj_eq : j = p * (j / p) + 1 := by
          have h := Nat.div_add_mod j p
          rw [hjmod] at h
          omega
        have htarget : j - 1 = p * (j / p) := by omega
        simpa using htarget
      · have he_pos : 0 < e := Nat.pos_of_ne_zero he0
        have hlow : p ^ e ∣ j - 1 :=
          ih fun r hrpos hrlt => hzero r hrpos (Nat.lt_trans hrlt (Nat.lt_succ_self e))
        rcases hlow with ⟨a, ha⟩
        have hj_pos : 0 < j := by
          by_contra hj_not
          have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj_not
          have hunit0 : digit j p 0 = 0 := by simp [digit, hj0]
          omega
        have hj_eq : j = p ^ e * a + 1 := by omega
        have hpow_pos : 0 < p ^ e := pow_pos hp.pos e
        have hrem_lt : 1 < p ^ e := Nat.one_lt_pow (Nat.ne_of_gt he_pos) hp.one_lt
        have hdiv : j / p ^ e = a := by
          rw [hj_eq, Nat.add_comm]
          rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
          simp
        have hdigit : digit j p e = 0 :=
          hzero e (by omega) (Nat.lt_succ_self e)
        have hpa : p ∣ a := by
          rw [digit, hdiv] at hdigit
          exact Nat.dvd_iff_mod_eq_zero.mpr hdigit
        rcases hpa with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [ha, hb, pow_succ']
        ac_rfl

theorem pow_dvd_mul_sub_one_of_digit_le_one_high_zero {j p e : ℕ}
    (hp : p.Prime) (hunit_le : digit j p 0 ≤ 1)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j * (j - 1) := by
  by_cases he0 : e = 0
  · subst e
    simp
  · have hunit_cases : digit j p 0 = 0 ∨ digit j p 0 = 1 := by omega
    rcases hunit_cases with hunit0 | hunit1
    · have hall_zero : ∀ r : ℕ, r < e → digit j p r = 0 := by
        intro r hr
        by_cases hr0 : r = 0
        · simpa [hr0] using hunit0
        · exact hzero r (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)) hr
      have hpow : p ^ e ∣ j := pow_dvd_of_forall_digit_eq_zero hp.pos hall_zero
      exact dvd_mul_of_dvd_left hpow (j - 1)
    · have hpow : p ^ e ∣ j - 1 :=
        pow_dvd_sub_one_of_unit_digit_one_high_zero hp hunit1 hzero
      exact dvd_mul_of_dvd_right hpow j

theorem i_three_window_one_prime_pow_dvd_mul_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ^ e ∣ n - 1) :
    p ^ e ∣ j * (j - 1) := by
  by_cases he0 : e = 0
  · subst e
    simp
  have hunit_le : digit j p 0 ≤ 1 := by
    exact i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one
      hnone hp hp5 hn (Nat.pos_of_ne_zero he0) hpdvd
  have hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0 := by
    intro r hrpos hrlt
    exact i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one
      hnone hp hp5 hn hrpos hrlt hpdvd
  exact pow_dvd_mul_sub_one_of_digit_le_one_high_zero hp hunit_le hzero

theorem digit_zero_eq_two_of_pow_dvd_sub_two {n p e : ℕ}
    (hp5 : 5 ≤ p) (h2n : 2 ≤ n) (he_pos : 0 < e) (hpdvd : p ^ e ∣ n - 2) :
    digit n p 0 = 2 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 2 := by omega
  have hp_dvd_pow : p ∣ p ^ e := prime_dvd_of_pow_dvd he_pos dvd_rfl
  have hp_dvd_left : p ∣ p ^ e * a := dvd_mul_of_dvd_left hp_dvd_pow a
  have hmod_left : p ^ e * a % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hp_dvd_left
  rw [digit, hn_eq]
  simp [Nat.add_mod, hmod_left, Nat.mod_eq_of_lt (by omega : 2 < p)]

theorem digit_eq_zero_of_pow_dvd_sub_two {n p e r : ℕ}
    (hp5 : 5 ≤ p) (h2n : 2 ≤ n) (hr_pos : 1 ≤ r) (hr_lt : r < e)
    (hpdvd : p ^ e ∣ n - 2) :
    digit n p r = 0 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 2 := by omega
  have hre : r ≤ e := Nat.le_of_lt hr_lt
  have hpow_split : p ^ e = p ^ r * p ^ (e - r) := by
    rw [← pow_add, Nat.add_sub_of_le hre]
  have hdiv :
      (p ^ e * a + 2) / p ^ r = p ^ (e - r) * a := by
    rw [hpow_split]
    have hpow_pos : 0 < p ^ r := pow_pos (by omega : 0 < p) r
    have hp_le_pow : p ≤ p ^ r :=
      Nat.le_self_pow (by omega : r ≠ 0) p
    have hrem_lt : 2 < p ^ r := by omega
    rw [mul_assoc]
    have hbase : (p ^ r * (p ^ (e - r) * a) + 2) / p ^ r =
        p ^ (e - r) * a := by
      rw [Nat.add_comm]
      rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
      simp
    exact hbase
  have hfactor : p ∣ p ^ (e - r) * a := by
    have hexp_pos : 0 < e - r := Nat.sub_pos_of_lt hr_lt
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hexp_pos) with ⟨c, hc⟩
    rw [hc, pow_succ']
    exact dvd_mul_of_dvd_left (dvd_mul_right p (p ^ c)) a
  rw [digit, hn_eq, hdiv]
  exact Nat.dvd_iff_mod_eq_zero.mp hfactor

theorem i_three_window_two_dominated_of_prime_pow_dvd_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 2) :
    dominated j n p := by
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have hn_mod : n % p = 2 := by
      simpa [digit] using
        digit_zero_eq_two_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) he_pos hpdvd
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  exact (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero

theorem i_three_window_two_units_digit_le_two_of_prime_pow_dvd_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 2) :
    digit j p 0 ≤ 2 := by
  have hdom : dominated j n p :=
    i_three_window_two_dominated_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn he_pos hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_digit : digit n p 0 = 2 :=
    digit_zero_eq_two_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) he_pos hpdvd
  simpa [hn_digit] using hdigitsj

theorem i_three_window_two_high_digit_zero_of_prime_pow_dvd_sub_two {n j p e r : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n)
    (hr_pos : 1 ≤ r) (hr_lt : r < e) (hpdvd : p ^ e ∣ n - 2) :
    digit j p r = 0 := by
  have hdom : dominated j n p :=
    i_three_window_two_dominated_of_prime_pow_dvd_sub_two hnone hp hp5 hn
      (by omega : 0 < e) hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom r
  have hn_digit : digit n p r = 0 :=
    digit_eq_zero_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) hr_pos hr_lt hpdvd
  have hle : digit j p r ≤ 0 := by simpa [hn_digit] using hdigitsj
  omega

theorem pow_dvd_sub_two_of_unit_digit_two_high_zero {j p e : ℕ}
    (hp5 : 5 ≤ p) (hunit : digit j p 0 = 2)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j - 2 := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      by_cases he0 : e = 0
      · subst e
        have hjmod : j % p = 2 := by
          simpa [digit] using hunit
        refine ⟨j / p, ?_⟩
        have hj_eq : j = p * (j / p) + 2 := by
          have h := Nat.div_add_mod j p
          rw [hjmod] at h
          omega
        have htarget : j - 2 = p * (j / p) := by omega
        simpa using htarget
      · have he_pos : 0 < e := Nat.pos_of_ne_zero he0
        have hlow : p ^ e ∣ j - 2 :=
          ih fun r hrpos hrlt => hzero r hrpos (Nat.lt_trans hrlt (Nat.lt_succ_self e))
        rcases hlow with ⟨a, ha⟩
        have hj_ge_two : 2 ≤ j := by
          by_contra hj_not
          have hj_lt : j < 2 := Nat.lt_of_not_ge hj_not
          have hj_cases : j = 0 ∨ j = 1 := by omega
          rcases hj_cases with hj0 | hj1
          · have hunit0 : digit j p 0 = 0 := by simp [digit, hj0]
            omega
          · have hunit1 : digit j p 0 = 1 := by
              simp [digit, hj1, Nat.mod_eq_of_lt (by omega : 1 < p)]
            omega
        have hj_eq : j = p ^ e * a + 2 := by omega
        have hpow_pos : 0 < p ^ e := pow_pos (by omega : 0 < p) e
        have hp_le_pow : p ≤ p ^ e :=
          Nat.le_self_pow (Nat.ne_of_gt he_pos) p
        have hrem_lt : 2 < p ^ e := by omega
        have hdiv : j / p ^ e = a := by
          rw [hj_eq, Nat.add_comm]
          rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
          simp
        have hdigit : digit j p e = 0 :=
          hzero e (by omega) (Nat.lt_succ_self e)
        have hpa : p ∣ a := by
          rw [digit, hdiv] at hdigit
          exact Nat.dvd_iff_mod_eq_zero.mpr hdigit
        rcases hpa with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [ha, hb, pow_succ']
        ac_rfl

theorem pow_dvd_mul_sub_one_sub_two_of_digit_le_two_high_zero {j p e : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hunit_le : digit j p 0 ≤ 2)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j * (j - 1) * (j - 2) := by
  by_cases he0 : e = 0
  · subst e
    simp
  · have hunit_cases : digit j p 0 = 0 ∨ digit j p 0 = 1 ∨ digit j p 0 = 2 := by omega
    rcases hunit_cases with hunit0 | hunit1 | hunit2
    · have hall_zero : ∀ r : ℕ, r < e → digit j p r = 0 := by
        intro r hr
        by_cases hr0 : r = 0
        · simpa [hr0] using hunit0
        · exact hzero r (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)) hr
      have hpow : p ^ e ∣ j := pow_dvd_of_forall_digit_eq_zero hp.pos hall_zero
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow (j - 1)) (j - 2)
    · have hpow : p ^ e ∣ j - 1 :=
        pow_dvd_sub_one_of_unit_digit_one_high_zero hp hunit1 hzero
      have hprod : p ^ e ∣ j * (j - 1) := dvd_mul_of_dvd_right hpow j
      exact dvd_mul_of_dvd_left hprod (j - 2)
    · have hpow : p ^ e ∣ j - 2 :=
        pow_dvd_sub_two_of_unit_digit_two_high_zero hp5 hunit2 hzero
      exact dvd_mul_of_dvd_right hpow (j * (j - 1))

theorem i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ^ e ∣ n - 2) :
    p ^ e ∣ j * (j - 1) * (j - 2) := by
  by_cases he0 : e = 0
  · subst e
    simp
  have hunit_le : digit j p 0 ≤ 2 := by
    exact i_three_window_two_units_digit_le_two_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn (Nat.pos_of_ne_zero he0) hpdvd
  have hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0 := by
    intro r hrpos hrlt
    exact i_three_window_two_high_digit_zero_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn hrpos hrlt hpdvd
  exact pow_dvd_mul_sub_one_sub_two_of_digit_le_two_high_zero hp hp5 hunit_le hzero

theorem dvd_mul_sub_one_of_mod_le_one {j p : ℕ} (hmod : j % p ≤ 1) :
    p ∣ j * (j - 1) := by
  have hcase : j % p = 0 ∨ j % p = 1 := by omega
  rcases hcase with hzero | hone
  · have hj : p ∣ j := Nat.dvd_iff_mod_eq_zero.mpr hzero
    exact dvd_mul_of_dvd_left hj (j - 1)
  · have hj1 : p ∣ j - 1 := dvd_sub_of_mod_eq hone
    exact dvd_mul_of_dvd_right hj1 j

theorem dvd_mul_sub_one_sub_two_of_mod_le_two {j p : ℕ} (hmod : j % p ≤ 2) :
    p ∣ j * (j - 1) * (j - 2) := by
  have hcase : j % p = 0 ∨ j % p = 1 ∨ j % p = 2 := by omega
  rcases hcase with hzero | hone | htwo
  · have hj : p ∣ j := Nat.dvd_iff_mod_eq_zero.mpr hzero
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hj (j - 1)) (j - 2)
  · have hj1 : p ∣ j - 1 := dvd_sub_of_mod_eq hone
    have hprod : p ∣ j * (j - 1) := dvd_mul_of_dvd_right hj1 j
    exact dvd_mul_of_dvd_left hprod (j - 2)
  · have hj2 : p ∣ j - 2 := dvd_sub_of_mod_eq htwo
    exact dvd_mul_of_dvd_right hj2 (j * (j - 1))

theorem i_three_window_one_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    p ∣ j * (j - 1) :=
  dvd_mul_sub_one_of_mod_le_one
    (i_three_window_one_digit_forcing hnone hp hp5 hn hpdvd)

theorem i_three_window_two_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    p ∣ j * (j - 1) * (j - 2) :=
  dvd_mul_sub_one_sub_two_of_mod_le_two
    (i_three_window_two_digit_forcing hnone hp hp5 hn hpdvd)

theorem three_mul_mod_eq_one_of_dvd_pred {j p : ℕ}
    (hp : p.Prime) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 1) :
    (3 * j) % p = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 1 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]

theorem three_mul_mod_eq_two_of_dvd_sub_two {j p : ℕ}
    (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 2) :
    (3 * j) % p = 2 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 2 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < p)]

theorem no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hlin : p ∣ 3 * j - 1)
    (hprod : p ∣ j * (j - 1)) : False := by
  have hmodlin : (3 * j) % p = 1 := three_mul_mod_eq_one_of_dvd_pred hp hj hlin
  have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  rcases hp.dvd_mul.mp hprod with hjdvd | hj1dvd
  · have hjmod : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hjdvd
    rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
    norm_num at hmodlin
  · have hjmod : j % p = 1 := mod_eq_of_dvd_sub (by omega) (by omega) hj1dvd
    rw [Nat.mul_mod, h3mod, hjmod, Nat.mod_eq_of_lt (by omega : 3 < p)] at hmodlin
    omega

theorem no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hlin : p ∣ 3 * j - 2)
    (hprod : p ∣ j * (j - 1) * (j - 2)) : False := by
  have hj_pos : 0 < j := by omega
  have hmodlin : (3 * j) % p = 2 := three_mul_mod_eq_two_of_dvd_sub_two hp5 hj_pos hlin
  have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  rcases hp.dvd_mul.mp hprod with hleft | hj2dvd
  · rcases hp.dvd_mul.mp hleft with hjdvd | hj1dvd
    · have hjmod : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hjdvd
      rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
      norm_num at hmodlin
    · have hjmod : j % p = 1 := mod_eq_of_dvd_sub (by omega) (by omega) hj1dvd
      rw [Nat.mul_mod, h3mod, hjmod, Nat.mod_eq_of_lt (by omega : 3 < p)] at hmodlin
      omega
  · have hjmod : j % p = 2 := mod_eq_of_dvd_sub hj (by omega) hj2dvd
    rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
    by_cases hp_eq_five : p = 5
    · subst p
      norm_num at hmodlin
    · have hp_ne_six : p ≠ 6 := by
        intro hp6
        subst p
        exact (by decide : ¬ Nat.Prime 6) hp
      have h6lt : 6 < p := by omega
      rw [Nat.mod_eq_of_lt h6lt] at hmodlin
      omega

theorem no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ n - 1) :
    False := by
  have hn_gt : 1 < n := by omega
  have hprod : p ∣ j * (j - 1) :=
    i_three_window_one_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 1 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one hp hp5 hj hlin hprod

theorem no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hpdvd : p ∣ n - 2) :
    False := by
  have hn_gt : 2 < n := by omega
  have hprod : p ∣ j * (j - 1) * (j - 2) :=
    i_three_window_two_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 2 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple hp hp5 hj hlin hprod

theorem twoPower_of_unique_prime_dvd_two {m : ℕ} (hm0 : m ≠ 0)
    (huniq : ∀ {p : ℕ}, p.Prime → p ∣ m → p = 2) :
    twoPower m := by
  exact ⟨m.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq⟩

theorem twoPower_of_no_prime_ge_five_and_not_three {m : ℕ} (hm0 : m ≠ 0)
    (hno5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ m) (hnot3 : ¬ 3 ∣ m) :
    twoPower m := by
  apply twoPower_of_unique_prime_dvd_two hm0
  intro p hp hpm
  by_cases hp2 : p = 2
  · exact hp2
  by_cases hp3 : p = 3
  · exact False.elim (hnot3 (by simpa [hp3] using hpm))
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp5 : 5 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega
  exact False.elim ((hno5 p hp hp5) hpm)

theorem not_three_dvd_sub_one_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 1 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega

theorem not_three_dvd_sub_two_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 2 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega

theorem twoPower_sub_one_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    twoPower (n - 1) := by
  apply twoPower_of_no_prime_ge_five_and_not_three
  · omega
  · intro p hp hp5 hpdvd
    exact no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul hnone hn_eq hp hp5 hj hpdvd
  · exact not_three_dvd_sub_one_of_eq_three_mul hn_eq hj

theorem twoPower_sub_two_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    twoPower (n - 2) := by
  apply twoPower_of_no_prime_ge_five_and_not_three
  · omega
  · intro p hp hp5 hpdvd
    exact no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul hnone hn_eq hp hp5 hj hpdvd
  · exact not_three_dvd_sub_two_of_eq_three_mul hn_eq (by omega)

theorem eq_three_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    n = 3 :=
  eq_three_of_sub_one_sub_two_twoPowers
    (twoPower_sub_one_of_no_common_eq_three_mul hnone hn_eq (by omega))
    (twoPower_sub_two_of_no_common_eq_three_mul hnone hn_eq hj)

theorem no_common_eq_three_mul_false_of_two_le {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    False := by
  have hn3 : n = 3 := eq_three_of_no_common_eq_three_mul hnone hn_eq hj
  omega

/-- Product of the prime divisors of `m` that are at least `lo`, without multiplicity. -/
def primeRadicalGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p

theorem prime_coprime_finset_prod_of_not_mem {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    p.Coprime (∏ q ∈ s, q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp_ne_a : p ≠ a := by
        intro hpa
        apply hnot
        rw [hpa]
        exact Finset.mem_insert_self a s
      have hpa_coprime : p.Coprime a :=
        (Nat.coprime_primes hp (hs a (Finset.mem_insert_self a s))).mpr hp_ne_a
      have hp_not_s : p ∉ s := by
        intro hps
        exact hnot (Finset.mem_insert_of_mem hps)
      have hprod : p.Coprime (∏ q ∈ s, q) :=
        ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) hp_not_s
      exact hpa_coprime.mul_right hprod

theorem finset_prod_primes_dvd_of_forall_dvd {s : Finset ℕ} {x : ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hdiv : ∀ p ∈ s, p ∣ x) :
    (∏ p ∈ s, p) ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hacoprime : a.Coprime (∏ p ∈ s, p) :=
        prime_coprime_finset_prod_of_not_mem (hprime a (Finset.mem_insert_self a s)) s
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)) ha
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hacoprime
        (hdiv a (Finset.mem_insert_self a s))
        (ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))

theorem primeRadicalGE_dvd_of_forall_prime_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ∣ x) :
    primeRadicalGE lo m ∣ x := by
  classical
  unfold primeRadicalGE
  apply finset_prod_primes_dvd_of_forall_dvd
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1
  · intro p hp_mem
    rcases Finset.mem_filter.mp hp_mem with ⟨hpm, hlo⟩
    exact h p (Nat.mem_primeFactors.mp hpm).1 hlo (Nat.mem_primeFactors.mp hpm).2.1

theorem i_three_window_one_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primeRadicalGE 5 (n - 1) ∣ j * (j - 1) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_one_product_forcing (p := p) hnone hp hp5 hn hpdvd

theorem i_three_window_two_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primeRadicalGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_two_product_forcing (p := p) hnone hp hp5 hn hpdvd

/-- Product of the full prime-power divisors of `m` whose prime is at least `lo`. -/
def primePowerPartGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p ^ m.factorization p

theorem prime_power_coprime_finset_prime_power_prod_of_not_mem {p : ℕ} {e : ℕ}
    {s : Finset ℕ} {f : ℕ → ℕ} (hp : p.Prime)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    (p ^ e).Coprime (∏ q ∈ s, q ^ f q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp_ne_a : p ≠ a := by
        intro hpa
        apply hnot
        rw [hpa]
        exact Finset.mem_insert_self a s
      have hpa_coprime : (p ^ e).Coprime (a ^ f a) :=
        Nat.coprime_pow_primes e (f a) hp
          (hs a (Finset.mem_insert_self a s)) hp_ne_a
      have hp_not_s : p ∉ s := by
        intro hps
        exact hnot (Finset.mem_insert_of_mem hps)
      have hprod : (p ^ e).Coprime (∏ q ∈ s, q ^ f q) :=
        ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) hp_not_s
      exact hpa_coprime.mul_right hprod

theorem finset_prod_prime_powers_dvd_of_forall_dvd {s : Finset ℕ} {e : ℕ → ℕ}
    {x : ℕ} (hprime : ∀ p ∈ s, p.Prime)
    (hdiv : ∀ p ∈ s, p ^ e p ∣ x) :
    (∏ p ∈ s, p ^ e p) ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hacoprime : (a ^ e a).Coprime (∏ p ∈ s, p ^ e p) :=
        prime_power_coprime_finset_prime_power_prod_of_not_mem
          (p := a) (e := e a) (s := s) (f := e)
          (hprime a (Finset.mem_insert_self a s))
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)) ha
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hacoprime
        (hdiv a (Finset.mem_insert_self a s))
        (ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))

theorem primePowerPartGE_dvd_of_forall_prime_power_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ^ m.factorization p ∣ x) :
    primePowerPartGE lo m ∣ x := by
  classical
  unfold primePowerPartGE
  apply finset_prod_prime_powers_dvd_of_forall_dvd
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1
  · intro p hp_mem
    rcases Finset.mem_filter.mp hp_mem with ⟨hpm, hlo⟩
    exact h p (Nat.mem_primeFactors.mp hpm).1 hlo (Nat.mem_primeFactors.mp hpm).2.1

theorem i_three_window_one_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primePowerPartGE 5 (n - 1) ∣ j * (j - 1) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hm_ne : n - 1 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 1).factorization p ∣ n - 1 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_one_prime_pow_dvd_mul_sub_one hnone hp hp5 hn hpowdvd

theorem i_three_window_two_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primePowerPartGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hm_ne : n - 2 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 2).factorization p ∣ n - 2 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two hnone hp hp5 hn hpowdvd

theorem primePowerPartGE_eq_self_of_forall_prime_ge {lo m : ℕ}
    (hm : m ≠ 0) (hlo : ∀ p : ℕ, p.Prime → p ∣ m → lo ≤ p) :
    primePowerPartGE lo m = m := by
  classical
  unfold primePowerPartGE
  have hfilter : m.primeFactors.filter (fun p => lo ≤ p) = m.primeFactors := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).1
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨hp, hlo p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1⟩
  rw [hfilter]
  simpa [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.prod_factorization_pow_eq_self hm

theorem primePowerPartGE_dvd_self {lo m : ℕ} (hm : m ≠ 0) :
    primePowerPartGE lo m ∣ m := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp _hlo _hpdvd
  exact (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl

theorem divisor_dvd_i_three_window_two_product_of_forall_prime_ge_five {d n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hd0 : d ≠ 0) (hdn : d ∣ n - 2)
    (hrel : ∀ p : ℕ, p.Prime → p ∣ d → 5 ≤ p) (hn : 2 < n) :
    d ∣ j * (j - 1) * (j - 2) := by
  have hd_eq : primePowerPartGE 5 d = d := by
    exact primePowerPartGE_eq_self_of_forall_prime_ge hd0 hrel
  rw [← hd_eq]
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hpow_dvd_d : p ^ d.factorization p ∣ d :=
    (hp.pow_dvd_iff_le_factorization hd0).mpr le_rfl
  have hpow_dvd_sub_two : p ^ d.factorization p ∣ n - 2 :=
    Nat.dvd_trans hpow_dvd_d hdn
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
    hnone hp hp5 hn hpow_dvd_sub_two

theorem finset_prod_prime_powers_coprime_four_of_ge_five {s : Finset ℕ}
    {f : ℕ → ℕ} (hge : ∀ p ∈ s, 5 ≤ p) (hprime : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p ^ f p).Coprime 4 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha_coprime_four : a.Coprime 4 := by
        exact (hprime a (Finset.mem_insert_self a s)).coprime_iff_not_dvd.mpr (by
          intro hdiv
          have ha_le_four : a ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hdiv
          have ha_ge_five : 5 ≤ a := hge a (Finset.mem_insert_self a s)
          omega)
      have hpow : (a ^ f a).Coprime 4 := ha_coprime_four.pow_left (f a)
      exact hpow.mul_left
        (ih (fun p hp => hge p (Finset.mem_insert_of_mem hp))
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)))

theorem primePowerPartGE_five_coprime_four (m : ℕ) :
    (primePowerPartGE 5 m).Coprime 4 := by
  classical
  unfold primePowerPartGE
  apply finset_prod_prime_powers_coprime_four_of_ge_five
  · intro p hp_mem
    exact (Finset.mem_filter.mp hp_mem).2
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1

theorem i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : 1 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) :
    n - 1 ∣ j * (j - 1) := by
  have hlarge : primePowerPartGE 5 (n - 1) = n - 1 := by
    apply primePowerPartGE_eq_self_of_forall_prime_ge
    · omega
    · intro p hp hpdvd
      by_cases hp2 : p = 2
      · subst p
        rcases h2n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      by_cases hp3 : p = 3
      · subst p
        rcases h3n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      have hp4 : p ≠ 4 := by
        intro hp_eq
        subst p
        exact (by decide : ¬ Nat.Prime 4) hp
      have hp2le : 2 ≤ p := hp.two_le
      omega
  rw [← hlarge]
  exact i_three_window_one_primePowerPartGE_dvd hnone hn

theorem sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (htX : t ≤ X) (hdvd : n - 1 ∣ j * (j - 1)) :
    n - 1 ∣ t * (X - t) := by
  let d := n - 1
  have hd_gt_one : 1 < d := by
    dsimp [d]
    omega
  have hn_mod_nat : n ≡ 1 [MOD d] := by
    have hn_eq : n = d * 1 + 1 := by
      dsimp [d]
      omega
    rw [hn_eq, Nat.ModEq]
    simp [Nat.mod_eq_of_lt hd_gt_one]
  have hFX_nat : F * X ≡ 1 [MOD d] := by
    simpa [d, hn] using hn_mod_nat
  have hFX_int : (F : ℤ) * (X : ℤ) ≡ 1 [ZMOD (d : ℤ)] := by
    exact_mod_cast hFX_nat
  have hzero_nat : j * (j - 1) ≡ 0 [MOD d] :=
    Nat.modEq_zero_iff_dvd.mpr (by simpa [d] using hdvd)
  have hzero_int : (j : ℤ) * ((j : ℤ) - 1) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast :
        ((j * (j - 1) : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hj_pos)]
      norm_num
    simpa [hcast] using (Int.natCast_modEq_iff.mpr hzero_nat)
  have hj_int : (j : ℤ) = (F : ℤ) * (t : ℤ) := by
    exact_mod_cast hj
  have hzero_Ft : ((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) ≡
      0 [ZMOD (d : ℤ)] := by
    simpa [hj_int] using hzero_int
  have hfirst : (X : ℤ) * ((F : ℤ) * (t : ℤ)) ≡ (t : ℤ) [ZMOD (d : ℤ)] := by
    have h := hFX_int.mul_right (t : ℤ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hsecond : (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 1) ≡
      (t : ℤ) - (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub] using h
  have hprod : ((X : ℤ) ^ 2) *
        (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1)) ≡
      (t : ℤ) * ((t : ℤ) - (X : ℤ)) [ZMOD (d : ℤ)] := by
    have h := hfirst.mul hsecond
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have hscaled_zero : ((X : ℤ) ^ 2) *
        (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1)) ≡
      0 [ZMOD (d : ℤ)] := by
    simpa using hzero_Ft.mul_left ((X : ℤ) ^ 2)
  have htx_zero : (t : ℤ) * ((t : ℤ) - (X : ℤ)) ≡ 0 [ZMOD (d : ℤ)] :=
    hprod.symm.trans hscaled_zero
  have htarget_int : ((t * (X - t) : ℕ) : ℤ) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast_sub : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) :=
      Nat.cast_sub htX
    have hcast :
        ((t * (X - t) : ℕ) : ℤ) =
          -((t : ℤ) * ((t : ℤ) - (X : ℤ))) := by
      rw [Nat.cast_mul, hcast_sub]
      ring
    simpa [hcast] using htx_zero.neg
  have hdvd_int : (d : ℤ) ∣ ((t * (X - t) : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.mp htarget_int
  exact Int.natCast_dvd_natCast.mp hdvd_int

theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    n - 1 ∣ t * (X - t) :=
  sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos htX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)

theorem i_three_caseI_row_one_exists_factor {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    ∃ g : ℕ, t * (X - t) = g * (n - 1) := by
  rcases i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n htX with ⟨g, hg⟩
  exact ⟨g, by simpa [mul_comm] using hg⟩

theorem central_branch_false_of_sub_one_dvd_t_mul_X_sub_t {n F X t : ℕ}
    (hn : n = F * X) (hn_gt : 2 < n) (hcentral : 2 * t = X)
    (hdvd : n - 1 ∣ t * (X - t)) : False := by
  have hcop_n : (n - 1).Coprime n := by
    have hsucc : n = (n - 1) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  have hX_dvd_n : X ∣ n := by
    rw [hn]
    exact dvd_mul_left X F
  have hcop_X : (n - 1).Coprime X :=
    Nat.Coprime.coprime_dvd_right hX_dvd_n hcop_n
  have ht_dvd_X : t ∣ X := by
    refine ⟨2, ?_⟩
    omega
  have hcop_t : (n - 1).Coprime t :=
    Nat.Coprime.coprime_dvd_right ht_dvd_X hcop_X
  have hXt : X - t = t := by omega
  have hdvd_tt : n - 1 ∣ t * t := by
    simpa [hXt] using hdvd
  have hdvd_t : n - 1 ∣ t := hcop_t.dvd_of_dvd_mul_left hdvd_tt
  have hself : (n - 1).Coprime (n - 1) :=
    Nat.Coprime.coprime_dvd_right hdvd_t hcop_t
  have hnm1_eq_one : n - 1 = 1 := by
    exact (Nat.coprime_self (n - 1)).mp hself
  omega

theorem i_three_caseI_central_branch_false {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcentral : 2 * t = X) : False :=
  central_branch_false_of_sub_one_dvd_t_mul_X_sub_t hn hn_gt hcentral
    (i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X))

theorem four_mul_t_mul_X_sub_t_le_sq {X t : ℕ} (h2tX : 2 * t ≤ X) :
    4 * (t * (X - t)) ≤ X * X := by
  have htX : t ≤ X := by omega
  have hcast_sub : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
  have hcalc :
      (4 : ℤ) * ((t : ℤ) * ((X : ℤ) - (t : ℤ))) ≤ (X : ℤ) * (X : ℤ) := by
    nlinarith [sq_nonneg ((X : ℤ) - 2 * (t : ℤ))]
  have h_int : ((4 * (t * (X - t)) : ℕ) : ℤ) ≤ ((X * X : ℕ) : ℤ) := by
    simpa [hcast_sub] using hcalc
  exact_mod_cast h_int

theorem four_mul_t_mul_X_sub_t_add_gap_sq_eq_sq {X t : ℕ} (h2tX : 2 * t ≤ X) :
    4 * (t * (X - t)) + (X - 2 * t) * (X - 2 * t) = X * X := by
  have htX : t ≤ X := by omega
  have hcast_Xt : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
  have hcast_gap : ((X - 2 * t : ℕ) : ℤ) = (X : ℤ) - 2 * (t : ℤ) := by
    have h :
        ((X - 2 * t : ℕ) : ℤ) = (X : ℤ) - ((2 * t : ℕ) : ℤ) :=
      Nat.cast_sub h2tX
    simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have h_int :
      ((4 * (t * (X - t)) + (X - 2 * t) * (X - 2 * t) : ℕ) : ℤ) =
        ((X * X : ℕ) : ℤ) := by
    simp [hcast_Xt, hcast_gap]
    ring
  exact_mod_cast h_int

theorem row_one_factor_gap_sq_eq_sq {n X t g : ℕ} (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    4 * (g * (n - 1)) + (X - 2 * t) * (X - 2 * t) = X * X := by
  simpa [hrow1] using four_mul_t_mul_X_sub_t_add_gap_sq_eq_sq (X := X) (t := t) h2tX

theorem four_mul_d_le_sq_of_dvd_t_mul_X_sub_t {d X t : ℕ}
    (ht_pos : 0 < t) (h2tX : 2 * t ≤ X) (hdvd : d ∣ t * (X - t)) :
    4 * d ≤ X * X := by
  have htX : t ≤ X := by omega
  have hXt_pos : 0 < X - t := by omega
  have hprod_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hd_le : d ≤ t * (X - t) := Nat.le_of_dvd hprod_pos hdvd
  exact (Nat.mul_le_mul_left 4 hd_le).trans (four_mul_t_mul_X_sub_t_le_sq h2tX)

theorem four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2tX : 2 * t ≤ X) (hdvd : n - 1 ∣ j * (j - 1)) :
    4 * (n - 1) ≤ X * X := by
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  exact four_mul_d_le_sq_of_dvd_t_mul_X_sub_t ht_pos h2tX
    (sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one
      hn hj hn_gt hj_pos (by omega : t ≤ X) hdvd)

theorem i_three_caseI_row_one_four_mul_sub_one_le_X_sq {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h2tX : 2 * t ≤ X) :
    4 * (n - 1) ≤ X * X :=
  four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos h2tX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)

theorem four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq {n F X : ℕ}
    (hn : n = F * X) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (hsize : 4 * (n - 1) ≤ X * X) :
    4 * F ≤ X := by
  by_contra hnot
  have hlt : X < 4 * F := Nat.lt_of_not_ge hnot
  have hn_pos : 0 < n := by
    subst n
    have hF_pos : 0 < F := by omega
    have hX_pos : 0 < X := by omega
    exact Nat.mul_pos hF_pos hX_pos
  have hcast_sub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
    Nat.cast_sub (by omega : 1 ≤ n)
  have hsize_int : (4 : ℤ) * ((n : ℤ) - 1) ≤ (X : ℤ) * (X : ℤ) := by
    have h := hsize
    have hcast : ((4 * (n - 1) : ℕ) : ℤ) = (4 : ℤ) * ((n : ℤ) - 1) := by
      rw [Nat.cast_mul, hcast_sub]
      norm_num
    have hcast_right : ((X * X : ℕ) : ℤ) = (X : ℤ) * (X : ℤ) := by norm_num
    exact hcast ▸ hcast_right ▸ (by exact_mod_cast h)
  have hn_int : (n : ℤ) = (F : ℤ) * (X : ℤ) := by exact_mod_cast hn
  have hdiff_ge_two_nat : 2 ≤ 4 * F - X := by
    rcases hX_even with ⟨a, ha⟩
    subst X
    have hdiff_pos : 0 < 4 * F - 2 * a := by omega
    have hdiff_even : 2 ∣ 4 * F - 2 * a := by
      refine ⟨2 * F - a, ?_⟩
      omega
    rcases hdiff_even with ⟨b, hb⟩
    have hb_pos : 0 < b := by omega
    omega
  have hcast_diff : ((4 * F - X : ℕ) : ℤ) = (4 : ℤ) * (F : ℤ) - (X : ℤ) :=
    Nat.cast_sub hlt.le
  have hdiff_ge_two : (2 : ℤ) ≤ (4 : ℤ) * (F : ℤ) - (X : ℤ) := by
    have h : (2 : ℤ) ≤ ((4 * F - X : ℕ) : ℤ) := by
      exact_mod_cast hdiff_ge_two_nat
    simpa [hcast_diff] using h
  have hX_four_int : (4 : ℤ) ≤ X := by exact_mod_cast hX_four
  nlinarith

theorem four_dvd_right_factor_of_four_dvd_mul_odd {F X : ℕ}
    (hFodd : Odd F) (h4 : 4 ∣ F * X) :
    4 ∣ X := by
  have h2mul : 2 ∣ F * X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
  have h2X : 2 ∣ X := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2mul with h2F | h2X
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2X
  rcases h2X with ⟨Y, hX⟩
  subst X
  have h2FY : 2 ∣ F * Y := by
    rcases h4 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hdouble : F * Y * 2 = (2 * a) * 2 := by
      calc
        F * Y * 2 = F * (2 * Y) := by ring
        _ = 4 * a := ha
        _ = (2 * a) * 2 := by ring
    exact Nat.mul_right_cancel (by decide : 0 < 2) hdouble
  have h2Y : 2 ∣ Y := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2FY with h2F | h2Y
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2Y
  rcases h2Y with ⟨Z, hY⟩
  refine ⟨Z, ?_⟩
  omega

theorem i_three_caseI_row_one_four_mul_factor_le_X {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (h2tX : 2 * t ≤ X) :
    4 * F ≤ X :=
  four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq hn hX_even hX_four
    (i_three_caseI_row_one_four_mul_sub_one_le_X_sq
      hnone hn hj hn_gt hj_pos h2n h3n h2tX)

theorem dvd_factor_mul_of_eq_mul_and_coprime {d e a b g : ℕ}
    (ha : a = g * d) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    e ∣ g * b := by
  have hdiv : e ∣ (g * b) * d := by
    simpa [ha, mul_assoc, mul_comm, mul_left_comm] using hedvd
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem exists_factor_dvd_factor_mul_of_dvd_and_coprime {d e a b : ℕ}
    (hda : d ∣ a) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    ∃ g : ℕ, a = g * d ∧ e ∣ g * b := by
  rcases hda with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · simpa [mul_comm] using hg
  · exact dvd_factor_mul_of_eq_mul_and_coprime (by simpa [mul_comm] using hg) hcop hedvd

theorem primePowerPartGE_five_sub_two_coprime_sub_one {n : ℕ} (hn : 2 < n) :
    (primePowerPartGE 5 (n - 2)).Coprime (n - 1) := by
  have hbase : (n - 2).Coprime (n - 1) := by
    have hsucc : n - 1 = (n - 2) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  exact Nat.Coprime.coprime_dvd_left
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0)) hbase

theorem half_sub_one_dvd_sub_two_of_even {n : ℕ} (h2n : 2 ∣ n) :
    n / 2 - 1 ∣ n - 2 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  refine ⟨2, ?_⟩
  omega

theorem half_sub_one_ne_zero_of_even {n : ℕ} (h2n : 2 ∣ n) (hn : 2 < n) :
    n / 2 - 1 ≠ 0 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  omega

theorem half_sub_one_ne_zero_of_even_three_dvd {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    n / 2 - 1 ≠ 0 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have h3m : 3 ∣ m := by
    have h3_two_mul : 3 ∣ 2 * m := by simpa [mul_comm] using h3n
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_two_mul with h32 | h3m
    · norm_num at h32
    · exact h3m
  rcases h3m with ⟨a, ha⟩
  omega

theorem not_two_dvd_of_coprime_four {d : ℕ} (hcop4 : d.Coprime 4) :
    ¬ 2 ∣ d := by
  intro h2d
  have h2g : 2 ∣ Nat.gcd d 4 := Nat.dvd_gcd h2d (by norm_num : 2 ∣ 4)
  have hgcd : Nat.gcd d 4 = 1 := hcop4.gcd_eq_one
  rw [hgcd] at h2g
  norm_num at h2g

theorem not_three_dvd_half_sub_one_of_even_three_dvd {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    ¬ 3 ∣ n / 2 - 1 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have h3m : 3 ∣ m := by
    have h3_two_mul : 3 ∣ 2 * m := by simpa [mul_comm] using h3n
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_two_mul with h32 | h3m
    · norm_num at h32
    · exact h3m
  intro h
  rcases h3m with ⟨a, ha⟩
  rcases h with ⟨b, hb⟩
  omega

theorem half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n)
    (hcop4 : (n / 2 - 1).Coprime 4) :
    ∀ p : ℕ, p.Prime → p ∣ n / 2 - 1 → 5 ≤ p := by
  intro p hp hpd
  by_cases hp2 : p = 2
  · subst p
    exact False.elim (not_two_dvd_of_coprime_four hcop4 hpd)
  by_cases hp3 : p = 3
  · subst p
    exact False.elim (not_three_dvd_half_sub_one_of_even_three_dvd h2n h3n hn hpd)
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp2le : 2 ≤ p := hp.two_le
  omega

theorem half_sub_one_coprime_sub_one_of_even {n : ℕ}
    (h2n : 2 ∣ n) (hn : 2 < n) :
    (n / 2 - 1).Coprime (n - 1) := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have hdiv : 2 * m / 2 = m := by omega
  have hsub_one : 2 * m - 1 = (m - 1) + ((m - 1) + 1) := by omega
  have hbase : (m - 1).Coprime ((m - 1) + 1) :=
    Nat.coprime_self_add_right.mpr (by simp)
  have htarget : (m - 1).Coprime ((m - 1) + ((m - 1) + 1)) :=
    Nat.coprime_self_add_right.mpr hbase
  rw [hdiv, hsub_one]
  exact htarget

theorem half_sub_one_coprime_four_of_four_dvd {n : ℕ}
    (h4n : 4 ∣ n) (hn : 2 < n) :
    (n / 2 - 1).Coprime 4 := by
  rcases h4n with ⟨m, hm⟩
  subst n
  have hdiv : 4 * m / 2 = 2 * m := by omega
  rw [hdiv]
  apply Nat.coprime_of_dvd
  intro p hp hpd hp4
  have hp_eq_two : p = 2 := by
    have hp_le_four : p ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hp4
    interval_cases p
    · exact False.elim ((by decide : ¬ Nat.Prime 0) hp)
    · exact False.elim ((by decide : ¬ Nat.Prime 1) hp)
    · rfl
    · exact False.elim (by norm_num at hp4)
    · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
  subst p
  rcases hpd with ⟨a, ha⟩
  omega

theorem primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd {n : ℕ}
    (h4n : 4 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) = n / 2 - 1 := by
  have h2n : 2 ∣ n := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4n
  exact primePowerPartGE_eq_self_of_forall_prime_ge
    (half_sub_one_ne_zero_of_even h2n hn)
    (half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four h2n h3n hn
      (half_sub_one_coprime_four_of_four_dvd h4n hn))

theorem primePowerPartGE_five_half_sub_one_coprime_sub_one {n : ℕ}
    (h2n : 2 ∣ n) (hn : 2 < n) :
    (primePowerPartGE 5 (n / 2 - 1)).Coprime (n - 1) :=
  Nat.Coprime.coprime_dvd_left
    (primePowerPartGE_dvd_self (half_sub_one_ne_zero_of_even h2n hn))
    (half_sub_one_coprime_sub_one_of_even h2n hn)

theorem i_three_caseI_half_sub_one_large_part_dvd_row_two_product {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (h2n : 2 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) ∣ j * (j - 1) * (j - 2) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hhalf_ne : n / 2 - 1 ≠ 0 := half_sub_one_ne_zero_of_even h2n hn
  have hpow_dvd_half : p ^ (n / 2 - 1).factorization p ∣ n / 2 - 1 :=
    (hp.pow_dvd_iff_le_factorization hhalf_ne).mpr le_rfl
  have hpow_dvd_sub_two : p ^ (n / 2 - 1).factorization p ∣ n - 2 :=
    Nat.dvd_trans hpow_dvd_half (half_sub_one_dvd_sub_two_of_even h2n)
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
    hnone hp hp5 hn hpow_dvd_sub_two

theorem i_three_caseI_half_sub_one_dvd_row_two_product {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n)
    (hcop4 : (n / 2 - 1).Coprime 4) :
    n / 2 - 1 ∣ j * (j - 1) * (j - 2) :=
  divisor_dvd_i_three_window_two_product_of_forall_prime_ge_five hnone
    (half_sub_one_ne_zero_of_even_three_dvd h2n h3n hn)
    (half_sub_one_dvd_sub_two_of_even h2n)
    (half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four h2n h3n hn hcop4)
    hn

theorem i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    (n - 1).Coprime (n / 2 - 1) ∧
      consecutiveDivisorKernelBelow (n - 1) (n / 2 - 1) n j := by
  have hcop : (n - 1).Coprime (n / 2 - 1) :=
    (half_sub_one_coprime_sub_one_of_even h2n hn_gt).symm
  have hrow1 : n - 1 ∣ j * (j - 1) :=
    i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n
  have hrow2 : n / 2 - 1 ∣ j * (j - 1) * (j - 2) :=
    i_three_caseI_half_sub_one_dvd_row_two_product hnone h2n h3n hn_gt
      (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)
  refine ⟨hcop, ?_⟩
  exact ⟨hjn, hrow1, hrow2⟩

theorem i_three_caseI_four_dvd_consecutive_kernel_in_range_from_no_common {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hj_gt : 3 < j) (hjn : 2 * j ≤ n) :
    (n - 1).Coprime (n / 2 - 1) ∧
      consecutiveDivisorKernelInRange (n - 1) (n / 2 - 1) 4 n j := by
  rcases i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common
      hnone hn_gt h2n h3n h4n hjn with
    ⟨hcop, hkernel⟩
  exact ⟨hcop, by omega, hkernel.1, hkernel.2⟩

theorem i_three_caseI_not_no_common_from_kernelInRange_empty {n j : ℕ}
    (hnoKernel :
      ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange (n - 1) (n / 2 - 1) 4 n t)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hj_gt : 3 < j) (hjn : 2 * j ≤ n) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q := by
  intro hnone
  exact
    hnoKernel
      ⟨j,
        (i_three_caseI_four_dvd_consecutive_kernel_in_range_from_no_common
          hnone hn_gt h2n h3n h4n hj_gt hjn).2⟩

theorem i_three_caseI_exists_common_from_kernelInRange_empty {n j : ℕ}
    (hnoKernel :
      ¬ ∃ t : ℕ, consecutiveDivisorKernelInRange (n - 1) (n / 2 - 1) 4 n t)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hj_gt : 3 < j) (hjn : 2 * j ≤ n) :
    ∃ q : ℕ, commonPrimeDivisor n 3 j q := by
  by_contra hnone_exists
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty hnoKernel
      hn_gt h2n h3n h4n hj_gt hjn
      (by
        intro q hq
        exact hnone_exists ⟨q, hq⟩)

theorem i_three_caseI_96_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 96) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 96 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 96) (j := j)
      (by simpa using not_exists_kernelInRange_95_47_4_96)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_96_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 96) :
    ∃ q : ℕ, commonPrimeDivisor 96 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 96) (j := j)
      (by simpa using not_exists_kernelInRange_95_47_4_96)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_6144_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 6144) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 6144 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 6144) (j := j)
      (by simpa using not_exists_kernelInRange_6143_3071_4_6144)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_6144_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 6144) :
    ∃ q : ℕ, commonPrimeDivisor 6144 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 6144) (j := j)
      (by simpa using not_exists_kernelInRange_6143_3071_4_6144)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_768_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 768) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 768 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 768) (j := j)
      (by simpa using not_exists_kernelInRange_767_383_4_768)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_768_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 768) :
    ∃ q : ℕ, commonPrimeDivisor 768 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 768) (j := j)
      (by simpa using not_exists_kernelInRange_767_383_4_768)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_1536_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 1536) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 1536 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 1536) (j := j)
      (by simpa using not_exists_kernelInRange_1535_767_4_1536)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_1536_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 1536) :
    ∃ q : ℕ, commonPrimeDivisor 1536 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 1536) (j := j)
      (by simpa using not_exists_kernelInRange_1535_767_4_1536)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_3072_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 3072) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 3072 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 3072) (j := j)
      (by simpa using not_exists_kernelInRange_3071_1535_4_3072)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_3072_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 3072) :
    ∃ q : ℕ, commonPrimeDivisor 3072 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 3072) (j := j)
      (by simpa using not_exists_kernelInRange_3071_1535_4_3072)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_12288_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 12288) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 12288 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 12288) (j := j)
      (by simpa using not_exists_kernelInRange_12287_6143_4_12288)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_12288_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 12288) :
    ∃ q : ℕ, commonPrimeDivisor 12288 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 12288) (j := j)
      (by simpa using not_exists_kernelInRange_12287_6143_4_12288)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_24576_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 24576) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 24576 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 24576) (j := j)
      (by simpa using not_exists_kernelInRange_24575_12287_4_24576)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_24576_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 24576) :
    ∃ q : ℕ, commonPrimeDivisor 24576 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 24576) (j := j)
      (by simpa using not_exists_kernelInRange_24575_12287_4_24576)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_49152_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 49152) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 49152 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 49152) (j := j)
      (by simpa using not_exists_kernelInRange_49151_24575_4_49152)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_49152_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 49152) :
    ∃ q : ℕ, commonPrimeDivisor 49152 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 49152) (j := j)
      (by simpa using not_exists_kernelInRange_49151_24575_4_49152)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_98304_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 98304) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 98304 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 98304) (j := j)
      (by simpa using not_exists_kernelInRange_98303_49151_4_98304)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_98304_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 98304) :
    ∃ q : ℕ, commonPrimeDivisor 98304 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 98304) (j := j)
      (by simpa using not_exists_kernelInRange_98303_49151_4_98304)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_196608_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 196608) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 196608 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 196608) (j := j)
      (by simpa using not_exists_kernelInRange_196607_98303_4_196608)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_196608_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 196608) :
    ∃ q : ℕ, commonPrimeDivisor 196608 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 196608) (j := j)
      (by simpa using not_exists_kernelInRange_196607_98303_4_196608)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_393216_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 393216) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 393216 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 393216) (j := j)
      (by simpa using not_exists_kernelInRange_393215_196607_4_393216)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_393216_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 393216) :
    ∃ q : ℕ, commonPrimeDivisor 393216 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 393216) (j := j)
      (by simpa using not_exists_kernelInRange_393215_196607_4_393216)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_786432_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 786432) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 786432 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 786432) (j := j)
      (by simpa using not_exists_kernelInRange_786431_393215_4_786432)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_786432_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 786432) :
    ∃ q : ℕ, commonPrimeDivisor 786432 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 786432) (j := j)
      (by simpa using not_exists_kernelInRange_786431_393215_4_786432)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_1572864_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 1572864) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 1572864 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 1572864) (j := j)
      (by simpa using not_exists_kernelInRange_1572863_786431_4_1572864)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_1572864_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 1572864) :
    ∃ q : ℕ, commonPrimeDivisor 1572864 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 1572864) (j := j)
      (by simpa using not_exists_kernelInRange_1572863_786431_4_1572864)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_3145728_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 3145728) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 3145728 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 3145728) (j := j)
      (by simpa using not_exists_kernelInRange_3145727_1572863_4_3145728)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_3145728_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 3145728) :
    ∃ q : ℕ, commonPrimeDivisor 3145728 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 3145728) (j := j)
      (by simpa using not_exists_kernelInRange_3145727_1572863_4_3145728)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_6291456_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 6291456) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 6291456 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 6291456) (j := j)
      (by simpa using not_exists_kernelInRange_6291455_3145727_4_6291456)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_6291456_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 6291456) :
    ∃ q : ℕ, commonPrimeDivisor 6291456 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 6291456) (j := j)
      (by simpa using not_exists_kernelInRange_6291455_3145727_4_6291456)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_12582912_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 12582912) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 12582912 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 12582912) (j := j)
      (by simpa using not_exists_kernelInRange_12582911_6291455_4_12582912)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_12582912_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 12582912) :
    ∃ q : ℕ, commonPrimeDivisor 12582912 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 12582912) (j := j)
      (by simpa using not_exists_kernelInRange_12582911_6291455_4_12582912)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_25165824_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 25165824) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 25165824 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 25165824) (j := j)
      (by simpa using not_exists_kernelInRange_25165823_12582911_4_25165824)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_25165824_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 25165824) :
    ∃ q : ℕ, commonPrimeDivisor 25165824 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 25165824) (j := j)
      (by simpa using not_exists_kernelInRange_25165823_12582911_4_25165824)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_50331648_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 50331648) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 50331648 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 50331648) (j := j)
      (by simpa using not_exists_kernelInRange_50331647_25165823_4_50331648)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_50331648_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 50331648) :
    ∃ q : ℕ, commonPrimeDivisor 50331648 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 50331648) (j := j)
      (by simpa using not_exists_kernelInRange_50331647_25165823_4_50331648)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_100663296_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 100663296) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 100663296 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 100663296) (j := j)
      (by simpa using not_exists_kernelInRange_100663295_50331647_4_100663296)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_100663296_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 100663296) :
    ∃ q : ℕ, commonPrimeDivisor 100663296 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 100663296) (j := j)
      (by simpa using not_exists_kernelInRange_100663295_50331647_4_100663296)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_201326592_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 201326592) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 201326592 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 201326592) (j := j)
      (by simpa using not_exists_kernelInRange_201326591_100663295_4_201326592)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_201326592_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 201326592) :
    ∃ q : ℕ, commonPrimeDivisor 201326592 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 201326592) (j := j)
      (by simpa using not_exists_kernelInRange_201326591_100663295_4_201326592)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_402653184_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 402653184) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 402653184 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 402653184) (j := j)
      (by simpa using not_exists_kernelInRange_402653183_201326591_4_402653184)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_402653184_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 402653184) :
    ∃ q : ℕ, commonPrimeDivisor 402653184 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 402653184) (j := j)
      (by simpa using not_exists_kernelInRange_402653183_201326591_4_402653184)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_805306368_not_no_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 805306368) :
    ¬ ∀ q : ℕ, ¬ commonPrimeDivisor 805306368 3 j q := by
  exact
    i_three_caseI_not_no_common_from_kernelInRange_empty
      (n := 805306368) (j := j)
      (by simpa using not_exists_kernelInRange_805306367_402653183_4_805306368)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem i_three_caseI_805306368_exists_common_from_row_bounds {j : ℕ}
    (hj_gt : 3 < j) (hjn : 2 * j ≤ 805306368) :
    ∃ q : ℕ, commonPrimeDivisor 805306368 3 j q := by
  exact
    i_three_caseI_exists_common_from_kernelInRange_empty
      (n := 805306368) (j := j)
      (by simpa using not_exists_kernelInRange_805306367_402653183_4_805306368)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj_gt hjn

theorem sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    {d n F X j t : ℕ} (hdn : d ∣ n - 2) (hcop4 : d.Coprime 4)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hj_two : 2 ≤ j)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hdvd : d ∣ j * (j - 1) * (j - 2)) :
    d ∣ t * (X - t) * (X - 2 * t) := by
  let target := t * (X - t) * (X - 2 * t)
  have hn_mod_int : (n : ℤ) ≡ 2 [ZMOD (d : ℤ)] := by
    rcases hdn with ⟨a, ha⟩
    have hsub_cast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Nat.cast_sub hn_ge_two
    have hdiff : (2 : ℤ) - (n : ℤ) = (d : ℤ) * (-(a : ℤ)) := by
      rw [← neg_sub]
      calc
        -((n : ℤ) - 2) = -((n - 2 : ℕ) : ℤ) := by rw [hsub_cast]
        _ = -((d * a : ℕ) : ℤ) := by rw [ha]
        _ = (d : ℤ) * (-(a : ℤ)) := by rw [Nat.cast_mul]; ring
    exact Int.modEq_iff_dvd.mpr ⟨-(a : ℤ), hdiff⟩
  have hFX_int : (F : ℤ) * (X : ℤ) ≡ 2 [ZMOD (d : ℤ)] := by
    have hn_int : (n : ℤ) = (F : ℤ) * (X : ℤ) := by exact_mod_cast hn
    simpa [hn_int] using hn_mod_int
  have hzero_nat : j * (j - 1) * (j - 2) ≡ 0 [MOD d] :=
    Nat.modEq_zero_iff_dvd.mpr hdvd
  have hzero_int :
      (j : ℤ) * ((j : ℤ) - 1) * ((j : ℤ) - 2) ≡ 0 [ZMOD (d : ℤ)] := by
    have hj_one : 1 ≤ j := by omega
    have hcast :
        ((j * (j - 1) * (j - 2) : ℕ) : ℤ) =
          (j : ℤ) * ((j : ℤ) - 1) * ((j : ℤ) - 2) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hj_one, Nat.cast_sub hj_two]
      norm_num
    simpa [hcast] using (Int.natCast_modEq_iff.mpr hzero_nat)
  have hj_int : (j : ℤ) = (F : ℤ) * (t : ℤ) := by exact_mod_cast hj
  have hzero_Ft :
      ((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
          (((F : ℤ) * (t : ℤ)) - 2) ≡ 0 [ZMOD (d : ℤ)] := by
    simpa [hj_int] using hzero_int
  have hfirst :
      (X : ℤ) * ((F : ℤ) * (t : ℤ)) ≡ 2 * (t : ℤ) [ZMOD (d : ℤ)] := by
    have h := hFX_int.mul_right (t : ℤ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hsecond :
      (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 1) ≡
        2 * (t : ℤ) - (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub] using h
  have hthird :
      (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 2) ≡
        2 * (t : ℤ) - 2 * (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (2 : ℤ) * (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub, two_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hprod_raw := (hfirst.mul hsecond).mul hthird
  have hprod :
      ((X : ℤ) ^ 3) *
          (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
            (((F : ℤ) * (t : ℤ)) - 2)) ≡
        4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ)))
          [ZMOD (d : ℤ)] := by
    convert hprod_raw using 1 <;> ring
  have hscaled_zero :
      ((X : ℤ) ^ 3) *
          (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
            (((F : ℤ) * (t : ℤ)) - 2)) ≡ 0 [ZMOD (d : ℤ)] := by
    simpa using hzero_Ft.mul_left ((X : ℤ) ^ 3)
  have hfour_target_zero :
      4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ))) ≡
        0 [ZMOD (d : ℤ)] :=
    hprod.symm.trans hscaled_zero
  have htarget_cast :
      ((target : ℕ) : ℤ) =
        (t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ)) := by
    have hcast_xt : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
    have hcast_x2t : ((X - 2 * t : ℕ) : ℤ) = (X : ℤ) - (2 * t : ℕ) :=
      Nat.cast_sub h2tX
    dsimp [target]
    rw [hcast_xt, hcast_x2t, Nat.cast_mul]
    norm_num
  have hfour_target_nat_int : (((4 * target : ℕ) : ℤ)) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast :
        (((4 * target : ℕ) : ℤ)) =
          4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ))) := by
      rw [Nat.cast_mul, htarget_cast]
      norm_num
    simpa [hcast] using hfour_target_zero
  have hdvd_four_int : (d : ℤ) ∣ ((4 * target : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.mp hfour_target_nat_int
  have hdvd_four_nat : d ∣ 4 * target := Int.natCast_dvd_natCast.mp hdvd_four_int
  exact hcop4.dvd_of_dvd_mul_left hdvd_four_nat

theorem i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t) :=
  sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0))
    (primePowerPartGE_five_coprime_four (n - 2)) hn hj hn_ge_two hj_two htX h2tX
    (i_three_window_two_primePowerPartGE_dvd hnone hn_gt_two)

theorem i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcop4 : (n / 2 - 1).Coprime 4)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    n / 2 - 1 ∣ t * (X - t) * (X - 2 * t) :=
  sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    (half_sub_one_dvd_sub_two_of_even h2n) hcop4 hn hj (by omega : 2 ≤ n)
    hj_two htX h2tX
    (i_three_caseI_half_sub_one_dvd_row_two_product hnone h2n h3n hn_gt hcop4)

theorem i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n / 2 - 1) ∣ t * (X - t) * (X - 2 * t) := by
  have hlarge_dvd_sub_two : primePowerPartGE 5 (n / 2 - 1) ∣ n - 2 :=
    Nat.dvd_trans
      (primePowerPartGE_dvd_self (half_sub_one_ne_zero_of_even h2n hn_gt))
      (half_sub_one_dvd_sub_two_of_even h2n)
  exact sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    hlarge_dvd_sub_two (primePowerPartGE_five_coprime_four (n / 2 - 1))
    hn hj (by omega : 2 ≤ n) hj_two htX h2tX
    (i_three_caseI_half_sub_one_large_part_dvd_row_two_product hnone h2n hn_gt)

theorem i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (primePowerPartGE_five_sub_two_coprime_sub_one hn_gt_two)
    (i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_ge_two hn_gt_two hj_two htX h2tX)

theorem i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcop4 : (n / 2 - 1).Coprime 4)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    n / 2 - 1 ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (half_sub_one_coprime_sub_one_of_even h2n hn_gt)
    (i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n h3n hcop4 htX h2tX)

theorem i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (primePowerPartGE_five_half_sub_one_coprime_sub_one h2n hn_gt)
    (i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n htX h2tX)

theorem i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) := by
  have hdvd :
      primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
      (by omega : t ≤ X) (by omega : 2 * t ≤ X) hrow1
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hXt_pos : 0 < X - t := by omega
  have hleft_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hright_pos : 0 < g * (n - 1) := by
    simpa [hrow1] using hleft_pos
  have hg_pos : 0 < g := by
    by_cases hg0 : g = 0
    · subst g
      simp at hright_pos
    · exact Nat.pos_of_ne_zero hg0
  exact Nat.le_of_dvd (Nat.mul_pos hg_pos hbranch) hdvd

theorem i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) := by
  have hdvd : primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n (by omega : t ≤ X) (by omega : 2 * t ≤ X)
      hrow1
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hXt_pos : 0 < X - t := by omega
  have hleft_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hright_pos : 0 < g * (n - 1) := by
    simpa [hrow1] using hleft_pos
  have hg_pos : 0 < g := by
    by_cases hg0 : g = 0
    · subst g
      simp at hright_pos
    · exact Nat.pos_of_ne_zero hg0
  exact Nat.le_of_dvd (Nat.mul_pos hg_pos hbranch) hdvd

theorem i_three_caseI_joint_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * (X - 2 * t) := by
  have hlarge :
      primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) :=
    i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two hrow1 hbranch
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  calc
    4 * ((n - 1) * primePowerPartGE 5 (n - 2))
        ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
          exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hlarge)
    _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
    _ ≤ (X * X) * (X - 2 * t) := by
          exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
    _ = X * X * (X - 2 * t) := by ring

theorem i_three_caseI_joint_half_sub_one_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * (X - 2 * t) := by
  have hlarge : primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  calc
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1))
        ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
          exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hlarge)
    _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
    _ ≤ (X * X) * (X - 2 * t) := by
          exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
    _ = X * X * (X - 2 * t) := by ring

theorem i_three_caseI_joint_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  have hgap :=
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  have hgap_le : X - 2 * t ≤ X := Nat.sub_le X (2 * t)
  exact hgap.trans (by
    simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) hgap_le)

theorem i_three_caseI_joint_half_sub_one_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  have hgap :=
    i_three_caseI_joint_half_sub_one_large_part_gap_bound
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch
  have hgap_le : X - 2 * t ≤ X := Nat.sub_le X (2 * t)
  exact hgap.trans (by
    simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) hgap_le)

theorem i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hrow1⟩
  exact ⟨g, hrow1,
    i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n (by omega : t ≤ X) (by omega : 2 * t ≤ X)
      hrow1,
    i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch,
    i_three_caseI_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch⟩

theorem i_three_caseI_noncentral_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem i_three_caseI_exists_joint_large_part_factor {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h2tX : 2 * t ≤ X) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hg⟩
  exact ⟨g, hg,
    i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two (by omega : t ≤ X) h2tX hg⟩

theorem i_three_caseI_exists_joint_large_part_factor_le {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) := by
  rcases i_three_caseI_exists_joint_large_part_factor
      hnone hn hj hn_gt hj_pos hj_two h2n h3n (by omega : 2 * t ≤ X) with
    ⟨g, hrow1, hdvd⟩
  exact ⟨g, hrow1, hdvd,
    i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two hrow1 hbranch⟩

theorem i_three_caseI_exists_joint_large_part_gap_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤
              X * X * (X - 2 * t) := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩

theorem i_three_caseI_exists_joint_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_gap_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle, _hgap⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩

theorem i_three_caseI_joint_lower_part_cube_bound {n F X j t g L : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) (hL : L ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * L) ≤ X * X * X := by
  have hcube :=
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  exact (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hL)).trans hcube

theorem i_three_caseI_joint_half_sub_one_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X :=
  i_three_caseI_joint_lower_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch hhalf

theorem i_three_caseI_exists_joint_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_two hrow1 hbranch hhalf⟩

theorem i_three_caseI_noncentral_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch hhalf with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem two_mul_factor_sq_le_of_even_half_cube_bound {n F X : ℕ}
    (hn : n = F * X) (hn_gt : 2 < n) (hX_even : 2 ∣ X)
    (hbound : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X) :
    2 * (F * F) ≤ X := by
  rcases hX_even with ⟨a, ha⟩
  subst X
  subst n
  have hdouble : F * (2 * a) = 2 * (F * a) := by ring
  have hFa_gt_one : 1 < F * a := by
    have hlt_double : 2 * 1 < 2 * (F * a) := by
      simpa [hdouble] using hn_gt
    exact Nat.lt_of_mul_lt_mul_left hlt_double
  by_contra hnot
  have hlt2 : 2 * a < 2 * (F * F) := Nat.lt_of_not_ge hnot
  have hlt : a < F * F := Nat.lt_of_mul_lt_mul_left hlt2
  have ha_pos : 0 < a := by
    by_contra hapos
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hapos
    subst a
    simp at hFa_gt_one
  have hF_ge_two : 2 ≤ F := by
    by_contra hFnot
    have hFlt2 : F < 2 := Nat.lt_of_not_ge hFnot
    interval_cases F <;> omega
  let k : ℕ := F * F - a
  have hk_pos : 0 < k := by
    dsimp [k]
    omega
  have hsum_int : (a : ℤ) + (k : ℤ) = (F : ℤ) * (F : ℤ) := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : a ≤ F * F), Nat.cast_mul]
    ring
  have ha_int : (1 : ℤ) ≤ a := by exact_mod_cast ha_pos
  have hk_int : (1 : ℤ) ≤ k := by exact_mod_cast hk_pos
  have hprod_lower_int : (F : ℤ) * (F : ℤ) - 1 ≤ (a : ℤ) * (k : ℤ) := by
    have hnonneg : (0 : ℤ) ≤ ((a : ℤ) - 1) * ((k : ℤ) - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have htwo_lower_int : (3 : ℤ) * (F : ℤ) ≤ 2 * ((F : ℤ) * (F : ℤ) - 1) := by
    have hF_int : (2 : ℤ) ≤ F := by exact_mod_cast hF_ge_two
    nlinarith
  have hkey_int : (3 : ℤ) * (F : ℤ) ≤ 2 * ((a : ℤ) * (k : ℤ)) := by
    nlinarith
  have hk_eq_int : ((k : ℕ) : ℤ) = (F : ℤ) * (F : ℤ) - (a : ℤ) := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : a ≤ F * F), Nat.cast_mul]
  have hF2a_ge_one : 1 ≤ F * (2 * a) := by omega
  have hcast1 : ((F * (2 * a) - 1 : ℕ) : ℤ) = (F : ℤ) * (2 * (a : ℤ)) - 1 := by
    rw [Nat.cast_sub hF2a_ge_one, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hcast2 : ((F * (2 * a) / 2 - 1 : ℕ) : ℤ) = (F : ℤ) * (a : ℤ) - 1 := by
    have hdiv : F * (2 * a) / 2 = F * a := by omega
    rw [hdiv, Nat.cast_sub (Nat.le_of_lt hFa_gt_one), Nat.cast_mul]
    norm_num
  have hbound_int :
      (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) * ((F : ℤ) * (a : ℤ) - 1)) ≤
        (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
    have h := hbound
    have hleft :
        ((4 * (((F * (2 * a) - 1) * (F * (2 * a) / 2 - 1))) : ℕ) : ℤ) =
          (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) *
            ((F : ℤ) * (a : ℤ) - 1)) := by
      rw [Nat.cast_mul, Nat.cast_mul, hcast1, hcast2]
      norm_num
    have hright : (((2 * a) * (2 * a) * (2 * a) : ℕ) : ℤ) =
        (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
      norm_num
    exact hleft ▸ hright ▸ (by exact_mod_cast h)
  have hmain_pos :
      (0 : ℤ) <
        (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) * ((F : ℤ) * (a : ℤ) - 1)) -
          (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
    rw [hk_eq_int] at hkey_int
    nlinarith
  nlinarith

theorem i_three_caseI_noncentral_factor_sq_squeeze {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X :=
  two_mul_factor_sq_le_of_even_half_cube_bound hn hn_gt hX_even
    (i_three_caseI_noncentral_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch hhalf)

theorem i_three_caseI_factor_sq_squeeze_of_half_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (h2tX : 2 * t ≤ X) (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X := by
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · have hbranch : 0 < X - 2 * t := by omega
    exact i_three_caseI_noncentral_factor_sq_squeeze
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hbranch hhalf

theorem i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hbranch : 0 < X - 2 * t) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hrow1⟩
  have hdvd : n / 2 - 1 ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n h3n hcop4 (by omega : t ≤ X)
      (by omega : 2 * t ≤ X) hrow1
  have hle : n / 2 - 1 ≤ g * (X - 2 * t) := by
    have ht_pos : 0 < t := by
      by_cases ht0 : t = 0
      · subst t
        simp at hj
        omega
      · exact Nat.pos_of_ne_zero ht0
    have hXt_pos : 0 < X - t := by omega
    have hleft_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
    have hright_pos : 0 < g * (n - 1) := by
      simpa [hrow1] using hleft_pos
    have hg_pos : 0 < g := by
      by_cases hg0 : g = 0
      · subst g
        simp at hright_pos
      · exact Nat.pos_of_ne_zero hg0
    exact Nat.le_of_dvd (Nat.mul_pos hg_pos hbranch) hdvd
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  have hgap : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * (X - 2 * t) := by
    calc
      4 * ((n - 1) * (n / 2 - 1))
          ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
            exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hle)
      _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
      _ ≤ (X * X) * (X - 2 * t) := by
            exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
      _ = X * X * (X - 2 * t) := by ring
  have hcube : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
    exact hgap.trans (by
      simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) (Nat.sub_le X (2 * t)))
  exact two_mul_factor_sq_le_of_even_half_cube_bound hn hn_gt hX_even hcube

theorem i_three_caseI_factor_sq_squeeze_of_half_coprime_four {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (h2tX : 2 * t ≤ X) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X := by
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · have hbranch : 0 < X - 2 * t := by omega
    exact i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hbranch hcop4

theorem two_mul_t_le_X_of_factorized_half_bound {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hj_pos : 0 < j) (hjn : 2 * j ≤ n) :
    2 * t ≤ X := by
  have hF_pos : 0 < F := by
    by_cases hF0 : F = 0
    · subst F
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero hF0
  subst n
  subst j
  have hmul : F * (2 * t) ≤ F * X := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hjn
  exact Nat.le_of_mul_le_mul_left hmul hF_pos

theorem t_le_X_of_factorized_half_bound {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hj_pos : 0 < j) (hjn : 2 * j ≤ n) :
    t ≤ X := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  omega

theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    n - 1 ∣ t * (X - t) :=
  i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
    hnone hn hj hn_gt hj_pos h2n h3n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_exists_factor_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ, t * (X - t) = g * (n - 1) :=
  i_three_caseI_row_one_exists_factor
    hnone hn hj hn_gt hj_pos h2n h3n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_sub_one_le_X_sq_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    4 * (n - 1) ≤ X * X :=
  i_three_caseI_row_one_four_mul_sub_one_le_X_sq
    hnone hn hj hn_gt hj_pos h2n h3n
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (hjn : 2 * j ≤ n) :
    4 * F ≤ X :=
  i_three_caseI_row_one_four_mul_factor_le_X
    hnone hn hj hn_gt hj_pos h2n h3n hX_even hX_four
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n) (hFodd : Odd F)
    (hjn : 2 * j ≤ n) :
    4 * F ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  have hX_pos : 0 < X := by
    by_contra hnot
    have hX0 : X = 0 := Nat.eq_zero_of_not_pos hnot
    subst X
    omega
  have hX_four : 4 ≤ X := Nat.le_of_dvd hX_pos h4X
  exact i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound
    hnone hn hj hn_gt hj_pos h2n h3n hX_even hX_four hjn

theorem i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (hjn : 2 * j ≤ n) :
    primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n)
    (hcop4 : (n / 2 - 1).Coprime 4) (hjn : 2 * j ≤ n) :
    n / 2 - 1 ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n h3n hcop4
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_two_half_large_part_dvd_triple_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hjn : 2 * j ≤ n) :
    primePowerPartGE 5 (n / 2 - 1) ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
    hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n)
    (hcop4 : (n / 2 - 1).Coprime 4) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    n / 2 - 1 ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n h3n hcop4
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem x_sub_two_t_pos_of_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    0 < X - 2 * t := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · omega

theorem i_three_caseI_exists_joint_large_part_factor_le_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) :=
  i_three_caseI_exists_joint_large_part_factor_le
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_large_part_gap_bound_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤
              X * X * (X - 2 * t) :=
  i_three_caseI_exists_joint_large_part_gap_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_large_part_cube_bound_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X :=
  i_three_caseI_exists_joint_large_part_cube_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X :=
  i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_half_large_part_cube_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hjn with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  have hlarge :=
    i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hjn
  simpa [primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd
    h4n h3n hn_gt] using hlarge

theorem i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem i_three_caseI_factor_sq_squeeze_of_half_bound_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hjn : 2 * j ≤ n) (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hhalf

theorem i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hjn : 2 * j ≤ n) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_coprime_four
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hcop4

theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hX_even : 2 ∣ X) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hjn
    (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)

theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  exact i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hX_even hjn

theorem i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X ∧
              4 * F ≤ X ∧
                2 * (F * F) ≤ X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨g, hrow1, hdvd, hle, hcube⟩
  have hrow :
      4 * F ≤ X :=
    i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos h2n h3n h4n hFodd hjn
  have hsq :
      2 * (F * F) ≤ X :=
    i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn
  exact ⟨g, hrow1, hdvd, hle, hcube, hrow, hsq⟩

theorem i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    4 * F ≤ X ∧ 2 * (F * F) ≤ X := by
  rcases
      i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
        hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn with
    ⟨_g, _hrow1, _hdvd, _hle, _hcube, hrow, hsq⟩
  exact ⟨hrow, hsq⟩

def squeezedNormalizedCaseIKernel (F X t g : ℕ) : Prop :=
  0 < F ∧
    0 < X ∧
      0 < t ∧
        Odd F ∧
          4 ∣ X ∧
            3 ≤ F ∧
              2 * t < X ∧
                4 * F ≤ X ∧
                  2 * (F * F) ≤ X ∧
                    t * (X - t) = g * (F * X - 1) ∧
                      F * X / 2 - 1 ∣ g * (X - 2 * t)

def squeezedNormalizedRowOneCandidate (F X t g : ℕ) : Prop :=
  0 < F ∧
    0 < X ∧
      0 < t ∧
        Odd F ∧
          4 ∣ X ∧
            3 ≤ F ∧
              2 * t < X ∧
                4 * F ≤ X ∧
                  2 * (F * F) ≤ X ∧
                    t * (X - t) = g * (F * X - 1)

/-- Normalized row-`n` digit-power constraint: every odd prime-power part of
`X` with prime at least the row index `3` must also divide `u`. -/
def rowNDigitPowerConstraint (X u : ℕ) : Prop :=
  ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p → p ^ e ∣ X → p ^ e ∣ u

/-- Exact guarded variant of `rowNDigitPowerConstraint`: require the
prime-power transfer only when row `3` is not digit-dominated by `F * X` at
that prime. The argument order in `dominated` is `k n p`. -/
def rowNDigitPowerConstraintExact (F X u : ℕ) : Prop :=
  ∀ ⦃p e : ℕ⦄,
    Nat.Prime p → 3 ≤ p → ¬ dominated 3 (F * X) p → p ^ e ∣ X → p ^ e ∣ u

theorem rowNDigitPowerConstraintExact_of_rowNDigitPowerConstraint {F X u : ℕ}
    (h : rowNDigitPowerConstraint X u) :
    rowNDigitPowerConstraintExact F X u := by
  intro p e hp hp3 _hnot hpow
  exact h hp hp3 hpow

theorem not_rowNDigitPowerConstraint_of_prime_power_counterexample
    {X u p e : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hX : p ^ e ∣ X) (hu : ¬ p ^ e ∣ u) :
    ¬ rowNDigitPowerConstraint X u := by
  intro h
  exact hu (h hp hp3 hX)

/-- Any prime divisor of an odd natural number is at least `3`. -/
theorem odd_prime_divisor_ge_three {H p : ℕ} (hHodd : Odd H)
    (hp : Nat.Prime p) (hpd : p ∣ H) :
    3 ≤ p := by
  rw [← hp.odd_iff]
  rw [← Nat.not_even_iff_odd]
  intro hpeven
  have hp2 : p = 2 := hp.even_iff.mp hpeven
  subst p
  exact hHodd.not_two_dvd_nat hpd

/-- Extract a full divisor from the row-`n` digit-power condition when every
prime divisor of that factor is relevant for row `3`. This is the formal
version of turning the odd prime-power part of `X` into a divisor of `u`. -/
theorem rowNDigitPowerConstraint.dvd_of_factor_dvd
    {X u H : ℕ} (hrow : rowNDigitPowerConstraint X u) (hHX : H ∣ X)
    (hH0 : H ≠ 0) (hprime : ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p) :
    H ∣ u := by
  by_cases hu0 : u = 0
  · subst u
    exact dvd_zero H
  · rw [← Nat.factorization_prime_le_iff_dvd hH0 hu0]
    intro p hp
    by_cases hHp0 : H.factorization p = 0
    · simp [hHp0]
    · have hp_dvd_H : p ∣ H := by
        rw [hp.dvd_iff_one_le_factorization hH0]
        omega
      have hp3 : 3 ≤ p := hprime p hp hp_dvd_H
      have hpowH : p ^ H.factorization p ∣ H := by
        rw [hp.pow_dvd_iff_le_factorization hH0]
      have hpowX : p ^ H.factorization p ∣ X := Nat.dvd_trans hpowH hHX
      have hpowu : p ^ H.factorization p ∣ u := hrow hp hp3 hpowX
      exact (hp.pow_dvd_iff_le_factorization hu0).mp hpowu

/-- Guarded divisor extraction for the exact row-`n` digit-power condition.
Only prime powers whose prime also satisfies the Lucas guard
`¬ dominated 3 (F*X) p` are transferred to `u`; primes outside that guard
remain free. -/
theorem rowNDigitPowerConstraintExact.dvd_of_factor_dvd
    {F X u H : ℕ} (hrow : rowNDigitPowerConstraintExact F X u) (hHX : H ∣ X)
    (hH0 : H ≠ 0)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 (F * X) p) :
    H ∣ u := by
  by_cases hu0 : u = 0
  · subst u
    exact dvd_zero H
  · rw [← Nat.factorization_prime_le_iff_dvd hH0 hu0]
    intro p hp
    by_cases hHp0 : H.factorization p = 0
    · simp [hHp0]
    · have hp_dvd_H : p ∣ H := by
        rw [hp.dvd_iff_one_le_factorization hH0]
        omega
      rcases hprime p hp hp_dvd_H with ⟨hp3, hnotdom⟩
      have hpowH : p ^ H.factorization p ∣ H := by
        rw [hp.pow_dvd_iff_le_factorization hH0]
      have hpowX : p ^ H.factorization p ∣ X := Nat.dvd_trans hpowH hHX
      have hpowu : p ^ H.factorization p ∣ u :=
        hrow hp hp3 hnotdom hpowX
      exact (hp.pow_dvd_iff_le_factorization hu0).mp hpowu

/-- The pure power-of-two quotient kernel isolated after imposing the
normalized row-`n` digit-power constraint. The conjectural next lemma is that
this predicate is empty. -/
def powerTwoQuotientKernel (A B v h : ℕ) : Prop :=
  4 ∣ A ∧
    (∃ a : ℕ, A = 2 ^ a) ∧
      Odd B ∧
        3 ≤ B ∧
          0 < v ∧
            0 < A - 2 * v ∧
              v * (A - v) = h * (B * A - 1) ∧
                B * (A / 2) - 1 ∣ h * (A - 2 * v)

/-- The isolated split/gcd obstruction for the pure power-of-two quotient
kernel. This is a hypothesis surface for the remaining C2 work, not a proved
theorem: proving this predicate for all admissible `A, B` is exactly the
missing split/gcd obstruction. -/
def powerTwoSplitGcdObstruction (A B : ℕ) : Prop :=
  (∃ a : ℕ, A = 2 ^ a) →
    4 ∣ A →
      Odd B →
        3 ≤ B →
          ∀ r s l m alpha beta c : ℕ,
            0 < r →
              0 < s →
                0 < l →
                  0 < m →
                    r * s = B * A - 1 →
                      r * l + s * m = A →
                        r * l < s * m →
                          alpha = r - B * m →
                            beta = s - B * l →
                              c = Nat.gcd alpha beta →
                                ¬ B * (A / 2) - 1 ∣ c * (l * m)

/-- Direct consumer for a stated `powerTwoSplitGcdObstruction`. -/
theorem powerTwoSplitGcdObstruction.not_dvd {A B r s l m alpha beta c : ℕ}
    (hobs : powerTwoSplitGcdObstruction A B)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hc : c = Nat.gcd alpha beta) :
    ¬ B * (A / 2) - 1 ∣ c * (l * m) :=
  hobs hApow hA4 hBodd hBge r s l m alpha beta c hrpos hspos hlpos hmpos
    hD hA hgap halpha hbeta hc

/-- Additive alpha/beta form of the split algebra. The statement deliberately
uses `r = B * m + alpha` and `s = B * l + beta`; this avoids deriving facts
from truncated natural subtraction in the still-open split/gcd obstruction. -/
theorem powerTwoSplitAdditive_alpha_beta_mul {A B r s l m alpha beta : ℕ}
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : r = B * m + alpha)
    (hbeta : s = B * l + beta) :
    alpha * beta + 1 = B * B * (l * m) := by
  have hDadd : r * s + 1 = B * A := by
    have hBApos : 0 < B * A := Nat.mul_pos hBpos hApos
    omega
  subst r
  subst s
  rw [← hA] at hDadd
  nlinarith

/-- Product identity coprimality: if `alpha * beta + 1` is a multiple of
`l * m`, then the common divisor of `alpha` and `beta` is coprime to
`l * m`. -/
theorem gcd_alpha_beta_coprime_l_mul_m_of_product_identity
    {K l m alpha beta c : ℕ}
    (hc : c = Nat.gcd alpha beta)
    (hab : alpha * beta + 1 = K * (l * m)) :
    c.Coprime (l * m) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let e := Nat.gcd c (l * m)
  apply Nat.eq_one_of_dvd_one
  have hec : e ∣ c := Nat.gcd_dvd_left c (l * m)
  have heLm : e ∣ l * m := Nat.gcd_dvd_right c (l * m)
  have hc_alpha : c ∣ alpha := by
    rw [hc]
    exact Nat.gcd_dvd_left alpha beta
  have healpha : e ∣ alpha := Nat.dvd_trans hec hc_alpha
  have healphabeta : e ∣ alpha * beta := dvd_mul_of_dvd_left healpha beta
  have heRhs : e ∣ K * (l * m) := dvd_mul_of_dvd_right heLm K
  have heSucc : e ∣ alpha * beta + 1 := by
    rw [hab]
    exact heRhs
  have hone : e ∣ (alpha * beta + 1) - alpha * beta :=
    Nat.dvd_sub heSucc healphabeta
  simpa using hone

/-- Integer form of the first subtractive split identity. It is the algebraic
reason the natural subtraction `r - B * m` is non-truncated in every positive
row-one split with `B ≥ 3`. -/
theorem powerTwoSplit_alpha_int_identity {A B r s l m : ℕ}
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A) :
    (s : ℤ) * ((r : ℤ) - (B : ℤ) * (m : ℤ)) =
      (B : ℤ) * (r : ℤ) * (l : ℤ) - 1 := by
  have hDadd : r * s + 1 = B * A := by
    have hBApos : 0 < B * A := Nat.mul_pos hBpos hApos
    omega
  have hDaddZ : (r : ℤ) * (s : ℤ) + 1 = (B : ℤ) * (A : ℤ) := by
    exact_mod_cast hDadd
  have hAZ : (r : ℤ) * (l : ℤ) + (s : ℤ) * (m : ℤ) = (A : ℤ) := by
    exact_mod_cast hA
  nlinarith

/-- Integer form of the second subtractive split identity. -/
theorem powerTwoSplit_beta_int_identity {A B r s l m : ℕ}
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A) :
    (r : ℤ) * ((s : ℤ) - (B : ℤ) * (l : ℤ)) =
      (B : ℤ) * (s : ℤ) * (m : ℤ) - 1 := by
  have hDadd : r * s + 1 = B * A := by
    have hBApos : 0 < B * A := Nat.mul_pos hBpos hApos
    omega
  have hDaddZ : (r : ℤ) * (s : ℤ) + 1 = (B : ℤ) * (A : ℤ) := by
    exact_mod_cast hDadd
  have hAZ : (r : ℤ) * (l : ℤ) + (s : ℤ) * (m : ℤ) = (A : ℤ) := by
    exact_mod_cast hA
  nlinarith

/-- In every positive row-one split with `B ≥ 3`, the subtractive alpha/beta
terms are genuinely positive: `B * m < r` and `B * l < s`. -/
theorem powerTwoSplitSubtractive_lt {A B r s l m : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A) :
    B * m < r ∧ B * l < s := by
  have hBpos : 0 < B := by omega
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have halpha_id := powerTwoSplit_alpha_int_identity
    (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
    hBpos hApos hD hA
  have hbeta_id := powerTwoSplit_beta_int_identity
    (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
    hBpos hApos hD hA
  have hBrl_ge_nat : 3 ≤ B * r * l := by
    have hBr : 3 ≤ B * r := by
      have hmul := Nat.mul_le_mul hBge hrpos
      simpa using hmul
    have hBrl : 3 * 1 ≤ (B * r) * l := Nat.mul_le_mul hBr hlpos
    simpa [mul_assoc] using hBrl
  have hBsm_ge_nat : 3 ≤ B * s * m := by
    have hBs : 3 ≤ B * s := by
      have hmul := Nat.mul_le_mul hBge hspos
      simpa using hmul
    have hBsm : 3 * 1 ≤ (B * s) * m := Nat.mul_le_mul hBs hmpos
    simpa [mul_assoc] using hBsm
  have hBrl_ge : (3 : ℤ) ≤ (B : ℤ) * (r : ℤ) * (l : ℤ) := by
    exact_mod_cast hBrl_ge_nat
  have hBsm_ge : (3 : ℤ) ≤ (B : ℤ) * (s : ℤ) * (m : ℤ) := by
    exact_mod_cast hBsm_ge_nat
  have hleft_prod_pos : (0 : ℤ) < (B : ℤ) * (r : ℤ) * (l : ℤ) - 1 := by
    nlinarith
  have hright_prod_pos : (0 : ℤ) < (B : ℤ) * (s : ℤ) * (m : ℤ) - 1 := by
    nlinarith
  have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hspos
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hrpos
  have hbm_lt_r_Z : (B : ℤ) * (m : ℤ) < (r : ℤ) := by
    nlinarith
  have hbl_lt_s_Z : (B : ℤ) * (l : ℤ) < (s : ℤ) := by
    nlinarith
  constructor
  · exact_mod_cast hbm_lt_r_Z
  · exact_mod_cast hbl_lt_s_Z

/-- The subtractive alpha/beta definitions in the split/gcd obstruction are
equivalent to the additive form required by the split product identity. -/
theorem powerTwoSplitSubtractive_to_additive {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    r = B * m + alpha ∧ s = B * l + beta := by
  rcases powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r) (s := s)
    (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA with ⟨hbm, hbl⟩
  constructor <;> omega

/-- Subtractive alpha/beta form of the exact split product identity:
`(r - B*m) * (s - B*l) + 1 = B^2*l*m`. -/
theorem powerTwoSplitSubtractive_alpha_beta_mul {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    alpha * beta + 1 = B * B * (l * m) := by
  have hBpos : 0 < B := by omega
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  rcases powerTwoSplitSubtractive_to_additive (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) (alpha := alpha) (beta := beta)
    hBge hrpos hspos hlpos hmpos hD hA halpha hbeta with
    ⟨halpha_add, hbeta_add⟩
  exact powerTwoSplitAdditive_alpha_beta_mul hBpos hApos hD hA halpha_add
    hbeta_add

/-- In every positive subtractive split, the common divisor of `alpha` and
`beta` is coprime to the row-one quotient factor `l * m`. -/
theorem powerTwoSplitSubtractive_gcd_alpha_beta_coprime_l_mul_m
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    (Nat.gcd alpha beta).Coprime (l * m) := by
  have hab : alpha * beta + 1 = B * B * (l * m) :=
    powerTwoSplitSubtractive_alpha_beta_mul hBge hrpos hspos hlpos hmpos hD
      hA halpha hbeta
  exact
    gcd_alpha_beta_coprime_l_mul_m_of_product_identity
      (K := B * B) (l := l) (m := m) (alpha := alpha) (beta := beta)
      (c := Nat.gcd alpha beta) rfl hab

/-- Additive half-row identity used by the row-two-to-gcd reduction:
`2M = 2 alpha beta + B(alpha*l + beta*m)`, where
`M = B * (A / 2) - 1`. -/
theorem powerTwoSplitHalfRow_alpha_beta_identity {A B r s l m alpha beta : ℕ}
    (hA2 : 2 ∣ A)
    (hBpos : 0 < B)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : r = B * m + alpha)
    (hbeta : s = B * l + beta) :
    2 * (B * (A / 2) - 1) =
      2 * (alpha * beta) + B * (alpha * l + beta * m) := by
  have hApos : 0 < A := by
    rw [← hA, halpha, hbeta]
    positivity
  have hAeq : A = 2 * (A / 2) := (Nat.mul_div_cancel' hA2).symm
  have hMpos : 0 < B * (A / 2) := by
    have hAhalf_pos : 0 < A / 2 := by omega
    exact Nat.mul_pos hBpos hAhalf_pos
  have hprod := powerTwoSplitAdditive_alpha_beta_mul hBpos hApos hD hA
    halpha hbeta
  have hA' := hA
  rw [halpha, hbeta] at hA'
  rw [hAeq] at hA'
  have hA_mul :
      B * ((B * m + alpha) * l + (B * l + beta) * m) =
        B * (2 * (A / 2)) := by
    rw [hA']
  ring_nf at hA_mul hprod
  have hsum :
      B * (A / 2) * 2 =
        (2 * (alpha * beta) + B * (alpha * l + beta * m)) + 2 := by
    ring_nf
    nlinarith
  omega

/-- Subtractive version of `powerTwoSplitHalfRow_alpha_beta_identity`. -/
theorem powerTwoSplitSubtractive_half_row_alpha_beta_identity
    {A B r s l m alpha beta : ℕ}
    (hA2 : 2 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    2 * (B * (A / 2) - 1) =
      2 * (alpha * beta) + B * (alpha * l + beta * m) := by
  have hBpos : 0 < B := by omega
  rcases powerTwoSplitSubtractive_to_additive (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) (alpha := alpha) (beta := beta)
    hBge hrpos hspos hlpos hmpos hD hA halpha hbeta with
    ⟨halpha_add, hbeta_add⟩
  exact powerTwoSplitHalfRow_alpha_beta_identity hA2 hBpos hlpos hmpos hD hA
    halpha_add hbeta_add

/-- Additive row-two alpha identity. This is the exact arithmetic behind the
congruence `B(A - 2r*l) ≡ -2s*alpha (mod M)`. -/
theorem powerTwoSplitRowTwo_alpha_identity {A B r s l m alpha : ℕ}
    (hA2 : 2 ∣ A)
    (hBpos : 0 < B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : r = B * m + alpha) :
    B * (s * m - r * l) + 2 * s * alpha =
      2 * (B * (A / 2) - 1) := by
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have hAeq : A = 2 * (A / 2) := (Nat.mul_div_cancel' hA2).symm
  have hDadd : r * s + 1 = B * A := by
    have hBApos : 0 < B * A := Nat.mul_pos hBpos hApos
    omega
  let delta := s * m - r * l
  have hdelta : delta + r * l = s * m := by
    dsimp [delta]
    exact Nat.sub_add_cancel (le_of_lt hgap)
  let M := B * (A / 2) - 1
  have hMpos0 : 0 < B * (A / 2) := by
    have hAhalf_pos : 0 < A / 2 := by omega
    exact Nat.mul_pos hBpos hAhalf_pos
  have hM : M + 1 = B * (A / 2) := by
    dsimp [M]
    omega
  change B * delta + 2 * s * alpha = 2 * M
  nlinarith

/-- Subtractive version of `powerTwoSplitRowTwo_alpha_identity`. -/
theorem powerTwoSplitSubtractive_row_two_alpha_identity
    {A B r s l m alpha : ℕ}
    (hA2 : 2 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m) :
    B * (s * m - r * l) + 2 * s * alpha =
      2 * (B * (A / 2) - 1) := by
  have hBpos : 0 < B := by omega
  rcases powerTwoSplitSubtractive_to_additive (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) (alpha := alpha) (beta := s - B * l)
    hBge hrpos hspos hlpos hmpos hD hA halpha rfl with
    ⟨halpha_add, _hbeta_add⟩
  exact powerTwoSplitRowTwo_alpha_identity hA2 hBpos hrpos hspos hlpos hmpos
    hgap hD hA halpha_add

/-- If `s ∣ 2*M + 1`, then `s` is coprime to `M`. This packages the
coprimality step used when `s` is a row-one split factor of `2M + 1`. -/
theorem coprime_of_dvd_two_mul_add_one {s M : ℕ}
    (hs : s ∣ 2 * M + 1) :
    s.Coprime M := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_one
  have hg_s : Nat.gcd s M ∣ s := Nat.gcd_dvd_left s M
  have hg_M : Nat.gcd s M ∣ M := Nat.gcd_dvd_right s M
  have hg_twoM : Nat.gcd s M ∣ 2 * M := dvd_mul_of_dvd_right hg_M 2
  have hg_twoM1 : Nat.gcd s M ∣ 2 * M + 1 := Nat.dvd_trans hg_s hs
  have hone : Nat.gcd s M ∣ (2 * M + 1) - 2 * M :=
    Nat.dvd_sub hg_twoM1 hg_twoM
  simpa using hone

/-- In the split setting, the right split factor `s` divides `2M + 1`, where
`M = B * (A / 2) - 1`. -/
theorem powerTwoSplit_s_dvd_two_half_row_add_one {A B r s : ℕ}
    (hA2 : 2 ∣ A)
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1) :
    s ∣ 2 * (B * (A / 2) - 1) + 1 := by
  have hAeq : A = 2 * (A / 2) := (Nat.mul_div_cancel' hA2).symm
  have hAhalf_pos : 0 < A / 2 := by omega
  have hMpos : 0 < B * (A / 2) := Nat.mul_pos hBpos hAhalf_pos
  have hBAeq : B * A = 2 * (B * (A / 2)) := by
    calc
      B * A = B * (2 * (A / 2)) :=
        congrArg (fun x : ℕ => B * x) hAeq
      _ = 2 * (B * (A / 2)) := by ring
  have hM_eq : 2 * (B * (A / 2) - 1) + 1 = B * A - 1 := by
    rw [hBAeq]
    omega
  rw [hM_eq, ← hD]
  exact Nat.dvd_mul_left s r

/-- The split factor `s` is coprime to the half-row divisor
`B * (A / 2) - 1`. -/
theorem powerTwoSplit_s_coprime_half_row {A B r s : ℕ}
    (hA2 : 2 ∣ A)
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1) :
    s.Coprime (B * (A / 2) - 1) :=
  coprime_of_dvd_two_mul_add_one
    (powerTwoSplit_s_dvd_two_half_row_add_one hA2 hBpos hApos hD)

/-- General cancellation lemma for the row-two congruence. If
`B*delta + 2*s*alpha = 2*M`, `B` is invertible modulo `M`, and `2*s` is
invertible modulo `M`, then divisibility by `delta` is equivalent to
divisibility by `alpha` after multiplying by the same `l*m` factor. -/
theorem rowTwoDeltaDvd_iff_alphaDvd_of_identity
    {M B s l m delta alpha : ℕ}
    (hidentity : B * delta + 2 * s * alpha = 2 * M)
    (hcopB : M.Coprime B)
    (hcop2s : M.Coprime (2 * s)) :
    M ∣ (l * m) * delta ↔ M ∣ (l * m) * alpha := by
  constructor
  · intro hrow
    have hBdiv0 : M ∣ B * ((l * m) * delta) :=
      dvd_mul_of_dvd_right hrow B
    have hBdiv : M ∣ (l * m) * (B * delta) := by
      convert hBdiv0 using 1
      ring
    have hsum : M ∣ (l * m) * (B * delta + 2 * s * alpha) := by
      rw [hidentity]
      refine dvd_mul_of_dvd_right ?_ (l * m)
      exact Nat.dvd_mul_left M 2
    have hsum' :
        M ∣ (l * m) * (B * delta) + (l * m) * (2 * s * alpha) := by
      convert hsum using 1
      ring
    have hterm : M ∣ (l * m) * (2 * s * alpha) :=
      (Nat.dvd_add_iff_right hBdiv).mpr hsum'
    have hterm' : M ∣ (2 * s) * ((l * m) * alpha) := by
      convert hterm using 1
      ring
    exact hcop2s.dvd_of_dvd_mul_left hterm'
  · intro halpha
    have h2sdiv0 : M ∣ (2 * s) * ((l * m) * alpha) :=
      dvd_mul_of_dvd_right halpha (2 * s)
    have h2sdiv : M ∣ (l * m) * (2 * s * alpha) := by
      convert h2sdiv0 using 1
      ring
    have hsum : M ∣ (l * m) * (B * delta + 2 * s * alpha) := by
      rw [hidentity]
      refine dvd_mul_of_dvd_right ?_ (l * m)
      exact Nat.dvd_mul_left M 2
    have hsum' :
        M ∣ (l * m) * (B * delta) + (l * m) * (2 * s * alpha) := by
      convert hsum using 1
      ring
    have hBdiv : M ∣ (l * m) * (B * delta) :=
      (Nat.dvd_add_iff_left h2sdiv).mpr hsum'
    have hBdiv' : M ∣ B * ((l * m) * delta) := by
      convert hBdiv using 1
      ring
    exact hcopB.dvd_of_dvd_mul_left hBdiv'

/-- The half-row divisor `B * (A / 2) - 1` is coprime to `B`. -/
theorem powerTwoSplit_half_row_coprime_B {A B : ℕ}
    (hBpos : 0 < B)
    (hAhalf_pos : 0 < A / 2) :
    (B * (A / 2) - 1).Coprime B := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd (B * (A / 2) - 1) B
  have hgM : g ∣ B * (A / 2) - 1 := Nat.gcd_dvd_left _ _
  have hgB : g ∣ B := Nat.gcd_dvd_right _ _
  have hgprod : g ∣ B * (A / 2) := dvd_mul_of_dvd_left hgB (A / 2)
  have hprod_pos : 0 < B * (A / 2) := Nat.mul_pos hBpos hAhalf_pos
  have hone : g ∣ B * (A / 2) - (B * (A / 2) - 1) :=
    Nat.dvd_sub hgprod hgM
  have hone' : g ∣ 1 := by
    convert hone using 1
    omega
  exact Nat.eq_one_of_dvd_one hone'

/-- If `4 ∣ A`, then `B * (A / 2) - 1` is odd, hence coprime to `2`. -/
theorem powerTwoSplit_half_row_coprime_two_of_four_dvd {A B : ℕ}
    (hA4 : 4 ∣ A)
    (hBpos : 0 < B)
    (hApos : 0 < A) :
    (B * (A / 2) - 1).Coprime 2 := by
  rw [Nat.coprime_two_right]
  rcases hA4 with ⟨q, hAeq4⟩
  have hqpos : 0 < q := by omega
  have hBqpos : 0 < B * q := Nat.mul_pos hBpos hqpos
  have hhalf : A / 2 = 2 * q := by
    rw [hAeq4]
    omega
  refine ⟨B * q - 1, ?_⟩
  rw [hhalf]
  ring_nf
  omega

/-- In a row-one split with `4 ∣ A`, the half-row divisor is coprime to
`2 * s`. -/
theorem powerTwoSplit_half_row_coprime_two_mul_s {A B r s : ℕ}
    (hA4 : 4 ∣ A)
    (hBpos : 0 < B)
    (hApos : 0 < A)
    (hD : r * s = B * A - 1) :
    (B * (A / 2) - 1).Coprime (2 * s) := by
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hcop2 : (B * (A / 2) - 1).Coprime 2 :=
    powerTwoSplit_half_row_coprime_two_of_four_dvd hA4 hBpos hApos
  have hcops : (B * (A / 2) - 1).Coprime s :=
    (powerTwoSplit_s_coprime_half_row hA2 hBpos hApos hD).symm
  exact hcop2.mul_right hcops

/-- Concrete row-two bridge from the split delta form to the alpha form:
under the power-of-two half-row hypotheses, divisibility by
`s*m - r*l` is equivalent to divisibility by `alpha`. -/
theorem powerTwoSplit_row_two_delta_dvd_iff_alpha_dvd
    {A B r s l m alpha : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : r = B * m + alpha) :
    B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) ↔
      B * (A / 2) - 1 ∣ (l * m) * alpha := by
  have hBpos : 0 < B := by omega
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hAhalf_pos : 0 < A / 2 := by omega
  have hcopB : (B * (A / 2) - 1).Coprime B :=
    powerTwoSplit_half_row_coprime_B hBpos hAhalf_pos
  have hcop2s : (B * (A / 2) - 1).Coprime (2 * s) :=
    powerTwoSplit_half_row_coprime_two_mul_s hA4 hBpos hApos hD
  have hidentity := powerTwoSplitRowTwo_alpha_identity hA2 hBpos hrpos hspos
    hlpos hmpos hgap hD hA halpha
  exact rowTwoDeltaDvd_iff_alphaDvd_of_identity hidentity hcopB hcop2s

/-- Subtractive version of `powerTwoSplit_row_two_delta_dvd_iff_alpha_dvd`,
matching the split/gcd obstruction's natural-subtraction definition of
`alpha`. -/
theorem powerTwoSplitSubtractive_row_two_delta_dvd_iff_alpha_dvd
    {A B r s l m alpha : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m) :
    B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) ↔
      B * (A / 2) - 1 ∣ (l * m) * alpha := by
  rcases powerTwoSplitSubtractive_to_additive (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) (alpha := alpha) (beta := s - B * l)
    hBge hrpos hspos hlpos hmpos hD hA halpha rfl with
    ⟨halpha_add, _hbeta_add⟩
  exact powerTwoSplit_row_two_delta_dvd_iff_alpha_dvd hA4 hBge hrpos hspos
    hlpos hmpos hgap hD hA halpha_add

/-- Exact counterexample to the proposed auxiliary bound
`gcd (gcd alpha beta) M ≤ B^2` under the power-of-two split hypotheses. It
does not satisfy row-two survival: the same certificate proves
`M ∤ c * (l * m)` and `l * m < M / d`. -/
theorem powerTwoSplit_gcd_bound_counterexample_not_row_two_survival :
    ∃ A B r s l m : ℕ,
      A = 2 ^ 52 ∧
      4 ∣ A ∧
      Odd B ∧
      3 ≤ B ∧
      0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
      r * s = B * A - 1 ∧
      r * l + s * m = A ∧
      r * l < s * m ∧
      let alpha := r - B * m
      let beta := s - B * l
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      let d := Nat.gcd c M
      B * B < d ∧ ¬ M ∣ c * (l * m) ∧ l * m < M / d := by
  refine ⟨4503599627370496, 5, 32587551572869, 691, 29, 5149870668245, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · exact ⟨2, by norm_num⟩
  norm_num [Nat.gcd]

/-- If `D` divides a product, the cofactor of the part of `D` already present
in the left factor divides the right factor. This is the arithmetic split
lemma used to move from a row-one product divisibility to the canonical
divisor split. -/
theorem dvd_div_gcd_of_dvd_mul {D x y : ℕ} (hDpos : 0 < D)
    (hdvd : D ∣ x * y) :
    D / Nat.gcd D x ∣ y := by
  let g := Nat.gcd D x
  have hgD : g ∣ D := Nat.gcd_dvd_left D x
  have hgx : g ∣ x := Nat.gcd_dvd_right D x
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left x hDpos
  have hD_eq : D = g * (D / g) := (Nat.mul_div_cancel' hgD).symm
  have hx_eq : x = g * (x / g) := (Nat.mul_div_cancel' hgx).symm
  have hcop : (D / g).Coprime (x / g) :=
    Nat.coprime_div_gcd_div_gcd (m := D) (n := x) hgpos
  have hdiv0 : g * (D / g) ∣ (g * (x / g)) * y := by
    rw [← hD_eq, ← hx_eq]
    exact hdvd
  have hdiv : g * (D / g) ∣ g * ((x / g) * y) := by
    rw [← mul_assoc]
    exact hdiv0
  have hdiv' : D / g ∣ (x / g) * y :=
    (Nat.mul_dvd_mul_iff_left hgpos).mp hdiv
  exact hcop.dvd_of_dvd_mul_left hdiv'

/-- Exact cancellation of the gcd part of a divisor against the left factor:
for `0 < M`, `M ∣ c * L` iff the reduced divisor
`M / gcd c M` divides `L`. -/
theorem dvd_mul_iff_div_gcd_dvd {M c L : ℕ} (hMpos : 0 < M) :
    M ∣ c * L ↔ M / Nat.gcd c M ∣ L := by
  constructor
  · intro h
    have h' : M / Nat.gcd M c ∣ L := dvd_div_gcd_of_dvd_mul hMpos h
    simpa [Nat.gcd_comm] using h'
  · intro h
    let g := Nat.gcd c M
    have hgM : g ∣ M := Nat.gcd_dvd_right c M
    have hgc : g ∣ c := Nat.gcd_dvd_left c M
    rcases h with ⟨t, ht⟩
    change L = M / g * t at ht
    refine ⟨(c / g) * t, ?_⟩
    have hM_eq : M = g * (M / g) := (Nat.mul_div_cancel' hgM).symm
    have hc_eq : c = g * (c / g) := (Nat.mul_div_cancel' hgc).symm
    calc
      c * L = c * ((M / g) * t) := by rw [ht]
      _ = (g * (c / g)) * ((M / g) * t) := by
        conv_lhs => rw [hc_eq]
      _ = (g * (M / g)) * ((c / g) * t) := by ring
      _ = M * ((c / g) * t) := by rw [← hM_eq]

/-- The half-row divisor is positive under the split-level hypotheses
`4 ∣ A`, `B ≥ 3`, and `0 < A`. -/
theorem powerTwoSplit_half_row_pos {A B : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hApos : 0 < A) :
    0 < B * (A / 2) - 1 := by
  rcases hA4 with ⟨q, hAeq⟩
  have hqpos : 0 < q := by omega
  have hhalf : A / 2 = 2 * q := by
    rw [hAeq]
    omega
  have htwoq_ge : 2 ≤ 2 * q := by omega
  have hprod_ge : 6 ≤ B * (2 * q) := by
    have hmul := Nat.mul_le_mul hBge htwoq_ge
    simpa using hmul
  rw [hhalf]
  omega

/-- Reduced-divisor form of the split/gcd row-two obstruction. This replaces
the false auxiliary bound `gcd (gcd alpha beta) M ≤ B^2`: the exact condition
is divisibility by `M / gcd (gcd alpha beta) M`. -/
theorem powerTwoSplit_gcd_dvd_iff_reduced_divisor
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hApos : 0 < A) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    M ∣ c * (l * m) ↔ M / Nat.gcd c M ∣ l * m := by
  dsimp
  exact dvd_mul_iff_div_gcd_dvd (powerTwoSplit_half_row_pos hA4 hBge hApos)

/-- Explicit row-two-survival form of
`powerTwoSplit_gcd_dvd_iff_reduced_divisor`, naming the reduced divisor
`d = gcd c M`. -/
theorem powerTwoSplit_row_two_survival_iff_reduced_divisor
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hApos : 0 < A) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    M ∣ c * (l * m) ↔ M / d ∣ l * m := by
  dsimp
  exact dvd_mul_iff_div_gcd_dvd (powerTwoSplit_half_row_pos hA4 hBge hApos)

/-- Negated form of `dvd_mul_iff_div_gcd_dvd`: failure of divisibility by
`M` after multiplying by `c` is exactly failure of divisibility by the reduced
divisor `M / gcd c M`. -/
theorem not_dvd_mul_iff_not_div_gcd_dvd {M c L : ℕ} (hMpos : 0 < M) :
    (¬ M ∣ c * L) ↔ ¬ M / Nat.gcd c M ∣ L := by
  constructor
  · intro h hdvd
    exact h ((dvd_mul_iff_div_gcd_dvd hMpos).mpr hdvd)
  · intro h hdvd
    exact h ((dvd_mul_iff_div_gcd_dvd hMpos).mp hdvd)

/-- Explicit obstruction form of the row-two reduced-divisor equivalence:
the surviving target is `M / d ∤ l*m`, not an upper bound on `d`. -/
theorem powerTwoSplit_row_two_obstruction_iff_reduced_divisor
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hApos : 0 < A) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    (¬ M ∣ c * (l * m)) ↔ ¬ M / d ∣ l * m := by
  dsimp
  exact not_dvd_mul_iff_not_div_gcd_dvd
    (powerTwoSplit_half_row_pos hA4 hBge hApos)

/-- Any gcd taken from the left side of a coprime pair remains coprime to the
right side. -/
theorem coprime_gcd_right_of_coprime_left {a b L : ℕ}
    (hcop : a.Coprime L) :
    (Nat.gcd a b).Coprime L :=
  Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a b) hcop

/-- If `c` is coprime to `L` and the reduced divisor `M / gcd c M` survives
by dividing `L`, then the captured gcd part is coprime to the remaining
cofactor of `M`. In other words, survival forces `gcd c M` to be a unitary
part of `M`. -/
theorem reduced_divisor_survival_coprime_forces_unitary_gcd {M c L : ℕ}
    (hcop : c.Coprime L)
    (hred : M / Nat.gcd c M ∣ L) :
    (Nat.gcd c M).Coprime (M / Nat.gcd c M) := by
  have hgcd_cop_L : (Nat.gcd c M).Coprime L :=
    coprime_gcd_right_of_coprime_left hcop
  exact Nat.Coprime.coprime_dvd_right hred hgcd_cop_L

/-- Split-level unitary consequence of reduced-divisor survival. In every
positive subtractive split, row-two survival can only happen when the captured
gcd part of the half-row modulus is coprime to the remaining reduced divisor. -/
theorem powerTwoSplitSubtractive_reduced_divisor_survival_forces_unitary_gcd
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hred :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      let d := Nat.gcd c M
      M / d ∣ l * m) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    d.Coprime (M / d) := by
  dsimp at hred ⊢
  have hcop : (Nat.gcd alpha beta).Coprime (l * m) :=
    powerTwoSplitSubtractive_gcd_alpha_beta_coprime_l_mul_m hBge hrpos
      hspos hlpos hmpos hD hA halpha hbeta
  exact reduced_divisor_survival_coprime_forces_unitary_gcd hcop hred

/-- Contrapositive of `reduced_divisor_survival_coprime_forces_unitary_gcd`:
if the captured gcd part is not unitary, the reduced divisor cannot survive
against a coprime right factor. -/
theorem not_reduced_divisor_survival_of_not_unitary_gcd {M c L : ℕ}
    (hcop : c.Coprime L)
    (hnunit : ¬ (Nat.gcd c M).Coprime (M / Nat.gcd c M)) :
    ¬ M / Nat.gcd c M ∣ L := by
  intro hred
  exact hnunit (reduced_divisor_survival_coprime_forces_unitary_gcd hcop hred)

/-- Split-level nonunitary obstruction: if the gcd part captured from the
half-row modulus is not coprime to the remaining reduced divisor, then the
row-two reduced-divisor survival condition is impossible. -/
theorem powerTwoSplitSubtractive_not_reduced_divisor_survival_of_not_unitary_gcd
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hnunit :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      let d := Nat.gcd c M
      ¬ d.Coprime (M / d)) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    ¬ M / d ∣ l * m := by
  dsimp at hnunit ⊢
  have hcop : (Nat.gcd alpha beta).Coprime (l * m) :=
    powerTwoSplitSubtractive_gcd_alpha_beta_coprime_l_mul_m hBge hrpos
      hspos hlpos hmpos hD hA halpha hbeta
  exact not_reduced_divisor_survival_of_not_unitary_gcd hcop hnunit

/-- A size certificate for failure of row-two divisibility after reducing by
the gcd part of the modulus. If the reduced divisor is strictly larger than
the positive right factor, then `M` cannot divide `c * L`. -/
theorem not_dvd_mul_of_reduced_divisor_gt {M c L : ℕ}
    (hMpos : 0 < M)
    (hLpos : 0 < L)
    (hlt : L < M / Nat.gcd c M) :
    ¬ M ∣ c * L := by
  intro hdvd
  have hred : M / Nat.gcd c M ∣ L :=
    (dvd_mul_iff_div_gcd_dvd hMpos).mp hdvd
  have hle : M / Nat.gcd c M ≤ L := Nat.le_of_dvd hLpos hred
  exact (not_le_of_gt hlt) hle

/-- If the right modulus is odd, the gcd of an even left factor with it is at
most half of the left factor. This is the parity refinement behind the
current reduced-divisor C2 target. -/
theorem gcd_le_half_of_even_left_odd_right {c M : ℕ}
    (hcpos : 0 < c)
    (hceven : Even c)
    (hModd : Odd M) :
    Nat.gcd c M ≤ c / 2 := by
  rcases hceven with ⟨k, hk⟩
  have hkpos : 0 < k := by omega
  have hgcd_dvd_c : Nat.gcd c M ∣ c := Nat.gcd_dvd_left c M
  have hgcd_dvd_M : Nat.gcd c M ∣ M := Nat.gcd_dvd_right c M
  have hgcd_odd : Odd (Nat.gcd c M) := hModd.of_dvd_nat hgcd_dvd_M
  have hcop_two : (Nat.gcd c M).Coprime 2 :=
    Nat.coprime_two_right.mpr hgcd_odd
  have htwo : c = 2 * k := by omega
  have hdvd_two_k : Nat.gcd c M ∣ 2 * k := by
    simpa [htwo] using hgcd_dvd_c
  have hdvd_k : Nat.gcd c M ∣ k := by
    exact hcop_two.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdvd_two_k)
  have hle : Nat.gcd c M ≤ k := Nat.le_of_dvd hkpos hdvd_k
  have hcdiv : c / 2 = k := by omega
  simpa [hcdiv] using hle

/-- Parity-branch sufficient gap certificate. For odd `c`, it is enough to
show `L < M / c`; for even `c`, because the odd modulus can only share at most
half of `c`, it is enough to show `L < M / (c / 2)`. -/
theorem not_dvd_mul_of_parity_reduced_divisor_gt {M c L : ℕ}
    (hMpos : 0 < M)
    (hModd : Odd M)
    (hcpos : 0 < c)
    (hLpos : 0 < L)
    (hgap : (Odd c ∧ L < M / c) ∨ (Even c ∧ L < M / (c / 2))) :
    ¬ M ∣ c * L := by
  refine not_dvd_mul_of_reduced_divisor_gt hMpos hLpos ?_
  have hgcdpos : 0 < Nat.gcd c M := Nat.gcd_pos_of_pos_left M hcpos
  rcases hgap with ⟨_hcodd, hgapc⟩ | ⟨hceven, hgapc⟩
  · have hgcd_le_c : Nat.gcd c M ≤ c := Nat.gcd_le_left M hcpos
    have hdiv_le : M / c ≤ M / Nat.gcd c M :=
      Nat.div_le_div_left hgcd_le_c hgcdpos
    exact lt_of_lt_of_le hgapc hdiv_le
  · have hgcd_le_half : Nat.gcd c M ≤ c / 2 :=
      gcd_le_half_of_even_left_odd_right hcpos hceven hModd
    have hdiv_le : M / (c / 2) ≤ M / Nat.gcd c M :=
      Nat.div_le_div_left hgcd_le_half hgcdpos
    exact lt_of_lt_of_le hgapc hdiv_le

/-- Floor-free way to prove `L < M / b`: it suffices to show
`b * (L + 1) ≤ M`. -/
theorem lt_div_of_mul_succ_le {M b L : ℕ}
    (hbpos : 0 < b)
    (hbound : b * (L + 1) ≤ M) :
    L < M / b := by
  have hsucc_le : L + 1 ≤ M / b := by
    exact (Nat.le_div_iff_mul_le hbpos).mpr (by simpa [mul_comm] using hbound)
  omega

/-- Floor-free product form is equivalent to `L < M / b`. -/
theorem lt_div_iff_mul_succ_le {M b L : ℕ}
    (hbpos : 0 < b) :
    L < M / b ↔ b * (L + 1) ≤ M := by
  constructor
  · intro hlt
    have hsucc_le : L + 1 ≤ M / b := by omega
    have hmul : (L + 1) * b ≤ M :=
      (Nat.le_div_iff_mul_le hbpos).mp hsucc_le
    simpa [mul_comm] using hmul
  · exact lt_div_of_mul_succ_le hbpos

/-- Product-form parity gap is exactly the same as the corresponding
division-form parity gap. -/
theorem parity_product_gap_iff_parity_reduced_divisor_gap {M c L : ℕ}
    (hcpos : 0 < c) :
    ((Odd c ∧ c * (L + 1) ≤ M) ∨
        (Even c ∧ (c / 2) * (L + 1) ≤ M)) ↔
      ((Odd c ∧ L < M / c) ∨
        (Even c ∧ L < M / (c / 2))) := by
  constructor
  · rintro (⟨hcodd, hbound⟩ | ⟨hceven, hbound⟩)
    · exact Or.inl ⟨hcodd, (lt_div_iff_mul_succ_le hcpos).mpr hbound⟩
    · have hc2pos : 0 < c / 2 := by
        rcases hceven with ⟨k, hk⟩
        have hkpos : 0 < k := by omega
        have hcdiv : c / 2 = k := by omega
        simpa [hcdiv] using hkpos
      exact Or.inr ⟨hceven, (lt_div_iff_mul_succ_le hc2pos).mpr hbound⟩
  · rintro (⟨hcodd, hgap⟩ | ⟨hceven, hgap⟩)
    · exact Or.inl ⟨hcodd, (lt_div_iff_mul_succ_le hcpos).mp hgap⟩
    · have hc2pos : 0 < c / 2 := by
        rcases hceven with ⟨k, hk⟩
        have hkpos : 0 < k := by omega
        have hcdiv : c / 2 = k := by omega
        simpa [hcdiv] using hkpos
      exact Or.inr ⟨hceven, (lt_div_iff_mul_succ_le hc2pos).mp hgap⟩

/-- If a factor `b` of the split gcd is at most `B^2`, then the floor-free
product gap follows from the product and half-row identities. This isolates
the remaining product-gap work to the exceptional large-denominator branch. -/
theorem product_gap_of_factor_bound_by_B_sq {M B l m alpha beta b : ℕ}
    (hBge : 3 ≤ B)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hbpos : 0 < b)
    (hb_le_B2 : b ≤ B * B)
    (hb_le_alpha : b ≤ alpha)
    (hb_le_beta : b ≤ beta)
    (hab : alpha * beta + 1 = B * B * (l * m))
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m)) :
    b * (l * m + 1) ≤ M := by
  have hlge : 1 ≤ l := Nat.succ_le_of_lt hlpos
  have hmge : 1 ≤ m := Nat.succ_le_of_lt hmpos
  have hb_alpha_l : b ≤ alpha * l := by
    have hmul : b * 1 ≤ alpha * l := Nat.mul_le_mul hb_le_alpha hlge
    simpa using hmul
  have hb_beta_m : b ≤ beta * m := by
    have hmul : b * 1 ≤ beta * m := Nat.mul_le_mul hb_le_beta hmge
    simpa using hmul
  have hbL_le_B2L : b * (l * m) ≤ (B * B) * (l * m) :=
    Nat.mul_le_mul_right (l * m) hb_le_B2
  have hsum_ge : 2 * b ≤ alpha * l + beta * m := by
    nlinarith
  have hBsum_ge : 6 * b ≤ B * (alpha * l + beta * m) := by
    have hmul : 3 * (2 * b) ≤ B * (alpha * l + beta * m) :=
      Nat.mul_le_mul hBge hsum_ge
    nlinarith
  have hBsum_ge_add : 2 * b + 2 ≤ B * (alpha * l + beta * m) := by
    nlinarith
  have hmain :
      2 * (b * (l * m + 1)) + 2 ≤
        2 * ((B * B) * (l * m)) + B * (alpha * l + beta * m) := by
    nlinarith
  have htwice : 2 * (b * (l * m + 1)) ≤ 2 * M := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)

/-- Quotient form of the parity product gap. If `alpha = c*x` and
`beta = c*y`, the half-row identity rewrites the target denominator as
`2*c*x*y + B*(x*l + y*m)`: the odd branch needs twice `L+1`, while the even
branch needs only `L+1`. -/
theorem parity_product_gap_of_gcd_quotient_ineq {M B l m c x y L : ℕ}
    (hhalf :
      2 * M =
        2 * ((c * x) * (c * y)) + B * ((c * x) * l + (c * y) * m))
    (hgap :
      (Odd c ∧ 2 * (L + 1) ≤ 2 * c * (x * y) + B * (x * l + y * m)) ∨
        (Even c ∧ L + 1 ≤ 2 * c * (x * y) + B * (x * l + y * m))) :
    (Odd c ∧ c * (L + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (L + 1) ≤ M) := by
  let T := 2 * c * (x * y) + B * (x * l + y * m)
  have hfactor : c * T = 2 * M := by
    calc
      c * T =
          2 * ((c * x) * (c * y)) + B * ((c * x) * l + (c * y) * m) := by
        dsimp [T]
        ring
      _ = 2 * M := hhalf.symm
  rcases hgap with ⟨hcodd, hineq⟩ | ⟨hceven, hineq⟩
  · have htwice : 2 * (c * (L + 1)) ≤ 2 * M := by
      calc
        2 * (c * (L + 1)) = c * (2 * (L + 1)) := by ring
        _ ≤ c * T := Nat.mul_le_mul_left c hineq
        _ = 2 * M := hfactor
    exact Or.inl ⟨hcodd,
      Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)⟩
  · rcases hceven with ⟨q, hcq⟩
    have hcdiv : c / 2 = q := by omega
    have htwice : 2 * ((c / 2) * (L + 1)) ≤ 2 * M := by
      calc
        2 * ((c / 2) * (L + 1)) = c * (L + 1) := by
          rw [hcdiv, hcq]
          ring
        _ ≤ c * T := Nat.mul_le_mul_left c hineq
        _ = 2 * M := hfactor
    exact Or.inr ⟨⟨q, hcq⟩,
      Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)⟩

/-- Exact quotient form of the reduced-divisor parity gap. Under the half-row
identity with `alpha = c*x` and `beta = c*y`, the scanner's quotient target is
not merely sufficient: it is equivalent to the reduced-divisor gap branch by
branch. -/
theorem parity_reduced_divisor_gap_iff_gcd_quotient_ineq
    {M B l m c x y L : ℕ}
    (hcpos : 0 < c)
    (hhalf :
      2 * M =
        2 * ((c * x) * (c * y)) + B * ((c * x) * l + (c * y) * m)) :
    let T := 2 * c * (x * y) + B * (x * l + y * m)
    (((Odd c ∧ L < M / c) ∨ (Even c ∧ L < M / (c / 2))) ↔
      ((Odd c ∧ 2 * (L + 1) ≤ T) ∨ (Even c ∧ L + 1 ≤ T))) := by
  dsimp
  let T := 2 * c * (x * y) + B * (x * l + y * m)
  have hfactor : c * T = 2 * M := by
    calc
      c * T =
          2 * ((c * x) * (c * y)) + B * ((c * x) * l + (c * y) * m) := by
        dsimp [T]
        ring
      _ = 2 * M := hhalf.symm
  constructor
  · rintro (⟨hcodd, hgap⟩ | ⟨hceven, hgap⟩)
    · have hprod : c * (L + 1) ≤ M :=
        (lt_div_iff_mul_succ_le hcpos).mp hgap
      have htwice : c * (2 * (L + 1)) ≤ c * T := by
        calc
          c * (2 * (L + 1)) = 2 * (c * (L + 1)) := by ring
          _ ≤ 2 * M := Nat.mul_le_mul_left 2 hprod
          _ = c * T := hfactor.symm
      exact Or.inl ⟨hcodd, Nat.le_of_mul_le_mul_left htwice hcpos⟩
    · rcases hceven with ⟨q, hcq⟩
      have hqpos : 0 < q := by omega
      have hcdiv : c / 2 = q := by omega
      have hgapq : L < M / q := by simpa [hcdiv] using hgap
      have hprod : q * (L + 1) ≤ M :=
        (lt_div_iff_mul_succ_le hqpos).mp hgapq
      have hqT : q * T = M := by
        have htwice : 2 * (q * T) = 2 * M := by
          rw [← hfactor, hcq]
          ring
        exact Nat.mul_left_cancel (by decide : 0 < 2) htwice
      have hle : q * (L + 1) ≤ q * T := by
        simpa [hqT] using hprod
      exact Or.inr ⟨⟨q, hcq⟩, Nat.le_of_mul_le_mul_left hle hqpos⟩
  · intro hquot
    have hprod : (Odd c ∧ c * (L + 1) ≤ M) ∨
        (Even c ∧ (c / 2) * (L + 1) ≤ M) := by
      exact parity_product_gap_of_gcd_quotient_ineq hhalf hquot
    exact (parity_product_gap_iff_parity_reduced_divisor_gap hcpos).mp hprod

/-- Linear form of the normalized gcd-quotient target. It is stronger than
`parity_product_gap_of_gcd_quotient_ineq`: the nonnegative term
`2*c*x*y` is discarded from the right-hand side. -/
theorem parity_product_gap_of_gcd_linear_ineq {M B l m c x y L : ℕ}
    (hhalf :
      2 * M =
        2 * ((c * x) * (c * y)) + B * ((c * x) * l + (c * y) * m))
    (hgap :
      (Odd c ∧ 2 * (L + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ L + 1 ≤ B * (x * l + y * m))) :
    (Odd c ∧ c * (L + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (L + 1) ≤ M) := by
  refine parity_product_gap_of_gcd_quotient_ineq hhalf ?_
  rcases hgap with ⟨hcodd, hineq⟩ | ⟨hceven, hineq⟩
  · exact Or.inl ⟨hcodd,
      hineq.trans (Nat.le_add_left (B * (x * l + y * m)) (2 * c * (x * y)))⟩
  · exact Or.inr ⟨hceven,
      hineq.trans (Nat.le_add_left (B * (x * l + y * m)) (2 * c * (x * y)))⟩

/-- Even-branch linear target as a deficit condition. The term
`m * (l - B*y)` is the amount left after the `B*y*m` part tries to cover
`l*m`; the `B*x*l` part must cover that deficit plus one. -/
theorem linear_even_iff_x_compensates_y_deficit {B x y l m : ℕ}
    (hpos : 1 ≤ B * x * l) :
    l * m + 1 ≤ B * (x * l + y * m) ↔
      m * (l - B * y) + 1 ≤ B * x * l := by
  constructor
  · intro hlin
    rcases le_or_gt l (B * y) with hle | hlt
    · have hsub : l - B * y = 0 := Nat.sub_eq_zero_of_le hle
      simpa [hsub] using hpos
    · have hleBy : B * y ≤ l := Nat.le_of_lt hlt
      have hdecomp : l * m = B * y * m + (l - B * y) * m := by
        nlinarith [Nat.sub_add_cancel hleBy]
      have hlin' :
          B * y * m + ((l - B * y) * m + 1) ≤
            B * y * m + B * x * l := by
        calc
          B * y * m + ((l - B * y) * m + 1) = l * m + 1 := by
            rw [hdecomp]
            ring
          _ ≤ B * (x * l + y * m) := hlin
          _ = B * y * m + B * x * l := by ring
      have hlin'' :
          B * y * m + (m * (l - B * y) + 1) ≤
            B * y * m + B * x * l := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlin'
      exact Nat.add_le_add_iff_left.mp hlin''
  · intro hdef
    rcases le_or_gt l (B * y) with hle | hlt
    · have hBym : l * m ≤ B * y * m := Nat.mul_le_mul_right m hle
      calc
        l * m + 1 ≤ B * y * m + B * x * l := Nat.add_le_add hBym hpos
        _ = B * (x * l + y * m) := by ring
    · have hleBy : B * y ≤ l := Nat.le_of_lt hlt
      have hdecomp : l * m = B * y * m + (l - B * y) * m := by
        nlinarith [Nat.sub_add_cancel hleBy]
      calc
        l * m + 1 = B * y * m + ((l - B * y) * m + 1) := by
          rw [hdecomp]
          ring
        _ = B * y * m + (m * (l - B * y) + 1) := by ring
        _ ≤ B * y * m + B * x * l := Nat.add_le_add_left hdef (B * y * m)
        _ = B * (x * l + y * m) := by ring

/-- Odd-branch linear target as a deficit condition. Compared with the even
branch, the `B*y*m` term tries to cover `2*l*m`, and the `B*x*l` term must
cover the remaining deficit plus two. -/
theorem linear_odd_iff_x_compensates_y_deficit {B x y l m : ℕ}
    (hpos : 2 ≤ B * x * l) :
    2 * (l * m + 1) ≤ B * (x * l + y * m) ↔
      m * (2 * l - B * y) + 2 ≤ B * x * l := by
  constructor
  · intro hlin
    rcases le_or_gt (2 * l) (B * y) with hle | hlt
    · have hsub : 2 * l - B * y = 0 := Nat.sub_eq_zero_of_le hle
      simpa [hsub] using hpos
    · have hleBy : B * y ≤ 2 * l := Nat.le_of_lt hlt
      have hdecomp :
          2 * (l * m) = B * y * m + (2 * l - B * y) * m := by
        nlinarith [Nat.sub_add_cancel hleBy]
      have heq_left :
          B * y * m + ((2 * l - B * y) * m + 2) =
            2 * (l * m + 1) := by
        calc
          B * y * m + ((2 * l - B * y) * m + 2) =
              2 * (l * m) + 2 := by
            rw [hdecomp]
            ring
          _ = 2 * (l * m + 1) := by ring
      have hlin' :
          B * y * m + ((2 * l - B * y) * m + 2) ≤
            B * y * m + B * x * l := by
        calc
          B * y * m + ((2 * l - B * y) * m + 2) =
              2 * (l * m + 1) := heq_left
          _ ≤ B * (x * l + y * m) := hlin
          _ = B * y * m + B * x * l := by ring
      have hlin'' :
          B * y * m + (m * (2 * l - B * y) + 2) ≤
            B * y * m + B * x * l := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlin'
      exact Nat.add_le_add_iff_left.mp hlin''
  · intro hdef
    rcases le_or_gt (2 * l) (B * y) with hle | hlt
    · have hBym : 2 * (l * m) ≤ B * y * m := by
        calc
          2 * (l * m) = (2 * l) * m := by ring
          _ ≤ (B * y) * m := Nat.mul_le_mul_right m hle
          _ = B * y * m := by ring
      calc
        2 * (l * m + 1) = 2 * (l * m) + 2 := by ring
        _ ≤ B * y * m + B * x * l := Nat.add_le_add hBym hpos
        _ = B * (x * l + y * m) := by ring
    · have hleBy : B * y ≤ 2 * l := Nat.le_of_lt hlt
      have hdecomp :
          2 * (l * m) = B * y * m + (2 * l - B * y) * m := by
        nlinarith [Nat.sub_add_cancel hleBy]
      calc
        2 * (l * m + 1) = 2 * (l * m) + 2 := by ring
        _ = B * y * m + ((2 * l - B * y) * m + 2) := by
          rw [hdecomp]
          ring
        _ = B * y * m + (m * (2 * l - B * y) + 2) := by ring
        _ ≤ B * y * m + B * x * l := Nat.add_le_add_left hdef (B * y * m)
        _ = B * (x * l + y * m) := by ring

/-- Parity-branch linear target rewritten as the exact deficit-compensation
condition for the `B*x*l` term. -/
theorem parity_linear_ineq_iff_deficit_ineq {B c x y l m : ℕ}
    (hpos : 2 ≤ B * x * l) :
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) ↔
      ((Odd c ∧ m * (2 * l - B * y) + 2 ≤ B * x * l) ∨
        (Even c ∧ m * (l - B * y) + 1 ≤ B * x * l)) := by
  constructor
  · rintro (⟨hcodd, hlin⟩ | ⟨hceven, hlin⟩)
    · exact Or.inl ⟨hcodd,
        (linear_odd_iff_x_compensates_y_deficit hpos).mp hlin⟩
    · have hpos1 : 1 ≤ B * x * l := by omega
      exact Or.inr ⟨hceven,
        (linear_even_iff_x_compensates_y_deficit hpos1).mp hlin⟩
  · rintro (⟨hcodd, hdef⟩ | ⟨hceven, hdef⟩)
    · exact Or.inl ⟨hcodd,
        (linear_odd_iff_x_compensates_y_deficit hpos).mpr hdef⟩
    · have hpos1 : 1 ≤ B * x * l := by omega
      exact Or.inr ⟨hceven,
        (linear_even_iff_x_compensates_y_deficit hpos1).mpr hdef⟩

/-- Even-branch automatic case: if `B*y` already covers `l`, then
`B*y*m` covers the `l*m` term and the positive `B*x*l` term supplies the
extra one. -/
theorem linear_even_of_y_covers_l {B x y l m : ℕ}
    (hpos : 1 ≤ B * x * l)
    (hcover : l ≤ B * y) :
    l * m + 1 ≤ B * (x * l + y * m) := by
  refine (linear_even_iff_x_compensates_y_deficit hpos).mpr ?_
  have hsub : l - B * y = 0 := Nat.sub_eq_zero_of_le hcover
  simpa [hsub] using hpos

/-- Odd-branch automatic case: if `B*y` already covers `2*l`, then
`B*y*m` covers the `2*l*m` term and the positive `B*x*l` term supplies the
extra two. -/
theorem linear_odd_of_y_covers_two_l {B x y l m : ℕ}
    (hpos : 2 ≤ B * x * l)
    (hcover : 2 * l ≤ B * y) :
    2 * (l * m + 1) ≤ B * (x * l + y * m) := by
  refine (linear_odd_iff_x_compensates_y_deficit hpos).mpr ?_
  have hsub : 2 * l - B * y = 0 := Nat.sub_eq_zero_of_le hcover
  simpa [hsub] using hpos

/-- Parity-branch automatic y-coverage case for the canonical linear target.
The odd branch needs `B*y` to cover `2*l`; the even branch needs it to cover
`l`. -/
theorem parity_linear_ineq_of_y_coverage {B c x y l m : ℕ}
    (hpos : 2 ≤ B * x * l)
    (hcover : (Odd c ∧ 2 * l ≤ B * y) ∨ (Even c ∧ l ≤ B * y)) :
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) := by
  rcases hcover with ⟨hcodd, hcover⟩ | ⟨hceven, hcover⟩
  · exact Or.inl ⟨hcodd, linear_odd_of_y_covers_two_l hpos hcover⟩
  · have hpos1 : 1 ≤ B * x * l := by omega
    exact Or.inr ⟨hceven, linear_even_of_y_covers_l hpos1 hcover⟩

/-- Even-branch x-compensation case: if `m ≤ B*x`, then the `B*x*l`
term covers `l*m`; the positive `B*y*m` term supplies the extra one. -/
theorem linear_even_of_m_le_B_mul_x {B x y l m : ℕ}
    (hbonus : 1 ≤ B * y * m)
    (hm : m ≤ B * x) :
    l * m + 1 ≤ B * (x * l + y * m) := by
  have hleft : l * m ≤ B * x * l := by
    have h := Nat.mul_le_mul_left l hm
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    l * m + 1 ≤ B * x * l + B * y * m := Nat.add_le_add hleft hbonus
    _ = B * (x * l + y * m) := by ring

/-- Odd-branch middle-coverage case: if `B*y` does not cover `2*l` but does
exceed `l`, then `m ≤ B*x` gives enough slack in `B*x*l` to cover the
remaining deficit. -/
theorem linear_odd_of_middle_y_and_m_le_B_mul_x {B x y l m : ℕ}
    (hlpos : 0 < l)
    (hBx : 2 ≤ B * x)
    (hm : m ≤ B * x)
    (hmiddle : l < B * y) :
    2 * (l * m + 1) ≤ B * (x * l + y * m) := by
  have hpos : 2 ≤ B * x * l := by nlinarith
  refine (linear_odd_iff_x_compensates_y_deficit hpos).mpr ?_
  let d := 2 * l - B * y
  have hdlt : d < l := by
    dsimp [d]
    omega
  have hdle : d ≤ l := Nat.le_of_lt hdlt
  have hmul : m * d ≤ B * x * d := by
    have h := Nat.mul_le_mul_right d hm
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hldiff : 0 < l - d := Nat.sub_pos_of_lt hdlt
  have hslack : 2 ≤ B * x * (l - d) := by nlinarith
  have hsum : m * d + 2 ≤ B * x * d + B * x * (l - d) :=
    Nat.add_le_add hmul hslack
  have hright : B * x * d + B * x * (l - d) = B * x * l := by
    have hcancel : d + (l - d) = l := Nat.add_sub_of_le hdle
    nlinarith
  calc
    m * d + 2 ≤ B * x * d + B * x * (l - d) := hsum
    _ = B * x * l := hright

/-- Parity-branch automatic target after allowing the first x-compensation
case. Odd `c` closes either from full y-coverage `2*l ≤ B*y` or from the
middle band `l < B*y` plus `m ≤ B*x`; even `c` closes either from
`l ≤ B*y` or from `m ≤ B*x`. -/
theorem parity_linear_ineq_of_y_or_x_coverage {B c x y l m : ℕ}
    (hlpos : 0 < l)
    (hBx : 2 ≤ B * x)
    (hbonus : 1 ≤ B * y * m)
    (hcover :
      (Odd c ∧ (2 * l ≤ B * y ∨ (l < B * y ∧ m ≤ B * x))) ∨
        (Even c ∧ (l ≤ B * y ∨ m ≤ B * x))) :
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) := by
  have hpos : 2 ≤ B * x * l := by nlinarith
  rcases hcover with ⟨hcodd, hbranch⟩ | ⟨hceven, hbranch⟩
  · rcases hbranch with hycover | ⟨hmiddle, hm⟩
    · exact Or.inl ⟨hcodd, linear_odd_of_y_covers_two_l hpos hycover⟩
    · exact Or.inl ⟨hcodd,
        linear_odd_of_middle_y_and_m_le_B_mul_x hlpos hBx hm hmiddle⟩
  · rcases hbranch with hycover | hm
    · have hpos1 : 1 ≤ B * x * l := by omega
      exact Or.inr ⟨hceven, linear_even_of_y_covers_l hpos1 hycover⟩
    · exact Or.inr ⟨hceven, linear_even_of_m_le_B_mul_x hbonus hm⟩

/-- Even-branch scaled-deficit case. If `m` is at most `q` copies of `B*x`
and the same scale still leaves the y-deficit below `l`, then the slack in
`B*x*l` supplies the missing `+1`. -/
theorem linear_even_of_scaled_deficit {B x y l m q : ℕ}
    (hBxpos : 0 < B * x)
    (hm : m ≤ q * (B * x))
    (hdef : q * (l - B * y) < l) :
    l * m + 1 ≤ B * (x * l + y * m) := by
  have hlpos : 0 < l := by omega
  have hpos : 1 ≤ B * x * l := Nat.mul_pos hBxpos hlpos
  refine (linear_even_iff_x_compensates_y_deficit hpos).mpr ?_
  let d := l - B * y
  have hqdlt : q * d < l := by simpa [d] using hdef
  have hqdle : q * d ≤ l := Nat.le_of_lt hqdlt
  have hmul : m * d ≤ B * x * (q * d) := by
    have h := Nat.mul_le_mul_right d hm
    calc
      m * d ≤ q * (B * x) * d := h
      _ = B * x * (q * d) := by ring
  have hldiff : 0 < l - q * d := Nat.sub_pos_of_lt hqdlt
  have hslack : 1 ≤ B * x * (l - q * d) := Nat.mul_pos hBxpos hldiff
  have hsum : m * d + 1 ≤ B * x * (q * d) + B * x * (l - q * d) :=
    Nat.add_le_add hmul hslack
  have hright : B * x * (q * d) + B * x * (l - q * d) = B * x * l := by
    have hcancel : q * d + (l - q * d) = l := Nat.add_sub_of_le hqdle
    nlinarith
  calc
    m * d + 1 ≤ B * x * (q * d) + B * x * (l - q * d) := hsum
    _ = B * x * l := hright

/-- Odd-branch scaled-deficit case. This is the same scaled slack mechanism
as `linear_even_of_scaled_deficit`, with the odd branch's `2*l - B*y`
deficit and the extra `+2`. -/
theorem linear_odd_of_scaled_deficit {B x y l m q : ℕ}
    (hBx : 2 ≤ B * x)
    (hm : m ≤ q * (B * x))
    (hdef : q * (2 * l - B * y) < l) :
    2 * (l * m + 1) ≤ B * (x * l + y * m) := by
  have hlpos : 0 < l := by omega
  have hpos : 2 ≤ B * x * l := by nlinarith
  refine (linear_odd_iff_x_compensates_y_deficit hpos).mpr ?_
  let d := 2 * l - B * y
  have hqdlt : q * d < l := by simpa [d] using hdef
  have hqdle : q * d ≤ l := Nat.le_of_lt hqdlt
  have hmul : m * d ≤ B * x * (q * d) := by
    have h := Nat.mul_le_mul_right d hm
    calc
      m * d ≤ q * (B * x) * d := h
      _ = B * x * (q * d) := by ring
  have hldiff : 0 < l - q * d := Nat.sub_pos_of_lt hqdlt
  have hslack : 2 ≤ B * x * (l - q * d) := by nlinarith
  have hsum : m * d + 2 ≤ B * x * (q * d) + B * x * (l - q * d) :=
    Nat.add_le_add hmul hslack
  have hright : B * x * (q * d) + B * x * (l - q * d) = B * x * l := by
    have hcancel : q * d + (l - q * d) = l := Nat.add_sub_of_le hqdle
    nlinarith
  calc
    m * d + 2 ≤ B * x * (q * d) + B * x * (l - q * d) := hsum
    _ = B * x * l := hright

/-- Parity-branch target after allowing a scaled x-compensation witness for
the y-deficit. The witness `q` bounds `m` by `q*(B*x)` while keeping the
scaled branch deficit below `l`. -/
theorem parity_linear_ineq_of_scaled_deficit_coverage {B c x y l m : ℕ}
    (hlpos : 0 < l)
    (hBx : 2 ≤ B * x)
    (hcover :
      (Odd c ∧
          (2 * l ≤ B * y ∨
            ∃ q : ℕ, m ≤ q * (B * x) ∧ q * (2 * l - B * y) < l)) ∨
        (Even c ∧
          (l ≤ B * y ∨
            ∃ q : ℕ, m ≤ q * (B * x) ∧ q * (l - B * y) < l))) :
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) := by
  have hpos : 2 ≤ B * x * l := by nlinarith
  have hBxpos : 0 < B * x := by omega
  rcases hcover with ⟨hcodd, hbranch⟩ | ⟨hceven, hbranch⟩
  · rcases hbranch with hycover | ⟨q, hm, hdef⟩
    · exact Or.inl ⟨hcodd, linear_odd_of_y_covers_two_l hpos hycover⟩
    · exact Or.inl ⟨hcodd, linear_odd_of_scaled_deficit hBx hm hdef⟩
  · rcases hbranch with hycover | ⟨q, hm, hdef⟩
    · have hpos1 : 1 ≤ B * x * l := by omega
      exact Or.inr ⟨hceven, linear_even_of_y_covers_l hpos1 hycover⟩
    · exact Or.inr ⟨hceven, linear_even_of_scaled_deficit hBxpos hm hdef⟩

/-- Canonical ceiling-scale bound used by the quotient diagnostics. For
positive `d`, the fixed witness `((m - 1) / d) + 1` supplies enough copies of
`d` to cover `m`. -/
theorem le_ceilSubOneDiv_succ_mul {d m : ℕ} (hd : 0 < d) :
    m ≤ ((m - 1) / d + 1) * d := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hlt : m - 1 < d * ((m - 1) / d + 1) :=
      Nat.lt_mul_div_succ (m - 1) hd
    have hsucc : (m - 1).succ ≤ d * ((m - 1) / d + 1) :=
      Nat.succ_le_iff.mpr hlt
    have hm_succ : (m - 1).succ = m := Nat.succ_pred_eq_of_pos hmpos
    rw [hm_succ] at hsucc
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsucc

/-- Even-branch canonical scaled-deficit case. The scale is fixed to the
ceiling witness `((m - 1)/(B*x))+1`, removing the arbitrary existential `q`
from `linear_even_of_scaled_deficit`. -/
theorem linear_even_of_ceil_scaled_deficit {B x y l m : ℕ}
    (hBxpos : 0 < B * x)
    (hdef : (((m - 1) / (B * x) + 1) * (l - B * y) < l)) :
    l * m + 1 ≤ B * (x * l + y * m) := by
  exact linear_even_of_scaled_deficit hBxpos
    (le_ceilSubOneDiv_succ_mul hBxpos) hdef

/-- Odd-branch canonical scaled-deficit case. The fixed ceiling witness
`((m - 1)/(B*x))+1` covers `m`, and the scaled odd y-deficit remains below
`l`. -/
theorem linear_odd_of_ceil_scaled_deficit {B x y l m : ℕ}
    (hBx : 2 ≤ B * x)
    (hdef : (((m - 1) / (B * x) + 1) * (2 * l - B * y) < l)) :
    2 * (l * m + 1) ≤ B * (x * l + y * m) := by
  have hBxpos : 0 < B * x := by omega
  exact linear_odd_of_scaled_deficit hBx
    (le_ceilSubOneDiv_succ_mul hBxpos) hdef

/-- Parity-branch target from the canonical ceiling-scaled y-deficit
condition. This is the machine form of the current C2 target: either y already
covers the branch threshold, or the fixed ceiling number of `B*x` blocks makes
the remaining deficit fit inside `l`. -/
theorem parity_linear_ineq_of_ceil_scaled_deficit_coverage {B c x y l m : ℕ}
    (hlpos : 0 < l)
    (hBx : 2 ≤ B * x)
    (hcover :
      (Odd c ∧
          (2 * l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (2 * l - B * y) < l)) ∨
        (Even c ∧
          (l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (l - B * y) < l))) :
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) := by
  have hpos : 2 ≤ B * x * l := by nlinarith
  have hBxpos : 0 < B * x := by omega
  rcases hcover with ⟨hcodd, hbranch⟩ | ⟨hceven, hbranch⟩
  · rcases hbranch with hycover | hdef
    · exact Or.inl ⟨hcodd, linear_odd_of_y_covers_two_l hpos hycover⟩
    · exact Or.inl ⟨hcodd, linear_odd_of_ceil_scaled_deficit hBx hdef⟩
  · rcases hbranch with hycover | hdef
    · have hpos1 : 1 ≤ B * x * l := by omega
      exact Or.inr ⟨hceven, linear_even_of_y_covers_l hpos1 hycover⟩
    · exact Or.inr ⟨hceven,
        linear_even_of_ceil_scaled_deficit hBxpos hdef⟩

/-- Product-form parity certificate. For odd `c`, it is enough to prove
`c * (L + 1) ≤ M`; for even `c`, it is enough to prove
`(c / 2) * (L + 1) ≤ M`. -/
theorem not_dvd_mul_of_parity_product_gap {M c L : ℕ}
    (hMpos : 0 < M)
    (hModd : Odd M)
    (hcpos : 0 < c)
    (hLpos : 0 < L)
    (hgap : (Odd c ∧ c * (L + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (L + 1) ≤ M)) :
    ¬ M ∣ c * L := by
  refine not_dvd_mul_of_parity_reduced_divisor_gt hMpos hModd hcpos hLpos ?_
  rcases hgap with ⟨hcodd, hbound⟩ | ⟨hceven, hbound⟩
  · exact Or.inl ⟨hcodd, lt_div_of_mul_succ_le hcpos hbound⟩
  · have hc2pos : 0 < c / 2 := by
      rcases hceven with ⟨k, hk⟩
      have hkpos : 0 < k := by omega
      have hcdiv : c / 2 = k := by omega
      simpa [hcdiv] using hkpos
    exact Or.inr ⟨hceven, lt_div_of_mul_succ_le hc2pos hbound⟩

/-- The half-row identity forces `gcd alpha beta` to divide `2*M`. This is
the exact denominator fact behind the parity branch of the reduced-divisor
target. -/
theorem gcd_alpha_beta_dvd_two_half_row_of_identity {M B l m alpha beta c : ℕ}
    (hc : c = Nat.gcd alpha beta)
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m)) :
    c ∣ 2 * M := by
  subst c
  have hcalpha : Nat.gcd alpha beta ∣ alpha := Nat.gcd_dvd_left alpha beta
  have hcbeta : Nat.gcd alpha beta ∣ beta := Nat.gcd_dvd_right alpha beta
  have hcab : Nat.gcd alpha beta ∣ alpha * beta :=
    dvd_mul_of_dvd_left hcalpha beta
  have hc2ab : Nat.gcd alpha beta ∣ 2 * (alpha * beta) :=
    dvd_mul_of_dvd_right hcab 2
  have hcal : Nat.gcd alpha beta ∣ alpha * l :=
    dvd_mul_of_dvd_left hcalpha l
  have hcbm : Nat.gcd alpha beta ∣ beta * m :=
    dvd_mul_of_dvd_left hcbeta m
  have hcsum : Nat.gcd alpha beta ∣ alpha * l + beta * m :=
    Nat.dvd_add hcal hcbm
  have hcBsum : Nat.gcd alpha beta ∣ B * (alpha * l + beta * m) :=
    dvd_mul_of_dvd_right hcsum B
  rw [hhalf]
  exact Nat.dvd_add hc2ab hcBsum

/-- If `c = gcd alpha beta` is odd, the half-row identity forces the full
`c` into the half-row modulus: `gcd c M = c`. -/
theorem gcd_alpha_beta_half_row_eq_self_of_odd {M B l m alpha beta c : ℕ}
    (hc : c = Nat.gcd alpha beta)
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m))
    (hcodd : Odd c) :
    Nat.gcd c M = c := by
  have hcdvd2M : c ∣ 2 * M :=
    gcd_alpha_beta_dvd_two_half_row_of_identity hc hhalf
  have hcop2 : c.Coprime 2 := Nat.coprime_two_right.mpr hcodd
  have hcM : c ∣ M :=
    hcop2.dvd_of_dvd_mul_right (by simpa [mul_comm] using hcdvd2M)
  exact Nat.dvd_antisymm (Nat.gcd_dvd_left c M) (Nat.dvd_gcd (dvd_rfl) hcM)

/-- If `c = gcd alpha beta` is even and the half-row modulus is odd, the
half-row identity forces exactly the odd half of `c` into the modulus:
`gcd c M = c / 2`. -/
theorem gcd_alpha_beta_half_row_eq_half_of_even {M B l m alpha beta c : ℕ}
    (hc : c = Nat.gcd alpha beta)
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m))
    (hModd : Odd M)
    (hcpos : 0 < c)
    (hceven : Even c) :
    Nat.gcd c M = c / 2 := by
  rcases hceven with ⟨q, hcq⟩
  have hqpos : 0 < q := by omega
  have hcdvd2M : c ∣ 2 * M :=
    gcd_alpha_beta_dvd_two_half_row_of_identity hc hhalf
  have hqM : q ∣ M := by
    rcases hcdvd2M with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hcq] at ht
    have ht' : 2 * M = 2 * (q * t) := by
      calc
        2 * M = (q + q) * t := ht
        _ = 2 * (q * t) := by ring
    exact Nat.mul_left_cancel (by decide : 0 < 2) ht'
  have hqC : q ∣ c := by
    refine ⟨2, ?_⟩
    rw [hcq]
    ring
  have hqGcd : q ∣ Nat.gcd c M := Nat.dvd_gcd hqC hqM
  have hGcdpos : 0 < Nat.gcd c M := Nat.gcd_pos_of_pos_left M hcpos
  have hq_le : q ≤ Nat.gcd c M := Nat.le_of_dvd hGcdpos hqGcd
  have hGcd_le : Nat.gcd c M ≤ c / 2 :=
    gcd_le_half_of_even_left_odd_right hcpos ⟨q, hcq⟩ hModd
  have hcdiv : c / 2 = q := by omega
  exact le_antisymm (by simpa [hcdiv] using hGcd_le) (by simpa [hcdiv] using hq_le)

/-- Under the half-row identity, the parity branch is exactly the
reduced-divisor denominator split: odd `c` contributes all of `c`, and even
`c` contributes exactly `c/2`. -/
theorem reduced_divisor_gap_iff_parity_gap_of_half_row_identity
    {M B l m alpha beta c L : ℕ}
    (hc : c = Nat.gcd alpha beta)
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m))
    (hModd : Odd M)
    (hcpos : 0 < c) :
    L < M / Nat.gcd c M ↔
      (Odd c ∧ L < M / c) ∨ (Even c ∧ L < M / (c / 2)) := by
  constructor
  · intro hgap
    rcases Nat.even_or_odd c with hceven | hcodd
    · have hgcd := gcd_alpha_beta_half_row_eq_half_of_even hc hhalf hModd
        hcpos hceven
      exact Or.inr ⟨hceven, by simpa [hgcd] using hgap⟩
    · have hgcd := gcd_alpha_beta_half_row_eq_self_of_odd hc hhalf hcodd
      exact Or.inl ⟨hcodd, by simpa [hgcd] using hgap⟩
  · rintro (⟨hcodd, hgap⟩ | ⟨hceven, hgap⟩)
    · have hgcd := gcd_alpha_beta_half_row_eq_self_of_odd hc hhalf hcodd
      simpa [hgcd] using hgap
    · have hgcd := gcd_alpha_beta_half_row_eq_half_of_even hc hhalf hModd
        hcpos hceven
      simpa [hgcd] using hgap

/-- The half-row modulus is odd for the power-of-two split setting. -/
theorem powerTwoSplit_half_row_odd {A B : ℕ}
    (hA4 : 4 ∣ A)
    (hApos : 0 < A)
    (hBodd : Odd B) :
    Odd (B * (A / 2) - 1) := by
  rcases hA4 with ⟨q, hAeq⟩
  rcases hBodd with ⟨_b, _hBeq⟩
  have hqpos : 0 < q := by omega
  have hBpos : 0 < B := by omega
  have hBqpos : 0 < B * q := Nat.mul_pos hBpos hqpos
  have hhalf : A / 2 = 2 * q := by
    rw [hAeq]
    omega
  have hmul : B * (2 * q) = 2 * (B * q) := by ring
  refine ⟨B * q - 1, ?_⟩
  rw [hhalf, hmul]
  omega

/-- Split specialization of
`gcd_alpha_beta_half_row_eq_self_of_odd`. In an admissible power-two split,
odd `c = gcd alpha beta` is exactly the part of the half-row modulus carried
by `c`. -/
theorem powerTwoSplitSubtractive_half_row_gcd_eq_self_of_odd
    {A B r s l m alpha beta c : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hc : c = Nat.gcd alpha beta)
    (hcodd : Odd c) :
    Nat.gcd c (B * (A / 2) - 1) = c := by
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  exact gcd_alpha_beta_half_row_eq_self_of_odd hc hhalf hcodd

/-- Split specialization of
`gcd_alpha_beta_half_row_eq_half_of_even`. In an admissible power-two split
with odd `B`, even `c = gcd alpha beta` contributes exactly `c/2` to the
half-row modulus. -/
theorem powerTwoSplitSubtractive_half_row_gcd_eq_half_of_even
    {A B r s l m alpha beta c : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hc : c = Nat.gcd alpha beta)
    (hcpos : 0 < c)
    (hceven : Even c) :
    Nat.gcd c (B * (A / 2) - 1) = c / 2 := by
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  exact gcd_alpha_beta_half_row_eq_half_of_even hc hhalf
    (powerTwoSplit_half_row_odd hA4 hApos hBodd) hcpos hceven

/-- In an admissible power-two split, the parity branch gap is equivalent to
the reduced-divisor gap. This upgrades the parity branch from a sufficient
condition to the exact denominator split for the remaining obstruction. -/
theorem powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_gap
    {A B r s l m alpha beta c : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hc : c = Nat.gcd alpha beta)
    (hcpos : 0 < c) :
    let M := B * (A / 2) - 1
    l * m < M / Nat.gcd c M ↔
      (Odd c ∧ l * m < M / c) ∨ (Even c ∧ l * m < M / (c / 2)) := by
  dsimp
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  exact reduced_divisor_gap_iff_parity_gap_of_half_row_identity
    (M := B * (A / 2) - 1) (B := B) (l := l) (m := m)
    (alpha := alpha) (beta := beta) (c := c) (L := l * m)
    hc hhalf (powerTwoSplit_half_row_odd hA4 hApos hBodd) hcpos

/-- In an admissible power-two split, the floor-free parity product target is
equivalent to the exact reduced-divisor gap. -/
theorem powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_product_gap
    {A B r s l m alpha beta c : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hc : c = Nat.gcd alpha beta)
    (hcpos : 0 < c) :
    let M := B * (A / 2) - 1
    l * m < M / Nat.gcd c M ↔
      (Odd c ∧ c * (l * m + 1) ≤ M) ∨
        (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp
  exact (powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_gap
    hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA halpha hbeta hc hcpos).trans
    (parity_product_gap_iff_parity_reduced_divisor_gap
      (M := B * (A / 2) - 1) (c := c) (L := l * m) hcpos).symm

/-- In an admissible power-two split, any branch where the parity denominator
is at most `B^2` automatically satisfies the product-form parity gap. The
universal product target is therefore reduced to the exceptional even branch
where `c / 2 > B^2`. -/
theorem powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hbound :
      let c := Nat.gcd alpha beta
      (Odd c ∧ c ≤ B * B) ∨ (Even c ∧ c / 2 ≤ B * B)) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    (Odd c ∧ c * (l * m + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp at hbound ⊢
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  have hab : alpha * beta + 1 = B * B * (l * m) :=
    powerTwoSplitSubtractive_alpha_beta_mul hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hbeta_pos : 0 < beta := by
    rw [hbeta]
    exact Nat.sub_pos_of_lt hsplit_lt.2
  have hc_le_alpha : Nat.gcd alpha beta ≤ alpha :=
    Nat.gcd_le_left beta halpha_pos
  have hc_le_beta : Nat.gcd alpha beta ≤ beta :=
    Nat.gcd_le_right alpha hbeta_pos
  rcases hbound with ⟨hcodd, hcB⟩ | ⟨hceven, hcB⟩
  · exact Or.inl ⟨hcodd,
      product_gap_of_factor_bound_by_B_sq hBge hlpos hmpos
        (Nat.gcd_pos_of_pos_left beta halpha_pos) hcB hc_le_alpha hc_le_beta
        hab hhalf⟩
  · have hc2_le_alpha : Nat.gcd alpha beta / 2 ≤ alpha :=
      (Nat.div_le_self (Nat.gcd alpha beta) 2).trans hc_le_alpha
    have hc2_le_beta : Nat.gcd alpha beta / 2 ≤ beta :=
      (Nat.div_le_self (Nat.gcd alpha beta) 2).trans hc_le_beta
    have hc2pos : 0 < Nat.gcd alpha beta / 2 := by
      rcases hceven with ⟨k, hk⟩
      have hcgcd_pos : 0 < Nat.gcd alpha beta :=
        Nat.gcd_pos_of_pos_left beta halpha_pos
      have hkpos : 0 < k := by omega
      have hcdiv : Nat.gcd alpha beta / 2 = k := by omega
      simpa [hcdiv] using hkpos
    exact Or.inr ⟨hceven,
      product_gap_of_factor_bound_by_B_sq hBge hlpos hmpos hc2pos hcB
        hc2_le_alpha hc2_le_beta hab hhalf⟩

/-- To prove the split product-form parity gap, it suffices to handle only
the large parity-denominator cases. The small denominator cases are discharged
by `powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq`. -/
theorem powerTwoSplitSubtractive_parity_product_gap_of_large_denominator_product_gap
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hlargeOdd :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      Odd c → B * B < c → c * (l * m + 1) ≤ M)
    (hlargeEven :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      Even c → B * B < c / 2 → (c / 2) * (l * m + 1) ≤ M) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    (Odd c ∧ c * (l * m + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp at hlargeOdd hlargeEven ⊢
  rcases Nat.even_or_odd (Nat.gcd alpha beta) with hceven | hcodd
  · rcases le_or_gt (Nat.gcd alpha beta / 2) (B * B) with hsmall | hlarge
    · exact powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq
        hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
        (Or.inr ⟨hceven, hsmall⟩)
    · exact Or.inr ⟨hceven, hlargeEven hceven hlarge⟩
  · rcases le_or_gt (Nat.gcd alpha beta) (B * B) with hsmall | hlarge
    · exact powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq
        hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
        (Or.inl ⟨hcodd, hsmall⟩)
    · exact Or.inl ⟨hcodd, hlargeOdd hcodd hlarge⟩

/-- Split specialization of the quotient form of the parity product gap. This
replaces the product target by normalized gcd quotients `alpha = c*x` and
`beta = c*y`. -/
theorem powerTwoSplitSubtractive_parity_product_gap_of_gcd_quotient_ineq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hquot :
      let c := Nat.gcd alpha beta
      ∃ x y : ℕ,
        alpha = c * x ∧
          beta = c * y ∧
            ((Odd c ∧
                2 * (l * m + 1) ≤ 2 * c * (x * y) + B * (x * l + y * m)) ∨
              (Even c ∧
                l * m + 1 ≤ 2 * c * (x * y) + B * (x * l + y * m)))) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    (Odd c ∧ c * (l * m + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp at hquot ⊢
  rcases hquot with ⟨x, y, halpha_c, hbeta_c, hgap⟩
  let c := Nat.gcd alpha beta
  have halpha_c' : alpha = c * x := halpha_c
  have hbeta_c' : beta = c * y := hbeta_c
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  have hhalf_quot :
      2 * (B * (A / 2) - 1) =
        2 * ((c * x) * (c * y)) +
          B * ((c * x) * l + (c * y) * m) := by
    have hhalf' := hhalf
    rw [halpha_c', hbeta_c'] at hhalf'
    exact hhalf'
  exact parity_product_gap_of_gcd_quotient_ineq hhalf_quot hgap

/-- Exact warning example: the quotient product identity and split orientation
alone do not imply the odd-branch quotient gap. The power-of-two row-sum
constraint is still essential. -/
theorem gcdQuotientBareIdentity_counterexample_not_quotient_gap :
    ∃ B c x y l m : ℕ,
      Odd B ∧
        3 ≤ B ∧
          Odd c ∧
            0 < x ∧
              0 < y ∧
                0 < l ∧
                  0 < m ∧
                    c * c * (x * y) + 1 = B * B * (l * m) ∧
                      x * l < y * m ∧
                        ¬ 2 * (l * m + 1) ≤
                          2 * c * (x * y) + B * (x * l + y * m) := by
  refine ⟨3, 19, 1, 26, 149, 7, ?_⟩
  constructor
  · exact ⟨1, by norm_num⟩
  constructor
  · norm_num
  constructor
  · exact ⟨9, by norm_num⟩
  norm_num

/-- Exact warning example: adding the quotient row-sum identity and `4 ∣ A`
still does not imply the stronger linear target. The actual power-of-two
row-sum hypothesis is not replaceable by four-divisibility alone. -/
theorem gcdQuotientFourDvdRowSum_counterexample_not_linear_gap :
    ∃ A B c x y l m : ℕ,
      4 ∣ A ∧
        Odd B ∧
          3 ≤ B ∧
            Even c ∧
              0 < c ∧
                0 < x ∧
                  0 < y ∧
                    0 < l ∧
                      0 < m ∧
                        Nat.Coprime x y ∧
                          c * c * (x * y) + 1 = B * B * (l * m) ∧
                            A = 2 * B * (l * m) + c * (x * l + y * m) ∧
                              x * l < y * m ∧
                                ¬ l * m + 1 ≤ B * (x * l + y * m) := by
  refine ⟨73176, 3, 38, 1, 38, 469, 13, ?_⟩
  constructor
  · norm_num
  constructor
  · exact ⟨1, by norm_num⟩
  constructor
  · norm_num
  constructor
  · exact ⟨19, by norm_num⟩
  norm_num

/-- Product identity in normalized gcd-quotient variables. -/
theorem powerTwoSplitSubtractive_gcd_quotient_product_identity
    {A B r s l m alpha beta c x y : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (halpha_c : alpha = c * x)
    (hbeta_c : beta = c * y) :
    c * c * (x * y) + 1 = B * B * (l * m) := by
  have hab : alpha * beta + 1 = B * B * (l * m) :=
    powerTwoSplitSubtractive_alpha_beta_mul hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
  nlinarith [hab, halpha_c, hbeta_c]

/-- Row-sum identity in normalized gcd-quotient variables. -/
theorem powerTwoSplitSubtractive_gcd_quotient_A_identity
    {A B r s l m alpha beta c x y : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (halpha_c : alpha = c * x)
    (hbeta_c : beta = c * y) :
    A = 2 * B * (l * m) + c * (x * l + y * m) := by
  rcases powerTwoSplitSubtractive_to_additive hBge hrpos hspos hlpos hmpos
      hD hA halpha hbeta with ⟨hr, hs⟩
  nlinarith [hA, hr, hs, halpha_c, hbeta_c]

/-- The chosen split orientation becomes `x*l < y*m` after passing to
normalized gcd-quotient variables. -/
theorem powerTwoSplitSubtractive_gcd_quotient_gap
    {A B r s l m alpha beta c x y : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hcpos : 0 < c)
    (halpha_c : alpha = c * x)
    (hbeta_c : beta = c * y) :
    x * l < y * m := by
  rcases powerTwoSplitSubtractive_to_additive hBge hrpos hspos hlpos hmpos
      hD hA halpha hbeta with ⟨hr, hs⟩
  have hcxcy : c * (x * l) < c * (y * m) := by
    nlinarith [hgap, hr, hs, halpha_c, hbeta_c]
  exact (Nat.mul_lt_mul_left hcpos).mp hcxcy

/-- Canonical-division interface for the normalized gcd-quotient inequality.
The witnesses are exactly `alpha / gcd alpha beta` and
`beta / gcd alpha beta`. -/
theorem powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_quotient_ineq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hquot :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧
          2 * (l * m + 1) ≤ 2 * c * (x * y) + B * (x * l + y * m)) ∨
        (Even c ∧
          l * m + 1 ≤ 2 * c * (x * y) + B * (x * l + y * m))) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    (Odd c ∧ c * (l * m + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp at hquot ⊢
  let c := Nat.gcd alpha beta
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have hcbeta : c ∣ beta := Nat.gcd_dvd_right alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hbeta_div : beta = c * (beta / c) := by
    have h := Nat.div_mul_cancel hcbeta
    simpa [mul_comm] using h.symm
  exact powerTwoSplitSubtractive_parity_product_gap_of_gcd_quotient_ineq
    hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
    ⟨alpha / c, beta / c, halpha_div, hbeta_div, hquot⟩

/-- In an admissible power-two split, the canonical normalized gcd-quotient
target is equivalent to the exact reduced-divisor gap. This is the split-level
version of `parity_reduced_divisor_gap_iff_gcd_quotient_ineq`, with canonical
quotients `alpha / gcd alpha beta` and `beta / gcd alpha beta`. -/
theorem powerTwoSplitSubtractive_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (_hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let x := alpha / c
    let y := beta / c
    l * m < M / Nat.gcd c M ↔
      ((Odd c ∧
          2 * (l * m + 1) ≤ 2 * c * (x * y) + B * (x * l + y * m)) ∨
        (Even c ∧
          l * m + 1 ≤ 2 * c * (x * y) + B * (x * l + y * m))) := by
  dsimp
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcpos : 0 < c := Nat.gcd_pos_of_pos_left beta halpha_pos
  have hparity :
      l * m < (B * (A / 2) - 1) / Nat.gcd c (B * (A / 2) - 1) ↔
        (Odd c ∧ l * m < (B * (A / 2) - 1) / c) ∨
          (Even c ∧ l * m < (B * (A / 2) - 1) / (c / 2)) :=
    powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_gap
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) (c := c)
      hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA halpha hbeta rfl hcpos
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have hcbeta : c ∣ beta := Nat.gcd_dvd_right alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hbeta_div : beta = c * (beta / c) := by
    have h := Nat.div_mul_cancel hcbeta
    simpa [mul_comm] using h.symm
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos hspos
      hlpos hmpos hD hA halpha hbeta
  have hhalf_quot :
      2 * (B * (A / 2) - 1) =
        2 * ((c * (alpha / c)) * (c * (beta / c))) +
          B * ((c * (alpha / c)) * l + (c * (beta / c)) * m) := by
    rw [← halpha_div, ← hbeta_div]
    exact hhalf
  exact hparity.trans
    (parity_reduced_divisor_gap_iff_gcd_quotient_ineq
      (M := B * (A / 2) - 1) (B := B) (l := l) (m := m)
      (c := c) (x := alpha / c) (y := beta / c) (L := l * m)
      hcpos hhalf_quot)

/-- Universal form of the exact canonical quotient target. For fixed `A, B`,
the universal reduced-divisor gap hypothesis used by the kernel consumers is
equivalent to the universal canonical normalized gcd-quotient inequality. -/
theorem powerTwoSplit_all_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq
    {A B : ℕ} :
    (((∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  l * m <
                                    (B * (A / 2) - 1) /
                                      Nat.gcd (Nat.gcd alpha beta)
                                        (B * (A / 2) - 1)) ↔
      ((∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m)))) := by
  constructor
  · intro hgapAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
      hlpos hmpos hD hA hsplitgap halpha hbeta
    exact
      (powerTwoSplitSubtractive_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq
        (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
        (alpha := alpha) (beta := beta) hA4 hBodd hBge hrpos hspos
        hlpos hmpos hD hA hsplitgap halpha hbeta).mp
        (hgapAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
          hlpos hmpos hD hA hsplitgap halpha hbeta)
  · intro hquotAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
      hlpos hmpos hD hA hsplitgap halpha hbeta
    exact
      (powerTwoSplitSubtractive_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq
        (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
        (alpha := alpha) (beta := beta) hA4 hBodd hBge hrpos hspos
        hlpos hmpos hD hA hsplitgap halpha hbeta).mpr
        (hquotAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
          hlpos hmpos hD hA hsplitgap halpha hbeta)

/-- Canonical-division interface for the stronger linear normalized
gcd-quotient inequality. The linear target discards the nonnegative
`2*c*x*y` term from the quotient target. -/
theorem powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_linear_ineq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hlin :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    (Odd c ∧ c * (l * m + 1) ≤ M) ∨
      (Even c ∧ (c / 2) * (l * m + 1) ≤ M) := by
  dsimp at hlin ⊢
  refine
    powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_quotient_ineq
      hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta ?_
  dsimp
  rcases hlin with ⟨hcodd, hineq⟩ | ⟨hceven, hineq⟩
  · exact Or.inl ⟨hcodd, hineq.trans
      (Nat.le_add_left
        (B * (alpha / Nat.gcd alpha beta * l + beta / Nat.gcd alpha beta * m))
        (2 * Nat.gcd alpha beta *
          (alpha / Nat.gcd alpha beta * (beta / Nat.gcd alpha beta))))⟩
  · exact Or.inr ⟨hceven, hineq.trans
      (Nat.le_add_left
        (B * (alpha / Nat.gcd alpha beta * l + beta / Nat.gcd alpha beta * m))
        (2 * Nat.gcd alpha beta *
          (alpha / Nat.gcd alpha beta * (beta / Nat.gcd alpha beta))))⟩

/-- Canonical normalized linear target as a deficit-compensation condition.
This is an exact reformulation: after setting
`x = alpha / gcd alpha beta` and `y = beta / gcd alpha beta`, the odd branch
asks `B*x*l` to cover `m*(2*l - B*y)+2`, while the even branch asks it to
cover `m*(l - B*y)+1`. -/
theorem powerTwoSplitSubtractive_canonical_gcd_linear_ineq_iff_deficit_ineq
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (_hbeta : beta = s - B * l) :
    let c := Nat.gcd alpha beta
    let x := alpha / c
    let y := beta / c
    ((Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) ↔
      ((Odd c ∧ m * (2 * l - B * y) + 2 ≤ B * x * l) ∨
        (Even c ∧ m * (l - B * y) + 1 ≤ B * x * l)) := by
  dsimp
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hxpos : 0 < alpha / c := by
    by_contra hxnot
    have hx0 : alpha / c = 0 := Nat.eq_zero_of_not_pos hxnot
    have : alpha = 0 := by
      rw [halpha_div, hx0, mul_zero]
    omega
  have hpos : 2 ≤ B * (alpha / c) * l := by
    have hx1 : 1 ≤ alpha / c := hxpos
    have hl1 : 1 ≤ l := hlpos
    calc
      2 ≤ 3 * 1 * 1 := by norm_num
      _ ≤ B * (alpha / c) * l := Nat.mul_le_mul (Nat.mul_le_mul hBge hx1) hl1
  exact parity_linear_ineq_iff_deficit_ineq
    (B := B) (c := c) (x := alpha / c) (y := beta / c) (l := l)
    (m := m) hpos

/-- Split specialization of the automatic y-coverage branch for the canonical
linear target. In canonical variables, the odd branch is automatic from
`2*l ≤ B*y`, and the even branch is automatic from `l ≤ B*y`. -/
theorem powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_y_coverage
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (_hbeta : beta = s - B * l)
    (hcover :
      let c := Nat.gcd alpha beta
      let y := beta / c
      (Odd c ∧ 2 * l ≤ B * y) ∨ (Even c ∧ l ≤ B * y)) :
    let c := Nat.gcd alpha beta
    let x := alpha / c
    let y := beta / c
    (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
      (Even c ∧ l * m + 1 ≤ B * (x * l + y * m)) := by
  dsimp at hcover ⊢
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcpos : 0 < c := Nat.gcd_pos_of_pos_left beta halpha_pos
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hxpos : 0 < alpha / c := by
    by_contra hxnot
    have hx0 : alpha / c = 0 := Nat.eq_zero_of_not_pos hxnot
    have : alpha = 0 := by
      rw [halpha_div, hx0, mul_zero]
    omega
  have hpos : 2 ≤ B * (alpha / c) * l := by
    have hx1 : 1 ≤ alpha / c := hxpos
    have hl1 : 1 ≤ l := hlpos
    calc
      2 ≤ 3 * 1 * 1 := by norm_num
      _ ≤ B * (alpha / c) * l := Nat.mul_le_mul (Nat.mul_le_mul hBge hx1) hl1
  exact parity_linear_ineq_of_y_coverage
    (B := B) (c := c) (x := alpha / c) (y := beta / c) (l := l)
    (m := m) hpos hcover

/-- Split specialization of the first residual x-compensation branch. In the
odd branch, after full y-coverage fails it is still enough to have
`l < B*y` and `m ≤ B*x`; in the even branch, `m ≤ B*x` itself is enough. -/
theorem powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_y_or_x_coverage
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hcover :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧ (2 * l ≤ B * y ∨ (l < B * y ∧ m ≤ B * x))) ∨
        (Even c ∧ (l ≤ B * y ∨ m ≤ B * x))) :
    let c := Nat.gcd alpha beta
    let x := alpha / c
    let y := beta / c
    (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
      (Even c ∧ l * m + 1 ≤ B * (x * l + y * m)) := by
  dsimp at hcover ⊢
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hbeta_pos : 0 < beta := by
    rw [hbeta]
    exact Nat.sub_pos_of_lt hsplit_lt.2
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have hcbeta : c ∣ beta := Nat.gcd_dvd_right alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hbeta_div : beta = c * (beta / c) := by
    have h := Nat.div_mul_cancel hcbeta
    simpa [mul_comm] using h.symm
  have hxpos : 0 < alpha / c := by
    by_contra hxnot
    have hx0 : alpha / c = 0 := Nat.eq_zero_of_not_pos hxnot
    have : alpha = 0 := by
      rw [halpha_div, hx0, mul_zero]
    omega
  have hypos : 0 < beta / c := by
    by_contra hynot
    have hy0 : beta / c = 0 := Nat.eq_zero_of_not_pos hynot
    have : beta = 0 := by
      rw [hbeta_div, hy0, mul_zero]
    omega
  have hBx : 2 ≤ B * (alpha / c) := by
    have hx1 : 1 ≤ alpha / c := hxpos
    calc
      2 ≤ 3 * 1 := by norm_num
      _ ≤ B * (alpha / c) := Nat.mul_le_mul hBge hx1
  have hbonus : 1 ≤ B * (beta / c) * m := by
    have hBpos : 0 < B := by omega
    exact Nat.mul_pos (Nat.mul_pos hBpos hypos) hmpos
  exact parity_linear_ineq_of_y_or_x_coverage
    (B := B) (c := c) (x := alpha / c) (y := beta / c) (l := l)
    (m := m) hlpos hBx hbonus hcover

/-- Split specialization of the scaled y-deficit x-compensation branch. It
packages the same canonical variables as the y-or-x branch, but lets the
residual deficit be covered by a scale witness `q`. -/
theorem powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_scaled_deficit_coverage
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (_hbeta : beta = s - B * l)
    (hcover :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧
          (2 * l ≤ B * y ∨
            ∃ q : ℕ, m ≤ q * (B * x) ∧ q * (2 * l - B * y) < l)) ∨
        (Even c ∧
          (l ≤ B * y ∨
            ∃ q : ℕ, m ≤ q * (B * x) ∧ q * (l - B * y) < l))) :
    let c := Nat.gcd alpha beta
    let x := alpha / c
    let y := beta / c
    (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
      (Even c ∧ l * m + 1 ≤ B * (x * l + y * m)) := by
  dsimp at hcover ⊢
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hxpos : 0 < alpha / c := by
    by_contra hxnot
    have hx0 : alpha / c = 0 := Nat.eq_zero_of_not_pos hxnot
    have : alpha = 0 := by
      rw [halpha_div, hx0, mul_zero]
    omega
  have hBx : 2 ≤ B * (alpha / c) := by
    have hx1 : 1 ≤ alpha / c := hxpos
    calc
      2 ≤ 3 * 1 := by norm_num
      _ ≤ B * (alpha / c) := Nat.mul_le_mul hBge hx1
  exact parity_linear_ineq_of_scaled_deficit_coverage
    (B := B) (c := c) (x := alpha / c) (y := beta / c) (l := l)
    (m := m) hlpos hBx hcover

/-- Split specialization of the canonical ceiling-scaled y-deficit branch.
This packages the computable scale `((m - 1)/(B*x))+1` in the canonical
gcd-quotient variables. -/
theorem powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_ceil_scaled_deficit_coverage
    {A B r s l m alpha beta : ℕ}
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (_hbeta : beta = s - B * l)
    (hcover :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧
          (2 * l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (2 * l - B * y) < l)) ∨
        (Even c ∧
          (l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (l - B * y) < l))) :
    let c := Nat.gcd alpha beta
    let x := alpha / c
    let y := beta / c
    (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
      (Even c ∧ l * m + 1 ≤ B * (x * l + y * m)) := by
  dsimp at hcover ⊢
  let c := Nat.gcd alpha beta
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcalpha : c ∣ alpha := Nat.gcd_dvd_left alpha beta
  have halpha_div : alpha = c * (alpha / c) := by
    have h := Nat.div_mul_cancel hcalpha
    simpa [mul_comm] using h.symm
  have hxpos : 0 < alpha / c := by
    by_contra hxnot
    have hx0 : alpha / c = 0 := Nat.eq_zero_of_not_pos hxnot
    have : alpha = 0 := by
      rw [halpha_div, hx0, mul_zero]
    omega
  have hBx : 2 ≤ B * (alpha / c) := by
    have hx1 : 1 ≤ alpha / c := hxpos
    calc
      2 ≤ 3 * 1 := by norm_num
      _ ≤ B * (alpha / c) := Nat.mul_le_mul hBge hx1
  exact parity_linear_ineq_of_ceil_scaled_deficit_coverage
    (B := B) (c := c) (x := alpha / c) (y := beta / c) (l := l)
    (m := m) hlpos hBx hcover

/-- The canonical linear inequality is strong enough to prove the exact
reduced-divisor gap, because the exact quotient target has the additional
nonnegative `2*c*x*y` term. -/
theorem powerTwoSplitSubtractive_reduced_divisor_gap_of_canonical_gcd_linear_ineq
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hlin :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧ 2 * (l * m + 1) ≤ B * (x * l + y * m)) ∨
        (Even c ∧ l * m + 1 ≤ B * (x * l + y * m))) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    l * m < M / Nat.gcd c M := by
  dsimp at hlin ⊢
  let c := Nat.gcd alpha beta
  have hquot :
      (Odd c ∧
          2 * (l * m + 1) ≤
            2 * c * ((alpha / c) * (beta / c)) +
              B * ((alpha / c) * l + (beta / c) * m)) ∨
        (Even c ∧
          l * m + 1 ≤
            2 * c * ((alpha / c) * (beta / c)) +
              B * ((alpha / c) * l + (beta / c) * m)) := by
    rcases hlin with ⟨hcodd, hineq⟩ | ⟨hceven, hineq⟩
    · exact Or.inl ⟨hcodd,
        hineq.trans (Nat.le_add_left
          (B * ((alpha / c) * l + (beta / c) * m))
          (2 * c * ((alpha / c) * (beta / c))))⟩
    · exact Or.inr ⟨hceven,
        hineq.trans (Nat.le_add_left
          (B * ((alpha / c) * l + (beta / c) * m))
          (2 * c * ((alpha / c) * (beta / c))))⟩
  exact
    (powerTwoSplitSubtractive_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta)
      hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA hgap halpha
      hbeta).mpr hquot

/-- Exact reduced-divisor gap from the canonical ceiling-scaled y-deficit
condition. This records the current C2 branch as a direct sufficient
condition for `M / gcd(c, M) > l*m`, not merely for a later no-divisibility
consumer. -/
theorem powerTwoSplitSubtractive_reduced_divisor_gap_of_canonical_gcd_ceil_scaled_deficit_coverage
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hcover :
      let c := Nat.gcd alpha beta
      let x := alpha / c
      let y := beta / c
      (Odd c ∧
          (2 * l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (2 * l - B * y) < l)) ∨
        (Even c ∧
          (l ≤ B * y ∨
            ((m - 1) / (B * x) + 1) * (l - B * y) < l))) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    l * m < M / Nat.gcd c M := by
  refine
    powerTwoSplitSubtractive_reduced_divisor_gap_of_canonical_gcd_linear_ineq
      hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA hgap halpha hbeta ?_
  exact
    powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_ceil_scaled_deficit_coverage
      hBge hrpos hspos hlpos hmpos hD hA halpha hbeta hcover

/-- Universal exact reduced-divisor gap from the canonical linear inequality.
This exposes the direct target consumed by
`powerTwoSplitGcdObstruction_of_reduced_divisor_gap`, without routing through
the parity-product sufficient condition. -/
theorem powerTwoSplit_all_reduced_divisor_gap_of_canonical_gcd_linear_ineq
    {A B : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  l * m < M / Nat.gcd c M := by
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos hD
    hA hgap halpha hbeta
  exact
    powerTwoSplitSubtractive_reduced_divisor_gap_of_canonical_gcd_linear_ineq
      hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA hgap halpha hbeta
      (hlinAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hgap halpha hbeta)

/-- Universal exact reduced-divisor gap from the canonical ceiling-scaled
branch. This is the direct exact-gap version of the current computable C2
condition. -/
theorem powerTwoSplit_all_reduced_divisor_gap_of_canonical_gcd_ceil_scaled_deficit_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  l * m < M / Nat.gcd c M := by
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos hD
    hA hgap halpha hbeta
  exact
    powerTwoSplitSubtractive_reduced_divisor_gap_of_canonical_gcd_ceil_scaled_deficit_coverage
      hA4 hBodd hBge hrpos hspos hlpos hmpos hD hA hgap halpha hbeta
      (hcoverAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hgap halpha hbeta)

/-- Split-level parity-branch certificate for the reduced divisor target. -/
theorem powerTwoSplitSubtractive_not_gcd_dvd_of_parity_reduced_divisor_gap
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hApos : 0 < A)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hcpos : 0 < Nat.gcd alpha beta)
    (hgap :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      (Odd c ∧ l * m < M / c) ∨ (Even c ∧ l * m < M / (c / 2))) :
    ¬ B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) := by
  dsimp at hgap
  exact not_dvd_mul_of_parity_reduced_divisor_gt
    (powerTwoSplit_half_row_pos hA4 hBge hApos)
    (powerTwoSplit_half_row_odd hA4 hApos hBodd)
    hcpos
    (Nat.mul_pos hlpos hmpos)
    hgap

/-- Split-level product-form parity certificate. -/
theorem powerTwoSplitSubtractive_not_gcd_dvd_of_parity_product_gap
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hApos : 0 < A)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hcpos : 0 < Nat.gcd alpha beta)
    (hgap :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      (Odd c ∧ c * (l * m + 1) ≤ M) ∨
        (Even c ∧ (c / 2) * (l * m + 1) ≤ M)) :
    ¬ B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) := by
  dsimp at hgap
  exact not_dvd_mul_of_parity_product_gap
    (powerTwoSplit_half_row_pos hA4 hBge hApos)
    (powerTwoSplit_half_row_odd hA4 hApos hBodd)
    hcpos
    (Nat.mul_pos hlpos hmpos)
    hgap

/-- If every admissible positive split satisfies the parity-branch gap
inequality, then the split/gcd obstruction holds. This is a weaker-looking
but often easier target than the exact reduced-divisor gap, because the
half-row modulus is odd. -/
theorem powerTwoSplitGcdObstruction_of_parity_reduced_divisor_gap {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ l * m < M / c) ∨
                                    (Even c ∧ l * m < M / (c / 2))) :
    powerTwoSplitGcdObstruction A B := by
  intro hApow hA4 hBodd hBge r s l m alpha beta c hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta hc
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcpos : 0 < Nat.gcd alpha beta :=
    Nat.gcd_pos_of_pos_left beta halpha_pos
  rw [hc]
  exact powerTwoSplitSubtractive_not_gcd_dvd_of_parity_reduced_divisor_gap
    hA4 hBodd hBge hApos hlpos hmpos hcpos
    (hgapAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
      hmpos hD hA hsplitgap halpha hbeta)

/-- If every admissible positive split satisfies the product-form parity gap,
then the split/gcd obstruction holds. -/
theorem powerTwoSplitGcdObstruction_of_parity_product_gap {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ c * (l * m + 1) ≤ M) ∨
                                    (Even c ∧ (c / 2) * (l * m + 1) ≤ M)) :
    powerTwoSplitGcdObstruction A B := by
  intro hApow hA4 hBodd hBge r s l m alpha beta c hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta hc
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  have hsplit_lt := powerTwoSplitSubtractive_lt (A := A) (B := B) (r := r)
    (s := s) (l := l) (m := m) hBge hrpos hspos hlpos hmpos hD hA
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact Nat.sub_pos_of_lt hsplit_lt.1
  have hcpos : 0 < Nat.gcd alpha beta :=
    Nat.gcd_pos_of_pos_left beta halpha_pos
  rw [hc]
  exact powerTwoSplitSubtractive_not_gcd_dvd_of_parity_product_gap
    hA4 hBodd hBge hApos hlpos hmpos hcpos
    (hgapAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
      hmpos hD hA hsplitgap halpha hbeta)

/-- If every admissible positive split satisfies the product-form parity gap
only in the large parity-denominator branches, then the split/gcd obstruction
holds. The complementary small-denominator branches are proved by
`powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq`. -/
theorem powerTwoSplitGcdObstruction_of_large_parity_denominator_product_gap
    {A B : ℕ}
    (hlargeAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c → B * B < c →
                                    c * (l * m + 1) ≤ M) ∧
                                  (Even c → B * B < c / 2 →
                                    (c / 2) * (l * m + 1) ≤ M)) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_parity_product_gap ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  have hlarge := hlargeAll hApow hA4 hBodd hBge r s l m alpha beta hrpos
    hspos hlpos hmpos hD hA hsplitgap halpha hbeta
  exact powerTwoSplitSubtractive_parity_product_gap_of_large_denominator_product_gap
    hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta hlarge.1 hlarge.2

/-- If every admissible positive split satisfies the normalized gcd-quotient
inequality, then the split/gcd obstruction holds. -/
theorem powerTwoSplitGcdObstruction_of_gcd_quotient_ineq
    {A B : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  ∃ x y : ℕ,
                                    alpha = c * x ∧
                                      beta = c * y ∧
                                        ((Odd c ∧
                                            2 * (l * m + 1) ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)) ∨
                                          (Even c ∧
                                            l * m + 1 ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_parity_product_gap ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact powerTwoSplitSubtractive_parity_product_gap_of_gcd_quotient_ineq
    hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
    (hquotAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
      hmpos hD hA hsplitgap halpha hbeta)

/-- Canonical-division version of
`powerTwoSplitGcdObstruction_of_gcd_quotient_ineq`. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_quotient_ineq
    {A B : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_parity_product_gap ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_quotient_ineq
      hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
      (hquotAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Linear canonical-division version of
`powerTwoSplitGcdObstruction_of_canonical_gcd_quotient_ineq`. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq
    {A B : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_parity_product_gap ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_linear_ineq
      hA4 hBge hrpos hspos hlpos hmpos hD hA halpha hbeta
      (hlinAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Deficit-compensation version of
`powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq`. This keeps the
same proof strength while exposing exactly what the `B*x*l` term must cover
after the `B*y*m` term is subtracted. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_deficit_ineq
    {A B : ℕ}
    (hdefAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      m * (2 * l - B * y) + 2 ≤
                                        B * x * l) ∨
                                    (Even c ∧
                                      m * (l - B * y) + 1 ≤
                                        B * x * l)) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    (powerTwoSplitSubtractive_canonical_gcd_linear_ineq_iff_deficit_ineq
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta).mpr
      (hdefAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Automatic y-coverage version of the canonical linear target. If every
admissible split satisfies the branch condition `2*l ≤ B*y` in the odd case
and `l ≤ B*y` in the even case, then the split/gcd obstruction follows. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_y_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let y := beta / c
                                  (Odd c ∧ 2 * l ≤ B * y) ∨
                                    (Even c ∧ l ≤ B * y)) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_y_coverage
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
      (hcoverAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- First residual x-compensation version of the canonical linear target. If
every admissible split satisfies the y-or-x branch condition, then the
split/gcd obstruction follows. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_y_or_x_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        (l < B * y ∧ m ≤ B * x))) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨ m ≤ B * x))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_y_or_x_coverage
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
      (hcoverAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Scaled-deficit version of the canonical linear target. If every
admissible split satisfies the scaled y-deficit coverage condition, then the
split/gcd obstruction follows. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_scaled_deficit_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (l - B * y) < l))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_scaled_deficit_coverage
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
      (hcoverAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Canonical ceiling-scaled version of
`powerTwoSplitGcdObstruction_of_canonical_gcd_scaled_deficit_coverage`.
The arbitrary scale witness is fixed to `((m - 1)/(B*x))+1`, matching the
exact compute diagnostic. -/
theorem powerTwoSplitGcdObstruction_of_canonical_gcd_ceil_scaled_deficit_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
    powerTwoSplitGcdObstruction A B := by
  refine powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq ?_
  intro hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta
  exact
    powerTwoSplitSubtractive_canonical_gcd_linear_ineq_of_ceil_scaled_deficit_coverage
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hBge hrpos hspos hlpos hmpos hD hA
      halpha hbeta
      (hcoverAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
        hmpos hD hA hsplitgap halpha hbeta)

/-- Split-level reduced-divisor gap certificate: if
`l*m < M / gcd (gcd alpha beta) M`, then the split/gcd row-two divisibility
fails. -/
theorem powerTwoSplitSubtractive_not_gcd_dvd_of_reduced_divisor_gap
    {A B l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hApos : 0 < A)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap :
      l * m <
        (B * (A / 2) - 1) /
          Nat.gcd (Nat.gcd alpha beta) (B * (A / 2) - 1)) :
    ¬ B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) := by
  exact not_dvd_mul_of_reduced_divisor_gt
    (powerTwoSplit_half_row_pos hA4 hBge hApos)
    (Nat.mul_pos hlpos hmpos) hgap

/-- If every admissible positive split satisfies the reduced-divisor gap
inequality, then the split/gcd obstruction holds. This isolates the remaining
research target as an inequality rather than a divisibility statement. -/
theorem powerTwoSplitGcdObstruction_of_reduced_divisor_gap {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  l * m <
                                    (B * (A / 2) - 1) /
                                      Nat.gcd (Nat.gcd alpha beta)
                                        (B * (A / 2) - 1)) :
    powerTwoSplitGcdObstruction A B := by
  intro hApow hA4 hBodd hBge r s l m alpha beta c hrpos hspos hlpos hmpos
    hD hA hsplitgap halpha hbeta hc
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  rw [hc]
  exact powerTwoSplitSubtractive_not_gcd_dvd_of_reduced_divisor_gap
    hA4 hBge hApos hlpos hmpos
    (hgapAll hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos
      hmpos hD hA hsplitgap halpha hbeta)

/-- The two split identities force the part of the half-row modulus contained
in `alpha` to be exactly the part contained in `gcd alpha beta`. The key
point is that a common divisor of `alpha` and `M` divides `B * beta * m` by
the half-row identity, while `alpha * beta + 1 = B^2 * l * m` makes it
coprime to `B * m`. -/
theorem gcd_alpha_half_row_eq_gcd_gcd_of_identities {M B l m alpha beta : ℕ}
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m))
    (hab : alpha * beta + 1 = B * B * (l * m)) :
    Nat.gcd alpha M = Nat.gcd (Nat.gcd alpha beta) M := by
  let d := Nat.gcd alpha M
  have hdalpha : d ∣ alpha := Nat.gcd_dvd_left alpha M
  have hdM : d ∣ M := Nat.gcd_dvd_right alpha M
  have hdcoprime : d.Coprime (B * m) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    let e := Nat.gcd d (B * m)
    apply Nat.eq_one_of_dvd_one
    have hed : e ∣ d := Nat.gcd_dvd_left d (B * m)
    have heBm : e ∣ B * m := Nat.gcd_dvd_right d (B * m)
    have healpha : e ∣ alpha := Nat.dvd_trans hed hdalpha
    have healphabeta : e ∣ alpha * beta := dvd_mul_of_dvd_left healpha beta
    have heRhs0 : e ∣ (B * m) * (B * l) := dvd_mul_of_dvd_left heBm (B * l)
    have heRhs : e ∣ B * B * (l * m) := by
      convert heRhs0 using 1
      ring
    have heSucc : e ∣ alpha * beta + 1 := by
      rw [hab]
      exact heRhs
    have hone : e ∣ (alpha * beta + 1) - alpha * beta :=
      Nat.dvd_sub heSucc healphabeta
    simpa using hone
  have hdbeta : d ∣ beta := by
    have hd_twoM : d ∣ 2 * M := dvd_mul_of_dvd_right hdM 2
    have hd_rhs : d ∣ 2 * (alpha * beta) + B * (alpha * l + beta * m) := by
      rw [← hhalf]
      exact hd_twoM
    have hd_alphabeta : d ∣ alpha * beta := dvd_mul_of_dvd_left hdalpha beta
    have hd_two_alphabeta : d ∣ 2 * (alpha * beta) :=
      dvd_mul_of_dvd_right hd_alphabeta 2
    have hd_rest : d ∣ B * (alpha * l + beta * m) :=
      (Nat.dvd_add_iff_right hd_two_alphabeta).mpr hd_rhs
    have hd_alpha_l : d ∣ alpha * l := dvd_mul_of_dvd_left hdalpha l
    have hd_B_alpha_l : d ∣ B * (alpha * l) :=
      dvd_mul_of_dvd_right hd_alpha_l B
    have hd_rest' : d ∣ B * (alpha * l) + B * (beta * m) := by
      convert hd_rest using 1
      ring
    have hd_B_beta_m : d ∣ B * (beta * m) :=
      (Nat.dvd_add_iff_right hd_B_alpha_l).mpr hd_rest'
    have hd_Bm_beta : d ∣ (B * m) * beta := by
      convert hd_B_beta_m using 1
      ring
    exact hdcoprime.dvd_of_dvd_mul_left hd_Bm_beta
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.dvd_gcd hdalpha hdbeta
    · exact hdM
  · apply Nat.dvd_gcd
    · exact Nat.dvd_trans
        (Nat.gcd_dvd_left (Nat.gcd alpha beta) M)
        (Nat.gcd_dvd_left alpha beta)
    · exact Nat.gcd_dvd_right (Nat.gcd alpha beta) M

/-- Under the split identities, row-two divisibility with the `alpha` factor
is equivalent to row-two divisibility with `gcd alpha beta`. -/
theorem alpha_mul_dvd_iff_gcd_mul_dvd_of_split_identities
    {M B l m alpha beta : ℕ}
    (hMpos : 0 < M)
    (hhalf : 2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m))
    (hab : alpha * beta + 1 = B * B * (l * m)) :
    M ∣ (l * m) * alpha ↔ M ∣ Nat.gcd alpha beta * (l * m) := by
  have hgcd : Nat.gcd alpha M = Nat.gcd (Nat.gcd alpha beta) M :=
    gcd_alpha_half_row_eq_gcd_gcd_of_identities hhalf hab
  have hleft : M ∣ alpha * (l * m) ↔ M / Nat.gcd alpha M ∣ l * m :=
    dvd_mul_iff_div_gcd_dvd hMpos
  have hright :
      M ∣ Nat.gcd alpha beta * (l * m) ↔
        M / Nat.gcd (Nat.gcd alpha beta) M ∣ l * m :=
    dvd_mul_iff_div_gcd_dvd hMpos
  constructor
  · intro h
    have h_alpha : M ∣ alpha * (l * m) := by
      convert h using 1
      ring
    exact hright.mpr (by
      simpa [hgcd] using hleft.mp h_alpha)
  · intro h
    have hred := hright.mp h
    have h_alpha : M ∣ alpha * (l * m) :=
      hleft.mpr (by simpa [hgcd] using hred)
    convert h_alpha using 1
    ring

/-- Subtractive split specialization of the alpha-to-gcd row-two bridge. -/
theorem powerTwoSplitSubtractive_row_two_alpha_dvd_iff_gcd_dvd
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    B * (A / 2) - 1 ∣ (l * m) * alpha ↔
      B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) := by
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  have hA2 : 2 ∣ A := dvd_trans (by decide : 2 ∣ 4) hA4
  have hMpos : 0 < B * (A / 2) - 1 :=
    powerTwoSplit_half_row_pos hA4 hBge hApos
  have hhalf :
      2 * (B * (A / 2) - 1) =
        2 * (alpha * beta) + B * (alpha * l + beta * m) :=
    powerTwoSplitSubtractive_half_row_alpha_beta_identity hA2 hBge hrpos
      hspos hlpos hmpos hD hA halpha hbeta
  have hab : alpha * beta + 1 = B * B * (l * m) :=
    powerTwoSplitSubtractive_alpha_beta_mul hBge hrpos hspos hlpos hmpos hD
      hA halpha hbeta
  exact alpha_mul_dvd_iff_gcd_mul_dvd_of_split_identities hMpos hhalf hab

/-- Complete split row-two bridge: the delta divisibility appearing directly
from the quotient kernel is equivalent to the split/gcd obstruction divisor. -/
theorem powerTwoSplitSubtractive_row_two_delta_dvd_iff_gcd_dvd
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) ↔
      B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) :=
  (powerTwoSplitSubtractive_row_two_delta_dvd_iff_alpha_dvd hA4 hBge hrpos
    hspos hlpos hmpos hgap hD hA halpha).trans
    (powerTwoSplitSubtractive_row_two_alpha_dvd_iff_gcd_dvd hA4 hBge hrpos
      hspos hlpos hmpos hD hA halpha hbeta)

/-- Subtractive split row-two bridge from the `alpha` divisor directly to the
reduced divisor `M / gcd (gcd alpha beta) M`. -/
theorem powerTwoSplitSubtractive_row_two_alpha_dvd_iff_reduced_divisor
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    M ∣ (l * m) * alpha ↔ M / d ∣ l * m := by
  dsimp
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  exact
    (powerTwoSplitSubtractive_row_two_alpha_dvd_iff_gcd_dvd hA4 hBge
      hrpos hspos hlpos hmpos hD hA halpha hbeta).trans
      (powerTwoSplit_row_two_survival_iff_reduced_divisor
        (A := A) (B := B) (l := l) (m := m) (alpha := alpha)
        (beta := beta) hA4 hBge hApos)

/-- Complete split row-two bridge from the quotient-kernel delta divisor
directly to the reduced divisor `M / gcd (gcd alpha beta) M`. -/
theorem powerTwoSplitSubtractive_row_two_delta_dvd_iff_reduced_divisor
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    M ∣ (l * m) * (s * m - r * l) ↔ M / d ∣ l * m := by
  dsimp
  have hApos : 0 < A := by
    rw [← hA]
    positivity
  exact
    (powerTwoSplitSubtractive_row_two_delta_dvd_iff_gcd_dvd hA4 hBge
      hrpos hspos hlpos hmpos hgap hD hA halpha hbeta).trans
      (powerTwoSplit_row_two_survival_iff_reduced_divisor
        (A := A) (B := B) (l := l) (m := m) (alpha := alpha)
        (beta := beta) hA4 hBge hApos)

/-- Negated complete split row-two bridge: failure of the quotient-kernel
delta divisibility is exactly failure of the reduced divisor to divide
`l*m`. -/
theorem powerTwoSplitSubtractive_row_two_delta_obstruction_iff_reduced_divisor
    {A B r s l m alpha beta : ℕ}
    (hA4 : 4 ∣ A)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hgap : r * l < s * m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l) :
    let c := Nat.gcd alpha beta
    let M := B * (A / 2) - 1
    let d := Nat.gcd c M
    (¬ M ∣ (l * m) * (s * m - r * l)) ↔ ¬ M / d ∣ l * m := by
  dsimp
  have hiff :=
    powerTwoSplitSubtractive_row_two_delta_dvd_iff_reduced_divisor
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) hA4 hBge hrpos hspos hlpos hmpos
      hgap hD hA halpha hbeta
  dsimp at hiff
  constructor
  · intro h hdvd
    exact h (hiff.mpr hdvd)
  · intro h hdvd
    exact h (hiff.mp hdvd)

/-- The row-one equation in the pure power-two quotient kernel forces the
right half of the canonical divisor split:
`(B * A - 1) / gcd (B * A - 1) v` divides `A - v`. -/
theorem powerTwoQuotientKernel.row_one_split_right_dvd {A B v h : ℕ}
    (hkernel : powerTwoQuotientKernel A B v h) :
    (B * A - 1) / Nat.gcd (B * A - 1) v ∣ A - v := by
  rcases hkernel with ⟨_hA4, hApow, _hBodd, hBge, _hvpos, _hgap, hrow, _hhalf⟩
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  have hAge1 : 1 ≤ A := hApos
  have hBAge : 3 ≤ B * A := by
    have hmul : B * 1 ≤ B * A := Nat.mul_le_mul_left B hAge1
    omega
  have hDpos : 0 < B * A - 1 := by omega
  have hDvd : B * A - 1 ∣ v * (A - v) :=
    ⟨h, by rw [hrow, mul_comm]⟩
  exact dvd_div_gcd_of_dvd_mul hDpos hDvd

/-- Every pure power-two quotient-kernel point has a canonical row-one split.
This packages the row-one equation into positive factors `r, s, l, m` with
`r * s = B * A - 1`, `v = r * l`, `A - v = s * m`, the strict gap
`r * l < s * m`, and quotient `h = l * m`. -/
theorem powerTwoQuotientKernel.exists_row_one_split {A B v h : ℕ}
    (hkernel : powerTwoQuotientKernel A B v h) :
    ∃ r s l m : ℕ,
      0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
        r * s = B * A - 1 ∧
          v = r * l ∧
            A - v = s * m ∧
              r * l + s * m = A ∧
                r * l < s * m ∧
                  h = l * m := by
  rcases hkernel with ⟨hA4, hApow, hBodd, hBge, hvpos, hgap, hrow, hhalf⟩
  let D := B * A - 1
  let r := Nat.gcd D v
  let s := D / r
  let l := v / r
  let m := (A - v) / s
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  have hAge1 : 1 ≤ A := hApos
  have hBAge : 3 ≤ B * A := by
    have hmul : B * 1 ≤ B * A := Nat.mul_le_mul_left B hAge1
    omega
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hrv : r ∣ v := Nat.gcd_dvd_right D v
  have hrD : r ∣ D := Nat.gcd_dvd_left D v
  have hrpos : 0 < r := Nat.gcd_pos_of_pos_left v hDpos
  have hrs : r * s = D := by
    dsimp [s]
    exact Nat.mul_div_cancel' hrD
  have hrs_unfold : r * s = B * A - 1 := by
    simpa [D] using hrs
  have hD_unfold : B * A - 1 = r * s := hrs_unfold.symm
  have hspos : 0 < s := by
    by_contra hsnot
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hsnot
    rw [hs0, mul_zero] at hrs
    omega
  have hv_eq : v = r * l := by
    dsimp [l]
    exact (Nat.mul_div_cancel' hrv).symm
  have hs_dvd : s ∣ A - v := by
    dsimp [s, r, D]
    exact powerTwoQuotientKernel.row_one_split_right_dvd
      (A := A) (B := B) (v := v) (h := h)
      ⟨hA4, hApow, hBodd, hBge, hvpos, hgap, hrow, hhalf⟩
  have hAv_eq : A - v = s * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel' hs_dvd).symm
  have hlpos : 0 < l := by
    by_contra hlnot
    have hl0 : l = 0 := Nat.eq_zero_of_not_pos hlnot
    rw [hl0, mul_zero] at hv_eq
    omega
  have hAvpos : 0 < A - v := by omega
  have hmpos : 0 < m := by
    by_contra hmnot
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmnot
    rw [hm0, mul_zero] at hAv_eq
    omega
  have hvleA : v ≤ A := by omega
  have hsum : r * l + s * m = A := by
    have hsum0 : v + (A - v) = A := Nat.add_sub_of_le hvleA
    rw [hAv_eq, hv_eq] at hsum0
    exact hsum0
  have hsplit_gap : r * l < s * m := by
    have hv_lt_Av : v < A - v := by omega
    rw [hAv_eq, hv_eq] at hv_lt_Av
    exact hv_lt_Av
  have hrow0 := hrow
  rw [hAv_eq, hv_eq, hD_unfold] at hrow0
  have hrow_split : (r * s) * (l * m) = h * (r * s) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hrow0
  have hDsplitpos : 0 < r * s := Nat.mul_pos hrpos hspos
  have hlm_eq_h : l * m = h := by
    exact Nat.mul_left_cancel hDsplitpos (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hrow_split)
  refine ⟨r, s, l, m, hrpos, hspos, hlpos, hmpos, hrs_unfold, hv_eq, hAv_eq,
    hsum, hsplit_gap, ?_⟩
  exact hlm_eq_h.symm

/-- Row two in split coordinates. Once a quotient-kernel point is expressed
with `v = r * l`, `A - v = s * m`, and `h = l * m`, the half-row divisor is
exactly a divisor of `(l * m) * (s * m - r * l)`. -/
theorem powerTwoQuotientKernel.row_two_split_dvd {A B v h r s l m : ℕ}
    (hkernel : powerTwoQuotientKernel A B v h)
    (hv : v = r * l)
    (hAv : A - v = s * m)
    (hh : h = l * m) :
    B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) := by
  rcases hkernel with ⟨_hA4, _hApow, _hBodd, _hBge, _hvpos, _hgap, _hrow, hhalf⟩
  have hgap_eq : A - v * 2 = s * m - r * l := by omega
  simpa [hh, hgap_eq, two_mul, mul_assoc, mul_comm, mul_left_comm] using hhalf

/-- Combined row-one and row-two split package for the pure quotient kernel. -/
theorem powerTwoQuotientKernel.exists_row_one_split_with_row_two {A B v h : ℕ}
    (hkernel : powerTwoQuotientKernel A B v h) :
    ∃ r s l m : ℕ,
      0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
        r * s = B * A - 1 ∧
          v = r * l ∧
            A - v = s * m ∧
              r * l + s * m = A ∧
                r * l < s * m ∧
                  h = l * m ∧
                    B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) := by
  rcases powerTwoQuotientKernel.exists_row_one_split hkernel with
    ⟨r, s, l, m, hrpos, hspos, hlpos, hmpos, hD, hv, hAv, hsum, hgap, hh⟩
  exact ⟨r, s, l, m, hrpos, hspos, hlpos, hmpos, hD, hv, hAv, hsum, hgap, hh,
    powerTwoQuotientKernel.row_two_split_dvd hkernel hv hAv hh⟩

/-- A quotient-kernel point produces a canonical positive row-one split whose
row-two condition is exactly reduced-divisor survival. -/
theorem powerTwoQuotientKernel.exists_row_one_split_with_reduced_divisor_survival
    {A B v h : ℕ}
    (hkernel : powerTwoQuotientKernel A B v h) :
    ∃ r s l m alpha beta : ℕ,
      0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
        r * s = B * A - 1 ∧
          v = r * l ∧
            A - v = s * m ∧
              r * l + s * m = A ∧
                r * l < s * m ∧
                  h = l * m ∧
                    alpha = r - B * m ∧
                      beta = s - B * l ∧
                        let c := Nat.gcd alpha beta
                        let M := B * (A / 2) - 1
                        let d := Nat.gcd c M
                        M / d ∣ l * m := by
  rcases hkernel with
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  let hkernel' : powerTwoQuotientKernel A B v h :=
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  rcases powerTwoQuotientKernel.exists_row_one_split_with_row_two hkernel' with
    ⟨r, s, l, m, hrpos, hspos, hlpos, hmpos, hD, hv, hAv, hsum, hgap,
      hh, hrowtwo⟩
  let alpha := r - B * m
  let beta := s - B * l
  have hred :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      let d := Nat.gcd c M
      M / d ∣ l * m := by
    dsimp [alpha, beta]
    exact
      (powerTwoSplitSubtractive_row_two_delta_dvd_iff_reduced_divisor
        (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
        (alpha := r - B * m) (beta := s - B * l) hA4 hBge hrpos hspos
        hlpos hmpos hgap hD hsum rfl rfl).mp hrowtwo
  exact ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hv, hAv,
    hsum, hgap, hh, rfl, rfl, hred⟩

/-- Exact no-survivor consumer: if every admissible positive split fails the
reduced-divisor survival condition, then the quotient kernel is empty at the
pointwise level. -/
theorem powerTwoQuotientKernel.not_of_no_reduced_divisor_survival_split
    {A B v h : ℕ}
    (hnoSurvivor :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  let d := Nat.gcd c M
                                  ¬ M / d ∣ l * m) :
    ¬ powerTwoQuotientKernel A B v h := by
  intro hkernel
  rcases hkernel with
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  let hkernel' : powerTwoQuotientKernel A B v h :=
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  rcases
    powerTwoQuotientKernel.exists_row_one_split_with_reduced_divisor_survival
      hkernel' with
    ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, _hv, _hAv,
      hsum, hgap, _hh, halpha, hbeta, hred⟩
  exact
    (hnoSurvivor hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
      hlpos hmpos hD hsum hgap halpha hbeta) hred

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_no_reduced_divisor_survival_split`. -/
theorem not_exists_powerTwoQuotientKernel_of_no_reduced_divisor_survival_split
    {A B : ℕ}
    (hnoSurvivor :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  let d := Nat.gcd c M
                                  ¬ M / d ∣ l * m) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_no_reduced_divisor_survival_split
      hnoSurvivor hkernel

/-- Nonunitary reduced-gcd consumer: if every admissible split captures a
nonunitary part of the half-row modulus, then the quotient kernel is empty at
the pointwise level. -/
theorem powerTwoQuotientKernel.not_of_nonunitary_reduced_gcd_split
    {A B v h : ℕ}
    (hnonunitary :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  let d := Nat.gcd c M
                                  ¬ d.Coprime (M / d)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_no_reduced_divisor_survival_split
    (fun hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos hlpos hmpos
        hD hsum hgap halpha hbeta =>
      powerTwoSplitSubtractive_not_reduced_divisor_survival_of_not_unitary_gcd
        hBge hrpos hspos hlpos hmpos hD hsum halpha hbeta
        (hnonunitary hApow hA4 hBodd hBge r s l m alpha beta hrpos hspos
          hlpos hmpos hD hsum hgap halpha hbeta))

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_nonunitary_reduced_gcd_split`. -/
theorem not_exists_powerTwoQuotientKernel_of_nonunitary_reduced_gcd_split
    {A B : ℕ}
    (hnonunitary :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  let d := Nat.gcd c M
                                  ¬ d.Coprime (M / d)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_nonunitary_reduced_gcd_split
      hnonunitary hkernel

/-- Converse reduced-divisor constructor: an admissible positive split whose
reduced divisor survives row two gives an actual pure power-two quotient-kernel
point. This is the reverse direction of the C2 reduction; it does not assert
that such a split exists. -/
theorem powerTwoQuotientKernel_of_reduced_divisor_survival_split
    {A B r s l m alpha beta : ℕ}
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B)
    (hrpos : 0 < r)
    (hspos : 0 < s)
    (hlpos : 0 < l)
    (hmpos : 0 < m)
    (hD : r * s = B * A - 1)
    (hA : r * l + s * m = A)
    (hgap : r * l < s * m)
    (halpha : alpha = r - B * m)
    (hbeta : beta = s - B * l)
    (hred :
      let c := Nat.gcd alpha beta
      let M := B * (A / 2) - 1
      let d := Nat.gcd c M
      M / d ∣ l * m) :
    powerTwoQuotientKernel A B (r * l) (l * m) := by
  have hvpos : 0 < r * l := Nat.mul_pos hrpos hlpos
  have hgap_kernel : 0 < A - 2 * (r * l) := by
    rw [← hA]
    omega
  have hAv : A - r * l = s * m := by
    rw [← hA]
    omega
  have hdelta : A - r * (l * 2) = s * m - r * l := by
    rw [← hA]
    have htwor : r * (l * 2) = r * l + r * l := by ring
    rw [htwor]
    omega
  have hrow : (r * l) * (A - r * l) = (l * m) * (B * A - 1) := by
    rw [hAv, ← hD]
    ring
  have hrowtwo_split :
      B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) := by
    exact
      (powerTwoSplitSubtractive_row_two_delta_dvd_iff_reduced_divisor
        (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
        (alpha := alpha) (beta := beta) hA4 hBge hrpos hspos hlpos hmpos
        hgap hD hA halpha hbeta).mpr hred
  have hhalf :
      B * (A / 2) - 1 ∣ (l * m) * (A - 2 * (r * l)) := by
    simpa [hdelta, mul_assoc, mul_comm, mul_left_comm] using hrowtwo_split
  exact ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩

/-- Existence-level form of the C2 reduced-divisor bridge: under the global
power-of-two and odd-row hypotheses, pure quotient-kernel points are exactly
surviving admissible positive splits. The open obstruction is therefore the
non-existence of the right-hand side. -/
theorem exists_powerTwoQuotientKernel_iff_exists_reduced_divisor_survival_split
    {A B : ℕ}
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B) :
    (∃ v h : ℕ, powerTwoQuotientKernel A B v h) ↔
      ∃ r s l m alpha beta : ℕ,
        0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
          r * s = B * A - 1 ∧
            r * l + s * m = A ∧
              r * l < s * m ∧
                alpha = r - B * m ∧
                  beta = s - B * l ∧
                    let c := Nat.gcd alpha beta
                    let M := B * (A / 2) - 1
                    let d := Nat.gcd c M
                    M / d ∣ l * m := by
  constructor
  · rintro ⟨v, h, hkernel⟩
    rcases
      powerTwoQuotientKernel.exists_row_one_split_with_reduced_divisor_survival
        hkernel with
      ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, _hv, _hAv,
        hsum, hgap, _hh, halpha, hbeta, hred⟩
    exact ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum,
      hgap, halpha, hbeta, hred⟩
  · rintro
      ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum, hgap,
        halpha, hbeta, hred⟩
    exact
      ⟨r * l, l * m,
        powerTwoQuotientKernel_of_reduced_divisor_survival_split
          hApow hA4 hBodd hBge hrpos hspos hlpos hmpos hD hsum hgap
          halpha hbeta hred⟩

/-- Coprime-refined existence-level C2 bridge. The extra coprimality condition
is automatic from the split product identity, but recording it here matches
the exact reduced-divisor obstruction used in the C2 analysis. -/
theorem exists_powerTwoQuotientKernel_iff_exists_reduced_divisor_survival_coprime_split
    {A B : ℕ}
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hA4 : 4 ∣ A)
    (hBodd : Odd B)
    (hBge : 3 ≤ B) :
    (∃ v h : ℕ, powerTwoQuotientKernel A B v h) ↔
      ∃ r s l m alpha beta : ℕ,
        0 < r ∧ 0 < s ∧ 0 < l ∧ 0 < m ∧
          r * s = B * A - 1 ∧
            r * l + s * m = A ∧
              r * l < s * m ∧
                alpha = r - B * m ∧
                  beta = s - B * l ∧
                    (Nat.gcd alpha beta).Coprime (l * m) ∧
                      let c := Nat.gcd alpha beta
                      let M := B * (A / 2) - 1
                      let d := Nat.gcd c M
                      M / d ∣ l * m := by
  constructor
  · intro hkernel_exists
    rcases
      (exists_powerTwoQuotientKernel_iff_exists_reduced_divisor_survival_split
        hApow hA4 hBodd hBge).mp hkernel_exists with
      ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum, hgap,
        halpha, hbeta, hred⟩
    have hcop : (Nat.gcd alpha beta).Coprime (l * m) :=
      powerTwoSplitSubtractive_gcd_alpha_beta_coprime_l_mul_m hBge hrpos
        hspos hlpos hmpos hD hsum halpha hbeta
    exact ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum,
      hgap, halpha, hbeta, hcop, hred⟩
  · rintro
      ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum, hgap,
        halpha, hbeta, _hcop, hred⟩
    exact
      (exists_powerTwoQuotientKernel_iff_exists_reduced_divisor_survival_split
        hApow hA4 hBodd hBge).mpr
        ⟨r, s, l, m, alpha, beta, hrpos, hspos, hlpos, hmpos, hD, hsum, hgap,
          halpha, hbeta, hred⟩

/-- Conditional consumer for the split/gcd obstruction: once
`powerTwoSplitGcdObstruction A B` is supplied, the pure power-two quotient
kernel is empty for that `A, B`. This does not prove the obstruction itself;
it proves that the current split/gcd target is exactly strong enough to kill
the quotient kernel. -/
theorem powerTwoQuotientKernel.not_of_splitGcdObstruction {A B v h : ℕ}
    (hobs : powerTwoSplitGcdObstruction A B) :
    ¬ powerTwoQuotientKernel A B v h := by
  intro hkernel
  rcases hkernel with
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  let hkernel' : powerTwoQuotientKernel A B v h :=
    ⟨hA4, hApow, hBodd, hBge, hvpos, hgap_kernel, hrow, hhalf⟩
  rcases powerTwoQuotientKernel.exists_row_one_split_with_row_two hkernel' with
    ⟨r, s, l, m, hrpos, hspos, hlpos, hmpos, hD, _hv, _hAv, hsum, hgap,
      _hh, hrowtwo⟩
  let alpha := r - B * m
  let beta := s - B * l
  have hrowtwo_gcd :
      B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m) := by
    exact
      (powerTwoSplitSubtractive_row_two_delta_dvd_iff_gcd_dvd
        (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
        (alpha := alpha) (beta := beta) hA4 hBge hrpos hspos hlpos hmpos
        hgap hD hsum rfl rfl).mp hrowtwo
  exact
    (powerTwoSplitGcdObstruction.not_dvd
      (A := A) (B := B) (r := r) (s := s) (l := l) (m := m)
      (alpha := alpha) (beta := beta) (c := Nat.gcd alpha beta)
      hobs hApow hA4 hBodd hBge hrpos hspos hlpos hmpos hD hsum hgap
      rfl rfl rfl) hrowtwo_gcd

/-- Direct conditional kernel kill from the reduced-divisor gap inequality.
This is the composed current endpoint of the split/gcd reductions: proving
the stated inequality for all admissible positive splits would eliminate the
pure power-two quotient kernel for the fixed `A, B`. -/
theorem powerTwoQuotientKernel.not_of_reduced_divisor_gap {A B v h : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  l * m <
                                    (B * (A / 2) - 1) /
                                      Nat.gcd (Nat.gcd alpha beta)
                                        (B * (A / 2) - 1)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_reduced_divisor_gap hgapAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_reduced_divisor_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_reduced_divisor_gap {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  l * m <
                                    (B * (A / 2) - 1) /
                                      Nat.gcd (Nat.gcd alpha beta)
                                        (B * (A / 2) - 1)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_reduced_divisor_gap hgapAll hkernel

/-- Direct conditional kernel kill from the canonical linear inequality, routed
through the exact reduced-divisor gap. This is propositionally the same
endpoint as `powerTwoQuotientKernel.not_of_canonical_gcd_linear_ineq`, but it
keeps the proof path aligned with the sharp condition
`l*m < M / gcd(c,M)`. -/
theorem powerTwoQuotientKernel.not_of_canonical_linear_via_reduced_gap
    {A B v h : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_reduced_divisor_gap
    (powerTwoSplit_all_reduced_divisor_gap_of_canonical_gcd_linear_ineq hlinAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_linear_via_reduced_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_linear_via_reduced_gap
    {A B : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_canonical_linear_via_reduced_gap
      hlinAll hkernel

/-- Direct conditional kernel kill from the canonical ceiling-scaled
deficit branch, routed through the exact reduced-divisor gap. This exposes the
current computable C2 condition at the sharp row-two obstruction. -/
theorem powerTwoQuotientKernel.not_of_canonical_ceil_scaled_via_reduced_gap
    {A B v h : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_reduced_divisor_gap
    (powerTwoSplit_all_reduced_divisor_gap_of_canonical_gcd_ceil_scaled_deficit_coverage
      hcoverAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_ceil_scaled_via_reduced_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_ceil_scaled_via_reduced_gap
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_canonical_ceil_scaled_via_reduced_gap
      hcoverAll hkernel

/-- Direct conditional kernel kill from the parity-branch gap inequality. -/
theorem powerTwoQuotientKernel.not_of_parity_reduced_divisor_gap {A B v h : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ l * m < M / c) ∨
                                    (Even c ∧ l * m < M / (c / 2))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_parity_reduced_divisor_gap hgapAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_parity_reduced_divisor_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_parity_reduced_divisor_gap
    {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ l * m < M / c) ∨
                                    (Even c ∧ l * m < M / (c / 2))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_parity_reduced_divisor_gap hgapAll hkernel

/-- Direct conditional kernel kill from the product-form parity gap. -/
theorem powerTwoQuotientKernel.not_of_parity_product_gap {A B v h : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ c * (l * m + 1) ≤ M) ∨
                                    (Even c ∧ (c / 2) * (l * m + 1) ≤ M)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_parity_product_gap hgapAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_parity_product_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_parity_product_gap
    {A B : ℕ}
    (hgapAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c ∧ c * (l * m + 1) ≤ M) ∨
                                    (Even c ∧ (c / 2) * (l * m + 1) ≤ M)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_parity_product_gap hgapAll hkernel

/-- Direct conditional kernel kill from the large-denominator-only
product-form parity target. The small parity-denominator branches are already
handled by `powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq`. -/
theorem powerTwoQuotientKernel.not_of_large_parity_denominator_product_gap
    {A B v h : ℕ}
    (hlargeAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c → B * B < c →
                                    c * (l * m + 1) ≤ M) ∧
                                  (Even c → B * B < c / 2 →
                                    (c / 2) * (l * m + 1) ≤ M)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_large_parity_denominator_product_gap
      hlargeAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_large_parity_denominator_product_gap`. -/
theorem not_exists_powerTwoQuotientKernel_of_large_parity_denominator_product_gap
    {A B : ℕ}
    (hlargeAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let M := B * (A / 2) - 1
                                  (Odd c → B * B < c →
                                    c * (l * m + 1) ≤ M) ∧
                                  (Even c → B * B < c / 2 →
                                    (c / 2) * (l * m + 1) ≤ M)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_large_parity_denominator_product_gap
      hlargeAll hkernel

/-- Direct conditional kernel kill from the normalized gcd-quotient
inequality. -/
theorem powerTwoQuotientKernel.not_of_gcd_quotient_ineq
    {A B v h : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  ∃ x y : ℕ,
                                    alpha = c * x ∧
                                      beta = c * y ∧
                                        ((Odd c ∧
                                            2 * (l * m + 1) ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)) ∨
                                          (Even c ∧
                                            l * m + 1 ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_gcd_quotient_ineq hquotAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_gcd_quotient_ineq`. -/
theorem not_exists_powerTwoQuotientKernel_of_gcd_quotient_ineq
    {A B : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  ∃ x y : ℕ,
                                    alpha = c * x ∧
                                      beta = c * y ∧
                                        ((Odd c ∧
                                            2 * (l * m + 1) ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)) ∨
                                          (Even c ∧
                                            l * m + 1 ≤
                                              2 * c * (x * y) +
                                                B * (x * l + y * m)))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_gcd_quotient_ineq hquotAll hkernel

/-- Direct conditional kernel kill from the canonical normalized gcd-quotient
inequality. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_quotient_ineq
    {A B v h : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_quotient_ineq hquotAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_quotient_ineq`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_quotient_ineq
    {A B : ℕ}
    (hquotAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        2 * c * (x * y) +
                                          B * (x * l + y * m))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact
    powerTwoQuotientKernel.not_of_canonical_gcd_quotient_ineq hquotAll hkernel

/-- Direct conditional kernel kill from the stronger canonical linear
normalized gcd-quotient inequality. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_linear_ineq
    {A B v h : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq hlinAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_linear_ineq`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_linear_ineq
    {A B : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        B * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        B * (x * l + y * m))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_linear_ineq hlinAll hkernel

/-- Direct conditional kernel kill from the canonical deficit-compensation
target equivalent to the stronger canonical linear inequality. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_deficit_ineq
    {A B v h : ℕ}
    (hdefAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      m * (2 * l - B * y) + 2 ≤
                                        B * x * l) ∨
                                    (Even c ∧
                                      m * (l - B * y) + 1 ≤
                                        B * x * l)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_deficit_ineq hdefAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_deficit_ineq`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_deficit_ineq
    {A B : ℕ}
    (hdefAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      m * (2 * l - B * y) + 2 ≤
                                        B * x * l) ∨
                                    (Even c ∧
                                      m * (l - B * y) + 1 ≤
                                        B * x * l)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_deficit_ineq hdefAll hkernel

/-- Direct conditional kernel kill from the automatic canonical y-coverage
branch. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_y_coverage
    {A B v h : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let y := beta / c
                                  (Odd c ∧ 2 * l ≤ B * y) ∨
                                    (Even c ∧ l ≤ B * y)) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_y_coverage hcoverAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_y_coverage`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_y_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let y := beta / c
                                  (Odd c ∧ 2 * l ≤ B * y) ∨
                                    (Even c ∧ l ≤ B * y)) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_y_coverage hcoverAll hkernel

/-- Direct conditional kernel kill from the canonical y-or-x branch. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_y_or_x_coverage
    {A B v h : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        (l < B * y ∧ m ≤ B * x))) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨ m ≤ B * x))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_y_or_x_coverage hcoverAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_y_or_x_coverage`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_y_or_x_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        (l < B * y ∧ m ≤ B * x))) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨ m ≤ B * x))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_y_or_x_coverage hcoverAll
    hkernel

/-- Direct conditional kernel kill from the canonical scaled-deficit branch. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_scaled_deficit_coverage
    {A B v h : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (l - B * y) < l))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_scaled_deficit_coverage
      hcoverAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_scaled_deficit_coverage`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_scaled_deficit_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ∃ q : ℕ,
                                          m ≤ q * (B * x) ∧
                                            q * (l - B * y) < l))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_scaled_deficit_coverage
    hcoverAll hkernel

/-- Direct conditional kernel kill from the canonical ceiling-scaled
gcd-deficit branch. -/
theorem powerTwoQuotientKernel.not_of_canonical_gcd_ceil_scaled_deficit_coverage
    {A B v h : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
    ¬ powerTwoQuotientKernel A B v h :=
  powerTwoQuotientKernel.not_of_splitGcdObstruction
    (powerTwoSplitGcdObstruction_of_canonical_gcd_ceil_scaled_deficit_coverage
      hcoverAll)

/-- Existence-free version of
`powerTwoQuotientKernel.not_of_canonical_gcd_ceil_scaled_deficit_coverage`. -/
theorem not_exists_powerTwoQuotientKernel_of_canonical_gcd_ceil_scaled_deficit_coverage
    {A B : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd B →
            3 ≤ B →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = B * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - B * m →
                                beta = s - B * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (2 * l - B * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ B * y ∨
                                        ((m - 1) / (B * x) + 1) *
                                            (l - B * y) < l))) :
    ¬ ∃ v h : ℕ, powerTwoQuotientKernel A B v h := by
  rintro ⟨v, h, hkernel⟩
  exact powerTwoQuotientKernel.not_of_canonical_gcd_ceil_scaled_deficit_coverage
    hcoverAll hkernel

/-- Quotient the corrected squeezed normalized kernel by an odd digit-forced
factor `H`. This formalizes the algebraic part of the reduction to the pure
power-of-two quotient kernel: once `X = A * H`, `u = H * v`, `g = H^2 * h`,
and the half-row modulus is coprime to `H`, any squeezed kernel point yields a
`powerTwoQuotientKernel` point for `A` and `F * H`. -/
theorem powerTwoQuotientKernel_of_squeezedNormalized_decomposition
    {F X u g A H v h : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hX : X = A * H)
    (hu : u = H * v)
    (hg : g = H * H * h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hcopHalf : Nat.Coprime H (F * H * (A / 2) - 1)) :
    powerTwoQuotientKernel A (F * H) v h := by
  rcases hkernel with
    ⟨_hFpos, _hXpos, hupos, hFodd, _h4X, hFge, h2u_lt, _h4F, _h2F2,
      hrow, hhalf⟩
  have hHpos : 0 < H := hHodd.pos
  have hBodd : Odd (F * H) := hFodd.mul hHodd
  have hBge : 3 ≤ F * H := by
    exact le_trans hFge (Nat.le_mul_of_pos_right F hHpos)
  have h2v_lt_A : 2 * v < A := by
    have hmul : H * (2 * v) < H * A := by
      simpa [hu, hX, mul_assoc, mul_comm, mul_left_comm] using h2u_lt
    exact (Nat.mul_lt_mul_left hHpos).mp hmul
  have hgap : 0 < A - 2 * v := by omega
  have hvpos : 0 < v := by
    by_contra hv
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv
    subst v
    simp at hu
    omega
  have hv_le_A : v ≤ A := by omega
  have hsub_u : X - u = H * (A - v) := by
    rw [hX, hu]
    rw [mul_comm A H]
    exact (Nat.mul_sub_left_distrib H A v).symm
  have hsub_gap : X - 2 * u = H * (A - 2 * v) := by
    rw [hX, hu]
    have hleft : 2 * (H * v) = H * (2 * v) := by ring
    rw [hleft]
    rw [mul_comm A H]
    exact (Nat.mul_sub_left_distrib H A (2 * v)).symm
  have hhalf_eq : F * X / 2 - 1 = F * H * (A / 2) - 1 := by
    rcases hA4 with ⟨c, hc⟩
    subst A
    rw [hX]
    have h4c : 4 * c / 2 = 2 * c := by
      calc
        4 * c / 2 = (2 * (2 * c)) / 2 := by ring_nf
        _ = 2 * c := Nat.mul_div_right (2 * c) (by decide : 0 < 2)
    have hdiv : F * (4 * c * H) / 2 = F * H * (2 * c) := by
      calc
        F * (4 * c * H) / 2 = (2 * (F * H * (2 * c))) / 2 := by ring_nf
        _ = F * H * (2 * c) :=
            Nat.mul_div_right (F * H * (2 * c)) (by decide : 0 < 2)
    rw [hdiv, h4c]
  have hrow_subst :
      (H * v) * (H * (A - v)) = (H * H * h) * (F * (A * H) - 1) := by
    have hrow' := hrow
    rw [hsub_u, hu, hg, hX] at hrow'
    exact hrow'
  have hrow_scaled :
      H * H * (v * (A - v)) = H * H * (h * (F * H * A - 1)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hrow_subst
  have hHHpos : 0 < H * H := Nat.mul_pos hHpos hHpos
  have hrow_reduced : v * (A - v) = h * (F * H * A - 1) := by
    exact Nat.mul_left_cancel hHHpos hrow_scaled
  have hrow_reduced' : v * (A - v) = h * ((F * H) * A - 1) := by
    simpa [mul_assoc] using hrow_reduced
  have hhalf_scaled :
      F * H * (A / 2) - 1 ∣ H * (H * (H * (h * (A - 2 * v)))) := by
    have hhalf_subst :
        F * H * (A / 2) - 1 ∣ (H * H * h) * (H * (A - 2 * v)) := by
      simpa [hhalf_eq, hg, hsub_gap] using hhalf
    convert hhalf_subst using 1
    ring
  have hcopM : Nat.Coprime (F * H * (A / 2) - 1) H := hcopHalf.symm
  have hdvd1 : F * H * (A / 2) - 1 ∣ H * (H * (h * (A - 2 * v))) :=
    hcopM.dvd_of_dvd_mul_left hhalf_scaled
  have hdvd2 : F * H * (A / 2) - 1 ∣ H * (h * (A - 2 * v)) :=
    hcopM.dvd_of_dvd_mul_left hdvd1
  have hdvd3 : F * H * (A / 2) - 1 ∣ h * (A - 2 * v) :=
    hcopM.dvd_of_dvd_mul_left hdvd2
  refine ⟨hA4, hApow, hBodd, hBge, hvpos, hgap, ?_, ?_⟩
  · simpa using hrow_reduced'
  · simpa [mul_assoc] using hdvd3

/-- Existential quotient form of
`powerTwoQuotientKernel_of_squeezedNormalized_decomposition`: row-one
coprimality forces `H^2 ∣ g`, so the quotient `h` exists. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_decomposition
    {F X u g A H v : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hX : X = A * H)
    (hu : u = H * v)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hcopRow : Nat.Coprime H (F * H * A - 1))
    (hcopHalf : Nat.Coprime H (F * H * (A / 2) - 1)) :
    ∃ h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  have hkernel' := hkernel
  rcases hkernel with
    ⟨_hFpos, _hXpos, _hupos, _hFodd, _h4X, _hFge, _h2u_lt, _h4F, _h2F2,
      hrow, _hhalf⟩
  have hsub_u : X - u = H * (A - v) := by
    rw [hX, hu]
    rw [mul_comm A H]
    exact (Nat.mul_sub_left_distrib H A v).symm
  have hrow_subst :
      (H * v) * (H * (A - v)) = g * (F * (A * H) - 1) := by
    have hrow' := hrow
    rw [hsub_u, hu, hX] at hrow'
    exact hrow'
  have hrow_scaled : H * H * (v * (A - v)) = g * (F * H * A - 1) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hrow_subst
  have hH2_dvd_gD : H * H ∣ g * (F * H * A - 1) := by
    rw [← hrow_scaled]
    exact Nat.dvd_mul_right (H * H) (v * (A - v))
  have hcopH2D : Nat.Coprime (H * H) (F * H * A - 1) :=
    hcopRow.mul_left hcopRow
  have hH2_dvd_g : H * H ∣ g :=
    hcopH2D.dvd_of_dvd_mul_right hH2_dvd_gD
  rcases hH2_dvd_g with ⟨h, hg⟩
  exact ⟨h,
    powerTwoQuotientKernel_of_squeezedNormalized_decomposition
      hkernel' hX hu hg hA4 hApow hHodd hcopHalf⟩

/-- A positive factor is coprime to one less than a positive multiple of it. -/
theorem coprime_left_mul_right_sub_one {H K : ℕ} (hH : 0 < H) (hK : 0 < K) :
    Nat.Coprime H (K * H - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_one
  let d := Nat.gcd H (K * H - 1)
  have hdH : d ∣ H := Nat.gcd_dvd_left H (K * H - 1)
  have hdM : d ∣ K * H - 1 := Nat.gcd_dvd_right H (K * H - 1)
  have hdKH : d ∣ K * H := Nat.dvd_mul_left_of_dvd hdH K
  have hsub : K * H - (K * H - 1) = 1 := by
    have hKH : 0 < K * H := Nat.mul_pos hK hH
    omega
  have hdsub : d ∣ K * H - (K * H - 1) := Nat.dvd_sub hdKH hdM
  simpa [d, hsub] using hdsub

/-- Version of the quotient reduction with the natural digit-factor output
`H ∣ u`. The coprimality hypotheses in
`exists_powerTwoQuotientKernel_of_squeezedNormalized_decomposition` are
automatic because both row moduli are one less than positive multiples of
`H`. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_factor_dvd
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hX : X = A * H)
    (hHu : H ∣ u)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  rcases hHu with ⟨v, hu⟩
  have hFpos : 0 < F := hkernel.1
  have hHpos : 0 < H := hHodd.pos
  have hApos : 0 < A := by
    rcases hApow with ⟨a, rfl⟩
    exact Nat.pow_pos (by decide : 0 < 2)
  have hAhalfpos : 0 < A / 2 := by
    have hAge4 : 4 ≤ A := Nat.le_of_dvd hApos hA4
    exact Nat.div_pos (by omega : 2 ≤ A) (by decide : 0 < 2)
  have hcopRow : Nat.Coprime H (F * H * A - 1) := by
    have hKpos : 0 < F * A := Nat.mul_pos hFpos hApos
    have hcop :=
      coprime_left_mul_right_sub_one (H := H) (K := F * A) hHpos hKpos
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcop
  have hcopHalf : Nat.Coprime H (F * H * (A / 2) - 1) := by
    have hKpos : 0 < F * (A / 2) := Nat.mul_pos hFpos hAhalfpos
    have hcop :=
      coprime_left_mul_right_sub_one (H := H) (K := F * (A / 2)) hHpos hKpos
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcop
  rcases exists_powerTwoQuotientKernel_of_squeezedNormalized_decomposition
      hkernel hX hu hA4 hApow hHodd hcopRow hcopHalf with
    ⟨h, hq⟩
  exact ⟨v, h, hq⟩

/-- Combine the row-`n` digit-power extraction with the quotient-kernel
bridge in the all-odd-prime-powers-forced branch. If `X = A * H` with odd
`H`, and `A` is the power-of-two quotient, then a squeezed normalized kernel
point yields a pure `powerTwoQuotientKernel` point. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigit_factor
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hrow : rowNDigitPowerConstraint X u)
    (hX : X = A * H)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  have hH0 : H ≠ 0 := ne_of_gt hHodd.pos
  have hHX : H ∣ X := by
    refine ⟨A, ?_⟩
    rw [hX, mul_comm]
  have hHu : H ∣ u := hrow.dvd_of_factor_dvd hHX hH0
    (fun p hp hpd => odd_prime_divisor_ge_three hHodd hp hpd)
  exact exists_powerTwoQuotientKernel_of_squeezedNormalized_factor_dvd
    hkernel hX hHu hA4 hApow hHodd

/-- Exact guarded version of
`exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigit_factor`. The
factor `H` is extracted only when each prime divisor of `H` is relevant for
row `3`, i.e. satisfies `¬ dominated 3 (F*X) p`. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigitExact_factor
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hrow : rowNDigitPowerConstraintExact F X u)
    (hX : X = A * H)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 (F * X) p) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  have hH0 : H ≠ 0 := ne_of_gt hHodd.pos
  have hHX : H ∣ X := by
    refine ⟨A, ?_⟩
    rw [hX, mul_comm]
  have hHu : H ∣ u :=
    hrow.dvd_of_factor_dvd hHX hH0 hprime
  exact exists_powerTwoQuotientKernel_of_squeezedNormalized_factor_dvd
    hkernel hX hHu hA4 hApow hHodd

/-- Contrapositive bridge from the quotient kernel back to the squeezed
normalized kernel. If the pure power-two quotient kernel is empty for
`A, F*H`, then no squeezed normalized point with the row-`n` digit-power
factor condition exists at `X = A*H`. -/
theorem not_exists_squeezedNormalized_rowNDigit_factor_of_no_powerTwoQuotientKernel
    {F A H : ℕ}
    (hno : ¬ ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraint (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  rintro ⟨u, g, hrow, hkernel⟩
  exact hno
    (exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigit_factor
      hkernel hrow rfl hA4 hApow hHodd)

/-- Exact guarded contrapositive bridge from the quotient kernel back to the
squeezed normalized kernel. The only digit-transfer hypothesis is the guarded
`rowNDigitPowerConstraintExact`, so primes below the row or dominated by row
`3` remain unconstrained. -/
theorem not_exists_squeezedNormalized_rowNDigitExact_factor_of_no_powerTwoQuotientKernel
    {F A H : ℕ}
    (hno : ¬ ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraintExact F (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  rintro ⟨u, g, hrow, hkernel⟩
  exact hno
    (exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigitExact_factor
      hkernel hrow rfl hA4 hApow hHodd hprime)

/-- Squeezed normalized no-kernel bridge from the canonical linear C2
hypothesis, routed through the exact reduced-divisor quotient-kernel kill. -/
theorem not_exists_squeezedNormalized_rowNDigit_factor_of_canonical_linear
    {F A H : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        F * H * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        F * H * (x * l + y * m)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraint (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_rowNDigit_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_linear_via_reduced_gap
        (A := A) (B := F * H) hlinAll)
      hA4 hApow hHodd

/-- Squeezed normalized no-kernel bridge from the canonical ceiling-scaled C2
hypothesis, routed through the exact reduced-divisor quotient-kernel kill. -/
theorem not_exists_squeezedNormalized_rowNDigit_factor_of_canonical_ceil_scaled
    {F A H : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (2 * l - F * H * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (l - F * H * y) < l)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraint (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_rowNDigit_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_ceil_scaled_via_reduced_gap
        (A := A) (B := F * H) hcoverAll)
      hA4 hApow hHodd

/-- Exact guarded squeezed-normalized no-kernel bridge from the canonical
linear C2 hypothesis. This is the sharp version with the Lucas guard in the
digit-factor hypothesis. -/
theorem not_exists_squeezedNormalized_rowNDigitExact_factor_of_canonical_linear
    {F A H : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        F * H * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        F * H * (x * l + y * m)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraintExact F (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_rowNDigitExact_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_linear_via_reduced_gap
        (A := A) (B := F * H) hlinAll)
      hA4 hApow hHodd hprime

/-- Exact guarded squeezed-normalized no-kernel bridge from the canonical
ceiling-scaled C2 hypothesis. This keeps the formal target aligned with the
correct Lucas guard and the exact reduced-divisor quotient obstruction. -/
theorem not_exists_squeezedNormalized_rowNDigitExact_factor_of_canonical_ceil_scaled
    {F A H : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (2 * l - F * H * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (l - F * H * y) < l)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p) :
    ¬ ∃ u g : ℕ,
      rowNDigitPowerConstraintExact F (A * H) u ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_rowNDigitExact_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_ceil_scaled_via_reduced_gap
        (A := A) (B := F * H) hcoverAll)
      hA4 hApow hHodd hprime

theorem squeezedNormalizedCaseIKernel_zero_t_false {F X g : ℕ} :
    ¬ squeezedNormalizedCaseIKernel F X 0 g := by
  intro h
  exact Nat.lt_irrefl 0 h.2.2.1

theorem squeezedNormalizedRowOneCandidate_zero_t_false {F X g : ℕ} :
    ¬ squeezedNormalizedRowOneCandidate F X 0 g := by
  intro h
  exact Nat.lt_irrefl 0 h.2.2.1

/-- The normalized squeezed kernel is not globally empty, even with `0 < t`. -/
theorem squeezedNormalizedCaseIKernel_counterexample_positive_t :
    squeezedNormalizedCaseIKernel 3 432184014644 186954166997 35360510289 := by
  unfold squeezedNormalizedCaseIKernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨1, by norm_num⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem exists_squeezedNormalizedCaseIKernel_counterexample_positive_t :
    ∃ F X t g : ℕ, squeezedNormalizedCaseIKernel F X t g :=
  ⟨3, 432184014644, 186954166997, 35360510289,
    squeezedNormalizedCaseIKernel_counterexample_positive_t⟩

theorem squeezedNormalizedCounterexample_not_rowNDigitPowerConstraint :
    ¬ rowNDigitPowerConstraint 432184014644 186954166997 := by
  exact
    not_rowNDigitPowerConstraint_of_prime_power_counterexample
      (X := 432184014644) (u := 186954166997) (p := 179) (e := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem squeezedNormalizedCounterexample_commonPrimeDivisor_five :
    commonPrimeDivisor 1296552043932 3 560862500991 5 := by
  refine ⟨by decide, by norm_num, ?_, ?_⟩
  · apply prime_dvd_choose_of_not_dominated (by decide : Nat.Prime 5)
    intro hdom
    have hdigits := (dominated_iff_forall_digits (by norm_num : 2 ≤ 5)).mp hdom 0
    norm_num [digit] at hdigits
  · apply prime_dvd_choose_of_not_dominated (by decide : Nat.Prime 5)
    intro hdom
    have hdigits := (dominated_iff_forall_digits (by norm_num : 2 ≤ 5)).mp hdom 1
    norm_num [digit] at hdigits

theorem squeezedNormalizedCounterexample_commonPrimeDivisor_eleven :
    commonPrimeDivisor 1296552043932 3 560862500991 11 := by
  exact commonPrimeDivisor_of_digit_failures
    (n := 1296552043932) (i := 3) (j := 560862500991)
    (p := 11) (ri := 0) (rj := 1)
    (by decide) (by norm_num) (by norm_num [digit]) (by norm_num [digit])

theorem squeezedNormalizedCounterexample_exists_commonPrimeDivisor :
    ∃ p : ℕ, commonPrimeDivisor 1296552043932 3 560862500991 p :=
  ⟨5, squeezedNormalizedCounterexample_commonPrimeDivisor_five⟩

theorem squeezedNormalizedRowOneCandidate_half_row_pos {F X t g : ℕ}
    (h : squeezedNormalizedRowOneCandidate F X t g) :
    0 < F * X / 2 - 1 := by
  rcases h with
    ⟨_hF_pos, hX_pos, _ht_pos, _hFodd, h4X, hF_ge, _h2t_lt, _h4F, _h2F2,
      _hrow⟩
  rcases h4X with ⟨a, ha⟩
  have ha_pos : 0 < a := by
    rw [ha] at hX_pos
    omega
  rw [ha]
  have hdiv : F * (4 * a) / 2 = F * (2 * a) := by
    calc
      F * (4 * a) / 2 = 2 * (F * (2 * a)) / 2 := by ring_nf
      _ = F * (2 * a) := Nat.mul_div_right (F * (2 * a)) (by decide : 0 < 2)
  rw [hdiv]
  have htwoa : 2 ≤ 2 * a := by omega
  have hprod : 6 ≤ F * (2 * a) := by
    simpa using Nat.mul_le_mul hF_ge htwoa
  omega

theorem squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_dvd
    {F X t g : ℕ} :
    squeezedNormalizedCaseIKernel F X t g ↔
      squeezedNormalizedRowOneCandidate F X t g ∧
        F * X / 2 - 1 ∣ g * (X - 2 * t) := by
  simp [squeezedNormalizedCaseIKernel, squeezedNormalizedRowOneCandidate, and_assoc]

theorem squeezedNormalizedRowOneCandidate_halfRow_dvd_iff_gcd_eq {F X t g : ℕ}
    (_hrow : squeezedNormalizedRowOneCandidate F X t g) :
    (F * X / 2 - 1 ∣ g * (X - 2 * t)) ↔
      Nat.gcd (g * (X - 2 * t)) (F * X / 2 - 1) = F * X / 2 - 1 := by
  constructor
  · intro hdvd
    exact Nat.gcd_eq_right hdvd
  · intro hgcd
    rw [← hgcd]
    exact Nat.gcd_dvd_left (g * (X - 2 * t)) (F * X / 2 - 1)

theorem squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq
    {F X t g : ℕ} :
    squeezedNormalizedCaseIKernel F X t g ↔
      squeezedNormalizedRowOneCandidate F X t g ∧
        Nat.gcd (g * (X - 2 * t)) (F * X / 2 - 1) = F * X / 2 - 1 := by
  rw [squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_dvd]
  constructor
  · rintro ⟨hrow, hdvd⟩
    exact ⟨hrow, (squeezedNormalizedRowOneCandidate_halfRow_dvd_iff_gcd_eq hrow).mp hdvd⟩
  · rintro ⟨hrow, hgcd⟩
    exact ⟨hrow, (squeezedNormalizedRowOneCandidate_halfRow_dvd_iff_gcd_eq hrow).mpr hgcd⟩

theorem squeezedNormalizedRowOneCandidate_not_caseIKernel_of_halfRow_gcd_lt
    {F X t g : ℕ} (_hrow : squeezedNormalizedRowOneCandidate F X t g)
    (hgcd : Nat.gcd (g * (X - 2 * t)) (F * X / 2 - 1) < F * X / 2 - 1) :
    ¬ squeezedNormalizedCaseIKernel F X t g := by
  intro hkernel
  have hgcd_eq :
      Nat.gcd (g * (X - 2 * t)) (F * X / 2 - 1) = F * X / 2 - 1 :=
    (squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq.mp hkernel).2
  omega

theorem
  exists_squeezedNormalizedCaseIKernel_iff_exists_mem_rowOneCandidate_halfRow_gcd_eq_of_list_exact
    {F X : ℕ} {candidates : List (ℕ × ℕ)}
    (hcover : ∀ t g : ℕ,
      squeezedNormalizedRowOneCandidate F X t g → (t, g) ∈ candidates)
    (hsound : ∀ tg ∈ candidates,
      squeezedNormalizedRowOneCandidate F X tg.1 tg.2) :
    (∃ t g : ℕ, squeezedNormalizedCaseIKernel F X t g) ↔
      ∃ tg ∈ candidates,
        Nat.gcd (tg.2 * (X - 2 * tg.1)) (F * X / 2 - 1) = F * X / 2 - 1 := by
  constructor
  · rintro ⟨t, g, hkernel⟩
    have hsplit :=
      squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq.mp hkernel
    exact ⟨(t, g), hcover t g hsplit.1, hsplit.2⟩
  · rintro ⟨tg, hmem, hgcd⟩
    rcases tg with ⟨t, g⟩
    exact ⟨t, g,
      (squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq).mpr
        ⟨hsound (t, g) hmem, hgcd⟩⟩

theorem not_exists_squeezedNormalizedCaseIKernel_of_list_covers_rowOneCandidate_halfRow_gcd_lt
    {F X : ℕ} {candidates : List (ℕ × ℕ)}
    (hcover : ∀ t g : ℕ,
      squeezedNormalizedRowOneCandidate F X t g → (t, g) ∈ candidates)
    (hfail : ∀ tg ∈ candidates,
      Nat.gcd (tg.2 * (X - 2 * tg.1)) (F * X / 2 - 1) < F * X / 2 - 1) :
    ¬ ∃ t g : ℕ, squeezedNormalizedCaseIKernel F X t g := by
  rintro ⟨t, g, hkernel⟩
  have hsplit :=
    squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq.mp hkernel
  have hmem : (t, g) ∈ candidates := hcover t g hsplit.1
  have hlt := hfail (t, g) hmem
  rw [hsplit.2] at hlt
  omega

theorem squeezedNormalized_gap_pos {F X t g : ℕ}
    (h : squeezedNormalizedCaseIKernel F X t g) :
    0 < X - 2 * t := by
  rcases h with
    ⟨_hF_pos, _hX_pos, _ht_pos, _hFodd, _h4X, _hF_ge, h2t_lt, _h4F, _h2F2,
      _hrow, _hhalf⟩
  omega

theorem squeezedNormalized_gap_sq_eq_sq {F X t g : ℕ}
    (h : squeezedNormalizedCaseIKernel F X t g) :
    4 * (g * (F * X - 1)) + (X - 2 * t) * (X - 2 * t) = X * X := by
  rcases h with
    ⟨_hF_pos, _hX_pos, _ht_pos, _hFodd, _h4X, _hF_ge, h2t_lt, _h4F, _h2F2,
      hrow, _hhalf⟩
  exact row_one_factor_gap_sq_eq_sq (n := F * X) (X := X) (t := t) (g := g)
    (by omega : 2 * t ≤ X) hrow

theorem squeezedNormalized_discriminant_eq_gap_sq {F X t g : ℕ}
    (h : squeezedNormalizedCaseIKernel F X t g) :
    X * X - 4 * (g * (F * X - 1)) = (X - 2 * t) * (X - 2 * t) := by
  have hsq := squeezedNormalized_gap_sq_eq_sq h
  omega

theorem i_three_caseI_four_dvd_odd_factor_squeezedNormalized_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hF_ge : 3 ≤ F) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ, squeezedNormalizedCaseIKernel F X t g := by
  have hF_pos : 0 < F := by omega
  have hX_pos : 0 < X := by
    by_cases hX0 : X = 0
    · subst X
      simp at hn
      omega
    · exact Nat.pos_of_ne_zero hX0
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have h2tX : 2 * t ≤ X :=
    two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  have h2t_lt : 2 * t < X := by
    have hne : 2 * t ≠ X := by
      intro hcentral
      exact i_three_caseI_central_branch_false
        hnone hn hj hn_gt hj_pos h2n h3n hcentral
    omega
  rcases
      i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
        hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn with
    ⟨g, hrow1, hdvd, _hle, _hcube, hrow, hsq⟩
  refine ⟨g, ?_⟩
  exact
    ⟨hF_pos, hX_pos, ht_pos, hFodd, h4X, hF_ge, h2t_lt, hrow, hsq,
      by simpa [hn] using hrow1, by simpa [hn] using hdvd⟩

theorem i_three_caseI_four_dvd_odd_factor_false_of_no_squeezedNormalized
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hF_ge : 3 ≤ F) (hjn : 2 * j ≤ n)
    (hkill : ∀ u g : ℕ, ¬ squeezedNormalizedCaseIKernel F X u g) :
    False := by
  rcases
      i_three_caseI_four_dvd_odd_factor_squeezedNormalized_from_row_bound
        hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hF_ge hjn with
    ⟨g, hg⟩
  exact hkill t g hg

theorem n_dvd_mul_choose_self {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    n ∣ j * Nat.choose n j := by
  have hidentity :
      n * Nat.choose (n - 1) (j - 1) = Nat.choose n j * j := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj
    simpa [hn_sub, hj_sub] using h
  rw [mul_comm j (Nat.choose n j), ← hidentity]
  exact dvd_mul_right n _

theorem prime_dvd_choose_three_of_prime_ge_five_dvd {n p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpn : p ∣ n) :
    p ∣ Nat.choose n 3 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_mod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have hthree_mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  simp [digit, hn_mod, hthree_mod] at hdigits

theorem dvd_j_of_no_common_i_three {d n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hn : 0 < n) (hj : 0 < j)
    (hdn : d ∣ n) (hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p)
    (hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3) :
    d ∣ j := by
  have hcop : d.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpchoose
    exact hnone p ⟨hp, hrel p hp hpd, hdchoose p hp hpd, hpchoose⟩
  have hn_dvd : n ∣ j * Nat.choose n j := n_dvd_mul_choose_self hn hj
  have hdprod : d ∣ j * Nat.choose n j := Nat.dvd_trans hdn hn_dvd
  exact (hcop.dvd_mul_right).mp hdprod

theorem prime_ge_five_of_dvd_div_three_odd_not_nine {n p : ℕ}
    (hodd : Odd n) (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hp : p.Prime)
    (hpd : p ∣ n / 3) :
    5 ≤ p := by
  have hn_eq : n = 3 * (n / 3) := (Nat.mul_div_cancel' h3n).symm
  have hdn : n / 3 ∣ n := by
    refine ⟨3, ?_⟩
    simpa [mul_comm] using hn_eq
  by_cases hp2 : p = 2
  · subst p
    have h2n : 2 ∣ n := Nat.dvd_trans hpd hdn
    have hn_even : Even n := even_iff_two_dvd.mpr h2n
    exact False.elim ((Nat.not_odd_iff_even.mpr hn_even) hodd)
  by_cases hp3 : p = 3
  · subst p
    rcases hpd with ⟨a, ha⟩
    apply False.elim
    apply hnot9
    refine ⟨a, ?_⟩
    rw [hn_eq, ha]
    omega
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp2le : 2 ≤ p := hp.two_le
  omega

theorem t5_collapse_eq_three_mul_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    n = 3 * j := by
  let d := n / 3
  have hj_pos : 0 < j := by omega
  have hn_pos : 0 < n := by omega
  have hn_eq : n = 3 * d := by
    dsimp [d]
    exact (Nat.mul_div_cancel' h3n).symm
  have hdn : d ∣ n := by
    refine ⟨3, ?_⟩
    simpa [mul_comm] using hn_eq
  have hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    omega
  have hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3 := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    exact prime_dvd_choose_three_of_prime_ge_five_dvd hp hp5 (Nat.dvd_trans hpd hdn)
  have hdj : d ∣ j := dvd_j_of_no_common_i_three hnone hn_pos hj_pos hdn hrel hdchoose
  have hd_pos : 0 < d := by omega
  have hj_lt_two_d : j < 2 * d := by omega
  have hj_eq_d : j = d := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdj hj_lt_two_d
  rw [hn_eq, hj_eq_d]

theorem t5_i_eq_three_odd_three_exactly_once {n j : ℕ} (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 3 j p := by
  by_contra hnone_exists
  rw [not_exists] at hnone_exists
  have hn_eq : n = 3 * j :=
    t5_collapse_eq_three_mul_of_no_common hnone_exists hodd h3n hnot9 hj hjn
  exact no_common_eq_three_mul_false_of_two_le hnone_exists hn_eq (by omega)

theorem prime_dvd_choose_two_of_odd_prime_dvd {n p : ℕ} (hp : p.Prime)
    (hp_ne_two : p ≠ 2) (hpn : p ∣ n) :
    p ∣ Nat.choose n 2 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have htwo_mod : 2 % p = 2 := Nat.mod_eq_of_lt hp_gt_two
  simp [digit, hn_mod, htwo_mod] at hdigits

theorem two_dvd_choose_two_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) :
    2 ∣ Nat.choose n 2 := by
  apply prime_dvd_choose_of_not_dominated (by decide : Nat.Prime 2)
  intro hdom
  have hdigits := (dominated_iff_forall_digits (by decide : 2 ≤ 2)).mp hdom 1
  rcases h4 with ⟨a, rfl⟩
  have hlevel : (4 * a / 2) % 2 = 0 := by
    have hdiv : 4 * a / 2 = 2 * a := by
      rw [show 4 * a = 2 * (2 * a) by omega]
      exact Nat.mul_div_cancel_left (2 * a) (by decide : 0 < 2)
    rw [hdiv]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_right 2 a)
  simp [digit, hlevel] at hdigits

theorem dvd_j_of_no_common_i_two {d n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 2 j p) (hn : 0 < n) (hj : 0 < j)
    (hdn : d ∣ n) (hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 2) :
    d ∣ j := by
  have hcop : d.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpchoose
    exact hnone p ⟨hp, hp.two_le, hdchoose p hp hpd, hpchoose⟩
  have hn_dvd : n ∣ j * Nat.choose n j := n_dvd_mul_choose_self hn hj
  have hdprod : d ∣ j * Nat.choose n j := Nat.dvd_trans hdn hn_dvd
  exact (hcop.dvd_mul_right).mp hdprod

theorem t2_collapse_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 2 j p)
    (hj : 2 < j) (hjn : 2 * j ≤ n) :
    n = 2 * j ∧ Odd j := by
  have hj_pos : 0 < j := by omega
  have hn_pos : 0 < n := by omega
  by_cases hnodd : Odd n
  · have hdchoose : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ Nat.choose n 2 := by
      intro p hp hpn
      have hp_ne_two : p ≠ 2 := by
        intro hp_eq
        subst p
        have hmod0 : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
        have hmod1 : n % 2 = 1 := Nat.odd_iff.mp hnodd
        omega
      exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_ne_two hpn
    have hn_dvd_j : n ∣ j :=
      dvd_j_of_no_common_i_two hnone hn_pos hj_pos dvd_rfl hdchoose
    have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hn_dvd_j
    omega
  · by_cases h4 : 4 ∣ n
    · have hdchoose : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ Nat.choose n 2 := by
        intro p hp hpn
        by_cases hp_eq_two : p = 2
        · subst p
          exact two_dvd_choose_two_of_four_dvd h4
        · exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_eq_two hpn
      have hn_dvd_j : n ∣ j :=
        dvd_j_of_no_common_i_two hnone hn_pos hj_pos dvd_rfl hdchoose
      have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hn_dvd_j
      omega
    · let m := n / 2
      have hneven : Even n := Nat.not_odd_iff_even.mp hnodd
      have h2n : 2 ∣ n := even_iff_two_dvd.mp hneven
      have hn_eq_two_m : n = 2 * m := by
        dsimp [m]
        exact (Nat.mul_div_cancel' h2n).symm
      have hmdvdn : m ∣ n := by
        refine ⟨2, ?_⟩
        rw [hn_eq_two_m, mul_comm]
      have hdchoose : ∀ p : ℕ, p.Prime → p ∣ m → p ∣ Nat.choose n 2 := by
        intro p hp hpm
        have hp_ne_two : p ≠ 2 := by
          intro hp_eq
          subst p
          apply h4
          rcases hpm with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          rw [hn_eq_two_m, ha]
          omega
        have hpn : p ∣ n := Nat.dvd_trans hpm hmdvdn
        exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_ne_two hpn
      have hm_dvd_j : m ∣ j :=
        dvd_j_of_no_common_i_two hnone hn_pos hj_pos hmdvdn hdchoose
      have hm_le_j : m ≤ j := Nat.le_of_dvd hj_pos hm_dvd_j
      have hj_le_m : j ≤ m := by
        dsimp [m]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        simpa [mul_comm] using hjn
      have hm_eq_j : m = j := le_antisymm hm_le_j hj_le_m
      have hn_eq : n = 2 * j := by
        rw [hn_eq_two_m, hm_eq_j]
      have hj_odd : Odd j := by
        apply Nat.not_even_iff_odd.mp
        intro hjeven
        apply h4
        have h2j : 2 ∣ j := even_iff_two_dvd.mp hjeven
        rcases h2j with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rw [hn_eq, ha]
        omega
      exact ⟨hn_eq, hj_odd⟩

theorem two_mul_mod_eq_one_of_dvd_pred {j p : ℕ}
    (hp : p.Prime) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    (2 * j) % p = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 2 * j = p * a + 1 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]

theorem prime_dvd_choose_two_of_dvd_two_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    p ∣ Nat.choose (2 * j) 2 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : (2 * j) % p = 1 := two_mul_mod_eq_one_of_dvd_pred hp hpdvd hj
  have htwo_mod : 2 % p = 2 := Nat.mod_eq_of_lt hp_gt_two
  simp [digit, hn_mod, htwo_mod] at hdigits

theorem prime_dvd_central_of_dvd_two_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    p ∣ Nat.choose (2 * j) j := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : (2 * j) % p = 1 := two_mul_mod_eq_one_of_dvd_pred hp hpdvd hj
  have hp_not_dvd_j : ¬ p ∣ j := by
    intro hpj
    have hj_mod0 : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpj
    have htwom0 : (2 * j) % p = 0 := by
      rw [Nat.mul_mod, hj_mod0]
      simp
    omega
  have hle : j % p ≤ 1 := by
    simpa [digit, hn_mod] using hdigits
  have hj_mod_ne_zero : j % p ≠ 0 := by
    intro hj_mod0
    exact hp_not_dvd_j (Nat.dvd_iff_mod_eq_zero.mpr hj_mod0)
  have hj_mod : j % p = 1 := by omega
  have htwom_calc : (2 * j) % p = 2 := by
    rw [Nat.mul_mod, hj_mod, Nat.mod_eq_of_lt hp_gt_two]
    exact Nat.mod_eq_of_lt hp_gt_two
  omega

theorem t2_i_eq_two {n j : ℕ} (hj : 2 < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 2 j p := by
  by_contra hnone_exists
  rw [not_exists] at hnone_exists
  have hj_pos : 0 < j := by omega
  have hcollapse := t2_collapse_of_no_common hnone_exists hj hjn
  rcases hcollapse with ⟨hn_eq, _⟩
  have hpred_ne_one : 2 * j - 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hpred_ne_one
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    subst p
    rcases hpdvd with ⟨a, ha⟩
    omega
  have hp_choose_two : p ∣ Nat.choose (2 * j) 2 :=
    prime_dvd_choose_two_of_dvd_two_mul_sub_one hp hp_ne_two hpdvd hj_pos
  have hp_choose_j : p ∣ Nat.choose (2 * j) j :=
    prime_dvd_central_of_dvd_two_mul_sub_one hp hp_ne_two hpdvd hj_pos
  exact hnone_exists p ⟨hp, hp.two_le, by simpa [hn_eq] using hp_choose_two,
    by simpa [hn_eq] using hp_choose_j⟩

theorem t1_i_eq_one {n j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 1 j p := by
  by_contra hnone
  rw [not_exists] at hnone
  have hj_pos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 2) hj
  have hn_pos : 0 < n := (Nat.mul_pos (by decide : 0 < 2) hj_pos).trans_le hjn
  have hcop : n.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpc
    have hp_one : 1 ≤ p := hp.one_le
    have hp_choose_one : p ∣ Nat.choose n 1 := by
      simpa [Nat.choose_one_right] using hpn
    exact hnone p ⟨hp, hp_one, hp_choose_one, hpc⟩
  have hidentity :
      n * Nat.choose (n - 1) (j - 1) = Nat.choose n j * j := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
    have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
    simpa [hn_sub, hj_sub] using h
  have hdiv_product : n ∣ j * Nat.choose n j := by
    rw [mul_comm j (Nat.choose n j), ← hidentity]
    exact dvd_mul_right n _
  have hdiv_j : n ∣ j := (hcop.dvd_mul_right).mp hdiv_product
  have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hdiv_j
  omega

/-- A prime `p` is relevant to row `i` exactly when `p ≥ i`. -/
def relevantPrime (i p : ℕ) : Prop :=
  p.Prime ∧ i ≤ p

theorem relevantPrime_ignores_small {i p : ℕ} (hp : p < i) :
    ¬ relevantPrime i p := by
  intro h
  exact Nat.not_le_of_gt hp h.2

/-- The corrected obstruction criterion: only primes `p ≥ i` are constrained. -/
def obstructionCriterion (n i j : ℕ) : Prop :=
  ∀ p : ℕ, relevantPrime i p → dominated i n p ∨ dominated j n p

theorem no_commonPrimeDivisor_iff_obstructionCriterion (n i j : ℕ) :
    (∀ p : ℕ, ¬ commonPrimeDivisor n i j p) ↔ obstructionCriterion n i j := by
  classical
  constructor
  · intro hnone p hrel
    by_cases hi : dominated i n p
    · exact Or.inl hi
    · right
      by_contra hj
      exact hnone p
        ⟨hrel.1, hrel.2, prime_dvd_choose_of_not_dominated hrel.1 hi,
          prime_dvd_choose_of_not_dominated hrel.1 hj⟩
  · intro hcrit p hcommon
    rcases hcommon with ⟨hp, hge, hpi, hpj⟩
    rcases hcrit p ⟨hp, hge⟩ with hdom_i | hdom_j
    · have hnonzero := (lucas_nonzero_mod_prime_iff_dominated hp).mpr hdom_i
      exact hnonzero (Nat.dvd_iff_mod_eq_zero.mp hpi)
    · have hnonzero := (lucas_nonzero_mod_prime_iff_dominated hp).mpr hdom_j
      exact hnonzero (Nat.dvd_iff_mod_eq_zero.mp hpj)

/-- If there is no common prime divisor for rows `3` and `j`, the corrected
Lucas obstruction transfers exactly the guarded prime-power part of `X` to
`u`, after the explicit coprimality needed to cancel the normalized factor
`F`. Primes below row `3`, and primes for which row `3` is already dominated,
remain unconstrained. -/
theorem rowNDigitPowerConstraintExact_of_no_common_i_three
    {n F X j u : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * u)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p → ¬ dominated 3 (F * X) p →
        p ^ e ∣ X → (p ^ e).Coprime F) :
    rowNDigitPowerConstraintExact F X u := by
  intro p e hp hp3 hnotdom hpowX
  have hcrit : obstructionCriterion n 3 j :=
    (no_commonPrimeDivisor_iff_obstructionCriterion n 3 j).mp hnone
  have hnotdom_n : ¬ dominated 3 n p := by
    simpa [hn] using hnotdom
  have hdomj : dominated j n p := by
    rcases hcrit p ⟨hp, hp3⟩ with hdom3 | hdomj
    · exact False.elim (hnotdom_n hdom3)
    · exact hdomj
  have hpowN : p ^ e ∣ n := by
    rw [hn]
    exact dvd_mul_of_dvd_right hpowX F
  have hpowJ : p ^ e ∣ j :=
    pow_dvd_of_dominated_and_pow_dvd hp hdomj hpowN
  have hpowFu : p ^ e ∣ F * u := by
    simpa [hj] using hpowJ
  exact (hcopF hp hp3 hnotdom hpowX).dvd_of_dvd_mul_left hpowFu

/-- Local product extraction from the corrected no-common-prime criterion. If
the prime powers in `H` all sit inside `X` and are guarded by the row-`3`
Lucas failure, then the full factor `H` divides `F*u`. This is the exact
statement available before any cancellation against the normalized factor
`F`. -/
theorem factor_dvd_mul_of_no_common_i_three
    {n F X j u H : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * u)
    (hHX : H ∣ X)
    (hH0 : H ≠ 0)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 n p) :
    H ∣ F * u := by
  by_cases hFu0 : F * u = 0
  · rw [hFu0]
    exact dvd_zero H
  · rw [← Nat.factorization_prime_le_iff_dvd hH0 hFu0]
    intro p hp
    by_cases hHp0 : H.factorization p = 0
    · simp [hHp0]
    · have hp_dvd_H : p ∣ H := by
        rw [hp.dvd_iff_one_le_factorization hH0]
        omega
      rcases hprime p hp hp_dvd_H with ⟨hp3, hnotdom⟩
      have hcrit : obstructionCriterion n 3 j :=
        (no_commonPrimeDivisor_iff_obstructionCriterion n 3 j).mp hnone
      have hdomj : dominated j n p := by
        rcases hcrit p ⟨hp, hp3⟩ with hdom3 | hdomj
        · exact False.elim (hnotdom hdom3)
        · exact hdomj
      have hpowH : p ^ H.factorization p ∣ H := by
        rw [hp.pow_dvd_iff_le_factorization hH0]
      have hpowX : p ^ H.factorization p ∣ X := Nat.dvd_trans hpowH hHX
      have hpowN : p ^ H.factorization p ∣ n := by
        rw [hn]
        exact dvd_mul_of_dvd_right hpowX F
      have hpowJ : p ^ H.factorization p ∣ j :=
        pow_dvd_of_dominated_and_pow_dvd hp hdomj hpowN
      have hpowFu : p ^ H.factorization p ∣ F * u := by
        simpa [hj] using hpowJ
      exact (hp.pow_dvd_iff_le_factorization hFu0).mp hpowFu

/-- Reduced extraction in the non-coprime case. Without a coprimality
hypothesis between `H` and `F`, the corrected no-common-prime criterion still
forces the quotient of `H` by the part already present in `F` to divide `u`. -/
theorem factor_div_gcd_dvd_of_no_common_i_three
    {n F X j u H : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * u)
    (hHX : H ∣ X)
    (hH0 : H ≠ 0)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 n p) :
    H / Nat.gcd H F ∣ u := by
  have hHpos : 0 < H := Nat.pos_of_ne_zero hH0
  have hH_dvd_Fu : H ∣ F * u :=
    factor_dvd_mul_of_no_common_i_three hnone hn hj hHX hH0 hprime
  exact dvd_div_gcd_of_dvd_mul hHpos hH_dvd_Fu

/-- An odd natural divisor of a power of two is trivial. This small parity
fact is the obstruction to absorbing an odd shared factor into a residual
power-of-two quotient. -/
theorem odd_dvd_two_pow_eq_one {d b : ℕ}
    (hdodd : Odd d) (hdvd : d ∣ 2 ^ b) :
    d = 1 := by
  induction b with
  | zero =>
      exact Nat.dvd_one.mp (by simpa using hdvd)
  | succ b ih =>
      have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hdodd
      have hdvd' : d ∣ 2 * 2 ^ b := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hdvd
      exact ih (hcop.dvd_of_dvd_mul_left hdvd')

/-- If an odd factor can be multiplied by some natural number and still be a
pure power of two, then that factor is already `1`. -/
theorem odd_factor_eq_one_of_mul_eq_two_pow {A d b : ℕ}
    (hdodd : Odd d) (hpow : A * d = 2 ^ b) :
    d = 1 := by
  have hdvd : d ∣ 2 ^ b := ⟨A, by simpa [mul_comm] using hpow.symm⟩
  exact odd_dvd_two_pow_eq_one hdodd hdvd

/-- If reducing a factor extraction by `gcd H F` leaves residual
`A * gcd H F`, and `H` is odd, that residual can be a power of two only in the
coprime case `gcd H F = 1`. -/
theorem gcd_eq_one_of_odd_left_of_mul_gcd_eq_two_pow {A H F b : ℕ}
    (hHodd : Odd H) (hpow : A * Nat.gcd H F = 2 ^ b) :
    Nat.gcd H F = 1 := by
  have hgodd : Odd (Nat.gcd H F) :=
    hHodd.of_dvd_nat (Nat.gcd_dvd_left H F)
  exact odd_factor_eq_one_of_mul_eq_two_pow hgodd hpow

/-- Existential-power wrapper for
`gcd_eq_one_of_odd_left_of_mul_gcd_eq_two_pow`. -/
theorem gcd_eq_one_of_odd_left_of_mul_gcd_is_power_two {A H F : ℕ}
    (hHodd : Odd H) (hpow : ∃ b : ℕ, A * Nat.gcd H F = 2 ^ b) :
    Nat.gcd H F = 1 := by
  rcases hpow with ⟨b, hb⟩
  exact gcd_eq_one_of_odd_left_of_mul_gcd_eq_two_pow hHodd hb

/-- Local factor extraction from the corrected no-common-prime criterion. This
is sharper than first proving `rowNDigitPowerConstraintExact F X u`: it only
requires cancellation for prime powers that actually occur in the factor `H`
being extracted from `X`. -/
theorem factor_dvd_of_no_common_i_three
    {n F X j u H : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * u)
    (hHX : H ∣ X)
    (hH0 : H ≠ 0)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 n p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → p ^ e ∣ H → (p ^ e).Coprime F) :
    H ∣ u := by
  by_cases hu0 : u = 0
  · subst u
    exact dvd_zero H
  · rw [← Nat.factorization_prime_le_iff_dvd hH0 hu0]
    intro p hp
    by_cases hHp0 : H.factorization p = 0
    · simp [hHp0]
    · have hp_dvd_H : p ∣ H := by
        rw [hp.dvd_iff_one_le_factorization hH0]
        omega
      rcases hprime p hp hp_dvd_H with ⟨hp3, hnotdom⟩
      have hcrit : obstructionCriterion n 3 j :=
        (no_commonPrimeDivisor_iff_obstructionCriterion n 3 j).mp hnone
      have hdomj : dominated j n p := by
        rcases hcrit p ⟨hp, hp3⟩ with hdom3 | hdomj
        · exact False.elim (hnotdom hdom3)
        · exact hdomj
      have hpowH : p ^ H.factorization p ∣ H := by
        rw [hp.pow_dvd_iff_le_factorization hH0]
      have hpowX : p ^ H.factorization p ∣ X := Nat.dvd_trans hpowH hHX
      have hpowN : p ^ H.factorization p ∣ n := by
        rw [hn]
        exact dvd_mul_of_dvd_right hpowX F
      have hpowJ : p ^ H.factorization p ∣ j :=
        pow_dvd_of_dominated_and_pow_dvd hp hdomj hpowN
      have hpowFu : p ^ H.factorization p ∣ F * u := by
        simpa [hj] using hpowJ
      have hpowu : p ^ H.factorization p ∣ u :=
        (hcopF (p := p) (e := H.factorization p) hp hpowH).dvd_of_dvd_mul_left
          hpowFu
      exact (hp.pow_dvd_iff_le_factorization hu0).mp hpowu

/-- Any divisor of a factor coprime to `F` is itself coprime to `F`. -/
theorem coprime_pow_of_dvd_of_coprime_left {H F p e : ℕ}
    (hHF : H.Coprime F) (hpowH : p ^ e ∣ H) :
    (p ^ e).Coprime F :=
  Nat.Coprime.coprime_dvd_left hpowH hHF

/-- Local factor extraction from no-common-prime data with a single
factor-level coprimality hypothesis `H.Coprime F`. -/
theorem factor_dvd_of_no_common_i_three_of_coprime_factor
    {n F X j u H : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * u)
    (hHX : H ∣ X)
    (hH0 : H ≠ 0)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 n p)
    (hHF : H.Coprime F) :
    H ∣ u :=
  factor_dvd_of_no_common_i_three hnone hn hj hHX hH0 hprime
    (fun {_p _e} _hp hpowH => coprime_pow_of_dvd_of_coprime_left hHF hpowH)

/-- Forward bridge from the corrected no-common-prime criterion to the
quotient-kernel obstruction. A squeezed normalized point at `X = A*H` yields a
pure power-two quotient-kernel point once the row-`3` no-common condition
forces the guarded row-digit transfer, the prime divisors of `H` satisfy the
Lucas guard, and the normalized factor `F` is explicitly coprime to the
guarded prime powers being cancelled. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor (F * X) 3 (F * u) q)
    (hX : X = A * H)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 (F * X) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p → ¬ dominated 3 (F * X) p →
        p ^ e ∣ X → (p ^ e).Coprime F) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  have hrow : rowNDigitPowerConstraintExact F X u :=
    rowNDigitPowerConstraintExact_of_no_common_i_three
      (n := F * X) (F := F) (X := X) (j := F * u) (u := u)
      hnone rfl rfl hcopF
  exact
    exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigitExact_factor
      hkernel hrow hX hA4 hApow hHodd hprime

/-- Local-cancellation version of
`exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor`.
It only assumes the prime powers in `H` are coprime to `F`, because those are
the only powers needed to extract `H | u` before quotienting. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor_local
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor (F * X) 3 (F * u) q)
    (hX : X = A * H)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 (F * X) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → p ^ e ∣ H → (p ^ e).Coprime F) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h := by
  have hH0 : H ≠ 0 := ne_of_gt hHodd.pos
  have hHX : H ∣ X := by
    refine ⟨A, ?_⟩
    rw [hX, mul_comm]
  have hHu : H ∣ u :=
    factor_dvd_of_no_common_i_three
      (n := F * X) (F := F) (X := X) (j := F * u) (u := u) (H := H)
      hnone rfl rfl hHX hH0 hprime hcopF
  exact exists_powerTwoQuotientKernel_of_squeezedNormalized_factor_dvd
    hkernel hX hHu hA4 hApow hHodd

/-- Single-coprimality version of the no-common-prime quotient bridge. The
per-prime-power cancellation required by the local bridge follows from
`H.Coprime F`. -/
theorem exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor_coprime
    {F X u g A H : ℕ}
    (hkernel : squeezedNormalizedCaseIKernel F X u g)
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor (F * X) 3 (F * u) q)
    (hX : X = A * H)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H → 3 ≤ p ∧ ¬ dominated 3 (F * X) p)
    (hHF : H.Coprime F) :
    ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h :=
  exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor_local
    hkernel hnone hX hA4 hApow hHodd hprime
    (fun {_p _e} _hp hpowH => coprime_pow_of_dvd_of_coprime_left hHF hpowH)

/-- Contrapositive local-cancellation bridge. Compared with
`not_exists_squeezedNormalized_noCommon_i_three_factor_of_no_powerTwoQuotientKernel`,
this only assumes cancellation for prime powers occurring in `H`. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_no_powerTwoQuotientKernel
    {F A H : ℕ}
    (hno : ¬ ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → p ^ e ∣ H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  rintro ⟨u, g, hnone, hkernel⟩
  exact hno
    (exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor_local
      (F := F) (X := A * H) (u := u) (g := g) (A := A) (H := H)
      hkernel hnone rfl hA4 hApow hHodd hprime hcopF)

/-- Local-cancellation no-common-prime squeezed-normalized no-kernel bridge
from the canonical linear C2 hypothesis. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_canonical_linear
    {F A H : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        F * H * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        F * H * (x * l + y * m)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → p ^ e ∣ H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_linear_via_reduced_gap
        (A := A) (B := F * H) hlinAll)
      hA4 hApow hHodd hprime hcopF

/-- Local-cancellation no-common-prime squeezed-normalized no-kernel bridge
from the canonical ceiling-scaled C2 hypothesis. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_canonical_ceil_scaled
    {F A H : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (2 * l - F * H * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (l - F * H * y) < l)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → p ^ e ∣ H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_ceil_scaled_via_reduced_gap
        (A := A) (B := F * H) hcoverAll)
      hA4 hApow hHodd hprime hcopF

/-- Contrapositive bridge with the single factor-level coprimality hypothesis
`H.Coprime F`. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_coprime_of_no_powerTwoQuotientKernel
    {F A H : ℕ}
    (hno : ¬ ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hHF : H.Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g :=
  not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_no_powerTwoQuotientKernel
    hno hA4 hApow hHodd hprime
    (fun {_p _e} _hp hpowH => coprime_pow_of_dvd_of_coprime_left hHF hpowH)

/-- Canonical-linear no-kernel bridge with factor-level coprimality
`H.Coprime F`. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_coprime_of_canonical_linear
    {F A H : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        F * H * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        F * H * (x * l + y * m)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hHF : H.Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g :=
  not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_canonical_linear
    hlinAll hA4 hApow hHodd hprime
    (fun {_p _e} _hp hpowH => coprime_pow_of_dvd_of_coprime_left hHF hpowH)

/-- Canonical ceiling-scaled no-kernel bridge with factor-level coprimality
`H.Coprime F`. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_coprime_of_canonical_ceil_scaled
    {F A H : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (2 * l - F * H * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (l - F * H * y) < l)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hHF : H.Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g :=
  not_exists_squeezedNormalized_noCommon_i_three_factor_local_of_canonical_ceil_scaled
    hcoverAll hA4 hApow hHodd hprime
    (fun {_p _e} _hp hpowH => coprime_pow_of_dvd_of_coprime_left hHF hpowH)

/-- Contrapositive version of
`exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor`.
This removes the intermediate `rowNDigitPowerConstraintExact` hypothesis from
the squeezed normalized layer and replaces it by the corrected no-common-prime
criterion for rows `3` and `F*u`. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_of_no_powerTwoQuotientKernel
    {F A H : ℕ}
    (hno : ¬ ∃ v h : ℕ, powerTwoQuotientKernel A (F * H) v h)
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p →
        ¬ dominated 3 (F * (A * H)) p →
          p ^ e ∣ A * H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  rintro ⟨u, g, hnone, hkernel⟩
  exact hno
    (exists_powerTwoQuotientKernel_of_squeezedNormalized_noCommon_i_three_factor
      (F := F) (X := A * H) (u := u) (g := g) (A := A) (H := H)
      hkernel hnone rfl hA4 hApow hHodd hprime hcopF)

/-- Corrected no-common-prime squeezed-normalized no-kernel bridge from the
canonical linear C2 hypothesis. This is still conditional on the universal C2
linear hypothesis, the `H` Lucas guard, and the explicit `F` cancellation
coprimality. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_of_canonical_linear
    {F A H : ℕ}
    (hlinAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      2 * (l * m + 1) ≤
                                        F * H * (x * l + y * m)) ∨
                                    (Even c ∧
                                      l * m + 1 ≤
                                        F * H * (x * l + y * m)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p →
        ¬ dominated 3 (F * (A * H)) p →
          p ^ e ∣ A * H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_noCommon_i_three_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_linear_via_reduced_gap
        (A := A) (B := F * H) hlinAll)
      hA4 hApow hHodd hprime hcopF

/-- Corrected no-common-prime squeezed-normalized no-kernel bridge from the
canonical ceiling-scaled C2 hypothesis. This removes the intermediate
row-digit hypothesis from the statement but leaves all genuinely needed
conditional hypotheses explicit. -/
theorem not_exists_squeezedNormalized_noCommon_i_three_factor_of_canonical_ceil_scaled
    {F A H : ℕ}
    (hcoverAll :
      (∃ a : ℕ, A = 2 ^ a) →
        4 ∣ A →
          Odd (F * H) →
            3 ≤ F * H →
              ∀ r s l m alpha beta : ℕ,
                0 < r →
                  0 < s →
                    0 < l →
                      0 < m →
                        r * s = F * H * A - 1 →
                          r * l + s * m = A →
                            r * l < s * m →
                              alpha = r - F * H * m →
                                beta = s - F * H * l →
                                  let c := Nat.gcd alpha beta
                                  let x := alpha / c
                                  let y := beta / c
                                  (Odd c ∧
                                      (2 * l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (2 * l - F * H * y) < l)) ∨
                                    (Even c ∧
                                      (l ≤ F * H * y ∨
                                        ((m - 1) / (F * H * x) + 1) *
                                            (l - F * H * y) < l)))
    (hA4 : 4 ∣ A)
    (hApow : ∃ a : ℕ, A = 2 ^ a)
    (hHodd : Odd H)
    (hprime :
      ∀ p : ℕ, Nat.Prime p → p ∣ H →
        3 ≤ p ∧ ¬ dominated 3 (F * (A * H)) p)
    (hcopF :
      ∀ ⦃p e : ℕ⦄, Nat.Prime p → 3 ≤ p →
        ¬ dominated 3 (F * (A * H)) p →
          p ^ e ∣ A * H → (p ^ e).Coprime F) :
    ¬ ∃ u g : ℕ,
      (∀ q : ℕ, ¬ commonPrimeDivisor (F * (A * H)) 3 (F * u) q) ∧
        squeezedNormalizedCaseIKernel F (A * H) u g := by
  exact
    not_exists_squeezedNormalized_noCommon_i_three_factor_of_no_powerTwoQuotientKernel
      (not_exists_powerTwoQuotientKernel_of_canonical_ceil_scaled_via_reduced_gap
        (A := A) (B := F * H) hcoverAll)
      hA4 hApow hHodd hprime hcopF

end Erdos699
