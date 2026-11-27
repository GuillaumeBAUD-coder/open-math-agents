import FormalConjectures.ErdosProblems.«727»
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev

/-! # A factorial divisibility result of Erdős, Graham, Ruzsa and Straus -/

open Finset

namespace Erdos727Aux

lemma carry_of_dvd_add {n i d : ℕ} (hi : 0 < i) (hdi : 2 * i ≤ d) (hd : d ∣ n + i) :
    d ≤ n % d + n % d := by
  obtain ⟨t, ht⟩ := hd
  have hd0 : 0 < d := by omega
  have ht0 : 0 < t := by
    by_contra! h
    simp [show t = 0 by omega] at ht
    omega
  have hn : n = (d - i) + d * (t - 1) := by
    have hmul : d * (t - 1) + d = d * t := by
      rw [← Nat.mul_succ, show (t - 1).succ = t by omega]
    omega
  nth_rw 1 2 [hn]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : d - i < d)]
  omega

lemma centralBinom_carries_ge {n p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ j ∈ s, 0 < j ∧ p ^ j ≤ n % p ^ j + n % p ^ j) :
    s.card ≤ n.centralBinom.factorization p := by
  let b := max (Nat.log p (n + n) + 1) (s.sup id + 1)
  have hb : Nat.log p (n + n) < b := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  rw [Nat.centralBinom, two_mul]
  rw [Nat.factorization_choose' hp hb]
  apply card_le_card
  intro j hj
  have hsup : j ≤ s.sup id := le_sup (f := id) hj
  exact mem_filter.mpr
    ⟨mem_Ico.mpr ⟨(hs j hj).1, lt_of_lt_of_le (Nat.lt_succ_of_le hsup) (le_max_right _ _)⟩,
       (hs j hj).2⟩

lemma binom_valuation_of_dvd_add {n i p : ℕ} (hp : p.Prime) (hi : 0 < i) (hpi : 2 * i ≤ p) :
    (n + i).factorization p ≤ n.centralBinom.factorization p := by
  apply le_trans ?_ (centralBinom_carries_ge hp (Icc 1 ((n + i).factorization p)) ?_)
  · simp [Nat.card_Icc]
  intro j hj
  have hj' := mem_Icc.mp hj
  have hpj : p ≤ p ^ j := by
    simpa using Nat.pow_le_pow_right hp.pos hj'.1
  exact ⟨hj'.1, carry_of_dvd_add hi (hpi.trans hpj)
    ((hp.pow_dvd_iff_le_factorization (by omega)).mpr hj'.2)⟩

lemma two_carries_of_prime_factor {m r : ℕ} (hr : r.Prime) (hm : m < r) (hmr : r < 2 * m) :
    2 ≤ (m * r - 1).centralBinom.factorization r := by
  apply le_trans ?_ (centralBinom_carries_ge hr ({1, 2} : Finset ℕ) ?_)
  · decide
  intro j hj
  simp only [mem_insert, mem_singleton] at hj
  rcases hj with rfl | rfl
  · simp only [pow_one]
    have hpos : 0 < m * r := Nat.mul_pos (by omega) hr.pos
    refine ⟨by decide, carry_of_dvd_add (i := 1) (by decide) hr.two_le ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m * r)]
    exact dvd_mul_left _ _
  · have hlow : r ^ 2 ≤ (m * r - 1) + (m * r - 1) := by
      have h := Nat.mul_le_mul_right r (show r + 1 ≤ 2 * m by omega)
      have hr2 := hr.two_le
      rw [Nat.add_mul, one_mul, Nat.mul_assoc] at h
      rw [pow_two]
      omega
    have hhi : m * r - 1 < r ^ 2 := by
      rw [pow_two]
      exact (Nat.sub_le _ _).trans_lt (Nat.mul_lt_mul_of_pos_right hm hr.pos)
    exact ⟨by decide, by simpa [Nat.mod_eq_of_lt hhi] using hlow⟩

lemma factorization_add_of_pow_dvd {p t i s : ℕ} (hp : p.Prime) (ht : p ^ s ∣ t)
    (hi : 0 < i) (hil : i < p ^ s) :
    (t + i).factorization p = i.factorization p := by
  have hnd : ¬ p ^ s ∣ i := by
    exact fun h => (not_le_of_gt hil) (Nat.le_of_dvd hi h)
  have hnd' : ¬ p ^ s ∣ t + i := by
    exact fun h => hnd (Nat.dvd_add_iff_right ht |>.2 h)
  have hpos : t + i ≠ 0 := by omega
  have hti : (t + i).factorization p < s := by
    exact Nat.lt_of_not_ge (fun h => hnd' ((hp.pow_dvd_iff_le_factorization hpos).2 h))
  have hii : i.factorization p < s := by
    exact Nat.lt_of_not_ge (fun h => hnd ((hp.pow_dvd_iff_le_factorization hi.ne').2 h))
  apply le_antisymm
  · have h := (hp.pow_dvd_iff_le_factorization hpos).2
      (le_rfl : (t + i).factorization p ≤ (t + i).factorization p)
    have ht' := (Nat.pow_dvd_pow p hti.le).trans ht
    exact (hp.pow_dvd_iff_le_factorization hi.ne').1 (Nat.dvd_add_iff_right ht' |>.2 h)
  · have h := (hp.pow_dvd_iff_le_factorization hi.ne').2
      (le_rfl : i.factorization p ≤ i.factorization p)
    have ht' := (Nat.pow_dvd_pow p hii.le).trans ht
    exact (hp.pow_dvd_iff_le_factorization hpos).1 (dvd_add ht' h)

end Erdos727Aux

open Finset Filter
open scoped Topology

namespace Erdos727Aux

def bertrandPrimes (m : ℕ) : Finset ℕ :=
  (range (2 * m + 1)).filter (fun p => m < p ∧ p.Prime)

lemma centralBinom_le_bertrandPrimes {n : ℕ} (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ (Nat.sqrt (2 * n) + 1) *
      4 ^ (2 * n / 3) * (2 * n) ^ (bertrandPrimes n).card := by
  let s := range (2 * n + 1)
  let u (p : ℕ) := if p ≤ Nat.sqrt (2 * n) then 2 * n else 1
  let v (p : ℕ) := if p ≤ 2 * n / 3 ∧ p.Prime then p else 1
  let w (p : ℕ) := if n < p ∧ p.Prime then 2 * n else 1
  have hupos (p : ℕ) : 1 ≤ u p := by dsimp [u]; split <;> omega
  have hvpos (p : ℕ) : 1 ≤ v p := by
    dsimp [v]
    split
    next h => exact h.2.one_lt.le
    next => rfl
  have hwpos (p : ℕ) : 1 ≤ w p := by dsimp [w]; split <;> omega
  have hpoint (p : ℕ) (hp : p ∈ s) : p ^ n.centralBinom.factorization p ≤ u p * v p * w p := by
    by_cases hprime : p.Prime
    · by_cases hp1 : p ≤ Nat.sqrt (2 * n)
      · have hbound : p ^ n.centralBinom.factorization p ≤ 2 * n :=
          Nat.pow_factorization_choose_le (k := n) (by omega)
        simp only [u, if_pos hp1]
        have h1 := Nat.mul_le_mul_left (2 * n) (hvpos p)
        have h2 := Nat.mul_le_mul_left (2 * n * v p) (hwpos p)
        simpa using hbound.trans ((by simpa using h1 : 2 * n ≤ 2 * n * v p).trans
          (by simpa using h2))
      · by_cases hp2 : n < p
        · have hbound : p ^ n.centralBinom.factorization p ≤ 2 * n :=
            Nat.pow_factorization_choose_le (k := n) (by omega)
          simp only [w, if_pos (show n < p ∧ p.Prime from ⟨hp2, hprime⟩)]
          have h1 : 1 ≤ u p * v p := Nat.mul_pos (hupos p) (hvpos p)
          exact hbound.trans (by simpa using Nat.mul_le_mul_right (2 * n) h1)
        · by_cases hp3 : p ≤ 2 * n / 3
          · have hbound : n.centralBinom.factorization p ≤ 1 :=
              Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hp1))
            have hpow := (Nat.pow_le_pow_right hprime.pos hbound)
            simp only [pow_one] at hpow
            simp only [v, if_pos (show p ≤ 2 * n / 3 ∧ p.Prime from ⟨hp3, hprime⟩)]
            have h1 : p ≤ u p * p := by simpa using Nat.mul_le_mul_right p (hupos p)
            have h2 : u p * p ≤ u p * p * w p := by
              simpa using Nat.mul_le_mul_left (u p * p) (hwpos p)
            exact hpow.trans (h1.trans h2)
          · rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn (by omega) (by omega),
                pow_zero]
            exact Nat.mul_pos (Nat.mul_pos (hupos p) (hvpos p)) (hwpos p)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hprime, pow_zero]
      exact Nat.mul_pos (Nat.mul_pos (hupos p) (hvpos p)) (hwpos p)
  have hu : (∏ p ∈ s, u p) ≤ (2 * n) ^ (Nat.sqrt (2 * n) + 1) := by
    simp only [u, ← prod_filter, prod_const]
    refine Nat.pow_le_pow_right (by omega) ?_
    refine (card_le_card (t := range (Nat.sqrt (2 * n) + 1)) ?_).trans (by simp)
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2)
  have hv : (∏ p ∈ s, v p) ≤ 4 ^ (2 * n / 3) := by
    rw [show (∏ p ∈ s, v p) = (∏ p ∈ (s.filter fun p => p ≤ 2 * n / 3 ∧ p.Prime), p) by
      simp only [v, prod_filter]]
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    change (∏ p ∈ _, p) ≤ ∏ p ∈ (range (2 * n / 3 + 1)).filter Nat.Prime, p
    apply prod_le_prod_of_subset_of_one_le'
    · intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2.1),
        (mem_filter.mp hp).2.2⟩
    · intro p hp _
      exact (mem_filter.mp hp).2.one_lt.le
  have hw : (∏ p ∈ s, w p) = (2 * n) ^ (bertrandPrimes n).card := by
    simp only [w, bertrandPrimes, s, ← prod_filter, prod_const]
  rw [← Nat.prod_pow_factorization_centralBinom]
  change (∏ p ∈ s, p ^ n.centralBinom.factorization p) ≤ _
  refine (prod_le_prod' hpoint).trans ?_
  rw [prod_mul_distrib, prod_mul_distrib, hw]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hu hv)

lemma eventually_many_bertrandPrimes :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * (Real.log 2 / 3) ≤
      ((bertrandPrimes n).card : ℝ) * Real.log (2 * n) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound
    (show 0 < Real.log 2 / 12 by positivity)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hlo
  refine eventually_atTop.mpr ⟨max 4 ⌈A⌉₊, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hAn : A ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 4 ⌈A⌉₊).trans hn)
  have hn4r : 4 ≤ (n : ℝ) := by exact_mod_cast hn4
  have hnpos : 0 < (n : ℝ) := by linarith
  have htwo : 0 < 2 * (n : ℝ) := by positivity
  have hsqrt : 2 ≤ Real.sqrt (2 * n) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    linarith
  have hsmall : Real.log (2 * n) ≤ Real.log 2 / 12 * Real.sqrt (2 * n) := by
    have h := hA (2 * n) (by linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_eq_abs, ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hsqrtn : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.nat_sqrt_le_real_sqrt (a := 2 * n)
  have hlogn : Real.log n ≤ Real.log (2 * n) := Real.log_le_log hnpos (by linarith)
  have hlognon : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have herr : Real.log n + ((Nat.sqrt (2 * n) : ℝ) + 1) * Real.log (2 * n) ≤
      (n : ℝ) * (Real.log 2 / 3) := by
    have h1 := mul_le_mul_of_nonneg_right (add_le_add_right hsqrtn 1) hlognon
    have h2 := mul_le_mul_of_nonneg_right
      (show Real.sqrt (2 * n) + 2 ≤ 2 * Real.sqrt (2 * n) by linarith) hlognon
    have h3 := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * Real.sqrt (2 * n) by positivity)
    rw [show 2 * Real.sqrt (2 * n) * (Real.log 2 / 12 * Real.sqrt (2 * n)) =
        (2 * (Real.log 2 / 12)) * Real.sqrt (2 * n) ^ 2 by ring,
      Real.sq_sqrt htwo.le] at h3
    linarith
  have hloN : (4 : ℝ) ^ n < (n : ℝ) * (n.centralBinom : ℝ) := by
    exact_mod_cast Nat.four_pow_lt_mul_centralBinom n hn4
  have hloR := Real.log_lt_log (show 0 < (4 : ℝ) ^ n by positivity) hloN
  rw [Real.log_pow, Real.log_mul hnpos.ne' (by exact_mod_cast n.centralBinom_ne_zero)] at hloR
  have hhiN : (n.centralBinom : ℝ) ≤ (2 * (n : ℝ)) ^ (Nat.sqrt (2 * n) + 1) *
      (4 : ℝ) ^ (2 * n / 3 : ℕ) * (2 * (n : ℝ)) ^ (bertrandPrimes n).card := by
    exact_mod_cast centralBinom_le_bertrandPrimes (show 2 < n by omega)
  have hhiR := Real.log_le_log (show 0 < (n.centralBinom : ℝ) by
    exact_mod_cast n.centralBinom_pos) hhiN
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hhiR
  have hdiv : 3 * (2 * n / 3 : ℕ) ≤ 2 * n := by omega
  have hdivR : 3 * ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hdiv
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl4 : 0 ≤ Real.log 4 := by rw [h4]; positivity
  have h4div := mul_le_mul_of_nonneg_right hdivR hl4
  rw [h4] at hloR hhiR h4div
  push_cast at hhiR
  linarith

end Erdos727Aux

open Finset

namespace Erdos727Aux

def largeDigits (p l x : ℕ) : ℕ :=
  ((range l).filter fun j => p ≤ 2 * (x / p ^ j % p)).card

lemma largeDigits_succ {p l x : ℕ} (_hp : 0 < p) :
    largeDigits p (l + 1) x = (if p ≤ 2 * (x % p) then 1 else 0) + largeDigits p l (x / p) := by
  simp only [largeDigits, card_filter, sum_range_succ', pow_zero, Nat.div_one]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [Nat.div_div_eq_div_mul, pow_succ']

lemma largeDigits_mod {p l x : ℕ} (hp : 0 < p) :
    largeDigits p l (x % p ^ l) = largeDigits p l x := by
  induction l generalizing x with
  | zero => simp [largeDigits]
  | succ l ih =>
    rw [largeDigits_succ hp, largeDigits_succ hp, pow_succ',
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

lemma sum_range_digits {α : Type*} [AddCommMonoid α] (p q : ℕ) (hp : 0 < p) (f : ℕ → α) :
    ∑ x ∈ range (p * q), f x = ∑ y ∈ range q, ∑ d ∈ range p, f (y * p + d) := by
  rw [← sum_product (f := fun z : ℕ × ℕ => f (z.1 * p + z.2))]
  apply sum_bij' (fun x _ => (x / p, x % p)) (fun yd _ => yd.1 * p + yd.2)
  · intro x hx
    exact mem_product.mpr ⟨mem_range.mpr
      ((Nat.div_lt_iff_lt_mul hp).2 (by simpa [mul_comm] using mem_range.mp hx)),
      mem_range.mpr (Nat.mod_lt _ hp)⟩
  · intro yd hd
    obtain ⟨y, d⟩ := yd
    obtain ⟨hy, hd⟩ := mem_product.mp hd
    simp only [mem_range] at hy hd ⊢
    have hmul := Nat.mul_le_mul_right p (show y + 1 ≤ q by omega)
    rw [Nat.add_mul, one_mul] at hmul
    rw [mul_comm p q]
    omega
  · intro x _
    simpa [add_comm, mul_comm] using Nat.mod_add_div x p
  · intro yd h
    obtain ⟨y, d⟩ := yd
    have hd := mem_range.mp (mem_product.mp h).2
    rw [Nat.mul_comm y p, Nat.mul_add_mod, Nat.mod_eq_of_lt hd,
      Nat.mul_add_div hp, Nat.div_eq_of_lt hd, add_zero]
  · intro x _
    congr 1
    simpa [add_comm, mul_comm] using (Nat.mod_add_div x p).symm

lemma digitWeight_sum (p l : ℕ) (hp : 2 ≤ p) :
    ∑ x ∈ range (p ^ l), (1 / 2 : ℝ) ^ largeDigits p l x ≤ (p : ℝ) ^ l * (5 / 6) ^ l := by
  have hp0 : 0 < p := by omega
  induction l with
  | zero => simp [largeDigits]
  | succ l ih =>
    rw [pow_succ' p l, sum_range_digits p (p ^ l) hp0]
    have hweight (d : ℕ) (hd : d ∈ range p) (y : ℕ) :
        (1 / 2 : ℝ) ^ largeDigits p (l + 1) (y * p + d) =
          (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) * (1 / 2 : ℝ) ^ largeDigits p l y := by
      have hd' := mem_range.mp hd
      rw [largeDigits_succ hp0, Nat.mul_comm y p, Nat.mul_add_mod, Nat.mod_eq_of_lt hd',
        Nat.mul_add_div hp0, Nat.div_eq_of_lt hd', add_zero, pow_add]
      split <;> simp
    have hsingle :
        (∑ d ∈ range p, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1)) ≤ (p : ℝ) * (5 / 6) := by
      let a := (p + 1) / 2
      have hap : a ≤ p := by dsimp [a]; omega
      have ha : a = ((p + 1) / 2 : ℕ) := rfl
      have hsplit (d : ℕ) :
          (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) =
            (1 / 2 : ℝ) + if d < a then 1 / 2 else 0 := by
        by_cases hd : d < a
        · rw [if_pos hd, if_neg (by omega : ¬ p ≤ 2 * d)]; norm_num
        · rw [if_neg hd, if_pos (by omega : p ≤ 2 * d), add_zero]
      simp_rw [hsplit]
      rw [sum_add_distrib, sum_const, ← sum_filter]
      have hrange : ((range p).filter (· < a)) = range a := by
        ext d
        simp only [mem_filter, mem_range]
        omega
      rw [hrange, sum_const]
      simp only [card_range, nsmul_eq_mul]
      have hrel : 3 * a ≤ 2 * p := by omega
      have hrelR : 3 * (a : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hrel
      linarith
    calc
      _ = (∑ d ∈ range p, if p ≤ 2 * d then (1 / 2 : ℝ) else 1) *
          ∑ y ∈ range (p ^ l), (1 / 2 : ℝ) ^ largeDigits p l y := by
          rw [mul_sum]
          apply sum_congr rfl
          intro y _
          rw [sum_mul]
          exact sum_congr rfl (fun d hd => hweight d hd y)
      _ ≤ (p : ℝ) * (5 / 6) * ((p : ℝ) ^ l * (5 / 6) ^ l) := by
          apply mul_le_mul hsingle ih
          · positivity
          · positivity
      _ = _ := by rw [pow_succ', pow_succ']; ring

def badDigits (p l t : ℕ) : Finset ℕ :=
  (range (p ^ l)).filter fun x => largeDigits p l x < t

lemma card_badDigits {p : ℕ} (hp : 2 ≤ p) (t : ℕ) :
    ((badDigits p (12 * t) t).card : ℝ) ≤ (p : ℝ) ^ (12 * t) * (1 / 2 : ℝ) ^ t := by
  let l := 12 * t
  have hcount :
      ((badDigits p l t).card : ℝ) * (1 / 2 : ℝ) ^ t ≤ (p : ℝ) ^ l * (5 / 6) ^ l := by
    calc
      _ = ∑ x ∈ badDigits p l t, (1 / 2 : ℝ) ^ t := by simp
      _ ≤ ∑ x ∈ badDigits p l t, (1 / 2 : ℝ) ^ largeDigits p l x := by
          apply sum_le_sum
          intro x hx
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (mem_filter.mp hx).2.le
      _ ≤ ∑ x ∈ range (p ^ l), (1 / 2 : ℝ) ^ largeDigits p l x := by
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ _ := digitWeight_sum p l hp
  change ((badDigits p l t).card : ℝ) ≤ _
  calc
    _ ≤ (p : ℝ) ^ l * (5 / 6) ^ l / (1 / 2 : ℝ) ^ t :=
      (le_div_iff₀ (by positivity)).2 hcount
    _ = (p : ℝ) ^ l * (((5 / 6 : ℝ) ^ 12) / (1 / 2)) ^ t := by
      have hpw : (5 / 6 : ℝ) ^ l = ((5 / 6 : ℝ) ^ 12) ^ t := by
        exact pow_mul _ _ _
      rw [hpw, mul_div_assoc, ← div_pow]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by norm_num) _

lemma badDigits_on_multiples {p t M A : ℕ} (hp : 2 ≤ p) (hA : 0 < A)
    (hcop : Nat.Coprime (p ^ (12 * t)) A) (hQ : p ^ (12 * t) ≤ M)
    (s : Finset ℕ) (hs : ∀ r ∈ s, 0 < r ∧ r ≤ 2 * M ∧
        largeDigits p (12 * t) (A * r - 1) < t) :
    (s.card : ℝ) ≤ 3 * (M : ℝ) * (1 / 2 : ℝ) ^ t := by
  let Q := p ^ (12 * t)
  have hQpos : 0 < Q := pow_pos (by omega) _
  let f (r : ℕ) := ((A * r - 1) % Q, r / Q)
  have hc : s.card ≤ (badDigits p (12 * t) t).card * (2 * M / Q + 1) := by
    rw [← card_range (2 * M / Q + 1), ← card_product]
    apply card_le_card_of_injOn f
    · intro r hr
      obtain ⟨hr0, hrM, hbad⟩ := hs r hr
      apply mem_product.mpr
      constructor
      · apply mem_filter.mpr
        exact ⟨mem_range.mpr (Nat.mod_lt _ hQpos), (largeDigits_mod (by omega : 0 < p)).trans_lt hbad⟩
      · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hrM))
    · intro r hr r' hr' hf
      have h1 : A * r - 1 ≡ A * r' - 1 [MOD Q] := congrArg Prod.fst hf
      have hm : A * r ≡ A * r' [MOD Q] := by
        simpa [Nat.sub_add_cancel (Nat.mul_pos hA (hs r hr).1),
          Nat.sub_add_cancel (Nat.mul_pos hA (hs r' hr').1)] using h1.add_right 1
      have h2 : r ≡ r' [MOD Q] := Nat.ModEq.cancel_left_of_coprime hcop hm
      have h3 : r / Q = r' / Q := congrArg Prod.snd hf
      change r % Q = r' % Q at h2
      calc
        r = r % Q + Q * (r / Q) := (Nat.mod_add_div r Q).symm
        _ = r' % Q + Q * (r' / Q) := by rw [h3, h2]
        _ = r' := Nat.mod_add_div r' Q
  have hcast : (s.card : ℝ) ≤ ((badDigits p (12 * t) t).card : ℝ) * ((2 * M / Q + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hc
  have hmul := Nat.div_mul_le_self (2 * M) Q
  have hbound : (2 * M / Q + 1) * Q ≤ 3 * M := by
    rw [Nat.add_mul, one_mul]
    omega
  have hboundR : ((2 * M / Q + 1 : ℕ) : ℝ) * (Q : ℝ) ≤ 3 * (M : ℝ) := by exact_mod_cast hbound
  have hbad : ((badDigits p (12 * t) t).card : ℝ) ≤ (Q : ℝ) * (1 / 2 : ℝ) ^ t := by
    simpa [Q] using card_badDigits hp t
  calc
    (s.card : ℝ) ≤ ((badDigits p (12 * t) t).card : ℝ) * ((2 * M / Q + 1 : ℕ) : ℝ) := hcast
    _ ≤ ((Q : ℝ) * (1 / 2 : ℝ) ^ t) * ((2 * M / Q + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = (((2 * M / Q + 1 : ℕ) : ℝ) * (Q : ℝ)) * (1 / 2 : ℝ) ^ t := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hboundR (by positivity)

end Erdos727Aux

open Finset Filter
open scoped Topology

namespace Erdos727Aux

lemma suffix_factorization (n l p : ℕ) :
    ((n + 2).ascFactorial l).factorization p =
      ∑ i ∈ range l, (n + 2 + i).factorization p := by
  rw [Nat.ascFactorial_eq_prod_range, Nat.factorization_prod_apply]
  intro i _
  omega

lemma required_factorization (n k p : ℕ) :
    ((n + 1) ^ 2 * (n + 2).ascFactorial (k - 1)).factorization p =
      2 * (n + 1).factorization p + ((n + 2).ascFactorial (k - 1)).factorization p := by
  rw [Nat.factorization_mul (by positivity) (Nat.ascFactorial_pos (n + 1) (k - 1)).ne',
    Nat.factorization_pow]
  simp

lemma suffix_val_of_pow_dvd {p s n k : ℕ} (hp : p.Prime)
    (hpow : p ^ s ∣ n + 1) (hks : k ≤ p ^ s) :
    ((n + 2).ascFactorial (k - 1)).factorization p ≤ k := by
  rw [suffix_factorization]
  have heq : ∑ i ∈ range (k - 1), (n + 2 + i).factorization p =
      ∑ i ∈ range (k - 1), (i + 1).factorization p := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [show n + 2 + i = (n + 1) + (i + 1) by omega]
    exact factorization_add_of_pow_dvd hp hpow (by omega) (by omega)
  rw [heq, ← Nat.factorization_prod_apply (fun i _ => by omega), prod_range_add_one_eq_factorial]
  exact (Nat.factorization_factorial_le_div_pred hp (k - 1)).trans (Nat.div_le_self _ _ |>.trans (by omega))

lemma suffix_val_of_dvd_large {p n k : ℕ} (_hp : p.Prime)
    (hk : k < p) (hdiv : p ∣ n + 1) :
    ((n + 2).ascFactorial (k - 1)).factorization p = 0 := by
  rw [suffix_factorization]
  apply sum_eq_zero
  intro i hi
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  rw [show n + 2 + i = (n + 1) + (i + 1) by omega] at h
  have h' := (Nat.dvd_add_iff_right hdiv).2 h
  have hip : i + 1 < p := by
    have := mem_range.mp hi
    omega
  exact (not_le_of_gt hip) (Nat.le_of_dvd (by omega) h')

lemma suffix_val_le_carries_of_large {p n k : ℕ} (hp : p.Prime) (hk : 2 * k < p) :
    ((n + 2).ascFactorial (k - 1)).factorization p ≤ n.centralBinom.factorization p := by
  rw [suffix_factorization]
  by_cases h : ∃ i ∈ range (k - 1), p ∣ n + 2 + i
  · obtain ⟨i, hi, hpi⟩ := h
    rw [sum_eq_single i]
    · rw [show n + 2 + i = n + (i + 2) by omega]
      have := mem_range.mp hi
      exact binom_valuation_of_dvd_add hp (by omega) (by omega)
    · intro j hj hji
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpj
      have he : n + 2 + j ≡ n + 2 + i [MOD p] :=
        (Nat.modEq_zero_iff_dvd.mpr hpj).trans (Nat.modEq_zero_iff_dvd.mpr hpi).symm
      have hmod : j % p = i % p := Nat.ModEq.add_left_cancel' _ he
      have hij : i < p ∧ j < p := by
        have := mem_range.mp hi
        have := mem_range.mp hj
        omega
      exact hji (by simpa [Nat.mod_eq_of_lt hij.1, Nat.mod_eq_of_lt hij.2] using hmod)
    · exact fun hi' => (hi' hi).elim
  · have hzero : ∑ i ∈ range (k - 1), (n + 2 + i).factorization p = 0 := by
      apply sum_eq_zero
      intro i hi
      exact Nat.factorization_eq_zero_of_not_dvd (fun hpi => h ⟨i, hi, hpi⟩)
    rw [hzero]
    exact Nat.zero_le _

lemma carries_of_largeDigits {p n s x t : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hn : n + 1 = p ^ s * x)
    (ht : t ≤ largeDigits p (12 * t) (x - 1)) :
    s + t ≤ n.centralBinom.factorization p := by
  have hlow (j : ℕ) (hj : j ∈ Icc 1 s) :
      0 < j ∧ p ^ j ≤ n % p ^ j + n % p ^ j := by
    have hj' := mem_Icc.mp hj
    have hle : 2 ≤ p ^ j := hp.two_le.trans (by
      simpa using Nat.pow_le_pow_right hp.pos hj'.1)
    have hd : p ^ j ∣ n + 1 := by rw [hn]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hj'.2) _
    exact ⟨hj'.1, carry_of_dvd_add (by decide : 0 < (1 : ℕ)) hle hd⟩
  have hquot : n / p ^ s = x - 1 := by
    have hdecomp : p ^ s * (x - 1) + p ^ s = p ^ s * x := by
      rw [← Nat.mul_succ, show (x - 1).succ = x by omega]
    apply Nat.div_eq_of_lt_le
    · have hpow : 0 < p ^ s := pow_pos hp.pos _
      rw [mul_comm]
      omega
    · rw [Nat.sub_add_cancel hx, mul_comm, ← hn]
      omega
  let f : ℕ ↪ ℕ := ⟨fun j => s + j + 1, by intro i j h; dsimp at h; omega⟩
  let d := (range (12 * t)).filter fun j => p ≤ 2 * ((x - 1) / p ^ j % p)
  let a := Icc 1 s ∪ d.map f
  have hdisj : Disjoint (Icc 1 s) (d.map f) := by
    refine disjoint_left.mpr fun j hj hj' => ?_
    obtain ⟨i, _, rfl⟩ := mem_map.mp hj'
    have := (mem_Icc.mp hj).2
    change s + i + 1 ≤ s at this
    omega
  have hc : s + t ≤ a.card := by
    rw [show a = _ by rfl, card_union_of_disjoint hdisj, card_map, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    exact Nat.add_le_add_left ht _
  refine hc.trans (centralBinom_carries_ge hp a fun j hj => ?_)
  rcases mem_union.mp hj with hj | hj
  · exact hlow j hj
  · obtain ⟨i, hi, rfl⟩ := mem_map.mp hj
    have hi' := (mem_filter.mp hi).2
    change 0 < s + i + 1 ∧
      p ^ (s + i + 1) ≤ n % p ^ (s + i + 1) + n % p ^ (s + i + 1)
    have hqi : n / p ^ (s + i) = (x - 1) / p ^ i := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, hquot]
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_pow_succ, hqi, pow_succ]
    let y := (x - 1) / p ^ i % p
    let q := p ^ (s + i)
    change q * p ≤ n % q + q * y + (n % q + q * y)
    calc
      _ ≤ q * (2 * y) := Nat.mul_le_mul_left q hi'
      _ = q * y + q * y := by ring
      _ ≤ _ := Nat.add_le_add (Nat.le_add_left _ _) (Nat.le_add_left _ _)

lemma factorial_dvd_of_window {n k : ℕ} (hk : 1 ≤ k)
    (h : (n + 1) ^ 2 * (n + 2).ascFactorial (k - 1) ∣ n.centralBinom) :
    (n + k).factorial * (n + 1).factorial ∣ (2 * n).factorial := by
  have hnk : n + k = (n + 1) + (k - 1) := by omega
  rw [hnk, ← Nat.factorial_mul_ascFactorial, Nat.factorial_succ]
  have hc : (2 * n).factorial = n.centralBinom * n.factorial * n.factorial := by
    simpa [Nat.centralBinom, two_mul] using (Nat.add_choose_mul_factorial_mul_factorial n n).symm
  rw [hc]
  convert Nat.mul_dvd_mul_right h (n.factorial * n.factorial) using 1 <;> ring

end Erdos727Aux

open Finset Filter
open scoped Topology Chebyshev

namespace Erdos727Aux

lemma exists_large_lcm (k : ℕ) : ∃ T ≥ max 2 (2 * k), T ^ 24 ≤ Nat.lcmUpto T := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (Real.isLittleO_log_id_atTop.bound
    (show 0 < Real.log 2 / 100 by positivity))
  let T := max (max 2 (2 * k)) ⌈A⌉₊
  have hT : 2 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hAr : A ≤ (T : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (max 2 (2 * k)) ⌈A⌉₊))
  have ht0 : 0 < (T : ℝ) := by linarith
  have hsmall : Real.log (T + 1) ≤ (Real.log 2 / 100) * (T + 1) := by
    have h := hA ((T : ℝ) + 1) (by linarith)
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (T : ℝ) + 1 by linarith),
      abs_of_nonneg (Real.log_nonneg (show 1 ≤ (T : ℝ) + 1 by linarith))] using h
  have hsmall2 : Real.log (T + 1) ≤ (Real.log 2 / 100) * (2 * T) :=
    hsmall.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hlo := Chebyshev.psi_ge T
  rw [Chebyshev.psi_eq_log_lcmUpto] at hlo
  refine ⟨T, le_max_left _ _, ?_⟩
  have hsign : 0 < ((Nat.lcmUpto T : ℕ) : ℝ) := by exact_mod_cast Nat.lcmUpto_pos T
  have hcast : (T : ℝ) ^ (24 : ℕ) ≤ ((Nat.lcmUpto T : ℕ) : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) hsign).1
    rw [Real.log_pow]
    have hmono : Real.log T ≤ Real.log (T + 1) := Real.log_le_log ht0 (by linarith)
    have h25 : 25 * Real.log (T + 1) ≤ (T : ℝ) * Real.log 2 := by
      calc
        _ ≤ 25 * ((Real.log 2 / 100) * (2 * T)) :=
          mul_le_mul_of_nonneg_left hsmall2 (by norm_num)
        _ = ((T : ℝ) * Real.log 2) / 2 := by ring
        _ ≤ _ := half_le_self_iff.mpr (mul_nonneg ht0.le hlog2.le)
    calc
      _ ≤ (24 : ℝ) * Real.log (T + 1) := mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = 25 * Real.log (T + 1) - Real.log (T + 1) := by ring
      _ ≤ (T : ℝ) * Real.log 2 - Real.log (T + 1) := sub_le_sub_right h25 _
      _ ≤ _ := hlo
  exact_mod_cast hcast

lemma exists_prime_good (B k z : ℕ) (hB : 1 < B)
    (hbal : ∀ p ∈ B.primeFactors, p ^ (24 * B.factorization p) ≤ B) :
    ∃ a ≥ k, ∃ r ∈ bertrandPrimes (B ^ a),
      z < B ^ a ∧ ∀ p ∈ B.primeFactors,
        (B ^ a).factorization p + k ≤ largeDigits p (12 * ((B ^ a).factorization p + k))
          (ordCompl[p] (B ^ a) * r - 1) := by
  have hpows : Tendsto (fun a : ℕ => B ^ a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hB
  have hcount := hpows.eventually eventually_many_bertrandPrimes
  let C : ℝ := 3 * (B.primeFactors.card : ℝ)
  have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have h1 := tendsto_self_mul_const_pow_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hdec : Tendsto (fun a : ℕ =>
      C * (1 / 2 : ℝ) ^ a * (Real.log 2 + a * Real.log B)) atTop (𝓝 0) := by
    have ht := ((h0.const_mul (Real.log 2)).add (h1.const_mul (Real.log B))).const_mul C
    simp only [mul_zero, add_zero] at ht
    exact ht.congr (fun a => by ring)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a, hak, haz, hap, habound⟩ := ((eventually_ge_atTop (max k 1)).and
    ((hpows.eventually (eventually_gt_atTop z)).and
      (hcount.and (hdec.eventually_lt_const (show 0 < Real.log 2 / 3 by positivity))))).exists
  let m := B ^ a
  have ha1 : 1 ≤ a := (le_max_right _ _).trans hak
  have hka : k ≤ a := (le_max_left _ _).trans hak
  have hm0 : 0 < m := pow_pos (by omega) _
  have hm1 : 1 ≤ m := hm0
  let bad (p : ℕ) := (bertrandPrimes m).filter fun r =>
    largeDigits p (12 * (m.factorization p + k)) (ordCompl[p] m * r - 1) <
      m.factorization p + k
  let allBad := B.primeFactors.biUnion bad
  have hbad (p : ℕ) (hp : p ∈ B.primeFactors) :
      ((bad p).card : ℝ) ≤ 3 * (m : ℝ) * (1 / 2 : ℝ) ^ a := by
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
    let v := B.factorization p
    have hv : 1 ≤ v := hpP.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    let s := m.factorization p
    have hsv : s = a * v := by simp [s, m, v, Nat.factorization_pow]
    let t := s + k
    have hsa : a ≤ s := by
      rw [hsv]
      simpa using Nat.mul_le_mul_left a hv
    have hta : a ≤ t := hsa.trans (Nat.le_add_right _ _)
    have hpow : p ^ (12 * t) ≤ m := by
      have hsk : k ≤ s := hka.trans hsa
      have h12 : 12 * t ≤ 24 * s := by dsimp [t]; omega
      calc
        _ ≤ p ^ (24 * s) := Nat.pow_le_pow_right hpP.pos h12
        _ = (p ^ (24 * v)) ^ a := by rw [hsv, ← pow_mul]; congr 1; ring
        _ ≤ m := Nat.pow_le_pow_left (hbal p hp) _
    have hcop : Nat.Coprime (p ^ (12 * t)) (ordCompl[p] m) :=
      (Nat.coprime_ordCompl hpP hm0.ne').pow_left _
    refine (badDigits_on_multiples hpP.two_le (Nat.ordCompl_pos p hm0.ne') hcop hpow
      (bad p) (fun r hr => ?_)).trans ?_
    · obtain ⟨hrMem, hFail⟩ := mem_filter.mp hr
      obtain ⟨hrLe, hrLt, hrPrime⟩ := mem_filter.mp hrMem
      exact ⟨hrPrime.pos, Nat.le_of_lt_succ (mem_range.mp hrLe), hFail⟩
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) hta)
        (by positivity)
  have hall : (allBad.card : ℝ) ≤ C * (m : ℝ) * (1 / 2 : ℝ) ^ a := by
    calc
      _ ≤ ∑ p ∈ B.primeFactors, ((bad p).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := B.primeFactors) (t := bad))
      _ ≤ ∑ _p ∈ B.primeFactors, 3 * (m : ℝ) * (1 / 2 : ℝ) ^ a :=
        sum_le_sum hbad
      _ = _ := by simp [C]; ring
  have hlog : Real.log (2 * m) = Real.log 2 + a * Real.log B := by
    rw [Real.log_mul (by norm_num) (by positivity : (m : ℝ) ≠ 0)]
    simp [m, Real.log_pow]
  have hstrict : (allBad.card : ℝ) * Real.log (2 * m) <
      (m : ℝ) * (Real.log 2 / 3) := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hmR1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
    refine (mul_le_mul_of_nonneg_right hall (Real.log_nonneg (by linarith))).trans_lt ?_
    rw [hlog]
    nlinarith [mul_lt_mul_of_pos_left habound hmR]
  have hs : ¬ bertrandPrimes m ⊆ allBad := by
    intro hs
    have hcards : ((bertrandPrimes m).card : ℝ) ≤ (allBad.card : ℝ) := by exact_mod_cast card_le_card hs
    have hmR1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
    exact hstrict.not_ge (hap.trans (mul_le_mul_of_nonneg_right hcards (Real.log_nonneg (by linarith))))
  obtain ⟨r, hr, hbad'⟩ : ∃ r ∈ bertrandPrimes m, r ∉ allBad := by
    by_contra! h
    exact hs (fun r hr => h r hr)
  refine ⟨a, hka, r, hr, haz, fun p hp => ?_⟩
  by_contra! hp'
  exact hbad' (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hr, hp'⟩⟩)

end Erdos727Aux

open Finset Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos727.erdos_727.variants.k_1_2 := by
  intro k hk
  apply Set.infinite_iff_exists_gt.mpr
  intro bound
  obtain ⟨T, hT, hTB⟩ := Erdos727Aux.exists_large_lcm k
  let B := Nat.lcmUpto T
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hTk : 2 * k ≤ T := (le_max_right _ _).trans hT
  have hB0 : B ≠ 0 := Nat.lcmUpto_ne_zero _
  have hB : 1 < B := by
    have hd : 2 ∣ B := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by decide, hT2⟩)
    exact Nat.le_of_dvd (Nat.lcmUpto_pos _) hd
  have hbal (p : ℕ) (hp : p ∈ B.primeFactors) : p ^ (24 * B.factorization p) ≤ B := by
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hv : p ^ B.factorization p ≤ T := by
      dsimp [B]
      rw [Nat.factorization_lcmUpto _ hpP]
      exact Nat.pow_log_le_self _ (by omega)
    rw [Nat.mul_comm 24, pow_mul]
    exact (Nat.pow_le_pow_left hv _).trans hTB
  obtain ⟨a, ha, r, hr, hbig, hgood⟩ :=
    Erdos727Aux.exists_prime_good B k (max bound (2 * k)) hB hbal
  let m := B ^ a
  let n := m * r - 1
  have hm0 : 0 < m := pow_pos (by omega) _
  have hm2 : 2 ≤ m := by omega
  have hkm : 2 * k < m := (le_max_right _ _).trans_lt hbig
  have hbm : bound < m := (le_max_left _ _).trans_lt hbig
  obtain ⟨hrRange, hmr, hrP⟩ := Finset.mem_filter.mp hr
  have hru : r < 2 * m := by
    have hru' : r ≤ 2 * m := Nat.le_of_lt_succ (Finset.mem_range.mp hrRange)
    by_contra! hn
    have he : r = 2 * m := by omega
    have hd : 2 ∣ r := he ▸ dvd_mul_right 2 m
    rcases (Nat.dvd_prime hrP).1 hd with hh | hh <;> omega
  have hr2k : 2 * k < r := hkm.trans hmr
  have hxpos : 0 < m * r := Nat.mul_pos hm0 hrP.pos
  have hn : n + 1 = m * r := Nat.sub_add_cancel hxpos
  have hmn : m ≤ n := by
    have h := Nat.mul_le_mul_left m hrP.two_le
    change m ≤ m * r - 1
    omega
  refine ⟨n, ?_, hbm.trans_le hmn⟩
  change (n + k).factorial * (n + 1).factorial ∣ (2 * n).factorial
  apply Erdos727Aux.factorial_dvd_of_window (by omega)
  apply (Nat.factorization_prime_le_iff_dvd (by
    exact Nat.mul_ne_zero (by positivity)
      (Nat.ascFactorial_pos (n + 1) _).ne') n.centralBinom_ne_zero).1
  intro p hp
  rw [Erdos727Aux.required_factorization]
  have hpVal : (n + 1).factorization p = m.factorization p + r.factorization p := by
    rw [hn, Nat.factorization_mul hm0.ne' hrP.ne_zero]
    rfl
  by_cases hpB : p ∈ B.primeFactors
  · let s := m.factorization p
    have hv : 0 < B.factorization p :=
      hp.factorization_pos_of_dvd hB0 (Nat.dvd_of_mem_primeFactors hpB)
    have hsa : a ≤ s := by
      simp only [s, m, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
      simpa using Nat.mul_le_mul_left a hv
    have hsk : k ≤ s := ha.trans hsa
    have hspow : k ≤ p ^ s := by
      have h2 : 2 ^ s ≤ p ^ s := Nat.pow_le_pow_left hp.two_le _
      exact hsk.trans ((Nat.lt_two_pow_self (n := s)).le.trans h2)
    have hpr : p < r := by
      have hpBd : p ∣ B := Nat.dvd_of_mem_primeFactors hpB
      have hpBl := Nat.le_of_dvd (Nat.lcmUpto_pos T) hpBd
      exact (hpBl.trans (by
        simpa using Nat.pow_le_pow_right (show 0 < B by omega) (show 1 ≤ a by omega))).trans_lt hmr
    have hpVal' : (n + 1).factorization p = s := by
      have hpr0 : r.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun hd =>
        ((Nat.dvd_prime hrP).1 hd).elim hp.ne_one hpr.ne
      rw [hpVal, hpr0, add_zero]
    have hdecomp : n + 1 = p ^ s * (ordCompl[p] m * r) := by
      rw [hn, ← Nat.mul_assoc, Nat.ordProj_mul_ordCompl_eq_self]
    have hdiv : p ^ s ∣ n + 1 := by rw [hdecomp]; exact dvd_mul_right _ _
    have hc := Erdos727Aux.carries_of_largeDigits (s := s) (t := s + k) hp
      (show 0 < ordCompl[p] m * r from Nat.mul_pos (Nat.ordCompl_pos _ hm0.ne') hrP.pos)
      hdecomp (hgood p hpB)
    have hsuf := Erdos727Aux.suffix_val_of_pow_dvd hp hdiv hspow
    rw [hpVal']
    omega
  · have hlarge : 2 * k < p := by
      by_contra! hp'
      apply hpB
      rw [Nat.primeFactors_lcmUpto]
      exact Nat.mem_primesLE.mpr ⟨hp'.trans hTk, hp⟩
    by_cases hpr : p = r
    · subst p
      have hdiv : r ∣ n + 1 := by rw [hn]; exact dvd_mul_left _ _
      rw [hpVal, Nat.factorization_eq_zero_of_lt hmr, hrP.factorization_self,
        Erdos727Aux.suffix_val_of_dvd_large hrP (by omega) hdiv]
      simpa using Erdos727Aux.two_carries_of_prime_factor hrP hmr hru
    · have hpnot : ¬ p ∣ B := fun hd => hpB (hp.mem_primeFactors hd hB0)
      have hpnot' : ¬ p ∣ m := fun hd => hpnot (hp.dvd_of_dvd_pow hd)
      have hpnotr : ¬ p ∣ r := fun hd =>
        ((Nat.dvd_prime hrP).1 hd).elim hp.ne_one hpr
      rw [hpVal, Nat.factorization_eq_zero_of_not_dvd hpnot',
        Nat.factorization_eq_zero_of_not_dvd hpnotr, add_zero, mul_zero, zero_add]
      exact Erdos727Aux.suffix_val_le_carries_of_large hp hlarge
