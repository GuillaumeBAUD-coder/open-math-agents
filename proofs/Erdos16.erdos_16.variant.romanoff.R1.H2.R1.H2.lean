import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1_H2_R1
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.PSeries

open Finset

namespace OMARom

/-- The multiplicative order of `2` modulo `d`. -/
noncomputable def e (d : ℕ) : ℕ := orderOf (2 : ZMod d)

lemma dvd_iff (d r : ℕ) : d ∣ 2 ^ r - 1 ↔ (2 : ZMod d) ^ r = 1 := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [← Nat.modEq_iff_dvd' h1, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm

lemma e_dvd {d r : ℕ} (h : d ∣ 2 ^ r - 1) : e d ∣ r :=
  orderOf_dvd_iff_pow_eq_one.2 ((dvd_iff d r).1 h)

lemma e_pos {d r : ℕ} (hr : 0 < r) (h : d ∣ 2 ^ r - 1) : 0 < e d := by
  rcases Nat.eq_zero_or_pos (e d) with h0 | h0
  · have := e_dvd h
    rw [h0] at this
    have := Nat.eq_zero_of_zero_dvd this
    omega
  · exact h0

lemma e_le {d r : ℕ} (hr : 0 < r) (h : d ∣ 2 ^ r - 1) : e d ≤ r :=
  Nat.le_of_dvd hr (e_dvd h)

lemma dvd_e (d : ℕ) : d ∣ 2 ^ e d - 1 :=
  (dvd_iff d (e d)).2 (pow_orderOf_eq_one _)

lemma pow_sub_one_pos {r : ℕ} (hr : 1 ≤ r) : 0 < 2 ^ r - 1 := by
  have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  omega

lemma pow_sub_one_odd {r : ℕ} (hr : 1 ≤ r) : ¬ 2 ∣ 2 ^ r - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- The constant `∑ 1 / n ^ 2`. -/
noncomputable def Z2 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 2

lemma perprime (x : ℝ) (hx : 1 ≤ x) :
    1 + 1 / x ≤ (1 + 1 / (x + 2)) * (1 + 2 / x ^ 2) := by
  have h : (1 + 1 / (x + 2)) * (1 + 2 / x ^ 2) - (1 + 1 / x) = 6 / (x ^ 2 * (x + 2)) := by
    field_simp
    ring
  have h2 : 0 ≤ 6 / (x ^ 2 * (x + 2)) := by positivity
  linarith

lemma prod_le_sum_divisors (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, (1 + 1 / (p : ℝ)) ≤ ∑ d ∈ m.divisors, 1 / (d : ℝ) := by
  rw [Finset.prod_one_add]
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (m.primeFactors.powerset : Set (Finset ℕ)) := by
    intro s hs t ht hst
    have hs' : ∀ p ∈ s, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 hs hp)
    have ht' : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 ht hp)
    have h1 := Nat.primeFactors_prod hs'
    have h2 := Nat.primeFactors_prod ht'
    simp only at hst
    rw [← h1, ← h2, hst]
  have heq : ∑ t ∈ m.primeFactors.powerset, ∏ i ∈ t, 1 / (i : ℝ) =
      ∑ d ∈ m.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p), 1 / (d : ℝ) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hd
    rw [Nat.mem_divisors]
    refine ⟨?_, hm⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.1 ht))
      (Nat.prod_primeFactors_dvd m)
  · intro d _ _
    positivity

lemma summable_Z2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.2 (by norm_num)

lemma W_le (r : ℕ) (hr : 1 ≤ r) :
    ∏ p ∈ (2 ^ r - 1 : ℕ).primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ)) ≤
      Real.exp (2 * Z2) * ∑ d ∈ (2 ^ r - 1 : ℕ).divisors, 1 / (d : ℝ) := by
  have hm := pow_sub_one_pos hr
  have hodd := pow_sub_one_odd hr
  generalize 2 ^ r - 1 = m at hm hodd
  have hp3 : ∀ p ∈ m.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 := hpp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · have : p = 2 := by omega
      subst this
      exact absurd hpd hodd
    · exact h
  have step1 : ∏ p ∈ m.primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ)) ≤
      ∏ p ∈ m.primeFactors, ((1 + 1 / (p : ℝ)) * (1 + 2 / ((p - 2 : ℕ) : ℝ) ^ 2)) := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      have h3 := hp3 p hp
      have hq : (1 : ℝ) ≤ ((p - 2 : ℕ) : ℝ) := by
        have : 1 ≤ p - 2 := by omega
        exact_mod_cast this
      have hpq : (p : ℝ) = ((p - 2 : ℕ) : ℝ) + 2 := by
        have : p = (p - 2) + 2 := by omega
        exact_mod_cast this
      have := perprime _ hq
      rw [hpq]
      exact this
  rw [Finset.prod_mul_distrib] at step1
  have step2 : ∏ p ∈ m.primeFactors, (1 + 2 / ((p - 2 : ℕ) : ℝ) ^ 2) ≤ Real.exp (2 * Z2) := by
    refine le_trans (Real.prod_one_add_le_exp_sum _ (fun i => by positivity)) ?_
    apply Real.exp_le_exp.2
    have hinj : Set.InjOn (fun p : ℕ => p - 2) (m.primeFactors : Set ℕ) := by
      intro a ha b hb hab
      have h1 := hp3 a ha
      have h2 := hp3 b hb
      simp only at hab
      omega
    have h1 : ∑ p ∈ m.primeFactors, 2 / ((p - 2 : ℕ) : ℝ) ^ 2 =
        2 * ∑ n ∈ m.primeFactors.image (fun p : ℕ => p - 2), 1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact summable_Z2.sum_le_tsum _ (fun i _ => by positivity)
  have step3 := prod_le_sum_divisors m hm.ne'
  have hnn : 0 ≤ ∏ p ∈ m.primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  calc ∏ p ∈ m.primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ))
      ≤ (∏ p ∈ m.primeFactors, (1 + 1 / (p : ℝ))) *
          ∏ p ∈ m.primeFactors, (1 + 2 / ((p - 2 : ℕ) : ℝ) ^ 2) := step1
    _ ≤ (∏ p ∈ m.primeFactors, (1 + 1 / (p : ℝ))) * Real.exp (2 * Z2) :=
        mul_le_mul_of_nonneg_left step2 hnn
    _ ≤ (∑ d ∈ m.divisors, 1 / (d : ℝ)) * Real.exp (2 * Z2) :=
        mul_le_mul_of_nonneg_right step3 (Real.exp_pos _).le
    _ = Real.exp (2 * Z2) * ∑ d ∈ m.divisors, 1 / (d : ℝ) := mul_comm _ _

/-- All divisors of `2 ^ r - 1` with `1 ≤ r ≤ M`. -/
noncomputable def D (M : ℕ) : Finset ℕ := (Finset.Icc 1 M).biUnion fun r => (2 ^ r - 1).divisors

lemma mem_D {M d : ℕ} : d ∈ D M ↔ ∃ r, 1 ≤ r ∧ r ≤ M ∧ d ∣ 2 ^ r - 1 := by
  unfold D
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨r, ⟨h1, h2⟩, h3, _⟩
    exact ⟨r, h1, h2, h3⟩
  · rintro ⟨r, h1, h2, h3⟩
    exact ⟨r, ⟨h1, h2⟩, h3, (pow_sub_one_pos h1).ne'⟩

lemma stepB (M : ℕ) :
    ∑ r ∈ Finset.Icc 1 M, ∑ d ∈ (2 ^ r - 1 : ℕ).divisors, 1 / (d : ℝ) ≤
      ((M : ℝ) + 1) * ∑ d ∈ D M, 1 / ((d : ℝ) * (e d : ℝ)) := by
  have h1 : ∀ r ∈ Finset.Icc 1 M, ∑ d ∈ (2 ^ r - 1 : ℕ).divisors, 1 / (d : ℝ) =
      ∑ d ∈ D M, if d ∣ 2 ^ r - 1 then 1 / (d : ℝ) else 0 := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, mem_D]
    constructor
    · rintro ⟨h, _⟩
      exact ⟨⟨r, hr.1, hr.2, h⟩, h⟩
    · rintro ⟨_, h⟩
      exact ⟨h, (pow_sub_one_pos hr.1).ne'⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨r0, hr01, hr0M, hr0d⟩ := mem_D.1 hd
  have hepos : 0 < e d := e_pos hr01 hr0d
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hr0d (pow_sub_one_pos hr01)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 M).filter (fun r => d ∣ 2 ^ r - 1)).card ≤ M / e d := by
    have hsub : (Finset.Icc 1 M).filter (fun r => d ∣ 2 ^ r - 1) ⊆
        (Finset.Icc 1 (M / e d)).image (fun i => e d * i) := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      obtain ⟨i, hi⟩ := e_dvd hr.2
      rw [Finset.mem_image]
      refine ⟨i, ?_, hi.symm⟩
      rw [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos i with h | h
        · subst h; omega
        · exact h
      · rw [Nat.le_div_iff_mul_le hepos]
        rw [hi] at hr
        linarith [hr.1.2, Nat.mul_comm (e d) i]
    calc _ ≤ ((Finset.Icc 1 (M / e d)).image (fun i => e d * i)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 (M / e d)).card := Finset.card_image_le
      _ = M / e d := by simp
  have hcardR : (((Finset.Icc 1 M).filter (fun r => d ∣ 2 ^ r - 1)).card : ℝ) ≤
      ((M : ℝ) + 1) / (e d : ℝ) := by
    have h2 : ((M / e d : ℕ) : ℝ) ≤ (M : ℝ) / (e d : ℝ) := Nat.cast_div_le
    have h3 : (((Finset.Icc 1 M).filter (fun r => d ∣ 2 ^ r - 1)).card : ℝ) ≤
        ((M / e d : ℕ) : ℝ) := by exact_mod_cast hcard
    have hepos' : (0 : ℝ) < e d := by exact_mod_cast hepos
    have h4 : (M : ℝ) / (e d : ℝ) ≤ ((M : ℝ) + 1) / (e d : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hepos'.le
    linarith
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hepos' : (0 : ℝ) < e d := by exact_mod_cast hepos
  calc (((Finset.Icc 1 M).filter (fun r => d ∣ 2 ^ r - 1)).card : ℝ) * (1 / (d : ℝ))
      ≤ (((M : ℝ) + 1) / (e d : ℝ)) * (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = ((M : ℝ) + 1) * (1 / ((d : ℝ) * (e d : ℝ))) := by
        field_simp

lemma frac_id (x : ℝ) (hx : 0 < x) : 1 / x = 1 / (x + 1) + 1 / (x * (x + 1)) := by
  field_simp

lemma tel (a M : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) :
    (1 : ℝ) / a = 1 / ((M : ℝ) + 1) + ∑ j ∈ Finset.Icc a M, 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
  induction M, haM using Nat.le_induction with
  | base =>
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact frac_id _ ha'
  | succ M hM ih =>
    have hM' : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have := frac_id _ hM'
    push_cast
    rw [this]
    ring

lemma abel (Dset : Finset ℕ) (M : ℕ) (hD : ∀ d ∈ Dset, 1 ≤ e d ∧ e d ≤ M)
    (C : ℕ → ℝ)
    (hC : ∀ j ∈ Finset.Icc 1 M, ∑ d ∈ Dset.filter (fun d => e d ≤ j), 1 / (d : ℝ) ≤ C j)
    (hCM : ∑ d ∈ Dset, 1 / (d : ℝ) ≤ C M) :
    ∑ d ∈ Dset, 1 / ((d : ℝ) * (e d : ℝ)) ≤
      C M * (1 / ((M : ℝ) + 1)) +
        ∑ j ∈ Finset.Icc 1 M, C j * (1 / ((j : ℝ) * ((j : ℝ) + 1))) := by
  have h1 : ∀ d ∈ Dset, 1 / ((d : ℝ) * (e d : ℝ)) =
      (1 / (d : ℝ)) * (1 / ((M : ℝ) + 1)) + ∑ j ∈ Finset.Icc 1 M,
        if e d ≤ j then (1 / (d : ℝ)) * (1 / ((j : ℝ) * ((j : ℝ) + 1))) else 0 := by
    intro d hd
    obtain ⟨he1, heM⟩ := hD d hd
    have ht := tel (e d) M he1 heM
    have hf : (Finset.Icc 1 M).filter (fun j => e d ≤ j) = Finset.Icc (e d) M := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hf, ← Finset.mul_sum, ← mul_add, ← ht, one_div_mul_one_div]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_comm]
  apply add_le_add
  · rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hCM (by positivity)
  · apply Finset.sum_le_sum
    intro j hj
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hC j hj) (by positivity)

lemma recip_sum (T : Finset ℕ) (hT : ∀ m ∈ T, 1 ≤ m) :
    ∑ m ∈ T, 1 / (m : ℝ) ≤ 2 + Real.log (T.card : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k, k = T.card := ⟨_, rfl⟩
  rw [← hk]
  have hsplit := (Finset.sum_filter_add_sum_filter_not T (fun m => m ≤ k)
    (fun m : ℕ => 1 / (m : ℝ))).symm
  have h1 : ∑ m ∈ T.filter (fun m => m ≤ k), 1 / (m : ℝ) ≤ 1 + Real.log k := by
    have hsub : T.filter (fun m => m ≤ k) ⊆ Finset.Icc 1 k := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Icc]
      exact ⟨hT m hm.1, hm.2⟩
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun m : ℕ => 1 / (m : ℝ))
      (fun i _ _ => by positivity)
    have hh := harmonic_le_one_add_log k
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    simp only [one_div] at h ⊢
    linarith
  have h2 : ∑ m ∈ T.filter (fun m => ¬ m ≤ k), 1 / (m : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · have hTe : T = ∅ := Finset.card_eq_zero.1 (by omega)
      rw [hTe]
      simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hpos
      have hle : ∀ m ∈ T.filter (fun m => ¬ m ≤ k), 1 / (m : ℝ) ≤ 1 / (k : ℝ) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        apply one_div_le_one_div_of_le hk'
        have : k ≤ m := by omega
        exact_mod_cast this
      have hs := Finset.sum_le_card_nsmul _ _ _ hle
      have hc : (T.filter (fun m => ¬ m ≤ k)).card ≤ k := by
        rw [hk]
        exact Finset.card_filter_le _ _
      rw [nsmul_eq_mul] at hs
      have hc' : ((T.filter (fun m => ¬ m ≤ k)).card : ℝ) ≤ k := by exact_mod_cast hc
      calc ∑ m ∈ T.filter (fun m => ¬ m ≤ k), 1 / (m : ℝ)
          ≤ ((T.filter (fun m => ¬ m ≤ k)).card : ℝ) * (1 / (k : ℝ)) := hs
        _ ≤ (k : ℝ) * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_right hc' (by positivity)
        _ = 1 := by field_simp
  linarith

lemma prime_recip (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤ 7 / 6 + (1 / 3) * Real.log (S.card : ℝ) := by
  have hsplit : ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤ 1 / 2 + ∑ p ∈ S.erase 3, 1 / ((p : ℝ) - 1) := by
    by_cases h3 : 3 ∈ S
    · rw [← Finset.add_sum_erase S _ h3]
      norm_num
    · rw [Finset.erase_eq_of_notMem h3]
      linarith
  have hprop : ∀ p ∈ S.erase 3, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
    intro p hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hpp, hp2⟩ := hS p hp.2
    have h2 : ¬ 2 ∣ p := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 h).symm
    have h3 : ¬ 3 ∣ p := fun h =>
      hp.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 h).symm
    have := hpp.two_le
    omega
  have hterm : ∀ p ∈ S.erase 3, 1 / ((p : ℝ) - 1) ≤ (1 / 3) * (1 / ((p / 3 : ℕ) : ℝ)) := by
    intro p hp
    obtain ⟨h5, h6⟩ := hprop p hp
    have h1 : 1 ≤ p / 3 := by omega
    have h2 : 3 * (p / 3) + 1 ≤ p := by omega
    have h1' : (0 : ℝ) < ((p / 3 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : 3 * ((p / 3 : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
      have : ((3 * (p / 3) + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) h2'
  have hinj : Set.InjOn (fun p : ℕ => p / 3) (S.erase 3 : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hprop a (Finset.mem_coe.1 ha)
    have h2 := hprop b (Finset.mem_coe.1 hb)
    simp only at hab
    omega
  have hsum : ∑ p ∈ S.erase 3, 1 / ((p : ℝ) - 1) ≤
      (1 / 3) * ∑ m ∈ (S.erase 3).image (fun p => p / 3), 1 / ((m : ℕ) : ℝ) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hT : ∀ m ∈ (S.erase 3).image (fun p => p / 3), 1 ≤ m := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    have := hprop p hp
    omega
  have hrec := recip_sum _ hT
  have hcard : ((S.erase 3).image (fun p => p / 3)).card ≤ S.card :=
    (Finset.card_image_le).trans (Finset.card_erase_le)
  have hlog : Real.log (((S.erase 3).image (fun p => p / 3)).card : ℝ) ≤
      Real.log (S.card : ℝ) := by
    rcases Nat.eq_zero_or_pos ((S.erase 3).image (fun p => p / 3)).card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
  linarith

/-- `n ↦ 1 / n` as a monoid homomorphism. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := ((n : ℝ))⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv]

lemma euler_bound (S Dset : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hD : ∀ d ∈ Dset, d ∈ Nat.factoredNumbers S) :
    ∑ d ∈ Dset, 1 / (d : ℝ) ≤ Real.exp (∑ p ∈ S, 1 / ((p : ℝ) - 1)) := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    show ‖((p : ℝ))⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hnorm S).2
  have hI : HasSum (Set.indicator (Nat.factoredNumbers S) (fun m : ℕ => invHom m))
      (∏ p ∈ S with p.Prime, (1 - invHom p)⁻¹) :=
    (hasSum_subtype_iff_indicator (f := fun m : ℕ => invHom m)).1 hE
  have hle := sum_le_hasSum Dset (fun i _ => Set.indicator_nonneg
    (fun m _ => by show (0 : ℝ) ≤ ((m : ℝ))⁻¹; positivity) i) hI
  have hsum : ∑ d ∈ Dset, Set.indicator (Nat.factoredNumbers S) (fun m : ℕ => invHom m) d =
      ∑ d ∈ Dset, 1 / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Set.indicator_of_mem (hD d hd)]
    show ((d : ℝ))⁻¹ = 1 / (d : ℝ)
    rw [one_div]
  rw [hsum] at hle
  refine hle.trans ?_
  rw [Finset.filter_true_of_mem hS, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    show 0 ≤ (1 - ((p : ℝ))⁻¹)⁻¹
    have : (0 : ℝ) < 1 - ((p : ℝ))⁻¹ := by
      have : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      linarith
    positivity
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    show (1 - ((p : ℝ))⁻¹)⁻¹ ≤ Real.exp (1 / ((p : ℝ) - 1))
    have heq : (1 - ((p : ℝ))⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [heq]
    exact Real.add_one_le_exp _

lemma C_bound (Dset : Finset ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hD : ∀ d ∈ Dset, 1 ≤ e d ∧ e d ≤ j) :
    ∑ d ∈ Dset, 1 / (d : ℝ) ≤ Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ i ∈ Finset.Icc 1 j, (2 ^ i - 1) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2
      (fun i hi => (pow_sub_one_pos (Finset.mem_Icc.1 hi).1).ne')
  have hNodd : ¬ 2 ∣ N := by
    intro h
    rw [hN] at h
    obtain ⟨i, hi, h2⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).1 h
    exact pow_sub_one_odd (Finset.mem_Icc.1 hi).1 h2
  have hfac : ∀ d ∈ Dset, d ∈ Nat.factoredNumbers N.primeFactors := by
    intro d hd
    obtain ⟨h1, h2⟩ := hD d hd
    have hdN : d ∣ N := by
      rw [hN]
      exact dvd_trans (dvd_e d) (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨h1, h2⟩))
    exact Nat.mem_factoredNumbers_of_dvd
      (Nat.mem_factoredNumbers_of_primeFactors_subset hN0 (Finset.Subset.refl _)) hdN
  have hE := euler_bound N.primeFactors Dset
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hfac
  have hP := prime_recip N.primeFactors (fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, fun h => hNodd (h ▸ Nat.dvd_of_mem_primeFactors hp)⟩)
  have hcard : N.primeFactors.card ≤ j * j := by
    have h1 : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 : ∏ p ∈ N.primeFactors, p ≤ N :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (Nat.prod_primeFactors_dvd N)
    have h3 : N ≤ 2 ^ (j * j) := by
      rw [hN]
      calc ∏ i ∈ Finset.Icc 1 j, (2 ^ i - 1) ≤ ∏ _i ∈ Finset.Icc 1 j, 2 ^ j := by
            apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            intro i hi
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Finset.mem_Icc.1 hi).2
            exact le_trans (Nat.sub_le _ _) this
        _ = 2 ^ (j * j) := by
            rw [Finset.prod_const, Nat.card_Icc, ← pow_mul]
            simp
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans (h2.trans h3))
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : Real.log (N.primeFactors.card : ℝ) ≤ 2 * Real.log (j : ℝ) := by
    rcases Nat.eq_zero_or_pos N.primeFactors.card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      have := Real.log_natCast_nonneg j
      linarith
    · have h := Real.log_le_log (by exact_mod_cast hpos)
        (show ((N.primeFactors.card : ℕ) : ℝ) ≤ ((j * j : ℕ) : ℝ) by exact_mod_cast hcard)
      rw [Nat.cast_mul, Real.log_mul hj0.ne' hj0.ne'] at h
      linarith
  refine hE.trans ?_
  have hexp : Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) =
      Real.exp (7 / 6 + Real.log (j : ℝ) * (2 / 3)) := by
    rw [Real.exp_add, Real.rpow_def_of_pos hj0]
  rw [hexp]
  apply Real.exp_le_exp.2
  linarith

/-- The constant `∑ n ^ (-4/3)`. -/
noncomputable def Z43 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹

lemma summable_Z43 : Summable (fun n : ℕ => ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.2 (by norm_num)

lemma D_sum_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ d ∈ D M, 1 / ((d : ℝ) * (e d : ℝ)) ≤ Real.exp (7 / 6) * (1 + Z43) := by
  have hD : ∀ d ∈ D M, 1 ≤ e d ∧ e d ≤ M := by
    intro d hd
    obtain ⟨r, h1, h2, h3⟩ := mem_D.1 hd
    exact ⟨e_pos h1 h3, (e_le h1 h3).trans h2⟩
  have hab := abel (D M) M hD (fun j => Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ))
    (fun j hj => C_bound _ j (Finset.mem_Icc.1 hj).1 (fun d hd => by
      rw [Finset.mem_filter] at hd
      exact ⟨(hD d hd.1).1, hd.2⟩))
    (C_bound _ M hM hD)
  refine hab.trans ?_
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : (0 : ℝ) < Real.exp (7 / 6) := Real.exp_pos _
  have t1 : Real.exp (7 / 6) * (M : ℝ) ^ (2 / 3 : ℝ) * (1 / ((M : ℝ) + 1)) ≤ Real.exp (7 / 6) := by
    have h1 : (M : ℝ) ^ (2 / 3 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by norm_num)
    rw [Real.rpow_one] at h1
    have h0 : 0 ≤ (M : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hM0.le _
    have h2 : (M : ℝ) ^ (2 / 3 : ℝ) * (1 / ((M : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    calc Real.exp (7 / 6) * (M : ℝ) ^ (2 / 3 : ℝ) * (1 / ((M : ℝ) + 1))
        = Real.exp (7 / 6) * ((M : ℝ) ^ (2 / 3 : ℝ) * (1 / ((M : ℝ) + 1))) := by ring
      _ ≤ Real.exp (7 / 6) * 1 := mul_le_mul_of_nonneg_left h2 hc.le
      _ = Real.exp (7 / 6) := mul_one _
  have t2 : ∑ j ∈ Finset.Icc 1 M, Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) *
      (1 / ((j : ℝ) * ((j : ℝ) + 1))) ≤ Real.exp (7 / 6) * Z43 := by
    have hterm : ∀ j ∈ Finset.Icc 1 M, Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) *
        (1 / ((j : ℝ) * ((j : ℝ) + 1))) ≤ Real.exp (7 / 6) * ((j : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
      intro j hj
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
      have hj0 : (0 : ℝ) < j := by linarith
      have hpow : (j : ℝ) ^ (2 / 3 : ℝ) * (j : ℝ) ^ (4 / 3 : ℝ) = (j : ℝ) ^ 2 := by
        rw [← Real.rpow_add hj0, show (2 / 3 : ℝ) + 4 / 3 = 2 by norm_num, Real.rpow_two]
      have hp43 : 0 < (j : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hj0 _
      have hkey : (j : ℝ) ^ (2 / 3 : ℝ) * (1 / ((j : ℝ) * ((j : ℝ) + 1))) ≤
          ((j : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
        rw [mul_one_div, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hp43, hpow]
        nlinarith
      calc Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) * (1 / ((j : ℝ) * ((j : ℝ) + 1)))
          = Real.exp (7 / 6) * ((j : ℝ) ^ (2 / 3 : ℝ) * (1 / ((j : ℝ) * ((j : ℝ) + 1)))) := by
            ring
        _ ≤ Real.exp (7 / 6) * ((j : ℝ) ^ (4 / 3 : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hkey hc.le
    calc ∑ j ∈ Finset.Icc 1 M, Real.exp (7 / 6) * (j : ℝ) ^ (2 / 3 : ℝ) *
          (1 / ((j : ℝ) * ((j : ℝ) + 1)))
        ≤ ∑ j ∈ Finset.Icc 1 M, Real.exp (7 / 6) * ((j : ℝ) ^ (4 / 3 : ℝ))⁻¹ :=
          Finset.sum_le_sum hterm
      _ = Real.exp (7 / 6) * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp (7 / 6) * Z43 :=
          mul_le_mul_of_nonneg_left
            (summable_Z43.sum_le_tsum _ (fun i _ => by positivity)) hc.le
  have : Real.exp (7 / 6) * (1 + Z43) = Real.exp (7 / 6) + Real.exp (7 / 6) * Z43 := by ring
  rw [this]
  exact add_le_add t1 t2

end OMARom

theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1_H2_R1.H2 := by
  have hZ : 0 ≤ OMARom.Z43 := tsum_nonneg (fun n => by positivity)
  refine ⟨1 + Real.exp (2 * OMARom.Z2) * (Real.exp (7 / 6) * (1 + OMARom.Z43)), by positivity, ?_⟩
  intro L hL
  show ∑ r ∈ Finset.range L, ∏ p ∈ (2 ^ r - 1 : ℕ).primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ)) ≤
    (1 + Real.exp (2 * OMARom.Z2) * (Real.exp (7 / 6) * (1 + OMARom.Z43))) * (L : ℝ)
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have hrange : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  rw [hrange, Finset.sum_insert h0]
  have hW0 : ∏ p ∈ (2 ^ 0 - 1 : ℕ).primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ)) = 1 := by simp
  rw [hW0]
  have hE2 : 0 < Real.exp (2 * OMARom.Z2) := Real.exp_pos _
  have hK : 0 ≤ Real.exp (7 / 6) * (1 + OMARom.Z43) := by positivity
  have hsum : ∑ r ∈ Finset.Icc 1 M, ∏ p ∈ (2 ^ r - 1 : ℕ).primeFactors,
      (1 + 1 / ((p - 2 : ℕ) : ℝ)) ≤
      Real.exp (2 * OMARom.Z2) * (((M : ℝ) + 1) * (Real.exp (7 / 6) * (1 + OMARom.Z43))) := by
    calc ∑ r ∈ Finset.Icc 1 M, ∏ p ∈ (2 ^ r - 1 : ℕ).primeFactors, (1 + 1 / ((p - 2 : ℕ) : ℝ))
        ≤ ∑ r ∈ Finset.Icc 1 M, Real.exp (2 * OMARom.Z2) *
            ∑ d ∈ (2 ^ r - 1 : ℕ).divisors, 1 / (d : ℝ) :=
          Finset.sum_le_sum (fun r hr => OMARom.W_le r (Finset.mem_Icc.1 hr).1)
      _ = Real.exp (2 * OMARom.Z2) *
            ∑ r ∈ Finset.Icc 1 M, ∑ d ∈ (2 ^ r - 1 : ℕ).divisors, 1 / (d : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp (2 * OMARom.Z2) *
            (((M : ℝ) + 1) * ∑ d ∈ OMARom.D M, 1 / ((d : ℝ) * (OMARom.e d : ℝ))) :=
          mul_le_mul_of_nonneg_left (OMARom.stepB M) hE2.le
      _ ≤ Real.exp (2 * OMARom.Z2) *
            (((M : ℝ) + 1) * (Real.exp (7 / 6) * (1 + OMARom.Z43))) := by
          apply mul_le_mul_of_nonneg_left _ hE2.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases Nat.eq_zero_or_pos M with hM | hM
          · subst hM
            have : OMARom.D 0 = ∅ := by
              unfold OMARom.D
              simp
            rw [this, Finset.sum_empty]
            exact hK
          · exact OMARom.D_sum_le M hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  push_cast
  nlinarith [mul_nonneg hE2.le (mul_nonneg hM0 hK)]
