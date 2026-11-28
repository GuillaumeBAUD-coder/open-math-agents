import OMAReductions.R_RiemannHypothesis_robin_criterion_rhs_R1
import Mathlib

/-!
# Finite interval verification for Robin's criterion (step H2 of robin_criterion_rhs.R1)

We prove `∀ n : ℕ, 5040 < n → n < 131072 → 4 ≤ n.primeFactors.card →
  (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)`.

Proof architecture:
1. Establish `71 / 40 < exp eulerMascheroniConstant` using an integer lower bound on
   `harmonic 176` (`> 23 / 4`) and `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 176`.
2. Establish seven monotone rational lower bounds `thresh n / 100 < exp γ * log (log n)` on
   `[5041, 131072)`.
3. Eliminate every `n < 131072` with `¬ 6 ∣ n` algebraically via the Euler-product upper bound
   `σ 1 n / n ≤ ∏_{p ∣ n} p / (p - 1) ≤ 37 / 10`.
4. For every multiple of `6` in `(5040, 131072)`, write `n = d * r` where `d` is the
   `{2, 3, 5, 7, 11, 13}`-smooth part and `r` is `17`-rough (so `r.primeFactors.card ≤ 3` and
   `σ 1 r / r ≤ (17 / 16) ^ r.primeFactors.card`). Enumerate all `1,019` smooth multiples `d`
   of `6` below `131072` structurally via `decide +kernel`, checking all four cases `ω(r) ∈ {0,1,2,3}`.
-/

namespace RobinRhsH2

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/- ### Part 1: Fast rational lower bounds for `exp γ * log (log n)` -/

private def harmScaled : ℕ → ℕ
  | 0 => 0
  | m + 1 => harmScaled m + 1000000 / (m + 1)

private lemma harmScaled_le_harmonic : ∀ k : ℕ,
    (harmScaled k : ℝ) / 1000000 ≤ (harmonic k : ℝ) := by
  intro k
  induction k with
  | zero => simp [harmScaled, harmonic]
  | succ m ih =>
    rw [harmScaled, harmonic_succ]
    push_cast
    have hterm : ((1000000 / (m + 1) : ℕ) : ℝ) / 1000000 ≤ ((m : ℝ) + 1)⁻¹ := by
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hdiv : ((1000000 / (m + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) ≤ 1000000 := by
        exact_mod_cast Nat.div_mul_le_self 1000000 (m + 1)
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
      have h1 : ((1000000 / (m + 1) : ℕ) : ℝ) ≤ 1000000 / ((m : ℝ) + 1) :=
        (le_div_iff₀ hm_pos).mpr hdiv
      simpa [div_eq_mul_inv, mul_comm] using h1
    linarith

private lemma exp_gamma_gt : (71 : ℝ) / 40 < exp eulerMascheroniConstant := by
  have hnat : 5750000 < harmScaled 176 := by decide +kernel
  have hsc : (23 : ℝ) / 4 < (harmScaled 176 : ℝ) / 1000000 := by
    have : (5750000 : ℝ) < (harmScaled 176 : ℝ) := by exact_mod_cast hnat
    linarith
  have hr : (23 : ℝ) / 4 < (harmonic 176 : ℝ) := hsc.trans_le (harmScaled_le_harmonic 176)
  have hγ : (harmonic 176 : ℝ) - Real.log 177 < eulerMascheroniConstant := by
    simpa only [eulerMascheroniSeq, Nat.cast_ofNat, show (176 : ℝ) + 1 = 177 by norm_num] using
      eulerMascheroniSeq_lt_eulerMascheroniConstant 176
  have he := exp_lt_exp.mpr ((sub_lt_sub_right hr (Real.log 177)).trans hγ)
  rw [exp_sub, exp_log (by norm_num : (0 : ℝ) < 177)] at he
  have hpow : ((71 : ℝ) / 40 * 177) ^ 4 < exp ((23 : ℝ) / 4) ^ 4 := by
    rw [← exp_nat_mul]
    have hmul : (4 : ℕ) * ((23 : ℝ) / 4) = 23 := by norm_num
    rw [hmul, show exp (23 : ℝ) = exp 1 ^ 23 by rw [← exp_nat_mul]; norm_num]
    have hlo : (2.71828 : ℝ) ^ 23 ≤ exp 1 ^ 23 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) 23
    have hnum : ((71 : ℝ) / 40 * 177) ^ 4 < (2.71828 : ℝ) ^ 23 := by norm_num
    exact hnum.trans_le hlo
  have hlt : (71 : ℝ) / 40 * 177 < exp ((23 : ℝ) / 4) := by
    by_contra! hle
    exact hpow.not_ge (pow_le_pow_left₀ (exp_pos _).le hle 4)
  have hdiv : (71 : ℝ) / 40 < exp ((23 : ℝ) / 4) / 177 := by linarith
  exact hdiv.trans he

private lemma robin_cutoff {n0 a1 b1 a2 b2 thr : ℕ} (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (ha1 : 0 < a1) (ha2 : 0 < a2)
    (h1 : (2.7183 : ℝ) ^ a1 < (n0 : ℝ) ^ b1)
    (h2 : (2.7183 : ℝ) ^ a2 < ((a1 : ℝ) / (b1 : ℝ)) ^ b2)
    (h3 : (thr : ℝ) / 100 < (71 : ℝ) / 40 * ((a2 : ℝ) / (b2 : ℝ)))
    {n : ℕ} (hn : n0 ≤ n) :
    (thr : ℝ) / 100 < exp eulerMascheroniConstant * log (log (n : ℝ)) := by
  have ha1_pos : (0 : ℝ) < a1 := by exact_mod_cast ha1
  have hb1_pos : (0 : ℝ) < b1 := by exact_mod_cast (Nat.pos_of_ne_zero hb1)
  have ha2_pos : (0 : ℝ) < a2 := by exact_mod_cast ha2
  have hb2_pos : (0 : ℝ) < b2 := by exact_mod_cast (Nat.pos_of_ne_zero hb2)
  have he1 : exp ((a1 : ℝ) / (b1 : ℝ)) < (n0 : ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt hb1 (Nat.cast_nonneg n0) h1
  have he2 : exp ((a2 : ℝ) / (b2 : ℝ)) < (a1 : ℝ) / (b1 : ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt hb2
      (div_nonneg ha1_pos.le hb1_pos.le) h2
  have hn0_pos : (0 : ℝ) < n0 := lt_of_lt_of_le (exp_pos _) he1.le
  have hn_ge : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (a1 : ℝ) / (b1 : ℝ) < log (n : ℝ) :=
    (lt_log_iff_exp_lt (lt_of_lt_of_le hn0_pos hn_ge)).mpr (he1.trans_le hn_ge)
  have hloglog : (a2 : ℝ) / (b2 : ℝ) < log (log (n : ℝ)) :=
    (lt_log_iff_exp_lt (lt_trans (div_pos ha1_pos hb1_pos) hlog)).mpr (he2.trans hlog)
  have hprod := mul_lt_mul'' exp_gamma_gt hloglog (by norm_num) (div_nonneg ha2_pos.le hb2_pos.le)
  exact h3.trans hprod

private def thresh (n : ℕ) : ℕ :=
  if Nat.ble 110880 n then 430
  else if Nat.ble 55440 n then 422
  else if Nat.ble 27720 n then 408
  else if Nat.ble 15120 n then 399
  else if Nat.ble 10080 n then 392
  else if Nat.ble 7560 n then 385
  else 370

private lemma thresh_mono {a b : ℕ} (hab : a ≤ b) : thresh a ≤ thresh b := by
  have hble : ∀ c : ℕ, Nat.ble c a = true → Nat.ble c b = true := fun c hc =>
    Nat.ble_eq_true_of_le ((Nat.le_of_ble_eq_true hc).trans hab)
  unfold thresh
  split_ifs <;> first
    | omega
    | (exfalso; exact ‹¬ Nat.ble 110880 b = true› (hble _ ‹Nat.ble 110880 a = true›))
    | (exfalso; exact ‹¬ Nat.ble 55440 b = true› (hble _ ‹Nat.ble 55440 a = true›))
    | (exfalso; exact ‹¬ Nat.ble 27720 b = true› (hble _ ‹Nat.ble 27720 a = true›))
    | (exfalso; exact ‹¬ Nat.ble 15120 b = true› (hble _ ‹Nat.ble 15120 a = true›))
    | (exfalso; exact ‹¬ Nat.ble 10080 b = true› (hble _ ‹Nat.ble 10080 a = true›))
    | (exfalso; exact ‹¬ Nat.ble 7560 b = true› (hble _ ‹Nat.ble 7560 a = true›))

private lemma thresh_lt_robin {n : ℕ} (hn : 5041 ≤ n) :
    (thresh n : ℝ) / 100 < exp eulerMascheroniConstant * log (log (n : ℝ)) := by
  unfold thresh
  split_ifs with h7 h6 h5 h4 h3 h2
  · exact robin_cutoff (n0 := 110880) (a1 := 23) (b1 := 2) (a2 := 17) (b2 := 7) (thr := 430)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h7)
  · exact robin_cutoff (n0 := 55440) (a1 := 76) (b1 := 7) (a2 := 31) (b2 := 13) (thr := 422)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h6)
  · exact robin_cutoff (n0 := 27720) (a1 := 10) (b1 := 1) (a2 := 23) (b2 := 10) (thr := 408)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h5)
  · exact robin_cutoff (n0 := 15120) (a1 := 19) (b1 := 2) (a2 := 9) (b2 := 4) (thr := 399)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h4)
  · exact robin_cutoff (n0 := 10080) (a1 := 46) (b1 := 5) (a2 := 31) (b2 := 14) (thr := 392)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h3)
  · exact robin_cutoff (n0 := 7560) (a1 := 71) (b1 := 8) (a2 := 24) (b2 := 11) (thr := 385)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (Nat.le_of_ble_eq_true h2)
  · exact robin_cutoff (n0 := 5041) (a1 := 17) (b1 := 2) (a2 := 17) (b2 := 8) (thr := 370)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) hn

/- ### Part 2: Euler-product bounds for `¬ 6 ∣ n` and `17`-rough cofactors -/

private lemma sigma_le_euler_prod {n : ℕ} (hn : n ≠ 0) :
    (σ 1 n : ℝ) ≤ (n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hfac : ∀ p ∈ n.primeFactors,
      (∑ i ∈ range (n.factorization p + 1), (p : ℝ) ^ i) ≤
        (p : ℝ) ^ n.factorization p * ((p : ℝ) / ((p : ℝ) - 1)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    rw [← mul_div_assoc, le_div_iff₀ (by linarith), geom_sum_mul, pow_succ]
    linarith
  calc (σ 1 n : ℝ) = ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p + 1), (p : ℝ) ^ i := by
        simp only [sigma_one_apply, Nat.sum_divisors hn, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow]
    _ ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p * ((p : ℝ) / ((p : ℝ) - 1))) :=
        prod_le_prod (fun _ _ => by positivity) hfac
    _ = (n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
        rw [prod_mul_distrib, hprod]

private lemma prod_primeFactors_le {n : ℕ} (hn : 0 < n) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ≤ n := by
  have hdvd : (∏ p ∈ S, p) ∣ n := by
    have h1 : (∏ p ∈ S, p) ∣ (∏ p ∈ n.primeFactors, p) := Finset.prod_dvd_prod_of_subset _ _ _ hS
    exact h1.trans (Nat.prod_primeFactors_dvd n)
  exact Nat.le_of_dvd hn hdvd

private lemma card_large_primes_le_four {n : ℕ} (hn0 : 0 < n) (hn : n < 131072) :
    (n.primeFactors.filter (11 ≤ ·)).card ≤ 4 := by
  by_contra! hge
  have h1 : 11 ^ (n.primeFactors.filter (11 ≤ ·)).card ≤ ∏ p ∈ n.primeFactors.filter (11 ≤ ·), p := by
    calc 11 ^ (n.primeFactors.filter (11 ≤ ·)).card
        = ∏ _p ∈ n.primeFactors.filter (11 ≤ ·), 11 := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ n.primeFactors.filter (11 ≤ ·), p :=
          Finset.prod_le_prod' fun p hp => (Finset.mem_filter.mp hp).2
  have h2 : 11 ^ 5 ≤ 11 ^ (n.primeFactors.filter (11 ≤ ·)).card :=
    Nat.pow_le_pow_right (by omega) hge
  have h3 : ∏ p ∈ n.primeFactors.filter (11 ≤ ·), p ≤ n :=
    prod_primeFactors_le hn0 _ (Finset.filter_subset (11 ≤ ·) n.primeFactors)
  omega

private lemma card_large_primes_le_two_of_70_dvd {n : ℕ} (hn0 : 0 < n) (hn : n < 131072)
    (h2 : 2 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) :
    (n.primeFactors.filter (11 ≤ ·)).card ≤ 2 := by
  set S := n.primeFactors.filter (11 ≤ ·)
  by_contra! hge
  have hmem2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h2, hn0.ne'⟩
  have hmem5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h5, hn0.ne'⟩
  have hmem7 : 7 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h7, hn0.ne'⟩
  have hdisj : Disjoint ({2, 5, 7} : Finset ℕ) S := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have := (Finset.mem_filter.mp hp2).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1
    omega
  have hsub : {2, 5, 7} ∪ S ⊆ n.primeFactors := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp1
      rcases hp1 with rfl | rfl | rfl <;> assumption
    · exact (Finset.mem_filter.mp hp2).1
  have hprod_le : (∏ p ∈ ({2, 5, 7} : Finset ℕ), p) * (∏ p ∈ S, p) ≤ n := by
    rw [← Finset.prod_union hdisj]
    exact prod_primeFactors_le hn0 _ hsub
  have h70 : ∏ p ∈ ({2, 5, 7} : Finset ℕ), p = 70 := by decide
  have hS_prod : 2431 ≤ ∏ p ∈ S, p := by
    have hprimeS : ∀ p ∈ S, p.Prime ∧ 11 ≤ p := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hgt17 : ∀ p ∈ S, p ≠ 11 → p ≠ 13 → 17 ≤ p := by
      intro p hp h11 h13
      have ⟨hpr, h11le⟩ := hprimeS p hp
      by_contra! hlt
      have : p = 12 ∨ p = 14 ∨ p = 15 ∨ p = 16 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> norm_num at hpr
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
    have hsub3 : ({a, b, c} : Finset ℕ) ⊆ S := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3le : a * b * c ≤ ∏ p ∈ S, p := by
      have heq : ∏ p ∈ ({a, b, c} : Finset ℕ), p = a * b * c := by
        rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
          Finset.prod_singleton]; ring
      rw [← heq]
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub3 fun p hp _ =>
        (hprimeS p hp).1.one_le
    have ha11 := (hprimeS a ha).2
    have hb11 := (hprimeS b hb).2
    have hc11 := (hprimeS c hc).2
    have hmul3 : ∀ x y z : ℕ, 11 ≤ x → 17 ≤ y → 17 ≤ z → 2431 ≤ x * y * z := fun x y z hx hy hz =>
      calc 2431 ≤ 11 * 17 * 17 := by decide
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
    have hmul3' : ∀ x y z : ℕ, (x = 11 ∨ x = 13) → (y = 11 ∨ y = 13) → x ≠ y → 17 ≤ z →
        2431 ≤ x * y * z := by
      intro x y z hx hy hxy hz
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
    have hmul_comm : ∀ x y z : ℕ, x * y * z = a * b * c → 2431 ≤ x * y * z → 2431 ≤ ∏ p ∈ S, p :=
      fun _ _ _ heq hle => hle.trans (heq ▸ h3le)
    by_cases ha1 : a = 11 ∨ a = 13 <;> by_cases hb1 : b = 11 ∨ b = 13 <;> by_cases hc1 : c = 11 ∨ c = 13
    · omega
    · exact hmul_comm a b c rfl (hmul3' a b c ha1 hb1 hab (hgt17 c hc (by tauto) (by tauto)))
    · exact hmul_comm a c b (by ring) (hmul3' a c b ha1 hc1 hac (hgt17 b hb (by tauto) (by tauto)))
    · exact hmul_comm a b c rfl (hmul3 a b c ha11 (hgt17 b hb (by tauto) (by tauto)) (hgt17 c hc (by tauto) (by tauto)))
    · exact hmul_comm b c a (by ring) (hmul3' b c a hb1 hc1 hbc (hgt17 a ha (by tauto) (by tauto)))
    · exact hmul_comm b a c (by ring) (hmul3 b a c hb11 (hgt17 a ha (by tauto) (by tauto)) (hgt17 c hc (by tauto) (by tauto)))
    · exact hmul_comm c a b (by ring) (hmul3 c a b hc11 (hgt17 a ha (by tauto) (by tauto)) (hgt17 b hb (by tauto) (by tauto)))
    · exact hmul_comm a b c rfl (hmul3 a b c ha11 (hgt17 b hb (by tauto) (by tauto)) (hgt17 c hc (by tauto) (by tauto)))
  rw [h70] at hprod_le
  omega

private lemma prod_div_pred_le_of_not_dvd_six {n : ℕ} (hn0 : 0 < n) (hn : n < 131072)
    (h6 : ¬ 6 ∣ n) :
    ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) ≤ (37 : ℝ) / 10 := by
  have hterm_nn : ∀ p ∈ n.primeFactors, (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := fun p hp => by
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (by linarith) (by linarith)
  have hsplit : ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) =
      (∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ n.primeFactors.filter (11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]
  have hlarge : ∏ p ∈ n.primeFactors.filter (11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
      (11 / 10 : ℝ) ^ (n.primeFactors.filter (11 ≤ ·)).card := by
    calc ∏ p ∈ n.primeFactors.filter (11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∏ _p ∈ n.primeFactors.filter (11 ≤ ·), (11 / 10 : ℝ) := by
          apply Finset.prod_le_prod (fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1)
          intro p hp
          have hp11 : (11 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      _ = (11 / 10 : ℝ) ^ (n.primeFactors.filter (11 ≤ ·)).card := Finset.prod_const _
  have hsmall_sub : ∀ (S : Finset ℕ), n.primeFactors.filter (¬ 11 ≤ ·) ⊆ S →
      (∀ p ∈ S, 1 < p) →
      ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
        ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    intro S hsub hgt
    rw [← Finset.prod_sdiff hsub]
    have h1 : (1 : ℝ) ≤ ∏ p ∈ S \ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) := by
      calc (1 : ℝ) = ∏ _p ∈ S \ n.primeFactors.filter (¬ 11 ≤ ·), (1 : ℝ) :=
            Finset.prod_const_one.symm
        _ ≤ ∏ p ∈ S \ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) :=
            Finset.prod_le_prod (fun _ _ => zero_le_one) fun p hp => by
              have hp1 : (1 : ℝ) < p := by exact_mod_cast hgt p (Finset.mem_sdiff.mp hp).1
              rw [one_le_div (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) :=
      Finset.prod_nonneg fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1
    nlinarith
  have hsmall_mem : ∀ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hlt : p < 11 := by have := (Finset.mem_filter.mp hp).2; omega
    have hge2 := hpr.two_le
    interval_cases p <;> first | decide | (exfalso; exact absurd hpr (by decide))
  have hcard4 := card_large_primes_le_four hn0 hn
  have hpow4 : (11 / 10 : ℝ) ^ (n.primeFactors.filter (11 ≤ ·)).card ≤ (11 / 10 : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by norm_num) hcard4
  rw [hsplit]
  by_cases h2 : 2 ∣ n
  · have h3 : ¬ 3 ∣ n := fun h3 => h6 (by omega)
    have hnot3 : 3 ∉ n.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
    by_cases h5 : 5 ∣ n
    · by_cases h7 : 7 ∣ n
      · have hcard2 := card_large_primes_le_two_of_70_dvd hn0 hn h2 h5 h7
        have hpow2 : (11 / 10 : ℝ) ^ (n.primeFactors.filter (11 ≤ ·)).card ≤ (11 / 10 : ℝ) ^ 2 :=
          pow_le_pow_right₀ (by norm_num) hcard2
        have hsm : ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
            ∏ p ∈ ({2, 5, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) :=
          hsmall_sub {2, 5, 7} (fun p hp => by
            rcases hsmall_mem p hp with rfl | rfl | rfl | rfl
            · simp
            · exact absurd (Finset.mem_filter.mp hp).1 hnot3
            · simp
            · simp) (by decide)
        have hval : ∏ p ∈ ({2, 5, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) = 35 / 12 := by norm_num
        rw [hval] at hsm
        calc _ ≤ (35 / 12 : ℝ) * (11 / 10 : ℝ) ^ 2 :=
              mul_le_mul hsm (hlarge.trans hpow2)
                (Finset.prod_nonneg fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1) (by norm_num)
          _ ≤ 37 / 10 := by norm_num
      · have hnot7 : 7 ∉ n.primeFactors := fun h => h7 (Nat.dvd_of_mem_primeFactors h)
        have hsm : ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
            ∏ p ∈ ({2, 5} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) :=
          hsmall_sub {2, 5} (fun p hp => by
            rcases hsmall_mem p hp with rfl | rfl | rfl | rfl
            · simp
            · exact absurd (Finset.mem_filter.mp hp).1 hnot3
            · simp
            · exact absurd (Finset.mem_filter.mp hp).1 hnot7) (by decide)
        have hval : ∏ p ∈ ({2, 5} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) = 5 / 2 := by norm_num
        rw [hval] at hsm
        calc _ ≤ (5 / 2 : ℝ) * (11 / 10 : ℝ) ^ 4 :=
              mul_le_mul hsm (hlarge.trans hpow4)
                (Finset.prod_nonneg fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1) (by norm_num)
          _ ≤ 37 / 10 := by norm_num
    · have hnot5 : 5 ∉ n.primeFactors := fun h => h5 (Nat.dvd_of_mem_primeFactors h)
      have hsm : ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
          ∏ p ∈ ({2, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) :=
        hsmall_sub {2, 7} (fun p hp => by
          rcases hsmall_mem p hp with rfl | rfl | rfl | rfl
          · simp
          · exact absurd (Finset.mem_filter.mp hp).1 hnot3
          · exact absurd (Finset.mem_filter.mp hp).1 hnot5
          · simp) (by decide)
      have hval : ∏ p ∈ ({2, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) = 7 / 3 := by norm_num
      rw [hval] at hsm
      calc _ ≤ (7 / 3 : ℝ) * (11 / 10 : ℝ) ^ 4 :=
            mul_le_mul hsm (hlarge.trans hpow4)
              (Finset.prod_nonneg fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1) (by norm_num)
        _ ≤ 37 / 10 := by norm_num
  · have hnot2 : 2 ∉ n.primeFactors := fun h => h2 (Nat.dvd_of_mem_primeFactors h)
    have hsm : ∏ p ∈ n.primeFactors.filter (¬ 11 ≤ ·), (p : ℝ) / ((p : ℝ) - 1) ≤
        ∏ p ∈ ({3, 5, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) :=
      hsmall_sub {3, 5, 7} (fun p hp => by
        rcases hsmall_mem p hp with rfl | rfl | rfl | rfl
        · exact absurd (Finset.mem_filter.mp hp).1 hnot2
        · simp
        · simp
        · simp) (by decide)
    have hval : ∏ p ∈ ({3, 5, 7} : Finset ℕ), (p : ℝ) / ((p : ℝ) - 1) = 35 / 16 := by norm_num
    rw [hval] at hsm
    calc _ ≤ (35 / 16 : ℝ) * (11 / 10 : ℝ) ^ 4 :=
          mul_le_mul hsm (hlarge.trans hpow4)
            (Finset.prod_nonneg fun p hp => hterm_nn p (Finset.mem_filter.mp hp).1) (by norm_num)
      _ ≤ 37 / 10 := by norm_num

/- ### Part 3: Structurally enumerating all 1,019 smooth multiples of 6 below 131072 -/

private lemma sigma_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ (k + 1)) = 1 + p * σ 1 (p ^ k) := by
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp,
    Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  conv_lhs => rw [Finset.sum_range_succ', pow_zero, add_comm]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ']

private def okSmooth (d sd : ℕ) : Bool :=
  (Nat.ble d 5040 || Nat.ble (100 * sd) (thresh d * d)) &&
  (Nat.ble 131072 (17 * d) || Nat.ble (100 * sd * 17) (thresh (max 5041 (17 * d)) * d * 16)) &&
  (Nat.ble 131072 (289 * d) || Nat.ble (100 * sd * 289) (thresh (max 5041 (289 * d)) * d * 256)) &&
  (Nat.ble 131072 (4913 * d) || Nat.ble (100 * sd * 4913) (thresh (max 5041 (4913 * d)) * d * 4096))

private def forPow (p : ℕ) (cont : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, d, sd, pp, sp =>
    if Nat.ble 131072 (d * pp) then true
    else cont (d * pp) (sd * sp) && forPow p cont fuel d sd (pp * p) (1 + p * sp)

private lemma forPow_spec {p : ℕ} (hp : p.Prime) (cont : ℕ → ℕ → Bool) :
    ∀ (fuel d sd k0 : ℕ),
      forPow p cont fuel d sd (p ^ k0) (σ 1 (p ^ k0)) = true →
      ∀ k : ℕ, k0 ≤ k → k < k0 + fuel → d * p ^ k < 131072 →
        cont (d * p ^ k) (sd * σ 1 (p ^ k)) = true := by
  intro fuel
  induction fuel with
  | zero => intro d sd k0 _ k h1 h2 _; omega
  | succ f ih =>
    intro d sd k0 hfp k hk0 hkf hlt
    have hlt0 : d * p ^ k0 < 131072 := by
      have hpow : p ^ k0 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk0
      exact lt_of_le_of_lt (Nat.mul_le_mul_left d hpow) hlt
    have hble_false : Nat.ble 131072 (d * p ^ k0) = false := by
      cases h : Nat.ble 131072 (d * p ^ k0)
      · rfl
      · exfalso; have := Nat.le_of_ble_eq_true h; omega
    rw [forPow, if_neg (by simp [hble_false]), Bool.and_eq_true] at hfp
    rcases eq_or_lt_of_le hk0 with rfl | hgt
    · exact hfp.1
    · have hrec : forPow p cont f d sd (p ^ (k0 + 1)) (σ 1 (p ^ (k0 + 1))) = true := by
        rw [sigma_prime_pow_succ hp, pow_succ]
        exact hfp.2
      exact ih d sd (k0 + 1) hrec k (by omega) (by omega) hlt

private def checkAllSmooth : Bool :=
  forPow 2 (fun d2 s2 =>
  forPow 3 (fun d3 s3 =>
  forPow 5 (fun d5 s5 =>
  forPow 7 (fun d7 s7 =>
  forPow 11 (fun d11 s11 =>
  forPow 13 okSmooth 5 d11 s11 1 1)
  5 d7 s7 1 1)
  6 d5 s5 1 1)
  8 d3 s3 1 1)
  11 d2 s2 3 4)
  17 1 1 2 3

private lemma checkAllSmooth_ok : checkAllSmooth = true := by
  decide +kernel

private lemma okSmooth_of_exps {a b c e f g : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hlt : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g < 131072) :
    okSmooth (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g)
      (σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (5 ^ c) * σ 1 (7 ^ e) * σ 1 (11 ^ f) * σ 1 (13 ^ g)) = true := by
  have h5 : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f < 131072 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) hlt
  have h4 : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e < 131072 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) h5
  have h3 : 2 ^ a * 3 ^ b * 5 ^ c < 131072 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) h4
  have h2 : 2 ^ a * 3 ^ b < 131072 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) h3
  have h1 : 2 ^ a < 131072 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) h2
  have ha_lt : a < 1 + 17 := by
    by_contra! hge
    have : 2 ^ 18 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) hge
    omega
  have hb_lt : b < 1 + 11 := by
    by_contra! hge
    have hpow : 3 ^ 12 ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) hge
    have hle : 3 ^ 12 ≤ 2 ^ a * 3 ^ b := hpow.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega
  have hc_lt : c < 0 + 8 := by
    by_contra! hge
    have hpow : 5 ^ 8 ≤ 5 ^ c := Nat.pow_le_pow_right (by omega) hge
    have hle : 5 ^ 8 ≤ 2 ^ a * 3 ^ b * 5 ^ c := hpow.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega
  have he_lt : e < 0 + 6 := by
    by_contra! hge
    have h2 : 2 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha)
    have h3 : 3 ≤ 3 ^ b := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hb)
    have h6ab : 6 ≤ 2 ^ a * 3 ^ b := by nlinarith
    have h6abc : 6 ≤ 2 ^ a * 3 ^ b * 5 ^ c :=
      h6ab.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hpow : 7 ^ 6 ≤ 7 ^ e := Nat.pow_le_pow_right (by omega) hge
    have hle : 6 * 7 ^ 6 ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e := Nat.mul_le_mul h6abc hpow
    omega
  have hf_lt : f < 0 + 5 := by
    by_contra! hge
    have hpow : 11 ^ 5 ≤ 11 ^ f := Nat.pow_le_pow_right (by omega) hge
    have hle : 11 ^ 5 ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f := hpow.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega
  have hg_lt : g < 0 + 5 := by
    by_contra! hge
    have hpow : 13 ^ 5 ≤ 13 ^ g := Nat.pow_le_pow_right (by omega) hge
    have hle : 13 ^ 5 ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g := hpow.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega
  have hs2 : σ 1 2 = 3 := by decide
  have hs3 : σ 1 3 = 4 := by decide
  have hs1 : σ 1 1 = 1 := by decide
  have step1 := forPow_spec (by decide : Nat.Prime 2) _ 17 1 1 1
    (by rw [pow_one, hs2]; exact checkAllSmooth_ok) a ha ha_lt (by simpa using h1)
  simp only [one_mul] at step1
  have step2 := forPow_spec (by decide : Nat.Prime 3) _ 11 (2 ^ a) (σ 1 (2 ^ a)) 1
    (by rw [pow_one, hs3]; exact step1) b hb hb_lt h2
  have step3 := forPow_spec (by decide : Nat.Prime 5) _ 8 (2 ^ a * 3 ^ b) (σ 1 (2 ^ a) * σ 1 (3 ^ b)) 0
    (by rw [pow_zero, hs1]; exact step2) c (Nat.zero_le c) hc_lt h3
  have step4 := forPow_spec (by decide : Nat.Prime 7) _ 6
    (2 ^ a * 3 ^ b * 5 ^ c) (σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (5 ^ c)) 0
    (by rw [pow_zero, hs1]; exact step3) e (Nat.zero_le e) he_lt h4
  have step5 := forPow_spec (by decide : Nat.Prime 11) _ 5
    (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e) (σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (5 ^ c) * σ 1 (7 ^ e)) 0
    (by rw [pow_zero, hs1]; exact step4) f (Nat.zero_le f) hf_lt h5
  exact forPow_spec (by decide : Nat.Prime 13) okSmooth 5
    (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f)
    (σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (5 ^ c) * σ 1 (7 ^ e) * σ 1 (11 ^ f)) 0
    (by rw [pow_zero, hs1]; exact step5) g (Nat.zero_le g) hg_lt hlt

private lemma sigma_smooth_mul_rough {n : ℕ} (hn_lo : 5040 < n) (hn_hi : n < 131072) (h6 : 6 ∣ n) :
    (σ 1 n : ℝ) ≤ ((thresh n : ℝ) / 100) * (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hn_pos : 0 < n := by omega
  let a := n.factorization 2
  let b := n.factorization 3
  let c := n.factorization 5
  let e := n.factorization 7
  let f := n.factorization 11
  let g := n.factorization 13
  let d := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g
  have hmem_fac : ∀ p : ℕ, p.Prime → p ∣ n → 1 ≤ n.factorization p := fun p hp hpn =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩))
  have ha : 1 ≤ a := hmem_fac 2 (by decide) (dvd_trans (by decide) h6)
  have hb : 1 ≤ b := hmem_fac 3 (by decide) (dvd_trans (by decide) h6)
  have hd_eq_prod : d = ∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), p ^ n.factorization p := by
    have : ({2, 3, 5, 7, 11, 13} : Finset ℕ) =
        insert 2 (insert 3 (insert 5 (insert 7 (insert 11 {13})))) := rfl
    rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    dsimp only [d, a, b, c, e, f, g]; ring
  have hd_dvd_n : d ∣ n := by
    have hsplit : n = (∏ p ∈ n.primeFactors.filter (· ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ)),
          p ^ n.factorization p) *
        (∏ p ∈ n.primeFactors.filter (· ∉ ({2, 3, 5, 7, 11, 13} : Finset ℕ)),
          p ^ n.factorization p) := by
      rw [Finset.prod_filter_mul_prod_filter_not]
      exact Nat.prod_primeFactors_pow_factorization hn0
    have hpart_eq : d = ∏ p ∈ n.primeFactors.filter (· ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ)),
        p ^ n.factorization p := by
      rw [hd_eq_prod]
      symm
      apply Finset.prod_subset (fun p hp => (Finset.mem_filter.mp hp).2)
      intro p hp hnot
      rw [Finset.mem_filter] at hnot
      have hnpf : p ∉ n.primeFactors := fun h => hnot ⟨h, hp⟩
      have hfz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hnpf
      simp [hfz]
    rw [hpart_eq]
    exact ⟨_, hsplit⟩
  let r := n / d
  have hmul : d * r = n := Nat.mul_div_cancel' hd_dvd_n
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_n hn_pos
  have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd hn_pos hd_dvd_n) hd_pos
  have hd_ge6 : 6 ≤ d := by
    have h2 : 2 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha)
    have h3 : 3 ≤ 3 ^ b := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hb)
    have h6ab : 6 ≤ 2 ^ a * 3 ^ b := by nlinarith
    have hrest : 1 ≤ 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g := Nat.succ_le_of_lt (by positivity)
    dsimp only [d]
    calc 6 = 6 * 1 := by ring
      _ ≤ (2 ^ a * 3 ^ b) * (5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g) := Nat.mul_le_mul h6ab hrest
      _ = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f * 13 ^ g := by ring
  have hd_lt : d < 131072 := lt_of_le_of_lt (Nat.le_of_dvd hn_pos hd_dvd_n) hn_hi
  have hndiv_r : ∀ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), ¬ p ∣ r := by
    intro p hp hpr
    have hprime : p.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hpd : p ^ n.factorization p ∣ d := by
      rw [hd_eq_prod]; exact Finset.dvd_prod_of_mem _ hp
    have hpow1 : p ^ (n.factorization p + 1) ∣ n := by
      rw [pow_succ]
      calc p ^ n.factorization p * p ∣ d * r := mul_dvd_mul hpd hpr
        _ = n := hmul
    have hle := hprime.pow_dvd_iff_le_factorization hn0 |>.mp hpow1
    omega
  have h17 : ∀ p ∈ r.primeFactors, 17 ≤ p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hge2 := hpr.two_le
    by_contra! hlt
    have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
      interval_cases p <;> first | decide | (exfalso; exact absurd hpr (by decide))
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hndiv_r _ (by simp) hdvd
  have hcop_dr : Nat.Coprime d r := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpr
    have hp17 := h17 p (Nat.mem_primeFactors.mpr ⟨hp, hpr, hr_pos.ne'⟩)
    rw [hd_eq_prod] at hpd
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff (fun q => q ^ n.factorization q)).mp hpd
    have hqprime : q.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpq)
    subst hp_eq_q
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  have hsig_d : σ 1 d = σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (5 ^ c) * σ 1 (7 ^ e) *
      σ 1 (11 ^ f) * σ 1 (13 ^ g) := by
    have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
    have hcop_pow : ∀ {p q k l : ℕ}, p.Prime → q.Prime → p ≠ q → Nat.Coprime (p ^ k) (q ^ l) :=
      fun hp hq hne => ((Nat.coprime_primes hp hq).mpr hne).pow _ _
    have h12 : Nat.Coprime (2 ^ a) (3 ^ b) := hcop_pow (by decide) (by decide) (by decide)
    have h123 : Nat.Coprime (2 ^ a * 3 ^ b) (5 ^ c) :=
      (hcop_pow (by decide) (by decide) (by decide)).mul_left (hcop_pow (by decide) (by decide) (by decide))
    have h1234 : Nat.Coprime (2 ^ a * 3 ^ b * 5 ^ c) (7 ^ e) :=
      ((hcop_pow (by decide) (by decide) (by decide)).mul_left (hcop_pow (by decide) (by decide) (by decide))).mul_left
        (hcop_pow (by decide) (by decide) (by decide))
    have h12345 : Nat.Coprime (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e) (11 ^ f) :=
      (((hcop_pow (by decide) (by decide) (by decide)).mul_left (hcop_pow (by decide) (by decide) (by decide))).mul_left
        (hcop_pow (by decide) (by decide) (by decide))).mul_left (hcop_pow (by decide) (by decide) (by decide))
    have h123456 : Nat.Coprime (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ e * 11 ^ f) (13 ^ g) :=
      ((((hcop_pow (by decide) (by decide) (by decide)).mul_left (hcop_pow (by decide) (by decide) (by decide))).mul_left
        (hcop_pow (by decide) (by decide) (by decide))).mul_left (hcop_pow (by decide) (by decide) (by decide))).mul_left
        (hcop_pow (by decide) (by decide) (by decide))
    dsimp only [d]
    rw [hm.map_mul_of_coprime h123456, hm.map_mul_of_coprime h12345,
      hm.map_mul_of_coprime h1234, hm.map_mul_of_coprime h123, hm.map_mul_of_coprime h12]
  have hsig_n : σ 1 n = σ 1 d * σ 1 r := by
    rw [← hmul, (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop_dr]
  have hok := okSmooth_of_exps ha hb hd_lt
  rw [← hsig_d] at hok
  simp only [okSmooth, Bool.and_eq_true, Bool.or_eq_true] at hok
  have h17pow : 17 ^ r.primeFactors.card ≤ r := by
    calc 17 ^ r.primeFactors.card
        = ∏ _p ∈ r.primeFactors, 17 := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ r.primeFactors, p := Finset.prod_le_prod' h17
      _ ≤ r := prod_primeFactors_le hr_pos _ subset_rfl
  have hsig_r : (σ 1 r : ℝ) ≤ (r : ℝ) * (17 / 16 : ℝ) ^ r.primeFactors.card := by
    refine (sigma_le_euler_prod hr_pos.ne').trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r))
    calc ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∏ _p ∈ r.primeFactors, (17 / 16 : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp17 : (17 : ℝ) ≤ p := by exact_mod_cast h17 p hp
            exact div_nonneg (by linarith) (by linarith)
          · intro p hp
            have hp17 : (17 : ℝ) ≤ p := by exact_mod_cast h17 p hp
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      _ = (17 / 16 : ℝ) ^ r.primeFactors.card := Finset.prod_const _
  have hcard_le3 : r.primeFactors.card ≤ 3 := by
    by_contra! hge
    have h4 : 17 ^ 4 ≤ 17 ^ r.primeFactors.card := Nat.pow_le_pow_right (by omega) hge
    have hmul6 : 6 * 17 ^ 4 ≤ d * r := Nat.mul_le_mul hd_ge6 (h4.trans h17pow)
    omega
  have hmulR : (n : ℝ) = (d : ℝ) * (r : ℝ) := by exact_mod_cast hmul.symm
  have hdR_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  have hrR_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr_pos
  have hcard_cases : r.primeFactors.card = 0 ∨ r.primeFactors.card = 1 ∨
      r.primeFactors.card = 2 ∨ r.primeFactors.card = 3 := by omega
  rcases hcard_cases with hk | hk | hk | hk
  · have hr1 : r = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hne
      have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpr, hr_pos.ne'⟩
      have := Finset.card_pos.mpr ⟨p, hmem⟩
      omega
    have hdn : d = n := by rw [← hmul, hr1, mul_one]
    rcases hok.1.1.1 with hbad | hgood
    · exfalso; have hle := Nat.le_of_ble_eq_true hbad; change d ≤ 5040 at hle; omega
    · have hnat := Nat.le_of_ble_eq_true hgood
      change 100 * σ 1 d ≤ thresh d * d at hnat
      rw [hdn] at hnat
      have hcast : (100 : ℝ) * (σ 1 n : ℝ) ≤ (thresh n : ℝ) * (n : ℝ) := by exact_mod_cast hnat
      ring_nf at hcast ⊢
      linarith
  · have hr17 : 17 ≤ r := by rw [hk] at h17pow; norm_num at h17pow; exact h17pow
    have h17d_lt : 17 * d < 131072 := by
      have : 17 * d ≤ d * r := by rw [mul_comm]; exact Nat.mul_le_mul_left d hr17
      omega
    rcases hok.1.1.2 with hbad | hgood
    · exfalso; have := Nat.le_of_ble_eq_true hbad; omega
    · have hnat := Nat.le_of_ble_eq_true hgood
      have hth : thresh (max 5041 (17 * d)) ≤ thresh n :=
        thresh_mono (max_le (by omega) (by rw [← hmul, mul_comm]; exact Nat.mul_le_mul_left d hr17))
      have hnat2 : 100 * σ 1 d * 17 ≤ thresh n * d * 16 :=
        hnat.trans (Nat.mul_le_mul_right 16 (Nat.mul_le_mul_right d hth))
      have hcast : (100 : ℝ) * (σ 1 d : ℝ) * 17 ≤ (thresh n : ℝ) * (d : ℝ) * 16 := by exact_mod_cast hnat2
      rw [hk] at hsig_r; norm_num at hsig_r
      have h1 := mul_le_mul_of_nonneg_left hsig_r (Nat.cast_nonneg (σ 1 d))
      have h2 := mul_le_mul_of_nonneg_right hcast hrR_pos.le
      rw [hsig_n, Nat.cast_mul, hmulR]
      ring_nf at h1 h2 ⊢
      linarith only [h1, h2]
  · have hr289 : 289 ≤ r := by rw [hk] at h17pow; norm_num at h17pow; exact h17pow
    have h289d_lt : 289 * d < 131072 := by
      have : 289 * d ≤ d * r := by rw [mul_comm]; exact Nat.mul_le_mul_left d hr289
      omega
    rcases hok.1.2 with hbad | hgood
    · exfalso; have := Nat.le_of_ble_eq_true hbad; omega
    · have hnat := Nat.le_of_ble_eq_true hgood
      have hth : thresh (max 5041 (289 * d)) ≤ thresh n :=
        thresh_mono (max_le (by omega) (by rw [← hmul, mul_comm]; exact Nat.mul_le_mul_left d hr289))
      have hnat2 : 100 * σ 1 d * 289 ≤ thresh n * d * 256 :=
        hnat.trans (Nat.mul_le_mul_right 256 (Nat.mul_le_mul_right d hth))
      have hcast : (100 : ℝ) * (σ 1 d : ℝ) * 289 ≤ (thresh n : ℝ) * (d : ℝ) * 256 := by exact_mod_cast hnat2
      rw [hk] at hsig_r; norm_num at hsig_r
      have h1 := mul_le_mul_of_nonneg_left hsig_r (Nat.cast_nonneg (σ 1 d))
      have h2 := mul_le_mul_of_nonneg_right hcast hrR_pos.le
      rw [hsig_n, Nat.cast_mul, hmulR]
      ring_nf at h1 h2 ⊢
      linarith only [h1, h2]
  · have hr4913 : 4913 ≤ r := by rw [hk] at h17pow; norm_num at h17pow; exact h17pow
    have h4913d_lt : 4913 * d < 131072 := by
      have : 4913 * d ≤ d * r := by rw [mul_comm]; exact Nat.mul_le_mul_left d hr4913
      omega
    rcases hok.2 with hbad | hgood
    · exfalso; have := Nat.le_of_ble_eq_true hbad; omega
    · have hnat := Nat.le_of_ble_eq_true hgood
      have hth : thresh (max 5041 (4913 * d)) ≤ thresh n :=
        thresh_mono (max_le (by omega) (by rw [← hmul, mul_comm]; exact Nat.mul_le_mul_left d hr4913))
      have hnat2 : 100 * σ 1 d * 4913 ≤ thresh n * d * 4096 :=
        hnat.trans (Nat.mul_le_mul_right 4096 (Nat.mul_le_mul_right d hth))
      have hcast : (100 : ℝ) * (σ 1 d : ℝ) * 4913 ≤ (thresh n : ℝ) * (d : ℝ) * 4096 := by exact_mod_cast hnat2
      rw [hk] at hsig_r; norm_num at hsig_r
      have h1 := mul_le_mul_of_nonneg_left hsig_r (Nat.cast_nonneg (σ 1 d))
      have h2 := mul_le_mul_of_nonneg_right hcast hrR_pos.le
      rw [hsig_n, Nat.cast_mul, hmulR]
      ring_nf at h1 h2 ⊢
      linarith only [h1, h2]

end RobinRhsH2

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.H2 := by
  intro n hn_lo hn_hi _
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  by_cases h6 : 6 ∣ n
  · have hsig_le := RobinRhsH2.sigma_smooth_mul_rough hn_lo hn_hi h6
    have hcut := RobinRhsH2.thresh_lt_robin (n := n) (by omega)
    have hlt := mul_lt_mul_of_pos_right hcut hn_posR
    calc (ArithmeticFunction.sigma 1 n : ℝ)
        ≤ ((RobinRhsH2.thresh n : ℝ) / 100) * (n : ℝ) := hsig_le
      _ < (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) * (n : ℝ) := hlt
      _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
  · have hsig_le := RobinRhsH2.sigma_le_euler_prod hn_pos.ne'
    have hprod := RobinRhsH2.prod_div_pred_le_of_not_dvd_six hn_pos hn_hi h6
    have hcut : (37 : ℝ) / 10 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
      have h := RobinRhsH2.robin_cutoff (n0 := 5041) (a1 := 17) (b1 := 2) (a2 := 17) (b2 := 8)
        (thr := 370) (by decide) (by decide) (by decide) (by decide)
        (by norm_num) (by norm_num) (by norm_num) (by omega : 5041 ≤ n)
      norm_num at h
      exact h
    calc (ArithmeticFunction.sigma 1 n : ℝ)
        ≤ (n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hsig_le
      _ ≤ (n : ℝ) * ((37 : ℝ) / 10) := mul_le_mul_of_nonneg_left hprod hn_posR.le
      _ < (n : ℝ) * (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) :=
          mul_lt_mul_of_pos_left hcut hn_posR
      _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
