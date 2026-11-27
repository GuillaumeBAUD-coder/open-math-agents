import OMAStatements.S_oeis_a201488

-- Problem: A201488: Decimal expansion of maximal quantum success probability of the CHSH game.
-- Upstream: formal-conjectures statements/oeis-a201488.lean:0 (declaration OMA.S_oeis_a201488.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Idea. With phi(q) the sum of q^(k^2) over all integers k, the claim is
-- (phi(q^2)/phi(q))^2 = (2 + sqrt 2)/4 at q = exp(-pi).
-- * Two doubling identities for T(t) = sum_k exp(-pi t k^2) and its alternating
--   companion U(t), proved by reindexing the double sum along (a, b) -> (a+b, a-b):
--   T(t)^2 + U(t)^2 = 2 T(2t)^2 and T(t) U(t) = U(2t)^2.
-- * Poisson summation gives T(1/2) = sqrt 2 * T(2). Together these force the value.
-- * Evaluation of an absolutely summable integer power series at exp(-pi) is
--   multiplicative (Cauchy product), and the inverse of the theta series is absolutely
--   summable there by a majorant bound.

namespace A201488

/-- The sign `(-1)^n` of an integer. -/
noncomputable def sg (n : ℤ) : ℝ := if Even n then 1 else -1

/-- The Gaussian term `exp (-pi t n^2)`. -/
noncomputable def ge (t : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

/-- The term of index `n` of an integer power series evaluated at `r`. -/
noncomputable def tm (r : ℝ) (f : PowerSeries ℤ) (n : ℕ) : ℝ :=
  ((PowerSeries.coeff n f : ℤ) : ℝ) * r ^ n

lemma sg_abs (n : ℤ) : |sg n| = 1 := by
  unfold sg; split_ifs <;> simp

lemma sg_add (a b : ℤ) : sg (a + b) = sg a * sg b := by
  unfold sg
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [Int.even_add, ha, hb]

lemma sg_sub (a b : ℤ) : sg (a - b) = sg a * sg b := by
  unfold sg
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [Int.even_sub, ha, hb]

lemma sg_mul_self (a : ℤ) : sg a * sg a = 1 := by
  unfold sg; split_ifs <;> norm_num

lemma sg_of_not_even {n : ℤ} (h : ¬ Even n) : sg n = -1 := by
  unfold sg; rw [if_neg h]

lemma ge_pos (t : ℝ) (n : ℤ) : 0 < ge t n := Real.exp_pos _

lemma ge_mul (t : ℝ) (a b : ℤ) :
    ge t (a + b) * ge t (a - b) = ge (2 * t) a * ge (2 * t) b := by
  unfold ge
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

lemma ge_le_geom {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ge t (n : ℤ) ≤ Real.exp (-Real.pi * t) ^ n := by
  unfold ge
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h2 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
    exact_mod_cast h2
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1 hpt.le]

lemma geom_ratio {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.exp (-Real.pi * t) ∧ Real.exp (-Real.pi * t) < 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_lt_one_iff]
  nlinarith [mul_pos Real.pi_pos ht]

lemma ge_summable_nat {t : ℝ} (ht : 0 < t) : Summable (fun n : ℕ => ge t (n : ℤ)) :=
  Summable.of_nonneg_of_le (fun _ => (ge_pos t _).le) (fun n => ge_le_geom ht n)
    (summable_geometric_of_lt_one (geom_ratio ht).1 (geom_ratio ht).2)

lemma ge_even (t : ℝ) (n : ℤ) : ge t (-n) = ge t n := by
  unfold ge; push_cast; ring_nf

lemma ge_summable {t : ℝ} (ht : 0 < t) : Summable (ge t) := by
  refine Summable.of_nat_of_neg (ge_summable_nat ht) ?_
  have h : (fun n : ℕ => ge t (-(n : ℤ))) = fun n : ℕ => ge t (n : ℤ) := by
    funext n; exact ge_even t n
  rw [h]; exact ge_summable_nat ht

lemma ge_norm_summable {t : ℝ} (ht : 0 < t) : Summable (fun n => ‖ge t n‖) := by
  have h : (fun n => ‖ge t n‖) = ge t := by
    funext n; rw [Real.norm_eq_abs, abs_of_pos (ge_pos t n)]
  rw [h]; exact ge_summable ht

lemma sge_norm_summable {t : ℝ} (ht : 0 < t) : Summable (fun n => ‖sg n * ge t n‖) := by
  have h : (fun n => ‖sg n * ge t n‖) = ge t := by
    funext n; rw [Real.norm_eq_abs, abs_mul, sg_abs, one_mul, abs_of_pos (ge_pos t n)]
  rw [h]; exact ge_summable ht

lemma shear_injective : Function.Injective (fun c : ℤ × ℤ => (c.1 + c.2, c.1 - c.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  rw [ha, hb]

lemma shear_range {z : ℤ × ℤ} (h : Even (z.1 + z.2)) :
    z ∈ Set.range (fun c : ℤ × ℤ => (c.1 + c.2, c.1 - c.2)) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(k, k - z.2), ?_⟩
  ext
  · simp only; omega
  · simp only; omega

/-- First doubling identity. -/
lemma thetaA {t : ℝ} (ht : 0 < t) :
    (∑' n, ge t n) ^ 2 + (∑' n, sg n * ge t n) ^ 2 = 2 * (∑' n, ge (2 * t) n) ^ 2 := by
  have h2t : 0 < 2 * t := by linarith
  have e1 := tsum_mul_tsum_of_summable_norm (ge_norm_summable ht) (ge_norm_summable ht)
  have e2 := tsum_mul_tsum_of_summable_norm (sge_norm_summable ht) (sge_norm_summable ht)
  have e3 := tsum_mul_tsum_of_summable_norm (ge_norm_summable h2t) (ge_norm_summable h2t)
  have s1 := summable_mul_of_summable_norm (ge_norm_summable ht) (ge_norm_summable ht)
  have s2 := summable_mul_of_summable_norm (sge_norm_summable ht) (sge_norm_summable ht)
  have key := shear_injective.tsum_eq
    (f := fun z : ℤ × ℤ => ge t z.1 * ge t z.2 + sg z.1 * ge t z.1 * (sg z.2 * ge t z.2)) ?_
  · rw [sq, sq, sq, e1, e2, e3, ← Summable.tsum_add s1 s2, ← key, ← tsum_mul_left]
    congr 1
    funext c
    show ge t (c.1 + c.2) * ge t (c.1 - c.2) +
        sg (c.1 + c.2) * ge t (c.1 + c.2) * (sg (c.1 - c.2) * ge t (c.1 - c.2)) =
      2 * (ge (2 * t) c.1 * ge (2 * t) c.2)
    have h1 := ge_mul t c.1 c.2
    have h2 : sg (c.1 + c.2) * sg (c.1 - c.2) = 1 := by
      rw [sg_add, sg_sub]
      have := sg_mul_self c.1
      have := sg_mul_self c.2
      nlinarith
    calc ge t (c.1 + c.2) * ge t (c.1 - c.2) +
          sg (c.1 + c.2) * ge t (c.1 + c.2) * (sg (c.1 - c.2) * ge t (c.1 - c.2))
        = (ge t (c.1 + c.2) * ge t (c.1 - c.2)) * (1 + sg (c.1 + c.2) * sg (c.1 - c.2)) := by ring
      _ = 2 * (ge (2 * t) c.1 * ge (2 * t) c.2) := by rw [h1, h2]; ring
  · intro z hz
    by_contra hnr
    have hodd : ¬ Even (z.1 + z.2) := fun h => hnr (shear_range h)
    apply hz
    have h3 : sg z.1 * sg z.2 = -1 := by rw [← sg_add]; exact sg_of_not_even hodd
    show ge t z.1 * ge t z.2 + sg z.1 * ge t z.1 * (sg z.2 * ge t z.2) = 0
    calc ge t z.1 * ge t z.2 + sg z.1 * ge t z.1 * (sg z.2 * ge t z.2)
        = ge t z.1 * ge t z.2 * (1 + sg z.1 * sg z.2) := by ring
      _ = 0 := by rw [h3]; ring

/-- Second doubling identity. -/
lemma thetaB {t : ℝ} (ht : 0 < t) :
    (∑' n, ge t n) * (∑' n, sg n * ge t n) = (∑' n, sg n * ge (2 * t) n) ^ 2 := by
  have h2t : 0 < 2 * t := by linarith
  have e1 := tsum_mul_tsum_of_summable_norm (ge_norm_summable ht) (sge_norm_summable ht)
  have e2 := tsum_mul_tsum_of_summable_norm (sge_norm_summable ht) (ge_norm_summable ht)
  have e3 := tsum_mul_tsum_of_summable_norm (sge_norm_summable h2t) (sge_norm_summable h2t)
  have s1 := summable_mul_of_summable_norm (ge_norm_summable ht) (sge_norm_summable ht)
  have s2 := summable_mul_of_summable_norm (sge_norm_summable ht) (ge_norm_summable ht)
  have key := shear_injective.tsum_eq
    (f := fun z : ℤ × ℤ => ge t z.1 * (sg z.2 * ge t z.2) + sg z.1 * ge t z.1 * ge t z.2) ?_
  · have hdouble : 2 * ((∑' n, ge t n) * (∑' n, sg n * ge t n)) =
        2 * (∑' n, sg n * ge (2 * t) n) ^ 2 := by
      have hcomm : (∑' n, ge t n) * (∑' n, sg n * ge t n) =
          (∑' n, sg n * ge t n) * (∑' n, ge t n) := mul_comm _ _
      rw [two_mul]
      nth_rewrite 2 [hcomm]
      rw [e1, e2, sq, e3, ← Summable.tsum_add s1 s2, ← key, ← tsum_mul_left]
      congr 1
      funext c
      show ge t (c.1 + c.2) * (sg (c.1 - c.2) * ge t (c.1 - c.2)) +
          sg (c.1 + c.2) * ge t (c.1 + c.2) * ge t (c.1 - c.2) =
        2 * (sg c.1 * ge (2 * t) c.1 * (sg c.2 * ge (2 * t) c.2))
      have h1 := ge_mul t c.1 c.2
      calc ge t (c.1 + c.2) * (sg (c.1 - c.2) * ge t (c.1 - c.2)) +
            sg (c.1 + c.2) * ge t (c.1 + c.2) * ge t (c.1 - c.2)
          = (ge t (c.1 + c.2) * ge t (c.1 - c.2)) * (sg (c.1 - c.2) + sg (c.1 + c.2)) := by ring
        _ = 2 * (sg c.1 * ge (2 * t) c.1 * (sg c.2 * ge (2 * t) c.2)) := by
            rw [h1, sg_add, sg_sub]; ring
    linarith
  · intro z hz
    by_contra hnr
    have hodd : ¬ Even (z.1 + z.2) := fun h => hnr (shear_range h)
    apply hz
    have h3 : sg z.1 * sg z.2 = -1 := by rw [← sg_add]; exact sg_of_not_even hodd
    have h4 : sg z.1 + sg z.2 = 0 := by
      have h5 := sg_mul_self z.1
      have h6 := sg_mul_self z.2
      nlinarith
    show ge t z.1 * (sg z.2 * ge t z.2) + sg z.1 * ge t z.1 * ge t z.2 = 0
    calc ge t z.1 * (sg z.2 * ge t z.2) + sg z.1 * ge t z.1 * ge t z.2
        = ge t z.1 * ge t z.2 * (sg z.1 + sg z.2) := by ring
      _ = 0 := by rw [h4]; ring

/-- Poisson summation at `a = 2`. -/
lemma theta_poisson : (∑' n, ge (1 / 2) n) = Real.sqrt 2 * ∑' n, ge 2 n := by
  have h := Real.tsum_exp_neg_mul_int_sq (a := 2) (by norm_num)
  have h1 : (∑' n : ℤ, Real.exp (-Real.pi * 2 * (n : ℝ) ^ 2)) = ∑' n, ge 2 n := rfl
  have h2 : (∑' n : ℤ, Real.exp (-Real.pi / 2 * (n : ℝ) ^ 2)) = ∑' n, ge (1 / 2) n := by
    congr 1; funext n; unfold ge; congr 1; ring
  rw [h1, h2, ← Real.sqrt_eq_rpow] at h
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [h]
  field_simp

lemma final_alg (a b x w : ℝ) (ha : 0 < a) (h1 : a ^ 2 + b ^ 2 = 2 * x ^ 2)
    (h2 : (Real.sqrt 2 * x) ^ 2 + w ^ 2 = 2 * a ^ 2) (h3 : Real.sqrt 2 * x * w = b ^ 2) :
    x ^ 2 / a ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hA : 0 < a ^ 2 := by positivity
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have h2' : 2 * x ^ 2 + w ^ 2 = 2 * a ^ 2 := by rw [mul_pow, hs] at h2; exact h2
  have h3' : 2 * x ^ 2 * w ^ 2 = (b ^ 2) ^ 2 := by
    rw [← h3]
    calc 2 * x ^ 2 * w ^ 2 = Real.sqrt 2 ^ 2 * x ^ 2 * w ^ 2 := by rw [hs]
      _ = (Real.sqrt 2 * x * w) ^ 2 := by ring
  have hw : w ^ 2 = 2 * a ^ 2 - 2 * x ^ 2 := by linarith
  have hbb : b ^ 2 = 2 * x ^ 2 - a ^ 2 := by linarith
  rw [hw, hbb] at h3'
  have hfac : (4 * x ^ 2 - 2 * a ^ 2 - Real.sqrt 2 * a ^ 2) *
      (4 * x ^ 2 - 2 * a ^ 2 + Real.sqrt 2 * a ^ 2) = 0 := by
    have : (4 * x ^ 2 - 2 * a ^ 2 - Real.sqrt 2 * a ^ 2) *
        (4 * x ^ 2 - 2 * a ^ 2 + Real.sqrt 2 * a ^ 2)
        = (4 * x ^ 2 - 2 * a ^ 2) ^ 2 - Real.sqrt 2 ^ 2 * (a ^ 2) ^ 2 := by ring
    rw [this, hs]
    linear_combination (-2) * h3'
  have hpos : 0 < 4 * x ^ 2 - 2 * a ^ 2 + Real.sqrt 2 * a ^ 2 := by
    have : 0 < Real.sqrt 2 * a ^ 2 := mul_pos hs0 hA
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · rw [div_eq_iff hA.ne']; linarith
  · exact absurd h hpos.ne'

/-- The value of the theta quotient. -/
lemma theta_value :
    (∑' n, ge 2 n) ^ 2 / (∑' n, ge 1 n) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have hA1 := thetaA (t := 1) one_pos
  have hAh := thetaA (t := 1 / 2) (by norm_num)
  have hBh := thetaB (t := 1 / 2) (by norm_num)
  rw [show (2 : ℝ) * 1 = 2 by norm_num] at hA1
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hAh hBh
  rw [theta_poisson] at hAh hBh
  have hpos : 0 < ∑' n, ge 1 n := by
    have h0 : ge 1 0 ≤ ∑' n, ge 1 n :=
      (ge_summable one_pos).le_tsum 0 (fun j _ => (ge_pos 1 j).le)
    exact lt_of_lt_of_le (ge_pos 1 0) h0
  exact final_alg _ _ _ _ hpos hA1 hAh hBh

-- ===================== power series evaluation =====================

lemma tm_mul (r : ℝ) (f g : PowerSeries ℤ) (n : ℕ) :
    tm r (f * g) n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, tm r f kl.1 * tm r g kl.2 := by
  unfold tm
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun kl hkl => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

lemma ev_mul (r : ℝ) (f g : PowerSeries ℤ) (hf : Summable (fun n => ‖tm r f n‖))
    (hg : Summable (fun n => ‖tm r g n‖)) :
    Summable (fun n => ‖tm r (f * g) n‖) ∧
      ∑' n, tm r (f * g) n = (∑' n, tm r f n) * (∑' n, tm r g n) := by
  constructor
  · have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
    have he : (fun n => ‖tm r (f * g) n‖) =
        fun n => ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, tm r f kl.1 * tm r g kl.2‖ := by
      funext n; rw [tm_mul]
    rw [he]; exact h
  · rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    congr 1; funext n; exact tm_mul r f g n

lemma inv_summable (r : ℝ) (D B : PowerSeries ℤ) (hDB : B = 1 - D * B)
    (s : ℝ) (hs1 : s < 1) (hD : ∀ M, ∑ k ∈ Finset.range M, ‖tm r D k‖ ≤ s) :
    Summable (fun n => ‖tm r B n‖) := by
  refine summable_of_sum_range_le (c := 1 / (1 - s)) (fun n => norm_nonneg _) (fun M => ?_)
  have hpt : ∀ n, ‖tm r B n‖ ≤ (if n = 0 then (1 : ℝ) else 0) +
      ∑ k ∈ Finset.range (n + 1), ‖tm r D k‖ * ‖tm r B (n - k)‖ := by
    intro n
    have h1 : tm r B n = (if n = 0 then (1 : ℝ) else 0) - tm r (D * B) n := by
      conv_lhs => rw [hDB]
      unfold tm
      rw [map_sub, PowerSeries.coeff_one]
      split_ifs with h
      · subst h; simp
      · push_cast; ring
    rw [h1, tm_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => tm r D k * tm r B l)]
    calc ‖(if n = 0 then (1 : ℝ) else 0) - ∑ k ∈ Finset.range n.succ, tm r D k * tm r B (n - k)‖
        ≤ ‖(if n = 0 then (1 : ℝ) else 0)‖ +
            ‖∑ k ∈ Finset.range n.succ, tm r D k * tm r B (n - k)‖ := norm_sub_le _ _
      _ ≤ (if n = 0 then (1 : ℝ) else 0) +
            ∑ k ∈ Finset.range (n + 1), ‖tm r D k‖ * ‖tm r B (n - k)‖ := by
          apply add_le_add
          · split_ifs <;> simp
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
            rw [norm_mul]
  have hT0 : 0 ≤ ∑ n ∈ Finset.range M, ‖tm r B n‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsum : ∑ n ∈ Finset.range M, ‖tm r B n‖ ≤
      1 + s * ∑ n ∈ Finset.range M, ‖tm r B n‖ := by
    calc ∑ n ∈ Finset.range M, ‖tm r B n‖
        ≤ ∑ n ∈ Finset.range M, ((if n = 0 then (1 : ℝ) else 0) +
            ∑ k ∈ Finset.range (n + 1), ‖tm r D k‖ * ‖tm r B (n - k)‖) :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = (∑ n ∈ Finset.range M, (if n = 0 then (1 : ℝ) else 0)) +
            ∑ n ∈ Finset.range M, ∑ k ∈ Finset.range (n + 1),
              ‖tm r D k‖ * ‖tm r B (n - k)‖ := Finset.sum_add_distrib
      _ ≤ 1 + ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (M - m),
              ‖tm r D m‖ * ‖tm r B k‖ := by
          apply add_le_add
          · rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
          · exact (Finset.sum_range_diag_flip M (fun k l => ‖tm r D k‖ * ‖tm r B l‖)).le
      _ ≤ 1 + ∑ m ∈ Finset.range M, ‖tm r D m‖ * ∑ k ∈ Finset.range M, ‖tm r B k‖ := by
          apply add_le_add le_rfl
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_range] at hk ⊢
            omega
          · intro k _ _; exact norm_nonneg _
      _ = 1 + (∑ m ∈ Finset.range M, ‖tm r D m‖) * ∑ k ∈ Finset.range M, ‖tm r B k‖ := by
          rw [Finset.sum_mul]
      _ ≤ 1 + s * ∑ n ∈ Finset.range M, ‖tm r B n‖ := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_right (hD M) hT0
  rw [le_div_iff₀ (by linarith)]
  nlinarith

-- ===================== the theta series =====================

lemma coeff_theta_sub_one (m n : ℕ) :
    PowerSeries.coeff n (OMA.S_oeis_a201488.thetaSeries m - 1) =
      ∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0 := by
  unfold OMA.S_oeis_a201488.thetaSeries
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  ring

lemma sq_shift_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (fun j : ℕ => m * (j + 1) ^ 2) := by
  intro j j' h
  have h1 : (j + 1) ^ 2 = (j' + 1) ^ 2 := Nat.eq_of_mul_eq_mul_left hm h
  have h2 : j + 1 = j' + 1 := Nat.pow_left_injective two_ne_zero h1
  omega

lemma inner_sum (m : ℕ) (hm : 0 < m) (j0 : ℕ) :
    (∑ j ∈ Finset.range (m * (j0 + 1) ^ 2),
      if m * (j + 1) ^ 2 = m * (j0 + 1) ^ 2 then (2 : ℤ) else 0) = 2 := by
  have h : ∀ j, (m * (j + 1) ^ 2 = m * (j0 + 1) ^ 2) ↔ j = j0 := by
    intro j
    constructor
    · intro h; exact sq_shift_injective m hm h
    · intro h; rw [h]
  simp_rw [h]
  rw [Finset.sum_ite_eq', if_pos]
  rw [Finset.mem_range]
  calc j0 < (j0 + 1) ^ 2 := by nlinarith
    _ ≤ m * (j0 + 1) ^ 2 := Nat.le_mul_of_pos_left _ hm

lemma inner_sum_zero (m n : ℕ) (h : ∀ j, m * (j + 1) ^ 2 ≠ n) :
    (∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (h j)]

lemma tm_theta_sub_one_nonneg (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ tm r (OMA.S_oeis_a201488.thetaSeries m - 1) n := by
  unfold tm
  rw [coeff_theta_sub_one]
  apply mul_nonneg _ (pow_nonneg hr n)
  have h : (0 : ℤ) ≤ ∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0 :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  exact_mod_cast h

lemma theta_split {t : ℝ} (ht : 0 < t) :
    (∑' n, ge t n) = 1 + 2 * ∑' j : ℕ, ge t ((j + 1 : ℕ) : ℤ) := by
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat (f := ge t) (fun n => ge_even t n)
    (ge_summable ht)
  have h0 : ge t 0 = 1 := by unfold ge; simp
  have h7 := tsum_pnat_eq_tsum_succ (f := fun k : ℕ => ge t (k : ℤ))
  rw [h, h0, h7, two_nsmul, two_mul]

lemma exp_pow_eq (m j : ℕ) :
    Real.exp (-Real.pi) ^ (m * (j + 1) ^ 2) = ge (m : ℝ) ((j + 1 : ℕ) : ℤ) := by
  unfold ge
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma hasSum_theta_sub_one (m : ℕ) (hm : 0 < m) :
    HasSum (fun n => tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m - 1) n)
      ((∑' n, ge (m : ℝ) n) - 1) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : HasSum (fun j : ℕ => 2 * ge (m : ℝ) ((j + 1 : ℕ) : ℤ))
      ((∑' n, ge (m : ℝ) n) - 1) := by
    have hsum : Summable (fun j : ℕ => ge (m : ℝ) ((j + 1 : ℕ) : ℤ)) :=
      (summable_nat_add_iff 1).mpr (ge_summable_nat hmr)
    have h2 := hsum.hasSum.mul_left 2
    have he : (∑' n, ge (m : ℝ) n) - 1 = 2 * ∑' j : ℕ, ge (m : ℝ) ((j + 1 : ℕ) : ℤ) := by
      rw [theta_split hmr]; ring
    rw [he]
    exact h2
  refine ((sq_shift_injective m hm).hasSum_iff ?_).mp ?_
  · intro n hn
    unfold tm
    rw [coeff_theta_sub_one, inner_sum_zero m n (fun j hj => hn ⟨j, hj⟩)]
    simp
  · convert hS using 1
    funext j
    show tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m - 1) (m * (j + 1) ^ 2) =
      2 * ge (m : ℝ) ((j + 1 : ℕ) : ℤ)
    unfold tm
    rw [coeff_theta_sub_one, inner_sum m hm j, exp_pow_eq]
    push_cast
    ring

lemma tm_one (r : ℝ) (n : ℕ) : tm r 1 n = if n = 0 then 1 else 0 := by
  unfold tm
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

lemma hasSum_tm_one (r : ℝ) : HasSum (fun n => tm r 1 n) 1 := by
  have h : (fun n => tm r 1 n) = fun n => if n = 0 then (1 : ℝ) else 0 := funext (tm_one r)
  rw [h]
  exact hasSum_ite_eq 0 1

lemma tm_split (r : ℝ) (f : PowerSeries ℤ) (n : ℕ) :
    tm r f n = tm r 1 n + tm r (f - 1) n := by
  unfold tm
  rw [map_sub]
  push_cast
  ring

lemma hasSum_theta (m : ℕ) (hm : 0 < m) :
    HasSum (fun n => tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m) n)
      (∑' n, ge (m : ℝ) n) := by
  have h := (hasSum_tm_one (Real.exp (-Real.pi))).add (hasSum_theta_sub_one m hm)
  convert h using 1
  · funext n; exact tm_split _ _ n
  · ring

lemma norm_summable_theta (m : ℕ) (hm : 0 < m) :
    Summable (fun n => ‖tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m) n‖) := by
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hnn : ∀ n, 0 ≤ tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m) n := by
    intro n
    rw [tm_split, tm_one]
    have h := tm_theta_sub_one_nonneg m _ hr0 n
    split_ifs <;> linarith
  have h : (fun n => ‖tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m) n‖) =
      fun n => tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries m) n := by
    funext n; rw [Real.norm_eq_abs, abs_of_nonneg (hnn n)]
  rw [h]
  exact (hasSum_theta m hm).summable

lemma theta_one_lt_two : (∑' n, ge 1 n) - 1 < 1 := by
  rw [theta_split one_pos]
  have hrr : Real.exp (-Real.pi * 1) = (Real.exp Real.pi)⁻¹ := by rw [mul_one, Real.exp_neg]
  have h1 : Real.pi + 1 < Real.exp Real.pi := Real.add_one_lt_exp Real.pi_pos.ne'
  have h2 : (4 : ℝ) < Real.exp Real.pi := by linarith [Real.pi_gt_three]
  have h3 : (Real.exp Real.pi)⁻¹ < (4 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr h2
  have hr0 : 0 ≤ Real.exp (-Real.pi * 1) := (Real.exp_pos _).le
  have hr4 : Real.exp (-Real.pi * 1) < 1 / 4 := by rw [hrr]; linarith
  have hle : ∀ j : ℕ, ge 1 ((j + 1 : ℕ) : ℤ) ≤ Real.exp (-Real.pi * 1) ^ (j + 1) :=
    fun j => ge_le_geom one_pos (j + 1)
  have hgs : Summable (fun j : ℕ => Real.exp (-Real.pi * 1) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 (by linarith))
  have hsum : Summable (fun j : ℕ => ge 1 ((j + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).mpr (ge_summable_nat one_pos)
  have h4 : ∑' j : ℕ, ge 1 ((j + 1 : ℕ) : ℤ) ≤ ∑' j : ℕ, Real.exp (-Real.pi * 1) ^ (j + 1) :=
    Summable.tsum_le_tsum hle hsum hgs
  have h5 : ∑' j : ℕ, Real.exp (-Real.pi * 1) ^ (j + 1) =
      Real.exp (-Real.pi * 1) * (1 - Real.exp (-Real.pi * 1))⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
  have h6 : Real.exp (-Real.pi * 1) * (1 - Real.exp (-Real.pi * 1))⁻¹ < 1 / 3 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith)]
    linarith
  linarith

end A201488

open A201488 in
theorem OMA.solution : type_of% @OMA.S_oeis_a201488.main := by
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hc : PowerSeries.constantCoeff (OMA.S_oeis_a201488.thetaSeries 1) = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold OMA.S_oeis_a201488.thetaSeries
    rw [PowerSeries.coeff_mk]
    simp
  have hTB := PowerSeries.mul_invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1 hc
  have hDB : PowerSeries.invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1 =
      1 - (OMA.S_oeis_a201488.thetaSeries 1 - 1) *
        PowerSeries.invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1 := by
    rw [sub_mul, one_mul, hTB]; ring
  have hsT1 := norm_summable_theta 1 one_pos
  have hsT2 := norm_summable_theta 2 two_pos
  have hD : ∀ M, ∑ k ∈ Finset.range M,
      ‖tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries 1 - 1) k‖ ≤
        (∑' n, ge 1 n) - 1 := by
    intro M
    have h := hasSum_theta_sub_one 1 one_pos
    rw [Nat.cast_one] at h
    have he : ∑ k ∈ Finset.range M,
        ‖tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries 1 - 1) k‖ =
        ∑ k ∈ Finset.range M,
          tm (Real.exp (-Real.pi)) (OMA.S_oeis_a201488.thetaSeries 1 - 1) k :=
      Finset.sum_congr rfl (fun k _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tm_theta_sub_one_nonneg 1 _ hr0 k)])
    rw [he]
    exact sum_le_hasSum (Finset.range M) (fun k _ => tm_theta_sub_one_nonneg 1 _ hr0 k) h
  have hsB := inv_summable _ _ _ hDB _ theta_one_lt_two hD
  have hev1 := (hasSum_theta 1 one_pos).tsum_eq
  have hev2 := (hasSum_theta 2 two_pos).tsum_eq
  rw [Nat.cast_one] at hev1
  rw [Nat.cast_ofNat] at hev2
  obtain ⟨-, hTBev⟩ := ev_mul _ _ _ hsT1 hsB
  rw [hTB, (hasSum_tm_one _).tsum_eq, hev1] at hTBev
  obtain ⟨hsG, hGev⟩ := ev_mul _ _ _ hsT2 hsB
  obtain ⟨hsGG, hGGev⟩ := ev_mul _ _ _ hsG hsG
  have hBe : ∑' n, tm (Real.exp (-Real.pi))
      (PowerSeries.invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1) n = (∑' n, ge 1 n)⁻¹ :=
    eq_inv_of_mul_eq_one_right hTBev.symm
  have hval : ∑' n, tm (Real.exp (-Real.pi))
      ((OMA.S_oeis_a201488.thetaSeries 2 *
        PowerSeries.invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1) ^ 2) n =
      (2 + Real.sqrt 2) / 4 := by
    rw [sq, hGGev, hGev, hev2, hBe, ← theta_value]
    ring
  have hsum : Summable (fun n => tm (Real.exp (-Real.pi))
      ((OMA.S_oeis_a201488.thetaSeries 2 *
        PowerSeries.invOfUnit (OMA.S_oeis_a201488.thetaSeries 1) 1) ^ 2) n) := by
    rw [sq]; exact hsGG.of_norm
  have hfin := hsum.hasSum
  rw [hval] at hfin
  exact hfin
