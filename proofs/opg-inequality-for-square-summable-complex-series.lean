import OMAStatements.S_opg_inequality_for_square_summable_complex_series

namespace OMA.P_opg_inequality_for_square_summable_complex_series

private def dyadicIdx (p : ℕ × ℕ) : ℕ :=
  2 ^ p.1 * (2 * p.2 + 1) - 1

private lemma dyadicIdx_succ (p : ℕ × ℕ) :
    dyadicIdx p + 1 = 2 ^ p.1 * (2 * p.2 + 1) := by
  unfold dyadicIdx
  have h1 : 1 ≤ 2 ^ p.1 := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 * p.2 + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have h : 1 ≤ 2 ^ p.1 * (2 * p.2 + 1) := Nat.mul_pos h1 h2
  omega

private lemma dyadic_eq_imp {k₁ k₂ l₁ l₂ : ℕ}
    (h : 2 ^ k₁ * (2 * l₁ + 1) = 2 ^ k₂ * (2 * l₂ + 1)) :
    k₁ = k₂ ∧ l₁ = l₂ := by
  have hle : ∀ {a b c d : ℕ}, a ≤ b →
      2 ^ a * (2 * c + 1) = 2 ^ b * (2 * d + 1) → a = b ∧ c = d := by
    intro a b c d hab heq
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at heq
    have hpos : 0 < 2 ^ a := by positivity
    have hcancel : 2 * c + 1 = 2 ^ e * (2 * d + 1) := Nat.eq_of_mul_eq_mul_left hpos heq
    cases e with
    | zero =>
      simp only [pow_zero, one_mul] at hcancel
      exact ⟨by omega, by omega⟩
    | succ e' =>
      rw [pow_succ', mul_assoc] at hcancel
      omega
  rcases le_total k₁ k₂ with h12 | h21
  · exact hle h12 h
  · obtain ⟨hk, hl⟩ := hle h21 h.symm
    exact ⟨hk.symm, hl.symm⟩

private lemma dyadic_surj : ∀ m : ℕ, 0 < m → ∃ k l : ℕ, 2 ^ k * (2 * l + 1) = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hpar : m % 2 = 0
    · have hm2_pos : 0 < m / 2 := by omega
      have hm2_lt : m / 2 < m := by omega
      obtain ⟨k, l, hkl⟩ := ih (m / 2) hm2_lt hm2_pos
      refine ⟨k + 1, l, ?_⟩
      rw [pow_succ', mul_assoc, hkl]
      omega
    · refine ⟨0, m / 2, ?_⟩
      simp only [pow_zero, one_mul]
      omega

private lemma dyadicIdx_bijective : Function.Bijective dyadicIdx := by
  constructor
  · intro p₁ p₂ h
    have h' : dyadicIdx p₁ + 1 = dyadicIdx p₂ + 1 := congrArg (· + 1) h
    rw [dyadicIdx_succ, dyadicIdx_succ] at h'
    obtain ⟨hk, hl⟩ := dyadic_eq_imp h'
    exact Prod.ext hk hl
  · intro n
    obtain ⟨k, l, hkl⟩ := dyadic_surj (n + 1) (Nat.succ_pos n)
    refine ⟨(k, l), ?_⟩
    have h : dyadicIdx (k, l) + 1 = 2 ^ k * (2 * l + 1) := dyadicIdx_succ (k, l)
    omega

private lemma hasSum_inv_sq_succ :
    HasSum (fun l : ℕ => (((l : ℝ) + 1) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, one_div, inv_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

private lemma inv_sq_succ_summable :
    Summable (fun l : ℕ => (((l : ℝ) + 1) ^ 2)⁻¹) :=
  hasSum_inv_sq_succ.summable

private lemma tsum_inv_sq_succ :
    ∑' l : ℕ, (((l : ℝ) + 1) ^ 2)⁻¹ = Real.pi ^ 2 / 6 :=
  hasSum_inv_sq_succ.tsum_eq

private lemma cauchy_schwarz_tsum {c d : ℕ → ℝ}
    (hc : Summable (fun l => c l ^ 2))
    (hd : Summable (fun l => d l ^ 2))
    (hcd : Summable (fun l => c l * d l))
    (hA : 0 < ∑' l, c l ^ 2) :
    (∑' l, c l * d l) ^ 2 ≤ (∑' l, c l ^ 2) * (∑' l, d l ^ 2) := by
  set A := ∑' l, c l ^ 2
  set B := ∑' l, c l * d l
  set C := ∑' l, d l ^ 2
  set t := B / A
  have hle : ∀ l : ℕ, 2 * t * (c l * d l) ≤ t ^ 2 * c l ^ 2 + d l ^ 2 := by
    intro l
    have hsq : 0 ≤ (t * c l - d l) ^ 2 := sq_nonneg _
    linarith
  have hsum : ∑' l, 2 * t * (c l * d l) ≤ ∑' l, (t ^ 2 * c l ^ 2 + d l ^ 2) :=
    (hcd.mul_left (2 * t)).tsum_le_tsum hle ((hc.mul_left (t ^ 2)).add hd)
  rw [tsum_mul_left, (hc.mul_left (t ^ 2)).tsum_add hd, tsum_mul_left] at hsum
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hmul : 2 * B ^ 2 ≤ B ^ 2 + A * C := by
    have h1 : A * (2 * t * B) ≤ A * (t ^ 2 * A + C) :=
      mul_le_mul_of_nonneg_left hsum hA.le
    have h2 : A * (2 * t * B) = 2 * B ^ 2 := by
      dsimp only [t]
      field_simp
    have h3 : A * (t ^ 2 * A + C) = B ^ 2 + A * C := by
      dsimp only [t]
      field_simp
    linarith
  linarith

private theorem prove_main : ∀ a : ℕ → ℂ, Summable (fun n : ℕ => ‖a (n + 1)‖ ^ 2) →
    (6 / Real.pi ^ 2) *
        (∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2) ≤
      ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
  intro a ha
  obtain ⟨e, he⟩ : ∃ e : ℕ × ℕ ≃ ℕ, ∀ p, e p = dyadicIdx p :=
    ⟨Equiv.ofBijective dyadicIdx dyadicIdx_bijective, fun _ => rfl⟩
  have hprod_eq : (fun p : ℕ × ℕ => ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2) =
      (fun n : ℕ => ‖a (n + 1)‖ ^ 2) ∘ e := by
    funext p
    simp only [Function.comp_apply, he p, dyadicIdx_succ]
  have hprod_sum : Summable (fun p : ℕ × ℕ => ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2) := by
    rw [hprod_eq]
    exact ha.comp_injective e.injective
  have hprod_tsum : ∑' p : ℕ × ℕ, ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2 =
      ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
    rw [hprod_eq]
    exact e.tsum_eq (fun n : ℕ => ‖a (n + 1)‖ ^ 2)
  have hrow_sum : ∀ k : ℕ, Summable (fun l : ℕ => ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) :=
    hprod_sum.prod_factor
  have houter_sum : Summable (fun k : ℕ => ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) :=
    hprod_sum.prod
  have houter_tsum : ∑' k : ℕ, ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 =
      ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
    rw [← hprod_tsum]
    exact hprod_sum.tsum_prod.symm
  have hpi_pos : 0 < Real.pi ^ 2 / 6 := by positivity
  have hrow_bound : ∀ k : ℕ,
      ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
        (Real.pi ^ 2 / 6) * ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 := by
    intro k
    let c : ℕ → ℝ := fun l => ((l : ℝ) + 1)⁻¹
    let d : ℕ → ℝ := fun l => ‖a (2 ^ k * (2 * l + 1))‖
    have hc_sq : (fun l : ℕ => c l ^ 2) = fun l : ℕ => (((l : ℝ) + 1) ^ 2)⁻¹ := by
      funext l
      simp only [c, inv_pow]
    have hc_sum : Summable (fun l => c l ^ 2) := by
      rw [hc_sq]
      exact inv_sq_succ_summable
    have hd_sum : Summable (fun l => d l ^ 2) := hrow_sum k
    have hnorm_eq : ∀ l : ℕ,
        ‖(((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ = c l * d l := by
      intro l
      rw [norm_mul, norm_inv]
      have hcast : ((l : ℂ) + 1) = (((l : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hcd_sum : Summable (fun l => c l * d l) := by
      refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (hc_sum.add hd_sum)
      have hsq : 0 ≤ (c l - d l) ^ 2 := sq_nonneg _
      nlinarith
    have hnorm_sum : Summable (fun l : ℕ => ‖(((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖) := by
      simpa only [hnorm_eq] using hcd_sum
    have htri : ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ≤
        ∑' l : ℕ, c l * d l := by
      calc ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖
          ≤ ∑' l : ℕ, ‖(((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ :=
            norm_tsum_le_tsum_norm hnorm_sum
        _ = ∑' l : ℕ, c l * d l := by simp only [hnorm_eq]
    have hcs := cauchy_schwarz_tsum hc_sum hd_sum hcd_sum (by rw [hc_sq, tsum_inv_sq_succ]; exact hpi_pos)
    rw [hc_sq, tsum_inv_sq_succ] at hcs
    have hnonneg : 0 ≤ ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ := norm_nonneg _
    have hsq_le : ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
        (∑' l : ℕ, c l * d l) ^ 2 := by nlinarith
    exact le_trans hsq_le hcs
  have hlhs_sum : Summable (fun k : ℕ =>
      ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hrow_bound (houter_sum.mul_left _)
  have hsum_le : ∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
      (Real.pi ^ 2 / 6) * ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
    calc ∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2
        ≤ ∑' k : ℕ, (Real.pi ^ 2 / 6) * ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 :=
          hlhs_sum.tsum_le_tsum hrow_bound (houter_sum.mul_left _)
      _ = (Real.pi ^ 2 / 6) * ∑' k : ℕ, ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 :=
          tsum_mul_left
      _ = (Real.pi ^ 2 / 6) * ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by rw [houter_tsum]
  have hcoeff_pos : 0 < 6 / Real.pi ^ 2 := by positivity
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  calc (6 / Real.pi ^ 2) *
        (∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2)
      ≤ (6 / Real.pi ^ 2) * ((Real.pi ^ 2 / 6) * ∑' n : ℕ, ‖a (n + 1)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_le hcoeff_pos.le
    _ = ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by field_simp

end OMA.P_opg_inequality_for_square_summable_complex_series

theorem OMA.solution :
    type_of% @OMA.S_opg_inequality_for_square_summable_complex_series.main :=
  OMA.P_opg_inequality_for_square_summable_complex_series.prove_main
