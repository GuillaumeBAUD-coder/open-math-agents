import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-! The tangent of a sum of arctangents via the coordinates of a Gaussian integer product. -/

open Arxiv.«2607.05739» Finset

namespace OMA

-- The cosine and sine are the two integer coordinates times the same positive factor.
lemma scaled_coordinates (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Real.cos (∑ k ∈ Icc 1 n, Real.arctan k) = c * (A n : ℝ) ∧
      Real.sin (∑ k ∈ Icc 1 n, Real.arctan k) = c * (B n : ℝ) := by
  induction n with
  | zero =>
    exact ⟨1, zero_lt_one, by norm_num [A, gaussProd], by norm_num [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨c, hc, hcos, hsin⟩ := ih
    let t : ℝ := (n + 1 : ℕ)
    have ht := Real.cos_arctan_pos t
    have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
      apply (div_eq_iff ht.ne').mp
      rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    have hp : gaussProd (n + 1) = gaussProd n * (⟨1, (n + 1 : ℕ)⟩ : GaussianInt) := by
      unfold gaussProd
      rw [prod_Icc_succ_top (by omega)]
    have ha : (A (n + 1) : ℝ) = A n - t * B n := by
      simp [A, B, hp, t, sub_eq_add_neg]
      ring
    have hb : (B (n + 1) : ℝ) = t * A n + B n := by
      simp [A, B, hp, t]
      ring
    refine ⟨c * Real.cos (Real.arctan t), mul_pos hc ht, ?_, ?_⟩
    · rw [sum_Icc_succ_top (by omega), Real.cos_add, hcos, hsin, ha]
      change _ - _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring
    · rw [sum_Icc_succ_top (by omega), Real.sin_add, hcos, hsin, hb]
      change _ + _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring

end OMA

theorem OMA.solution : type_of% @Arxiv.«2607.05739».x_eq_tan_sum_arctan := by
  intro n _
  obtain ⟨c, hc, hcos, hsin⟩ := OMA.scaled_coordinates n
  rw [Real.tan_eq_sin_div_cos, hsin, hcos, x]
  push_cast
  rw [mul_div_mul_left _ _ hc.ne']
