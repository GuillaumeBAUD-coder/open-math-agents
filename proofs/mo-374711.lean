import OMAStatements.S_mo_374711
import Mathlib

open OMA.S_mo_374711

namespace OMA.P_mo_374711

theorem qform_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qform A (c • x) = c ^ 2 * qform A x := by
  unfold qform
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem qform_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {x : Fin n → ℝ}
    (hx : x ≠ 0) : 0 < qform A x := by
  have := hA.dotProduct_mulVec_pos hx
  simpa [qform] using this

theorem qform_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : qform A 0 = 0 := by
  simp [qform]

end OMA.P_mo_374711

open OMA.P_mo_374711 in
theorem OMA.solution : type_of% @OMA.S_mo_374711.main := by
  intro n A B hA hB x
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    right
    have hBx := qform_pos hB hx
    set s := Real.sqrt (qform B x) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hBx
    have hs2 : s ^ 2 = qform B x := Real.sq_sqrt hBx.le
    set t := 1 / Real.sqrt s with ht
    have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have htpos : 0 < t := by positivity
    have ht2 : t ^ 2 = 1 / s := by
      rw [ht, div_pow, Real.sq_sqrt hspos.le]; ring
    refine ⟨t • x, ?_, ?_⟩
    · rw [qform_smul, h, ht2]; field_simp
    · rw [qform_smul, ← hs2]
      have : Real.sqrt (t ^ 2 * s ^ 2) = t * s := by
        rw [show t ^ 2 * s ^ 2 = (t * s) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [this, smul_smul]
      have : t * s * t = 1 := by
        have : t * s * t = t ^ 2 * s := by ring
        rw [this, ht2]; field_simp
      rw [this, one_smul]
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · simp [qform_zero]
    · rw [qform_smul, qform_smul, hu, mul_one]
      have hB0 : 0 ≤ qform B u := by
        by_cases hu0 : u = 0
        · rw [hu0, qform_zero]
        · exact (qform_pos hB hu0).le
      rw [Real.sq_sqrt hB0]
      rw [show qform B u * qform B u = (qform B u) ^ 2 by ring, Real.sqrt_sq hB0]
