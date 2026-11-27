import OMAStatements.S_oeis_a246396
import Mathlib

namespace A246396

lemma cos_one_gt : (1 : ℝ) / 2 < Real.cos 1 := by
  have h := Real.one_sub_sq_div_two_lt_cos (x := 1) one_ne_zero
  norm_num at h
  linarith

lemma key (x : ℝ) (h0 : Real.cos x ≤ 0) (h1 : Real.cos (x + 1) ≤ 0) :
    Real.cos (x + 1 + 1) ≤ 0 ∨ Real.cos (x - 1) ≤ 0 := by
  have hc := cos_one_gt
  have e2 : Real.cos (x + 1 + 1) = 2 * Real.cos (x + 1) * Real.cos 1 - Real.cos x := by
    have a1 := Real.cos_add (x + 1) 1
    have a2 := Real.cos_sub (x + 1) 1
    have e : x + 1 - 1 = x := by ring
    rw [e] at a2
    linarith
  have e3 : Real.cos (x - 1) = 2 * Real.cos x * Real.cos 1 - Real.cos (x + 1) := by
    have a1 := Real.cos_add x 1
    have a2 := Real.cos_sub x 1
    linarith
  by_cases hc2 : Real.cos (x + 1 + 1) ≤ 0
  · exact Or.inl hc2
  · right
    have hc3 := not_le.mp hc2
    rw [e2] at hc3
    rw [e3]
    have p1 : 0 ≤ (-Real.cos (x + 1)) * (Real.cos 1 - 1 / 2) :=
      mul_nonneg (neg_nonneg.mpr h1) (by linarith)
    have p2 : 0 ≤ (-Real.cos x) * (Real.cos 1 - 1 / 2) :=
      mul_nonneg (neg_nonneg.mpr h0) (by linarith)
    nlinarith
end A246396

theorem OMA.solution : type_of% @OMA.S_oeis_a246396.main := by
  rintro t ⟨h0, h1⟩
  rcases t with _ | m
  · simp at h0
    linarith
  · rcases A246396.key _ h0 h1 with h | h
    · left
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_add, Nat.cast_one]
        exact h1
      · rw [Nat.cast_add, Nat.cast_one]
        exact h
    · right
      refine ⟨by omega, ?_, ?_⟩
      · have e : m + 1 - 1 = m := by omega
        rw [e]
        have e' : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
        rw [e'] at h
        exact h
      · have e : m + 1 - 1 = m := by omega
        rw [e]
        have e' : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [e'] at h0
        exact h0
