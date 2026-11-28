import OMAStatements.S_oeis_a344503
import Mathlib

namespace A344503Proof

def B (j : ℕ) : ℚ := ((3 * j).choose j : ℚ)

def Cc (j : ℕ) : ℚ := ((3 * j + 2).choose j : ℚ)

lemma B_succ (j : ℕ) : B (j + 1) = 3 * Cc j := by
  unfold B Cc
  have e : 3 * (j + 1) = 3 * j + 2 + 1 := by ring
  rw [e]
  have h := Nat.add_one_mul_choose_eq (3 * j + 2) j
  have hq : (3 * (j : ℚ) + 2 + 1) * (((3 * j + 2).choose j : ℕ) : ℚ)
      = (((3 * j + 2 + 1).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) := by
    exact_mod_cast h
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hj
  linear_combination -hq

lemma Cc_eq (j : ℕ) :
    Cc j = B j * ((3 * (j : ℚ) + 1) * (3 * (j : ℚ) + 2)) / ((2 * (j : ℚ) + 1) * (2 * (j : ℚ) + 2)) := by
  unfold B Cc
  have h1 := Nat.choose_mul_succ_eq (3 * j) j
  have h2 := Nat.choose_mul_succ_eq (3 * j + 1) j
  have e1 : 3 * j + 1 - j = 2 * j + 1 := by omega
  have e2 : 3 * j + 1 + 1 - j = 2 * j + 2 := by omega
  rw [e1] at h1
  rw [e2] at h2
  have q1 : (((3 * j).choose j : ℕ) : ℚ) * (3 * (j : ℚ) + 1)
      = (((3 * j + 1).choose j : ℕ) : ℚ) * (2 * (j : ℚ) + 1) := by
    exact_mod_cast h1
  have q2 : (((3 * j + 1).choose j : ℕ) : ℚ) * (3 * (j : ℚ) + 1 + 1)
      = (((3 * j + 2).choose j : ℕ) : ℚ) * (2 * (j : ℚ) + 2) := by
    exact_mod_cast h2
  rw [eq_div_iff (by positivity)]
  linear_combination -(2 * (j : ℚ) + 1) * q2 - (3 * (j : ℚ) + 2) * q1

end A344503Proof

open A344503Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a344503.main := by
  intro a h0 h1 h2 n hn
  have hB : ∀ j : ℕ, a (3 * j) = B j := h0
  have hC : ∀ j : ℕ, a (3 * j + 2) = -Cc j := h2
  obtain ⟨i, hi⟩ : ∃ i, n = 3 * i + 5 ∨ n = 3 * i + 6 ∨ n = 3 * i + 7 := ⟨(n - 5) / 3, by omega⟩
  have d1 : ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2)) ≠ 0 := by positivity
  have d2 : ((2 * ((i : ℚ) + 1) + 1) * (2 * ((i : ℚ) + 1) + 2)) ≠ 0 := by positivity
  rcases hi with rfl | rfl | rfl
  · -- next residue class
    have s1 : 3 * i + 5 - 1 = 3 * i + 4 := by omega
    have s2 : 3 * i + 5 - 2 = 3 * i + 3 := by omega
    have s3 : 3 * i + 5 - 3 = 3 * i + 2 := by omega
    have s4 : 3 * i + 5 - 4 = 3 * i + 1 := by omega
    have s5 : 3 * i + 5 - 5 = 3 * i := by omega
    have v0 : a (3 * i + 5) = -Cc (i + 1) := by
      rw [show 3 * i + 5 = 3 * (i + 1) + 2 by ring]
      exact hC _
    have v1 : a (3 * i + 4) = 0 := by
      rw [show 3 * i + 4 = 3 * (i + 1) + 1 by ring]
      exact h1 _
    have v2 : a (3 * i + 3) = B (i + 1) := by
      rw [show 3 * i + 3 = 3 * (i + 1) by ring]
      exact hB _
    have v3 : a (3 * i + 2) = -Cc i := by
      exact hC _
    have v4 : a (3 * i + 1) = 0 := by
      exact h1 _
    have v5 : a (3 * i) = B i := by
      exact hB _
    rw [s1, s2, s3, s4, s5, v0, v1, v2, v3, v4, v5, Cc_eq (i + 1), B_succ i, Cc_eq i]
    push_cast
    field_simp
    ring
  · -- next residue class
    have s1 : 3 * i + 6 - 1 = 3 * i + 5 := by omega
    have s2 : 3 * i + 6 - 2 = 3 * i + 4 := by omega
    have s3 : 3 * i + 6 - 3 = 3 * i + 3 := by omega
    have s4 : 3 * i + 6 - 4 = 3 * i + 2 := by omega
    have s5 : 3 * i + 6 - 5 = 3 * i + 1 := by omega
    have v0 : a (3 * i + 6) = B (i + 1 + 1) := by
      rw [show 3 * i + 6 = 3 * (i + 1 + 1) by ring]
      exact hB _
    have v1 : a (3 * i + 5) = -Cc (i + 1) := by
      rw [show 3 * i + 5 = 3 * (i + 1) + 2 by ring]
      exact hC _
    have v2 : a (3 * i + 4) = 0 := by
      rw [show 3 * i + 4 = 3 * (i + 1) + 1 by ring]
      exact h1 _
    have v3 : a (3 * i + 3) = B (i + 1) := by
      rw [show 3 * i + 3 = 3 * (i + 1) by ring]
      exact hB _
    have v4 : a (3 * i + 2) = -Cc i := by
      exact hC _
    have v5 : a (3 * i + 1) = 0 := by
      exact h1 _
    rw [s1, s2, s3, s4, s5, v0, v1, v2, v3, v4, v5, B_succ (i + 1), Cc_eq (i + 1), B_succ i, Cc_eq i]
    push_cast
    field_simp
    ring
  · -- next residue class
    have s1 : 3 * i + 7 - 1 = 3 * i + 6 := by omega
    have s2 : 3 * i + 7 - 2 = 3 * i + 5 := by omega
    have s3 : 3 * i + 7 - 3 = 3 * i + 4 := by omega
    have s4 : 3 * i + 7 - 4 = 3 * i + 3 := by omega
    have s5 : 3 * i + 7 - 5 = 3 * i + 2 := by omega
    have v0 : a (3 * i + 7) = 0 := by
      rw [show 3 * i + 7 = 3 * (i + 1 + 1) + 1 by ring]
      exact h1 _
    have v1 : a (3 * i + 6) = B (i + 1 + 1) := by
      rw [show 3 * i + 6 = 3 * (i + 1 + 1) by ring]
      exact hB _
    have v2 : a (3 * i + 5) = -Cc (i + 1) := by
      rw [show 3 * i + 5 = 3 * (i + 1) + 2 by ring]
      exact hC _
    have v3 : a (3 * i + 4) = 0 := by
      rw [show 3 * i + 4 = 3 * (i + 1) + 1 by ring]
      exact h1 _
    have v4 : a (3 * i + 3) = B (i + 1) := by
      rw [show 3 * i + 3 = 3 * (i + 1) by ring]
      exact hB _
    have v5 : a (3 * i + 2) = -Cc i := by
      exact hC _
    rw [s1, s2, s3, s4, s5, v0, v1, v2, v3, v4, v5, B_succ (i + 1), Cc_eq (i + 1), B_succ i, Cc_eq i]
    push_cast
    field_simp
    ring
