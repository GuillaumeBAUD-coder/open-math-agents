import OMAStatements.S_oeis_a005654
import Mathlib

namespace OMA.A005654Proof

open OMA.S_oeis_a005654

/-- The central binomial coefficient as a rational number. -/
def P (m : ℕ) : ℚ := (Nat.centralBinom m : ℚ)

lemma P_succ (m : ℕ) : P (m + 1) = 2 * (2 * (m : ℚ) + 1) * P m / ((m : ℚ) + 1) := by
  have h : ((m : ℚ) + 1) * P (m + 1) = 2 * (2 * (m : ℚ) + 1) * P m := by
    unfold P
    have := Nat.succ_mul_centralBinom_succ m
    exact_mod_cast this
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linarith

lemma half (m : ℕ) : (Nat.choose (2 * m + 1) (m + 1) : ℚ) = P (m + 1) / 2 := by
  unfold P
  have h : Nat.centralBinom (m + 1) = 2 * Nat.choose (2 * m + 1) (m + 1) := by
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [Nat.centralBinom, e, Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  rw [h]; push_cast; ring

lemma a_odd (m : ℕ) : a (2 * m + 1) = (P (2 * m + 1) / 2 + P m) / 2 := by
  have e1 : 2 * (2 * m + 1) - 1 = 2 * (2 * m) + 1 := by omega
  have e2 : 2 * m + 1 - 1 = 2 * m := by omega
  have e3 : (2 * m + 1) / 2 = m := by omega
  unfold a
  rw [e1, e2, e3, half (2 * m)]
  rfl

lemma a_even (m : ℕ) : a (2 * m + 2) = (P (2 * m + 2) / 2 + P (m + 1) / 2) / 2 := by
  have e1 : 2 * (2 * m + 2) - 1 = 2 * (2 * m + 1) + 1 := by omega
  have e2 : 2 * m + 2 - 1 = 2 * m + 1 := by omega
  have e3 : (2 * m + 2) / 2 = m + 1 := by omega
  unfold a
  rw [e1, e2, e3, half (2 * m + 1), half m]

lemma res_odd (j : ℕ) : residual a (2 * j + 5) = 0 := by
  have i0 : a (2 * j + 5) = (P (2 * j + 5) / 2 + P (j + 2)) / 2 := a_odd (j + 2)
  have i1 : a (2 * j + 5 - 1) = (P (2 * j + 4) / 2 + P (j + 2) / 2) / 2 := a_even (j + 1)
  have i2 : a (2 * j + 5 - 2) = (P (2 * j + 3) / 2 + P (j + 1)) / 2 := a_odd (j + 1)
  have i3 : a (2 * j + 5 - 3) = (P (2 * j + 2) / 2 + P (j + 1) / 2) / 2 := a_even j
  have i4 : a (2 * j + 5 - 4) = (P (2 * j + 1) / 2 + P j) / 2 := a_odd j
  have h5 : P (2 * j + 5) = _ := P_succ (2 * j + 4)
  have h4 : P (2 * j + 4) = _ := P_succ (2 * j + 3)
  have h3 : P (2 * j + 3) = _ := P_succ (2 * j + 2)
  have h2 : P (2 * j + 2) = _ := P_succ (2 * j + 1)
  have g2 : P (j + 2) = _ := P_succ (j + 1)
  have g1 : P (j + 1) = _ := P_succ j
  simp only [OMA.S_oeis_a005654.residual]
  rw [i0, i1, i2, i3, i4, h5, h4, h3, h2, g2, g1]
  push_cast
  field_simp
  ring

lemma res_even (j : ℕ) : residual a (2 * j + 6) = 0 := by
  have i0 : a (2 * j + 6) = (P (2 * j + 6) / 2 + P (j + 3) / 2) / 2 := a_even (j + 2)
  have i1 : a (2 * j + 6 - 1) = (P (2 * j + 5) / 2 + P (j + 2)) / 2 := a_odd (j + 2)
  have i2 : a (2 * j + 6 - 2) = (P (2 * j + 4) / 2 + P (j + 2) / 2) / 2 := a_even (j + 1)
  have i3 : a (2 * j + 6 - 3) = (P (2 * j + 3) / 2 + P (j + 1)) / 2 := a_odd (j + 1)
  have i4 : a (2 * j + 6 - 4) = (P (2 * j + 2) / 2 + P (j + 1) / 2) / 2 := a_even j
  have h6 : P (2 * j + 6) = _ := P_succ (2 * j + 5)
  have h5 : P (2 * j + 5) = _ := P_succ (2 * j + 4)
  have h4 : P (2 * j + 4) = _ := P_succ (2 * j + 3)
  have h3 : P (2 * j + 3) = _ := P_succ (2 * j + 2)
  have g3 : P (j + 3) = _ := P_succ (j + 2)
  have g2 : P (j + 2) = _ := P_succ (j + 1)
  simp only [OMA.S_oeis_a005654.residual]
  rw [i0, i1, i2, i3, i4, h6, h5, h4, h3, g3, g2]
  push_cast
  field_simp
  ring

end OMA.A005654Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a005654.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · exact OMA.A005654Proof.res_odd j
  · have e : 2 * j + 1 + 5 = 2 * j + 6 := by omega
    rw [e]
    exact OMA.A005654Proof.res_even j
