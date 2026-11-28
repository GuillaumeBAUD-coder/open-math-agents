import OMAReductions.R_OeisA110475_conjecture_R1

/-!
# Proof of `OeisA110475.conjecture.R1.H2`

Every `n` with `a n = 1` satisfies `n ≥ 4` and is not prime (since `a 0 = a 1 = 0` and `a p = 0`
for every prime `p`). Consequently, any sum `m = x + y` with `a x = a y = 1` satisfies `m ≥ 8`,
and cannot equal `9` (which forces `5 ∈ {x, y}`) or `11` (which forces `5 ∈ {x, y}` or
`7 ∈ {x, y}`), so `m ∉ exceptionalSet = {1, 2, 3, 4, 5, 6, 7, 9, 11}`.
-/

namespace OMA.P_OeisA110475_H2

open OeisA110475

private lemma a_zero : a 0 = 0 := by
  simp [a]

private lemma a_one : a 1 = 0 := by
  simp [a]

private lemma a_prime {p : ℕ} (hp : p.Prime) : a p = 0 := by
  dsimp [a]
  rw [hp.factorization]
  simp only [Nat.support_factorization, hp.primeFactors]
  simp

private lemma four_le_of_a_eq_one {n : ℕ} (h : a n = 1) : 4 ≤ n := by
  by_contra hlt
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [a_zero] at h; omega
  · rw [a_one] at h; omega
  · rw [a_prime (by decide : Nat.Prime 2)] at h; omega
  · rw [a_prime (by decide : Nat.Prime 3)] at h; omega

private lemma ne_five_of_a_eq_one {n : ℕ} (h : a n = 1) : n ≠ 5 := by
  rintro rfl
  rw [a_prime (by decide : Nat.Prime 5)] at h
  omega

private lemma ne_seven_of_a_eq_one {n : ℕ} (h : a n = 1) : n ≠ 7 := by
  rintro rfl
  rw [a_prime (by decide : Nat.Prime 7)] at h
  omega

theorem h2_proof : OMA.R_OeisA110475_conjecture_R1.H2 := by
  intro m _ ⟨x, y, hx, hy, hxy⟩ hm
  have hx4 : 4 ≤ x := four_le_of_a_eq_one hx
  have hy4 : 4 ≤ y := four_le_of_a_eq_one hy
  have hx5 : x ≠ 5 := ne_five_of_a_eq_one hx
  have hy5 : y ≠ 5 := ne_five_of_a_eq_one hy
  have hx7 : x ≠ 7 := ne_seven_of_a_eq_one hx
  have hy7 : y ≠ 7 := ne_seven_of_a_eq_one hy
  simp only [exceptionalSet, Finset.mem_insert, Finset.mem_singleton] at hm
  omega

end OMA.P_OeisA110475_H2

theorem OMA.solution : OMA.R_OeisA110475_conjecture_R1.H2 :=
  OMA.P_OeisA110475_H2.h2_proof
