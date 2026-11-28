import OMAStatements.S_oeis_a200216

namespace OMA.P200216

open OMA.S_oeis_a200216

lemma pw_succ (k : ℕ) : pw (k + 1)
    = (682 * (pw k).1 + 125 * 61 * (pw k).2, 61 * (pw k).1 + 682 * (pw k).2) := by
  rw [pw]

/-- The odd powers: the pair for the exponent 2j+1. -/
def P (j : ℕ) : ℤ × ℤ := pw (2 * j + 1)

lemma P_succ (j : ℕ) : P (j + 1)
    = (930249 * (P j).1 + 125 * 83204 * (P j).2, 83204 * (P j).1 + 930249 * (P j).2) := by
  unfold P
  have e : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
  rw [e, pw_succ, pw_succ]
  apply Prod.ext
  · dsimp only
    ring
  · dsimp only
    ring

lemma a_eq (j : ℕ) : a (j + 1)
    = (((P j).1 : ℚ) ^ 2 - 6 * (-1) ^ (j + 1) * ((P j).1 : ℚ) + 4) / 5 := by
  unfold a t P
  have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [e]
  have hg : ((-1 : ℚ) ^ (j + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨j + 1, by ring⟩
  generalize ((-1 : ℚ) ^ (j + 1)) = g at hg ⊢
  linear_combination ((((pw (2 * j + 1)).1 : ℚ)) ^ 2 / 5) * hg

end OMA.P200216

open OMA.S_oeis_a200216 OMA.P200216 in
theorem OMA.solution : type_of% @OMA.S_oeis_a200216.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  have e1 : j + 6 - 1 = j + 5 := by omega
  have e2 : j + 6 - 2 = j + 4 := by omega
  have e3 : j + 6 - 3 = j + 3 := by omega
  have e4 : j + 6 - 4 = j + 2 := by omega
  have e5 : j + 6 - 5 = j + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  have h6 : a (j + 6) = _ := a_eq (j + 5)
  have h5 : a (j + 5) = _ := a_eq (j + 4)
  have h4 : a (j + 4) = _ := a_eq (j + 3)
  have h3 : a (j + 3) = _ := a_eq (j + 2)
  have h2 : a (j + 2) = _ := a_eq (j + 1)
  have h1 : a (j + 1) = _ := a_eq j
  rw [h6, h5, h4, h3, h2, h1]
  have p5 : P (j + 5) = _ := P_succ (j + 4)
  have p4 : P (j + 4) = _ := P_succ (j + 3)
  have p3 : P (j + 3) = _ := P_succ (j + 2)
  have p2 : P (j + 2) = _ := P_succ (j + 1)
  have p1 : P (j + 1) = _ := P_succ j
  simp only [p5, p4, p3, p2, p1]
  push_cast
  ring
