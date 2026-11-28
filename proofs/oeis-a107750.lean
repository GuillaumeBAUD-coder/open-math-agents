import OMAStatements.S_oeis_a107750

namespace OMA.P_oeis_a107750

open OMA.S_oeis_a107750

lemma step (n v : ℕ) (hv : a n < v ∧ zeros v ≠ zeros (a n))
    (hmin : ∀ m, a n < m → m < v → zeros m = zeros (a n)) : a (n + 1) = v := by
  show sInf {m | a n < m ∧ zeros m ≠ zeros (a n)} = v
  apply le_antisymm (Nat.sInf_le hv)
  apply le_csInf ⟨v, hv⟩
  intro m hm
  by_contra hlt
  have hlt' : m < v := by omega
  exact hm.2 (hmin m hm.1 hlt')

lemma z0 : zeros 0 = 1 := rfl
lemma z1 : zeros 1 = 0 := by norm_num [zeros]
lemma z2 : zeros 2 = 1 := by norm_num [zeros]
lemma z3 : zeros 3 = 0 := by norm_num [zeros]
lemma z4 : zeros 4 = 2 := by norm_num [zeros]
lemma z5 : zeros 5 = 1 := by norm_num [zeros]
lemma z6 : zeros 6 = 1 := by norm_num [zeros]
lemma z7 : zeros 7 = 0 := by norm_num [zeros]

lemma a0 : a 0 = 0 := rfl
lemma a1 : a 1 = 1 := step 0 1 (by simp [a0, z0, z1]) (by intro m h1 h2; omega)
lemma a2 : a 2 = 2 := step 1 2 (by simp [a1, z1, z2]) (by intro m h1 h2; rw [a1] at h1; omega)
lemma a3 : a 3 = 3 := step 2 3 (by simp [a2, z2, z3]) (by intro m h1 h2; rw [a2] at h1; omega)
lemma a4 : a 4 = 4 := step 3 4 (by simp [a3, z3, z4]) (by intro m h1 h2; rw [a3] at h1; omega)
lemma a5 : a 5 = 5 := step 4 5 (by simp [a4, z4, z5]) (by intro m h1 h2; rw [a4] at h1; omega)
lemma a6 : a 6 = 7 := step 5 7 (by simp [a5, z5, z7]) (by
  intro m h1 h2
  rw [a5] at h1
  obtain rfl : m = 6 := by omega
  rw [a5, z6, z5])

end OMA.P_oeis_a107750

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107750.main) := by
  intro h
  have h6 := h.2 6 (by norm_num)
  norm_num [OMA.P_oeis_a107750.a6, OMA.P_oeis_a107750.a5, OMA.P_oeis_a107750.a3,
    OMA.P_oeis_a107750.a2] at h6
