import OMAStatements.S_oeis_a107750

open OMA.S_oeis_a107750

lemma zeros_vals :
    zeros 0 = 1 ∧ zeros 1 = 0 ∧ zeros 2 = 1 ∧ zeros 3 = 0 ∧
      zeros 4 = 2 ∧ zeros 5 = 1 ∧ zeros 6 = 1 ∧ zeros 7 = 0 := by
  decide

lemma next_a (n m : ℕ) (hm : a n < m) (hz : zeros m ≠ zeros (a n))
    (hmin : ∀ k, a n < k → k < m → zeros k = zeros (a n)) : a (n + 1) = m := by
  let s : Set ℕ := {k | a n < k ∧ zeros k ≠ zeros (a n)}
  have hmem : m ∈ s := ⟨hm, hz⟩
  have hle : sInf s ≤ m := Nat.sInf_le hmem
  have hge : m ≤ sInf s := by
    by_contra h
    have hlt : sInf s < m := by omega
    have hin : sInf s ∈ s := Nat.sInf_mem ⟨m, hmem⟩
    exact hin.2 (hmin (sInf s) hin.1 hlt)
  have ha : a (n + 1) = sInf s := by simp [a, s]
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107750.main) := by
  intro h
  have z0 : zeros 0 = 1 := zeros_vals.1
  have z1 : zeros 1 = 0 := zeros_vals.2.1
  have z2 : zeros 2 = 1 := zeros_vals.2.2.1
  have z3 : zeros 3 = 0 := zeros_vals.2.2.2.1
  have z4 : zeros 4 = 2 := zeros_vals.2.2.2.2.1
  have z5 : zeros 5 = 1 := zeros_vals.2.2.2.2.2.1
  have z6 : zeros 6 = 1 := zeros_vals.2.2.2.2.2.2.1
  have z7 : zeros 7 = 0 := zeros_vals.2.2.2.2.2.2.2
  have ha0 : a 0 = 0 := by simp [a]
  have ha1 : a 1 = 1 := by
    have : a 0 < 1 := by simp [ha0]
    exact next_a 0 1 this (by simp [ha0, z0, z1]) (by intro k hk hlt; omega)
  have ha2 : a 2 = 2 := by
    exact next_a 1 2 (by simp [ha1]) (by simp [ha1, z1, z2]) (by intro k hk hlt; omega)
  have ha3 : a 3 = 3 := by
    exact next_a 2 3 (by simp [ha2]) (by simp [ha2, z2, z3]) (by intro k hk hlt; omega)
  have ha4 : a 4 = 4 := by
    exact next_a 3 4 (by simp [ha3]) (by simp [ha3, z3, z4]) (by intro k hk hlt; omega)
  have ha5 : a 5 = 5 := by
    exact next_a 4 5 (by simp [ha4]) (by simp [ha4, z4, z5]) (by intro k hk hlt; omega)
  have ha6 : a 6 = 7 := by
    refine next_a 5 7 (by simp [ha5]) (by simp [ha5, z5, z7]) ?_
    intro k hk hlt
    have hk5 : 5 < k := by simpa [ha5] using hk
    interval_cases k
    simp [ha5, z5, z6]
  have hrec := h.2 6 (by decide)
  simp [ha6, ha5, ha3, ha2] at hrec
