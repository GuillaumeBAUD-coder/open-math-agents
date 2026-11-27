import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1

/-!
# Cubic character search bound for `Λ(3, 2) ≤ 77`

Every labeling `w : ℕ → ZMod 3` of the primes yields an `n ∈ [1, 77]` such that both `n` and
`n + 1` have zero prime-factor weight sum modulo `3`. Only the five primes `2, 3, 7, 11, 13`
and ten consecutive pairs are needed; checking all `3^5 = 243` assignments finishes the proof.
-/

namespace OMA.E436ThreeTwoH1

lemma cover_five :
    ∀ a b c d e : ZMod 3,
      a = 0 ∨
      (c = 0 ∧ a + (a + a) = 0) ∨
      (a + (a + a) = 0 ∧ b + b = 0) ∨
      (d = 0 ∧ a + (a + b) = 0) ∨
      (a + (a + b) = 0 ∧ e = 0) ∨
      (b + c = 0 ∧ a + d = 0) ∨
      (a + e = 0 ∧ b + (b + b) = 0) ∨
      (b + (b + b) = 0 ∧ a + (a + c) = 0) ∨
      (b + (b + c) = 0 ∧ a + (a + (a + (a + (a + a)))) = 0) ∨
      (c + d = 0 ∧ a + (b + e) = 0) := by
  decide

end OMA.E436ThreeTwoH1

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  intro w
  rcases OMA.E436ThreeTwoH1.cover_five (w 2) (w 3) (w 7) (w 11) (w 13) with
      h | h | h | h | h | h | h | h | h | h
  · refine ⟨1, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (1 : ℕ).primeFactorsList = [] by decide,
      show (1 + 1 : ℕ).primeFactorsList = [2] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact ⟨rfl, h⟩
  · refine ⟨7, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (7 : ℕ).primeFactorsList = [7] by decide,
      show (7 + 1 : ℕ).primeFactorsList = [2, 2, 2] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨8, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (8 : ℕ).primeFactorsList = [2, 2, 2] by decide,
      show (8 + 1 : ℕ).primeFactorsList = [3, 3] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨11, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (11 : ℕ).primeFactorsList = [11] by decide,
      show (11 + 1 : ℕ).primeFactorsList = [2, 2, 3] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨12, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (12 : ℕ).primeFactorsList = [2, 2, 3] by decide,
      show (12 + 1 : ℕ).primeFactorsList = [13] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨21, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (21 : ℕ).primeFactorsList = [3, 7] by decide,
      show (21 + 1 : ℕ).primeFactorsList = [2, 11] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨26, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (26 : ℕ).primeFactorsList = [2, 13] by decide,
      show (26 + 1 : ℕ).primeFactorsList = [3, 3, 3] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨27, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (27 : ℕ).primeFactorsList = [3, 3, 3] by decide,
      show (27 + 1 : ℕ).primeFactorsList = [2, 2, 7] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨63, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (63 : ℕ).primeFactorsList = [3, 3, 7] by decide,
      show (63 + 1 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 2] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
  · refine ⟨77, Finset.mem_Icc.mpr ⟨by decide, by decide⟩, ?_⟩
    rw [show (77 : ℕ).primeFactorsList = [7, 11] by decide,
      show (77 + 1 : ℕ).primeFactorsList = [2, 3, 13] by decide]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact h
