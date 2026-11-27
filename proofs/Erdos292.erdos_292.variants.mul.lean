import FormalConjectures.ErdosProblems.«292»
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.mul := by
  rintro m ⟨S, hS, hm, h⟩ n ⟨T, hT, hn, k⟩
  have m0 : 0 < m := (Finset.mem_Icc.1 (hS hm)).1
  have d : Disjoint (S.erase m) (T.map ⟨(m * ·), mul_right_injective₀ m0.ne'⟩) := by
    simp only [Finset.disjoint_left, Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
    intro a ha b hb e
    have := Finset.mem_Icc.1 (hS (Finset.mem_of_mem_erase ha))
    have := Finset.ne_of_mem_erase ha
    have := Nat.le_mul_of_pos_right m (Finset.mem_Icc.1 (hT hb)).1
    omega
  refine ⟨S.erase m ∪ T.map ⟨(m * ·), mul_right_injective₀ m0.ne'⟩, fun x hx => ?_,
    Finset.mem_union_right _ (Finset.mem_map_of_mem _ hn), ?_⟩
  · simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · have := Finset.mem_Icc.1 (hS (Finset.mem_of_mem_erase hx))
      have := (Finset.mem_Icc.1 (hT hn)).1
      simp only [Finset.mem_Icc]; constructor <;> nlinarith
    · have := Finset.mem_Icc.1 (hT hb)
      simp only [Finset.mem_Icc]; constructor <;> nlinarith
  · rw [Finset.sum_union d, Finset.sum_map, Finset.sum_erase_eq_sub hm, h]
    simp only [Function.Embedding.coeFn_mk, Nat.cast_mul, ← one_div_mul_one_div, ← Finset.mul_sum, k]
    ring
