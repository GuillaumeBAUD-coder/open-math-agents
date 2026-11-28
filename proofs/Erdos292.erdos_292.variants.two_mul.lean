import FormalConjectures.ErdosProblems.«292»
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.two_mul := by
  rintro n ⟨S, hS, hn, h⟩ h1
  have o : 1 ∉ S := fun o => by
    have := Finset.add_le_sum (f := fun m : ℕ => (1 : ℚ) / m) (fun _ _ => by positivity) o hn (by omega)
    have : (0 : ℚ) < 1 / n := by positivity
    simp only [h] at *
    norm_num at *
    linarith
  refine ⟨insert 2 (S.map ⟨(2 * ·), mul_right_injective₀ two_ne_zero⟩), fun m hm => ?_,
    Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hn), ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk] at hm
    rcases hm with rfl | ⟨k, hk, rfl⟩
    · simp; omega
    · have := Finset.mem_Icc.1 (hS hk); simp; omega
  · rw [Finset.sum_insert (by simpa using o), Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Nat.cast_mul, Nat.cast_ofNat, ← one_div_mul_one_div, ← Finset.mul_sum, h]
    norm_num
