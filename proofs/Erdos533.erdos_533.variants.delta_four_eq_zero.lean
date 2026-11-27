import FormalConjectures.ErdosProblems.«533»

/-! A maximum-degree vertex has a large, triangle-free neighborhood. -/

open Filter SimpleGraph Finset

theorem OMA.solution : type_of% @Erdos533.erdos_533.variants.delta_four_eq_zero := by
  intro δ hδ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  intro G hG he
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ _v : Fin n, δ * (n : ℝ) < ∑ v : Fin n, (G.degree v : ℝ) := by
    have hdegree := congrArg (fun m : ℕ ↦ (m : ℝ)) G.sum_degrees_eq_twice_card_edges
    push_cast at hdegree
    rw [hdegree, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    nlinarith [mul_pos hδ (pow_pos hnreal 2)]
  obtain ⟨v, _, hv⟩ := Finset.exists_lt_of_sum_lt hsum
  refine ⟨G.neighborFinset v, by simpa [G.card_neighborFinset_eq_degree] using hv.le, ?_⟩
  simpa using CliqueFreeOn.of_succ G (n := 3)
    (hG.cliqueFreeOn (s := Set.univ)) (Set.mem_univ v)
