import FormalConjectures.ErdosProblems.«617»

/-! Color edges by slope over a prime field. Two points with the same
intercept at a prescribed slope give an edge of that color. -/

theorem OMA.solution : type_of% @Erdos617.erdos_617.variants.r2 := by
  classical
  apply Nat.infinite_setOfPred_prime.mono
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  let V := ZMod p × ZMod p
  let e := Fintype.equivFinOfCardEq (ZMod.card p)
  let slope (u v : V) := (u.2 - v.2) / (u.1 - v.1)
  let color : Sym2 V → Fin p := Sym2.lift ⟨fun u v => e (slope u v), fun u v => by
    dsimp [slope]
    rw [← neg_sub v.2 u.2, ← neg_sub v.1 u.1, neg_div_neg_eq]⟩
  refine ⟨V, inferInstance, inferInstance, by simp [V, ZMod.card, pow_two], color, ?_⟩
  intro S hS k
  obtain ⟨u, hu, v, hv, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun u : V => u.2 - e.symm k * u.1) (s := S) (t := Finset.univ)
    (by simp [hS, ZMod.card]) (fun x _ => Finset.mem_univ _)
  have hx : u.1 ≠ v.1 := fun h => hne (Prod.ext h (by rwa [h, sub_left_inj] at heq))
  refine ⟨u, hu, v, hv, hne, ?_⟩
  change e (slope u v) = k
  rw [← e.apply_symm_apply k, e.injective.eq_iff]
  apply (div_eq_iff (sub_ne_zero.mpr hx)).2
  linear_combination heq
