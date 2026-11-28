import FormalConjectures.ErdosProblems.«617»

/-! Use the slope of an edge over the prime field to color the pair. For a
prescribed slope, use the repeated intercept in the selected vertex subtype.
This uses the original slope-coloring construction. -/

theorem OMA.solution : type_of% @Erdos617.erdos_617.variants.r2 := by
  classical
  apply Nat.infinite_setOfPred_prime.mono
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  let V := ZMod p × ZMod p
  let e := ZMod.finEquiv p
  let slope (u v : V) := (u.2 - v.2) / (u.1 - v.1)
  let color : Sym2 V → Fin p := Sym2.lift ⟨fun u v => e.symm (slope u v), fun u v => by
    simp only [slope, ← neg_sub v.2 u.2, ← neg_sub v.1 u.1, neg_div_neg_eq]⟩
  refine ⟨V, inferInstance, inferInstance, by simp [V, ZMod.card, pow_two], color, ?_⟩
  intro S hS k
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun u : S => u.val.2 - e k * u.val.1) (by simp [hS, ZMod.card])
  have huv : u ≠ v := fun h => hne (Subtype.ext h)
  have hx : u.1 ≠ v.1 := fun h => huv (Prod.ext h (by rwa [h, sub_left_inj] at heq))
  refine ⟨u, hu, v, hv, huv, ?_⟩
  apply e.toEquiv.symm_apply_eq.mpr
  apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
  linear_combination heq
