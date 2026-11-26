import FormalConjectures.ErdosProblems.«617»

/-! Over a prime field, color each edge by its slope (using zero for vertical edges).
Among more than p points, two lie on a common line of any prescribed finite slope. -/

theorem OMA.solution : type_of% @Erdos617.erdos_617.variants.r2 := by
  classical
  apply Nat.infinite_setOfPred_prime.mono
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  let F := ZMod p
  let V := F × F
  let e : F ≃ Fin p := Fintype.equivFinOfCardEq (ZMod.card p)
  let slope (u v : V) : F := (u.2 - v.2) / (u.1 - v.1)
  have symm (u v : V) : slope u v = slope v u := by
    dsimp [slope]
    rw [← neg_sub v.2 u.2, ← neg_sub v.1 u.1, neg_div_neg_eq]
  let color : Sym2 V → Fin p := Sym2.lift ⟨fun u v => e (slope u v), fun u v => congrArg e (symm u v)⟩
  refine ⟨V, inferInstance, inferInstance, ?_, color, ?_⟩
  · simp [V,F,ZMod.card,pow_two]
  intro S hS k
  let m := e.symm k
  let intercept (u : V) : F := u.2 - m * u.1
  have hlt : (Finset.univ : Finset F).card < S.card := by simp [F,hS,ZMod.card]
  obtain ⟨u,hu,v,hv,hne,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := intercept) (fun x _ => Finset.mem_univ _)
  change u.2 - m * u.1 = v.2 - m * v.1 at heq
  have hx : u.1 ≠ v.1 := by
    intro hh
    apply hne
    exact Prod.ext hh (by rwa [hh, sub_left_inj] at heq)
  have hm : slope u v = m := by
    apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
    linear_combination heq
  refine ⟨u,hu,v,hv,hne,?_⟩
  change e (slope u v) = k
  rw [hm, e.apply_symm_apply]
