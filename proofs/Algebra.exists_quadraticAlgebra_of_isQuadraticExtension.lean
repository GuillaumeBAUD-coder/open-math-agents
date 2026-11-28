import FormalConjectures.Wikipedia.WallSunSun

/-! Extend 1 to an independent pair, then use equal finite dimensions to identify the quadratic algebra. -/
theorem OMA.solution : type_of% @Algebra.exists_quadraticAlgebra_of_isQuadraticExtension := by
  intro K L _ _ _ _
  have hfin := Algebra.IsQuadraticExtension.finrank_eq_two K L
  obtain ⟨w, hw⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (show 1 < Module.finrank K L by omega) (one_ne_zero : (1 : L) ≠ 0)
  let B := Module.Basis.mk hw
    (hw.span_eq_top_of_card_eq_finrank (by simp [hfin])).ge
  have hb (i) : B i = ![(1 : L), w] i := by simp [B]
  obtain ⟨a, b, hab⟩ : ∃ a b : K, w * w = a • (1 : L) + b • w := by
    have hs := B.sum_repr (w * w)
    rw [Fin.sum_univ_two, hb, hb] at hs
    exact ⟨_, _, hs.symm⟩
  let f : QuadraticAlgebra K a b →ₐ[K] L := QuadraticAlgebra.lift ⟨w, hab⟩
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨hr, hm⟩ := LinearIndependent.pair_iff.mp hw x.re x.im hx
    ext <;> assumption
  have hs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (by rw [QuadraticAlgebra.finrank_eq_two, hfin])).mp hi
  exact ⟨a, b, ⟨(AlgEquiv.ofBijective f ⟨hi, hs⟩).symm⟩⟩
