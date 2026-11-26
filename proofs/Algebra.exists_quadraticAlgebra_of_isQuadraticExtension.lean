import FormalConjectures.Wikipedia.WallSunSun

-- Problem: Infinitude of Wall–Sun–Sun primes — exists quadraticAlgebra of isQuadraticExtension
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WallSunSun.lean (declaration Algebra.exists_quadraticAlgebra_of_isQuadraticExtension)
-- Credit: @florynepierson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Algebra.exists_quadraticAlgebra_of_isQuadraticExtension := by
  intro K L _ _ _ _
  have hfin : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  obtain ⟨w, hw⟩ : ∃ w : L, ∀ r : K, w ≠ algebraMap K L r := by
    by_contra hcon
    push_neg at hcon
    have hle : Module.finrank K L ≤ 1 := by
      apply finrank_le_one (1 : L)
      intro y
      obtain ⟨r, hr⟩ := hcon y
      exact ⟨r, by rw [hr, Algebra.algebraMap_eq_smul_one]⟩
    omega
  have hli : LinearIndependent K ![(1 : L), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      rw [← Algebra.algebraMap_eq_smul_one] at hst
      have hs : s = 0 := (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp hst
      exact ⟨hs, rfl⟩
    · exfalso
      have h1 : t • w = -(s • (1 : L)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have h2 : w = t⁻¹ • (t • w) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      apply hw (-s / t)
      rw [Algebra.algebraMap_eq_smul_one, h2, h1, smul_neg, smul_smul, ← neg_smul]
      congr 1; ring
  have hcard : Fintype.card (Fin 2) = Module.finrank K L := by simp [hfin]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin 2) K L, ∀ i, B i = ![(1 : L), w] i :=
    ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank hcard).ge, fun i => by simp⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : K, w * w = a • (1 : L) + b • w := by
    have hs := B.sum_repr (w * w)
    rw [Fin.sum_univ_two, hB, hB] at hs
    exact ⟨B.repr (w * w) 0, B.repr (w * w) 1, by simpa using hs.symm⟩
  let φ : QuadraticAlgebra K a b →ₐ[K] L := QuadraticAlgebra.lift ⟨w, hab⟩
  have hφ : ∀ z : QuadraticAlgebra K a b, φ z = z.re • (1 : L) + z.im • w := fun z => rfl
  have key : ∀ x y : K, x • (1 : L) + y • w = 0 → x = 0 ∧ y = 0 :=
    fun x y h => LinearIndependent.pair_iff.mp hli x y h
  have hinj : Function.Injective φ := by
    intro z1 z2 h
    rw [hφ, hφ] at h
    have hz := key (z1.re - z2.re) (z1.im - z2.im)
      (by rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]; exact h)
    ext <;> [exact sub_eq_zero.mp hz.1; exact sub_eq_zero.mp hz.2]
  have hsurj : Function.Surjective φ := by
    intro z
    exact ⟨⟨B.repr z 0, B.repr z 1⟩, by
      rw [hφ]
      have hs := B.sum_repr z
      rw [Fin.sum_univ_two, hB, hB] at hs
      simpa using hs⟩
  exact ⟨a, b, ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩⟩
