import OMAStatements.S_mo_353633
import Mathlib

-- Problem: mo-353633, a Vandermonde matrix of rank k has exactly k distinct nodes.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The column space of the Vandermonde matrix of x_1..x_n consists of the vectors
-- (p(x_1), ..., p(x_n)) for polynomials p of degree < n. With S the set of distinct nodes
-- (so |S| <= n), Lagrange interpolation shows this is exactly the space of vectors of the form
-- (g(x_1), ..., g(x_n)) for g : S -> K, which has dimension |S|.

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_mo_353633.main := by
  intro K _ _ n k x hrank
  subst hrank
  have hxS : ∀ i, x i ∈ Finset.univ.image x := fun i =>
    Finset.mem_image_of_mem x (Finset.mem_univ i)
  have hsurj : Function.Surjective
      (fun i : Fin n => (⟨x i, hxS i⟩ : (Finset.univ.image x : Finset K))) := by
    rintro ⟨s, hs⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, rfl⟩
  have hcard : (Finset.univ.image x).card ≤ n := by
    calc (Finset.univ.image x).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_image_le
      _ = n := by simp
  have hrange : LinearMap.range (Matrix.vandermonde x).mulVecLin =
      LinearMap.range (LinearMap.funLeft K K
        (fun i : Fin n => (⟨x i, hxS i⟩ : (Finset.univ.image x : Finset K)))) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      refine ⟨fun s => ∑ j : Fin n, (s : K) ^ (j : ℕ) * c j, ?_⟩
      ext i
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    · rintro _ ⟨g, rfl⟩
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · refine ⟨0, ?_⟩
        ext i
        exact absurd i.2 (by omega)
      · have hinj : Set.InjOn (id : K → K) (Finset.univ.image x : Finset K) :=
          Function.injective_id.injOn
        have hdeg : (Lagrange.interpolate (Finset.univ.image x) id
            (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0)).degree <
            ((Finset.univ.image x).card : WithBot ℕ) :=
          Lagrange.degree_interpolate_lt _ hinj
        have hnat : (Lagrange.interpolate (Finset.univ.image x) id
            (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0)).natDegree < n := by
          by_cases hp : Lagrange.interpolate (Finset.univ.image x) id
              (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0) = 0
          · rw [hp, natDegree_zero]
            exact hnpos
          · exact (natDegree_lt_iff_degree_lt hp).mpr
              (lt_of_lt_of_le hdeg (by exact_mod_cast hcard))
        refine ⟨fun j => (Lagrange.interpolate (Finset.univ.image x) id
            (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0)).coeff j, ?_⟩
        ext i
        have heval : eval (x i) (Lagrange.interpolate (Finset.univ.image x) id
            (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0)) =
            g ⟨x i, hxS i⟩ := by
          have h1 := Lagrange.eval_interpolate_at_node
            (r := fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0) hinj (hxS i)
          simpa [hxS i] using h1
        rw [Matrix.mulVecLin_apply, LinearMap.funLeft_apply, ← heval,
          eval_eq_sum_range' hnat,
          ← Fin.sum_univ_eq_sum_range (fun j => (Lagrange.interpolate (Finset.univ.image x) id
            (fun t => if h : t ∈ Finset.univ.image x then g ⟨t, h⟩ else 0)).coeff j * x i ^ j) n]
        simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [Matrix.rank, hrange,
    LinearMap.finrank_range_of_inj (LinearMap.funLeft_injective_of_surjective K K _ hsurj),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
