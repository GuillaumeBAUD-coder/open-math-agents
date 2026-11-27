import FormalConjectures.ErdosProblems.«133»

open Filter SimpleGraph
open scoped Classical

theorem OMA.solution : type_of% @Erdos133.erdos_133.variants.lower_bound := by
  classical
  intro ε hε
  by_cases hε₁ : 1 ≤ ε
  · exact Eventually.of_forall fun _ =>
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hε₁) (Real.sqrt_nonneg _)).trans
        (Nat.cast_nonneg _)
  have hf : 0 ≤ 1 - ε := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε)
  filter_upwards [eventually_ge_atTop (3 : ℕ), eventually_ge_atTop N] with n hn hnN
  let r : Fin n := ⟨0, by omega⟩
  have hne : {d : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
      ∀ v, G.degree v ≤ d}.Nonempty := by
    let a : Fin n := ⟨1, by omega⟩; let b : Fin n := ⟨2, by omega⟩
    have ha : a ≠ r := by simp [Fin.ext_iff, a, r]
    have hb : b ≠ r := by simp [Fin.ext_iff, b, r]
    have hab : a ≠ b := by simp [Fin.ext_iff, a, b]
    let G := starGraph r
    have hup : G.ediam ≤ 2 := by
      have : G.eccent r ≤ 1 := (eccent_le_one_iff r).mpr fun _ h => starGraph_center_adj h
      calc G.ediam ≤ 2 * G.eccent r := ediam_le_two_mul_eccent r
        _ ≤ 2 * 1 := by gcongr
        _ = 2 := by simp
    have hlo : 2 ≤ G.ediam := by
      have : G.edist a b = 2 := edist_eq_two_iff.mpr
        ⟨hab, by simp [G, ha, hb],
          ⟨r, G.mem_commonNeighbors.mpr ⟨starGraph_center_adj' ha.symm, starGraph_center_adj' hb.symm⟩⟩⟩
      exact this ▸ edist_le_ediam
    exact ⟨n, G, (isAcyclic_starGraph r).cliqueFree (by decide),
      by rw [SimpleGraph.diam, le_antisymm hup hlo]; rfl,
      fun v => by
        let : DecidableRel G.Adj := fun u w => Classical.propDecidable (G.Adj u w)
        exact Nat.le_of_lt (by simpa using G.degree_lt_card_verts v)⟩
  obtain ⟨G, _, hdiam, hdeg⟩ := Nat.sInf_mem hne
  have hed : G.ediam = 2 := (ENat.toNat_eq_iff (by decide : (2 : ℕ) ≠ 0)).mp hdiam
  let br (u : Fin n) := insert u ((G.neighborFinset u).erase r)
  have hcov : (Finset.univ : Finset (Fin n)) ⊆ insert r ((G.neighborFinset r).biUnion br) := by
    intro v _
    by_cases hvr : v = r
    · simp [hvr]
    apply Finset.mem_insert_of_mem
    by_cases hadj : G.Adj r v
    · exact Finset.mem_biUnion.mpr ⟨v, (G.mem_neighborFinset r v).mpr hadj, Finset.mem_insert_self _ _⟩
    have hcm : (G.commonNeighbors r v).Nonempty := by
      by_contra h
      exact not_lt_of_ge (hed ▸ edist_le_ediam : G.edist r v ≤ 2)
        (two_lt_edist_iff.mpr ⟨Ne.symm hvr, hadj, Set.not_nonempty_iff_eq_empty.mp h⟩)
    obtain ⟨u, hu⟩ := hcm
    obtain ⟨hru, hvu⟩ := G.mem_commonNeighbors.mp hu
    exact Finset.mem_biUnion.mpr ⟨u, (G.mem_neighborFinset r u).mpr hru,
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvr, (G.mem_neighborFinset u v).mpr hvu.symm⟩)⟩
  have hbr (u : Fin n) (hu : u ∈ G.neighborFinset r) : (br u).card ≤ Erdos133.f n := by
    have hur : r ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u r).mpr ((G.mem_neighborFinset r u).mp hu).symm
    have := Finset.card_insert_le u ((G.neighborFinset u).erase r)
    have := Finset.card_erase_of_mem hur
    have := Finset.card_pos.mpr ⟨r, hur⟩
    have : (G.neighborFinset u).card ≤ Erdos133.f n := hdeg u
    dsimp [br]; omega
  have hbound : n ≤ Erdos133.f n ^ 2 + 1 := by
    have h1 := (Finset.card_le_card hcov).trans (Finset.card_insert_le _ _)
    have h2 := Finset.card_biUnion_le_card_mul _ _ _ hbr
    have h3 : (G.neighborFinset r).card ≤ Erdos133.f n := hdeg r
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    nlinarith
  have hmul : 1 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp (hN.trans (by exact_mod_cast hnN))
  have hcount : (n : ℝ) ≤ (Erdos133.f n : ℝ) ^ 2 + 1 := by exact_mod_cast hbound
  have hsq : ((1 - ε) * Real.sqrt n) ^ 2 ≤ (Erdos133.f n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_right (show (1 - ε) ^ 2 ≤ 1 - ε by nlinarith) (Nat.cast_nonneg n)]
  exact (sq_le_sq₀ (mul_nonneg hf (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)).mp hsq
