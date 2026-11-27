import OMAStatements.S_arxiv_2003_13166

-- Problem: A Conjecture on Induced Subgraphs of Cayley Graphs (Potechin, Tsang, arXiv:2003.13166, Conjecture 1)
-- Upstream: formal-conjectures statements/arxiv-2003.13166.lean:0 (declaration OMA.S_arxiv_2003_13166.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)

/-
The conjecture is false for non-abelian groups, as shown by Lehner and Verret
(Counterexamples to a conjecture on induced subgraphs of Cayley graphs, 2020).
Explicit instance used here: the dihedral group of order 18 with the three reflections
sr 0, sr 1, sr 3 as generating set. Its Cayley graph is cubic and bipartite: r j is adjacent
to sr (j + a) for a in {0, 1, 3}. The ten vertices
  r 0, r 1, r 3, r 4, r 7, sr 0, sr 2, sr 5, sr 6, sr 8
are more than half of the group and induce a perfect matching, so every vertex of this set has
exactly one neighbour inside it, while sqrt(3/2) > 1.
-/

open DihedralGroup

def cexS : Finset (DihedralGroup 9) := {sr 0, sr 1, sr 3}

def cexU : Finset (DihedralGroup 9) :=
  {r 0, r 1, r 3, r 4, r 7, sr 0, sr 2, sr 5, sr 6, sr 8}

def cexAdj (u v : DihedralGroup 9) : Bool :=
  decide (u ≠ v ∧ ((∃ s ∈ cexS, v = s * u) ∨ (∃ s ∈ cexS, u = s * v)))

theorem cexAdj_iff (u v : DihedralGroup 9) :
    (OMA.S_arxiv_2003_13166.cayley (cexS : Set (DihedralGroup 9))).Adj u v ↔
      cexAdj u v = true := by
  simp [OMA.S_arxiv_2003_13166.cayley, cexAdj, SimpleGraph.fromRel_adj]

set_option maxRecDepth 8192 in
theorem cexCount : ∀ u ∈ cexU, (cexU.filter (fun v => cexAdj u v = true)).card ≤ 1 := by
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2003_13166.main) := by
  intro h
  have hS1 : (1 : DihedralGroup 9) ∉ (cexS : Set (DihedralGroup 9)) := by
    rw [Finset.mem_coe]
    decide
  have hSinv : ∀ s ∈ (cexS : Set (DihedralGroup 9)), s⁻¹ ∈ (cexS : Set (DihedralGroup 9)) := by
    intro s hs
    rw [Finset.mem_coe] at hs ⊢
    revert s
    decide
  have hgen : Subgroup.closure (cexS : Set (DihedralGroup 9)) = ⊤ := by
    have h0 : (sr 0 : DihedralGroup 9) ∈ Subgroup.closure (cexS : Set (DihedralGroup 9)) :=
      Subgroup.subset_closure (Finset.mem_coe.2 (by decide))
    have h1 : (sr 1 : DihedralGroup 9) ∈ Subgroup.closure (cexS : Set (DihedralGroup 9)) :=
      Subgroup.subset_closure (Finset.mem_coe.2 (by decide))
    have hr1 : (r 1 : DihedralGroup 9) ∈ Subgroup.closure (cexS : Set (DihedralGroup 9)) := by
      have e : (sr 0 : DihedralGroup 9) * sr 1 = r 1 := by decide
      rw [← e]
      exact Subgroup.mul_mem _ h0 h1
    have hr : ∀ i : ZMod 9,
        (r i : DihedralGroup 9) ∈ Subgroup.closure (cexS : Set (DihedralGroup 9)) := by
      intro i
      have hpow := Subgroup.pow_mem _ hr1 i.val
      rw [DihedralGroup.r_one_pow] at hpow
      simpa using hpow
    refine eq_top_iff.2 (fun g _ => ?_)
    cases g with
    | r i => exact hr i
    | sr i =>
      have e : (sr 0 : DihedralGroup 9) * r i = sr i := by simp [DihedralGroup.sr_mul_r]
      rw [← e]
      exact Subgroup.mul_mem _ h0 (hr i)
  have hU : Nat.card (DihedralGroup 9) < 2 * (cexU : Set (DihedralGroup 9)).ncard := by
    rw [DihedralGroup.nat_card, Set.ncard_coe_finset]
    decide
  obtain ⟨u, hu, hle⟩ := h (DihedralGroup 9) (cexS : Set (DihedralGroup 9)) hS1 hSinv hgen
    (cexU : Set (DihedralGroup 9)) hU
  have hset : {v | v ∈ (cexU : Set (DihedralGroup 9)) ∧
      (OMA.S_arxiv_2003_13166.cayley (cexS : Set (DihedralGroup 9))).Adj u v}
      = ((cexU.filter (fun v => cexAdj u v = true) : Finset (DihedralGroup 9)) :
          Set (DihedralGroup 9)) := by
    ext v
    simp [cexAdj_iff]
  rw [hset, Set.ncard_coe_finset, Set.ncard_coe_finset] at hle
  have hc := cexCount u (Finset.mem_coe.1 hu)
  have hS3 : cexS.card = 3 := by decide
  rw [hS3] at hle
  have hlt : (1 : ℝ) < Real.sqrt (((3 : ℕ) : ℝ) / 2) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hc' : ((cexU.filter (fun v => cexAdj u v = true)).card : ℝ) ≤ 1 := by
    exact_mod_cast hc
  linarith
