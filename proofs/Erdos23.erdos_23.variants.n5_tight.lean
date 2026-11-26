import FormalConjectures.ErdosProblems.«23»

-- Problem: Erdős Problem 23 — n5 tight
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/23.lean:92 (declaration Erdos23.erdos_23.variants.n5_tight)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- The balanced blow-up of the 5-cycle on `Fin 25`: vertex `v` lies in part `v / 5`. -/
def blow : SimpleGraph (Fin 25) :=
  SimpleGraph.fromRel fun u v => (u.val / 5 + 1) % 5 = v.val / 5 ∨ (v.val / 5 + 1) % 5 = u.val / 5

/-- The `j`-th vertex of the 5-cycle indexed by `(a, b)`. -/
def vtx (a b j : Fin 5) : Fin 25 :=
  ⟨5 * j.val + (a.val + b.val * j.val) % 5, by
    have h1 := Nat.mod_lt (a.val + b.val * j.val) (show 0 < 5 by norm_num)
    have h2 := j.isLt
    omega⟩

theorem vtx_div (a b j : Fin 5) : (vtx a b j).val / 5 = j.val := by
  have h1 := Nat.mod_lt (a.val + b.val * j.val) (show 0 < 5 by norm_num)
  simp only [vtx]
  omega

theorem pigeon : ∀ f : Fin 5 → Fin 2, ∃ j : Fin 5, f j = f (j + 1) := by
  decide

theorem no_tri : ∀ x y z : Fin 5,
    ((x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val) →
    ((x.val + 1) % 5 = z.val ∨ (z.val + 1) % 5 = x.val) →
    ((y.val + 1) % 5 = z.val ∨ (z.val + 1) % 5 = y.val) → False := by
  decide

theorem vtx_inj : ∀ a b j a' b' j' : Fin 5,
    s(vtx a b j, vtx a b (j + 1)) = s(vtx a' b' j', vtx a' b' (j' + 1)) → a = a' ∧ b = b' := by
  decide +kernel

theorem blow_adj (a b j : Fin 5) : blow.Adj (vtx a b j) (vtx a b (j + 1)) := by
  have hj : (j + 1 : Fin 5).val = (j.val + 1) % 5 := by
    rw [Fin.val_add]
    rfl
  have h1 := vtx_div a b j
  have h2 := vtx_div a b (j + 1)
  rw [hj] at h2
  simp only [blow, SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, Or.inl (Or.inl ?_)⟩
  · rw [h] at h1
    have := j.isLt
    omega
  · rw [h1, h2]

theorem blow_cliqueFree : blow.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := hs
  simp only [blow, SimpleGraph.fromRel_adj] at hxy hxz hyz
  have hx : x.val / 5 < 5 := by omega
  have hy : y.val / 5 < 5 := by omega
  have hz : z.val / 5 < 5 := by omega
  exact no_tri ⟨_, hx⟩ ⟨_, hy⟩ ⟨_, hz⟩ (by tauto) (by tauto) (by tauto)

end OMA

open scoped Classical in
theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n5_tight := by
  refine ⟨OMA.blow, OMA.blow_cliqueFree, fun H hHG hH => ?_⟩
  obtain ⟨c⟩ := hH
  choose j hj using fun p : Fin 5 × Fin 5 => OMA.pigeon fun i => c (OMA.vtx p.1 p.2 i)
  let e : Fin 5 × Fin 5 → Sym2 (Fin 25) :=
    fun p => s(OMA.vtx p.1 p.2 (j p), OMA.vtx p.1 p.2 (j p + 1))
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Fin 5 × Fin 5)),
      e p ∈ OMA.blow.edgeFinset \ H.edgeFinset := by
    intro p _
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
    refine ⟨OMA.blow_adj _ _ _, fun hadj => ?_⟩
    exact c.valid hadj (hj p)
  have hinj : Set.InjOn e (Finset.univ : Finset (Fin 5 × Fin 5)) := by
    intro p _ q _ hpq
    have := OMA.vtx_inj _ _ _ _ _ _ hpq
    exact Prod.ext this.1 this.2
  have hcard := Finset.card_le_card_of_injOn e hmaps hinj
  simpa using hcard
