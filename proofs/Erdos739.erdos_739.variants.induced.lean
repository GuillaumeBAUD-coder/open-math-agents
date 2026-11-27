import FormalConjectures.ErdosProblems.«739»

-- Problem: Erdős Problem 739 — induced
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/739.lean:85 (declaration Erdos739.erdos_739.variants.induced)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.GalvinShift

open Cardinal

universe u

/-- Increasing pairs of a linear order. -/
def P (S : Type u) [LinearOrder S] : Type u := {p : S × S // p.1 < p.2}

/-- The shift graph: `(x, y)` is adjacent to `(y, z)`. -/
def shiftGraph (S : Type u) [LinearOrder S] : SimpleGraph (P S) where
  Adj p q := p.1.2 = q.1.1 ∨ q.1.2 = p.1.1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by
    rcases h with h | h <;> exact (ne_of_gt p.2) h⟩

variable {S : Type u} [LinearOrder S]

theorem shiftGraph_adj {p q : P S} :
    (shiftGraph S).Adj p q ↔ (p.1.2 = q.1.1 ∨ q.1.2 = p.1.1) := Iff.rfl

/-- A coloring of the whole shift graph by `C` gives an injection `S → Set C`. -/
theorem mk_le_of_coloring {C : Type u} (h : (shiftGraph S).Coloring C) :
    #S ≤ 2 ^ #C := by
  rw [← Cardinal.mk_set]
  let g : S → Set C := fun x => {c | ∃ q : P S, q.1.1 = x ∧ h q = c}
  have key : ∀ q : P S, h q ∈ g q.1.1 ∧ h q ∉ g q.1.2 := by
    intro q
    refine ⟨⟨q, rfl, rfl⟩, ?_⟩
    rintro ⟨q', hq', hc⟩
    exact h.valid (shiftGraph_adj.2 (Or.inl hq'.symm)) hc.symm
  refine Cardinal.mk_le_of_injective (f := g) ?_
  intro x y hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨h1, h2⟩ := key ⟨(x, y), hlt⟩
    exact h2 (hxy ▸ h1)
  · obtain ⟨h1, h2⟩ := key ⟨(y, x), hlt⟩
    exact h2 (hxy ▸ h1)

/-- The antichain map. -/
def phi {K : Type u} (A : Set K) : Set (K × Bool) :=
  {p | (p.2 = true ∧ p.1 ∈ A) ∨ (p.2 = false ∧ p.1 ∉ A)}

theorem phi_subset {K : Type u} {A B : Set K} (h : phi A ⊆ phi B) : A = B := by
  ext k
  constructor
  · intro hk
    have := h (show (k, true) ∈ phi A from Or.inl ⟨rfl, hk⟩)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · simp at h1
  · intro hk
    by_contra hnk
    have := h (show (k, false) ∈ phi A from Or.inr ⟨rfl, hnk⟩)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · simp at h1
    · exact h2 hk

/-- Galvin's lemma: a coloring of an induced subgraph with `2 ^ #C = #(Set K)` gives a coloring
by `K × Bool`. -/
theorem coloring_of_induce {s : Set (P S)} {C K : Type u}
    (h : ((shiftGraph S).induce s).Coloring C) (e : Set C ≃ Set K) :
    Nonempty (((shiftGraph S).induce s).Coloring (K × Bool)) := by
  let g : S → Set C := fun x => {c | ∃ q : s, q.1.1.1 = x ∧ h q = c}
  have key : ∀ q : s, h q ∈ g q.1.1.1 ∧ h q ∉ g q.1.1.2 := by
    intro q
    refine ⟨⟨q, rfl, rfl⟩, ?_⟩
    rintro ⟨q', hq', hc⟩
    exact h.valid (SimpleGraph.induce_adj.2 (shiftGraph_adj.2 (Or.inl hq'.symm))) hc.symm
  let G' : S → Set (K × Bool) := fun x => phi (e (g x))
  have hns : ∀ q : s, ¬ G' q.1.1.1 ⊆ G' q.1.1.2 := by
    intro q hsub
    have h1 := e.injective (phi_subset hsub)
    obtain ⟨k1, k2⟩ := key q
    exact k2 (h1 ▸ k1)
  have hex : ∀ q : s, ∃ c, c ∈ G' q.1.1.1 ∧ c ∉ G' q.1.1.2 := by
    intro q
    exact Set.not_subset.1 (hns q)
  choose col hcol using hex
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro q q' hadj
  rcases shiftGraph_adj.1 (SimpleGraph.induce_adj.1 hadj) with h' | h'
  · intro hc
    exact (hcol q).2 (h' ▸ hc ▸ (hcol q').1)
  · intro hc
    exact (hcol q').2 (h' ▸ hc ▸ (hcol q).1)

/-- Chromatic cardinal of a graph that is colorable by `C` is at most `#C`. -/
theorem chrom_le {V : Type u} {G : SimpleGraph V} {C : Type u} (h : G.Coloring C) :
    G.chromaticCardinal ≤ #C :=
  csInf_le' ⟨C, rfl, ⟨h⟩⟩

/-- Some coloring realises the chromatic cardinal. -/
theorem exists_coloring_chrom {V : Type u} (G : SimpleGraph V) :
    ∃ C : Type u, #C = G.chromaticCardinal ∧ Nonempty (G.Coloring C) := by
  have hne : {κ : Cardinal.{u} | ∃ (C : Type u) (_ : #C = κ), Nonempty (G.Coloring C)}.Nonempty :=
    ⟨#V, V, rfl, ⟨SimpleGraph.Coloring.mk id (fun h => G.ne_of_adj h)⟩⟩
  obtain ⟨C, hC, hcol⟩ := csInf_mem hne
  exact ⟨C, hC, hcol⟩

theorem main_inf (H : ∀ (V : Type u) (G : SimpleGraph V) (n : Cardinal.{u}),
      ℵ₀ ≤ n → n < G.chromaticCardinal →
        ∃ s : Set V, (G.induce s).chromaticCardinal = n)
    (κ μ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hκμ : κ < μ) (heq : (2 : Cardinal.{u}) ^ μ = 2 ^ κ) :
    False := by
  have hμ : ℵ₀ ≤ μ := hκ.trans hκμ.le
  let T : Type u := Set (Quotient.out (2 ^ μ : Cardinal.{u}))
  let _ : LinearOrder T := IsWellOrder.linearOrder WellOrderingRel
  have hT : 2 ^ μ < #T := by
    simp only [T, Cardinal.mk_set, Cardinal.mk_out]
    exact Cardinal.cantor _
  have hlt : μ < (shiftGraph T).chromaticCardinal := by
    by_contra hle
    push Not at hle
    obtain ⟨C, hC, ⟨h⟩⟩ := exists_coloring_chrom (shiftGraph T)
    have h1 := mk_le_of_coloring h
    have h2 : (2 : Cardinal.{u}) ^ #C ≤ 2 ^ μ :=
      Cardinal.power_le_power_left two_ne_zero (hC ▸ hle)
    exact absurd (h1.trans h2) (not_le.2 hT)
  obtain ⟨s, hs⟩ := H _ (shiftGraph T) μ hμ hlt
  obtain ⟨C, hC, ⟨h⟩⟩ := exists_coloring_chrom ((shiftGraph T).induce s)
  rw [hs] at hC
  have hcard : #(Set C) = #(Set (Quotient.out κ)) := by
    rw [Cardinal.mk_set, Cardinal.mk_set, Cardinal.mk_out, hC, heq]
  obtain ⟨e⟩ := Cardinal.eq.1 hcard
  obtain ⟨h'⟩ := coloring_of_induce h e
  have hle := chrom_le h'
  rw [hs] at hle
  have hprod : #(Quotient.out κ × Bool) < μ := by
    have e2 : #(Quotient.out κ × Bool) = κ * 2 := by simp [Cardinal.mk_prod]
    rw [e2]
    exact Cardinal.mul_lt_of_lt hμ hκμ
      ((Cardinal.natCast_lt_aleph0 (n := 2)).trans_le hμ)
  exact absurd (hle.trans_lt hprod) (lt_irrefl _)

end OMA.GalvinShift

theorem OMA.solution : type_of% @Erdos739.erdos_739.variants.induced := by
  intro H κ μ hκμ
  by_contra hlt
  have hle : (2 : Cardinal) ^ μ ≤ 2 ^ κ := not_lt.1 hlt
  rcases lt_or_ge μ Cardinal.aleph0 with hμ | hμ
  · obtain ⟨m, rfl⟩ := Cardinal.lt_aleph0.1 hμ
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 (hκμ.trans hμ)
    have hnm : n < m := by exact_mod_cast hκμ
    have : (2 : Cardinal) ^ (m : Cardinal) ≤ 2 ^ (n : Cardinal) := hle
    have h2 : 2 ^ m ≤ 2 ^ n := by exact_mod_cast this
    have h3 : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hnm
    omega
  rcases lt_or_ge κ Cardinal.aleph0 with hκ | hκ
  · have h1 : (2 : Cardinal) ^ κ < Cardinal.aleph0 :=
      Cardinal.power_lt_aleph0 (Cardinal.natCast_lt_aleph0 (n := 2)) hκ
    have h2 : Cardinal.aleph0 < 2 ^ μ := hμ.trans_lt (Cardinal.cantor μ)
    exact absurd (hle.trans_lt (h1.trans h2)) (lt_irrefl _)
  · exact OMA.GalvinShift.main_inf H κ μ hκ hκμ
      (le_antisymm hle (Cardinal.power_le_power_left two_ne_zero hκμ.le))
