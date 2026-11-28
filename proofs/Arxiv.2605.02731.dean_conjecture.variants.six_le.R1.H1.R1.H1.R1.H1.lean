import OMAReductions.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H1_R1

/-!
Proof of `OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H1_R1.H1`.
Maximum cut: choose a two-colouring c of the vertices minimising the number of ordered
monochromatic adjacent pairs, and keep the bichromatic edges. Recolouring a vertex v changes
that number by twice (other(v) - same(v)), where other(v) and same(v) count the neighbours of
v of the other and of the same colour. By minimality other(v) is at least same(v), and their
sum is the degree of v, at least 6, so v keeps at least 3 neighbours in the bipartite subgraph.
-/

namespace OMAProof.Dean6H1

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Number of ordered monochromatic adjacent pairs. -/
def mono (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) : ℤ :=
  ∑ u, ∑ w, if G.Adj u w ∧ c u = c w then (1 : ℤ) else 0

/-- Change of the potential at a vertex. -/
def gain (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v x : V) : ℤ :=
  (if G.Adj v x ∧ c v ≠ c x then (1 : ℤ) else 0) - (if G.Adj v x ∧ c v = c x then (1 : ℤ) else 0)

/-- Neighbours of the other colour. -/
def other (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ c v ≠ c w)).card

/-- Neighbours of the same colour. -/
def same (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ c v = c w)).card

omit [Fintype V] in
lemma pointwise (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v u w : V) :
    (if G.Adj u w ∧ Function.update c v (!c v) u = Function.update c v (!c v) w then (1 : ℤ)
      else 0) =
    (if G.Adj u w ∧ c u = c w then (1 : ℤ) else 0) +
      ((if u = v then gain G c v w else 0) + (if w = v then gain G c v u else 0)) := by
  by_cases hu : u = v
  · subst hu
    by_cases hw : w = u
    · subst hw
      simp [gain]
    · simp only [Function.update_apply, if_neg hw, gain]
      by_cases ha : G.Adj u w
      · cases hcu : c u <;> cases hcw : c w <;> simp [ha]
      · simp [ha]
  · by_cases hw : w = v
    · subst hw
      simp only [Function.update_apply, if_neg hu, gain]
      by_cases ha : G.Adj u w
      · have ha' : G.Adj w u := ha.symm
        cases hcu : c u <;> cases hcw : c w <;> simp [ha, ha']
      · have ha' : ¬ G.Adj w u := fun h => ha h.symm
        simp [ha, ha']
    · simp [hu, hw]

lemma mono_update (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) :
    mono G (Function.update c v (!c v)) = mono G c + 2 * ∑ x, gain G c v x := by
  have h1 : (∑ u, ∑ w, if u = v then gain G c v w else (0 : ℤ)) = ∑ w, gain G c v w := by
    rw [Finset.sum_comm]
    simp
  have h2 : (∑ u, ∑ w, if w = v then gain G c v u else (0 : ℤ)) = ∑ u, gain G c v u := by
    simp
  unfold mono
  simp only [pointwise G c v, Finset.sum_add_distrib]
  rw [h1, h2]
  ring

omit [DecidableEq V] in
lemma sum_gain (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) :
    ∑ x, gain G c v x = (other G c v : ℤ) - (same G c v : ℤ) := by
  simp only [gain, other, same, Finset.sum_sub_distrib, Finset.card_filter]
  push_cast
  rfl

omit [DecidableEq V] in
lemma degree_split (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) :
    G.degree v = other G c v + same G c v := by
  rw [other, same, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases ha : G.Adj v w <;> by_cases hc : c v = c w <;> simp [ha, hc]

/-- The bichromatic edges of `G` under `c`. -/
def cutGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ c u ≠ c w
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun e => h.2 e.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (cutGraph G c).Adj :=
  fun u w => inferInstanceAs (Decidable (G.Adj u w ∧ c u ≠ c w))

omit [DecidableEq V] in
lemma cut_degree (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) :
    (cutGraph G c).degree v = other G c v := by
  rw [other, ← card_neighborFinset_eq_degree]
  congr 1
  ext w
  rw [mem_neighborFinset, mem_filter]
  exact ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩

end OMAProof.Dean6H1

open OMAProof.Dean6H1 SimpleGraph Finset in
theorem OMA.solution :
    OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H1_R1.H1 := by
  intro V _ _ G _ h6
  obtain ⟨c, -, hc⟩ := Finset.exists_min_image (univ : Finset (V → Bool)) (mono G)
    univ_nonempty
  refine ⟨cutGraph G c, inferInstance, fun u w h => h.1, ?_, ?_⟩
  · refine ⟨Coloring.mk (fun v => if c v then (0 : Fin 2) else 1) ?_⟩
    intro u w h
    have h2 : c u ≠ c w := h.2
    cases hu : c u <;> cases hw : c w <;> simp_all
  · rcases isEmpty_or_nonempty V with hV | hV
    · exfalso
      rw [minDegree_of_subsingleton] at h6
      omega
    refine le_minDegree_of_forall_le_degree _ _ fun v => ?_
    have hmin := hc (Function.update c v (!c v)) (mem_univ _)
    rw [mono_update, sum_gain] at hmin
    have hdeg := degree_split G c v
    have hG := G.minDegree_le_degree v
    have hH := cut_degree G c v
    have key : same G c v ≤ other G c v := by
      have : (same G c v : ℤ) ≤ other G c v := by
        linarith
      exact_mod_cast this
    rw [hH]
    omega
