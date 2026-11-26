import FormalConjectures.ErdosProblems.«902»

-- Problem: Erdős Problem 902 — f two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/902.lean:130 (declaration Erdos902.erdos_902.variants.f_two)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMA

/-- In a tournament with property `S_2`, every vertex has at least three in-neighbours. -/
theorem indeg_ge_three {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
    [DecidableRel G.Adj]
    (hG : G.IsTournament) (hS : Erdos902.HasPropertyS G 2) (v : Fin m) :
    3 ≤ (univ.filter (fun x => G.Adj x v)).card := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨x1, hx1, h1⟩ := hS {v, u} (card_pair hu.symm)
  have a1 : G.Adj x1 v := h1 v (by simp)
  have n1 : v ≠ x1 := fun h => hG.1 v (h ▸ a1)
  obtain ⟨x2, hx2, h2⟩ := hS {v, x1} (card_pair n1)
  have a2 : G.Adj x2 v := h2 v (by simp)
  have b2 : G.Adj x2 x1 := h2 x1 (by simp)
  have n2 : v ≠ x2 := fun h => hG.1 v (h ▸ a2)
  obtain ⟨x3, hx3, h3⟩ := hS {v, x2} (card_pair n2)
  have a3 : G.Adj x3 v := h3 v (by simp)
  have b3 : G.Adj x3 x2 := h3 x2 (by simp)
  have e12 : x1 ≠ x2 := fun h => hG.1 x1 (h ▸ b2)
  have e23 : x2 ≠ x3 := fun h => hG.1 x2 (h ▸ b3)
  have e13 : x1 ≠ x3 := by
    intro h
    rw [← h] at b3
    exact ((hG.2 x1 x2 e12).1 b3) b2
  have hsub : ({x1, x2, x3} : Finset (Fin m)) ⊆ univ.filter (fun x => G.Adj x v) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [mem_filter]
    rcases hy with rfl | rfl | rfl
    · exact ⟨mem_univ _, a1⟩
    · exact ⟨mem_univ _, a2⟩
    · exact ⟨mem_univ _, a3⟩
  calc 3 = ({x1, x2, x3} : Finset (Fin m)).card := (card_eq_three.mpr ⟨x1, x2, x3, e12, e13, e23, rfl⟩).symm
    _ ≤ _ := card_le_card hsub

/-- A tournament on `m` vertices has `m * m - m` ordered pairs, half of them arcs. -/
theorem two_mul_arcs {m : ℕ} (G : Digraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.IsTournament) :
    2 * ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card = m * m - m := by
  have hT : ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card =
      ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.1 p.2)).card := by
    simp only [card_filter]
    rw [Fintype.sum_prod_type_right]
  have hswap : ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.2 p.1)).card =
      ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.1 p.2)).card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, hp.2⟩
    · intro p _ q _ h
      rw [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      rw [mem_filter] at hq
      exact ⟨(q.2, q.1), by rw [mem_filter]; exact ⟨mem_univ _, hq.2⟩, rfl⟩
  have hunion : ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.1 p.2)) ∪
      ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.2 p.1)) =
      (univ : Finset (Fin m)).offDiag := by
    ext p
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_offDiag]
    constructor
    · rintro (h | h)
      · exact fun e => hG.1 p.1 (by rw [← e] at h; exact h)
      · exact fun e => hG.1 p.1 (by rw [← e] at h; exact h)
    · intro hne
      by_cases h : G.Adj p.1 p.2
      · exact Or.inl h
      · exact Or.inr (by
          by_contra h'
          exact h ((hG.2 p.1 p.2 hne).2 h'))
  have hdisj : Disjoint ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.1 p.2))
      ((univ : Finset (Fin m × Fin m)).filter (fun p => G.Adj p.2 p.1)) := by
    rw [disjoint_left]
    intro p hp hq
    rw [mem_filter] at hp hq
    have hne : p.1 ≠ p.2 := fun e => hG.1 p.1 (by have := hp.2; rw [← e] at this; exact this)
    exact (hG.2 p.1 p.2 hne).1 hp.2 hq.2
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, offDiag_card, hswap] at hcard
  simp only [card_univ, Fintype.card_fin] at hcard
  rw [hT]
  omega

theorem seven_le {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
    (hG : G.IsTournament) (hS : Erdos902.HasPropertyS G 2) : 7 ≤ m := by
  classical
  have h1 : ∑ _v : Fin m, 3 ≤ ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card :=
    sum_le_sum (fun v _ => indeg_ge_three hm G hG hS v)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 := two_mul_arcs G hG
  by_contra hlt
  have hm7 : m < 7 := by omega
  interval_cases m <;> omega

end OMA

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.f_two := by
  refine le_antisymm Erdos902.f_two_le (le_csInf ⟨7, ?_⟩ ?_)
  · refine ⟨by norm_num, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
      ⟨by decide, by decide⟩, ?_⟩
    intro E hE
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
    have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
        a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
      decide
    obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
    refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ha
    · rw [Finset.mem_singleton.1 he]
      exact hb
  · rintro m ⟨hm, G, hG, hS⟩
    exact OMA.seven_le hm G hG hS
