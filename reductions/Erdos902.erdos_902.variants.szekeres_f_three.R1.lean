import FormalConjectures.ErdosProblems.«902»

/-!
For the upper bound use the quadratic-residue tournament on 19 vertices.
For the lower bound it suffices to exclude tournaments on exactly 18 vertices:
a smaller witness extends by cloning vertices. Averaging the in-degrees and
applying the two-vertex domination bound to an in-neighborhood leaves only
the two indicated degrees.
-/

namespace OMA.R_Erdos902_erdos_902_variants_szekeres_f_three_R1

open Erdos902 Finset

private theorem nineteen : ∃ G : Digraph (Fin 19), G.IsTournament ∧ HasPropertyS G 3 := by
  let Q : Finset (Fin 19) := {1, 4, 5, 6, 7, 9, 11, 16, 17}
  let G : Digraph (Fin 19) := ⟨fun a b => b - a ∈ Q⟩
  refine ⟨G, ⟨by decide, by decide⟩, ?_⟩
  -- Translation by the first vertex leaves only two offsets to check.
  have cover : ∀ i j : Fin 19, ∃ t : Fin 19, -t ∈ Q ∧ i - t ∈ Q ∧ j - t ∈ Q := by
    decide +kernel
  intro E hE
  obtain ⟨a, b, c, _, _, _, rfl⟩ := card_eq_three.mp hE
  obtain ⟨t, h0, h1, h2⟩ := cover (b - a) (c - a)
  have allAdj : ∀ e ∈ ({a,b,c} : Finset (Fin 19)), G.Adj (a+t) e := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    change e - (a+t) ∈ Q
    rcases he with rfl | rfl | rfl
    · simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using h0
    · simpa only [sub_add_eq_sub_sub] using h1
    · simpa only [sub_add_eq_sub_sub] using h2
  exact ⟨a+t, fun h => (show ¬ G.Adj (a+t) (a+t) from fun hloop =>
    (show (0 : Fin 19) ∉ Q by decide) (by simpa [G] using hloop)) (allAdj _ h), allAdj⟩

-- In-degree counting lemmas adapted from @luciusacarr's proof of
-- Erdos902.erdos_902.variants.f_two in this repository.
/-- In a tournament with property `S_2`, every vertex has at least three in-neighbours. -/
private theorem indeg_ge_three {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
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
private theorem two_mul_arcs {m : ℕ} (G : Digraph (Fin m)) [DecidableRel G.Adj]
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

private theorem seven_le {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
    (hG : G.IsTournament) (hS : Erdos902.HasPropertyS G 2) : 7 ≤ m := by
  classical
  have h1 : ∑ _v : Fin m, 3 ≤ ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card :=
    sum_le_sum (fun v _ => indeg_ge_three hm G hG hS v)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 := two_mul_arcs G hG
  by_contra hlt
  have hm7 : m < 7 := by omega
  interval_cases m <;> omega


private theorem dominate_small {m : ℕ} {G : Digraph (Fin m)} (hm : 3 ≤ m)
    (hS : HasPropertyS G 3) (s : Finset (Fin m)) (hs : s.card ≤ 3) :
    ∃ x ∉ s, ∀ y ∈ s, G.Adj x y := by
  obtain ⟨t, hst, _, ht⟩ := exists_subsuperset_card_eq (subset_univ s) hs (by simpa using hm)
  obtain ⟨x, hx, h⟩ := hS t ht
  exact ⟨x, fun hxs => hx (hst hxs), fun y hy => h y (hst hy)⟩

private theorem extend_to_eighteen {m : ℕ} (hm : 3 ≤ m) (hm' : m ≤ 18)
    (G : Digraph (Fin m)) (hG : G.IsTournament) (hS : HasPropertyS G 3) :
    ∃ T : Digraph (Fin 18), T.IsTournament ∧ HasPropertyS T 3 := by
  classical
  let π (x : Fin 18) : Fin m := if h : x.val < m then ⟨x.val, h⟩ else ⟨0, by omega⟩
  let lift (x : Fin m) : Fin 18 := x.castLE hm'
  have section_eq (x : Fin m) : π (lift x) = x := by simp [π, lift, x.isLt]
  let T : Digraph (Fin 18) := ⟨fun x y => if π x = π y then x < y else G.Adj (π x) (π y)⟩
  refine ⟨T, ⟨fun x => by simp [T], ?_⟩, ?_⟩
  · intro x y hxy
    by_cases h : π x = π y
    · simp only [T, h, if_true, not_lt]
      exact lt_iff_le_and_ne.trans (and_iff_left hxy)
    · simpa [T, h, Ne.symm h] using hG.2 (π x) (π y) h
  · intro E hE
    obtain ⟨u, hu, h⟩ := dominate_small hm hS (E.image π) ((card_image_le).trans hE.le)
    refine ⟨lift u, fun hmem => hu (section_eq u ▸ mem_image_of_mem π hmem), ?_⟩
    intro y hy
    have hy' := mem_image_of_mem π hy
    have hne : u ≠ π y := fun e => hu (e.symm ▸ hy')
    simpa [T, section_eq, hne] using h (π y) hy'

private theorem neighborhood_bound (G : Digraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.IsTournament) (hS : HasPropertyS G 3) (v : Fin 18) :
    7 ≤ (univ.filter (fun u => G.Adj u v)).card := by
  classical
  let N := univ.filter (fun u => G.Adj u v)
  have memN (x : Fin 18) : x ∈ N ↔ G.Adj x v := by simp [N]
  have hv : v ∉ N := fun hv => hG.1 v ((memN v).mp hv)
  obtain ⟨a, _, ha⟩ := dominate_small (by decide) hS {v} (by simp)
  have haN := (memN a).mpr (ha v (by simp))
  obtain ⟨b, hb, h⟩ := dominate_small (by decide) hS {a,v}
    (by simpa using (card_insert_le a {v}).trans (show ({v} : Finset _).card + 1 ≤ 3 by simp))
  have hbN := (memN b).mpr (h v (by simp))
  have hab : a ≠ b := fun e => hb (by simp [e])
  have htwo : 2 ≤ N.card := by
    rw [← card_pair hab]
    apply card_le_card
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact haN
    · exact mem_singleton.mp hx ▸ hbN
  let e : Fin N.card ≃ N := N.equivFin.symm
  let T : Digraph (Fin N.card) := ⟨fun x y => G.Adj (e x).val (e y).val⟩
  apply seven_le htwo T
  · refine ⟨fun x => hG.1 _, fun x y hxy => hG.2 _ _ ?_⟩
    exact fun heq => hxy (e.injective (Subtype.ext heq))
  · intro E hE
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hE
    let u := (e i).val
    let w := (e j).val
    have huw : u ≠ w := fun h => hij (e.injective (Subtype.ext h))
    have huv : u ≠ v := fun h => hv (h ▸ (e i).property)
    have hwv : w ≠ v := fun h => hv (h ▸ (e j).property)
    obtain ⟨x, hx, hdom⟩ := hS {u,w,v} (card_eq_three.mpr ⟨u,w,v,huw,huv,hwv,rfl⟩)
    let z : N := ⟨x, (memN x).mpr (hdom v (by simp))⟩
    have hz : (e (e.symm z)).val = x := by simp [z]
    have hzu : x ≠ u := fun h => hx (by simp [h])
    have hzw : x ≠ w := fun h => hx (by simp [h])
    refine ⟨e.symm z, ?_, ?_⟩
    · intro hm
      rcases mem_insert.mp hm with he | he
      · exact hzu (hz.symm.trans (congrArg (fun k => (e k).val) he))
      · exact hzw (hz.symm.trans (congrArg (fun k => (e k).val) (mem_singleton.mp he)))
    · intro k hk
      change G.Adj (e (e.symm z)).val (e k).val
      rw [hz]
      rcases mem_insert.mp hk with rfl | hk
      · exact hdom u (by simp)
      · rw [mem_singleton.mp hk]
        exact hdom w (by simp)

def H1 : Prop :=
  ∀ (G : Digraph (Fin 18)) [DecidableRel G.Adj], G.IsTournament →
    ∀ v, (univ.filter (fun u => G.Adj u v)).card = 7 → ¬ HasPropertyS G 3

def H2 : Prop :=
  ∀ (G : Digraph (Fin 18)) [DecidableRel G.Adj], G.IsTournament →
    ∀ v, (univ.filter (fun u => G.Adj u v)).card = 8 → ¬ HasPropertyS G 3

theorem main : H1 → H2 → type_of% @Erdos902.erdos_902.variants.szekeres_f_three := by
  classical
  intro h7 h8
  have h19 : 19 ∈ {m : ℕ | 3 ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G 3} :=
    ⟨by decide, nineteen⟩
  apply le_antisymm (Nat.sInf_le h19)
  apply le_csInf ⟨19, h19⟩
  rintro m ⟨hm, G, hG, hS⟩
  by_contra! hlt
  obtain ⟨T, ht, hs⟩ := extend_to_eighteen hm (by omega) G hG hS
  let deg (v : Fin 18) := (univ.filter (fun x => T.Adj x v)).card
  have low : ∃ v, deg v ≤ 8 := by
    by_contra! hall
    have hsum := sum_le_sum (s := univ) (fun v _ => show 9 ≤ deg v from hall v)
    have arcs := two_mul_arcs T ht
    change 2 * ∑ v, deg v = _ at arcs
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega
  obtain ⟨v,hv⟩ := low
  have lo : 7 ≤ deg v := neighborhood_bound T ht hs v
  rcases (show deg v = 7 ∨ deg v = 8 by omega) with h | h
  · exact h7 T ht v h hs
  · exact h8 T ht v h hs

end OMA.R_Erdos902_erdos_902_variants_szekeres_f_three_R1
