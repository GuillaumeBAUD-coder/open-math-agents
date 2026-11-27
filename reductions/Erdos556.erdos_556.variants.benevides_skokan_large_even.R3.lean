import FormalConjectures.ErdosProblems.«556»
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin

/-!
Credit: @fqlx.

An exact component reduction for the three-colour even-cycle Ramsey theorem.
This is a conditional reduction, not a proof of its two independent hypotheses.
The first branch has a monochromatic component of more than three quarters of
all vertices. The second has four nonempty classes with the exact cross-colour
pattern of the three perfect matchings of K4, and has no component of that size.

The sharp lower-bound construction and its checked cardinality argument below
are reused from @senamakel's R1 and @abduljaleel's R2 reductions. The new component
lemmas establish the exhaustive structural split used in the upper-bound proof.
-/

open Filter SimpleGraph
open scoped Fin.NatCast

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3

theorem rc4_no_cycle (N m : ℕ) (G : SimpleGraph (Fin N)) (P : Fin N → Prop)
    (hP : ∀ u v, P u → P v → u = v) (L : Fin N → ℕ)
    (hL : ∀ u v, G.Adj u v → ¬ P u → ¬ P v → L u = L v)
    (hc : ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ P v → L v = j →
      (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m)) :
    ¬ cycleGraph (2 * m + 2) ⊑ G := by
  classical
  have : NeZero (2 * m + 2) := ⟨by omega⟩
  rintro ⟨f⟩
  have hinj := f.injective
  -- choose the base index
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (2 * m + 2), ∀ i, P (f i) → i = i0 := by
    by_cases hh : ∃ i, P (f i)
    · obtain ⟨i, hi⟩ := hh
      exact ⟨i, fun j hj => hinj (hP _ _ hj hi)⟩
    · push Not at hh
      exact ⟨0, fun j hj => absurd hj (hh j)⟩
  let idx : ℕ → Fin (2 * m + 2) := fun t => i0 + ((t + 1 : ℕ) : Fin (2 * m + 2))
  have hidx_ne : ∀ t, t < 2 * m + 1 → idx t ≠ i0 := by
    intro t ht h
    have h2 : ((t + 1 : ℕ) : Fin (2 * m + 2)) = 0 := by
      have := congrArg (fun x => x - i0) h
      simpa [idx] using this
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    simp at this
  have hidx_inj : ∀ a b, a < 2 * m + 1 → b < 2 * m + 1 → idx a = idx b → a = b := by
    intro a b ha hb h
    have h2 : ((a + 1 : ℕ) : Fin (2 * m + 2)) = ((b + 1 : ℕ) : Fin (2 * m + 2)) := by
      simpa [idx] using h
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hnP : ∀ t, t < 2 * m + 1 → ¬ P (f (idx t)) := by
    intro t ht h
    exact hidx_ne t ht (hi0 _ h)
  have hadj : ∀ t, G.Adj (f (idx (t + 1))) (f (idx t)) := by
    intro t
    apply f.toHom.map_adj
    rw [cycleGraph_adj]
    left
    simp only [idx]
    push_cast
    abel
  have hlab : ∀ t, t < 2 * m + 1 → L (f (idx t)) = L (f (idx 0)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [← ih (by omega)]
      exact hL _ _ (hadj t) (hnP _ ht) (hnP _ (by omega))
  obtain ⟨a, b, hab⟩ := hc (L (f (idx 0)))
  let S : Finset ℕ := Finset.range (2 * m + 1)
  have hmaps : ∀ t ∈ S, (f (idx t)).val ∈ Finset.Ico a (a + m) ∪ Finset.Ico b (b + m) := by
    intro t ht
    have ht' : t < 2 * m + 1 := Finset.mem_range.mp ht
    rcases hab _ (hnP t ht') (hlab t ht') with h | h
    · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr h)
  have hinjOn : Set.InjOn (fun t => (f (idx t)).val) S := by
    intro x hx y hy hxy
    exact hidx_inj x y (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
      (hinj (Fin.ext hxy))
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinjOn
  have h2 := Finset.card_union_le (Finset.Ico a (a + m)) (Finset.Ico b (b + m))
  simp [S] at h1 h2
  omega


theorem rc4_key_red : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 4 → t ≠ 4 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 0 →
    (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_green : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 5 → t ≠ 5 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 1 →
    (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_blue : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 6 → t ≠ 6 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 2 →
    (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_lower (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN : N ≤ 4 * m + 3)
    (ty : ℕ → ℕ) (hty : ∀ v, ty v = if v < m then 0 else if v < 2 * m then 1 else
      if v < 3 * m then 2 else if v < 4 * m then 3 else v - 4 * m + 4)
    (κ : ℕ → ℕ → ℕ) (hκ : ∀ s t, κ s t = if s = 6 ∨ t = 6 then 2 else
      if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else
      if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) :
    ∃ c : Fin 3 → SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c ∧
      ∀ i, ¬ cycleGraph (2 * m + 2) ⊑ c i := by
  have hκs : ∀ s t, κ s t = κ t s := by
    intro s t; rw [hκ, hκ]; split_ifs <;> omega
  have hκ3 : ∀ s t, κ s t < 3 := by
    intro s t; rw [hκ]; split_ifs <;> omega
  have hty6 : ∀ v : Fin N, ty v.val ≤ 6 := by
    intro v; have := v.isLt; rw [hty]; split_ifs <;> omega
  let c : Fin 3 → SimpleGraph (Fin N) := fun i =>
    SimpleGraph.fromRel (fun u v : Fin N => κ (ty u.val) (ty v.val) = i.val)
  have hcadj : ∀ i u v, (c i).Adj u v ↔ u ≠ v ∧ κ (ty u.val) (ty v.val) = i.val := by
    intro i u v
    simp only [c, fromRel_adj]
    rw [hκs (ty v.val)]
    simp
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · ext u v
    simp only [top_adj, iSup_adj, hcadj]
    constructor
    · intro h; exact ⟨⟨_, hκ3 _ _⟩, h, rfl⟩
    · rintro ⟨_, h, _⟩; exact h
  · intro i j hij
    rw [SimpleGraph.disjoint_left]
    intro u v h1 h2
    rw [hcadj] at h1 h2
    exact hij (Fin.ext (h1.2.symm.trans h2.2))
  · have hP : ∀ k : ℕ, 4 ≤ k → k ≤ 6 → ∀ u v : Fin N, ty u.val = k → ty v.val = k → u = v := by
      intro k _ _ u v hu hv
      apply Fin.ext
      rw [hty] at hu hv
      split_ifs at hu hv <;> omega
    have hcl : ∀ (f : ℕ → ℕ) (A0 B0 A1 B1 : ℕ) (k : ℕ), 4 ≤ k → k ≤ 6 →
        (∀ s, s < 4 → f s ≤ 1) → (∀ s, 4 ≤ s → f s = s + 10) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 0 →
          (A0 ≤ v.val ∧ v.val < A0 + m) ∨ (B0 ≤ v.val ∧ v.val < B0 + m)) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 1 →
          (A1 ≤ v.val ∧ v.val < A1 + m) ∨ (B1 ≤ v.val ∧ v.val < B1 + m)) →
        ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ ty v.val = k → f (ty v.val) = j →
          (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m) := by
      intro f A0 B0 A1 B1 k _ _ hf1 hf2 h0 h1 j
      by_cases hj0 : j = 0
      · refine ⟨A0, B0, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h0 v hlt (hv.trans hj0)
      by_cases hj1 : j = 1
      · refine ⟨A1, B1, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h1 v hlt (hv.trans hj1)
      refine ⟨4 * m + j - 14, 4 * m + j - 14, fun v _ hv => ?_⟩
      have hge : 4 ≤ ty v.val := by
        by_contra hc; have := hf1 (ty v.val) (by omega); omega
      rw [hf2 _ hge] at hv
      left
      have hv' := hv
      rw [hty] at hv'
      have := v.isLt
      split_ifs at hv' <;> omega
    have hint : ∀ v : Fin N, (ty v.val = 0 → v.val < m) ∧ (ty v.val = 1 → m ≤ v.val ∧ v.val < 2 * m) ∧
        (ty v.val = 2 → 2 * m ≤ v.val ∧ v.val < 3 * m) ∧ (ty v.val = 3 → 3 * m ≤ v.val ∧ v.val < 4 * m) := by
      intro v; refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have e := hty v.val <;> split_ifs at e <;> omega
    intro i
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · -- red, hub r
      refine rc4_no_cycle N m (c 0) (fun v => ty v.val = 4) (fun u v hu hv => hP 4 le_rfl
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_red
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) 0 m (2 * m) (3 * m)
          4 le_rfl (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- green, hub g
      refine rc4_no_cycle N m (c 1) (fun v => ty v.val = 5) (fun u v hu hv => hP 5 (by norm_num)
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_green
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) 0 (3 * m) m
          (2 * m) 5 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- blue, hub b
      refine rc4_no_cycle N m (c 2) (fun v => ty v.val = 6) (fun u v hu hv => hP 6 (by norm_num)
        le_rfl u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_blue
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) 0 (2 * m) m
          (3 * m) 6 (by norm_num) le_rfl ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega


/-- If every pair of triples agrees in a coordinate, either two fibres of
different coordinate maps cover the domain, or the triples form the four
corners of the binary parity rectangle. All four corners have representatives.

The cover alternatives may both use the first coordinate. This is stronger
than allowing any pair of different coordinate maps in the cover branch. -/
theorem cover_or_rectangle
    {V A B C : Type*} [Nonempty V]
    (r : V → A) (b : V → B) (g : V → C)
    (agree : ∀ x y, r x = r y ∨ b x = b y ∨ g x = g y) :
    (∃ p q, ∀ x, r x = r p ∨ b x = b q) ∨
    (∃ p q, ∀ x, r x = r p ∨ g x = g q) ∨
    ∃ p q u v : V,
      r p ≠ r q ∧ b p ≠ b q ∧ g p ≠ g u ∧
      g q = g p ∧ r u = r q ∧ b u = b p ∧
      r v = r p ∧ b v = b q ∧ g v = g u ∧
      ∀ x, (r x = r p ∧ b x = b p ∧ g x = g p) ∨
        (r x = r q ∧ b x = b q ∧ g x = g p) ∨
        (r x = r q ∧ b x = b p ∧ g x = g u) ∨
        (r x = r p ∧ b x = b q ∧ g x = g u) := by
  classical
  by_cases hRB : ∃ p q, ∀ x, r x = r p ∨ b x = b q
  · exact Or.inl hRB
  by_cases hRG : ∃ p q, ∀ x, r x = r p ∨ g x = g q
  · exact Or.inr (Or.inl hRG)
  have outsideRB (p q : V) : ∃ x, r x ≠ r p ∧ b x ≠ b q := by
    apply Classical.byContradiction
    intro h
    apply hRB
    refine ⟨p, q, fun x => ?_⟩
    by_cases hr : r x = r p
    · exact Or.inl hr
    · apply Or.inr
      apply Classical.byContradiction
      intro hb
      exact h ⟨x, hr, hb⟩
  have outsideRG (p q : V) : ∃ x, r x ≠ r p ∧ g x ≠ g q := by
    apply Classical.byContradiction
    intro h
    apply hRG
    refine ⟨p, q, fun x => ?_⟩
    by_cases hr : r x = r p
    · exact Or.inl hr
    · apply Or.inr
      apply Classical.byContradiction
      intro hg
      exact h ⟨x, hr, hg⟩
  obtain ⟨p⟩ := ‹Nonempty V›
  obtain ⟨q, hqr, hqb⟩ := outsideRB p p
  have hqg : g q = g p := by
    rcases agree q p with h | h | h
    · exact (hqr h).elim
    · exact (hqb h).elim
    · exact h
  obtain ⟨u, hur, hug⟩ := outsideRG p p
  have hub : b u = b p := by
    rcases agree u p with h | h | h
    · exact (hur h).elim
    · exact h
    · exact (hug h).elim
  have huq : r u = r q := by
    rcases agree u q with h | h | h
    · exact h
    · exact (hqb (h.symm.trans hub)).elim
    · exact (hug (h.trans hqg)).elim
  obtain ⟨v, hvr, hvg⟩ := outsideRG q p
  have hvb : b v = b q := by
    rcases agree v q with h | h | h
    · exact (hvr h).elim
    · exact h
    · exact (hvg (h.trans hqg)).elim
  have hvp : r v = r p := by
    rcases agree v p with h | h | h
    · exact h
    · exact (hqb (hvb.symm.trans h)).elim
    · exact (hvg h).elim
  have hvu : g v = g u := by
    rcases agree v u with h | h | h
    · exact (hvr (h.trans huq)).elim
    · exact (hqb (hvb.symm.trans (h.trans hub))).elim
    · exact h
  refine Or.inr (Or.inr ⟨p, q, u, v, Ne.symm hqr, Ne.symm hqb, Ne.symm hug,
    hqg, huq, hub, hvp, hvb, hvu, ?_⟩)
  intro x
  have hp := agree x p
  have hq := agree x q
  have hu := agree x u
  have hv := agree x v
  clear agree outsideRB outsideRG hRB hRG
  rcases hp with hp | hp | hp <;>
    rcases hq with hq | hq | hq <;>
    rcases hu with hu | hu | hu <;>
    rcases hv with hv | hv | hv <;>
    simp_all

/-- The component labels of three graphs covering the edges of a complete
graph satisfy the pair-agreement hypothesis of `cover_or_rectangle`.
Pairwise disjointness of the edge sets is not needed for this implication. -/
theorem component_labels_agree
    {V : Type*} (R B G : SimpleGraph V)
    (complete : ∀ x y, x ≠ y → R.Adj x y ∨ B.Adj x y ∨ G.Adj x y) :
    ∀ x y, R.connectedComponentMk x = R.connectedComponentMk y ∨
      B.connectedComponentMk x = B.connectedComponentMk y ∨
      G.connectedComponentMk x = G.connectedComponentMk y := by
  intro x y
  by_cases h : x = y
  · subst y
    exact Or.inl rfl
  rcases complete x y h with h | h | h
  · exact Or.inl (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h)
  · exact Or.inr (Or.inl
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h))
  · exact Or.inr (Or.inr
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h))

/-- The complete-edge covering hypothesis follows from the exact colouring
definition used in the Erdős 556 target. -/
theorem edges_covered_of_colouring
    {V : Type*} (c : Fin 3 → SimpleGraph V)
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) :
    ∀ x y, x ≠ y → (c 0).Adj x y ∨ (c 1).Adj x y ∨ (c 2).Adj x y := by
  intro x y hxy
  have hadj : (⊤ : SimpleGraph V).Adj x y := hxy
  rw [hc.1, SimpleGraph.iSup_adj] at hadj
  obtain ⟨i, hi⟩ := hadj
  have cases3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases3 with rfl | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

/-- Direct applicability of `cover_or_rectangle` to the component maps in
any three-edge-colouring of a complete graph. -/
theorem labels_agree_of_colouring
    {V : Type*} (c : Fin 3 → SimpleGraph V)
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) :
    ∀ x y, (c 0).connectedComponentMk x = (c 0).connectedComponentMk y ∨
      (c 1).connectedComponentMk x = (c 1).connectedComponentMk y ∨
      (c 2).connectedComponentMk x = (c 2).connectedComponentMk y :=
  component_labels_agree (c 0) (c 1) (c 2) (edges_covered_of_colouring c hc)

/-- Different labels in two colours force the edge to have the remaining
colour. Applied to the four corners in `cover_or_rectangle`, this gives
exactly the three perfect matchings of the four classes. -/
theorem forced_colour
    {V : Type*} (R B G : SimpleGraph V)
    (complete : ∀ x y, x ≠ y → R.Adj x y ∨ B.Adj x y ∨ G.Adj x y)
    {x y : V}
    (hb : B.connectedComponentMk x ≠ B.connectedComponentMk y)
    (hg : G.connectedComponentMk x ≠ G.connectedComponentMk y) : R.Adj x y := by
  have hxy : x ≠ y := fun h => hb (congrArg B.connectedComponentMk h)
  rcases complete x y hxy with h | h | h
  · exact h
  · exact (hb (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h)).elim
  · exact (hg (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h)).elim

/-- In the two-component-cover branch, the complements of the two covering
components have a complete join in the third colour. This is the exact
complete-bipartite graph available from the component argument. -/
theorem complement_join_third_colour
    {V : Type*} (R B G : SimpleGraph V)
    (complete : ∀ x y, x ≠ y → R.Adj x y ∨ B.Adj x y ∨ G.Adj x y)
    (p q : V)
    (cover : ∀ z, R.connectedComponentMk z = R.connectedComponentMk p ∨
      B.connectedComponentMk z = B.connectedComponentMk q)
    {x y : V}
    (hx : R.connectedComponentMk x ≠ R.connectedComponentMk p)
    (hy : B.connectedComponentMk y ≠ B.connectedComponentMk q) : G.Adj x y := by
  have hxb : B.connectedComponentMk x = B.connectedComponentMk q :=
    (cover x).resolve_left hx
  have hyr : R.connectedComponentMk y = R.connectedComponentMk p :=
    (cover y).resolve_right hy
  have hxy : x ≠ y := fun h => hx ((congrArg R.connectedComponentMk h).trans hyr)
  rcases complete x y hxy with h | h | h
  · exact (hx ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h).trans hyr)).elim
  · exact (hy ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h).symm.trans hxb)).elim
  · exact h

open SimpleGraph

/-- A complete join between two disjoint sets, each of size at least `m`,
contains the even cycle of length `2*m`. The embedding explicitly alternates
between chosen `m`-element subsets. Its parity argument is the elementary
part of the alternating-representatives construction used in the existing
Benevides--Skokan R2 reduction; this lemma does not import that reduction. -/
theorem cycle_of_complete_join
    {V : Type*} (G : SimpleGraph V) {m : ℕ} (_hm : 2 ≤ m)
    (A B : Finset V) (hAB : Disjoint A B) (hA : m ≤ A.card) (hB : m ≤ B.card)
    (join : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : cycleGraph (2*m) ⊑ G := by
  classical
  obtain ⟨A', hA', hAc⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨B', hB', hBc⟩ := Finset.exists_subset_card_eq hB
  let eA : A' ≃ Fin m := Finset.equivFinOfCardEq hAc
  let eB : B' ≃ Fin m := Finset.equivFinOfCardEq hBc
  let x (i : Fin m) : V := (eA.symm i).val
  let y (i : Fin m) : V := (eB.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp eA.symm.injective
  have hy : Function.Injective y := Subtype.val_injective.comp eB.symm.injective
  have hxA (i : Fin m) : x i ∈ A := hA' (eA.symm i).property
  have hyB (i : Fin m) : y i ∈ B := hB' (eB.symm i).property
  have hxy (i j : Fin m) : x i ≠ y j := by
    intro h
    exact Finset.disjoint_left.mp hAB (hxA i) (h ▸ hyB j)
  let half (a : Fin (2*m)) : Fin m := ⟨a.val/2, by have := a.isLt; omega⟩
  let f (a : Fin (2*m)) := if a.val%2=0 then x (half a) else y (half a)
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val%2=0 <;> by_cases hb : b.val%2=0
    · have he := congrArg Fin.val (hx (by simpa [f,ha,hb] using hab : x (half a)=x (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
    · exact (hxy _ _ (by simpa [f,ha,hb] using hab)).elim
    · exact (hxy _ _ (by simpa [f,ha,hb] using hab.symm)).elim
    · have he := congrArg Fin.val (hy (by simpa [f,ha,hb] using hab : y (half a)=y (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
  have parity (a b : Fin (2*m)) (hz : (b-a).val=1) : a.val%2 ≠ b.val%2 := by
    have ha := a.isLt
    have hb := b.isLt
    rw [Fin.val_sub] at hz
    have consecutive : b.val=a.val+1 ∨ (a.val+1=2*m ∧ b.val=0) := by
      by_cases hle : a.val ≤ b.val
      · rw [show 2*m-a.val+b.val=2*m+(b.val-a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inr (by omega)
    rcases consecutive with h | ⟨h₁,h₂⟩ <;> omega
  let hom : cycleGraph (2*m) →g G := ⟨f, by
    intro a b hab
    have hp : a.val%2 ≠ b.val%2 := by
      rcases cycleGraph_adj'.mp hab with h | h
      · exact Ne.symm (parity b a h)
      · exact parity a b h
    by_cases ha : a.val%2=0
    · have hb : b.val%2≠0 := by omega
      simpa only [f,ha,hb,if_true,if_false] using join _ (hxA (half a)) _ (hyB (half b))
    · have hb : b.val%2=0 := by omega
      simpa only [f,ha,hb,if_true,if_false] using (join _ (hxA (half b)) _ (hyB (half a))).symm⟩
  exact ⟨⟨hom,hinj⟩⟩

/-- If a red and a blue component cover `4*m` vertices and there is no green
`2*m`-cycle, one of those two covering components has more than `3*m` vertices.
This is a size restriction, not a long-cycle theorem for large components. -/
theorem covering_components_large_of_no_third_cycle
    (m : ℕ) (hm : 2 ≤ m) (R B G : SimpleGraph (Fin (4*m)))
    (complete : ∀ x y, x ≠ y → R.Adj x y ∨ B.Adj x y ∨ G.Adj x y)
    (p q : Fin (4*m))
    (cover : ∀ z, R.connectedComponentMk z=R.connectedComponentMk p ∨
      B.connectedComponentMk z=B.connectedComponentMk q)
    (hno : ¬ cycleGraph (2*m) ⊑ G) :
    3*m < Nat.card {z : Fin (4*m) // R.connectedComponentMk z=R.connectedComponentMk p} ∨
    3*m < Nat.card {z : Fin (4*m) // B.connectedComponentMk z=B.connectedComponentMk q} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let X := Finset.univ.filter (fun z => R.connectedComponentMk z≠R.connectedComponentMk p)
  let Y := Finset.univ.filter (fun z => B.connectedComponentMk z≠B.connectedComponentMk q)
  have hdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hx hy
    exact (cover z).elim (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hjoin : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y := by
    intro x hx y hy
    exact complement_join_third_colour R B G complete p q cover
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hcardR :
      (Finset.univ.filter (fun z => R.connectedComponentMk z=R.connectedComponentMk p)).card+
        X.card=4*m := by
    simpa [X] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (4*m))))
      (fun z => R.connectedComponentMk z=R.connectedComponentMk p)
  have hcardB :
      (Finset.univ.filter (fun z => B.connectedComponentMk z=B.connectedComponentMk q)).card+
        Y.card=4*m := by
    simpa [Y] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (4*m))))
      (fun z => B.connectedComponentMk z=B.connectedComponentMk q)
  by_cases hx : m ≤ X.card
  · by_cases hy : m ≤ Y.card
    · exact (hno (cycle_of_complete_join G hm X Y hdisj hx hy hjoin)).elim
    · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- The finite size consequence for any two different colours in the exact
three-edge-colouring API used in the target. No monochromatic `C_(2m)` plus
a cover by two differently coloured components forces a covering component
of order strictly greater than `3*m`. -/
theorem covering_components_large_of_no_monochromatic_cycle
    (m : ℕ) (hm : 2 ≤ m) (c : Fin 3 → SimpleGraph (Fin (4*m)))
    (hc : (⊤ : SimpleGraph (Fin (4*m))).IsEdgeColouring c)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin (4*m))
    (cover : ∀ z, (c i).connectedComponentMk z=(c i).connectedComponentMk p ∨
      (c j).connectedComponentMk z=(c j).connectedComponentMk q)
    (hno : ∀ k, ¬ cycleGraph (2*m) ⊑ c k) :
    3*m < Nat.card {z : Fin (4*m) // (c i).connectedComponentMk z=(c i).connectedComponentMk p} ∨
    3*m < Nat.card {z : Fin (4*m) // (c j).connectedComponentMk z=(c j).connectedComponentMk q} := by
  classical
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  let k : Fin 3 := ⟨3-i.val-j.val, by omega⟩
  have colours (l : Fin 3) : l=i ∨ l=j ∨ l=k := by
    have hk : k.val=3-i.val-j.val := rfl
    omega
  apply covering_components_large_of_no_third_cycle m hm (c i) (c j) (c k) ?_ p q cover (hno k)
  intro x y hxy
  have hadj : (⊤ : SimpleGraph (Fin (4*m))).Adj x y := hxy
  rw [hc.1, SimpleGraph.iSup_adj] at hadj
  obtain ⟨l,hl⟩ := hadj
  rcases colours l with rfl | rfl | rfl
  · exact Or.inl hl
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hl)


theorem eq_from_upper (m : ℕ) (hm : 2 ≤ m) (up : ∀ c : Fin 3 → SimpleGraph (Fin (4*m)),
    (⊤ : SimpleGraph (Fin (4*m))).IsEdgeColouring c → ∃ i, cycleGraph (2*m) ⊑ c i) :
    multicolourRamsey (cycleGraph (2*m)) 3 = 4*m := by
  unfold multicolourRamsey
  apply le_antisymm
  · exact Nat.sInf_le up
  refine le_csInf ⟨4*m,up⟩ ?_
  intro N hN
  by_contra h
  obtain ⟨c,hc,hno⟩ := rc4_lower (m-1) (by omega) N (by omega)
    (fun v => if v < m-1 then 0 else if v < 2*(m-1) then 1 else
      if v < 3*(m-1) then 2 else if v < 4*(m-1) then 3 else v-4*(m-1)+4)
    (fun _ => rfl)
    (fun s t => if s=6 ∨ t=6 then 2 else if s=5 ∨ t=5 then 1 else
      if s=4 ∨ t=4 then 0 else if s/2=t/2 then 0 else if s+t=3 then 1 else 2)
    (fun _ _ => rfl)
  obtain ⟨i,hi⟩ := hN c hc
  have hlen : 2*m = 2*(m-1)+2 := by omega
  rw [hlen] at hi
  exact hno i hi

/-- If neither a colour-0/colour-1 nor a colour-0/colour-2 pair of components
covers the vertices, the exact component labels give a surjective partition
into four classes with the K4 perfect-matching cross-colour pattern. -/
theorem factorization_of_no_cover
    {V : Type*} [Nonempty V] (c : Fin 3 → SimpleGraph V)
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    (no01 : ¬ ∃ p q, ∀ z,
      (c 0).connectedComponentMk z=(c 0).connectedComponentMk p ∨
      (c 1).connectedComponentMk z=(c 1).connectedComponentMk q)
    (no02 : ¬ ∃ p q, ∀ z,
      (c 0).connectedComponentMk z=(c 0).connectedComponentMk p ∨
      (c 2).connectedComponentMk z=(c 2).connectedComponentMk q) :
    ∃ f : V → Fin 4, Function.Surjective f ∧
      ∀ i a b, (i,a,b) ∈
        ([(0,0,3),(0,1,2),(1,0,2),(1,1,3),(2,0,1),(2,2,3)] :
          List (Fin 3 × Fin 4 × Fin 4)) →
        ∀ x y, f x=a → f y=b → (c i).Adj x y := by
  classical
  rcases cover_or_rectangle (c 0).connectedComponentMk (c 1).connectedComponentMk
      (c 2).connectedComponentMk (labels_agree_of_colouring c hc) with h | h | h
  · exact (no01 h).elim
  · exact (no02 h).elim
  obtain ⟨p,q,u,v,hr,hb,hg,hqg,huq,hub,hvp,hvb,hvu,hclasses⟩ := h
  let f : V → Fin 4 := fun x =>
    if (c 0).connectedComponentMk x=(c 0).connectedComponentMk p then
      if (c 1).connectedComponentMk x=(c 1).connectedComponentMk p then 0 else 3
    else if (c 1).connectedComponentMk x=(c 1).connectedComponentMk p then 2 else 1
  have fp : f p=0 := by simp [-SimpleGraph.ConnectedComponent.eq,f]
  have fq : f q=1 := by simp [-SimpleGraph.ConnectedComponent.eq,f, Ne.symm hr, Ne.symm hb]
  have fu : f u=2 := by simp [-SimpleGraph.ConnectedComponent.eq,f,huq,hub,Ne.symm hr]
  have fv : f v=3 := by simp [-SimpleGraph.ConnectedComponent.eq,f,hvp,hvb,Ne.symm hb]
  have labels (x : V) :
      (f x=0 → (c 0).connectedComponentMk x=(c 0).connectedComponentMk p ∧
        (c 1).connectedComponentMk x=(c 1).connectedComponentMk p ∧
        (c 2).connectedComponentMk x=(c 2).connectedComponentMk p) ∧
      (f x=1 → (c 0).connectedComponentMk x=(c 0).connectedComponentMk q ∧
        (c 1).connectedComponentMk x=(c 1).connectedComponentMk q ∧
        (c 2).connectedComponentMk x=(c 2).connectedComponentMk p) ∧
      (f x=2 → (c 0).connectedComponentMk x=(c 0).connectedComponentMk q ∧
        (c 1).connectedComponentMk x=(c 1).connectedComponentMk p ∧
        (c 2).connectedComponentMk x=(c 2).connectedComponentMk u) ∧
      (f x=3 → (c 0).connectedComponentMk x=(c 0).connectedComponentMk p ∧
        (c 1).connectedComponentMk x=(c 1).connectedComponentMk q ∧
        (c 2).connectedComponentMk x=(c 2).connectedComponentMk u) := by
    rcases hclasses x with ⟨hx,hb',hg'⟩ | ⟨hx,hb',hg'⟩ | ⟨hx,hb',hg'⟩ | ⟨hx,hb',hg'⟩ <;>
      simp [-SimpleGraph.ConnectedComponent.eq,f,hx,hb',hg',hr,hb,hg,Ne.symm hr,Ne.symm hb,Ne.symm hg]
  have complete := edges_covered_of_colouring c hc
  have complete102 : ∀ x y, x ≠ y → (c 1).Adj x y ∨ (c 0).Adj x y ∨ (c 2).Adj x y := by
    intro x y hxy
    rcases complete x y hxy with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have complete201 : ∀ x y, x ≠ y → (c 2).Adj x y ∨ (c 0).Adj x y ∨ (c 1).Adj x y := by
    intro x y hxy
    rcases complete x y hxy with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  refine ⟨f,?_,?_⟩
  · intro j
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨p,fp⟩
    · exact ⟨q,fq⟩
    · exact ⟨u,fu⟩
    · exact ⟨v,fv⟩
  · intro i a b htable x y hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at htable
    rcases htable with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · have hxl := (labels x).1 hx
      have hyl := (labels y).2.2.2 hy
      apply forced_colour (c 0) (c 1) (c 2) complete
      · rw [hxl.2.1,hyl.2.1]; exact hb
      · rw [hxl.2.2,hyl.2.2]; exact hg
    · have hxl := (labels x).2.1 hx
      have hyl := (labels y).2.2.1 hy
      apply forced_colour (c 0) (c 1) (c 2) complete
      · rw [hxl.2.1,hyl.2.1]; exact Ne.symm hb
      · rw [hxl.2.2,hyl.2.2]; exact hg
    · have hxl := (labels x).1 hx
      have hyl := (labels y).2.2.1 hy
      apply forced_colour (c 1) (c 0) (c 2) complete102
      · rw [hxl.1,hyl.1]; exact hr
      · rw [hxl.2.2,hyl.2.2]; exact hg
    · have hxl := (labels x).2.1 hx
      have hyl := (labels y).2.2.2 hy
      apply forced_colour (c 1) (c 0) (c 2) complete102
      · rw [hxl.1,hyl.1]; exact Ne.symm hr
      · rw [hxl.2.2,hyl.2.2]; exact hg
    · have hxl := (labels x).1 hx
      have hyl := (labels y).2.1 hy
      apply forced_colour (c 2) (c 0) (c 1) complete201
      · rw [hxl.1,hyl.1]; exact hr
      · rw [hxl.2.1,hyl.2.1]; exact hb
    · have hxl := (labels x).2.2.1 hx
      have hyl := (labels y).2.2.2 hy
      apply forced_colour (c 2) (c 0) (c 1) complete201
      · rw [hxl.1,hyl.1]; exact Ne.symm hr
      · rw [hxl.2.1,hyl.2.1]; exact hb

/-- The large-component case. No extremal partition is assumed. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  ∀ c : Fin 3 → SimpleGraph (Fin (4*m)),
    (⊤ : SimpleGraph (Fin (4*m))).IsEdgeColouring c →
    (∃ (i : Fin 3) (p : Fin (4*m)),
      3*m < Nat.card {z : Fin (4*m) //
        (c i).connectedComponentMk z=(c i).connectedComponentMk p}) →
    ∃ i, cycleGraph (2*m) ⊑ c i

/-- The exact four-class case, with arbitrary edges within each class.
Surjectivity requires all four classes to be nonempty. The component bound
excludes the branch treated by H1, without referring to that hypothesis. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  ∀ c : Fin 3 → SimpleGraph (Fin (4*m)),
    (⊤ : SimpleGraph (Fin (4*m))).IsEdgeColouring c →
    (∀ (i : Fin 3) (p : Fin (4*m)),
      Nat.card {z : Fin (4*m) //
        (c i).connectedComponentMk z=(c i).connectedComponentMk p} ≤ 3*m) →
    ∀ f : Fin (4*m) → Fin 4, Function.Surjective f →
      (∀ i a b, (i,a,b) ∈
        ([(0,0,3),(0,1,2),(1,0,2),(1,1,3),(2,0,1),(2,2,3)] :
          List (Fin 3 × Fin 4 × Fin 4)) →
        ∀ x y, f x=a → f y=b → (c i).Adj x y) →
      ∃ i, cycleGraph (2*m) ⊑ c i

theorem main : H1 → H2 →
    type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  classical
  intro h1 h2
  have evenBound : ∀ᶠ m : ℕ in atTop,
      multicolourRamsey (cycleGraph (2*m)) 3=4*m := by
    filter_upwards [h1,h2,eventually_ge_atTop 2] with m hlarge hfour hm
    apply eq_from_upper m hm
    intro c hc
    by_cases hbig : ∃ (i : Fin 3) (p : Fin (4*m)),
        3*m < Nat.card {z : Fin (4*m) //
          (c i).connectedComponentMk z=(c i).connectedComponentMk p}
    · exact hlarge c hc hbig
    have hsmall : ∀ (i : Fin 3) (p : Fin (4*m)),
        Nat.card {z : Fin (4*m) //
          (c i).connectedComponentMk z=(c i).connectedComponentMk p} ≤ 3*m := by
      intro i p
      exact le_of_not_gt (fun h => hbig ⟨i,p,h⟩)
    by_contra hnone
    have hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i := fun i hi => hnone ⟨i,hi⟩
    letI : Nonempty (Fin (4*m)) := ⟨⟨0,by omega⟩⟩
    have no01 : ¬ ∃ p q, ∀ z,
        (c 0).connectedComponentMk z=(c 0).connectedComponentMk p ∨
        (c 1).connectedComponentMk z=(c 1).connectedComponentMk q := by
      rintro ⟨p,q,hcover⟩
      rcases covering_components_large_of_no_monochromatic_cycle m hm c hc
          0 1 (by decide) p q hcover hno with h | h
      · exact (not_lt_of_ge (hsmall 0 p)) h
      · exact (not_lt_of_ge (hsmall 1 q)) h
    have no02 : ¬ ∃ p q, ∀ z,
        (c 0).connectedComponentMk z=(c 0).connectedComponentMk p ∨
        (c 2).connectedComponentMk z=(c 2).connectedComponentMk q := by
      rintro ⟨p,q,hcover⟩
      rcases covering_components_large_of_no_monochromatic_cycle m hm c hc
          0 2 (by decide) p q hcover hno with h | h
      · exact (not_lt_of_ge (hsmall 0 p)) h
      · exact (not_lt_of_ge (hsmall 2 q)) h
    obtain ⟨f,hsurj,hcross⟩ := factorization_of_no_cover c hc no01 no02
    exact hnone (hfour c hc hsmall f hsurj hcross)
  obtain ⟨M,hM⟩ := eventually_atTop.mp evenBound
  filter_upwards [eventually_ge_atTop (2*M)] with n hn he
  obtain ⟨m,rfl⟩ := he
  have hlen : m+m=2*m := by omega
  rw [hlen,show 2*(2*m)=4*m by omega]
  exact hM m (by omega)

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3

