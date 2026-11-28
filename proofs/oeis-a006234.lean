import OMAStatements.S_oeis_a006234
import Mathlib

-- Proof of the statement for OEIS A006234 (statement by @Dugongue): the book graph on 2(n-2) vertices has
-- n * 3^(n-4) spanning trees (a theorem of Doslic, 2013). Self-contained; no site proof was adapted.
-- Idea. Write n = q + 4. The graph bookGraph (q + 2) has the spine edge (0,F)-(0,T) and q + 1 pages; page i
-- has the three private edges (0,F)-(i+1,F), (i+1,F)-(i+1,T), (0,T)-(i+1,T). A spanning subgraph is a choice
-- of edges (a function c on the 3(q+1)+1 abstract edges). By Mathlib's isTree_iff_connected_and_card it is a
-- tree iff it is connected and has 2q+3 edges. Connected forces at least two private edges on every page
-- (otherwise a private vertex, or the pair of private vertices of the page, is cut off); with 2q+3 edges this
-- leaves: spine and no full page, or no spine and exactly one full page, and both kinds are connected.
-- Count: 3^(q+1) + (q+1) * 3^q = (q+4) * 3^q.

namespace OMAA006234Helpers

open OMA.S_oeis_a006234

/-- Vertices of `bookGraph (q + 2)`. -/
abbrev V (q : ℕ) := Fin (q + 2) × Bool

/-- Abstract edges: `none` is the spine, `some (i, j)` is the `j`-th private edge of page `i`. -/
abbrev E (q : ℕ) := Option (Fin (q + 1) × Fin 3)

/-- The two end points of an abstract edge. -/
def ends {q : ℕ} : E q → V q × V q
  | none => ((0, false), (0, true))
  | some (i, j) =>
    if j = 0 then ((0, false), (i.succ, false))
    else if j = 1 then ((i.succ, false), (i.succ, true))
    else ((0, true), (i.succ, true))

theorem ends_ne {q : ℕ} (x : E q) : (ends x).1 ≠ (ends x).2 := by
  rcases x with _ | ⟨i, j⟩
  · simp [ends]
  · fin_cases j <;> simp [ends, (Fin.succ_ne_zero _).symm]

theorem ends_inj {q : ℕ} (x y : E q)
    (h : ((ends y).1 = (ends x).1 ∧ (ends y).2 = (ends x).2) ∨
      ((ends y).1 = (ends x).2 ∧ (ends y).2 = (ends x).1)) : y = x := by
  rcases x with _ | ⟨i, j⟩ <;> rcases y with _ | ⟨i', j'⟩
  · rfl
  · fin_cases j' <;> simp [ends, Fin.succ_ne_zero] at h
  · fin_cases j <;> simp [ends, (Fin.succ_ne_zero _).symm] at h
  · fin_cases j <;> fin_cases j' <;>
      simp [ends, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm] at h ⊢ <;> exact h

/-- The spanning subgraph with edge indicator `c`. -/
def G {q : ℕ} (c : E q → Bool) : SimpleGraph (V q) :=
  SimpleGraph.fromEdgeSet ((fun x => s((ends x).1, (ends x).2)) '' {x | c x = true})

theorem G_adj {q : ℕ} (c : E q → Bool) (u v : V q) :
    (G c).Adj u v ↔ ∃ x, c x = true ∧
      (((ends x).1 = u ∧ (ends x).2 = v) ∨ ((ends x).1 = v ∧ (ends x).2 = u)) := by
  simp only [G, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Set.mem_ofPred_eq, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨x, hx, h⟩, -⟩
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨x, hx, h⟩, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ends_ne x
    · exact (ends_ne x).symm

theorem G_adj_ends {q : ℕ} (c : E q → Bool) (x : E q) :
    (G c).Adj (ends x).1 (ends x).2 ↔ c x = true := by
  rw [G_adj]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← ends_inj x y h]
    exact hy
  · intro hx
    exact ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩

theorem book_adj {q : ℕ} (i j : Fin (q + 2)) (b b' : Bool) :
    (bookGraph (q + 2)).Adj (i, b) (j, b') ↔
      (b = b' ∧ ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))) ∨ (i = j ∧ b ≠ b') := by
  simp only [bookGraph, starGraph, SimpleGraph.fromRel_adj, ne_eq, Prod.mk.injEq, not_and,
    Fin.val_eq_zero_iff]
  constructor
  · rintro ⟨hne, (⟨hb, -, h⟩ | ⟨hij, hb⟩) | (⟨hb, -, h⟩ | ⟨hij, hb⟩)⟩
    · rcases h with h | h
      · exact Or.inl ⟨hb, Or.inl h⟩
      · exact Or.inl ⟨hb, Or.inr h⟩
    · exact Or.inr ⟨hij, hb⟩
    · rcases h with h | h
      · exact Or.inl ⟨hb.symm, Or.inr h⟩
      · exact Or.inl ⟨hb.symm, Or.inl h⟩
    · exact Or.inr ⟨hij.symm, fun h => hb h.symm⟩
  · rintro (⟨hb, h | h⟩ | ⟨hij, hb⟩)
    · refine ⟨fun hij _ => h.2 (hij ▸ h.1), Or.inl (Or.inl ⟨hb, fun hij => h.2 (hij ▸ h.1), Or.inl h⟩)⟩
    · refine ⟨fun hij _ => h.2 (hij ▸ h.1), Or.inl (Or.inl ⟨hb, fun hij => h.2 (hij.symm ▸ h.1), Or.inr h⟩)⟩
    · exact ⟨fun _ => hb, Or.inl (Or.inr ⟨hij, hb⟩)⟩

theorem book_ends {q : ℕ} (x : E q) : (bookGraph (q + 2)).Adj (ends x).1 (ends x).2 := by
  rcases x with _ | ⟨i, j⟩
  · simp [ends, book_adj]
  · fin_cases j <;> simp [ends, book_adj, Fin.succ_ne_zero]

theorem book_cover {q : ℕ} (u v : V q) (h : (bookGraph (q + 2)).Adj u v) :
    ∃ x : E q, ((ends x).1 = u ∧ (ends x).2 = v) ∨ ((ends x).1 = v ∧ (ends x).2 = u) := by
  obtain ⟨i, b⟩ := u
  obtain ⟨j, b'⟩ := v
  rw [book_adj] at h
  rcases h with ⟨rfl, ⟨rfl, hj⟩ | ⟨rfl, hi⟩⟩ | ⟨rfl, hb⟩
  · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    cases b
    · exact ⟨some (j', 0), Or.inl (by simp [ends])⟩
    · exact ⟨some (j', 2), Or.inl (by simp [ends])⟩
  · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    cases b
    · exact ⟨some (i', 0), Or.inr (by simp [ends])⟩
    · exact ⟨some (i', 2), Or.inr (by simp [ends])⟩
  · induction i using Fin.cases with
    | zero =>
      cases b <;> cases b' <;> simp at hb
      · exact ⟨none, Or.inl (by simp [ends])⟩
      · exact ⟨none, Or.inr (by simp [ends])⟩
    | succ i' =>
      cases b <;> cases b' <;> simp at hb
      · exact ⟨some (i', 1), Or.inl (by simp [ends])⟩
      · exact ⟨some (i', 1), Or.inr (by simp [ends])⟩

theorem G_le {q : ℕ} (c : E q → Bool) : G c ≤ bookGraph (q + 2) := by
  intro u v h
  obtain ⟨x, -, h⟩ := (G_adj c u v).mp h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact book_ends x
  · exact (book_ends x).symm

/-- Number of chosen edges. -/
def cnt {q : ℕ} (c : E q → Bool) : ℕ := ∑ x, if c x = true then 1 else 0

theorem card_edges {q : ℕ} (c : E q → Bool) : Nat.card (G c).edgeSet = cnt c := by
  have hinj : Function.Injective (fun x : E q => s((ends x).1, (ends x).2)) := by
    intro x y h
    exact ends_inj y x (Sym2.eq_iff.mp h)
  have h1 : (G c).edgeSet = (fun x : E q => s((ends x).1, (ends x).2)) '' {x | c x = true} := by
    rw [G, SimpleGraph.edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
    rintro _ ⟨x, -, rfl⟩ h
    exact ends_ne x (Sym2.mk_isDiag_iff.mp h)
  rw [h1, Nat.card_image_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_subtype, cnt,
    Finset.card_filter]
  simp

/-- Along a reachability, a predicate closed under adjacency is preserved. -/
theorem inv_of_reachable {W : Type} (H : SimpleGraph W) (P : W → Prop)
    (hP : ∀ u v, H.Adj u v → P u → P v) {u v : W} (h : H.Reachable u v) (hu : P u) : P v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

theorem closed_of_ends {q : ℕ} (c : E q → Bool) (P : V q → Prop)
    (h : ∀ x, c x = true → (P (ends x).1 ↔ P (ends x).2)) :
    ∀ u v, (G c).Adj u v → P u → P v := by
  intro u v hadj hu
  obtain ⟨x, hx, hm⟩ := (G_adj c u v).mp hadj
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (h x hx).mp hu
  · exact (h x hx).mpr hu

/-- Page `i` keeps at least two of its three private edges. -/
def pg {q : ℕ} (c : E q → Bool) (i : Fin (q + 1)) : Prop :=
  (c (some (i, 0)) = true ∨ c (some (i, 1)) = true) ∧
  (c (some (i, 1)) = true ∨ c (some (i, 2)) = true) ∧
  (c (some (i, 0)) = true ∨ c (some (i, 2)) = true)

theorem pg_of_connected {q : ℕ} (c : E q → Bool) (hc : (G c).Connected) (i : Fin (q + 1)) :
    pg c i := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon
    rw [not_or] at hcon
    have hcl := closed_of_ends c (fun x => x = (i.succ, false)) (by
      intro x hx
      rcases x with _ | ⟨i', j⟩
      · simp [ends, (Fin.succ_ne_zero _).symm]
      · fin_cases j <;> simp [ends, (Fin.succ_ne_zero _).symm] <;>
          (rintro rfl; simp_all))
    have := inv_of_reachable (G c) _ hcl (hc.preconnected (i.succ, false) (0, false)) rfl
    simp [(Fin.succ_ne_zero _).symm] at this
  · by_contra hcon
    rw [not_or] at hcon
    have hcl := closed_of_ends c (fun x => x = (i.succ, true)) (by
      intro x hx
      rcases x with _ | ⟨i', j⟩
      · simp [ends, (Fin.succ_ne_zero _).symm]
      · fin_cases j <;> simp [ends, (Fin.succ_ne_zero _).symm] <;>
          (rintro rfl; simp_all))
    have := inv_of_reachable (G c) _ hcl (hc.preconnected (i.succ, true) (0, false)) rfl
    simp at this
  · by_contra hcon
    rw [not_or] at hcon
    have hcl := closed_of_ends c (fun x => x.1 = i.succ) (by
      intro x hx
      rcases x with _ | ⟨i', j⟩
      · simp [ends, (Fin.succ_ne_zero _).symm]
      · fin_cases j <;> simp [ends, (Fin.succ_ne_zero _).symm] <;>
          (rintro rfl; simp_all))
    have := inv_of_reachable (G c) _ hcl (hc.preconnected (i.succ, false) (0, false)) rfl
    simp [(Fin.succ_ne_zero _).symm] at this

theorem connected_of {q : ℕ} (c : E q → Bool) (hp : ∀ i, pg c i)
    (hz : c none = true ∨ ∃ i, c (some (i, 0)) = true ∧ c (some (i, 1)) = true ∧
      c (some (i, 2)) = true) : (G c).Connected := by
  have e0 : ∀ i, c (some (i, 0)) = true → (G c).Adj (0, false) (i.succ, false) := by
    intro i h
    have := (G_adj_ends c (some (i, 0))).mpr h
    simpa [ends] using this
  have e1 : ∀ i, c (some (i, 1)) = true → (G c).Adj (i.succ, false) (i.succ, true) := by
    intro i h
    have := (G_adj_ends c (some (i, 1))).mpr h
    simpa [ends] using this
  have e2 : ∀ i, c (some (i, 2)) = true → (G c).Adj (0, true) (i.succ, true) := by
    intro i h
    have := (G_adj_ends c (some (i, 2))).mpr h
    simpa [ends] using this
  have h0 : (G c).Reachable (0, false) (0, true) := by
    rcases hz with h | ⟨i, ha, hr, hb⟩
    · have := (G_adj_ends c none).mpr h
      exact SimpleGraph.Adj.reachable (by simpa [ends] using this)
    · exact ((e0 i ha).reachable.trans (e1 i hr).reachable).trans (e2 i hb).symm.reachable
  have hF : ∀ i : Fin (q + 1), (G c).Reachable (0, false) (i.succ, false) := by
    intro i
    by_cases ha : c (some (i, 0)) = true
    · exact (e0 i ha).reachable
    · obtain ⟨h1, h2, h3⟩ := hp i
      have hr : c (some (i, 1)) = true := h1.resolve_left ha
      have hb : c (some (i, 2)) = true := h3.resolve_left ha
      exact (h0.trans (e2 i hb).reachable).trans (e1 i hr).symm.reachable
  have hT : ∀ i : Fin (q + 1), (G c).Reachable (0, false) (i.succ, true) := by
    intro i
    by_cases hb : c (some (i, 2)) = true
    · exact h0.trans (e2 i hb).reachable
    · obtain ⟨h1, h2, h3⟩ := hp i
      have hr : c (some (i, 1)) = true := h2.resolve_right hb
      have ha : c (some (i, 0)) = true := h3.resolve_right hb
      exact (e0 i ha).reachable.trans (e1 i hr).reachable
  have hall : ∀ v : V q, (G c).Reachable (0, false) v := by
    rintro ⟨j, b⟩
    induction j using Fin.cases with
    | zero =>
      cases b
      · exact SimpleGraph.Reachable.refl _
      · exact h0
    | succ i =>
      cases b
      · exact hF i
      · exact hT i
  exact (SimpleGraph.connected_iff _).mpr ⟨fun u v => (hall u).symm.trans (hall v), ⟨(0, false)⟩⟩

theorem cnt_eq {q : ℕ} (c : E q → Bool) :
    cnt c = (if c none = true then 1 else 0) +
      ∑ i : Fin (q + 1), ((if c (some (i, 0)) = true then 1 else 0) +
        (if c (some (i, 1)) = true then 1 else 0) + (if c (some (i, 2)) = true then 1 else 0)) := by
  simp only [cnt, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- The combinatorial description of spanning trees. -/
def Cond {q : ℕ} (c : E q → Bool) : Prop := (∀ i, pg c i) ∧ cnt c = 2 * q + 3

theorem isTree_iff {q : ℕ} (c : E q → Bool) : (G c).IsTree ↔ Cond c := by
  rw [SimpleGraph.isTree_iff_connected_and_card, card_edges]
  have hV : Nat.card (V q) = 2 * q + 4 := by
    simp [Nat.card_eq_fintype_card]
    ring
  rw [hV]
  constructor
  · rintro ⟨hc, hcard⟩
    exact ⟨pg_of_connected c hc, by omega⟩
  · rintro ⟨hp, hcard⟩
    refine ⟨connected_of c hp ?_, by omega⟩
    by_contra hcon
    rw [not_or, not_exists] at hcon
    obtain ⟨hs, hfull⟩ := hcon
    have hsum : ∑ i : Fin (q + 1), ((if c (some (i, 0)) = true then 1 else 0) +
        (if c (some (i, 1)) = true then 1 else 0) + (if c (some (i, 2)) = true then 1 else 0))
        = ∑ _i : Fin (q + 1), 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have h1 := hp i
      have h2 := hfull i
      unfold pg at h1
      rcases Bool.eq_false_or_eq_true (c (some (i, 0))) with a | a <;>
        rcases Bool.eq_false_or_eq_true (c (some (i, 1))) with b | b <;>
        rcases Bool.eq_false_or_eq_true (c (some (i, 2))) with d | d <;>
        simp_all
    rw [cnt_eq, hsum] at hcard
    simp [hs] at hcard
    omega

/-- The spanning tree of the book graph given by a tree `G c`. -/
def toT {q : ℕ} (c : E q → Bool) (h : (G c).IsTree) :
    {T : (bookGraph (q + 2)).Subgraph // T.IsSpanning ∧ T.coe.IsTree} :=
  ⟨SimpleGraph.toSubgraph (G c) (G_le c), SimpleGraph.toSubgraph.isSpanning _ _,
    (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning _
      (SimpleGraph.toSubgraph.isSpanning _ _)).isTree_iff.mp h⟩

/-- Explicit configurations: the spine bit and the three bits of every page. -/
abbrev Cfg (q : ℕ) := Bool × (Fin (q + 1) → Bool × Bool × Bool)

def on {q : ℕ} (k : Cfg q) : E q → Bool
  | none => k.1
  | some (i, j) => if j = 0 then (k.2 i).1 else if j = 1 then (k.2 i).2.1 else (k.2 i).2.2

theorem on_injective {q : ℕ} : Function.Injective (on (q := q)) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  have h0 : s = s' := by simpa [on] using congrFun h none
  have h1 : t = t' := by
    funext i
    have a := congrFun h (some (i, 0))
    have b := congrFun h (some (i, 1))
    have d := congrFun h (some (i, 2))
    simp [on] at a b d
    exact Prod.ext a (Prod.ext b d)
  rw [h0, h1]

/-- Full pages. -/
def full (x : Bool × Bool × Bool) : ℕ := if x = (true, true, true) then 1 else 0

/-- At least two bits. -/
def two (x : Bool × Bool × Bool) : Prop :=
  (x.1 = true ∨ x.2.1 = true) ∧ (x.2.1 = true ∨ x.2.2 = true) ∧ (x.1 = true ∨ x.2.2 = true)

instance (x : Bool × Bool × Bool) : Decidable (two x) := by unfold two; infer_instance

theorem cond_on {q : ℕ} (k : Cfg q) :
    Cond (on k) ↔ (∀ i, two (k.2 i)) ∧ (if k.1 = true then 1 else 0) + ∑ i, full (k.2 i) = 1 := by
  obtain ⟨s, t⟩ := k
  unfold Cond
  have hpg : ∀ i, pg (on (s, t)) i ↔ two (t i) := by
    intro i
    simp [pg, two, on]
  simp only [hpg]
  refine and_congr_right (fun htwo => ?_)
  rw [cnt_eq]
  have hsum : ∑ i : Fin (q + 1), ((if on (s, t) (some (i, 0)) = true then 1 else 0) +
      (if on (s, t) (some (i, 1)) = true then 1 else 0) +
      (if on (s, t) (some (i, 2)) = true then 1 else 0))
      = ∑ i : Fin (q + 1), (2 + full (t i)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := htwo i
    rcases hti : t i with ⟨a, b, d⟩
    rw [hti] at h
    cases a <;> cases b <;> cases d <;> simp_all [on, two, full]
  have hsum2 : ∑ i : Fin (q + 1), (2 + full (t i)) = 2 * (q + 1) + ∑ i, full (t i) := by
    rw [Finset.sum_add_distrib]
    simp
    ring
  have hs : on (s, t) none = s := rfl
  rw [hsum, hsum2, hs]
  omega

/-- Number of page assignments with all pages good and `e` full pages. -/
def Z (p e : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin p → Bool × Bool × Bool =>
    (∀ i, two (t i)) ∧ ∑ i, full (t i) = e)).card

theorem Z_succ (p e : ℕ) :
    Z (p + 1) e = 3 * Z p e + (if e = 0 then 0 else Z p (e - 1)) := by
  unfold Z
  rw [Finset.card_filter]
  refine (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (p + 1) => Bool × Bool × Bool))
    (fun t : Fin (p + 1) → Bool × Bool × Bool =>
      if (∀ i, two (t i)) ∧ ∑ i, full (t i) = e then 1 else 0)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Finset.card_filter]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [two, full]
    ring
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp [two, full, add_comm 1]
    ring

theorem Z_zero (p : ℕ) : Z p 0 = 3 ^ p := by
  induction p with
  | zero => simp [Z]
  | succ p ih => rw [Z_succ, ih]; simp; ring

theorem Z_one (p : ℕ) : Z p 1 = p * 3 ^ (p - 1) := by
  induction p with
  | zero => simp [Z]
  | succ p ih =>
    rw [Z_succ, ih, if_neg one_ne_zero, Z_zero]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp
      ring

theorem card_cfg (q : ℕ) :
    Fintype.card {k : Cfg q // (∀ i, two (k.2 i)) ∧
      (if k.1 = true then 1 else 0) + ∑ i, full (k.2 i) = 1} = (q + 4) * 3 ^ q := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, zero_add]
  have h1 : (∑ t : Fin (q + 1) → Bool × Bool × Bool,
      if (∀ i, two (t i)) ∧ 1 + ∑ i, full (t i) = 1 then 1 else 0) = Z (q + 1) 0 := by
    rw [Z, Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp
  have h2 : (∑ t : Fin (q + 1) → Bool × Bool × Bool,
      if (∀ i, two (t i)) ∧ ∑ i, full (t i) = 1 then 1 else 0) = Z (q + 1) 1 := by
    rw [Z, Finset.card_filter]
  rw [h1, h2, Z_zero, Z_one]
  simp
  ring

open Classical in
theorem main_q (q : ℕ) :
    Nat.card {T : (bookGraph (q + 2)).Subgraph // T.IsSpanning ∧ T.coe.IsTree} =
      (q + 4) * 3 ^ q := by
  -- configurations satisfying the condition
  let X := {k : Cfg q // (∀ i, two (k.2 i)) ∧
      (if k.1 = true then 1 else 0) + ∑ i, full (k.2 i) = 1}
  have treeX : ∀ k : X, (G (on k.1)).IsTree := fun k => (isTree_iff _).mpr ((cond_on k.1).mpr k.2)
  let φ : X → {T : (bookGraph (q + 2)).Subgraph // T.IsSpanning ∧ T.coe.IsTree} := fun k =>
    toT (on k.1) (treeX k)
  have hinj : Function.Injective φ := by
    intro k k' h
    have h1 : (G (on k.1)).Adj = (G (on k'.1)).Adj := by
      have := congrArg (fun T => T.1.Adj) h
      exact this
    apply Subtype.ext
    apply on_injective
    funext x
    have hx : (G (on k.1)).Adj (ends x).1 (ends x).2 ↔ (G (on k'.1)).Adj (ends x).1 (ends x).2 := by
      rw [h1]
    rw [G_adj_ends, G_adj_ends] at hx
    exact Bool.eq_iff_iff.mpr hx
  have hsurj : Function.Surjective φ := by
    rintro ⟨T, hs, ht⟩
    let k : Cfg q := (decide (T.Adj (0, false) (0, true)),
      fun i => (decide (T.Adj (0, false) (i.succ, false)),
        decide (T.Adj (i.succ, false) (i.succ, true)), decide (T.Adj (0, true) (i.succ, true))))
    have hk : ∀ x : E q, on k x = true ↔ T.Adj (ends x).1 (ends x).2 := by
      intro x
      rcases x with _ | ⟨i, j⟩
      · simp [on, ends, k]
      · fin_cases j <;> simp [on, ends, k]
    have hG : ∀ u v, (G (on k)).Adj u v ↔ T.Adj u v := by
      intro u v
      rw [G_adj]
      constructor
      · rintro ⟨x, hx, hm⟩
        have := (hk x).mp hx
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact this
        · exact this.symm
      · intro h
        obtain ⟨x, hm⟩ := book_cover u v (T.adj_sub h)
        refine ⟨x, (hk x).mpr ?_, hm⟩
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact h.symm
    have hTeq : SimpleGraph.toSubgraph (G (on k)) (G_le _) = T := by
      apply SimpleGraph.Subgraph.ext
      · exact (SimpleGraph.Subgraph.isSpanning_iff.mp hs).symm
      · funext u v
        exact propext (hG u v)
    have hGeq : G (on k) = T.spanningCoe := by
      ext u v
      exact hG u v
    have htree : (G (on k)).IsTree := by
      rw [hGeq]
      exact (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning T hs).isTree_iff.mpr ht
    refine ⟨⟨k, (cond_on k).mp ((isTree_iff _).mp htree)⟩, ?_⟩
    exact Subtype.ext hTeq
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card]
  exact card_cfg q

end OMAA006234Helpers

open OMAA006234Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a006234.main := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
  exact main_q q
