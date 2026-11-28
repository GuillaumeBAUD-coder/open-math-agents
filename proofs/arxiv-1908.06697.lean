import OMAStatements.S_arxiv_1908_06697
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Formalization of Bellitto, Klimosova, Merker, Witkowski, Yuditsky, arXiv:1908.06697.
-- Sketch: for odd M >= 3 take M copies of the 16-vertex gadget H' of the paper (two copies of
-- H = an 8-cycle with chords v2v6, v3v7, joined by v4u1, v5u0) on ZMod M x Fin 16, and glue
-- the copies into two rings through the degree-2 vertices: (i, v1) ~ (i+1, v0) and
-- (i, u4) ~ (i+1, u5). The graph is cubic. No good colouring: Lemma 5 of the paper is checked
-- by decide on the 8 vertices of H, Lemma 6 follows for each copy of H', and then the colour of
-- (i, v0) alternates along the ring, impossible for odd M. 3-connectivity: reachability inside
-- one column minus at most two vertices is computed with bitmasks (decide), and the columns
-- are linked around the two rings; two deleted vertices in distinct columns cut at most one
-- consecutive pair of columns, which leaves a path of columns.

namespace OMA.P_arxiv_1908_06697

open OMA.S_arxiv_1908_06697

/-! ## Generic consequences of a good colouring -/

section generic
variable {V : Type} {G : SimpleGraph V} {c : V → Bool}

lemma cherry [Finite V] (h : GoodColouring G c) {x y z : V} (hy : G.Adj x y) (hz : G.Adj x z)
    (hyz : y ≠ z) (hx : c x = true) (hcy : c y = true) (hcz : c z = true) : False := by
  have h1 := h.1 x hx
  have hsub : ({y, z} : Set V) ⊆ {w | G.Adj x w ∧ c w = true} := by
    intro w hw
    rcases hw with rfl | rfl
    · exact ⟨hy, hcy⟩
    · exact ⟨hz, hcz⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hyz] at this
  omega

lemma redNbr (h : GoodColouring G c) {x n1 n2 n3 : V} (hx : c x = false)
    (hn : ∀ y, G.Adj x y → y = n1 ∨ y = n2 ∨ y = n3) :
    c n1 = false ∨ c n2 = false ∨ c n3 = false := by
  obtain ⟨w, hw, hcw⟩ := h.2.1 x hx
  rcases hn w hw with rfl | rfl | rfl
  · exact Or.inl hcw
  · exact Or.inr (Or.inl hcw)
  · exact Or.inr (Or.inr hcw)

lemma noPath (h : GoodColouring G c) {a b d e : V} (h1 : G.Adj a b) (h2 : G.Adj b d)
    (h3 : G.Adj d e) (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e)
    (hde : d ≠ e) (ca : c a = false) (cb : c b = false) (cd : c d = false)
    (ce : c e = false) : False := by
  apply h.2.2
  refine ⟨![a, b, d, e], ?_, ?_, h1, h2, h3⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [hab, had, hae, hbd, hbe, hde,
      hab.symm, had.symm, hae.symm, hbd.symm, hbe.symm, hde.symm] at hij)
  · intro i
    fin_cases i <;> simpa

end generic

/-! ## The graph: `M` copies of the 16-vertex gadget `H'` glued into two rings -/

/-- Half-edges at a local vertex: (target local vertex, column offset). Local vertices `0..7`
are `v₀..v₇` and `8..15` are `u₀..u₇` of the gadget `H'` of the paper. -/
def HE : Fin 16 → List (Fin 16 × ℤ) :=
  ![[(1, -1), (1, 0), (7, 0)],
    [(0, 0), (0, 1), (2, 0)],
    [(1, 0), (3, 0), (6, 0)],
    [(2, 0), (4, 0), (7, 0)],
    [(3, 0), (5, 0), (9, 0)],
    [(4, 0), (6, 0), (8, 0)],
    [(2, 0), (5, 0), (7, 0)],
    [(0, 0), (3, 0), (6, 0)],
    [(5, 0), (9, 0), (15, 0)],
    [(4, 0), (8, 0), (10, 0)],
    [(9, 0), (11, 0), (14, 0)],
    [(10, 0), (12, 0), (15, 0)],
    [(11, 0), (13, 0), (13, 1)],
    [(12, -1), (12, 0), (14, 0)],
    [(10, 0), (13, 0), (15, 0)],
    [(8, 0), (11, 0), (14, 0)]]

lemma HE_symm : ∀ k : Fin 16, ∀ p ∈ HE k, (k, -p.2) ∈ HE p.1 := by decide
lemma HE_irrefl : ∀ k : Fin 16, ∀ p ∈ HE k, p.1 ≠ k := by decide
lemma HE_off : ∀ k : Fin 16, ∀ p ∈ HE k, p.2 = -1 ∨ p.2 = 0 ∨ p.2 = 1 := by decide
lemma HE_nodup : ∀ k : Fin 16, (HE k).Nodup := by decide
lemma HE_len : ∀ k : Fin 16, (HE k).length = 3 := by decide

section graph
variable (M : ℕ)

def Adj' (x y : ZMod M × Fin 16) : Prop := ∃ p ∈ HE x.2, y.2 = p.1 ∧ y.1 = x.1 + (p.2 : ZMod M)

def G : SimpleGraph (ZMod M × Fin 16) where
  Adj := Adj' M
  symm := ⟨by
    rintro ⟨i, k⟩ ⟨j, l⟩ ⟨p, hp, h1, h2⟩
    simp only at h1 h2
    subst h1
    refine ⟨(k, -p.2), HE_symm k p hp, rfl, ?_⟩
    simp only
    rw [h2]; push_cast; ring⟩
  loopless := ⟨by
    rintro ⟨i, k⟩ ⟨p, hp, h1, -⟩
    exact HE_irrefl k p hp h1.symm⟩

instance : DecidableRel (G M).Adj := fun x y => by
  show Decidable (Adj' M x y)
  unfold Adj'
  infer_instance

variable {M}

lemma off_inj (hM : 3 ≤ M) {o o' : ℤ} (ho : o = -1 ∨ o = 0 ∨ o = 1)
    (ho' : o' = -1 ∨ o' = 0 ∨ o' = 1) (h : (o : ZMod M) = o') : o = o' := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hM' : (3 : ℤ) ≤ M := by exact_mod_cast hM
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

lemma adj_local {i : ZMod M} {k l : Fin 16} (h : (l, 0) ∈ HE k) : (G M).Adj (i, k) (i, l) :=
  ⟨(l, 0), h, rfl, by simp⟩

lemma adj_iff {x y : ZMod M × Fin 16} :
    (G M).Adj x y ↔ ∃ p ∈ HE x.2, y = (x.1 + (p.2 : ZMod M), p.1) := by
  show Adj' M x y ↔ _
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, hp, Prod.ext h2 h1⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl, rfl⟩

lemma regular [NeZero M] (hM : 3 ≤ M) : (G M).IsRegularOfDegree 3 := by
  intro x
  have hnb : (G M).neighborFinset x =
      ((HE x.2).map (fun p => (x.1 + (p.2 : ZMod M), p.1))).toFinset := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, adj_iff, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, List.toFinset_card_of_nodup,
    List.length_map, HE_len]
  apply List.Nodup.map_on _ (HE_nodup _)
  intro p hp q hq hpq
  simp only [Prod.mk.injEq] at hpq
  have h2 : p.2 = q.2 := off_inj hM (HE_off _ p hp) (HE_off _ q hq) (add_left_cancel hpq.1)
  exact Prod.ext hpq.2 h2

end graph

/-! ## No good colouring -/

def hCh : List (Fin 8 × Fin 8 × Fin 8) := [(0, 1, 7), (1, 0, 2), (2, 1, 3), (2, 1, 6), (2, 3, 6), (3, 2, 4), (3, 2, 7), (3, 4, 7), (4, 3, 5), (5, 4, 6), (6, 2, 5), (6, 2, 7), (6, 5, 7), (7, 0, 3), (7, 0, 6), (7, 3, 6)]
def hPath : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) := [(0, 1, 2, 3), (0, 1, 2, 6), (0, 7, 3, 2), (0, 7, 3, 4), (0, 7, 6, 2), (0, 7, 6, 5), (1, 0, 7, 3), (1, 0, 7, 6), (1, 2, 3, 4), (1, 2, 3, 7), (1, 2, 6, 5), (1, 2, 6, 7), (2, 1, 0, 7), (2, 3, 4, 5), (2, 3, 7, 6), (2, 6, 5, 4), (2, 6, 7, 3), (3, 2, 6, 5), (3, 2, 6, 7), (3, 4, 5, 6), (3, 7, 6, 5), (4, 3, 2, 6), (4, 3, 7, 6), (4, 5, 6, 7), (5, 4, 3, 7), (6, 2, 3, 7)]
def hRed : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) := [(2, 1, 3, 6), (3, 2, 4, 7), (6, 2, 5, 7), (7, 0, 3, 6)]

/-- Local checks inside one copy of `H` (the 8-vertex gadget of the paper). -/
def okH (a : Fin 8 → Bool) : Bool :=
  hCh.all (fun t => !(a t.1 && a t.2.1 && a t.2.2)) &&
  hPath.all (fun t => a t.1 || a t.2.1 || a t.2.2.1 || a t.2.2.2) &&
  hRed.all (fun t => a t.1 || !a t.2.1 || !a t.2.2.1 || !a t.2.2.2)

/-- Lemma 5 of the paper. -/
def concl5 (a : Fin 8 → Bool) : Bool :=
  (a 0 || a 1) && (!(a 0 && !a 1 && !a 2) || (a 4 && a 5)) &&
    (!(a 1 && !a 0 && !a 7) || (a 4 && a 5))

set_option maxRecDepth 100000 in
lemma lemma5 : ∀ a : Fin 8 → Bool, okH a = true → concl5 a = true := by decide +kernel

/-- The two copies of `H` inside `H'`. -/
def emb : Bool → Fin 8 → Fin 16
  | false => ![0, 1, 2, 3, 4, 5, 6, 7]
  | true => ![8, 9, 10, 11, 12, 13, 14, 15]

lemma emb_inj : ∀ e : Bool, ∀ x y : Fin 8, emb e x = emb e y → x = y := by decide

lemma hCh_ok : ∀ e : Bool, ∀ t ∈ hCh, (emb e t.2.1, (0 : ℤ)) ∈ HE (emb e t.1) ∧
    (emb e t.2.2, (0 : ℤ)) ∈ HE (emb e t.1) ∧ t.2.1 ≠ t.2.2 := by decide +kernel

def pathOk (e : Bool) (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Prop :=
  (emb e t.2.1, (0 : ℤ)) ∈ HE (emb e t.1) ∧
    (emb e t.2.2.1, (0 : ℤ)) ∈ HE (emb e t.2.1) ∧ (emb e t.2.2.2, (0 : ℤ)) ∈ HE (emb e t.2.2.1) ∧
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧ t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧
    t.2.2.1 ≠ t.2.2.2

instance (e t) : Decidable (pathOk e t) := by unfold pathOk; infer_instance

lemma hPath_okF : (hPath.all fun t => decide (pathOk false t)) = true := by decide +kernel
lemma hPath_okT : (hPath.all fun t => decide (pathOk true t)) = true := by decide +kernel

lemma hPath_ok (e : Bool) : ∀ t ∈ hPath, pathOk e t := by
  intro t ht
  cases e
  · exact of_decide_eq_true (List.all_eq_true.mp hPath_okF t ht)
  · exact of_decide_eq_true (List.all_eq_true.mp hPath_okT t ht)

lemma hRed_ok : ∀ e : Bool, ∀ t ∈ hRed, HE (emb e t.1) =
    [(emb e t.2.1, 0), (emb e t.2.2.1, 0), (emb e t.2.2.2, 0)] := by
  intro e t ht
  simp only [hRed, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> cases e <;> rfl

section colour
variable {M : ℕ} {c : ZMod M × Fin 16 → Bool}

lemma nbr3 {x : ZMod M × Fin 16} {a b d : Fin 16 × ℤ} (hx : HE x.2 = [a, b, d]) (y)
    (hy : (G M).Adj x y) : y = (x.1 + (a.2 : ZMod M), a.1) ∨ y = (x.1 + (b.2 : ZMod M), b.1) ∨
      y = (x.1 + (d.2 : ZMod M), d.1) := by
  obtain ⟨p, hp, rfl⟩ := adj_iff.mp hy
  rw [hx] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp

lemma okH_of_good [NeZero M] (h : GoodColouring (G M) c) (i : ZMod M) (e : Bool) :
    okH (fun k => c (i, emb e k)) = true := by
  have hne : ∀ x y : Fin 8, x ≠ y → ((i, emb e x) : ZMod M × Fin 16) ≠ (i, emb e y) := by
    intro x y hxy hh
    exact hxy (emb_inj e x y (Prod.mk.inj hh).2)
  simp only [okH, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := hCh_ok e t ht
    cases hx : c (i, emb e t.1) <;> cases hy : c (i, emb e t.2.1) <;>
      cases hz : c (i, emb e t.2.2) <;> simp
    exact cherry h (adj_local h1) (adj_local h2) (hne _ _ h3) hx hy hz
  · intro t ht
    obtain ⟨h1, h2, h3, d1, d2, d3, d4, d5, d6⟩ := hPath_ok e t ht
    cases ha : c (i, emb e t.1) <;> cases hb : c (i, emb e t.2.1) <;>
      cases hd : c (i, emb e t.2.2.1) <;> cases he : c (i, emb e t.2.2.2) <;> simp
    exact noPath h (adj_local h1) (adj_local h2) (adj_local h3) (hne _ _ d1) (hne _ _ d2)
      (hne _ _ d3) (hne _ _ d4) (hne _ _ d5) (hne _ _ d6) ha hb hd he
  · intro t ht
    have hl := hRed_ok e t ht
    have hn := nbr3 (x := (i, emb e t.1)) hl
    simp only [Int.cast_zero, add_zero] at hn
    cases hx : c (i, emb e t.1) <;> simp
    rcases redNbr h hx hn with h1 | h1 | h1 <;> simp [h1]

/-- Compact consequences of Lemmas 5 and 6 at one column. -/
lemma colLemma : ∀ p x0 x1 x2 x4 x5 x7 x8 x9 r : Bool,
    ((x0 || x1) && (!(x0 && !x1 && !x2) || (x4 && x5)) && (!(x1 && !x0 && !x7) || (x4 && x5))) = true →
    (x8 || x9) = true → (!(x4 && x5 && x9)) = true → (!(x5 && x4 && x8)) = true →
    (x0 || !p || !x1 || !x7) = true → (x1 || !x0 || !r || !x2) = true →
    (x0 || x1) = true ∧ (x0 || !x1 || !p) = true ∧ (x1 || !x0 || !r) = true := by decide

lemma combine : ∀ x0 x1 y0 y1 : Bool, (x0 || x1) = true → (x1 || !x0 || !y0) = true →
    (!(x1 && x0 && y0)) = true → (y0 || y1) = true → (y0 || !y1 || !x1) = true →
    y0 = !x0 := by decide

lemma col_facts [NeZero M] (hM : 3 ≤ M) (h : GoodColouring (G M) c) (i : ZMod M) :
    (c (i, 0) || c (i, 1)) = true ∧ (c (i, 0) || !c (i, 1) || !c (i - 1, 1)) = true ∧
    (c (i, 1) || !c (i, 0) || !c (i + 1, 0)) = true := by
  have V5 := lemma5 _ (okH_of_good h i false)
  have U5 := lemma5 _ (okH_of_good h i true)
  simp only [concl5, Bool.and_eq_true] at U5
  have hU : (c (i, 8) || c (i, 9)) = true := U5.1.1
  have hne : ∀ x y : Fin 16, x ≠ y → ((i, x) : ZMod M × Fin 16) ≠ (i, y) := by
    intro x y hxy hh; exact hxy (Prod.mk.inj hh).2
  have ch4 : (!(c (i, 4) && c (i, 5) && c (i, 9))) = true := by
    cases hx : c (i, 4) <;> cases hy : c (i, 5) <;> cases hz : c (i, 9) <;> simp
    exact cherry h (adj_local (by decide)) (adj_local (by decide)) (hne 5 9 (by decide)) hx hy hz
  have ch5 : (!(c (i, 5) && c (i, 4) && c (i, 8))) = true := by
    cases hx : c (i, 5) <;> cases hy : c (i, 4) <;> cases hz : c (i, 8) <;> simp
    exact cherry h (adj_local (by decide)) (adj_local (by decide)) (hne 4 8 (by decide)) hx hy hz
  have r0 : (c (i, 0) || !c (i - 1, 1) || !c (i, 1) || !c (i, 7)) = true := by
    have hn := nbr3 (x := (i, 0)) (a := (1, -1)) (b := (1, 0)) (d := (7, 0)) rfl
    simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, add_zero, ← sub_eq_add_neg] at hn
    cases hx : c (i, 0) <;> simp
    rcases redNbr h hx hn with h1 | h1 | h1 <;> simp [h1]
  have r1 : (c (i, 1) || !c (i, 0) || !c (i + 1, 0) || !c (i, 2)) = true := by
    have hn := nbr3 (x := (i, 1)) (a := (0, 0)) (b := (0, 1)) (d := (2, 0)) rfl
    simp only [Int.cast_one, Int.cast_zero, add_zero] at hn
    cases hx : c (i, 1) <;> simp
    rcases redNbr h hx hn with h1 | h1 | h1 <;> simp [h1]
  exact colLemma _ _ _ _ _ _ _ _ _ _ V5 hU ch4 ch5 r0 r1

lemma alternate [NeZero M] (hM : 3 ≤ M) (h : GoodColouring (G M) c) (i : ZMod M) :
    c (i + 1, 0) = !c (i, 0) := by
  obtain ⟨a1, -, a3⟩ := col_facts hM h i
  obtain ⟨b1, b2, -⟩ := col_facts hM h (i + 1)
  rw [add_sub_cancel_right] at b2
  have hne : ((i, 0) : ZMod M × Fin 16) ≠ (i + 1, 0) := by
    intro hh
    have h1 : (1 : ZMod M) = 0 := by
      have := congrArg Prod.fst hh
      simpa using this.symm
    have : ((1 : ℕ) : ZMod M) = 0 := by simpa using h1
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd one_pos this
    omega
  have ch : (!(c (i, 1) && c (i, 0) && c (i + 1, 0))) = true := by
    cases hx : c (i, 1) <;> cases hy : c (i, 0) <;> cases hz : c (i + 1, 0) <;> simp
    exact cherry h (adj_local (by decide)) ⟨(0, 1), (by decide : ((0 : Fin 16), (1 : ℤ)) ∈ HE 1), rfl, by simp⟩ hne hx hy hz
  exact combine _ _ _ _ a1 a3 ch b1 b2

lemma noGood [NeZero M] (hM : 3 ≤ M) (hodd : Odd M) (c : ZMod M × Fin 16 → Bool) :
    ¬ GoodColouring (G M) c := by
  intro h
  have key : ∀ n : ℕ, c ((0 : ZMod M) + n, 0) = (if Even n then c (0, 0) else !c (0, 0)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, alternate hM h, ih]
      by_cases hn : Even n
      · have : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hn
        simp [hn, this]
      · have : Even (n + 1) := by rw [Nat.even_add_one]; exact hn
        simp [hn, this]
  have := key M
  rw [ZMod.natCast_self, add_zero, if_neg (Nat.not_even_iff_odd.mpr hodd)] at this
  cases hc : c (0, 0) <;> simp [hc] at this

end colour

/-! ## 3-connectivity

Local reachability inside one column is computed with bitmasks: `clos t1 t2 a` is the set of
local vertices reachable from `a` in `H'` minus the (at most two) local vertices `t1`, `t2`. -/

def nbMask : Fin 16 → ℕ :=
  ![130, 5, 74, 148, 552, 336, 164, 73, 33312, 1296, 18944, 37888, 10240, 20480, 41984, 18688]

def bitO : Option (Fin 16) → ℕ
  | none => 0
  | some k => 2 ^ k.val

def remB (t1 t2 : Option (Fin 16)) (b : Fin 16) : Bool := decide (some b = t1) || decide (some b = t2)

def spread (m : ℕ) : ℕ :=
  (List.finRange 16).foldr (fun k acc => (if m.testBit k.val then nbMask k else 0) ||| acc) 0

def step (R m : ℕ) : ℕ := m ||| (spread m &&& (65535 ^^^ R))

def iter (R : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | n + 1, m => iter R n (step R m)

def clos (t1 t2 : Option (Fin 16)) (a : Fin 16) : ℕ := iter (bitO t1 ||| bitO t2) 10 (2 ^ a.val)

def ports : List (Fin 16) := [0, 1, 12, 13]

def a0 (t1 t2 : Option (Fin 16)) : Fin 16 := if remB t1 t2 0 then 1 else 0

theorem F1_0 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB none t2 a = false →
    ∃ p ∈ ports, remB none t2 p = false ∧ (clos none t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_1 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 0) t2 a = false →
    ∃ p ∈ ports, remB (some 0) t2 p = false ∧ (clos (some 0) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_2 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 1) t2 a = false →
    ∃ p ∈ ports, remB (some 1) t2 p = false ∧ (clos (some 1) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_3 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 2) t2 a = false →
    ∃ p ∈ ports, remB (some 2) t2 p = false ∧ (clos (some 2) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_4 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 3) t2 a = false →
    ∃ p ∈ ports, remB (some 3) t2 p = false ∧ (clos (some 3) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_5 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 4) t2 a = false →
    ∃ p ∈ ports, remB (some 4) t2 p = false ∧ (clos (some 4) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_6 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 5) t2 a = false →
    ∃ p ∈ ports, remB (some 5) t2 p = false ∧ (clos (some 5) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_7 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 6) t2 a = false →
    ∃ p ∈ ports, remB (some 6) t2 p = false ∧ (clos (some 6) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_8 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 7) t2 a = false →
    ∃ p ∈ ports, remB (some 7) t2 p = false ∧ (clos (some 7) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_9 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 8) t2 a = false →
    ∃ p ∈ ports, remB (some 8) t2 p = false ∧ (clos (some 8) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_10 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 9) t2 a = false →
    ∃ p ∈ ports, remB (some 9) t2 p = false ∧ (clos (some 9) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_11 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 10) t2 a = false →
    ∃ p ∈ ports, remB (some 10) t2 p = false ∧ (clos (some 10) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_12 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 11) t2 a = false →
    ∃ p ∈ ports, remB (some 11) t2 p = false ∧ (clos (some 11) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_13 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 12) t2 a = false →
    ∃ p ∈ ports, remB (some 12) t2 p = false ∧ (clos (some 12) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_14 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 13) t2 a = false →
    ∃ p ∈ ports, remB (some 13) t2 p = false ∧ (clos (some 13) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_15 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 14) t2 a = false →
    ∃ p ∈ ports, remB (some 14) t2 p = false ∧ (clos (some 14) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1_16 : ∀ t2 : Option (Fin 16), ∀ a : Fin 16, remB (some 15) t2 a = false →
    ∃ p ∈ ports, remB (some 15) t2 p = false ∧ (clos (some 15) t2 a).testBit p.val = true := by
  decide +kernel

theorem F1 : ∀ t1 t2 : Option (Fin 16), ∀ a : Fin 16, remB t1 t2 a = false →
    ∃ p ∈ ports, remB t1 t2 p = false ∧ (clos t1 t2 a).testBit p.val = true := by
  intro t1
  rcases t1 with _ | k
  · exact F1_0
  · fin_cases k
    exacts [F1_1, F1_2, F1_3, F1_4, F1_5, F1_6, F1_7, F1_8, F1_9, F1_10, F1_11, F1_12, F1_13,
      F1_14, F1_15, F1_16]

theorem F2n : ∀ t : Option (Fin 16), ∀ b : Fin 16,
    remB t none b = false → (clos t none (a0 t none)).testBit b.val = true := by
  decide +kernel

lemma remB_a0 : ∀ t : Option (Fin 16), remB t none (a0 t none) = false := by decide

lemma bitO_testBit : ∀ t1 t2 : Option (Fin 16), ∀ b : Fin 16,
    (bitO t1 ||| bitO t2).testBit b.val = remB t1 t2 b := by decide +kernel

lemma full_testBit : ∀ b : Fin 16, (65535 : ℕ).testBit b.val = true := by decide

lemma nbMask_ok : ∀ k b : Fin 16, (nbMask k).testBit b.val = true → (b, (0 : ℤ)) ∈ HE k := by
  decide +kernel

lemma remB_comm (t1 t2 : Option (Fin 16)) : remB t1 t2 = remB t2 t1 := by
  funext b; simp [remB, Bool.or_comm]

lemma clos_comm (t1 t2 : Option (Fin 16)) : clos t1 t2 = clos t2 t1 := by
  funext a; simp [clos, Nat.lor_comm]

lemma F2 (t1 t2 : Option (Fin 16)) (hs : t1 = none ∨ t2 = none) :
    remB t1 t2 (a0 t1 t2) = false ∧ ∀ b : Fin 16, remB t1 t2 b = false →
      (clos t1 t2 (a0 t1 t2)).testBit b.val = true := by
  rcases hs with rfl | rfl
  · have ha : a0 none t2 = a0 t2 none := by simp [a0, remB_comm none t2]
    rw [ha, remB_comm, clos_comm]
    exact ⟨remB_a0 t2, F2n t2⟩
  · exact ⟨remB_a0 t1, F2n t1⟩

lemma foldr_testBit (m b : ℕ) (l : List (Fin 16))
    (h : (l.foldr (fun k acc => (if m.testBit k.val then nbMask k else 0) ||| acc) 0).testBit b
      = true) : ∃ k ∈ l, m.testBit k.val = true ∧ (nbMask k).testBit b = true := by
  induction l with
  | nil => simp at h
  | cons k l ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · split_ifs at h with hk
      · exact ⟨k, by simp, hk, h⟩
      · simp at h
    · obtain ⟨k', hk', h1, h2⟩ := ih h
      exact ⟨k', by simp [hk'], h1, h2⟩

section conn
variable {M : ℕ} (o1 o2 : Option (ZMod M × Fin 16))

def rem (x : ZMod M × Fin 16) : Prop := some x = o1 ∨ some x = o2

instance (x : ZMod M × Fin 16) : Decidable (rem o1 o2 x) := by unfold rem; infer_instance

def locO (o : Option (ZMod M × Fin 16)) (i : ZMod M) : Option (Fin 16) :=
  o.bind (fun s => if s.1 = i then some s.2 else none)

lemma some_eq_iff (o : Option (ZMod M × Fin 16)) (i : ZMod M) (b : Fin 16) :
    some (i, b) = o ↔ some b = locO o i := by
  rcases o with _ | ⟨s1, s2⟩
  · simp [locO]
  · by_cases h : s1 = i
    · subst h; simp [locO, eq_comm]
    · simp [locO, h, Ne.symm h]

lemma rem_iff (i : ZMod M) (b : Fin 16) :
    rem o1 o2 (i, b) ↔ remB (locO o1 i) (locO o2 i) b = true := by
  simp [rem, remB, some_eq_iff]

def Rch (x y : ZMod M × Fin 16) : Prop :=
  ∃ (hx : ¬ rem o1 o2 x) (hy : ¬ rem o1 o2 y),
    ((G M).induce {z | rem o1 o2 z}ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩

variable {o1 o2}

lemma Rch.refl {x} (hx : ¬ rem o1 o2 x) : Rch o1 o2 x x := ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

lemma Rch.symm {x y} (h : Rch o1 o2 x y) : Rch o1 o2 y x :=
  let ⟨hx, hy, r⟩ := h; ⟨hy, hx, r.symm⟩

lemma Rch.trans {x y z} (h : Rch o1 o2 x y) (h' : Rch o1 o2 y z) : Rch o1 o2 x z :=
  let ⟨hx, _, r⟩ := h; let ⟨_, hz, r'⟩ := h'; ⟨hx, hz, r.trans r'⟩

lemma Rch.of_adj {x y} (hx : ¬ rem o1 o2 x) (hy : ¬ rem o1 o2 y) (h : (G M).Adj x y) :
    Rch o1 o2 x y :=
  ⟨hx, hy, SimpleGraph.Adj.reachable (by simpa using h)⟩

lemma clos_sound (i : ZMod M) (a : Fin 16) (ha : ¬ rem o1 o2 (i, a)) (b : Fin 16)
    (hb : (clos (locO o1 i) (locO o2 i) a).testBit b.val = true) : Rch o1 o2 (i, a) (i, b) := by
  have hstep : ∀ m : ℕ, (∀ b : Fin 16, m.testBit b.val = true → Rch o1 o2 (i, a) (i, b)) →
      ∀ b : Fin 16, (step (bitO (locO o1 i) ||| bitO (locO o2 i)) m).testBit b.val = true →
        Rch o1 o2 (i, a) (i, b) := by
    intro m H b hb
    simp only [step, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Bool.or_eq_true,
      Bool.and_eq_true, full_testBit, bitO_testBit] at hb
    rcases hb with hb | ⟨hs, hr⟩
    · exact H b hb
    · obtain ⟨k, -, hk, hkb⟩ := foldr_testBit m b.val _ hs
      have hrem : ¬ rem o1 o2 (i, b) := by
        rw [rem_iff, ← bitO_testBit]; simpa [Nat.testBit_or] using hr
      have hik := H k hk
      exact hik.trans (Rch.of_adj hik.2.1 hrem (adj_local (nbMask_ok k b hkb)))
  have hiter : ∀ n : ℕ, ∀ m : ℕ, (∀ b : Fin 16, m.testBit b.val = true → Rch o1 o2 (i, a) (i, b)) →
      ∀ b : Fin 16, (iter (bitO (locO o1 i) ||| bitO (locO o2 i)) n m).testBit b.val = true →
        Rch o1 o2 (i, a) (i, b) := by
    intro n
    induction n with
    | zero => intro m H; exact H
    | succ n ih => intro m H; exact ih _ (hstep m H)
  refine hiter 10 _ ?_ b hb
  intro b' hb'
  rw [Nat.testBit_two_pow] at hb'
  have : a = b' := Fin.ext (of_decide_eq_true hb')
  subst this
  exact Rch.refl ha

lemma colPort (i : ZMod M) (a : Fin 16) (ha : ¬ rem o1 o2 (i, a)) :
    ∃ p ∈ ports, ¬ rem o1 o2 (i, p) ∧ Rch o1 o2 (i, a) (i, p) := by
  rw [rem_iff] at ha
  obtain ⟨p, hp, hp1, hp2⟩ := F1 (locO o1 i) (locO o2 i) a (by simpa using ha)
  have hpr : ¬ rem o1 o2 (i, p) := by rw [rem_iff]; simpa using hp1
  exact ⟨p, hp, hpr, clos_sound i a (by rw [rem_iff]; exact ha) p hp2⟩

lemma colConn (i : ZMod M) (hs : locO o1 i = none ∨ locO o2 i = none) (a b : Fin 16)
    (ha : ¬ rem o1 o2 (i, a)) (hb : ¬ rem o1 o2 (i, b)) : Rch o1 o2 (i, a) (i, b) := by
  obtain ⟨hz, hall⟩ := F2 _ _ hs
  have hz' : ¬ rem o1 o2 (i, a0 (locO o1 i) (locO o2 i)) := by rw [rem_iff]; simp [hz]
  have h1 := clos_sound i _ hz' a (hall a (by rw [rem_iff] at ha; simpa using ha))
  have h2 := clos_sound i _ hz' b (hall b (by rw [rem_iff] at hb; simpa using hb))
  exact h1.symm.trans h2

lemma conn_of_hub (z : ZMod M × Fin 16) (hz : ¬ rem o1 o2 z)
    (H : ∀ x, ¬ rem o1 o2 x → Rch o1 o2 x z) :
    ((G M).induce {x | rem o1 o2 x}ᶜ).Connected := by
  have : Nonempty ↥({x | rem o1 o2 x}ᶜ) := ⟨⟨z, hz⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨_, _, hu⟩ := H u.1 u.2
  obtain ⟨_, _, hv⟩ := H v.1 v.2
  exact hu.trans hv.symm

lemma adj_top (i : ZMod M) : (G M).Adj (i, 1) (i + 1, 0) :=
  ⟨(0, 1), (by decide : ((0 : Fin 16), (1 : ℤ)) ∈ HE 1), rfl, by simp⟩

lemma adj_bot (i : ZMod M) : (G M).Adj (i, 12) (i + 1, 13) :=
  ⟨(13, 1), (by decide : ((13 : Fin 16), (1 : ℤ)) ∈ HE 12), rfl, by simp⟩

lemma walk (i0 : ZMod M) (zb : Fin 16) (hz : ¬ rem o1 o2 (i0, zb)) (K : ℕ)
    (hconn : ∀ k ≤ K, ∀ a b, ¬ rem o1 o2 (i0 + k, a) → ¬ rem o1 o2 (i0 + k, b) →
      Rch o1 o2 (i0 + k, a) (i0 + k, b))
    (hlink : ∀ k < K, (¬ rem o1 o2 (i0 + k, 1) ∧ ¬ rem o1 o2 (i0 + k + 1, 0)) ∨
      (¬ rem o1 o2 (i0 + k, 12) ∧ ¬ rem o1 o2 (i0 + k + 1, 13))) :
    ∀ k ≤ K, ∀ a, ¬ rem o1 o2 (i0 + k, a) → Rch o1 o2 (i0 + k, a) (i0, zb) := by
  intro k
  induction k with
  | zero =>
    intro hk a ha
    have := hconn 0 hk a zb ha (by simpa using hz)
    simpa using this
  | succ k ih =>
    intro hk a ha
    have e : i0 + ((k + 1 : ℕ) : ZMod M) = i0 + (k : ZMod M) + 1 := by push_cast; ring
    have hc := hconn (k + 1) hk
    rw [e] at ha hc ⊢
    rcases hlink k (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hc a 0 ha h2).trans ((Rch.of_adj h2 h1 (adj_top _).symm).trans (ih (by omega) 1 h1))
    · exact (hc a 13 ha h2).trans ((Rch.of_adj h2 h1 (adj_bot _).symm).trans (ih (by omega) 12 h1))

lemma natCast_ne (hM : 3 ≤ M) {k : ℕ} (h0 : 0 < k) (h1 : k < M) : (k : ZMod M) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd h0 h
  omega

lemma column_val [NeZero M] (i0 j : ZMod M) : ∃ k : ℕ, k < M ∧ j = i0 + (k : ZMod M) := by
  refine ⟨(j - i0).val, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val]; ring

lemma locO_none (o : Option (ZMod M × Fin 16)) (i : ZMod M) (h : ∀ s, o = some s → s.1 ≠ i) :
    locO o i = none := by
  rcases o with _ | s
  · rfl
  · simp [locO, h s rfl]

theorem conn [NeZero M] (hM : 3 ≤ M) : ((G M).induce {x | rem o1 o2 x}ᶜ).Connected := by
  by_cases hA : ∃ c : ZMod M, ∀ x, rem o1 o2 x → x.1 = c
  · obtain ⟨c, hc⟩ := hA
    have hfree : ∀ x : ZMod M × Fin 16, x.1 ≠ c → ¬ rem o1 o2 x := fun x hx hr => hx (hc x hr)
    have hsing : ∀ i, i ≠ c → locO o1 i = none ∨ locO o2 i = none := by
      intro i hi
      left
      apply locO_none
      intro s hs hsi
      exact hi (hsi ▸ hc s (Or.inl hs.symm))
    have hne : ∀ k : ℕ, k ≤ M - 2 → c + 1 + (k : ZMod M) ≠ c := by
      intro k hk h
      apply natCast_ne hM (k := k + 1) (by omega) (by omega)
      push_cast
      linear_combination h
    have hz : ¬ rem o1 o2 (c + 1, 0) := hfree _ (by simpa using hne 0 (by omega))
    have hw := walk (c + 1) 0 hz (M - 2)
      (fun k hk a b ha hb => colConn _ (hsing _ (hne k hk)) a b ha hb)
      (fun k hk => Or.inl ⟨hfree _ (hne k (by omega)), hfree _ (by
          have := hne (k + 1) (by omega); push_cast at this; simpa [add_assoc] using this)⟩)
    have hother : ∀ x : ZMod M × Fin 16, x.1 ≠ c → Rch o1 o2 x (c + 1, 0) := by
      rintro ⟨j, a⟩ hj
      obtain ⟨k, hlt, rfl⟩ := column_val (c + 1) j
      have hk : k ≤ M - 2 := by
        by_contra hk
        have hk' : k = M - 1 := by omega
        apply hj
        simp only
        rw [hk', Nat.cast_sub (by omega), ZMod.natCast_self]
        ring
      exact hw k hk a (hfree _ hj)
    apply conn_of_hub (c + 1, 0) hz
    rintro ⟨j, a⟩ hx
    by_cases hj : j = c
    · subst hj
      obtain ⟨p, hp, hpr, hrp⟩ := colPort j a hx
      have hm1 : j - 1 ≠ j := by
        intro h
        apply natCast_ne hM (k := 1) (by omega) (by omega)
        simpa using (show (1 : ZMod M) = 0 by linear_combination -h)
      have hp1 : j + 1 ≠ j := by simpa using hne 0 (by omega)
      simp only [ports, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · have hq := hfree (j - 1, 1) hm1
        have hadj : (G M).Adj (j, 0) (j - 1, 1) := by
          have := (adj_top (M := M) (j - 1)).symm; simpa using this
        exact hrp.trans ((Rch.of_adj hpr hq hadj).trans (hother _ hm1))
      · have hq := hfree (j + 1, 0) hp1
        exact hrp.trans ((Rch.of_adj hpr hq (adj_top j)).trans (hother _ hp1))
      · have hq := hfree (j + 1, 13) hp1
        exact hrp.trans ((Rch.of_adj hpr hq (adj_bot j)).trans (hother _ hp1))
      · have hq := hfree (j - 1, 12) hm1
        have hadj : (G M).Adj (j, 13) (j - 1, 12) := by
          have := (adj_bot (M := M) (j - 1)).symm; simpa using this
        exact hrp.trans ((Rch.of_adj hpr hq hadj).trans (hother _ hm1))
    · exact hother _ hj
  · -- two removed vertices in different columns
    obtain ⟨s1, s2, rfl, rfl, hcol⟩ : ∃ s1 s2 : ZMod M × Fin 16, o1 = some s1 ∧ o2 = some s2 ∧
        s1.1 ≠ s2.1 := by
      rcases o1 with _ | s1
      · exfalso; apply hA
        rcases o2 with _ | s2
        · exact ⟨0, fun x hx => by simp [rem] at hx⟩
        · exact ⟨s2.1, fun x hx => by simp [rem] at hx; rw [hx]⟩
      · rcases o2 with _ | s2
        · exfalso; apply hA
          exact ⟨s1.1, fun x hx => by simp [rem] at hx; rw [hx]⟩
        · refine ⟨s1, s2, rfl, rfl, fun h => hA ⟨s1.1, fun x hx => ?_⟩⟩
          simp only [rem, Option.some.injEq] at hx
          rcases hx with rfl | rfl
          · rfl
          · exact h.symm
    have remE : ∀ x, rem (some s1) (some s2) x ↔ x = s1 ∨ x = s2 := by
      intro x; simp [rem]
    have hsing : ∀ i, locO (some s1) i = none ∨ locO (some s2) i = none := by
      intro i
      by_cases h : s1.1 = i
      · right; apply locO_none; intro s hs; cases hs; intro h'; exact hcol (h.trans h'.symm)
      · left; apply locO_none; intro s hs; cases hs; exact h
    have hconnAll : ∀ i a b, ¬ rem (some s1) (some s2) (i, a) → ¬ rem (some s1) (some s2) (i, b) →
        Rch (some s1) (some s2) (i, a) (i, b) := fun i => colConn i (hsing i)
    have hdead : ∀ i, ¬ ((¬ rem (some s1) (some s2) (i, 1) ∧ ¬ rem (some s1) (some s2) (i + 1, 0)) ∨
        (¬ rem (some s1) (some s2) (i, 12) ∧ ¬ rem (some s1) (some s2) (i + 1, 13))) →
        (s1.1 = i ∧ s2.1 = i + 1) ∨ (s1.1 = i + 1 ∧ s2.1 = i) := by
      intro i h
      have h1 : rem (some s1) (some s2) (i, 1) ∨ rem (some s1) (some s2) (i + 1, 0) := by
        by_contra hh; push Not at hh; exact h (Or.inl hh)
      have h2 : rem (some s1) (some s2) (i, 12) ∨ rem (some s1) (some s2) (i + 1, 13) := by
        by_contra hh; push Not at hh; exact h (Or.inr hh)
      rcases h1 with t1 | t1 <;> rcases h2 with t2 | t2 <;> rw [remE] at t1 t2 <;>
        rcases t1 with t1 | t1 <;> rcases t2 with t2 | t2 <;>
        first
        | (exfalso; rw [← t1] at t2; simp at t2; done)
        | (exfalso; apply hcol; simp [← t1, ← t2]; done)
        | (left; refine ⟨?_, ?_⟩ <;> simp [← t1, ← t2] <;> done)
        | (right; refine ⟨?_, ?_⟩ <;> simp [← t1, ← t2] <;> done)
    have h2ne : (2 : ZMod M) ≠ 0 := by
      have := natCast_ne hM (k := 2) (by omega) (by omega); simpa using this
    -- choose the starting column
    obtain ⟨i0, hi0⟩ : ∃ i0 : ZMod M, ∀ k : ℕ, k < M - 1 →
        ((¬ rem (some s1) (some s2) (i0 + k, 1) ∧ ¬ rem (some s1) (some s2) (i0 + k + 1, 0)) ∨
        (¬ rem (some s1) (some s2) (i0 + k, 12) ∧ ¬ rem (some s1) (some s2) (i0 + k + 1, 13))) := by
      by_cases h12 : s2.1 = s1.1 + 1
      · refine ⟨s1.1 + 1, fun k hk => ?_⟩
        by_contra hd
        rcases hdead _ hd with ⟨a, b⟩ | ⟨a, b⟩
        · apply natCast_ne hM (k := k + 1) (by omega) (by omega)
          push_cast; linear_combination -a
        · apply h2ne; linear_combination -a + b - h12
      · by_cases h21 : s1.1 = s2.1 + 1
        · refine ⟨s2.1 + 1, fun k hk => ?_⟩
          by_contra hd
          rcases hdead _ hd with ⟨a, b⟩ | ⟨a, b⟩
          · apply h2ne; linear_combination -b + a - h21
          · apply natCast_ne hM (k := k + 1) (by omega) (by omega)
            push_cast; linear_combination -b
        · refine ⟨s1.1, fun k hk => ?_⟩
          by_contra hd
          rcases hdead _ hd with ⟨a, b⟩ | ⟨a, b⟩
          · apply h12; rw [a, b]
          · apply h21; rw [a, b]
    -- the hub
    have hz : ¬ rem (some s1) (some s2) (i0, if rem (some s1) (some s2) (i0, 0) then 1 else 0) := by
      split_ifs with h0
      · intro h1
        rw [remE] at h0 h1
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
        · rw [← h1] at h0; simp at h0
        · exact hcol (by rw [← h0, ← h1])
        · exact hcol (by rw [← h0, ← h1])
        · rw [← h1] at h0; simp at h0
      · exact h0
    have hw := walk i0 _ hz (M - 1) (fun k _ a b ha hb => hconnAll _ a b ha hb)
      (fun k hk => hi0 k hk)
    apply conn_of_hub _ hz
    rintro ⟨j, a⟩ hx
    obtain ⟨k, hlt, rfl⟩ := column_val i0 j
    exact hw k (by omega) a hx

end conn

lemma set_two {α : Type} [Finite α] (S : Set α) (h : S.ncard ≤ 2) :
    ∃ o1 o2 : Option α, ∀ x, x ∈ S ↔ (some x = o1 ∨ some x = o2) := by
  rcases Nat.lt_or_ge S.ncard 2 with h2 | h2
  · rcases Nat.lt_or_ge S.ncard 1 with h1 | h1
    · have h0 : S.ncard = 0 := by omega
      have : S = ∅ := (Set.ncard_eq_zero (Set.toFinite S)).mp h0
      exact ⟨none, none, by simp [this]⟩
    · have h1' : S.ncard = 1 := by omega
      obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h1'
      exact ⟨some a, none, by simp [eq_comm]⟩
  · have h2' : S.ncard = 2 := by omega
    obtain ⟨a, b, -, rfl⟩ := Set.ncard_eq_two.mp h2'
    exact ⟨some a, some b, by simp [eq_comm]⟩

theorem main' : ∀ N : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj), N ≤ Fintype.card V ∧ 8 ≤ Fintype.card V ∧
    G.IsRegularOfDegree 3 ∧ ThreeConnected G ∧ ∀ c : V → Bool, ¬ GoodColouring G c := by
  intro N
  have : NeZero (2 * N + 3) := ⟨by omega⟩
  have hM : 3 ≤ 2 * N + 3 := by omega
  have hodd : Odd (2 * N + 3) := ⟨N + 1, by ring⟩
  have hcard : Fintype.card (ZMod (2 * N + 3) × Fin 16) = (2 * N + 3) * 16 := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
  refine ⟨ZMod (2 * N + 3) × Fin 16, inferInstance, G (2 * N + 3), inferInstance, ?_, ?_,
    regular hM, ⟨?_, ?_⟩, noGood hM hodd⟩
  · rw [hcard]; omega
  · rw [hcard]; omega
  · rw [hcard]; omega
  · intro S hS
    obtain ⟨o1, o2, hS'⟩ := set_two S hS
    have hS2 : S = {x | rem o1 o2 x} := Set.ext hS'
    subst hS2
    exact conn hM

end OMA.P_arxiv_1908_06697

theorem OMA.solution : type_of% @OMA.S_arxiv_1908_06697.main := OMA.P_arxiv_1908_06697.main'

