import OMAReductions.R_Erdos596_erdos_596_variants_K4_K3_exceptional_iff_R1
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-!
Folkman's finite edge Ramsey theorem for triangles, by the Nešetřil–Rödl
partite construction. See Erdős Problem 596 (https://www.erdosproblems.com/596).
JaviSoto previously formalized the finite triangle case in
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2517.
Credit for this proof: @grp06.
-/

namespace FolkmanTrianglePartite

open SimpleGraph Combinatorics

private lemma copy_of_adj {V : Type} {G : SimpleGraph V} {k : ℕ} (f : Fin k → V)
    (hf : ∀ ⦃i j⦄, i ≠ j → G.Adj (f i) (f j)) :
    (completeGraph (Fin k)).IsContained G := by
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    exact hf hij
  · intro i j he
    by_contra hne
    exact (hf hne).ne he

private lemma triangle_of_adj {V : Type} {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (completeGraph (Fin 3)).IsContained G := by
  refine copy_of_adj (![x, y, z]) ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact hxy | exact hxz | exact hyz
          | exact hxy.symm | exact hxz.symm | exact hyz.symm

/-- The crude bound obtained by repeatedly taking a single-colour neighborhood. -/
private def threshold (n : ℕ) : ℕ → ℕ
  | 0 => 2
  | k + 1 => n * threshold n k + 1

private lemma threshold_two {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 2 ≤ threshold n k := by
  induction k with
  | zero => simp [threshold]
  | succ k ih =>
    have h := Nat.mul_le_mul_right (threshold n k) hn
    simp only [Nat.one_mul] at h
    rw [threshold]
    omega

private lemma ramsey_on_finset {P : Type} {n : ℕ} (hn : 1 ≤ n)
    (d : P → P → Fin n) (k : ℕ) (s : Finset P) (t : Finset (Fin n))
    (hs : threshold n k ≤ s.card) (ht : t.card ≤ k)
    (hcol : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d x y ∈ t) :
    ∃ x y z : P, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ d x y = d x z ∧ d x y = d y z := by
  classical
  induction k generalizing s t with
  | zero =>
    have hsize : 1 < s.card := by
      have h := threshold_two hn 0
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hsize
    have hm := hcol x hx y hy hxy
    have hp : 0 < t.card := Finset.card_pos.mpr ⟨_, hm⟩
    omega
  | succ k ih =>
    have hs2 := (threshold_two hn (k + 1)).trans hs
    have hspos : 0 < s.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hspos
    let u := s.erase x
    have hu : n * threshold n k ≤ u.card := by
      have he : u.card + 1 = s.card := Finset.card_erase_add_one hx
      rw [threshold] at hs
      omega
    have hpalette : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hmul : (Finset.univ : Finset (Fin n)).card * threshold n k ≤ u.card := by
      simpa using hu
    obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := d x) (s := u) (fun _ _ => Finset.mem_univ _) hpalette hmul
    let v := u.filter (fun y => d x y = c)
    have hv : threshold n k ≤ v.card := hc
    have hmem : ∀ y ∈ v, y ≠ x ∧ y ∈ s ∧ d x y = c := by
      intro y hy
      change y ∈ u.filter (fun z => d x z = c) at hy
      obtain ⟨hyu, hyc⟩ := Finset.mem_filter.mp hy
      change y ∈ s.erase x at hyu
      obtain ⟨hyx, hys⟩ := Finset.mem_erase.mp hyu
      exact ⟨hyx, hys, hyc⟩
    have hv2 := (threshold_two hn k).trans hv
    have hvpos : 0 < v.card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hvpos
    obtain ⟨hyx, hys, hyc⟩ := hmem y hy
    have hct : c ∈ t := hyc ▸ hcol x hx y hys hyx.symm
    by_cases hm : ∃ a ∈ v, ∃ b ∈ v, a ≠ b ∧ d a b = c
    · obtain ⟨a, ha, b, hb, hab, hcab⟩ := hm
      obtain ⟨hax, _, hca⟩ := hmem a ha
      obtain ⟨hbx, _, hcb⟩ := hmem b hb
      exact ⟨x, a, b, hax.symm, hbx.symm, hab, hca.trans hcb.symm, hca.trans hcab.symm⟩
    · have ht' : (t.erase c).card ≤ k := by
        have he := Finset.card_erase_add_one hct
        omega
      refine ih v (t.erase c) hv ht' ?_
      intro a ha b hb hab
      apply Finset.mem_erase.mpr
      exact ⟨fun h => hm ⟨a, ha, b, hb, hab, h⟩,
        hcol a (hmem a ha).2.1 b (hmem b hb).2.1 hab⟩

private abbrev Parted {W P : Type} (G : SimpleGraph W) (p : W → P) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → p x ≠ p y

section Expansion

variable {P W : Type} (G : SimpleGraph W) (p : W → P) (a b : P)

/-- Letters record an edge oriented from part `a` to part `b`. -/
private abbrev Fiber := {e : W × W // G.Adj e.1 e.2 ∧ p e.1 = a ∧ p e.2 = b}

private abbrev Expanded (I : Type) :=
  P × ((I → W) × Option (Line (Fiber G p a b) I))

private abbrev Inside (a b r : P) : Prop := r = a ∨ r = b

/-- A vertex in one of the two distinguished parts is represented by a word.
The other vertices are also marked with the line that supplied their copy. -/
private noncomputable def place {I : Type} (l : Line (Fiber G p a b) I) (x : W) :
    Expanded G p a b I := by
  classical
  exact (p x, (fun i =>
    match l.idxFun i with
    | none => x
    | some e => if p x = a then e.val.1 else if p x = b then e.val.2 else x),
    if Inside a b (p x) then none else some l)

private lemma place_at {I : Type} (l : Line (Fiber G p a b) I) {i : I}
    (hi : l.idxFun i = none) (x : W) :
    (place G p a b l x).2.1 i = x := by
  simp [place, hi]

private lemma place_injective {I : Type} (l : Line (Fiber G p a b) I) :
    Function.Injective (place G p a b l) := by
  intro x y h
  obtain ⟨i, hi⟩ := l.proper
  have he := congrArg (fun v : Expanded G p a b I => v.2.1 i) h
  simpa only [place_at G p a b l hi] using he

private lemma place_outside {I : Type} (l m : Line (Fiber G p a b) I) {x y : W}
    (hxy : place G p a b l x = place G p a b m y) (hx : ¬ Inside a b (p x)) :
    l = m := by
  classical
  have hp : p x = p y := congrArg Prod.fst hxy
  have hy : ¬ Inside a b (p y) := hp ▸ hx
  have htag := congrArg (fun v : Expanded G p a b I => v.2.2) hxy
  simpa [place, hx, hy] using htag

private lemma place_left {I : Type} (l : Line (Fiber G p a b) I)
    (e : Fiber G p a b) :
    place G p a b l e.val.1 = (a, (fun i => (l e i).val.1), none) := by
  classical
  apply Prod.ext e.property.2.1
  apply Prod.ext
  · funext i
    cases hi : l.idxFun i <;> simp [place, hi, e.property.2.1]
  · simp [place, Inside, e.property.2.1]

private lemma place_right {I : Type} (l : Line (Fiber G p a b) I)
    (e : Fiber G p a b) (hab : a ≠ b) :
    place G p a b l e.val.2 = (b, (fun i => (l e i).val.2), none) := by
  classical
  apply Prod.ext e.property.2.2
  apply Prod.ext
  · funext i
    cases hi : l.idxFun i <;> simp [place, hi, e.property.2.2, hab.symm]
  · simp [place, Inside, e.property.2.2]

/-- Edges are supplied by copies indexed by the combinatorial lines. -/
private noncomputable def expand {I : Type} (hp : Parted G p) :
    SimpleGraph (Expanded G p a b I) where
  Adj u v := ∃ (l : Line (Fiber G p a b) I) (x y : W),
    G.Adj x y ∧ u = place G p a b l x ∧ v = place G p a b l y
  symm := ⟨fun _ _ ⟨l, x, y, h, hu, hv⟩ => ⟨l, y, x, h.symm, hv, hu⟩⟩
  loopless := ⟨fun _ ⟨_, _, _, h, hu, hv⟩ =>
    hp h (congrArg Prod.fst (hu.symm.trans hv))⟩

private lemma expand_parted {I : Type} (hp : Parted G p) :
    Parted (expand G p a b (I := I) hp) Prod.fst := by
  intro u v h
  rcases h with ⟨l, x, y, hxy, rfl, rfl⟩
  exact hp hxy

/-- Every edge between the distinguished parts is visible at every coordinate. -/
private lemma inside_edge_at {I : Type} {hp : Parted G p}
    {u v : Expanded G p a b I} (h : (expand G p a b hp).Adj u v)
    (hu : Inside a b u.1) (hv : Inside a b v.1) (i : I) :
    G.Adj (u.2.1 i) (v.2.1 i) := by
  classical
  obtain ⟨l, x, y, hxy, rfl, rfl⟩ := h
  change Inside a b (p x) at hu
  change Inside a b (p y) at hv
  have hne := hp hxy
  cases hi : l.idxFun i with
  | none => simpa [place, hi] using hxy
  | some e =>
    rcases hu with hx | hx <;> rcases hv with hy | hy
    · exact (hne (hx.trans hy.symm)).elim
    · have hab : a ≠ b := fun h => hne (hx.trans (h.trans hy.symm))
      simpa [place, hi, hx, hy, hab.symm] using e.property.1
    · have hba : b ≠ a := fun h => hne (hx.trans (h.trans hy.symm))
      simpa [place, hi, hx, hy, hba] using e.property.1.symm
    · exact (hne (hx.trans hy.symm)).elim

private lemma expand_free {I : Type} (hp : Parted G p)
    (hfree : (completeGraph (Fin 4)).Free G) :
    (completeGraph (Fin 4)).Free (expand G p a b (I := I) hp) := by
  classical
  rintro ⟨f⟩
  have hadj : ∀ ⦃j k : Fin 4⦄, j ≠ k → (expand G p a b hp).Adj (f j) (f k) := by
    intro j k h
    exact f.toHom.map_rel h
  have hp' := expand_parted G p a b (I := I) hp
  have hout : ∃ k : Fin 4, ¬ Inside a b (f k).1 := by
    by_contra h
    have hall (t : Fin 4) : Inside a b (f t).1 := by
      by_contra ht
      exact h ⟨t, ht⟩
    have h01 := hp' (hadj (show (0 : Fin 4) ≠ 1 by decide))
    have h02 := hp' (hadj (show (0 : Fin 4) ≠ 2 by decide))
    have h12 := hp' (hadj (show (1 : Fin 4) ≠ 2 by decide))
    rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;>
      rcases hall 2 with h2 | h2
    all_goals first
      | exact h01 (h0.trans h1.symm)
      | exact h02 (h0.trans h2.symm)
      | exact h12 (h1.trans h2.symm)
  obtain ⟨k, hk⟩ := hout
  obtain ⟨j, hj⟩ := exists_ne k
  obtain ⟨l, x, y, _, hx, _⟩ := hadj hj.symm
  have hxout : ¬ Inside a b (p x) := by
    rw [hx] at hk
    exact hk
  have hcover : ∀ t : Fin 4, ∃ z, f t = place G p a b l z := by
    intro t
    by_cases ht : k = t
    · subst t
      exact ⟨x, hx⟩
    · obtain ⟨m, u, v, _, hu, hv⟩ := hadj ht
      have hlm := place_outside G p a b l m (hx.symm.trans hu) hxout
      exact ⟨v, by simpa only [hlm] using hv⟩
  obtain ⟨i, hi⟩ := l.proper
  apply hfree
  apply copy_of_adj (fun t => (f t).2.1 i)
  intro r s hrs
  have project_outside : ∀ (j k : Fin 4), j ≠ k → ¬ Inside a b (f j).1 →
      G.Adj ((f j).2.1 i) ((f k).2.1 i) := by
    intro j k hjk hjout
    obtain ⟨z, hz⟩ := hcover j
    obtain ⟨m, u, v, huv, hu, hv⟩ := hadj hjk
    have hzout : ¬ Inside a b (p z) := by
      rw [hz] at hjout
      exact hjout
    have hlm := place_outside G p a b l m (hz.symm.trans hu) hzout
    subst m
    simpa only [hu, hv, place_at G p a b l hi] using huv
  by_cases hr : Inside a b (f r).1
  · by_cases hs : Inside a b (f s).1
    · exact inside_edge_at G p a b (hadj hrs) hr hs i
    · exact (project_outside s r hrs.symm hs).symm
  · exact project_outside r s hrs hr

end Expansion

/-- One enlargement makes the edges of a prescribed ordered pair of parts
monochromatic on some copy, with respect to any coloring of the enlargement. -/
private lemma enlarge {P W K : Type} [Finite P] [Finite W] [Finite K]
    (fallback : K) (G : SimpleGraph W) (p : W → P) (hp : Parted G p)
    (hfree : (completeGraph (Fin 4)).Free G) (a b : P) :
    ∃ (V : Type) (_ : Finite V) (H : SimpleGraph V) (q : V → P),
      Parted H q ∧ (completeGraph (Fin 4)).Free H ∧
      ∀ d : V → V → K, ∃ (f : W ↪ V) (c : K),
        (∀ x, q (f x) = p x) ∧
        (∀ x y, G.Adj x y → H.Adj (f x) (f y)) ∧
        (∀ x y, G.Adj x y → p x = a → p y = b → d (f x) (f y) = c) := by
  classical
  by_cases hab : a = b
  · refine ⟨W, inferInstance, G, p, hp, hfree, fun _ => ⟨Function.Embedding.refl W, fallback, ?_, ?_, ?_⟩⟩
    · intro x
      rfl
    · intro x y h
      exact h
    · intro x y h hx hy
      exact (hp h (hx.trans (hab.trans hy.symm))).elim
  obtain ⟨I, hI, hj⟩ := Line.exists_mono_in_high_dimension (Fiber G p a b) K
  letI : Fintype I := hI
  let E := Fiber G p a b
  letI : Finite (Line E I) := Finite.of_injective Line.idxFun (by
    intro l m h
    cases l
    cases m
    cases h
    rfl)
  let V := Expanded G p a b I
  let H : SimpleGraph V := expand G p a b hp
  refine ⟨V, inferInstance, H, Prod.fst, expand_parted G p a b (I := I) hp,
    expand_free G p a b (I := I) hp hfree, ?_⟩
  intro d
  let left : (I → E) → V := fun w => (a, (fun i => (w i).val.1), none)
  let right : (I → E) → V := fun w => (b, (fun i => (w i).val.2), none)
  obtain ⟨l, hl⟩ := hj (fun w => d (left w) (right w))
  obtain ⟨c, hc⟩ :
      ∃ c : K, ∀ e : E, d (left (l e)) (right (l e)) = c := hl
  let f : W ↪ V := ⟨place G p a b l, place_injective G p a b l⟩
  refine ⟨f, c, fun _ => rfl, ?_, ?_⟩
  · intro x y hxy
    exact ⟨l, x, y, hxy, rfl, rfl⟩
  · intro x y hxy hx hy
    let e : E := ⟨(x, y), hxy, hx, hy⟩
    have hl : place G p a b l x = left (l e) := place_left G p a b l e
    have hr : place G p a b l y = right (l e) := place_right G p a b l e hab
    change d (place G p a b l x) (place G p a b l y) = c
    rw [hl, hr]
    exact hc e

/-- Compose the copy maps backwards through a finite list of enlargements. -/
private lemma homogenize {P W K : Type} [Finite P] [Finite W] [Finite K]
    (fallback : K) (G : SimpleGraph W) (p : W → P) (hp : Parted G p)
    (hfree : (completeGraph (Fin 4)).Free G) (s : Finset (P × P)) :
    ∃ (V : Type) (_ : Finite V) (H : SimpleGraph V) (q : V → P),
      Parted H q ∧ (completeGraph (Fin 4)).Free H ∧
      ∀ d : V → V → K, ∃ (f : W ↪ V) (c : P × P → K),
        (∀ x, q (f x) = p x) ∧
        (∀ x y, G.Adj x y → H.Adj (f x) (f y)) ∧
        (∀ x y, G.Adj x y → (p x, p y) ∈ s → d (f x) (f y) = c (p x, p y)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨W, inferInstance, G, p, hp, hfree, fun _ => ⟨Function.Embedding.refl W, fun _ => fallback, ?_, ?_, ?_⟩⟩
    · intro x
      rfl
    · intro x y h
      exact h
    · intro x y _ hm
      exact (Finset.notMem_empty _ hm).elim
  | @insert e s _ ih =>
    obtain ⟨U, hU, J, r, hJp, hJfree, pull⟩ := ih
    letI : Finite U := hU
    obtain ⟨V, hV, H, q, hHp, hHfree, one⟩ :=
      enlarge fallback J r hJp hJfree e.1 e.2
    refine ⟨V, hV, H, q, hHp, hHfree, ?_⟩
    intro d
    obtain ⟨g, ce, hg, hge, hmono⟩ := one d
    obtain ⟨f, c, hf, hfe, hpull⟩ := pull (fun x y => d (g x) (g y))
    refine ⟨f.trans g, fun z => if z = e then ce else c z,
      fun x => (hg (f x)).trans (hf x), fun x y h => hge _ _ (hfe x y h), ?_⟩
    intro x y hxy hm
    change d (g (f x)) (g (f y)) = (if (p x, p y) = e then ce else c (p x, p y))
    by_cases he : (p x, p y) = e
    · have hxa : p x = e.1 := congrArg Prod.fst he
      have hyb : p y = e.2 := congrArg Prod.snd he
      simpa only [if_pos he] using
        hmono (f x) (f y) (hfe x y hxy) ((hf x).trans hxa) ((hf y).trans hyb)
    · have hmem : (p x, p y) ∈ s := (Finset.mem_insert.mp hm).resolve_left he
      simpa only [if_neg he] using hpull x y hxy hmem

/-- Initially each triple of parts carries a separate triangle. -/
private abbrev Start (P : Type) :=
  {v : Finset P × P // v.1.card = 3 ∧ v.2 ∈ v.1}

private def startGraph (P : Type) : SimpleGraph (Start P) where
  Adj x y := x.val.1 = y.val.1 ∧ x.val.2 ≠ y.val.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private lemma start_free (P : Type) : (completeGraph (Fin 4)).Free (startGraph P) := by
  classical
  rintro ⟨f⟩
  let s : Finset P := (f 0).val.1
  have he : ∀ k : Fin 4, (f k).val.1 = s := by
    intro k
    by_cases hk : k = 0
    · subst k
      rfl
    · have h : (startGraph P).Adj (f k) (f 0) := f.toHom.map_rel hk
      exact h.1
  let g : Fin 4 → s := fun k => ⟨(f k).val.2, he k ▸ (f k).property.2⟩
  have hg : Function.Injective g := by
    intro i j h
    by_contra hij
    have hadj : (startGraph P).Adj (f i) (f j) := f.toHom.map_rel hij
    exact hadj.2 (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective g hg
  have hs : s.card = 3 := (f 0).property.1
  rw [Fintype.card_fin, Fintype.card_coe, hs] at hcard
  omega

private lemma start_triangle {P : Type} {x y z : P} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    ∃ u v w : Start P, u.val.2 = x ∧ v.val.2 = y ∧ w.val.2 = z ∧
      (startGraph P).Adj u v ∧ (startGraph P).Adj u w ∧ (startGraph P).Adj v w := by
  classical
  let s : Finset P := {x, y, z}
  have hx : x ∉ ({y, z} : Finset P) := by simp [hxy, hxz]
  have hy : y ∉ ({z} : Finset P) := by simpa using hyz
  have hs : s.card = 3 := by
    change (insert x (insert y ({z} : Finset P))).card = 3
    rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy, Finset.card_singleton]
  let u : Start P := ⟨(s, x), hs, by simp [s]⟩
  let v : Start P := ⟨(s, y), hs, by simp [s]⟩
  let w : Start P := ⟨(s, z), hs, by simp [s]⟩
  exact ⟨u, v, w, rfl, rfl, rfl, ⟨rfl, hxy⟩, ⟨rfl, hxz⟩, ⟨rfl, hyz⟩⟩

theorem finite_triangle_folkman :
    HasFiniteRamseyProperty (completeGraph (Fin 4)) (completeGraph (Fin 3)) := by
  classical
  intro n hn
  let P := Fin (threshold n n)
  let p : Start P → P := fun v => v.val.2
  let fallback : Fin n := ⟨0, hn⟩
  have hp : Parted (startGraph P) p := by
    intro u v h
    exact h.2
  -- Both orientations are processed so the coloring used in the iteration can
  -- be any total function on ordered vertex pairs.
  obtain ⟨V, _, H, q, _, hfree, pull⟩ :=
    homogenize fallback (startGraph P) p hp (start_free P) (Finset.univ : Finset (P × P))
  refine ⟨V, H, hfree, ?_⟩
  intro C hC
  have cover : ∀ x y, H.Adj x y → ∃ i, (C i).Adj x y := by
    intro x y h
    rw [hC.1, iSup_adj] at h
    exact h
  let d : V → V → Fin n := fun x y =>
    if h : H.Adj x y then (cover x y h).choose else fallback
  have hd : ∀ x y, H.Adj x y → (C (d x y)).Adj x y := by
    intro x y h
    simpa only [d, dif_pos h] using (cover x y h).choose_spec
  obtain ⟨f, c, _, hf, hc⟩ := pull d
  have hsize : threshold n n ≤ (Finset.univ : Finset P).card := by simp [P]
  have hcolors : (Finset.univ : Finset (Fin n)).card ≤ n := by simp
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz, hxyyz⟩ :=
    ramsey_on_finset hn (fun x y => c (x, y)) n Finset.univ Finset.univ hsize hcolors
      (fun _ _ _ _ _ => Finset.mem_univ _)
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := start_triangle hxy hxz hyz
  have huv' : d (f u) (f v) = c (x, y) := by
    simpa only [p, hu, hv] using hc u v huv (Finset.mem_univ _)
  have huw' : d (f u) (f w) = c (x, y) := by
    have h := hc u w huw (Finset.mem_univ _)
    simpa only [p, hu, hw, ← hxyz] using h
  have hvw' : d (f v) (f w) = c (x, y) := by
    have h := hc v w hvw (Finset.mem_univ _)
    simpa only [p, hv, hw, ← hxyyz] using h
  refine ⟨c (x, y), triangle_of_adj (x := f u) (y := f v) (z := f w) ?_ ?_ ?_⟩
  · simpa only [huv'] using hd (f u) (f v) (hf u v huv)
  · simpa only [huw'] using hd (f u) (f w) (hf u w huw)
  · simpa only [hvw'] using hd (f v) (f w) (hf v w hvw)

end FolkmanTrianglePartite

theorem OMA.solution : OMA.R_Erdos596_erdos_596_variants_K4_K3_exceptional_iff_R1.H1 :=
  FolkmanTrianglePartite.finite_triangle_folkman
