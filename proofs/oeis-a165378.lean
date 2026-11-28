import OMAStatements.S_oeis_a165378
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Problem: A165378, connected colorings of slanted arrays of width four.
-- Source: https://oeis.org/A165378
-- Statement credit: @Haruzame0
-- Frontier connectivity, completed-color flags, and degrees give an exact
-- finite automaton for the stated arrays. Kernel-checked transfer identities
-- then give the quadratic formula for every number of rows greater than three.

-- Component: A165378Glue

namespace A165378Glue

open Relation

universe u v w
variable {α : Type u} {β : Type v} {F : Type w}

/-- Extend an old graph by new vertices, with cross edges confined to the old frontier. -/
def joined (r : α → α → Prop) (ι : F → α) (c : F → β → Prop)
    (s : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
  | .inl x, .inl y => r x y
  | .inl x, .inr y => ∃ i, x = ι i ∧ c i y
  | .inr x, .inl y => ∃ i, y = ι i ∧ c i x
  | .inr x, .inr y => s x y

/-- Compress the old graph to its reachability relation on the frontier. -/
def compressed (r : α → α → Prop) (ι : F → α) (c : F → β → Prop)
    (s : β → β → Prop) : F ⊕ β → F ⊕ β → Prop
  | .inl i, .inl j => ReflTransGen r (ι i) (ι j)
  | .inl i, .inr y => c i y
  | .inr x, .inl j => c j x
  | .inr x, .inr y => s x y

def expose (ι : F → α) : F ⊕ β → α ⊕ β := Sum.map ι id

variable (r : α → α → Prop) (ι : F → α) (c : F → β → Prop)
    (s : β → β → Prop)

theorem old_path {x y : α} (h : ReflTransGen r x y) :
    ReflTransGen (joined r ι c s) (.inl x) (.inl y) :=
  h.lift Sum.inl (fun _ _ h => h)

theorem compressed_step {x y : F ⊕ β} (h : compressed r ι c s x y) :
    ReflTransGen (joined r ι c s) (expose ι x) (expose ι y) := by
  cases x with
  | inl i =>
    cases y with
    | inl j => exact old_path r ι c s h
    | inr y => exact .single ⟨i, rfl, h⟩
  | inr x =>
    cases y with
    | inl j => exact .single ⟨j, rfl, h⟩
    | inr y => exact .single h

private def Lifted (a : F ⊕ β) : α ⊕ β → Prop
  | .inl x => ∃ i, ReflTransGen (compressed r ι c s) a (.inl i) ∧
      ReflTransGen r (ι i) x
  | .inr y => ReflTransGen (compressed r ι c s) a (.inr y)

private theorem lifted_initial (a : F ⊕ β) : Lifted r ι c s a (expose ι a) := by
  cases a with
  | inl i => exact ⟨i, .refl, .refl⟩
  | inr y => exact .refl

private theorem lifted_step (a : F ⊕ β) {x y : α ⊕ β}
    (hx : Lifted r ι c s a x) (hxy : joined r ι c s x y) :
    Lifted r ι c s a y := by
  cases x with
  | inl x =>
    obtain ⟨i, hi, hix⟩ := hx
    cases y with
    | inl y => exact ⟨i, hi, hix.tail hxy⟩
    | inr y =>
      obtain ⟨j, rfl, hj⟩ := hxy
      have hij : compressed r ι c s (.inl i) (.inl j) := hix
      exact (hi.tail hij).tail hj
  | inr x =>
    cases y with
    | inl y =>
      obtain ⟨j, rfl, hj⟩ := hxy
      exact ⟨j, hx.tail hj, .refl⟩
    | inr y => exact hx.tail hxy

/-- Paths between exposed vertices are completely determined by the old frontier relation. -/
theorem reach_expose_iff (a b : F ⊕ β) :
    ReflTransGen (joined r ι c s) (expose ι a) (expose ι b) ↔
      ReflTransGen (compressed r ι c s) a b := by
  constructor
  · intro h
    have hb : Lifted r ι c s a (expose ι b) := by
      have aux : ∀ z, ReflTransGen (joined r ι c s) (expose ι a) z →
          Lifted r ι c s a z := by
        intro z hz
        induction hz with
        | refl => exact lifted_initial r ι c s a
        | tail _ hxy ih => exact lifted_step r ι c s a ih hxy
      exact aux _ h
    cases b with
    | inl j =>
      obtain ⟨i, hi, hij⟩ := hb
      exact hi.tail hij
    | inr y => exact hb
  · intro h
    exact h.lift' (expose ι) (fun _ _ h => compressed_step r ι c s h)

/-- An old component missing the frontier cannot acquire any new vertices or connections. -/
theorem closed_component {x : α} (hx : ∀ i, ¬ ReflTransGen r x (ι i))
    {z : α ⊕ β} (h : ReflTransGen (joined r ι c s) (.inl x) z) :
    ∃ y, z = .inl y ∧ ReflTransGen r x y := by
  induction h with
  | refl => exact ⟨x, rfl, .refl⟩
  | @tail b z h hz ih =>
    obtain ⟨y, rfl, hxy⟩ := ih
    cases z with
    | inl z => exact ⟨z, rfl, hxy.tail hz⟩
    | inr z =>
      obtain ⟨i, hy, _⟩ := hz
      exact (hx i (hy ▸ hxy)).elim

theorem closed_old_iff {x y : α} (hx : ∀ i, ¬ ReflTransGen r x (ι i)) :
    ReflTransGen (joined r ι c s) (.inl x) (.inl y) ↔ ReflTransGen r x y := by
  constructor
  · intro h
    obtain ⟨z, hz, hxz⟩ := closed_component r ι c s hx h
    cases Sum.inl.inj hz
    exact hxz
  · exact old_path r ι c s

theorem closed_not_new {x : α} (hx : ∀ i, ¬ ReflTransGen r x (ι i)) (y : β) :
    ¬ ReflTransGen (joined r ι c s) (.inl x) (.inr y) := by
  intro h
  obtain ⟨z, hz, _⟩ := closed_component r ι c s hx h
  cases hz

theorem reverse_path (hr : ∀ x y, r x y → r y x) {x y : α}
    (h : ReflTransGen r x y) : ReflTransGen r y x := by
  induction h with
  | refl => exact .refl
  | @tail b z h hz ih => exact ih.head (hr b z hz)

/-- Any old vertex connected to a frontier representative has the same new connections. -/
theorem old_new_iff_of_representative (hr : ∀ x y, r x y → r y x)
    {x : α} {i : F} (hxi : ReflTransGen r x (ι i)) (y : β) :
    ReflTransGen (joined r ι c s) (.inl x) (.inr y) ↔
      ReflTransGen (compressed r ι c s) (.inl i) (.inr y) := by
  constructor
  · intro h
    apply (reach_expose_iff r ι c s (.inl i) (.inr y)).mp
    exact (old_path r ι c s (reverse_path r hr hxi)).trans h
  · intro h
    exact (old_path r ι c s hxi).trans
      ((reach_expose_iff r ι c s (.inl i) (.inr y)).mpr h)

/-- An old component meets the new row exactly when a frontier representative reaches it. -/
theorem old_new_iff (hr : ∀ x y, r x y → r y x) (x : α) (y : β) :
    ReflTransGen (joined r ι c s) (.inl x) (.inr y) ↔
      ∃ i, ReflTransGen r x (ι i) ∧
        ReflTransGen (compressed r ι c s) (.inl i) (.inr y) := by
  classical
  constructor
  · intro h
    have hi : ∃ i, ReflTransGen r x (ι i) := by
      by_contra hn
      exact closed_not_new r ι c s (fun i h => hn ⟨i, h⟩) y h
    obtain ⟨i, hi⟩ := hi
    exact ⟨i, hi, (old_new_iff_of_representative r ι c s hr hi y).mp h⟩
  · rintro ⟨i, hi, hiy⟩
    exact (old_new_iff_of_representative r ι c s hr hi y).mpr hiy

theorem disappears_iff (i : F) :
    (∀ y : β, ¬ ReflTransGen (joined r ι c s) (.inl (ι i)) (.inr y)) ↔
      ∀ y : β, ¬ ReflTransGen (compressed r ι c s) (.inl i) (.inr y) := by
  simp only [← reach_expose_iff r ι c s, expose, Sum.map_inl, Sum.map_inr, id_eq]

end A165378Glue

-- Component: A165378Invariant

namespace A165378Invariant
open Relation A165378Glue
universe u v w z
variable {α : Type u} {β : Type v} {F : Type w} {Color : Type z}

def Closed (r : α → α → Prop) (ι : F → α) (x : α) : Prop :=
  ∀ i, ¬ ReflTransGen r x (ι i)
def Good (r : α → α → Prop) (col : α → Color) (ι : F → α) : Prop :=
  ∀ x, Closed r ι x → ∀ y, col y = col x → ReflTransGen r x y
def Done (r : α → α → Prop) (col : α → Color) (ι : F → α) (v : Color) : Prop :=
  ∃ x, col x = v ∧ Closed r ι x

variable (r : α → α → Prop) (ι : F → α) (c : F → β → Prop)
    (s : β → β → Prop) (col : α → Color) (row : β → Color)

def Lost (i : F) : Prop :=
  ∀ j, ¬ ReflTransGen (compressed r ι c s) (.inl i) (.inr j)

theorem path_color (hcol : ∀ x y, r x y → col x = col y) {x y : α}
    (h : ReflTransGen r x y) : col x = col y := by
  induction h with
  | refl => rfl
  | @tail b z h hz ih => exact ih.trans (hcol b z hz)

theorem closed_or_represented (x : α) :
    Closed r ι x ∨ ∃ i, ReflTransGen r x (ι i) := by
  classical
  by_cases hx : Closed r ι x
  · exact Or.inl hx
  · right
    by_contra hn
    exact hx (fun i hi => hn ⟨i, hi⟩)

theorem closed_old (x : α) (hx : Closed r ι x) :
    Closed (joined r ι c s) Sum.inr (.inl x) :=
  fun j => closed_not_new r ι c s hx j

theorem closed_representative (hr : ∀ x y, r x y → r y x)
    {x : α} {i : F} (hxi : ReflTransGen r x (ι i)) :
    Closed (joined r ι c s) Sum.inr (.inl x) ↔ Lost r ι c s i := by
  unfold Closed Lost
  exact forall_congr' fun j => not_congr (old_new_iff_of_representative r ι c s hr hxi j)

theorem done_joined_iff (hr : ∀ x y, r x y → r y x)
    (hcol : ∀ x y, r x y → col x = col y) (v : Color) :
    Done (joined r ι c s) (Sum.elim col row) Sum.inr v ↔
      Done r col ι v ∨ ∃ i, col (ι i) = v ∧ Lost r ι c s i := by
  constructor
  · rintro ⟨x, hc, hx⟩
    cases x with
    | inr j => exact (hx j .refl).elim
    | inl x =>
      rcases closed_or_represented r ι x with hxold | ⟨i, hi⟩
      · exact Or.inl ⟨x, hc, hxold⟩
      · exact Or.inr ⟨i, (path_color r col hcol hi).symm.trans hc,
          (closed_representative r ι c s hr hi).mp hx⟩
  · rintro (⟨x, hc, hx⟩ | ⟨i, hc, hi⟩)
    · exact ⟨.inl x, hc, closed_old r ι c s x hx⟩
    · exact ⟨.inl (ι i), hc,
        (closed_representative r ι c s hr (ReflTransGen.refl (a := ι i))).mpr hi⟩

theorem good_joined_iff (hr : ∀ x y, r x y → r y x)
    (hcol : ∀ x y, r x y → col x = col y) (hg : Good r col ι) :
    Good (joined r ι c s) (Sum.elim col row) Sum.inr ↔
      (∀ v, Done r col ι v → ∀ j, row j ≠ v) ∧
      (∀ i, Lost r ι c s i → ∀ z : F ⊕ β,
        Sum.elim (col ∘ ι) row z = col (ι i) →
          ReflTransGen (compressed r ι c s) (.inl i) z) := by
  constructor
  · intro hgood
    constructor
    · rintro v ⟨x, hc, hx⟩ j hj
      have hclosed := closed_old r ι c s x hx
      have hp := hgood (.inl x) hclosed (.inr j) (hj.trans hc.symm)
      exact hclosed j hp
    · intro i hi z hz
      have hclosed : Closed (joined r ι c s) Sum.inr (.inl (ι i)) :=
        (closed_representative r ι c s hr (ReflTransGen.refl (a := ι i))).mpr hi
      have hc : Sum.elim col row (expose ι z) = col (ι i) := by
        cases z <;> exact hz
      exact (reach_expose_iff r ι c s (.inl i) z).mp
        (hgood (.inl (ι i)) hclosed (expose ι z) hc)
  · rintro ⟨havoid, hfront⟩ x hx y hxy
    cases x with
    | inr j => exact (hx j .refl).elim
    | inl x =>
      rcases closed_or_represented r ι x with hxold | ⟨i, hi⟩
      · cases y with
        | inl y => exact old_path r ι c s (hg x hxold y hxy)
        | inr j => exact (havoid (col x) ⟨x, rfl, hxold⟩ j hxy).elim
      · have hlost : Lost r ι c s i := (closed_representative r ι c s hr hi).mp hx
        have hcxi : col x = col (ι i) := path_color r col hcol hi
        cases y with
        | inr j =>
          have hp := hfront i hlost (.inr j) (hxy.trans hcxi)
          exact (hlost j hp).elim
        | inl y =>
          rcases closed_or_represented r ι y with hyold | ⟨j, hj⟩
          · have hyx := hg y hyold x hxy.symm
            exact (hyold i (hyx.trans hi)).elim
          · have hcyj : col y = col (ι j) := path_color r col hcol hj
            have hp := hfront i hlost (.inl j) (hcyj.symm.trans (hxy.trans hcxi))
            exact (old_path r ι c s hi).trans
              (((reach_expose_iff r ι c s (.inl i) (.inl j)).mpr hp).trans
                (old_path r ι c s (reverse_path r hr hj)))

theorem not_closed_of_surjective (hι : Function.Surjective ι) (x : α) : ¬ Closed r ι x := by
  obtain ⟨i, rfl⟩ := hι x
  exact fun h => h i .refl

theorem good_of_surjective (hι : Function.Surjective ι) : Good r col ι :=
  fun x hx => (not_closed_of_surjective r ι hι x hx).elim

theorem not_done_of_surjective (hι : Function.Surjective ι) (v : Color) : ¬ Done r col ι v := by
  rintro ⟨x, _, hx⟩
  exact not_closed_of_surjective r ι hι x hx

theorem connected_iff (hr : ∀ x y, r x y → r y x)
    (hcol : ∀ x y, r x y → col x = col y) (hg : Good r col ι)
    (v : Color) (hocc : ∃ x, col x = v) :
    (∀ x y, col x = v → col y = v → ReflTransGen r x y) ↔
      (Done r col ι v ∧ ∀ i, col (ι i) ≠ v) ∨
      (¬ Done r col ι v ∧ ∃ j, col (ι j) = v ∧
        ∀ i, col (ι i) = v → ReflTransGen r (ι i) (ι j)) := by
  classical
  constructor
  · intro hconn
    by_cases hd : Done r col ι v
    · left
      refine ⟨hd, ?_⟩
      obtain ⟨x, hx, hc⟩ := hd
      exact fun i hi => hc i (hconn x (ι i) hx hi)
    · right
      refine ⟨hd, ?_⟩
      obtain ⟨x, hx⟩ := hocc
      rcases closed_or_represented r ι x with hc | ⟨j, hj⟩
      · exact (hd ⟨x, hx, hc⟩).elim
      · have hjc : col (ι j) = v := (path_color r col hcol hj).symm.trans hx
        exact ⟨j, hjc, fun i hi => hconn (ι i) (ι j) hi hjc⟩
  · rintro (⟨⟨x, hx, hc⟩, _⟩ | ⟨hd, j, hj, hf⟩)
    · intro y z hy hz
      exact (reverse_path r hr (hg x hc y (hy.trans hx.symm))).trans
        (hg x hc z (hz.trans hx.symm))
    · have hall : ∀ x, col x = v → ReflTransGen r x (ι j) := by
        intro x hx
        rcases closed_or_represented r ι x with hc | ⟨i, hi⟩
        · exact (hd ⟨x, hx, hc⟩).elim
        · exact hi.trans (hf i ((path_color r col hcol hi).symm.trans hx))
      exact fun x y hx hy => (hall x hx).trans (reverse_path r hr (hall y hy))

end A165378Invariant

-- Component: A165378Board

namespace A165378Board

open OMA.S_oeis_a165378 Relation

def oldCell {n : ℕ} (p : Cell n) : Cell (n + 1) := (p.1.castSucc, p.2)

def newCell (n : ℕ) (j : Fin 4) : Cell (n + 1) := (Fin.last n, j)

def cellEquiv (n : ℕ) : Cell n ⊕ Fin 4 ≃ Cell (n + 1) where
  toFun := Sum.elim oldCell (newCell n)
  invFun := fun p => if h : p.1.val < n then .inl (⟨p.1.val, h⟩, p.2) else .inr p.2
  left_inv := by
    intro p
    cases p with
    | inl p => simp [oldCell, p.1.isLt]
    | inr j => simp [newCell]
  right_inv := by
    intro p
    dsimp only
    split_ifs with h
    · rfl
    · apply Prod.ext
      · apply Fin.ext
        have := p.1.isLt
        change n = p.1.val
        omega
      · rfl

@[simp] theorem cellEquiv_old (n : ℕ) (p : Cell n) :
    cellEquiv n (.inl p) = oldCell p := rfl

@[simp] theorem cellEquiv_new (n : ℕ) (j : Fin 4) :
    cellEquiv n (.inr j) = newCell n j := rfl

def append {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4) : Cell (n + 1) → Fin 4 :=
  fun p => Sum.elim f r ((cellEquiv n).symm p)

@[simp] theorem append_old {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4) (p : Cell n) :
    append f r (oldCell p) = f p := by
  change Sum.elim f r ((cellEquiv n).symm (cellEquiv n (.inl p))) = f p
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem append_new {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4) (j : Fin 4) :
    append f r (newCell n j) = r j := by
  change Sum.elim f r ((cellEquiv n).symm (cellEquiv n (.inr j))) = r j
  rw [Equiv.symm_apply_apply]
  rfl

theorem neighbors_reverse {n : ℕ} {p q : Cell n} (h : neighbors p q) : neighbors q p := by
  rcases h with ⟨hrow, hoff⟩ | h | h
  · exact Or.inl ⟨hrow.symm, hoff.symm⟩
  · exact Or.inr (Or.inr ⟨h.1, h.2.symm⟩)
  · exact Or.inr (Or.inl ⟨h.1, h.2.symm⟩)

theorem sameAdj_reverse {n : ℕ} {f : Cell n → Fin 4} {p q : Cell n}
    (h : sameAdj f p q) : sameAdj f q p :=
  ⟨neighbors_reverse h.1, h.2.symm⟩

theorem sameAdj_comm {n : ℕ} (f : Cell n → Fin 4) (p q : Cell n) :
    sameAdj f p q ↔ sameAdj f q p := ⟨sameAdj_reverse, sameAdj_reverse⟩

@[simp] theorem neighbors_old_old {n : ℕ} (p q : Cell n) :
    neighbors (oldCell p) (oldCell q) ↔ neighbors p q := by
  simp only [neighbors, absCol, oldCell, Fin.castSucc_inj, Fin.val_castSucc]

@[simp] theorem neighbors_old_new {n : ℕ} (p : Cell n) (j : Fin 4) :
    neighbors (oldCell p) (newCell n j) ↔ p.1.val + 1 = n ∧ p.2.val = j.val + 1 := by
  have := p.1.isLt
  simp only [neighbors, absCol, oldCell, newCell, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_last]
  omega

@[simp] theorem neighbors_new_old {n : ℕ} (j : Fin 4) (p : Cell n) :
    neighbors (newCell n j) (oldCell p) ↔ p.1.val + 1 = n ∧ p.2.val = j.val + 1 :=
  (show neighbors (newCell n j) (oldCell p) ↔ neighbors (oldCell p) (newCell n j) from
    ⟨neighbors_reverse, neighbors_reverse⟩).trans (neighbors_old_new p j)

@[simp] theorem neighbors_new_new (n : ℕ) (i j : Fin 4) :
    neighbors (newCell n i) (newCell n j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp [neighbors, absCol, newCell]

@[simp] theorem sameAdj_old_old {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4)
    (p q : Cell n) : sameAdj (append f r) (oldCell p) (oldCell q) ↔ sameAdj f p q := by
  simp only [sameAdj, neighbors_old_old, append_old]

@[simp] theorem sameAdj_old_new {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4)
    (p : Cell n) (j : Fin 4) :
    sameAdj (append f r) (oldCell p) (newCell n j) ↔
      (p.1.val + 1 = n ∧ p.2.val = j.val + 1) ∧ f p = r j := by
  simp only [sameAdj, neighbors_old_new, append_old, append_new]

def horizontalRel (r : Fin 4 → Fin 4) (i j : Fin 4) : Prop :=
  (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j

@[simp] theorem sameAdj_new_new {n : ℕ} (f : Cell n → Fin 4) (r : Fin 4 → Fin 4)
    (i j : Fin 4) :
    sameAdj (append f r) (newCell n i) (newCell n j) ↔ horizontalRel r i j := by
  simp only [sameAdj, neighbors_new_new, append_new, horizontalRel]

def cross {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Fin 4 → Fin 4) (i j : Fin 4) : Prop :=
  i.val = j.val + 1 ∧ f (newCell n i) = r j

theorem sameAdj_cross {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Fin 4 → Fin 4)
    (p : Cell (n + 1)) (j : Fin 4) :
    sameAdj (append f r) (oldCell p) (newCell (n + 1) j) ↔
      ∃ i, p = newCell n i ∧ cross f r i j := by
  rw [sameAdj_old_new]
  constructor
  · rintro ⟨⟨hrow, hcol⟩, hc⟩
    have hp : p = newCell n p.2 := by
      apply Prod.ext
      · apply Fin.ext
        simp only [newCell, Fin.val_last]
        omega
      · rfl
    exact ⟨p.2, hp, hcol, hp ▸ hc⟩
  · rintro ⟨i, rfl, h⟩
    exact ⟨⟨rfl, h.1⟩, h.2⟩

/-- The exact board adjacency is the generic gluing relation. -/
theorem sameAdj_joined {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Fin 4 → Fin 4)
    (p q : Cell (n + 1) ⊕ Fin 4) :
    sameAdj (append f r) (cellEquiv (n + 1) p) (cellEquiv (n + 1) q) ↔
      A165378Glue.joined (sameAdj f) (newCell n) (cross f r) (horizontalRel r) p q := by
  cases p with
  | inl p =>
    cases q with
    | inl q => exact sameAdj_old_old f r p q
    | inr j => exact sameAdj_cross f r p j
  | inr i =>
    cases q with
    | inl q =>
      rw [sameAdj_comm]
      exact sameAdj_cross f r q i
    | inr j => exact sameAdj_new_new f r i j

theorem reach_cellEquiv_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Fin 4 → Fin 4)
    (p q : Cell (n + 1) ⊕ Fin 4) :
    ReflTransGen (sameAdj (append f r)) (cellEquiv (n + 1) p) (cellEquiv (n + 1) q) ↔
      ReflTransGen (A165378Glue.joined (sameAdj f) (newCell n) (cross f r)
        (horizontalRel r)) p q := by
  constructor
  · intro h
    have hm : ∀ x y, sameAdj (append f r) x y →
        A165378Glue.joined (sameAdj f) (newCell n) (cross f r) (horizontalRel r)
          ((cellEquiv (n + 1)).symm x) ((cellEquiv (n + 1)).symm y) := by
      intro x y hxy
      apply (sameAdj_joined f r _ _).mp
      simpa only [Equiv.apply_symm_apply] using hxy
    simpa only [Function.onFun, Equiv.symm_apply_apply] using
      h.lift (cellEquiv (n + 1)).symm hm
  · intro h
    exact h.lift (cellEquiv (n + 1)) (fun x y hxy => (sameAdj_joined f r x y).mpr hxy)

theorem reach_exposed_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Fin 4 → Fin 4)
    (p q : Fin 4 ⊕ Fin 4) :
    ReflTransGen (sameAdj (append f r))
      (cellEquiv (n + 1) (A165378Glue.expose (newCell n) p))
      (cellEquiv (n + 1) (A165378Glue.expose (newCell n) q)) ↔
      ReflTransGen (A165378Glue.compressed (sameAdj f) (newCell n) (cross f r)
        (horizontalRel r)) p q :=
  (reach_cellEquiv_iff f r _ _).trans
    (A165378Glue.reach_expose_iff (sameAdj f) (newCell n) (cross f r) (horizontalRel r) p q)

theorem append_eta {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    append (fun p => f (oldCell p)) (fun j => f (newCell n j)) = f := by
  funext p
  obtain ⟨q, rfl⟩ := (cellEquiv n).surjective p
  cases q <;> simp only [cellEquiv_old, cellEquiv_new, append_old, append_new]

end A165378Board

-- Component: A165378Automaton

namespace A165378Proof

abbrev Row := Fin 4 → Fin 4

structure State where
  row : Row
  deg : Fin 4 → ℕ
  part : Fin 4 → ℕ
  done : Fin 4 → Bool
  deriving DecidableEq, Inhabited

def old (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
def new (i : Fin 4) : Fin 8 := ⟨4 + i.val, by omega⟩

def color (s : State) (r : Row) (i : Fin 8) : Fin 4 :=
  if h : i.val < 4 then s.row ⟨i.val, h⟩ else r ⟨i.val - 4, by omega⟩

def initialLabels (s : State) (i : Fin 8) : ℕ :=
  if h : i.val < 4 then s.part ⟨i.val, h⟩ else i.val

/-- Join two classes, retaining an arbitrary representative until normalization. -/
def merge (l : Fin 8 → ℕ) (a b : Fin 8) : Fin 8 → ℕ :=
  fun i => if l i = l b then l a else l i

def join (s : State) (r : Row) (l : Fin 8 → ℕ) (a b : Fin 8) : Fin 8 → ℕ :=
  if color s r a = color s r b then merge l a b else l

/-- The three horizontal edges in the new row and the three edges across the cut. -/
def links (s : State) (r : Row) : Fin 8 → ℕ :=
  let l := initialLabels s
  let l := join s r l 4 5
  let l := join s r l 5 6
  let l := join s r l 6 7
  let l := join s r l 1 4
  let l := join s r l 2 5
  join s r l 3 6

def bit (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

def horizontal (r : Row) : Fin 4 → ℕ :=
  ![bit (r 0 = r 1),
    bit (r 0 = r 1) + bit (r 1 = r 2),
    bit (r 1 = r 2) + bit (r 2 = r 3),
    bit (r 2 = r 3)]

def oldDegrees (s : State) (r : Row) : Fin 4 → ℕ :=
  ![s.deg 0, s.deg 1 + bit (s.row 1 = r 0),
    s.deg 2 + bit (s.row 2 = r 1), s.deg 3 + bit (s.row 3 = r 2)]

def newDegrees (s : State) (r : Row) : Fin 4 → ℕ :=
  ![horizontal r 0 + bit (s.row 1 = r 0),
    horizontal r 1 + bit (s.row 2 = r 1),
    horizontal r 2 + bit (s.row 3 = r 2), horizontal r 3]

/-- Use the first index in each class as its representative. -/
def normalize (l : Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  if l i = l 0 then 0 else if l i = l 1 then 1 else if l i = l 2 then 2 else 3

def lost (s : State) (r : Row) (i : Fin 4) : Prop :=
  ∀ j : Fin 4, links s r (old i) ≠ links s r (new j)

instance (s : State) (r : Row) (i : Fin 4) : Decidable (lost s r i) :=
  inferInstanceAs (Decidable (∀ j : Fin 4, links s r (old i) ≠ links s r (new j)))

def permissible (s : State) (r : Row) : Prop :=
  (∀ j : Fin 4, s.done (r j) = false) ∧
  (∀ j : Fin 4, oldDegrees s r j ≤ 2) ∧
  (∀ j : Fin 4, newDegrees s r j ≤ 2) ∧
  ∀ i : Fin 4, lost s r i → ∀ j : Fin 8,
    color s r j = s.row i → links s r j = links s r (old i)

instance (s : State) (r : Row) : Decidable (permissible s r) :=
  inferInstanceAs (Decidable ((∀ j : Fin 4, s.done (r j) = false) ∧
    (∀ j : Fin 4, oldDegrees s r j ≤ 2) ∧
    (∀ j : Fin 4, newDegrees s r j ≤ 2) ∧
    ∀ i : Fin 4, lost s r i → ∀ j : Fin 8,
      color s r j = s.row i → links s r j = links s r (old i)))

def advance (s : State) (r : Row) : State where
  row := r
  deg := newDegrees s r
  part := normalize (fun i => links s r (new i))
  done := fun c => s.done c || decide (∃ i : Fin 4, s.row i = c ∧ lost s r i)

def step (s : State) (r : Row) : Option State :=
  if permissible s r then some (advance s r) else none

def rowLabels (r : Row) : Fin 4 → ℕ :=
  ![0, if r 0 = r 1 then 0 else 1,
    if r 1 = r 2 then (if r 0 = r 1 then 0 else 1) else 2,
    if r 2 = r 3 then
      (if r 1 = r 2 then (if r 0 = r 1 then 0 else 1) else 2) else 3]

def initial (r : Row) : State where
  row := r
  deg := horizontal r
  part := rowLabels r
  done := fun _ => false

def accepting (s : State) : Prop :=
  s.row 0 = 2 ∧ s.row 3 = 3 ∧ ∀ c : Fin 4,
    (s.done c = true ∧ ∀ j : Fin 4, s.row j ≠ c) ∨
    (s.done c = false ∧ ∃ j : Fin 4, s.row j = c ∧
      ∀ i : Fin 4, s.row i = c → s.part i = s.part j)

instance (s : State) : Decidable (accepting s) :=
  inferInstanceAs (Decidable (s.row 0 = 2 ∧ s.row 3 = 3 ∧ ∀ c : Fin 4,
    (s.done c = true ∧ ∀ j : Fin 4, s.row j ≠ c) ∨
    (s.done c = false ∧ ∃ j : Fin 4, s.row j = c ∧
      ∀ i : Fin 4, s.row i = c → s.part i = s.part j)))

def run : State → List Row → Option State
  | s, [] => some s
  | s, r :: rs => (step s r).bind fun t => run t rs

def Accepted : List Row → Prop
  | [] => False
  | r :: rs => r 0 = 0 ∧ r 3 = 1 ∧ ∃ s, run (initial r) rs = some s ∧ accepting s

lemma normalize_eq_iff (l : Fin 4 → ℕ) (i j : Fin 4) :
    normalize l i = normalize l j ↔ l i = l j := by
  fin_cases i <;> fin_cases j <;> simp only [normalize] <;> split_ifs <;> simp_all <;> omega

lemma merge_eq_iff (l : Fin 8 → ℕ) (a b i j : Fin 8) :
    merge l a b i = merge l a b j ↔
      l i = l j ∨ (l i = l a ∧ l j = l b) ∨ (l i = l b ∧ l j = l a) := by
  simp only [merge]
  split_ifs <;> simp_all <;> aesop

end A165378Proof

-- Component: A165378Degree

namespace A165378Degree

open OMA.S_oeis_a165378 A165378Board A165378Proof
open scoped BigOperators

lemma neighborSame_sum {n : ℕ} (f : Cell n → Fin 4) (c : Cell n) :
    neighborSame f c = ∑ d : Cell n, bit (neighbors c d ∧ f c = f d) := by
  classical
  simp only [neighborSame, Finset.card_eq_sum_ones, Finset.sum_filter, bit]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [eq_comm]

lemma sum_cells {n : ℕ} (g : Cell (n + 1) → ℕ) :
    (∑ c : Cell (n + 1), g c) =
      (∑ c : Cell n, g (oldCell c)) + ∑ j : Fin 4, g (newCell n j) := by
  rw [← (cellEquiv n).sum_comp g, Fintype.sum_sum_type]
  rfl

lemma degree_old_split {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell n) :
    neighborSame (append f r) (oldCell c) = neighborSame f c +
      ∑ j : Fin 4, bit ((c.1.val + 1 = n ∧ c.2.val = j.val + 1) ∧ f c = r j) := by
  classical
  rw [neighborSame_sum, sum_cells, neighborSame_sum]
  simp only [neighbors_old_old, neighbors_old_new, append_old, append_new]

lemma degree_old_interior {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell n)
    (hc : c.1.val + 1 < n) :
    neighborSame (append f r) (oldCell c) = neighborSame f c := by
  rw [degree_old_split]
  simp [bit, Nat.ne_of_lt hc]

lemma degree_old_le {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell n) :
    neighborSame f c ≤ neighborSame (append f r) (oldCell c) := by
  rw [degree_old_split]
  omega

lemma degree_old_frontier {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hr : s.row = fun j => f (newCell n j))
    (hd : s.deg = fun j => neighborSame f (newCell n j)) (i : Fin 4) :
    neighborSame (append f r) (oldCell (newCell n i)) = oldDegrees s r i := by
  classical
  rw [degree_old_split, Fin.sum_univ_four]
  fin_cases i <;>
    simp [oldDegrees, hr, hd, newCell, bit]

lemma horizontal_sum (r : Row) (i : Fin 4) :
    (∑ j : Fin 4, bit ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j)) =
      horizontal r i := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> simp [horizontal, bit, eq_comm, Nat.add_comm] <;>
    split_ifs <;> simp_all

lemma degree_single (r : Row) (i : Fin 4) :
    neighborSame (fun c : Cell 1 => r c.2) (newCell 0 i) = horizontal r i := by
  classical
  rw [neighborSame_sum, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  simpa [neighbors, absCol, newCell, Fin.ext_iff] using horizontal_sum r i

lemma degree_new_split {n : ℕ} (f : Cell n → Fin 4) (r : Row) (i : Fin 4) :
    neighborSame (append f r) (newCell n i) =
      (∑ c : Cell n, bit ((c.1.val + 1 = n ∧ c.2.val = i.val + 1) ∧ r i = f c)) +
        horizontal r i := by
  classical
  rw [neighborSame_sum, sum_cells]
  simp only [neighbors_new_old, neighbors_new_new, append_old, append_new]
  rw [horizontal_sum]

lemma degree_new_frontier {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hr : s.row = fun j => f (newCell n j)) (i : Fin 4) :
    neighborSame (append f r) (newCell (n + 1) i) = newDegrees s r i := by
  classical
  rw [degree_new_split, Fintype.sum_prod_type]
  have hrow : (∑ k : Fin (n + 1), ∑ j : Fin 4,
      bit ((k.val + 1 = n + 1 ∧ j.val = i.val + 1) ∧ r i = f (k, j))) =
      ∑ j : Fin 4, bit (j.val = i.val + 1 ∧ r i = f (newCell n j)) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [newCell, bit]
      split_ifs with h
      · exact (if_pos h).symm
      · exact (if_neg h).symm
    · intro b hb hbn
      have hneq : b.val ≠ n := by
        intro he
        apply hbn
        exact Fin.ext he
      simp [bit, hneq]
    · simp
  rw [hrow, Fin.sum_univ_four]
  fin_cases i <;>
    simp [newDegrees, hr, bit, eq_comm, Nat.add_comm]

lemma degree_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hr : s.row = fun j => f (newCell n j))
    (hd : s.deg = fun j => neighborSame f (newCell n j))
    (hf : ∀ c, neighborSame f c ≤ 2) :
    (∀ c, neighborSame (append f r) c ≤ 2) ↔
      (∀ i, oldDegrees s r i ≤ 2) ∧ (∀ i, newDegrees s r i ≤ 2) := by
  constructor
  · intro h
    constructor
    · intro i
      rw [← degree_old_frontier f r s hr hd]
      exact h _
    · intro i
      rw [← degree_new_frontier f r s hr]
      exact h _
  · rintro ⟨ho, hn⟩ c
    obtain ⟨c, rfl⟩ := (cellEquiv (n + 1)).surjective c
    cases c with
    | inl c =>
      change neighborSame (append f r) (oldCell c) ≤ 2
      by_cases hlast : c.1.val = n
      · have he : c = newCell n c.2 := by
          apply Prod.ext
          · exact Fin.ext hlast
          · rfl
        rw [he, degree_old_frontier f r s hr hd]
        exact ho _
      · rw [degree_old_interior f r c (by have := c.1.isLt; omega)]
        exact hf c
    | inr i =>
      change neighborSame (append f r) (newCell (n + 1) i) ≤ 2
      rw [degree_new_frontier f r s hr]
      exact hn i

end A165378Degree

-- Component: A165378TrackBase

namespace A165378Proof

open OMA.S_oeis_a165378 A165378Board A165378Glue A165378Invariant A165378Degree Relation

structure Track {n : ℕ} (f : Cell (n + 1) → Fin 4) (s : State) : Prop where
  row_eq : s.row = fun i => f (newCell n i)
  deg_eq : s.deg = fun i => neighborSame f (newCell n i)
  part_iff : ∀ i j, s.part i = s.part j ↔
    ReflTransGen (sameAdj f) (newCell n i) (newCell n j)
  done_iff : ∀ v, s.done v = true ↔ Done (sameAdj f) f (newCell n) v
  bounded : ∀ i, s.part i < 4
  good : Good (sameAdj f) f (newCell n)
  degrees : ∀ p, neighborSame f p ≤ 2

lemma append_cellEquiv {n : ℕ} (f : Cell n → Fin 4) (r : Row) (x : Cell n ⊕ Fin 4) :
    append f r (cellEquiv n x) = Sum.elim f r x := by
  cases x <;> simp only [cellEquiv_old, cellEquiv_new, append_old, append_new, Sum.elim_inl,
    Sum.elim_inr]

lemma closed_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (x : Cell (n + 1) ⊕ Fin 4) :
    Closed (sameAdj (append f r)) (newCell (n + 1)) (cellEquiv (n + 1) x) ↔
      Closed (joined (sameAdj f) (newCell n) (cross f r) (horizontalRel r)) Sum.inr x := by
  unfold Closed
  exact forall_congr' fun j => not_congr (reach_cellEquiv_iff f r x (.inr j))

lemma done_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row) (v : Fin 4) :
    Done (sameAdj (append f r)) (append f r) (newCell (n + 1)) v ↔
      Done (joined (sameAdj f) (newCell n) (cross f r) (horizontalRel r))
        (Sum.elim f r) Sum.inr v := by
  constructor
  · rintro ⟨x, hc, hx⟩
    obtain ⟨x, rfl⟩ := (cellEquiv (n + 1)).surjective x
    exact ⟨x, (append_cellEquiv f r x).symm.trans hc, (closed_append_iff f r x).mp hx⟩
  · rintro ⟨x, hc, hx⟩
    exact ⟨cellEquiv (n + 1) x, (append_cellEquiv f r x).trans hc,
      (closed_append_iff f r x).mpr hx⟩

lemma good_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row) :
    Good (sameAdj (append f r)) (append f r) (newCell (n + 1)) ↔
      Good (joined (sameAdj f) (newCell n) (cross f r) (horizontalRel r))
        (Sum.elim f r) Sum.inr := by
  constructor
  · intro h x hx y hc
    apply (reach_cellEquiv_iff f r x y).mp
    apply h _ ((closed_append_iff f r x).mpr hx)
    simpa only [append_cellEquiv] using hc
  · intro h x hx y hc
    obtain ⟨x, rfl⟩ := (cellEquiv (n + 1)).surjective x
    obtain ⟨y, rfl⟩ := (cellEquiv (n + 1)).surjective y
    apply (reach_cellEquiv_iff f r x y).mpr
    apply h x ((closed_append_iff f r x).mp hx) y
    simpa only [append_cellEquiv] using hc

lemma good_old_of_append {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (h : Good (sameAdj (append f r)) (append f r) (newCell (n + 1))) :
    Good (sameAdj f) f (newCell n) := by
  intro x hx y hc
  have hh := (good_append_iff f r).mp h
  have hp := hh (.inl x) (closed_old _ _ _ _ x hx) (.inl y) hc
  exact (closed_old_iff _ _ _ _ hx).mp hp

lemma accepting_component_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (v : Fin 4) (hocc : ∃ x, f x = v) :
    colorConnected f v ↔
      (s.done v = true ∧ ∀ j, s.row j ≠ v) ∨
      (s.done v = false ∧ ∃ j, s.row j = v ∧ ∀ i, s.row i = v → s.part i = s.part j) := by
  have hh := connected_iff (sameAdj f) (newCell n) f
    (fun _ _ => sameAdj_reverse) (fun _ _ hxy => hxy.2) h.good v hocc
  have hd : s.done v = false ↔ ¬ Done (sameAdj f) f (newCell n) v :=
    Bool.eq_false_iff.trans (not_congr (h.done_iff v))
  simpa only [colorConnected, hd, h.done_iff, h.row_eq, h.part_iff] using hh

lemma accepting_occurs {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (ha : accepting s) (v : Fin 4) : ∃ x, f x = v := by
  rcases ha.2.2 v with ⟨hd, _⟩ | ⟨_, j, hj, _⟩
  · obtain ⟨x, hx, _⟩ := (h.done_iff v).mp hd
    exact ⟨x, hx⟩
  · exact ⟨newCell n j, by simpa only [h.row_eq] using hj⟩

lemma accepting_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (hocc : ∀ v, ∃ x, f x = v) :
    accepting s ↔ f (newCell n 0) = 2 ∧ f (newCell n 3) = 3 ∧
      ∀ v, colorConnected f v := by
  unfold accepting
  have hc := forall_congr' (fun v => accepting_component_iff h v (hocc v))
  rw [← hc]
  simp only [h.row_eq]

end A165378Proof

-- Component: A165378Merge

namespace A165378Proof
open Relation

def pairEdge (a b x y : Fin 8) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

def addEdge (R : Fin 8 → Fin 8 → Prop) (c : Fin 8 → Fin 4) (a b : Fin 8) :
    Fin 8 → Fin 8 → Prop :=
  fun x y => R x y ∨ (c a = c b ∧ pairEdge a b x y)

lemma rtc_labels (l : Fin 8 → ℕ) (i j : Fin 8) :
    ReflTransGen (fun x y => l x = l y) i j ↔ l i = l j := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ he ih => exact ih.trans he
  · intro he
    exact ReflTransGen.single he

lemma merge_reach (R : Fin 8 → Fin 8 → Prop) (l : Fin 8 → ℕ)
    (h : ∀ i j, ReflTransGen R i j ↔ l i = l j) (a b i j : Fin 8) :
    ReflTransGen (fun x y => R x y ∨ pairEdge a b x y) i j ↔
      merge l a b i = merge l a b j := by
  constructor
  · intro hij
    induction hij with
    | refl => rfl
    | @tail x y hp he ih =>
      apply ih.trans
      apply (merge_eq_iff l a b x y).mpr
      rcases he with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ((h _ _).mp (.single he))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro hij
    have lift {x y : Fin 8} (hxy : ReflTransGen R x y) :
        ReflTransGen (fun x y => R x y ∨ pairEdge a b x y) x y := by
      induction hxy with
      | refl => exact .refl
      | tail _ he ih => exact ih.tail (Or.inl he)
    have hab : ReflTransGen (fun x y => R x y ∨ pairEdge a b x y) a b :=
      .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hba : ReflTransGen (fun x y => R x y ∨ pairEdge a b x y) b a :=
      .single (Or.inr (Or.inr ⟨rfl, rfl⟩))
    rcases (merge_eq_iff l a b i j).mp hij with hij | ⟨hia, hjb⟩ | ⟨hib, hja⟩
    · exact lift ((h _ _).mpr hij)
    · exact (lift ((h _ _).mpr hia)).trans (hab.trans (lift ((h _ _).mpr hjb.symm)))
    · exact (lift ((h _ _).mpr hib)).trans (hba.trans (lift ((h _ _).mpr hja.symm)))

lemma join_reach (s : State) (r : Row) (R : Fin 8 → Fin 8 → Prop)
    (l : Fin 8 → ℕ) (h : ∀ i j, ReflTransGen R i j ↔ l i = l j)
    (a b i j : Fin 8) :
    ReflTransGen (addEdge R (color s r) a b) i j ↔
      join s r l a b i = join s r l a b j := by
  unfold addEdge
  by_cases he : color s r a = color s r b
  · simpa [addEdge, join, he] using merge_reach R l h a b i j
  · simpa [addEdge, join, he] using h i j

def finalRel (s : State) (r : Row) : Fin 8 → Fin 8 → Prop :=
  let R := fun i j => initialLabels s i = initialLabels s j
  let R := addEdge R (color s r) 4 5
  let R := addEdge R (color s r) 5 6
  let R := addEdge R (color s r) 6 7
  let R := addEdge R (color s r) 1 4
  let R := addEdge R (color s r) 2 5
  addEdge R (color s r) 3 6

lemma links_reach (s : State) (r : Row) (i j : Fin 8) :
    ReflTransGen (finalRel s r) i j ↔ links s r i = links s r j := by
  have h0 := rtc_labels (initialLabels s)
  have h1 := join_reach s r _ _ h0 4 5
  have h2 := join_reach s r _ _ h1 5 6
  have h3 := join_reach s r _ _ h2 6 7
  have h4 := join_reach s r _ _ h3 1 4
  have h5 := join_reach s r _ _ h4 2 5
  have h6 := join_reach s r _ _ h5 3 6
  exact h6 i j

end A165378Proof

-- Component: A165378Labels

namespace A165378Proof
open Relation

def exposeIndex : Fin 4 ⊕ Fin 4 ≃ Fin 8 where
  toFun := Sum.elim old new
  invFun := fun i => if h : i.val < 4 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 4, by omega⟩
  left_inv := by
    intro a
    cases a with
    | inl i => simp [old, i.isLt]
    | inr i => simp [new]
  right_inv := by
    intro i
    dsimp
    split_ifs with h
    · rfl
    · apply Fin.ext
      dsimp [new]
      omega

def compact (s : State) (r : Row) : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Prop
  | .inl i, .inl j => s.part i = s.part j
  | .inl i, .inr j => i.val = j.val + 1 ∧ s.row i = r j
  | .inr i, .inl j => j.val = i.val + 1 ∧ s.row j = r i
  | .inr i, .inr j => (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j

private lemma fin4_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
private lemma fin4_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
private lemma fin4_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
private lemma fin4_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl

set_option maxHeartbeats 500000 in
private lemma finalRel_oo (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (i j : Fin 4) :
    finalRel s r (old i) (old j) ↔ i = j ∨ s.part i = s.part j := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases i <;> fin_cases j <;>
    norm_num [finalRel, addEdge, pairEdge, old, new, initialLabels, color, fin4_0, fin4_1, fin4_2, fin4_3, Fin.ext_iff] <;> omega

set_option maxHeartbeats 500000 in
private lemma finalRel_on (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (i j : Fin 4) :
    finalRel s r (old i) (new j) ↔ i.val = j.val + 1 ∧ s.row i = r j := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases i <;> fin_cases j <;>
    norm_num [finalRel, addEdge, pairEdge, old, new, initialLabels, color, fin4_0, fin4_1, fin4_2, fin4_3, Fin.ext_iff] <;> omega

set_option maxHeartbeats 500000 in
private lemma finalRel_no (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (i j : Fin 4) :
    finalRel s r (new i) (old j) ↔ j.val = i.val + 1 ∧ s.row j = r i := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases i <;> fin_cases j <;>
    norm_num [finalRel, addEdge, pairEdge, old, new, initialLabels, color, fin4_0, fin4_1, fin4_2, fin4_3, Fin.ext_iff] <;> omega

set_option maxHeartbeats 500000 in
private lemma finalRel_nn (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (i j : Fin 4) :
    finalRel s r (new i) (new j) ↔ i = j ∨ ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j) := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases i <;> fin_cases j <;>
    norm_num [finalRel, addEdge, pairEdge, old, new, initialLabels, color, fin4_0, fin4_1, fin4_2, fin4_3, Fin.ext_iff] <;> omega

lemma finalRel_iff (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (a b : Fin 4 ⊕ Fin 4) :
    finalRel s r (exposeIndex a) (exposeIndex b) ↔ a = b ∨ compact s r a b := by
  rcases a with i | i <;> rcases b with j | j
  · simpa only [exposeIndex, Equiv.coe_fn_mk, Sum.elim_inl, Sum.inl.injEq, compact]
      using finalRel_oo s r hb i j
  · simpa only [exposeIndex, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
      Sum.inl_ne_inr, false_or, compact] using finalRel_on s r hb i j
  · simpa only [exposeIndex, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
      Sum.inr_ne_inl, false_or, compact] using finalRel_no s r hb i j
  · simpa only [exposeIndex, Equiv.coe_fn_mk, Sum.elim_inr, Sum.inr.injEq, compact]
      using finalRel_nn s r hb i j

lemma links_eq_iff (s : State) (r : Row) (hb : ∀ i, s.part i < 4)
    (a b : Fin 4 ⊕ Fin 4) :
    links s r (exposeIndex a) = links s r (exposeIndex b) ↔
      ReflTransGen (compact s r) a b := by
  rw [← links_reach]
  constructor
  · intro h
    have hh := h.lift' exposeIndex.symm (fun x y hxy => by
      change ReflTransGen (compact s r) (exposeIndex.symm x) (exposeIndex.symm y)
      have he := (finalRel_iff s r hb (exposeIndex.symm x) (exposeIndex.symm y)).mp
        (by simpa using hxy)
      rcases he with he | he
      · rw [he]
      · exact ReflTransGen.single he)
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hh
  · intro h
    exact h.lift exposeIndex (fun x y hxy =>
      (finalRel_iff s r hb x y).mpr (Or.inr hxy))

end A165378Proof

-- Component: A165378Track

namespace A165378Proof
open OMA.S_oeis_a165378 A165378Board A165378Glue A165378Invariant A165378Degree Relation

lemma compact_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State} (h : Track f s)
    (r : Row) (a b : Fin 4 ⊕ Fin 4) :
    compact s r a b ↔ compressed (sameAdj f) (newCell n) (cross f r) (horizontalRel r) a b := by
  cases a with
  | inl i =>
    cases b with
    | inl j => exact h.part_iff i j
    | inr j => simp only [compact, compressed, cross, h.row_eq]
  | inr i =>
    cases b with
    | inl j => simp only [compact, compressed, cross, h.row_eq]
    | inr j => rfl

lemma compact_reach_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State} (h : Track f s)
    (r : Row) (a b : Fin 4 ⊕ Fin 4) :
    ReflTransGen (compact s r) a b ↔
      ReflTransGen (compressed (sameAdj f) (newCell n) (cross f r) (horizontalRel r)) a b := by
  constructor
  · exact fun hp => ReflTransGen.mono (fun x y hxy => (compact_iff h r x y).mp hxy) a b hp
  · exact fun hp => ReflTransGen.mono (fun x y hxy => (compact_iff h r x y).mpr hxy) a b hp

lemma links_reach_compressed {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (r : Row) (a b : Fin 4 ⊕ Fin 4) :
    links s r (exposeIndex a) = links s r (exposeIndex b) ↔
      ReflTransGen (compressed (sameAdj f) (newCell n) (cross f r) (horizontalRel r)) a b :=
  (links_eq_iff s r h.bounded a b).trans (compact_reach_iff h r a b)

lemma lost_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State} (h : Track f s)
    (r : Row) (i : Fin 4) :
    lost s r i ↔ Lost (sameAdj f) (newCell n) (cross f r) (horizontalRel r) i := by
  unfold lost Lost
  exact forall_congr' fun j => not_congr (links_reach_compressed h r (.inl i) (.inr j))

lemma color_exposeIndex {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State} (h : Track f s)
    (r : Row) (a : Fin 4 ⊕ Fin 4) :
    color s r (exposeIndex a) = Sum.elim (f ∘ newCell n) r a := by
  cases a with
  | inl i => simp [exposeIndex, old, color, i.isLt, h.row_eq]
  | inr i => simp [exposeIndex, new, color]

lemma avoid_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State} (h : Track f s) (r : Row) :
    (∀ j, s.done (r j) = false) ↔
      ∀ v, Done (sameAdj f) f (newCell n) v → ∀ j, r j ≠ v := by
  constructor
  · intro ha v hv j hj
    have hh := (h.done_iff v).mpr hv
    rw [← hj, ha j] at hh
    cases hh
  · intro ha j
    cases hd : s.done (r j) with
    | false => rfl
    | true => exact (ha (r j) ((h.done_iff (r j)).mp hd) j rfl).elim

lemma lost_classes_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (r : Row) :
    (∀ i, lost s r i → ∀ j : Fin 8,
      color s r j = s.row i → links s r j = links s r (old i)) ↔
    (∀ i, Lost (sameAdj f) (newCell n) (cross f r) (horizontalRel r) i →
      ∀ z : Fin 4 ⊕ Fin 4, Sum.elim (f ∘ newCell n) r z = f (newCell n i) →
        ReflTransGen (compressed (sameAdj f) (newCell n) (cross f r)
          (horizontalRel r)) (.inl i) z) := by
  constructor
  · intro hc i hi z hz
    apply (links_reach_compressed h r (.inl i) z).mp
    apply Eq.symm
    apply hc i ((lost_iff h r i).mpr hi) (exposeIndex z)
    simpa only [color_exposeIndex h r z, h.row_eq] using hz
  · intro hc i hi j hj
    obtain ⟨z, rfl⟩ := exposeIndex.surjective j
    apply Eq.symm
    apply (links_reach_compressed h r (.inl i) z).mpr
    apply hc i ((lost_iff h r i).mp hi) z
    simpa only [color_exposeIndex h r z, h.row_eq] using hj

lemma permissible_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (r : Row) :
    permissible s r ↔
      Good (sameAdj (append f r)) (append f r) (newCell (n + 1)) ∧
        ∀ c, neighborSame (append f r) c ≤ 2 := by
  have hg := (good_append_iff f r).trans
    (good_joined_iff (sameAdj f) (newCell n) (cross f r) (horizontalRel r) f r
      (fun _ _ => sameAdj_reverse) (fun _ _ hxy => hxy.2) h.good)
  have hd := degree_append_iff f r s h.row_eq h.deg_eq h.degrees
  rw [hg, hd, ← avoid_iff h r, ← lost_classes_iff h r]
  constructor
  · rintro ⟨ha, ho, hn, hl⟩
    exact ⟨⟨ha, hl⟩, ho, hn⟩
  · rintro ⟨⟨ha, hl⟩, ho, hn⟩
    exact ⟨ha, ho, hn, hl⟩

lemma done_advance_iff {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (r : Row) (v : Fin 4) :
    (advance s r).done v = true ↔
      Done (sameAdj (append f r)) (append f r) (newCell (n + 1)) v := by
  rw [done_append_iff, done_joined_iff _ _ _ _ _ _
    (fun _ _ => sameAdj_reverse) (fun _ _ hxy => hxy.2)]
  simp only [advance, Bool.or_eq_true, decide_eq_true_eq, h.done_iff, h.row_eq,
    lost_iff h r]

lemma track_advance {n : ℕ} {f : Cell (n + 1) → Fin 4} {s : State}
    (h : Track f s) (r : Row) (hp : permissible s r) : Track (append f r) (advance s r) := by
  have hg := (permissible_iff h r).mp hp
  refine ⟨?_, ?_, ?_, done_advance_iff h r, ?_, hg.1, hg.2⟩
  · funext i
    exact (append_new f r i).symm
  · funext i
    exact (degree_new_frontier f r s h.row_eq i).symm
  · intro i j
    change normalize (fun k => links s r (new k)) i =
      normalize (fun k => links s r (new k)) j ↔ _
    rw [normalize_eq_iff]
    exact (links_reach_compressed h r (.inr i) (.inr j)).trans
      (reach_exposed_iff f r (.inr i) (.inr j)).symm
  · intro i
    change normalize (fun k => links s r (new k)) i < 4
    unfold normalize
    split_ifs <;> decide

end A165378Proof

-- Component: A165378Initial

namespace A165378Proof
open Relation A165378Board

lemma horizontal_symmetric (r : Row) (i j : Fin 4) (h : horizontalRel r i j) :
    horizontalRel r j i := ⟨h.1.symm, h.2.symm⟩

lemma rowLabels_preserved (r : Row) (i j : Fin 4) (h : horizontalRel r i j) :
    rowLabels r i = rowLabels r j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [horizontalRel] at h <;>
    simp_all [rowLabels]

lemma rowLabels_rep (r : Row) (i : Fin 4) :
    ReflTransGen (horizontalRel r) (Fin.ofNat 4 (rowLabels r i)) i := by
  have of0 : Fin.ofNat 4 0 = (0 : Fin 4) := rfl
  have of1 : Fin.ofNat 4 1 = (1 : Fin 4) := rfl
  have of2 : Fin.ofNat 4 2 = (2 : Fin 4) := rfl
  have of3 : Fin.ofNat 4 3 = (3 : Fin 4) := rfl
  have e01 (h : r 0 = r 1) : ReflTransGen (horizontalRel r) 0 1 :=
    .single ⟨Or.inl rfl, h⟩
  have e12 (h : r 1 = r 2) : ReflTransGen (horizontalRel r) 1 2 :=
    .single ⟨Or.inl rfl, h⟩
  have e23 (h : r 2 = r 3) : ReflTransGen (horizontalRel r) 2 3 :=
    .single ⟨Or.inl rfl, h⟩
  fin_cases i
  · exact .refl
  · change ReflTransGen (horizontalRel r)
      (Fin.ofNat 4 (if r 0 = r 1 then 0 else 1)) 1
    by_cases h : r 0 = r 1
    · simpa only [of0, of1, of2, of3, if_pos h] using e01 h
    · simpa only [of0, of1, of2, of3, if_neg h] using
        (show ReflTransGen (horizontalRel r) 1 1 from .refl)
  · change ReflTransGen (horizontalRel r)
      (Fin.ofNat 4 (if r 1 = r 2 then (if r 0 = r 1 then 0 else 1) else 2)) 2
    by_cases h12 : r 1 = r 2
    · by_cases h01 : r 0 = r 1
      · simpa only [of0, of1, of2, of3, if_pos h12, if_pos h01] using (e01 h01).trans (e12 h12)
      · simpa only [of0, of1, of2, of3, if_pos h12, if_neg h01] using e12 h12
    · simpa only [of0, of1, of2, of3, if_neg h12] using
        (show ReflTransGen (horizontalRel r) 2 2 from .refl)
  · change ReflTransGen (horizontalRel r)
      (Fin.ofNat 4 (if r 2 = r 3 then
        (if r 1 = r 2 then (if r 0 = r 1 then 0 else 1) else 2) else 3)) 3
    by_cases h23 : r 2 = r 3
    · by_cases h12 : r 1 = r 2
      · by_cases h01 : r 0 = r 1
        · simpa only [of0, of1, of2, of3, if_pos h23, if_pos h12, if_pos h01] using
            ((e01 h01).trans (e12 h12)).trans (e23 h23)
        · simpa only [of0, of1, of2, of3, if_pos h23, if_pos h12, if_neg h01] using
            (e12 h12).trans (e23 h23)
      · simpa only [of0, of1, of2, of3, if_pos h23, if_neg h12] using e23 h23
    · simpa only [of0, of1, of2, of3, if_neg h23] using
        (show ReflTransGen (horizontalRel r) 3 3 from .refl)

lemma rowLabels_reach (r : Row) (i j : Fin 4) :
    rowLabels r i = rowLabels r j ↔ ReflTransGen (horizontalRel r) i j := by
  constructor
  · intro h
    have hi := A165378Glue.reverse_path (horizontalRel r) (horizontal_symmetric r)
      (rowLabels_rep r i)
    apply hi.trans
    simpa only [h] using rowLabels_rep r j
  · intro h
    induction h with
    | refl => rfl
    | tail _ he ih => exact ih.trans (rowLabels_preserved r _ _ he)

lemma rowLabels_lt (r : Row) (i : Fin 4) : rowLabels r i < 4 := by
  fin_cases i <;> dsimp [rowLabels] <;> (try split_ifs) <;> omega

lemma normalize_lt (l : Fin 4 → ℕ) (i : Fin 4) : normalize l i < 4 := by
  unfold normalize
  split_ifs <;> omega

end A165378Proof

-- Component: A165378TrackInitial

namespace A165378Proof
open OMA.S_oeis_a165378 A165378Board A165378Glue A165378Invariant A165378Degree Relation

lemma single_cell_eq (x : Cell 1) : newCell 0 x.2 = x := by
  apply Prod.ext
  · apply Fin.ext
    have hx := x.1.isLt
    change 0 = x.1.val
    omega
  · rfl

lemma single_frontier_surjective : Function.Surjective (newCell 0) :=
  fun x => ⟨x.2, single_cell_eq x⟩

lemma single_edge_iff (r : Row) (i j : Fin 4) :
    sameAdj (fun c : Cell 1 => r c.2) (newCell 0 i) (newCell 0 j) ↔ horizontalRel r i j := by
  change (neighbors (newCell 0 i) (newCell 0 j) ∧ r i = r j) ↔ horizontalRel r i j
  rw [neighbors_new_new]
  rfl

lemma single_reach_iff (r : Row) (i j : Fin 4) :
    ReflTransGen (sameAdj (fun c : Cell 1 => r c.2)) (newCell 0 i) (newCell 0 j) ↔
      ReflTransGen (horizontalRel r) i j := by
  constructor
  · intro h
    have hm : ∀ x y : Cell 1, sameAdj (fun c => r c.2) x y → horizontalRel r x.2 y.2 := by
      intro x y hxy
      apply (single_edge_iff r x.2 y.2).mp
      simpa only [single_cell_eq] using hxy
    exact h.lift Prod.snd hm
  · intro h
    exact h.lift (newCell 0) (fun x y hxy => (single_edge_iff r x y).mpr hxy)

lemma horizontal_le (r : Row) (i : Fin 4) : horizontal r i ≤ 2 := by
  fin_cases i <;> dsimp [horizontal] <;> unfold bit <;> split_ifs <;> decide

lemma track_initial (r : Row) : Track (fun c : Cell 1 => r c.2) (initial r) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    exact (degree_single r i).symm
  · intro i j
    exact (rowLabels_reach r i j).trans (single_reach_iff r i j).symm
  · intro v
    exact iff_of_false Bool.false_ne_true
      (not_done_of_surjective _ _ _ single_frontier_surjective v)
  · intro i
    exact rowLabels_lt r i
  · exact good_of_surjective _ _ _ single_frontier_surjective
  · intro p
    rw [← single_cell_eq p, degree_single]
    exact horizontal_le r p.2

end A165378Proof

-- Component: A165378ScanBase

namespace A165378Proof
open OMA.S_oeis_a165378 A165378Board

def rows {n : ℕ} (f : Cell n → Fin 4) : List Row :=
  List.ofFn (fun i j => f (i, j))

def scanRows : List Row → Option State
  | [] => none
  | r :: rs => run (initial r) rs

def scan {n : ℕ} (f : Cell n → Fin 4) : Option State := scanRows (rows f)

lemma run_append (s : State) (xs ys : List Row) :
    run s (xs ++ ys) = (run s xs).bind (fun t => run t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, run, ih, Option.bind_assoc]

lemma scanRows_append (xs : List Row) (r : Row) (h : xs ≠ []) :
    scanRows (xs ++ [r]) = (scanRows xs).bind (fun s => step s r) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons q qs => simp [scanRows, run_append, run]

lemma rows_append {n : ℕ} (f : Cell n → Fin 4) (r : Row) :
    rows (append f r) = rows f ++ [r] := by
  unfold rows
  rw [List.ofFn_succ_last]
  have ho : (fun (i : Fin n) (j : Fin 4) => append f r (i.castSucc, j)) =
      fun i j => f (i, j) := by
    funext i j
    exact append_old f r (i, j)
  have hn : (fun j => append f r (Fin.last n, j)) = r := by
    funext j
    exact append_new f r j
  rw [ho, hn]

lemma rows_ne_nil {n : ℕ} (f : Cell (n + 1) → Fin 4) : rows f ≠ [] := by
  simp [rows]

lemma scan_append {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row) :
    scan (append f r) = (scan f).bind (fun s => step s r) := by
  unfold scan
  rw [rows_append]
  exact scanRows_append (rows f) r (rows_ne_nil f)

lemma rows_single (r : Row) : rows (fun c : Cell 1 => r c.2) = [r] := by
  simp [rows, List.ofFn_succ, List.ofFn_zero]

lemma scan_single (r : Row) : scan (fun c : Cell 1 => r c.2) = some (initial r) := by
  rw [scan, rows_single]
  rfl

lemma accepted_scan_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    Accepted (rows f) ↔
      f (0, 0) = 0 ∧ f (0, 3) = 1 ∧ ∃ s, scan f = some s ∧ accepting s := by
  unfold scan rows
  rw [List.ofFn_succ]
  rfl

end A165378Proof

-- Component: A165378Scan

namespace A165378Proof
open OMA.S_oeis_a165378 A165378Board A165378Glue A165378Invariant A165378Degree Relation

lemma scan_some_track {n : ℕ} (f : Cell (n + 1) → Fin 4) (s : State)
    (hs : scan f = some s) : Track f s := by
  induction n generalizing s with
  | zero =>
    let r : Row := fun j => f (newCell 0 j)
    have he : f = (fun c : Cell 1 => r c.2) := by
      funext c
      exact congrArg f (single_cell_eq c).symm
    rw [he, scan_single] at hs
    cases Option.some.inj hs
    rw [he]
    exact track_initial r
  | succ n ih =>
    let f₀ : Cell (n + 1) → Fin 4 := fun p => f (oldCell p)
    let r : Row := fun j => f (newCell (n + 1) j)
    have he : append f₀ r = f := append_eta f
    rw [← he, scan_append] at hs
    cases ho : scan f₀ with
    | none => simp only [ho, Option.bind_none, reduceCtorEq] at hs
    | some t =>
      have ht := ih f₀ t ho
      have hh : step t r = some s := by simpa only [ho, Option.bind_some] using hs
      unfold step at hh
      split_ifs at hh with hp
      · cases Option.some.inj hh
        rw [← he]
        exact track_advance ht r hp

lemma good_degree_scan_exists {n : ℕ} (f : Cell (n + 1) → Fin 4)
    (hg : Good (sameAdj f) f (newCell n)) (hd : ∀ c, neighborSame f c ≤ 2) :
    ∃ s, scan f = some s := by
  induction n with
  | zero =>
    let r : Row := fun j => f (newCell 0 j)
    have he : f = (fun c : Cell 1 => r c.2) := by
      funext c
      exact congrArg f (single_cell_eq c).symm
    exact ⟨initial r, by rw [he, scan_single]⟩
  | succ n ih =>
    let f₀ : Cell (n + 1) → Fin 4 := fun p => f (oldCell p)
    let r : Row := fun j => f (newCell (n + 1) j)
    have he : append f₀ r = f := append_eta f
    have hg₀ : Good (sameAdj f₀) f₀ (newCell n) :=
      good_old_of_append f₀ r (by simpa only [he] using hg)
    have hd₀ : ∀ c, neighborSame f₀ c ≤ 2 := by
      intro c
      exact (degree_old_le f₀ r c).trans (by simpa only [he] using hd (oldCell c))
    obtain ⟨s, hs⟩ := ih f₀ hg₀ hd₀
    have ht := scan_some_track f₀ s hs
    have hp : permissible s r := (permissible_iff ht r).mpr
      ⟨by simpa only [he] using hg, by simpa only [he] using hd⟩
    refine ⟨advance s r, ?_⟩
    rw [← he, scan_append, hs]
    simp only [Option.bind_some, step, if_pos hp]

lemma valid_corners {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    Valid (n + 1) f ↔
      f (0, 0) = 0 ∧ f (0, 3) = 1 ∧ f (newCell n 0) = 2 ∧
        f (newCell n 3) = 3 ∧ (∀ v, colorConnected f v) ∧ ∀ c, neighborSame f c ≤ 2 := by
  simp only [Valid, Nat.add_sub_cancel, newCell]
  constructor
  · rintro ⟨hn, h⟩
    exact h
  · intro h
    exact ⟨Nat.succ_pos n, h⟩

lemma corners_occurs {n : ℕ} {f : Cell (n + 1) → Fin 4}
    (h₀ : f (0, 0) = 0) (h₁ : f (0, 3) = 1)
    (h₂ : f (newCell n 0) = 2) (h₃ : f (newCell n 3) = 3) (v : Fin 4) :
    ∃ x, f x = v := by
  fin_cases v
  · exact ⟨(0, 0), h₀⟩
  · exact ⟨(0, 3), h₁⟩
  · exact ⟨newCell n 0, h₂⟩
  · exact ⟨newCell n 3, h₃⟩

lemma valid_accepted_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    Valid (n + 1) f ↔ Accepted (List.ofFn (fun i j => f (i, j))) := by
  change Valid (n + 1) f ↔ Accepted (rows f)
  rw [valid_corners, accepted_scan_iff]
  constructor
  · rintro ⟨h₀, h₁, h₂, h₃, hc, hd⟩
    have hg : Good (sameAdj f) f (newCell n) := by
      intro x hx y hy
      exact hc (f x) x y rfl hy
    obtain ⟨s, hs⟩ := good_degree_scan_exists f hg hd
    have ht := scan_some_track f s hs
    exact ⟨h₀, h₁, s, hs,
      (accepting_iff ht (corners_occurs h₀ h₁ h₂ h₃)).mpr ⟨h₂, h₃, hc⟩⟩
  · rintro ⟨h₀, h₁, s, hs, ha⟩
    have ht := scan_some_track f s hs
    obtain ⟨h₂, h₃, hc⟩ := (accepting_iff ht (accepting_occurs ht ha)).mp ha
    exact ⟨h₀, h₁, h₂, h₃, hc, ht.degrees⟩

end A165378Proof

-- Component: A165378Count

namespace A165378Count

open scoped BigOperators

variable {S : Type*}

def advance (children : S → Finset S) (f : S → ℕ) (s : S) : ℕ :=
  ∑ t ∈ children s, f t

def count (children : S → Finset S) (final : S → ℕ) : ℕ → S → ℕ
  | 0 => final
  | n + 1 => advance children (count children final n)

lemma advance_add (children : S → Finset S) (f g : S → ℕ) :
    advance children (fun s => f s + g s) =
      fun s => advance children f s + advance children g s := by
  funext s
  simp [advance, Finset.sum_add_distrib]

lemma advance_mul (children : S → Finset S) (k : ℕ) (f : S → ℕ) :
    advance children (fun s => k * f s) = fun s => k * advance children f s := by
  funext s
  simp [advance, Finset.mul_sum]

lemma count_certificate (children : S → Finset S) (final : S → ℕ)
    (offset : ℕ) (u v w : S → ℕ)
    (hbase : count children final offset = u)
    (hu : advance children u = fun s => u s + v s)
    (hv : advance children v = fun s => v s + w s)
    (hw : advance children w = w) (n : ℕ) :
    count children final (offset + n) =
      fun s => u s + n * v s + n.choose 2 * w s := by
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    rw [Nat.add_succ, count, ih, advance_add, advance_add,
      advance_mul, advance_mul, hu, hv, hw]
    funext s
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    ring

lemma initial_sum_certificate (children : S → Finset S) (final : S → ℕ)
    (initial : Finset S) (offset : ℕ) (u v w : S → ℕ)
    (hbase : count children final offset = u)
    (hu : advance children u = fun s => u s + v s)
    (hv : advance children v = fun s => v s + w s)
    (hw : advance children w = w) (n : ℕ) :
    (∑ s ∈ initial, count children final (offset + n) s) =
      (∑ s ∈ initial, u s) + n * (∑ s ∈ initial, v s) +
        n.choose 2 * (∑ s ∈ initial, w s) := by
  rw [count_certificate children final offset u v w hbase hu hv hw n]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

lemma quadratic_form (k : ℕ) :
    158 + k * 85 + k.choose 2 * 18 = 9 * (k + 4) ^ 2 + 4 * (k + 4) - 2 := by
  have h : 158 + k * 85 + k.choose 2 * 18 + 2 =
      9 * (k + 4) ^ 2 + 4 * (k + 4) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  omega

def admissible (children : S → Finset S) (final : S → Prop) :
    (n : ℕ) → S → (Fin n → S) → Prop
  | 0, s, _ => final s
  | n + 1, s, f => f 0 ∈ children s ∧ admissible children final n (f 0) (Fin.tail f)

noncomputable def pathSuccEquiv (children : S → Finset S) (final : S → Prop)
    (n : ℕ) (s : S) :
    {f : Fin (n + 1) → S // admissible children final (n + 1) s f} ≃
      (t : {t // t ∈ children s}) ×
        {f : Fin n → S // admissible children final n t.val f} where
  toFun f := ⟨⟨f.val 0, f.property.1⟩, ⟨Fin.tail f.val, f.property.2⟩⟩
  invFun f := ⟨Fin.cons f.1.val f.2.val, by
    simpa only [admissible, Fin.cons_zero, Fin.tail_cons] using
      And.intro f.1.property f.2.property⟩
  left_inv f := by ext i; exact congrFun (Fin.cons_self_tail f.val) i
  right_inv f := by cases f; rfl

lemma card_paths [Fintype S] (children : S → Finset S) (final : S → Prop)
    [DecidablePred final]
    (n : ℕ) (s : S) :
    Nat.card {f : Fin n → S // admissible children final n s f} =
      count children (fun t => if final t then 1 else 0) n s := by
  classical
  induction n generalizing s with
  | zero =>
    by_cases h : final s
    · simp [admissible, count, h, Nat.card_eq_fintype_card]
    · simp [admissible, count, h, Nat.card_eq_fintype_card]
  | succ n ih =>
    rw [Nat.card_congr (pathSuccEquiv children final n s)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [← Nat.card_eq_fintype_card, ih]
    simp [count, advance, Finset.sum_attach]

def Paths (initial : Finset S) (children : S → Finset S) (final : S → Prop)
    (n : ℕ) :=
  (s : {s // s ∈ initial}) × {f : Fin n → S // admissible children final n s.val f}

lemma card_initial_paths [Fintype S] (initial : Finset S)
    (children : S → Finset S) (final : S → Prop) [DecidablePred final] (n : ℕ) :
    Nat.card (Paths initial children final n) =
      ∑ s ∈ initial, count children (fun t => if final t then 1 else 0) n s := by
  classical
  unfold Paths
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [← Nat.card_eq_fintype_card, card_paths]
  exact Finset.sum_attach _ _

lemma initial_quadratic (children : S → Finset S) (final : S → ℕ)
    (initial : Finset S) (u v w : S → ℕ)
    (hbase : count children final 3 = u)
    (hu : advance children u = fun s => u s + v s)
    (hv : advance children v = fun s => v s + w s)
    (hw : advance children w = w)
    (hu0 : (∑ s ∈ initial, u s) = 158)
    (hv0 : (∑ s ∈ initial, v s) = 85)
    (hw0 : (∑ s ∈ initial, w s) = 18) (n : ℕ) (hn : 3 < n) :
    (∑ s ∈ initial, count children final (n - 1) s) = 9 * n ^ 2 + 4 * n - 2 := by
  have hindex : n - 1 = 3 + (n - 4) := by omega
  rw [hindex, initial_sum_certificate children final initial 3 u v w hbase hu hv hw,
    hu0, hv0, hw0, quadratic_form]
  rw [Nat.sub_add_cancel (by omega : 4 ≤ n)]

end A165378Count

-- Component: A165378PathBridge

namespace A165378PathBridge

open A165378Proof A165378Count
open scoped BigOperators

variable {S : Type*}

/-- The finite table recognizes exactly the row-by-row automaton, with no duplicate
choices of the same row at either an initial or a subsequent step. -/
structure CorrectTable (state : S → State) (starts : Finset S)
    (children : S → Finset S) : Prop where
  start_rows : ∀ r : Row, (r 0 = 0 ∧ r 3 = 1) ↔
    ∃ i ∈ starts, (state i).row = r
  start_initial : ∀ i ∈ starts, state i = initial (state i).row
  start_injective : ∀ i j, i ∈ starts → j ∈ starts →
    (state i).row = (state j).row → i = j
  step_iff : ∀ i r t, step (state i) r = some t ↔
    ∃ j ∈ children i, (state j).row = r ∧ state j = t
  child_injective : ∀ i j k, j ∈ children i → k ∈ children i →
    (state j).row = (state k).row → j = k

variable {state : S → State} {starts : Finset S} {children : S → Finset S}

lemma run_of_admissible (h : CorrectTable state starts children)
    {n : ℕ} {i : S} {p : Fin n → S}
    (hp : admissible children (fun j => accepting (state j)) n i p) :
    ∃ t, run (state i) (List.ofFn fun k => (state (p k)).row) = some t ∧
      accepting t := by
  induction n generalizing i with
  | zero => exact ⟨state i, rfl, hp⟩
  | succ n ih =>
    obtain ⟨t, ht, ha⟩ := ih hp.2
    have hs : step (state i) (state (p 0)).row = some (state (p 0)) :=
      (h.step_iff _ _ _).mpr ⟨p 0, hp.1, rfl, rfl⟩
    refine ⟨t, ?_, ha⟩
    simpa only [List.ofFn_succ, run, hs, Option.bind_some, Fin.tail] using ht

lemma path_of_run (h : CorrectTable state starts children) {n : ℕ}
    {i : S} {r : Fin n → Row}
    (hr : ∃ t, run (state i) (List.ofFn r) = some t ∧ accepting t) :
    ∃ p : Fin n → S,
      admissible children (fun j => accepting (state j)) n i p ∧
      ∀ k, (state (p k)).row = r k := by
  induction n generalizing i with
  | zero =>
    obtain ⟨t, ht, ha⟩ := hr
    have he : state i = t := by simpa only [List.ofFn_zero, run, Option.some.injEq] using ht
    refine ⟨Fin.elim0, ?_, fun k => Fin.elim0 k⟩
    simpa only [admissible, he] using ha
  | succ n ih =>
    obtain ⟨t, ht, ha⟩ := hr
    rw [List.ofFn_succ, run] at ht
    cases hs : step (state i) (r 0) with
    | none => simp only [hs, Option.bind_none, reduceCtorEq] at ht
    | some s =>
      simp only [hs, Option.bind_some] at ht
      obtain ⟨j, hj, hjr, hjs⟩ := (h.step_iff _ _ _).mp hs
      obtain ⟨p, hp, hpr⟩ := ih (i := j) (r := Fin.tail r) ⟨t, hjs ▸ ht, ha⟩
      refine ⟨Fin.cons j p, ?_, ?_⟩
      · simpa only [admissible, Fin.cons_zero, Fin.tail_cons] using And.intro hj hp
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · exact hjr
        · exact hpr l

lemma path_rows_injective (h : CorrectTable state starts children)
    {n : ℕ} {i : S} {p q : Fin n → S}
    (hp : admissible children (fun j => accepting (state j)) n i p)
    (hq : admissible children (fun j => accepting (state j)) n i q)
    (hr : ∀ k, (state (p k)).row = (state (q k)).row) : p = q := by
  induction n generalizing i with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have he : p 0 = q 0 := h.child_injective i (p 0) (q 0) hp.1 hq.1 (hr 0)
    have ht : Fin.tail p = Fin.tail q :=
      ih hp.2 (he ▸ hq.2) (fun k => hr k.succ)
    funext k
    exact Fin.cases he (congrFun ht) k

def pathRows {n : ℕ}
    (p : Paths starts children (fun i => accepting (state i)) n) : Fin (n + 1) → Row :=
  Fin.cons (state p.1.val).row (fun k => (state (p.2.val k)).row)

lemma pathRows_accepted (h : CorrectTable state starts children) {n : ℕ}
    (p : Paths starts children (fun i => accepting (state i)) n) :
    Accepted (List.ofFn (pathRows p)) := by
  have hs := (h.start_rows (state p.1.val).row).mpr ⟨p.1.val, p.1.property, rfl⟩
  have hr := run_of_admissible h p.2.property
  rw [h.start_initial p.1.val p.1.property] at hr
  simpa only [pathRows, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Accepted] using
    And.intro hs.1 (And.intro hs.2 hr)

def pathToRows (h : CorrectTable state starts children) (n : ℕ) :
    Paths starts children (fun i => accepting (state i)) n →
      {r : Fin (n + 1) → Row // Accepted (List.ofFn r)} :=
  fun p => ⟨pathRows p, pathRows_accepted h p⟩

lemma pathToRows_injective (h : CorrectTable state starts children) (n : ℕ) :
    Function.Injective (pathToRows h n) := by
  rintro ⟨⟨i, hi⟩, ⟨p, hp⟩⟩ ⟨⟨j, hj⟩, ⟨q, hq⟩⟩ he
  have hr := congrArg Subtype.val he
  have hfirst : (state i).row = (state j).row := congrFun hr 0
  have hij := h.start_injective i j hi hj hfirst
  subst j
  have hpq : p = q := path_rows_injective h hp hq (fun k => congrFun hr k.succ)
  subst q
  rfl

lemma pathToRows_surjective (h : CorrectTable state starts children) (n : ℕ) :
    Function.Surjective (pathToRows h n) := by
  rintro ⟨r, hr⟩
  rw [List.ofFn_succ] at hr
  rcases hr with ⟨h0, h3, ht⟩
  obtain ⟨i, hi, hir⟩ := (h.start_rows (r 0)).mp ⟨h0, h3⟩
  have hinit : state i = initial (r 0) := (h.start_initial i hi).trans (congrArg initial hir)
  obtain ⟨p, hp, hpr⟩ := path_of_run h (i := i) (r := Fin.tail r) (hinit ▸ ht)
  refine ⟨⟨⟨i, hi⟩, ⟨p, hp⟩⟩, ?_⟩
  apply Subtype.ext
  funext k
  exact Fin.cases hir hpr k

noncomputable def pathRowsEquiv (h : CorrectTable state starts children) (n : ℕ) :
    Paths starts children (fun i => accepting (state i)) n ≃
      {r : Fin (n + 1) → Row // Accepted (List.ofFn r)} :=
  Equiv.ofBijective (pathToRows h n)
    ⟨pathToRows_injective h n, pathToRows_surjective h n⟩

theorem card_accepted [Fintype S] (h : CorrectTable state starts children) (n : ℕ) :
    Nat.card {r : Fin (n + 1) → Row // Accepted (List.ofFn r)} =
      ∑ i ∈ starts,
        count children (fun j => if accepting (state j) then 1 else 0) n i := by
  rw [← Nat.card_congr (pathRowsEquiv h n)]
  exact card_initial_paths starts children (fun i => accepting (state i)) n

theorem card_valid_of_iff [Fintype S] (h : CorrectTable state starts children) (n : ℕ)
    (hvalid : ∀ f : OMA.S_oeis_a165378.Cell (n + 1) → Fin 4,
      OMA.S_oeis_a165378.Valid (n + 1) f ↔
        Accepted (List.ofFn fun i j => f (i, j))) :
    Nat.card {f : OMA.S_oeis_a165378.Cell (n + 1) → Fin 4 //
      OMA.S_oeis_a165378.Valid (n + 1) f} =
      ∑ i ∈ starts,
        count children (fun j => if accepting (state j) then 1 else 0) n i := by
  rw [Nat.card_congr ((Equiv.curry (Fin (n + 1)) (Fin 4) (Fin 4)).subtypeEquiv
    (q := fun r => Accepted (List.ofFn r)) hvalid)]
  exact card_accepted h n

theorem card_valid_of_iff_pos [Fintype S] (h : CorrectTable state starts children)
    (n : ℕ) (hn : 0 < n)
    (hvalid : ∀ f : OMA.S_oeis_a165378.Cell n → Fin 4,
      OMA.S_oeis_a165378.Valid n f ↔ Accepted (List.ofFn fun i j => f (i, j))) :
    Nat.card {f : OMA.S_oeis_a165378.Cell n → Fin 4 // OMA.S_oeis_a165378.Valid n f} =
      ∑ i ∈ starts,
        count children (fun j => if accepting (state j) then 1 else 0) (n - 1) i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact card_valid_of_iff h k hvalid

end A165378PathBridge

-- Component: A165378Finish

namespace A165378Finish
open OMA.S_oeis_a165378 A165378Proof A165378Count A165378PathBridge
open scoped BigOperators

theorem card_formula {S : Type*} [Fintype S] {state : S → State}
    {starts : Finset S} {children : S → Finset S} {final : S → ℕ}
    (ht : CorrectTable state starts children)
    (hf : final = fun i => if accepting (state i) then 1 else 0)
    (hc : ∀ n, 3 < n → (∑ i ∈ starts, count children final (n - 1) i) =
      9 * n ^ 2 + 4 * n - 2) (n : ℕ) (hn : 3 < n) :
    Nat.card {f : Cell n → Fin 4 // Valid n f} = 9 * n ^ 2 + 4 * n - 2 := by
  have hpos : 0 < n := by omega
  have hv : ∀ f : Cell n → Fin 4, Valid n f ↔
      Accepted (List.ofFn (fun i j => f (i, j))) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    exact valid_accepted_iff
  have he := card_valid_of_iff_pos ht n hpos hv
  rw [← hf] at he
  exact he.trans (hc n hn)

end A165378Finish

-- Component: A165378Data

namespace A165378Data
open A165378Proof
abbrev Index := Fin 766

def decodeState (k : ℕ) : State where
  row := fun j => ⟨(k / 4 ^ j.val) % 4, Nat.mod_lt _ (by decide)⟩
  deg := fun j => (k / 4 ^ (4 + j.val)) % 4
  part := fun j => (k / 4 ^ (8 + j.val)) % 4
  done := fun j => k.testBit (24 + j.val)

def stateCode (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    12589376
                  else
                    10507600
                else
                  if i.val < 3 then
                    14681440
                  else
                    if i.val < 4 then
                      14681456
                    else
                      14942276
              else
                if i.val < 8 then
                  if i.val < 6 then
                    5530708
                  else
                    if i.val < 7 then
                      14942308
                    else
                      14942324
                else
                  if i.val < 9 then
                    14942280
                  else
                    if i.val < 10 then
                      10768472
                    else
                      13898856
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    14942328
                  else
                    if i.val < 13 then
                      14942284
                    else
                      10768476
                else
                  if i.val < 15 then
                    14942316
                  else
                    if i.val < 16 then
                      13898876
                    else
                      14947345
              else
                if i.val < 20 then
                  if i.val < 18 then
                    10773585
                  else
                    if i.val < 19 then
                      14947473
                    else
                      14947537
                else
                  if i.val < 21 then
                    29370773
                  else
                    if i.val < 22 then
                      29370837
                    else
                      27549785
          else
            if i.val < 35 then
              if i.val < 29 then
                if i.val < 26 then
                  if i.val < 24 then
                    31723673
                  else
                    if i.val < 25 then
                      31723737
                    else
                      27549789
                else
                  if i.val < 27 then
                    31723677
                  else
                    if i.val < 28 then
                      31723741
                    else
                      39086082
              else
                if i.val < 32 then
                  if i.val < 30 then
                    47454338
                  else
                    if i.val < 31 then
                      47454402
                    else
                      14947346
                else
                  if i.val < 33 then
                    10773586
                  else
                    if i.val < 34 then
                      14947474
                    else
                      14947538
            else
              if i.val < 41 then
                if i.val < 38 then
                  if i.val < 36 then
                    48497698
                  else
                    if i.val < 37 then
                      44324002
                    else
                      48497890
                else
                  if i.val < 39 then
                    48497714
                  else
                    if i.val < 40 then
                      48497842
                    else
                      44324082
              else
                if i.val < 44 then
                  if i.val < 42 then
                    30680214
                  else
                    if i.val < 43 then
                      30680278
                    else
                      27288922
                else
                  if i.val < 45 then
                    31462810
                  else
                    if i.val < 46 then
                      31462874
                    else
                      50358698
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    62921194
                  else
                    if i.val < 49 then
                      65013178
                    else
                      60839418
                else
                  if i.val < 51 then
                    27549790
                  else
                    if i.val < 52 then
                      31723678
                    else
                      31723742
              else
                if i.val < 56 then
                  if i.val < 54 then
                    61100206
                  else
                    if i.val < 55 then
                      65274094
                    else
                      64230590
                else
                  if i.val < 57 then
                    55862526
                  else
                    if i.val < 58 then
                      39086083
                    else
                      47454339
            else
              if i.val < 65 then
                if i.val < 62 then
                  if i.val < 60 then
                    47454403
                  else
                    if i.val < 61 then
                      14947347
                    else
                      10773587
                else
                  if i.val < 63 then
                    14947475
                  else
                    if i.val < 64 then
                      14947539
                    else
                      48497699
              else
                if i.val < 68 then
                  if i.val < 66 then
                    44324003
                  else
                    if i.val < 67 then
                      48497891
                    else
                      48497715
                else
                  if i.val < 69 then
                    48497843
                  else
                    if i.val < 70 then
                      44324083
                    else
                      30680215
          else
            if i.val < 83 then
              if i.val < 77 then
                if i.val < 74 then
                  if i.val < 72 then
                    30680279
                  else
                    if i.val < 73 then
                      27549787
                    else
                      31723675
                else
                  if i.val < 75 then
                    31723739
                  else
                    if i.val < 76 then
                      55862443
                    else
                      64230635
              else
                if i.val < 80 then
                  if i.val < 78 then
                    65274043
                  else
                    if i.val < 79 then
                      61100283
                    else
                      27288927
                else
                  if i.val < 81 then
                    31462815
                  else
                    if i.val < 82 then
                      31462879
                    else
                      60839343
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    65013231
                  else
                    if i.val < 85 then
                      62921151
                    else
                      50358783
                else
                  if i.val < 87 then
                    33581568
                  else
                    if i.val < 88 then
                      46144128
                    else
                      46144192
              else
                if i.val < 92 then
                  if i.val < 90 then
                    14685712
                  else
                    if i.val < 91 then
                      10511952
                    else
                      14685840
                else
                  if i.val < 93 then
                    14685904
                  else
                    if i.val < 94 then
                      48236064
                    else
                      44062368
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    48236256
                  else
                    if i.val < 97 then
                      48236080
                    else
                      48236208
                else
                  if i.val < 99 then
                    44062448
                  else
                    if i.val < 100 then
                      10769668
                    else
                      14943556
              else
                if i.val < 104 then
                  if i.val < 102 then
                    14943620
                  else
                    if i.val < 103 then
                      14943684
                    else
                      13904148
                else
                  if i.val < 105 then
                    13904276
                  else
                    if i.val < 106 then
                      13904340
                    else
                      14943524
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    14943588
                  else
                    if i.val < 109 then
                      10769828
                    else
                      14943716
                else
                  if i.val < 111 then
                    14943540
                  else
                    if i.val < 112 then
                      14943604
                    else
                      14943668
              else
                if i.val < 116 then
                  if i.val < 114 then
                    10769908
                  else
                    if i.val < 115 then
                      44323080
                    else
                      48497032
                else
                  if i.val < 117 then
                    48497096
                  else
                    if i.val < 118 then
                      14946584
                    else
                      10772824
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    14946712
                  else
                    if i.val < 121 then
                      14946776
                    else
                      47453480
                else
                  if i.val < 123 then
                    39085480
                  else
                    if i.val < 124 then
                      47453672
                    else
                      48496952
              else
                if i.val < 128 then
                  if i.val < 126 then
                    48497080
                  else
                    if i.val < 127 then
                      44323320
                    else
                      44323084
                else
                  if i.val < 129 then
                    48497036
                  else
                    if i.val < 130 then
                      48497100
                    else
                      14946588
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    10772828
                  else
                    if i.val < 133 then
                      14946716
                    else
                      14946780
                else
                  if i.val < 135 then
                    48496940
                  else
                    if i.val < 136 then
                      44323244
                    else
                      48497132
              else
                if i.val < 140 then
                  if i.val < 138 then
                    47453500
                  else
                    if i.val < 139 then
                      47453628
                    else
                      39085564
                else
                  if i.val < 141 then
                    31459685
                  else
                    if i.val < 142 then
                      27285925
                    else
                      31459813
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    31459701
                  else
                    if i.val < 145 then
                      31459765
                    else
                      27286005
                else
                  if i.val < 147 then
                    30681238
                  else
                    if i.val < 148 then
                      30681302
                    else
                      31720550
              else
                if i.val < 152 then
                  if i.val < 150 then
                    27546790
                  else
                    if i.val < 151 then
                      31720678
                    else
                      31720566
                else
                  if i.val < 153 then
                    31720630
                  else
                    if i.val < 154 then
                      27546870
                    else
                      30681239
            else
              if i.val < 161 then
                if i.val < 158 then
                  if i.val < 156 then
                    30681303
                  else
                    if i.val < 157 then
                      31720551
                    else
                      27546791
                else
                  if i.val < 159 then
                    31720679
                  else
                    if i.val < 160 then
                      31720567
                    else
                      31720631
              else
                if i.val < 164 then
                  if i.val < 162 then
                    27546871
                  else
                    if i.val < 163 then
                      100690432
                    else
                      113253056
                else
                  if i.val < 165 then
                    81794576
                  else
                    if i.val < 166 then
                      77620816
                    else
                      81794768
          else
            if i.val < 179 then
              if i.val < 173 then
                if i.val < 170 then
                  if i.val < 168 then
                    115344944
                  else
                    if i.val < 169 then
                      111171312
                    else
                      81011988
                else
                  if i.val < 171 then
                    81012180
                  else
                    if i.val < 172 then
                      44324104
                    else
                      48498056
              else
                if i.val < 176 then
                  if i.val < 174 then
                    48498120
                  else
                    if i.val < 175 then
                      14947608
                    else
                      10773848
                else
                  if i.val < 177 then
                    14947736
                  else
                    if i.val < 178 then
                      14947800
                    else
                      47454504
            else
              if i.val < 185 then
                if i.val < 182 then
                  if i.val < 180 then
                    39086504
                  else
                    if i.val < 181 then
                      47454696
                    else
                      48497976
                else
                  if i.val < 183 then
                    48498104
                  else
                    if i.val < 184 then
                      44324344
                    else
                      111431948
              else
                if i.val < 188 then
                  if i.val < 186 then
                    115605964
                  else
                    if i.val < 187 then
                      82055452
                    else
                      77881692
                else
                  if i.val < 189 then
                    82055644
                  else
                    if i.val < 190 then
                      114562364
                    else
                      106194428
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            if i.val < 203 then
              if i.val < 197 then
                if i.val < 194 then
                  if i.val < 192 then
                    96479701
                  else
                    if i.val < 193 then
                      27550809
                    else
                      31724697
                else
                  if i.val < 195 then
                    31724761
                  else
                    if i.val < 196 then
                      94658653
                    else
                      98832605
              else
                if i.val < 200 then
                  if i.val < 198 then
                    27289946
                  else
                    if i.val < 199 then
                      31463834
                    else
                      31463898
                else
                  if i.val < 201 then
                    65014202
                  else
                    if i.val < 202 then
                      60840442
                    else
                      97789143
            else
              if i.val < 209 then
                if i.val < 206 then
                  if i.val < 204 then
                    27550811
                  else
                    if i.val < 205 then
                      31724699
                    else
                      31724763
                else
                  if i.val < 207 then
                    55863467
                  else
                    if i.val < 208 then
                      64231659
                    else
                      65275067
              else
                if i.val < 212 then
                  if i.val < 210 then
                    61101307
                  else
                    if i.val < 211 then
                      94397791
                    else
                      98571743
                else
                  if i.val < 213 then
                    117467647
                  else
                    if i.val < 214 then
                      167799296
                    else
                      180361856
          else
            if i.val < 227 then
              if i.val < 221 then
                if i.val < 218 then
                  if i.val < 216 then
                    148903440
                  else
                    if i.val < 217 then
                      144729680
                    else
                      148903568
                else
                  if i.val < 219 then
                    182453792
                  else
                    if i.val < 220 then
                      178280096
                    else
                      148120852
              else
                if i.val < 224 then
                  if i.val < 222 then
                    148120980
                  else
                    if i.val < 223 then
                      178540808
                    else
                      182714760
                else
                  if i.val < 225 then
                    149164312
                  else
                    if i.val < 226 then
                      144990552
                    else
                      149164440
            else
              if i.val < 233 then
                if i.val < 230 then
                  if i.val < 228 then
                    181671208
                  else
                    if i.val < 229 then
                      173303208
                    else
                      44324108
                else
                  if i.val < 231 then
                    48498060
                  else
                    if i.val < 232 then
                      48498124
                    else
                      14947612
              else
                if i.val < 236 then
                  if i.val < 234 then
                    10773852
                  else
                    if i.val < 235 then
                      14947740
                    else
                      14947804
                else
                  if i.val < 237 then
                    48497964
                  else
                    if i.val < 238 then
                      44324268
                    else
                      48498156
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    47454524
                  else
                    if i.val < 241 then
                      47454652
                    else
                      39086588
                else
                  if i.val < 243 then
                    163588501
                  else
                    if i.val < 244 then
                      161767513
                    else
                      165941401
              else
                if i.val < 248 then
                  if i.val < 246 then
                    27550813
                  else
                    if i.val < 247 then
                      31724701
                    else
                      31724765
                else
                  if i.val < 249 then
                    164897942
                  else
                    if i.val < 250 then
                      161506650
                    else
                      165680538
            else
              if i.val < 257 then
                if i.val < 254 then
                  if i.val < 252 then
                    184576426
                  else
                    if i.val < 253 then
                      27550814
                    else
                      31724702
                else
                  if i.val < 255 then
                    31724766
                  else
                    if i.val < 256 then
                      61101230
                    else
                      65275118
              else
                if i.val < 260 then
                  if i.val < 258 then
                    64231614
                  else
                    if i.val < 259 then
                      55863550
                    else
                      27289951
                else
                  if i.val < 261 then
                    31463839
                  else
                    if i.val < 262 then
                      31463903
                    else
                      60840367
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    65014255
                  else
                    if i.val < 265 then
                      17064281
                    else
                      29626777
                else
                  if i.val < 267 then
                    29626841
                  else
                    if i.val < 268 then
                      30676329
                    else
                      22308265
              else
                if i.val < 272 then
                  if i.val < 270 then
                    30676457
                  else
                    if i.val < 271 then
                      31719801
                    else
                      31719865
                else
                  if i.val < 273 then
                    27546105
                  else
                    if i.val < 274 then
                      17064285
                    else
                      29626781
            else
              if i.val < 281 then
                if i.val < 278 then
                  if i.val < 276 then
                    29626845
                  else
                    if i.val < 277 then
                      31719789
                    else
                      27546029
                else
                  if i.val < 279 then
                    31719917
                  else
                    if i.val < 280 then
                      30676349
                    else
                      30676413
              else
                if i.val < 284 then
                  if i.val < 282 then
                    22308349
                  else
                    if i.val < 283 then
                      96479957
                    else
                      27551065
                else
                  if i.val < 285 then
                    31724953
                  else
                    if i.val < 286 then
                      31725017
                    else
                      94658909
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              if i.val < 293 then
                if i.val < 290 then
                  if i.val < 288 then
                    98832861
                  else
                    if i.val < 289 then
                      163588757
                    else
                      161767769
                else
                  if i.val < 291 then
                    165941657
                  else
                    if i.val < 292 then
                      27551069
                    else
                      31724957
              else
                if i.val < 296 then
                  if i.val < 294 then
                    31725021
                  else
                    if i.val < 295 then
                      98568565
                    else
                      94394869
                else
                  if i.val < 297 then
                    30681494
                  else
                    if i.val < 298 then
                      30681558
                    else
                      31720806
            else
              if i.val < 305 then
                if i.val < 302 then
                  if i.val < 300 then
                    27547046
                  else
                    if i.val < 301 then
                      31720934
                    else
                      31720822
                else
                  if i.val < 303 then
                    31720886
                  else
                    if i.val < 304 then
                      27547126
                    else
                      27289178
              else
                if i.val < 308 then
                  if i.val < 306 then
                    31463066
                  else
                    if i.val < 307 then
                      31463130
                    else
                      50358954
                else
                  if i.val < 309 then
                    62921450
                  else
                    if i.val < 310 then
                      65013434
                    else
                      60839674
          else
            if i.val < 323 then
              if i.val < 317 then
                if i.val < 314 then
                  if i.val < 312 then
                    27550046
                  else
                    if i.val < 313 then
                      31723934
                    else
                      31723998
                else
                  if i.val < 315 then
                    61100462
                  else
                    if i.val < 316 then
                      65274350
                    else
                      64230846
              else
                if i.val < 320 then
                  if i.val < 318 then
                    55862782
                  else
                    if i.val < 319 then
                      97790167
                    else
                      98829431
                else
                  if i.val < 321 then
                    94655735
                  else
                    if i.val < 322 then
                      30680470
                    else
                      30680534
            else
              if i.val < 329 then
                if i.val < 326 then
                  if i.val < 324 then
                    27290202
                  else
                    if i.val < 325 then
                      31464090
                    else
                      31464154
                else
                  if i.val < 327 then
                    65014458
                  else
                    if i.val < 328 then
                      60840698
                    else
                      94659677
              else
                if i.val < 332 then
                  if i.val < 330 then
                    98833629
                  else
                    if i.val < 331 then
                      164898198
                    else
                      161506906
                else
                  if i.val < 333 then
                    165680794
                  else
                    if i.val < 334 then
                      184576682
                    else
                      27551070
        else
          if i.val < 359 then
            if i.val < 347 then
              if i.val < 341 then
                if i.val < 338 then
                  if i.val < 336 then
                    31724958
                  else
                    if i.val < 337 then
                      31725022
                    else
                      61101486
                else
                  if i.val < 339 then
                    65275374
                  else
                    if i.val < 340 then
                      64231870
                    else
                      55863806
              else
                if i.val < 344 then
                  if i.val < 342 then
                    94398815
                  else
                    if i.val < 343 then
                      98572767
                    else
                      165677413
                else
                  if i.val < 345 then
                    161503653
                  else
                    if i.val < 346 then
                      164898966
                    else
                      165938278
            else
              if i.val < 353 then
                if i.val < 350 then
                  if i.val < 348 then
                    161764518
                  else
                    if i.val < 349 then
                      30681495
                    else
                      30681559
                else
                  if i.val < 351 then
                    31720807
                  else
                    if i.val < 352 then
                      27547047
                    else
                      31720935
              else
                if i.val < 356 then
                  if i.val < 354 then
                    31720823
                  else
                    if i.val < 355 then
                      31720887
                    else
                      27547127
                else
                  if i.val < 357 then
                    27550043
                  else
                    if i.val < 358 then
                      31723931
                    else
                      31723995
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  if i.val < 360 then
                    55862699
                  else
                    if i.val < 361 then
                      64230891
                    else
                      65274299
                else
                  if i.val < 363 then
                    61100539
                  else
                    if i.val < 364 then
                      27289183
                    else
                      31463071
              else
                if i.val < 368 then
                  if i.val < 366 then
                    31463135
                  else
                    if i.val < 367 then
                      60839599
                    else
                      65013487
                else
                  if i.val < 369 then
                    62921407
                  else
                    if i.val < 370 then
                      50359039
                    else
                      161768537
            else
              if i.val < 377 then
                if i.val < 374 then
                  if i.val < 372 then
                    165942425
                  else
                    if i.val < 373 then
                      161507674
                    else
                      165681562
                else
                  if i.val < 375 then
                    97789399
                  else
                    if i.val < 376 then
                      27551067
                    else
                      31724955
              else
                if i.val < 380 then
                  if i.val < 378 then
                    31725019
                  else
                    if i.val < 379 then
                      55863723
                    else
                      64231915
                else
                  if i.val < 381 then
                    65275323
                  else
                    if i.val < 382 then
                      61101563
                    else
                      94398047
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              if i.val < 388 then
                if i.val < 385 then
                  if i.val < 384 then
                    98571999
                  else
                    117467903
                else
                  if i.val < 386 then
                    30680471
                  else
                    if i.val < 387 then
                      30680535
                    else
                      27290207
              else
                if i.val < 391 then
                  if i.val < 389 then
                    31464095
                  else
                    if i.val < 390 then
                      31464159
                    else
                      60840623
                else
                  if i.val < 392 then
                    65014511
                  else
                    if i.val < 393 then
                      62925290
                    else
                      61104302
            else
              if i.val < 400 then
                if i.val < 397 then
                  if i.val < 395 then
                    65278190
                  else
                    if i.val < 396 then
                      64234731
                    else
                      60843439
                else
                  if i.val < 398 then
                    65017327
                  else
                    if i.val < 399 then
                      65017274
                    else
                      60843514
              else
                if i.val < 403 then
                  if i.val < 401 then
                    64234686
                  else
                    if i.val < 402 then
                      65278139
                    else
                      61104379
                else
                  if i.val < 404 then
                    62925247
                  else
                    if i.val < 405 then
                      111174927
                    else
                      115348943
          else
            if i.val < 418 then
              if i.val < 412 then
                if i.val < 409 then
                  if i.val < 407 then
                    115610675
                  else
                    if i.val < 408 then
                      111437043
                    else
                      113257152
                else
                  if i.val < 410 then
                    77882628
                  else
                    if i.val < 411 then
                      82056516
                    else
                      82056644
              else
                if i.val < 415 then
                  if i.val < 413 then
                    111436044
                  else
                    if i.val < 414 then
                      115610060
                    else
                      234908160
                else
                  if i.val < 416 then
                    115349040
                  else
                    if i.val < 417 then
                      111175408
                    else
                      212096260
            else
              if i.val < 424 then
                if i.val < 421 then
                  if i.val < 419 then
                    216270148
                  else
                    if i.val < 420 then
                      215226644
                    else
                      206858580
                else
                  if i.val < 422 then
                    82056500
                  else
                    if i.val < 423 then
                      82056564
                    else
                      77882868
              else
                if i.val < 427 then
                  if i.val < 425 then
                    114566460
                  else
                    if i.val < 426 then
                      98572661
                    else
                      94398965
                else
                  if i.val < 428 then
                    98833527
                  else
                    if i.val < 429 then
                      94659831
                    else
                      111437068
        else
          if i.val < 454 then
            if i.val < 442 then
              if i.val < 436 then
                if i.val < 433 then
                  if i.val < 431 then
                    115611084
                  else
                    if i.val < 432 then
                      111432972
                    else
                      115606988
                else
                  if i.val < 434 then
                    114567484
                  else
                    if i.val < 435 then
                      97789309
                    else
                      31724902
              else
                if i.val < 439 then
                  if i.val < 437 then
                    27551142
                  else
                    if i.val < 438 then
                      31725030
                    else
                      62925546
                else
                  if i.val < 440 then
                    61104558
                  else
                    if i.val < 441 then
                      65278446
                    else
                      156526934
            else
              if i.val < 448 then
                if i.val < 445 then
                  if i.val < 443 then
                    164895126
                  else
                    if i.val < 444 then
                      165938534
                    else
                      161764774
                else
                  if i.val < 446 then
                    31724918
                  else
                    if i.val < 447 then
                      31724982
                    else
                      27551222
              else
                if i.val < 451 then
                  if i.val < 449 then
                    65017530
                  else
                    if i.val < 450 then
                      60843770
                    else
                      64234942
                else
                  if i.val < 452 then
                    65279163
                  else
                    if i.val < 453 then
                      61105403
                    else
                      61105582
          else
            if i.val < 466 then
              if i.val < 460 then
                if i.val < 457 then
                  if i.val < 455 then
                    65279470
                  else
                    if i.val < 456 then
                      64235966
                    else
                      98833783
                else
                  if i.val < 458 then
                    94660087
                  else
                    if i.val < 459 then
                      178283786
                    else
                      182457738
              else
                if i.val < 463 then
                  if i.val < 461 then
                    182719522
                  else
                    if i.val < 462 then
                      178545826
                    else
                      180365952
                else
                  if i.val < 464 then
                    144991492
                  else
                    if i.val < 465 then
                      149165380
                    else
                      149165444
            else
              if i.val < 472 then
                if i.val < 469 then
                  if i.val < 467 then
                    178544904
                  else
                    if i.val < 468 then
                      182718856
                    else
                      182457888
                else
                  if i.val < 470 then
                    178284192
                  else
                    if i.val < 471 then
                      149165348
                    else
                      149165412
              else
                if i.val < 475 then
                  if i.val < 473 then
                    144991652
                  else
                    if i.val < 474 then
                      181675304
                    else
                      165681509
                else
                  if i.val < 476 then
                    161507749
                  else
                    if i.val < 477 then
                      165942374
                    else
                      161768614
      else
        if i.val < 526 then
          if i.val < 502 then
            if i.val < 490 then
              if i.val < 484 then
                if i.val < 481 then
                  if i.val < 479 then
                    178545928
                  else
                    if i.val < 480 then
                      182719880
                    else
                      178541832
                else
                  if i.val < 482 then
                    182715784
                  else
                    if i.val < 483 then
                      181676328
                    else
                      164898153
              else
                if i.val < 487 then
                  if i.val < 485 then
                    165942630
                  else
                    if i.val < 486 then
                      161768870
                    else
                      89418071
                else
                  if i.val < 488 then
                    97786327
                  else
                    if i.val < 489 then
                      31724903
                    else
                      27551143
            else
              if i.val < 496 then
                if i.val < 493 then
                  if i.val < 491 then
                    31725031
                  else
                    if i.val < 492 then
                      98829687
                    else
                      94655991
                else
                  if i.val < 494 then
                    64234987
                  else
                    if i.val < 495 then
                      60843695
                    else
                      65017583
              else
                if i.val < 499 then
                  if i.val < 497 then
                    31724919
                  else
                    if i.val < 498 then
                      31724983
                    else
                      27551223
                else
                  if i.val < 500 then
                    65278395
                  else
                    if i.val < 501 then
                      61104635
                    else
                      62925503
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  if i.val < 503 then
                    64236011
                  else
                    if i.val < 504 then
                      65279419
                    else
                      61105659
                else
                  if i.val < 506 then
                    61105326
                  else
                    if i.val < 507 then
                      65279214
                    else
                      44066058
              else
                if i.val < 511 then
                  if i.val < 509 then
                    48240010
                  else
                    if i.val < 510 then
                      48240074
                    else
                      44326926
                else
                  if i.val < 512 then
                    48500878
                  else
                    if i.val < 513 then
                      48500942
                    else
                      44326923
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    48500875
                  else
                    if i.val < 516 then
                      48500939
                    else
                      44066063
                else
                  if i.val < 518 then
                    48240015
                  else
                    if i.val < 519 then
                      48240079
                    else
                      48501794
              else
                if i.val < 523 then
                  if i.val < 521 then
                    44328098
                  else
                    if i.val < 522 then
                      48501986
                    else
                      106194947
                else
                  if i.val < 524 then
                    114563267
                  else
                    if i.val < 525 then
                      48501795
                    else
                      44328099
        else
          if i.val < 550 then
            if i.val < 538 then
              if i.val < 532 then
                if i.val < 529 then
                  if i.val < 527 then
                    48501987
                  else
                    if i.val < 528 then
                      115606579
                    else
                      111432947
                else
                  if i.val < 530 then
                    173303810
                  else
                    if i.val < 531 then
                      181672066
                    else
                      182715426
              else
                if i.val < 535 then
                  if i.val < 533 then
                    178541730
                  else
                    if i.val < 534 then
                      48501810
                    else
                      48501938
                else
                  if i.val < 536 then
                    44328178
                  else
                    if i.val < 537 then
                      48501811
                    else
                      48501939
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    44328179
                  else
                    if i.val < 540 then
                      46148224
                    else
                      46148288
                else
                  if i.val < 542 then
                    10773764
                  else
                    if i.val < 543 then
                      14947652
                    else
                      14947716
              else
                if i.val < 547 then
                  if i.val < 545 then
                    14947780
                  else
                    if i.val < 546 then
                      44327176
                    else
                      48501128
                else
                  if i.val < 548 then
                    48501192
                  else
                    if i.val < 549 then
                      44327180
                    else
                      48501132
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    48501196
                  else
                    if i.val < 552 then
                      48240160
                    else
                      44066464
                else
                  if i.val < 554 then
                    48240352
                  else
                    if i.val < 555 then
                      77878532
                    else
                      82052420
              else
                if i.val < 559 then
                  if i.val < 557 then
                    82052548
                  else
                    if i.val < 558 then
                      81008916
                    else
                      72640852
                else
                  if i.val < 560 then
                    81009108
                  else
                    if i.val < 561 then
                      14947620
                    else
                      14947684
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    10773924
                  else
                    if i.val < 564 then
                      14947812
                    else
                      82052404
                else
                  if i.val < 566 then
                    82052468
                  else
                    if i.val < 567 then
                      77878772
                    else
                      47457576
              else
                if i.val < 571 then
                  if i.val < 569 then
                    47457768
                  else
                    if i.val < 570 then
                      48501036
                    else
                      44327340
                else
                  if i.val < 572 then
                    48501228
                  else
                    if i.val < 573 then
                      31463781
                    else
                      27290021
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                if i.val < 577 then
                  if i.val < 575 then
                    31463909
                  else
                    if i.val < 576 then
                      31724646
                    else
                      27550886
                else
                  if i.val < 578 then
                    31724774
                  else
                    if i.val < 579 then
                      89417815
                    else
                      97786071
              else
                if i.val < 583 then
                  if i.val < 581 then
                    31724647
                  else
                    if i.val < 582 then
                      27550887
                    else
                      31724775
                else
                  if i.val < 584 then
                    48240176
                  else
                    if i.val < 585 then
                      48240304
                    else
                      44066544
            else
              if i.val < 592 then
                if i.val < 589 then
                  if i.val < 587 then
                    144987396
                  else
                    if i.val < 588 then
                      149161284
                    else
                      149161348
                else
                  if i.val < 590 then
                    148117780
                  else
                    if i.val < 591 then
                      139749716
                    else
                      148117908
              else
                if i.val < 595 then
                  if i.val < 593 then
                    149161252
                  else
                    if i.val < 594 then
                      149161316
                    else
                      144987556
                else
                  if i.val < 596 then
                    14947636
                  else
                    if i.val < 597 then
                      14947700
                    else
                      14947764
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    10774004
                  else
                    if i.val < 600 then
                      48501048
                    else
                      48501176
                else
                  if i.val < 602 then
                    44327416
                  else
                    if i.val < 603 then
                      47457596
                    else
                      47457724
              else
                if i.val < 607 then
                  if i.val < 605 then
                    31463797
                  else
                    if i.val < 606 then
                      31463861
                    else
                      27290101
                else
                  if i.val < 608 then
                    156526678
                  else
                    if i.val < 609 then
                      164894870
                    else
                      31724662
            else
              if i.val < 616 then
                if i.val < 613 then
                  if i.val < 611 then
                    31724726
                  else
                    if i.val < 612 then
                      27550966
                    else
                      31724663
                else
                  if i.val < 614 then
                    31724727
                  else
                    if i.val < 615 then
                      27550967
                    else
                      44328200
              else
                if i.val < 619 then
                  if i.val < 617 then
                    48502152
                  else
                    if i.val < 618 then
                      48502216
                    else
                      47458600
                else
                  if i.val < 620 then
                    47458792
                  else
                    if i.val < 621 then
                      64235755
                    else
                      181672232
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  if i.val < 623 then
                    173304232
                  else
                    if i.val < 624 then
                      48502072
                    else
                      48502200
                else
                  if i.val < 626 then
                    44328440
                  else
                    if i.val < 627 then
                      65018298
                    else
                      60844538
              else
                if i.val < 631 then
                  if i.val < 629 then
                    44328204
                  else
                    if i.val < 630 then
                      48502156
                    else
                      48502220
                else
                  if i.val < 632 then
                    48502060
                  else
                    if i.val < 633 then
                      44328364
                    else
                      48502252
            else
              if i.val < 640 then
                if i.val < 637 then
                  if i.val < 635 then
                    114563388
                  else
                    if i.val < 636 then
                      106195452
                    else
                      60844463
                else
                  if i.val < 638 then
                    65018351
                  else
                    if i.val < 639 then
                      47458620
                    else
                      47458748
              else
                if i.val < 643 then
                  if i.val < 641 then
                    64235710
                  else
                    if i.val < 642 then
                      83913301
                    else
                      96475861
                else
                  if i.val < 644 then
                    31463013
                  else
                    if i.val < 645 then
                      27289253
                    else
                      31463141
          else
            if i.val < 658 then
              if i.val < 652 then
                if i.val < 649 then
                  if i.val < 647 then
                    98567797
                  else
                    if i.val < 648 then
                      94394101
                    else
                      27546969
                else
                  if i.val < 650 then
                    31720857
                  else
                    if i.val < 651 then
                      31720921
                    else
                      30681449
              else
                if i.val < 655 then
                  if i.val < 653 then
                    30681577
                  else
                    if i.val < 654 then
                      31720825
                    else
                      31720889
                else
                  if i.val < 656 then
                    27547129
                  else
                    if i.val < 657 then
                      94654813
                    else
                      98828765
            else
              if i.val < 664 then
                if i.val < 661 then
                  if i.val < 659 then
                    31723885
                  else
                    if i.val < 660 then
                      27550125
                    else
                      31724013
                else
                  if i.val < 662 then
                    97785213
                  else
                    if i.val < 663 then
                      89417213
                    else
                      218131029
              else
                if i.val < 667 then
                  if i.val < 665 then
                    98571893
                  else
                    if i.val < 666 then
                      94398197
                    else
                      161764697
                else
                  if i.val < 668 then
                    165938585
                  else
                    if i.val < 669 then
                      164895081
                    else
                      156527017
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    31724921
                  else
                    if i.val < 672 then
                      31724985
                    else
                      27551225
                else
                  if i.val < 674 then
                    165680741
                  else
                    if i.val < 675 then
                      161506981
                    else
                      94655837
              else
                if i.val < 679 then
                  if i.val < 677 then
                    98829789
                  else
                    if i.val < 678 then
                      31724909
                    else
                      27551149
                else
                  if i.val < 680 then
                    31725037
                  else
                    if i.val < 681 then
                      97786237
                    else
                      89418237
            else
              if i.val < 688 then
                if i.val < 685 then
                  if i.val < 683 then
                    151022165
                  else
                    if i.val < 684 then
                      163584661
                    else
                      165676645
                else
                  if i.val < 686 then
                    161502885
                  else
                    if i.val < 687 then
                      31463029
                    else
                      31463093
              else
                if i.val < 691 then
                  if i.val < 689 then
                    27289333
                  else
                    if i.val < 690 then
                      161763673
                    else
                      165937561
                else
                  if i.val < 692 then
                    164894057
                  else
                    if i.val < 693 then
                      156525993
                    else
                      31723897
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    31723961
                  else
                    if i.val < 696 then
                      27550201
                    else
                      27546973
                else
                  if i.val < 698 then
                    31720861
                  else
                    if i.val < 699 then
                      31720925
                    else
                      31720813
              else
                if i.val < 703 then
                  if i.val < 701 then
                    27547053
                  else
                    if i.val < 702 then
                      31720941
                    else
                      30681469
                else
                  if i.val < 704 then
                    30681533
                  else
                    if i.val < 705 then
                      50618798
                    else
                      63181294
            else
              if i.val < 712 then
                if i.val < 709 then
                  if i.val < 707 then
                    65018554
                  else
                    if i.val < 708 then
                      60844794
                    else
                      60844719
                else
                  if i.val < 710 then
                    65018607
                  else
                    if i.val < 711 then
                      63181243
                    else
                      50618875
              else
                if i.val < 715 then
                  if i.val < 713 then
                    94659933
                  else
                    if i.val < 714 then
                      98833885
                    else
                      97790333
                else
                  if i.val < 716 then
                    161768793
                  else
                    if i.val < 717 then
                      165942681
                    else
                      164899177
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                if i.val < 721 then
                  if i.val < 719 then
                    111175183
                  else
                    if i.val < 720 then
                      115349199
                    else
                      115610931
                else
                  if i.val < 722 then
                    111437299
                  else
                    if i.val < 723 then
                      178284042
                    else
                      182457994
              else
                if i.val < 727 then
                  if i.val < 725 then
                    182719778
                  else
                    if i.val < 726 then
                      178546082
                    else
                      111435788
                else
                  if i.val < 728 then
                    115609804
                  else
                    if i.val < 729 then
                      44066314
                    else
                      48240266
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    48240330
                  else
                    if i.val < 732 then
                      44327182
                    else
                      48501134
                else
                  if i.val < 734 then
                    48501198
                  else
                    if i.val < 735 then
                      48502050
                    else
                      44328354
              else
                if i.val < 739 then
                  if i.val < 737 then
                    48502242
                  else
                    if i.val < 738 then
                      115349808
                    else
                      111176176
                else
                  if i.val < 740 then
                    173304066
                  else
                    if i.val < 741 then
                      181672322
                    else
                      182715682
          else
            if i.val < 754 then
              if i.val < 748 then
                if i.val < 745 then
                  if i.val < 743 then
                    178541986
                  else
                    if i.val < 744 then
                      48502066
                    else
                      48502194
                else
                  if i.val < 746 then
                    44328434
                  else
                    if i.val < 747 then
                      178544648
                    else
                      182718600
              else
                if i.val < 751 then
                  if i.val < 749 then
                    44327179
                  else
                    if i.val < 750 then
                      48501131
                    else
                      48501195
                else
                  if i.val < 752 then
                    44066319
                  else
                    if i.val < 753 then
                      48240271
                    else
                      48240335
            else
              if i.val < 760 then
                if i.val < 757 then
                  if i.val < 755 then
                    182458656
                  else
                    if i.val < 756 then
                      178284960
                    else
                      106195203
                else
                  if i.val < 758 then
                    114563523
                  else
                    if i.val < 759 then
                      48502051
                    else
                      44328355
              else
                if i.val < 763 then
                  if i.val < 761 then
                    48502243
                  else
                    if i.val < 762 then
                      115606835
                    else
                      111433203
                else
                  if i.val < 764 then
                    48502067
                  else
                    if i.val < 765 then
                      48502195
                    else
                      44328435

def state (i : Index) : State := decodeState (stateCode i)

def childrenList (i : Index) : List Index :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    ([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85] : List Index)
                  else
                    ([86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 22, 23, 24, 25, 26, 27, 146, 147, 148, 149, 150, 151, 152, 153, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 154, 155, 156, 157, 158, 159, 160, 161, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85] : List Index)
                else
                  if i.val < 3 then
                    ([162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212] : List Index)
                  else
                    if i.val < 4 then
                      ([213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 8 then
                  if i.val < 6 then
                    ([264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85] : List Index)
                  else
                    if i.val < 7 then
                      ([282, 283, 284, 285, 286, 287] : List Index)
                    else
                      ([288, 289, 290, 291, 292, 293] : List Index)
                else
                  if i.val < 9 then
                    ([] : List Index)
                  else
                    if i.val < 10 then
                      ([294, 295, 195, 196, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 210, 211, 212] : List Index)
                    else
                      ([191, 192, 193, 194, 195, 196, 321, 322, 323, 324, 325, 326, 327, 311, 312, 313, 314, 315, 316, 317, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212] : List Index)
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    ([328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342] : List Index)
                  else
                    if i.val < 13 then
                      ([] : List Index)
                    else
                      ([343, 344, 243, 244, 345, 346, 347, 249, 250, 251, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                else
                  if i.val < 15 then
                    ([370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384] : List Index)
                  else
                    if i.val < 16 then
                      ([242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 385, 386, 356, 357, 358, 359, 360, 361, 362, 387, 388, 389, 390, 391] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 20 then
                  ([] : List Index)
                else
                  if i.val < 21 then
                    ([392, 393, 394, 395, 396, 397, 212] : List Index)
                  else
                    if i.val < 22 then
                      ([251, 398, 399, 400, 401, 402, 403] : List Index)
                    else
                      ([] : List Index)
          else
            if i.val < 35 then
              if i.val < 29 then
                if i.val < 26 then
                  ([] : List Index)
                else
                  if i.val < 27 then
                    ([] : List Index)
                  else
                    if i.val < 28 then
                      ([] : List Index)
                    else
                      ([404, 405, 212] : List Index)
              else
                if i.val < 32 then
                  if i.val < 30 then
                    ([] : List Index)
                  else
                    if i.val < 31 then
                      ([406, 407] : List Index)
                    else
                      ([408, 409, 410, 411, 412, 413] : List Index)
                else
                  if i.val < 33 then
                    ([162, 163, 164, 165, 166, 167, 168, 184, 185, 186, 187, 188, 189, 190, 195, 196, 210, 211, 212] : List Index)
                  else
                    if i.val < 34 then
                      ([] : List Index)
                    else
                      ([414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428] : List Index)
            else
              if i.val < 41 then
                if i.val < 38 then
                  ([] : List Index)
                else
                  if i.val < 39 then
                    ([429, 430] : List Index)
                  else
                    if i.val < 40 then
                      ([] : List Index)
                    else
                      ([414, 415, 416, 431, 432, 433] : List Index)
              else
                if i.val < 44 then
                  if i.val < 42 then
                    ([] : List Index)
                  else
                    if i.val < 43 then
                      ([434] : List Index)
                    else
                      ([195, 196, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 210, 211, 212] : List Index)
                else
                  if i.val < 45 then
                    ([435, 436, 437, 438, 439, 440] : List Index)
                  else
                    if i.val < 46 then
                      ([425, 426, 441, 442, 443, 444, 445, 446, 447, 333, 448, 449, 450, 427, 428] : List Index)
                    else
                      ([396, 397, 212] : List Index)
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    ([451, 452] : List Index)
                  else
                    if i.val < 49 then
                      ([453, 454] : List Index)
                    else
                      ([333, 448, 449, 337, 338, 455] : List Index)
                else
                  if i.val < 51 then
                    ([382, 383, 384] : List Index)
                  else
                    if i.val < 52 then
                      ([] : List Index)
                    else
                      ([456, 457] : List Index)
              else
                if i.val < 56 then
                  ([] : List Index)
                else
                  if i.val < 57 then
                    ([] : List Index)
                  else
                    if i.val < 58 then
                      ([458, 459, 251] : List Index)
                    else
                      ([460, 461] : List Index)
            else
              if i.val < 65 then
                if i.val < 62 then
                  if i.val < 60 then
                    ([] : List Index)
                  else
                    if i.val < 61 then
                      ([462, 463, 464, 465, 466, 467] : List Index)
                    else
                      ([213, 214, 215, 216, 217, 218, 219, 222, 223, 224, 225, 226, 227, 228, 243, 244, 249, 250, 251] : List Index)
                else
                  if i.val < 63 then
                    ([414, 468, 469, 417, 418, 419, 420, 470, 471, 472, 473, 474, 475, 476, 477] : List Index)
                  else
                    if i.val < 64 then
                      ([] : List Index)
                    else
                      ([478, 479] : List Index)
              else
                if i.val < 68 then
                  if i.val < 66 then
                    ([414, 468, 469, 480, 481, 482] : List Index)
                  else
                    ([] : List Index)
                else
                  if i.val < 69 then
                    ([] : List Index)
                  else
                    if i.val < 70 then
                      ([] : List Index)
                    else
                      ([483] : List Index)
          else
            if i.val < 83 then
              if i.val < 77 then
                if i.val < 74 then
                  if i.val < 72 then
                    ([] : List Index)
                  else
                    if i.val < 73 then
                      ([331, 332, 333] : List Index)
                    else
                      ([484, 485] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 80 then
                  if i.val < 78 then
                    ([] : List Index)
                  else
                    if i.val < 79 then
                      ([] : List Index)
                    else
                      ([243, 244, 249, 250, 251, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                else
                  if i.val < 81 then
                    ([474, 475, 476, 477, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 384] : List Index)
                  else
                    if i.val < 82 then
                      ([496, 497, 498, 499, 500, 501] : List Index)
                    else
                      ([502, 380, 381, 494, 495, 384] : List Index)
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    ([503, 504] : List Index)
                  else
                    if i.val < 85 then
                      ([505, 506] : List Index)
                    else
                      ([251, 398, 399] : List Index)
                else
                  if i.val < 87 then
                    ([507, 508, 509, 46, 47, 48, 49, 510, 511, 512, 53, 54, 55, 56, 513, 514, 515, 75, 76, 77, 78, 516, 517, 518, 82, 83, 84, 85] : List Index)
                  else
                    if i.val < 88 then
                      ([519, 520, 521, 392, 393, 394, 522, 523, 524, 525, 526, 527, 528, 395, 396, 397, 212] : List Index)
                    else
                      ([529, 530, 531, 532, 533, 534, 535, 251, 398, 399, 400, 536, 537, 538, 401, 402, 403] : List Index)
              else
                if i.val < 92 then
                  if i.val < 90 then
                    ([539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550] : List Index)
                  else
                    if i.val < 91 then
                      ([86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 22, 23, 24, 25, 26, 27, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85] : List Index)
                    else
                      ([162, 163, 551, 552, 553, 167, 168, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 184, 185, 569, 570, 571, 189, 190, 572, 573, 574, 294, 295, 575, 576, 577, 392, 393, 394, 578, 579, 580, 581, 582, 319, 320, 395, 396, 397, 212] : List Index)
                else
                  if i.val < 93 then
                    ([213, 214, 218, 219, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 222, 223, 227, 228, 599, 600, 601, 602, 603, 343, 344, 604, 605, 606, 607, 608, 346, 347, 609, 610, 611, 251, 398, 399, 400, 612, 613, 614, 401, 402, 403] : List Index)
                  else
                    if i.val < 94 then
                      ([408, 615, 616, 617, 412, 413] : List Index)
                    else
                      ([162, 163, 551, 552, 553, 167, 168, 171, 172, 173, 618, 619, 181, 182, 183, 184, 185, 569, 570, 571, 189, 190, 200, 201, 393, 394, 620, 208, 209, 396, 397, 212] : List Index)
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    ([414, 415, 416, 480, 481, 621, 622, 623, 624, 625, 424, 626, 627, 451, 452] : List Index)
                  else
                    if i.val < 97 then
                      ([462, 466, 467, 628, 629, 630] : List Index)
                    else
                      ([414, 468, 469, 473, 431, 432, 631, 632, 633, 634, 635, 505, 506, 636, 637] : List Index)
                else
                  if i.val < 99 then
                    ([213, 214, 218, 219, 583, 584, 585, 222, 223, 227, 228, 599, 600, 601, 229, 230, 231, 236, 237, 238, 638, 639, 251, 398, 399, 255, 256, 640, 401, 402, 262, 263] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 104 then
                  ([] : List Index)
                else
                  if i.val < 105 then
                    ([392, 393, 394, 395, 396, 397, 212] : List Index)
                  else
                    if i.val < 106 then
                      ([251, 398, 399, 400, 401, 402, 403] : List Index)
                    else
                      ([] : List Index)
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    ([282, 283, 284, 285, 286, 287] : List Index)
                  else
                    if i.val < 109 then
                      ([641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 200, 201, 393, 394, 620, 208, 209, 396, 397, 212] : List Index)
                    else
                      ([663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 434, 626, 627, 451, 452] : List Index)
                else
                  if i.val < 111 then
                    ([] : List Index)
                  else
                    if i.val < 112 then
                      ([288, 289, 290, 291, 292, 293] : List Index)
                    else
                      ([663, 673, 674, 483, 675, 676, 677, 678, 679, 680, 681, 505, 506, 636, 637] : List Index)
              else
                if i.val < 116 then
                  if i.val < 114 then
                    ([682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 251, 398, 399, 255, 256, 640, 401, 402, 262, 263] : List Index)
                  else
                    ([] : List Index)
                else
                  if i.val < 117 then
                    ([] : List Index)
                  else
                    if i.val < 118 then
                      ([] : List Index)
                    else
                      ([195, 196, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 210, 211, 212] : List Index)
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    ([435, 436, 437, 438, 439, 440] : List Index)
                  else
                    if i.val < 121 then
                      ([425, 426, 441, 442, 443, 444, 445, 446, 447, 333, 448, 449, 450, 427, 428] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 123 then
                    ([704, 705, 316, 317, 396, 397, 212] : List Index)
                  else
                    if i.val < 124 then
                      ([706, 707, 450, 451, 452] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 128 then
                  if i.val < 126 then
                    ([453, 454] : List Index)
                  else
                    if i.val < 127 then
                      ([333, 448, 449, 337, 338, 455] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    ([243, 244, 249, 250, 251, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                  else
                    if i.val < 133 then
                      ([474, 475, 476, 477, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 384] : List Index)
                    else
                      ([496, 497, 498, 499, 500, 501] : List Index)
                else
                  if i.val < 135 then
                    ([] : List Index)
                  else
                    if i.val < 136 then
                      ([502, 380, 381, 494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
              else
                if i.val < 140 then
                  if i.val < 138 then
                    ([] : List Index)
                  else
                    if i.val < 139 then
                      ([505, 506, 493, 708, 709] : List Index)
                    else
                      ([251, 398, 399, 359, 360, 710, 711] : List Index)
                else
                  if i.val < 141 then
                    ([] : List Index)
                  else
                    if i.val < 142 then
                      ([200, 201, 393, 394, 620, 208, 209, 396, 397, 212] : List Index)
                    else
                      ([626, 627, 451, 452] : List Index)
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    ([] : List Index)
                  else
                    if i.val < 145 then
                      ([505, 506, 636, 637] : List Index)
                    else
                      ([251, 398, 399, 255, 256, 640, 401, 402, 262, 263] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 152 then
                  if i.val < 150 then
                    ([] : List Index)
                  else
                    if i.val < 151 then
                      ([] : List Index)
                    else
                      ([712, 713] : List Index)
                else
                  if i.val < 153 then
                    ([] : List Index)
                  else
                    if i.val < 154 then
                      ([663, 664, 665, 675, 676, 714] : List Index)
                    else
                      ([] : List Index)
            else
              if i.val < 161 then
                if i.val < 158 then
                  if i.val < 156 then
                    ([] : List Index)
                  else
                    if i.val < 157 then
                      ([715, 716] : List Index)
                    else
                      ([663, 673, 674, 666, 667, 717] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 164 then
                  if i.val < 162 then
                    ([] : List Index)
                  else
                    if i.val < 163 then
                      ([404, 405, 212] : List Index)
                    else
                      ([406, 407] : List Index)
                else
                  if i.val < 165 then
                    ([408, 409, 410, 411, 412, 413] : List Index)
                  else
                    if i.val < 166 then
                      ([162, 163, 164, 165, 166, 167, 168, 184, 185, 186, 187, 188, 189, 190, 195, 196, 210, 211, 212] : List Index)
                    else
                      ([414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428] : List Index)
          else
            if i.val < 179 then
              if i.val < 173 then
                if i.val < 170 then
                  if i.val < 168 then
                    ([429, 430] : List Index)
                  else
                    if i.val < 169 then
                      ([414, 415, 416, 431, 432, 433] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 171 then
                    ([434] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 176 then
                  if i.val < 174 then
                    ([] : List Index)
                  else
                    if i.val < 175 then
                      ([] : List Index)
                    else
                      ([195, 196, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 210, 211, 212] : List Index)
                else
                  if i.val < 177 then
                    ([435, 436, 437, 438, 439, 440] : List Index)
                  else
                    if i.val < 178 then
                      ([425, 426, 441, 442, 443, 444, 445, 446, 447, 333, 448, 449, 450, 427, 428] : List Index)
                    else
                      ([] : List Index)
            else
              if i.val < 185 then
                if i.val < 182 then
                  if i.val < 180 then
                    ([396, 397, 212] : List Index)
                  else
                    if i.val < 181 then
                      ([451, 452] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 183 then
                    ([453, 454] : List Index)
                  else
                    if i.val < 184 then
                      ([333, 448, 449, 337, 338, 455] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 188 then
                  if i.val < 186 then
                    ([] : List Index)
                  else
                    if i.val < 187 then
                      ([] : List Index)
                    else
                      ([382, 383, 384] : List Index)
                else
                  if i.val < 189 then
                    ([456, 457] : List Index)
                  else
                    ([] : List Index)
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            if i.val < 203 then
              if i.val < 197 then
                ([] : List Index)
              else
                if i.val < 200 then
                  if i.val < 198 then
                    ([195, 196, 210, 211, 212] : List Index)
                  else
                    if i.val < 199 then
                      ([] : List Index)
                    else
                      ([425, 426, 427, 428] : List Index)
                else
                  ([] : List Index)
            else
              if i.val < 209 then
                if i.val < 206 then
                  if i.val < 204 then
                    ([331, 332, 333] : List Index)
                  else
                    if i.val < 205 then
                      ([484, 485] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 212 then
                  if i.val < 210 then
                    ([] : List Index)
                  else
                    if i.val < 211 then
                      ([382, 383, 384] : List Index)
                    else
                      ([456, 457] : List Index)
                else
                  if i.val < 213 then
                    ([] : List Index)
                  else
                    if i.val < 214 then
                      ([458, 459, 251] : List Index)
                    else
                      ([460, 461] : List Index)
          else
            if i.val < 227 then
              if i.val < 221 then
                if i.val < 218 then
                  if i.val < 216 then
                    ([462, 463, 464, 465, 466, 467] : List Index)
                  else
                    if i.val < 217 then
                      ([213, 214, 215, 216, 217, 218, 219, 222, 223, 224, 225, 226, 227, 228, 243, 244, 249, 250, 251] : List Index)
                    else
                      ([414, 468, 469, 417, 418, 419, 420, 470, 471, 472, 473, 474, 475, 476, 477] : List Index)
                else
                  if i.val < 219 then
                    ([478, 479] : List Index)
                  else
                    if i.val < 220 then
                      ([414, 468, 469, 480, 481, 482] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 224 then
                  if i.val < 222 then
                    ([483] : List Index)
                  else
                    ([] : List Index)
                else
                  if i.val < 225 then
                    ([] : List Index)
                  else
                    if i.val < 226 then
                      ([331, 332, 333] : List Index)
                    else
                      ([484, 485] : List Index)
            else
              if i.val < 233 then
                ([] : List Index)
              else
                if i.val < 236 then
                  if i.val < 234 then
                    ([243, 244, 249, 250, 251, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                  else
                    if i.val < 235 then
                      ([474, 475, 476, 477, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 384] : List Index)
                    else
                      ([496, 497, 498, 499, 500, 501] : List Index)
                else
                  if i.val < 237 then
                    ([] : List Index)
                  else
                    if i.val < 238 then
                      ([502, 380, 381, 494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    ([] : List Index)
                  else
                    if i.val < 241 then
                      ([505, 506] : List Index)
                    else
                      ([251, 398, 399] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 248 then
                  ([] : List Index)
                else
                  if i.val < 249 then
                    ([] : List Index)
                  else
                    if i.val < 250 then
                      ([331, 332, 333] : List Index)
                    else
                      ([484, 485] : List Index)
            else
              if i.val < 257 then
                if i.val < 254 then
                  if i.val < 252 then
                    ([] : List Index)
                  else
                    if i.val < 253 then
                      ([382, 383, 384] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 255 then
                    ([456, 457] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 260 then
                  if i.val < 258 then
                    ([] : List Index)
                  else
                    if i.val < 259 then
                      ([] : List Index)
                    else
                      ([243, 244, 249, 250, 251] : List Index)
                else
                  if i.val < 261 then
                    ([474, 475, 476, 477] : List Index)
                  else
                    ([] : List Index)
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    ([] : List Index)
                  else
                    if i.val < 265 then
                      ([195, 196, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 210, 211, 212] : List Index)
                    else
                      ([435, 436, 437, 438, 439, 440] : List Index)
                else
                  if i.val < 267 then
                    ([425, 426, 441, 442, 443, 444, 445, 446, 447, 333, 448, 449, 450, 427, 428] : List Index)
                  else
                    if i.val < 268 then
                      ([] : List Index)
                    else
                      ([704, 705, 316, 317, 396, 397, 212] : List Index)
              else
                if i.val < 272 then
                  if i.val < 270 then
                    ([706, 707, 450, 451, 452] : List Index)
                  else
                    if i.val < 271 then
                      ([] : List Index)
                    else
                      ([453, 454] : List Index)
                else
                  if i.val < 273 then
                    ([333, 448, 449, 337, 338, 455] : List Index)
                  else
                    if i.val < 274 then
                      ([243, 244, 249, 250, 251, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                    else
                      ([474, 475, 476, 477, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 384] : List Index)
            else
              if i.val < 281 then
                if i.val < 278 then
                  if i.val < 276 then
                    ([496, 497, 498, 499, 500, 501] : List Index)
                  else
                    if i.val < 277 then
                      ([] : List Index)
                    else
                      ([502, 380, 381, 494, 495, 384] : List Index)
                else
                  if i.val < 279 then
                    ([503, 504] : List Index)
                  else
                    if i.val < 280 then
                      ([] : List Index)
                    else
                      ([505, 506, 493, 708, 709] : List Index)
              else
                if i.val < 284 then
                  if i.val < 282 then
                    ([251, 398, 399, 359, 360, 710, 711] : List Index)
                  else
                    ([] : List Index)
                else
                  ([] : List Index)
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              ([] : List Index)
            else
              if i.val < 305 then
                if i.val < 302 then
                  if i.val < 300 then
                    ([] : List Index)
                  else
                    if i.val < 301 then
                      ([] : List Index)
                    else
                      ([712, 713] : List Index)
                else
                  if i.val < 303 then
                    ([] : List Index)
                  else
                    if i.val < 304 then
                      ([663, 664, 665, 675, 676, 714] : List Index)
                    else
                      ([195, 196, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 210, 211, 212] : List Index)
              else
                if i.val < 308 then
                  if i.val < 306 then
                    ([435, 436, 437, 438, 439, 440] : List Index)
                  else
                    if i.val < 307 then
                      ([425, 426, 441, 442, 443, 444, 445, 446, 447, 333, 448, 449, 450, 427, 428] : List Index)
                    else
                      ([396, 397, 212] : List Index)
                else
                  if i.val < 309 then
                    ([451, 452] : List Index)
                  else
                    if i.val < 310 then
                      ([453, 454] : List Index)
                    else
                      ([333, 448, 449, 337, 338, 455] : List Index)
          else
            if i.val < 323 then
              if i.val < 317 then
                if i.val < 314 then
                  if i.val < 312 then
                    ([382, 383, 384] : List Index)
                  else
                    if i.val < 313 then
                      ([] : List Index)
                    else
                      ([456, 457] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 320 then
                  ([] : List Index)
                else
                  if i.val < 321 then
                    ([] : List Index)
                  else
                    if i.val < 322 then
                      ([] : List Index)
                    else
                      ([434] : List Index)
            else
              if i.val < 329 then
                if i.val < 326 then
                  if i.val < 324 then
                    ([195, 196, 210, 211, 212] : List Index)
                  else
                    if i.val < 325 then
                      ([] : List Index)
                    else
                      ([425, 426, 427, 428] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 332 then
                  if i.val < 330 then
                    ([] : List Index)
                  else
                    if i.val < 331 then
                      ([] : List Index)
                    else
                      ([331, 332, 333] : List Index)
                else
                  if i.val < 333 then
                    ([484, 485] : List Index)
                  else
                    if i.val < 334 then
                      ([] : List Index)
                    else
                      ([382, 383, 384] : List Index)
        else
          if i.val < 359 then
            if i.val < 347 then
              if i.val < 341 then
                if i.val < 338 then
                  if i.val < 336 then
                    ([] : List Index)
                  else
                    if i.val < 337 then
                      ([456, 457] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
              else
                ([] : List Index)
            else
              if i.val < 353 then
                if i.val < 350 then
                  ([] : List Index)
                else
                  if i.val < 351 then
                    ([715, 716] : List Index)
                  else
                    if i.val < 352 then
                      ([663, 673, 674, 666, 667, 717] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 356 then
                  ([] : List Index)
                else
                  if i.val < 357 then
                    ([331, 332, 333] : List Index)
                  else
                    if i.val < 358 then
                      ([484, 485] : List Index)
                    else
                      ([] : List Index)
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  ([] : List Index)
                else
                  if i.val < 363 then
                    ([] : List Index)
                  else
                    if i.val < 364 then
                      ([243, 244, 249, 250, 251, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369] : List Index)
                    else
                      ([474, 475, 476, 477, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 384] : List Index)
              else
                if i.val < 368 then
                  if i.val < 366 then
                    ([496, 497, 498, 499, 500, 501] : List Index)
                  else
                    if i.val < 367 then
                      ([502, 380, 381, 494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
                else
                  if i.val < 369 then
                    ([505, 506] : List Index)
                  else
                    if i.val < 370 then
                      ([251, 398, 399] : List Index)
                    else
                      ([] : List Index)
            else
              if i.val < 377 then
                if i.val < 374 then
                  ([] : List Index)
                else
                  if i.val < 375 then
                    ([] : List Index)
                  else
                    if i.val < 376 then
                      ([331, 332, 333] : List Index)
                    else
                      ([484, 485] : List Index)
              else
                if i.val < 380 then
                  ([] : List Index)
                else
                  if i.val < 381 then
                    ([] : List Index)
                  else
                    if i.val < 382 then
                      ([] : List Index)
                    else
                      ([382, 383, 384] : List Index)
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              if i.val < 388 then
                if i.val < 385 then
                  if i.val < 384 then
                    ([456, 457] : List Index)
                  else
                    ([] : List Index)
                else
                  if i.val < 386 then
                    ([483] : List Index)
                  else
                    if i.val < 387 then
                      ([] : List Index)
                    else
                      ([243, 244, 249, 250, 251] : List Index)
              else
                if i.val < 391 then
                  if i.val < 389 then
                    ([474, 475, 476, 477] : List Index)
                  else
                    ([] : List Index)
                else
                  ([] : List Index)
            else
              if i.val < 400 then
                if i.val < 397 then
                  if i.val < 395 then
                    ([] : List Index)
                  else
                    if i.val < 396 then
                      ([] : List Index)
                    else
                      ([494, 495, 384] : List Index)
                else
                  if i.val < 398 then
                    ([503, 504] : List Index)
                  else
                    if i.val < 399 then
                      ([453, 454] : List Index)
                    else
                      ([333, 448, 449] : List Index)
              else
                if i.val < 403 then
                  ([] : List Index)
                else
                  if i.val < 404 then
                    ([] : List Index)
                  else
                    if i.val < 405 then
                      ([718, 719, 384] : List Index)
                    else
                      ([720, 721] : List Index)
          else
            if i.val < 418 then
              if i.val < 412 then
                ([] : List Index)
              else
                if i.val < 415 then
                  ([] : List Index)
                else
                  if i.val < 416 then
                    ([429, 430] : List Index)
                  else
                    if i.val < 417 then
                      ([414, 415, 416] : List Index)
                    else
                      ([] : List Index)
            else
              if i.val < 424 then
                if i.val < 421 then
                  ([] : List Index)
                else
                  if i.val < 422 then
                    ([] : List Index)
                  else
                    if i.val < 423 then
                      ([712, 713] : List Index)
                    else
                      ([663, 664, 665] : List Index)
              else
                ([] : List Index)
        else
          if i.val < 454 then
            if i.val < 442 then
              ([] : List Index)
            else
              if i.val < 448 then
                if i.val < 445 then
                  ([] : List Index)
                else
                  if i.val < 446 then
                    ([712, 713] : List Index)
                  else
                    if i.val < 447 then
                      ([] : List Index)
                    else
                      ([663, 664, 665] : List Index)
              else
                if i.val < 451 then
                  if i.val < 449 then
                    ([453, 454] : List Index)
                  else
                    if i.val < 450 then
                      ([333, 448, 449] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
          else
            if i.val < 466 then
              if i.val < 460 then
                if i.val < 457 then
                  ([] : List Index)
                else
                  if i.val < 458 then
                    ([] : List Index)
                  else
                    if i.val < 459 then
                      ([722, 723, 333] : List Index)
                    else
                      ([724, 725] : List Index)
              else
                ([] : List Index)
            else
              if i.val < 472 then
                if i.val < 469 then
                  if i.val < 467 then
                    ([] : List Index)
                  else
                    if i.val < 468 then
                      ([] : List Index)
                    else
                      ([478, 479] : List Index)
                else
                  if i.val < 470 then
                    ([414, 468, 469] : List Index)
                  else
                    if i.val < 471 then
                      ([] : List Index)
                    else
                      ([715, 716] : List Index)
              else
                if i.val < 475 then
                  if i.val < 473 then
                    ([663, 673, 674] : List Index)
                  else
                    ([] : List Index)
                else
                  ([] : List Index)
      else
        if i.val < 526 then
          if i.val < 502 then
            if i.val < 490 then
              if i.val < 484 then
                ([] : List Index)
              else
                if i.val < 487 then
                  ([] : List Index)
                else
                  if i.val < 488 then
                    ([] : List Index)
                  else
                    if i.val < 489 then
                      ([715, 716] : List Index)
                    else
                      ([663, 673, 674] : List Index)
            else
              if i.val < 496 then
                if i.val < 493 then
                  ([] : List Index)
                else
                  if i.val < 494 then
                    ([] : List Index)
                  else
                    if i.val < 495 then
                      ([494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
              else
                ([] : List Index)
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  ([] : List Index)
                else
                  if i.val < 506 then
                    ([] : List Index)
                  else
                    if i.val < 507 then
                      ([] : List Index)
                    else
                      ([726, 727, 728, 729, 730, 307, 308, 309, 310, 731, 732, 733, 314, 315, 316, 317, 404, 405, 212] : List Index)
              else
                if i.val < 511 then
                  if i.val < 509 then
                    ([734, 735, 736, 438, 439, 440] : List Index)
                  else
                    if i.val < 510 then
                      ([737, 738, 739, 740, 741, 742, 743, 744, 745, 333, 448, 449, 450, 406, 407] : List Index)
                    else
                      ([718, 719, 384] : List Index)
                else
                  if i.val < 512 then
                    ([] : List Index)
                  else
                    if i.val < 513 then
                      ([720, 721] : List Index)
                    else
                      ([722, 723, 333] : List Index)
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    ([724, 725] : List Index)
                  else
                    if i.val < 516 then
                      ([] : List Index)
                    else
                      ([746, 747, 458, 459, 251, 748, 749, 750, 359, 360, 361, 362, 751, 752, 753, 366, 367, 368, 369] : List Index)
                else
                  if i.val < 518 then
                    ([754, 755, 460, 461, 756, 757, 758, 759, 760, 761, 762, 493, 494, 495, 384] : List Index)
                  else
                    if i.val < 519 then
                      ([763, 764, 765, 499, 500, 501] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 523 then
                  ([] : List Index)
                else
                  if i.val < 524 then
                    ([] : List Index)
                  else
                    if i.val < 525 then
                      ([478, 479] : List Index)
                    else
                      ([414, 468, 469] : List Index)
        else
          if i.val < 550 then
            if i.val < 538 then
              if i.val < 532 then
                ([] : List Index)
              else
                if i.val < 535 then
                  if i.val < 533 then
                    ([] : List Index)
                  else
                    if i.val < 534 then
                      ([429, 430] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 536 then
                    ([414, 415, 416] : List Index)
                  else
                    ([] : List Index)
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    ([] : List Index)
                  else
                    if i.val < 540 then
                      ([392, 393, 394, 395, 396, 397, 212] : List Index)
                    else
                      ([251, 398, 399, 400, 401, 402, 403] : List Index)
                else
                  ([] : List Index)
              else
                ([] : List Index)
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    ([] : List Index)
                  else
                    if i.val < 552 then
                      ([408, 615, 616, 617, 412, 413] : List Index)
                    else
                      ([162, 163, 551, 552, 553, 167, 168, 184, 185, 569, 570, 571, 189, 190, 393, 394, 396, 397, 212] : List Index)
                else
                  if i.val < 554 then
                    ([414, 415, 416, 480, 481, 621, 622, 623, 624, 625, 424, 626, 627, 451, 452] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 559 then
                  if i.val < 557 then
                    ([] : List Index)
                  else
                    if i.val < 558 then
                      ([] : List Index)
                    else
                      ([210, 211, 212] : List Index)
                else
                  if i.val < 560 then
                    ([427, 428] : List Index)
                  else
                    if i.val < 561 then
                      ([] : List Index)
                    else
                      ([282, 283, 284, 285, 286, 287] : List Index)
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    ([641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 393, 394, 396, 397, 212] : List Index)
                  else
                    if i.val < 564 then
                      ([663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 434, 626, 627, 451, 452] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 566 then
                    ([712, 713] : List Index)
                  else
                    if i.val < 567 then
                      ([663, 664, 665, 675, 676, 714] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 571 then
                  if i.val < 569 then
                    ([450] : List Index)
                  else
                    if i.val < 570 then
                      ([] : List Index)
                    else
                      ([494, 495, 384] : List Index)
                else
                  if i.val < 572 then
                    ([503, 504] : List Index)
                  else
                    if i.val < 573 then
                      ([] : List Index)
                    else
                      ([393, 394, 396, 397, 212] : List Index)
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                if i.val < 577 then
                  if i.val < 575 then
                    ([626, 627, 451, 452] : List Index)
                  else
                    ([] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 583 then
                  if i.val < 581 then
                    ([715, 716] : List Index)
                  else
                    if i.val < 582 then
                      ([663, 673, 674] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 584 then
                    ([462, 466, 467, 628, 629, 630] : List Index)
                  else
                    if i.val < 585 then
                      ([414, 468, 469, 473, 431, 432, 631, 632, 633, 634, 635, 505, 506, 636, 637] : List Index)
                    else
                      ([213, 214, 218, 219, 583, 584, 585, 222, 223, 227, 228, 599, 600, 601, 251, 398, 399, 401, 402] : List Index)
            else
              if i.val < 592 then
                if i.val < 589 then
                  ([] : List Index)
                else
                  if i.val < 590 then
                    ([] : List Index)
                  else
                    if i.val < 591 then
                      ([249, 250, 251] : List Index)
                    else
                      ([476, 477] : List Index)
              else
                if i.val < 595 then
                  if i.val < 593 then
                    ([] : List Index)
                  else
                    if i.val < 594 then
                      ([715, 716] : List Index)
                    else
                      ([663, 673, 674, 666, 667, 717] : List Index)
                else
                  if i.val < 596 then
                    ([] : List Index)
                  else
                    if i.val < 597 then
                      ([288, 289, 290, 291, 292, 293] : List Index)
                    else
                      ([663, 673, 674, 483, 675, 676, 677, 678, 679, 680, 681, 505, 506, 636, 637] : List Index)
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    ([682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 251, 398, 399, 401, 402] : List Index)
                  else
                    if i.val < 600 then
                      ([] : List Index)
                    else
                      ([453, 454] : List Index)
                else
                  if i.val < 602 then
                    ([333, 448, 449] : List Index)
                  else
                    if i.val < 603 then
                      ([] : List Index)
                    else
                      ([493] : List Index)
              else
                if i.val < 607 then
                  if i.val < 605 then
                    ([] : List Index)
                  else
                    if i.val < 606 then
                      ([505, 506, 636, 637] : List Index)
                    else
                      ([251, 398, 399, 401, 402] : List Index)
                else
                  if i.val < 608 then
                    ([] : List Index)
                  else
                    if i.val < 609 then
                      ([] : List Index)
                    else
                      ([712, 713] : List Index)
            else
              if i.val < 616 then
                if i.val < 613 then
                  if i.val < 611 then
                    ([] : List Index)
                  else
                    if i.val < 612 then
                      ([663, 664, 665] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
              else
                ([] : List Index)
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  if i.val < 623 then
                    ([] : List Index)
                  else
                    if i.val < 624 then
                      ([] : List Index)
                    else
                      ([453, 454] : List Index)
                else
                  if i.val < 626 then
                    ([333, 448, 449] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 631 then
                  ([] : List Index)
                else
                  if i.val < 632 then
                    ([] : List Index)
                  else
                    if i.val < 633 then
                      ([494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
            else
              if i.val < 640 then
                ([] : List Index)
              else
                if i.val < 643 then
                  if i.val < 641 then
                    ([] : List Index)
                  else
                    if i.val < 642 then
                      ([210, 211, 212] : List Index)
                    else
                      ([427, 428] : List Index)
                else
                  if i.val < 644 then
                    ([282, 283, 284, 285, 286, 287] : List Index)
                  else
                    if i.val < 645 then
                      ([641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 393, 394, 396, 397, 212] : List Index)
                    else
                      ([663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 434, 626, 627, 451, 452] : List Index)
          else
            if i.val < 658 then
              if i.val < 652 then
                if i.val < 649 then
                  if i.val < 647 then
                    ([712, 713] : List Index)
                  else
                    if i.val < 648 then
                      ([663, 664, 665, 675, 676, 714] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 655 then
                  if i.val < 653 then
                    ([] : List Index)
                  else
                    if i.val < 654 then
                      ([] : List Index)
                    else
                      ([453, 454] : List Index)
                else
                  if i.val < 656 then
                    ([333, 448, 449, 337, 338, 455] : List Index)
                  else
                    ([] : List Index)
            else
              if i.val < 664 then
                if i.val < 661 then
                  if i.val < 659 then
                    ([] : List Index)
                  else
                    if i.val < 660 then
                      ([494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 667 then
                  if i.val < 665 then
                    ([712, 713] : List Index)
                  else
                    if i.val < 666 then
                      ([663, 664, 665] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    ([] : List Index)
                  else
                    if i.val < 672 then
                      ([453, 454] : List Index)
                    else
                      ([333, 448, 449] : List Index)
                else
                  if i.val < 674 then
                    ([715, 716] : List Index)
                  else
                    if i.val < 675 then
                      ([663, 673, 674] : List Index)
                    else
                      ([] : List Index)
              else
                if i.val < 679 then
                  if i.val < 677 then
                    ([] : List Index)
                  else
                    if i.val < 678 then
                      ([] : List Index)
                    else
                      ([494, 495, 384] : List Index)
                else
                  if i.val < 680 then
                    ([503, 504] : List Index)
                  else
                    ([] : List Index)
            else
              if i.val < 688 then
                if i.val < 685 then
                  if i.val < 683 then
                    ([249, 250, 251] : List Index)
                  else
                    if i.val < 684 then
                      ([476, 477] : List Index)
                    else
                      ([715, 716] : List Index)
                else
                  if i.val < 686 then
                    ([663, 673, 674, 666, 667, 717] : List Index)
                  else
                    if i.val < 687 then
                      ([288, 289, 290, 291, 292, 293] : List Index)
                    else
                      ([663, 673, 674, 483, 675, 676, 677, 678, 679, 680, 681, 505, 506, 636, 637] : List Index)
              else
                if i.val < 691 then
                  if i.val < 689 then
                    ([682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 251, 398, 399, 401, 402] : List Index)
                  else
                    ([] : List Index)
                else
                  ([] : List Index)
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    ([453, 454] : List Index)
                  else
                    if i.val < 696 then
                      ([333, 448, 449] : List Index)
                    else
                      ([] : List Index)
                else
                  ([] : List Index)
              else
                if i.val < 703 then
                  if i.val < 701 then
                    ([502, 380, 381, 494, 495, 384] : List Index)
                  else
                    if i.val < 702 then
                      ([503, 504] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 704 then
                    ([] : List Index)
                  else
                    if i.val < 705 then
                      ([494, 495, 384] : List Index)
                    else
                      ([503, 504] : List Index)
            else
              if i.val < 712 then
                if i.val < 709 then
                  ([] : List Index)
                else
                  if i.val < 710 then
                    ([] : List Index)
                  else
                    if i.val < 711 then
                      ([453, 454] : List Index)
                    else
                      ([333, 448, 449] : List Index)
              else
                ([] : List Index)
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                if i.val < 721 then
                  if i.val < 719 then
                    ([718, 719, 384] : List Index)
                  else
                    if i.val < 720 then
                      ([720, 721] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 722 then
                    ([] : List Index)
                  else
                    if i.val < 723 then
                      ([722, 723, 333] : List Index)
                    else
                      ([724, 725] : List Index)
              else
                if i.val < 727 then
                  ([] : List Index)
                else
                  if i.val < 728 then
                    ([] : List Index)
                  else
                    if i.val < 729 then
                      ([726, 727, 728, 729, 730, 307, 308, 309, 310, 731, 732, 733, 314, 315, 316, 317, 404, 405, 212] : List Index)
                    else
                      ([734, 735, 736, 438, 439, 440] : List Index)
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    ([737, 738, 739, 740, 741, 742, 743, 744, 745, 333, 448, 449, 450, 406, 407] : List Index)
                  else
                    if i.val < 732 then
                      ([718, 719, 384] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 734 then
                    ([720, 721] : List Index)
                  else
                    ([] : List Index)
              else
                ([] : List Index)
          else
            if i.val < 754 then
              if i.val < 748 then
                if i.val < 745 then
                  if i.val < 743 then
                    ([] : List Index)
                  else
                    if i.val < 744 then
                      ([429, 430] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 746 then
                    ([414, 415, 416] : List Index)
                  else
                    ([] : List Index)
              else
                if i.val < 751 then
                  if i.val < 749 then
                    ([722, 723, 333] : List Index)
                  else
                    if i.val < 750 then
                      ([724, 725] : List Index)
                    else
                      ([] : List Index)
                else
                  if i.val < 752 then
                    ([746, 747, 458, 459, 251, 748, 749, 750, 359, 360, 361, 362, 751, 752, 753, 366, 367, 368, 369] : List Index)
                  else
                    if i.val < 753 then
                      ([754, 755, 460, 461, 756, 757, 758, 759, 760, 761, 762, 493, 494, 495, 384] : List Index)
                    else
                      ([763, 764, 765, 499, 500, 501] : List Index)
            else
              if i.val < 760 then
                if i.val < 757 then
                  ([] : List Index)
                else
                  if i.val < 758 then
                    ([] : List Index)
                  else
                    if i.val < 759 then
                      ([478, 479] : List Index)
                    else
                      ([414, 468, 469] : List Index)
              else
                ([] : List Index)

def children (i : Index) : Finset Index := (childrenList i).toFinset

def starts : Finset Index := ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List Index).toFinset

def final (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            0
          else
            if i.val < 35 then
              if i.val < 29 then
                0
              else
                if i.val < 32 then
                  if i.val < 30 then
                    0
                  else
                    if i.val < 31 then
                      1
                    else
                      0
                else
                  if i.val < 33 then
                    0
                  else
                    if i.val < 34 then
                      0
                    else
                      1
            else
              if i.val < 41 then
                if i.val < 38 then
                  0
                else
                  if i.val < 39 then
                    0
                  else
                    if i.val < 40 then
                      0
                    else
                      1
              else
                if i.val < 44 then
                  if i.val < 42 then
                    0
                  else
                    if i.val < 43 then
                      1
                    else
                      0
                else
                  if i.val < 45 then
                    0
                  else
                    if i.val < 46 then
                      1
                    else
                      0
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    1
                  else
                    if i.val < 49 then
                      0
                    else
                      1
                else
                  0
              else
                if i.val < 56 then
                  0
                else
                  if i.val < 57 then
                    1
                  else
                    0
            else
              0
          else
            0
      else
        if i.val < 143 then
          0
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  0
                else
                  if i.val < 147 then
                    0
                  else
                    if i.val < 148 then
                      1
                    else
                      0
              else
                if i.val < 152 then
                  0
                else
                  if i.val < 153 then
                    0
                  else
                    if i.val < 154 then
                      1
                    else
                      0
            else
              0
          else
            0
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            if i.val < 203 then
              if i.val < 197 then
                0
              else
                if i.val < 200 then
                  if i.val < 198 then
                    0
                  else
                    if i.val < 199 then
                      0
                    else
                      1
                else
                  if i.val < 201 then
                    0
                  else
                    if i.val < 202 then
                      1
                    else
                      0
            else
              0
          else
            0
        else
          if i.val < 263 then
            if i.val < 251 then
              0
            else
              if i.val < 257 then
                0
              else
                if i.val < 260 then
                  if i.val < 258 then
                    0
                  else
                    if i.val < 259 then
                      1
                    else
                      0
                else
                  0
          else
            0
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              if i.val < 293 then
                0
              else
                if i.val < 296 then
                  0
                else
                  if i.val < 297 then
                    0
                  else
                    if i.val < 298 then
                      1
                    else
                      0
            else
              if i.val < 305 then
                if i.val < 302 then
                  0
                else
                  if i.val < 303 then
                    0
                  else
                    if i.val < 304 then
                      1
                    else
                      0
              else
                if i.val < 308 then
                  if i.val < 306 then
                    0
                  else
                    if i.val < 307 then
                      1
                    else
                      0
                else
                  if i.val < 309 then
                    1
                  else
                    if i.val < 310 then
                      0
                    else
                      1
          else
            if i.val < 323 then
              if i.val < 317 then
                0
              else
                if i.val < 320 then
                  if i.val < 318 then
                    1
                  else
                    0
                else
                  if i.val < 321 then
                    0
                  else
                    if i.val < 322 then
                      0
                    else
                      1
            else
              if i.val < 329 then
                if i.val < 326 then
                  if i.val < 324 then
                    0
                  else
                    if i.val < 325 then
                      0
                    else
                      1
                else
                  if i.val < 327 then
                    0
                  else
                    if i.val < 328 then
                      1
                    else
                      0
              else
                0
        else
          if i.val < 359 then
            if i.val < 347 then
              if i.val < 341 then
                if i.val < 338 then
                  0
                else
                  if i.val < 339 then
                    0
                  else
                    if i.val < 340 then
                      0
                    else
                      1
              else
                0
            else
              0
          else
            0
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              if i.val < 388 then
                0
              else
                if i.val < 391 then
                  0
                else
                  if i.val < 392 then
                    0
                  else
                    if i.val < 393 then
                      1
                    else
                      0
            else
              if i.val < 400 then
                if i.val < 397 then
                  0
                else
                  if i.val < 398 then
                    0
                  else
                    if i.val < 399 then
                      0
                    else
                      1
              else
                0
          else
            0
        else
          if i.val < 454 then
            if i.val < 442 then
              if i.val < 436 then
                0
              else
                if i.val < 439 then
                  if i.val < 437 then
                    0
                  else
                    if i.val < 438 then
                      0
                    else
                      1
                else
                  0
            else
              if i.val < 448 then
                if i.val < 445 then
                  0
                else
                  if i.val < 446 then
                    0
                  else
                    if i.val < 447 then
                      0
                    else
                      1
              else
                if i.val < 451 then
                  if i.val < 449 then
                    0
                  else
                    if i.val < 450 then
                      1
                    else
                      0
                else
                  0
          else
            0
      else
        if i.val < 526 then
          if i.val < 502 then
            0
          else
            if i.val < 514 then
              if i.val < 508 then
                0
              else
                if i.val < 511 then
                  if i.val < 509 then
                    0
                  else
                    if i.val < 510 then
                      1
                    else
                      0
                else
                  0
            else
              0
        else
          if i.val < 550 then
            if i.val < 538 then
              if i.val < 532 then
                0
              else
                if i.val < 535 then
                  0
                else
                  if i.val < 536 then
                    1
                  else
                    0
            else
              0
          else
            0
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            0
          else
            if i.val < 610 then
              0
            else
              if i.val < 616 then
                if i.val < 613 then
                  if i.val < 611 then
                    0
                  else
                    if i.val < 612 then
                      1
                    else
                      0
                else
                  0
              else
                0
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  0
                else
                  if i.val < 626 then
                    0
                  else
                    if i.val < 627 then
                      0
                    else
                      1
              else
                0
            else
              0
          else
            0
      else
        if i.val < 718 then
          if i.val < 694 then
            0
          else
            if i.val < 706 then
              0
            else
              if i.val < 712 then
                if i.val < 709 then
                  if i.val < 707 then
                    0
                  else
                    if i.val < 708 then
                      1
                    else
                      0
                else
                  0
              else
                0
        else
          if i.val < 742 then
            if i.val < 730 then
              0
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    1
                  else
                    0
                else
                  0
              else
                0
          else
            if i.val < 754 then
              if i.val < 748 then
                if i.val < 745 then
                  0
                else
                  if i.val < 746 then
                    1
                  else
                    0
              else
                0
            else
              0

def c1 (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    8
                  else
                    6
                else
                  if i.val < 3 then
                    2
                  else
                    if i.val < 4 then
                      1
                    else
                      0
              else
                if i.val < 8 then
                  if i.val < 6 then
                    4
                  else
                    0
                else
                  if i.val < 9 then
                    0
                  else
                    if i.val < 10 then
                      6
                    else
                      4
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    1
                  else
                    0
                else
                  if i.val < 15 then
                    0
                  else
                    if i.val < 16 then
                      1
                    else
                      0
              else
                if i.val < 20 then
                  0
                else
                  if i.val < 21 then
                    1
                  else
                    if i.val < 22 then
                      1
                    else
                      0
          else
            if i.val < 35 then
              0
            else
              if i.val < 41 then
                0
              else
                if i.val < 44 then
                  if i.val < 42 then
                    0
                  else
                    if i.val < 43 then
                      0
                    else
                      4
                else
                  if i.val < 45 then
                    1
                  else
                    if i.val < 46 then
                      2
                    else
                      0
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    0
                  else
                    if i.val < 49 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 83 then
              0
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    0
                  else
                    if i.val < 85 then
                      0
                    else
                      1
                else
                  if i.val < 87 then
                    4
                  else
                    if i.val < 88 then
                      1
                    else
                      2
              else
                if i.val < 92 then
                  if i.val < 90 then
                    0
                  else
                    if i.val < 91 then
                      4
                    else
                      1
                else
                  if i.val < 93 then
                    2
                  else
                    if i.val < 94 then
                      0
                    else
                      1
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    1
                  else
                    0
                else
                  if i.val < 99 then
                    1
                  else
                    0
              else
                if i.val < 104 then
                  0
                else
                  if i.val < 105 then
                    1
                  else
                    if i.val < 106 then
                      1
                    else
                      0
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    0
                  else
                    1
                else
                  0
              else
                if i.val < 116 then
                  if i.val < 114 then
                    1
                  else
                    0
                else
                  if i.val < 117 then
                    0
                  else
                    if i.val < 118 then
                      0
                    else
                      4
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    1
                  else
                    if i.val < 121 then
                      2
                    else
                      0
                else
                  if i.val < 123 then
                    1
                  else
                    if i.val < 124 then
                      1
                    else
                      0
              else
                if i.val < 128 then
                  if i.val < 126 then
                    0
                  else
                    if i.val < 127 then
                      1
                    else
                      0
                else
                  0
            else
              if i.val < 137 then
                0
              else
                if i.val < 140 then
                  if i.val < 138 then
                    0
                  else
                    if i.val < 139 then
                      0
                    else
                      1
                else
                  if i.val < 141 then
                    0
                  else
                    1
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    0
                  else
                    if i.val < 145 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 179 then
              if i.val < 173 then
                0
              else
                if i.val < 176 then
                  if i.val < 174 then
                    0
                  else
                    if i.val < 175 then
                      0
                    else
                      4
                else
                  if i.val < 177 then
                    1
                  else
                    if i.val < 178 then
                      2
                    else
                      0
            else
              if i.val < 185 then
                if i.val < 182 then
                  0
                else
                  if i.val < 183 then
                    0
                  else
                    if i.val < 184 then
                      1
                    else
                      0
              else
                0
    else
      if i.val < 287 then
        if i.val < 239 then
          0
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    0
                  else
                    if i.val < 241 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    0
                  else
                    if i.val < 265 then
                      4
                    else
                      1
                else
                  if i.val < 267 then
                    2
                  else
                    if i.val < 268 then
                      0
                    else
                      1
              else
                if i.val < 272 then
                  if i.val < 270 then
                    1
                  else
                    0
                else
                  if i.val < 273 then
                    1
                  else
                    0
            else
              if i.val < 281 then
                0
              else
                if i.val < 284 then
                  if i.val < 282 then
                    1
                  else
                    0
                else
                  0
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              0
            else
              if i.val < 305 then
                if i.val < 302 then
                  0
                else
                  if i.val < 303 then
                    0
                  else
                    if i.val < 304 then
                      0
                    else
                      4
              else
                if i.val < 308 then
                  if i.val < 306 then
                    1
                  else
                    if i.val < 307 then
                      2
                    else
                      0
                else
                  if i.val < 309 then
                    0
                  else
                    if i.val < 310 then
                      0
                    else
                      1
          else
            0
        else
          if i.val < 359 then
            0
          else
            if i.val < 371 then
              if i.val < 365 then
                0
              else
                if i.val < 368 then
                  0
                else
                  if i.val < 369 then
                    0
                  else
                    if i.val < 370 then
                      1
                    else
                      0
            else
              0
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              0
            else
              if i.val < 400 then
                if i.val < 397 then
                  0
                else
                  if i.val < 398 then
                    0
                  else
                    if i.val < 399 then
                      0
                    else
                      1
              else
                0
          else
            0
        else
          if i.val < 454 then
            if i.val < 442 then
              0
            else
              if i.val < 448 then
                0
              else
                if i.val < 451 then
                  if i.val < 449 then
                    0
                  else
                    if i.val < 450 then
                      1
                    else
                      0
                else
                  0
          else
            0
      else
        if i.val < 526 then
          if i.val < 502 then
            0
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  0
                else
                  if i.val < 506 then
                    0
                  else
                    if i.val < 507 then
                      0
                    else
                      4
              else
                if i.val < 511 then
                  if i.val < 509 then
                    1
                  else
                    if i.val < 510 then
                      2
                    else
                      0
                else
                  0
            else
              0
        else
          if i.val < 550 then
            if i.val < 538 then
              0
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    0
                  else
                    1
                else
                  0
              else
                0
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  0
                else
                  if i.val < 554 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    0
                  else
                    if i.val < 564 then
                      1
                    else
                      0
                else
                  0
              else
                0
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                if i.val < 577 then
                  if i.val < 575 then
                    1
                  else
                    0
                else
                  0
              else
                if i.val < 583 then
                  0
                else
                  if i.val < 584 then
                    0
                  else
                    if i.val < 585 then
                      0
                    else
                      1
            else
              0
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    1
                  else
                    0
                else
                  if i.val < 602 then
                    1
                  else
                    0
              else
                if i.val < 607 then
                  if i.val < 605 then
                    0
                  else
                    if i.val < 606 then
                      0
                    else
                      1
                else
                  0
            else
              0
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  0
                else
                  if i.val < 626 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 640 then
                0
              else
                if i.val < 643 then
                  0
                else
                  if i.val < 644 then
                    0
                  else
                    if i.val < 645 then
                      0
                    else
                      1
          else
            if i.val < 658 then
              if i.val < 652 then
                0
              else
                if i.val < 655 then
                  0
                else
                  if i.val < 656 then
                    1
                  else
                    0
            else
              0
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    0
                  else
                    if i.val < 672 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              if i.val < 688 then
                0
              else
                if i.val < 691 then
                  if i.val < 689 then
                    1
                  else
                    0
                else
                  0
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    0
                  else
                    if i.val < 696 then
                      1
                    else
                      0
                else
                  0
              else
                0
            else
              if i.val < 712 then
                if i.val < 709 then
                  0
                else
                  if i.val < 710 then
                    0
                  else
                    if i.val < 711 then
                      0
                    else
                      1
              else
                0
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                0
              else
                if i.val < 727 then
                  0
                else
                  if i.val < 728 then
                    0
                  else
                    if i.val < 729 then
                      4
                    else
                      1
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    2
                  else
                    0
                else
                  0
              else
                0
          else
            0

def c2 (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    11
                  else
                    45
                else
                  if i.val < 3 then
                    8
                  else
                    if i.val < 4 then
                      1
                    else
                      0
              else
                if i.val < 8 then
                  if i.val < 6 then
                    20
                  else
                    0
                else
                  if i.val < 9 then
                    0
                  else
                    if i.val < 10 then
                      8
                    else
                      0
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    0
                  else
                    if i.val < 13 then
                      0
                    else
                      1
                else
                  0
              else
                if i.val < 20 then
                  0
                else
                  if i.val < 21 then
                    0
                  else
                    if i.val < 22 then
                      1
                    else
                      0
          else
            if i.val < 35 then
              0
            else
              if i.val < 41 then
                0
              else
                if i.val < 44 then
                  if i.val < 42 then
                    0
                  else
                    if i.val < 43 then
                      0
                    else
                      8
                else
                  if i.val < 45 then
                    0
                  else
                    if i.val < 46 then
                      1
                    else
                      0
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    0
                  else
                    if i.val < 49 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 83 then
              if i.val < 77 then
                0
              else
                if i.val < 80 then
                  if i.val < 78 then
                    0
                  else
                    if i.val < 79 then
                      0
                    else
                      1
                else
                  0
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    0
                  else
                    if i.val < 85 then
                      0
                    else
                      1
                else
                  if i.val < 87 then
                    9
                  else
                    if i.val < 88 then
                      0
                    else
                      1
              else
                if i.val < 92 then
                  if i.val < 90 then
                    2
                  else
                    if i.val < 91 then
                      37
                    else
                      3
                else
                  if i.val < 93 then
                    5
                  else
                    if i.val < 94 then
                      0
                    else
                      2
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    1
                  else
                    0
                else
                  if i.val < 99 then
                    3
                  else
                    0
              else
                if i.val < 104 then
                  0
                else
                  if i.val < 105 then
                    0
                  else
                    if i.val < 106 then
                      1
                    else
                      0
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    0
                  else
                    if i.val < 109 then
                      2
                    else
                      1
                else
                  0
              else
                if i.val < 116 then
                  if i.val < 114 then
                    3
                  else
                    0
                else
                  if i.val < 117 then
                    0
                  else
                    if i.val < 118 then
                      0
                    else
                      8
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    0
                  else
                    if i.val < 121 then
                      1
                    else
                      0
                else
                  0
              else
                if i.val < 128 then
                  if i.val < 126 then
                    0
                  else
                    if i.val < 127 then
                      1
                    else
                      0
                else
                  0
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    1
                  else
                    0
                else
                  0
              else
                if i.val < 140 then
                  if i.val < 138 then
                    0
                  else
                    if i.val < 139 then
                      0
                    else
                      2
                else
                  0
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    0
                  else
                    if i.val < 145 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 179 then
              if i.val < 173 then
                0
              else
                if i.val < 176 then
                  if i.val < 174 then
                    0
                  else
                    if i.val < 175 then
                      0
                    else
                      8
                else
                  if i.val < 177 then
                    0
                  else
                    if i.val < 178 then
                      1
                    else
                      0
            else
              if i.val < 185 then
                if i.val < 182 then
                  0
                else
                  if i.val < 183 then
                    0
                  else
                    if i.val < 184 then
                      1
                    else
                      0
              else
                0
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            0
          else
            if i.val < 227 then
              0
            else
              if i.val < 233 then
                0
              else
                if i.val < 236 then
                  if i.val < 234 then
                    1
                  else
                    0
                else
                  0
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    0
                  else
                    if i.val < 241 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    0
                  else
                    if i.val < 265 then
                      8
                    else
                      0
                else
                  if i.val < 267 then
                    1
                  else
                    0
              else
                if i.val < 272 then
                  0
                else
                  if i.val < 273 then
                    1
                  else
                    if i.val < 274 then
                      1
                    else
                      0
            else
              if i.val < 281 then
                0
              else
                if i.val < 284 then
                  if i.val < 282 then
                    2
                  else
                    0
                else
                  0
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              0
            else
              if i.val < 305 then
                if i.val < 302 then
                  0
                else
                  if i.val < 303 then
                    0
                  else
                    if i.val < 304 then
                      0
                    else
                      8
              else
                if i.val < 308 then
                  if i.val < 306 then
                    0
                  else
                    if i.val < 307 then
                      1
                    else
                      0
                else
                  if i.val < 309 then
                    0
                  else
                    if i.val < 310 then
                      0
                    else
                      1
          else
            0
        else
          if i.val < 359 then
            0
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  0
                else
                  if i.val < 363 then
                    0
                  else
                    if i.val < 364 then
                      1
                    else
                      0
              else
                if i.val < 368 then
                  0
                else
                  if i.val < 369 then
                    0
                  else
                    if i.val < 370 then
                      1
                    else
                      0
            else
              0
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              0
            else
              if i.val < 400 then
                if i.val < 397 then
                  0
                else
                  if i.val < 398 then
                    0
                  else
                    if i.val < 399 then
                      0
                    else
                      1
              else
                0
          else
            0
        else
          if i.val < 454 then
            if i.val < 442 then
              0
            else
              if i.val < 448 then
                0
              else
                if i.val < 451 then
                  if i.val < 449 then
                    0
                  else
                    if i.val < 450 then
                      1
                    else
                      0
                else
                  0
          else
            0
      else
        if i.val < 526 then
          if i.val < 502 then
            0
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  0
                else
                  if i.val < 506 then
                    0
                  else
                    if i.val < 507 then
                      0
                    else
                      8
              else
                if i.val < 511 then
                  if i.val < 509 then
                    0
                  else
                    if i.val < 510 then
                      1
                    else
                      0
                else
                  0
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    0
                  else
                    if i.val < 516 then
                      0
                    else
                      1
                else
                  0
              else
                0
        else
          if i.val < 550 then
            if i.val < 538 then
              0
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    0
                  else
                    if i.val < 540 then
                      0
                    else
                      1
                else
                  0
              else
                0
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    0
                  else
                    if i.val < 552 then
                      0
                    else
                      1
                else
                  if i.val < 554 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    1
                  else
                    if i.val < 564 then
                      1
                    else
                      0
                else
                  0
              else
                0
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                0
              else
                if i.val < 583 then
                  0
                else
                  if i.val < 584 then
                    0
                  else
                    if i.val < 585 then
                      0
                    else
                      3
            else
              0
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    3
                  else
                    0
                else
                  if i.val < 602 then
                    1
                  else
                    0
              else
                if i.val < 607 then
                  if i.val < 605 then
                    0
                  else
                    if i.val < 606 then
                      0
                    else
                      1
                else
                  0
            else
              0
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  0
                else
                  if i.val < 626 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 640 then
                0
              else
                if i.val < 643 then
                  0
                else
                  if i.val < 644 then
                    0
                  else
                    1
          else
            if i.val < 658 then
              if i.val < 652 then
                0
              else
                if i.val < 655 then
                  0
                else
                  if i.val < 656 then
                    1
                  else
                    0
            else
              0
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    0
                  else
                    if i.val < 672 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              if i.val < 688 then
                0
              else
                if i.val < 691 then
                  if i.val < 689 then
                    3
                  else
                    0
                else
                  0
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    0
                  else
                    if i.val < 696 then
                      1
                    else
                      0
                else
                  0
              else
                0
            else
              if i.val < 712 then
                if i.val < 709 then
                  0
                else
                  if i.val < 710 then
                    0
                  else
                    if i.val < 711 then
                      0
                    else
                      1
              else
                0
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                0
              else
                if i.val < 727 then
                  0
                else
                  if i.val < 728 then
                    0
                  else
                    if i.val < 729 then
                      8
                    else
                      0
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    1
                  else
                    0
                else
                  0
              else
                0
          else
            if i.val < 754 then
              if i.val < 748 then
                0
              else
                if i.val < 751 then
                  0
                else
                  if i.val < 752 then
                    1
                  else
                    0
            else
              0

def v0 (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    13
                  else
                    96
                else
                  if i.val < 3 then
                    10
                  else
                    if i.val < 4 then
                      2
                    else
                      0
              else
                if i.val < 8 then
                  if i.val < 6 then
                    25
                  else
                    0
                else
                  if i.val < 9 then
                    0
                  else
                    if i.val < 10 then
                      10
                    else
                      0
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    0
                  else
                    if i.val < 13 then
                      0
                    else
                      2
                else
                  0
              else
                if i.val < 20 then
                  0
                else
                  if i.val < 21 then
                    0
                  else
                    if i.val < 22 then
                      1
                    else
                      0
          else
            if i.val < 35 then
              0
            else
              if i.val < 41 then
                0
              else
                if i.val < 44 then
                  if i.val < 42 then
                    0
                  else
                    if i.val < 43 then
                      0
                    else
                      10
                else
                  if i.val < 45 then
                    0
                  else
                    if i.val < 46 then
                      1
                    else
                      0
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    0
                  else
                    if i.val < 49 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 83 then
              if i.val < 77 then
                0
              else
                if i.val < 80 then
                  if i.val < 78 then
                    0
                  else
                    if i.val < 79 then
                      0
                    else
                      2
                else
                  0
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    0
                  else
                    if i.val < 85 then
                      0
                    else
                      1
                else
                  if i.val < 87 then
                    12
                  else
                    if i.val < 88 then
                      0
                    else
                      1
              else
                if i.val < 92 then
                  if i.val < 90 then
                    1
                  else
                    if i.val < 91 then
                      88
                    else
                      4
                else
                  if i.val < 93 then
                    9
                  else
                    if i.val < 94 then
                      0
                    else
                      3
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    1
                  else
                    0
                else
                  if i.val < 99 then
                    5
                  else
                    0
              else
                if i.val < 104 then
                  0
                else
                  if i.val < 105 then
                    0
                  else
                    if i.val < 106 then
                      1
                    else
                      0
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    0
                  else
                    if i.val < 109 then
                      3
                    else
                      1
                else
                  0
              else
                if i.val < 116 then
                  if i.val < 114 then
                    5
                  else
                    0
                else
                  if i.val < 117 then
                    0
                  else
                    if i.val < 118 then
                      0
                    else
                      10
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    0
                  else
                    if i.val < 121 then
                      1
                    else
                      0
                else
                  0
              else
                if i.val < 128 then
                  if i.val < 126 then
                    0
                  else
                    if i.val < 127 then
                      1
                    else
                      0
                else
                  0
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    2
                  else
                    0
                else
                  0
              else
                if i.val < 140 then
                  if i.val < 138 then
                    0
                  else
                    if i.val < 139 then
                      0
                    else
                      2
                else
                  0
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    0
                  else
                    if i.val < 145 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 179 then
              if i.val < 173 then
                0
              else
                if i.val < 176 then
                  if i.val < 174 then
                    0
                  else
                    if i.val < 175 then
                      0
                    else
                      10
                else
                  if i.val < 177 then
                    0
                  else
                    if i.val < 178 then
                      1
                    else
                      0
            else
              if i.val < 185 then
                if i.val < 182 then
                  0
                else
                  if i.val < 183 then
                    0
                  else
                    if i.val < 184 then
                      1
                    else
                      0
              else
                0
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            0
          else
            if i.val < 227 then
              0
            else
              if i.val < 233 then
                0
              else
                if i.val < 236 then
                  if i.val < 234 then
                    2
                  else
                    0
                else
                  0
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    0
                  else
                    if i.val < 241 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              0
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    0
                  else
                    if i.val < 265 then
                      10
                    else
                      0
                else
                  if i.val < 267 then
                    1
                  else
                    0
              else
                if i.val < 272 then
                  0
                else
                  if i.val < 273 then
                    1
                  else
                    if i.val < 274 then
                      2
                    else
                      0
            else
              if i.val < 281 then
                0
              else
                if i.val < 284 then
                  if i.val < 282 then
                    2
                  else
                    0
                else
                  0
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              0
            else
              if i.val < 305 then
                if i.val < 302 then
                  0
                else
                  if i.val < 303 then
                    0
                  else
                    if i.val < 304 then
                      0
                    else
                      10
              else
                if i.val < 308 then
                  if i.val < 306 then
                    0
                  else
                    if i.val < 307 then
                      1
                    else
                      0
                else
                  if i.val < 309 then
                    0
                  else
                    if i.val < 310 then
                      0
                    else
                      1
          else
            0
        else
          if i.val < 359 then
            0
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  0
                else
                  if i.val < 363 then
                    0
                  else
                    if i.val < 364 then
                      2
                    else
                      0
              else
                if i.val < 368 then
                  0
                else
                  if i.val < 369 then
                    0
                  else
                    if i.val < 370 then
                      1
                    else
                      0
            else
              0
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              0
            else
              if i.val < 400 then
                if i.val < 397 then
                  0
                else
                  if i.val < 398 then
                    0
                  else
                    if i.val < 399 then
                      0
                    else
                      1
              else
                0
          else
            0
        else
          if i.val < 454 then
            if i.val < 442 then
              0
            else
              if i.val < 448 then
                0
              else
                if i.val < 451 then
                  if i.val < 449 then
                    0
                  else
                    if i.val < 450 then
                      1
                    else
                      0
                else
                  0
          else
            0
      else
        if i.val < 526 then
          if i.val < 502 then
            0
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  0
                else
                  if i.val < 506 then
                    0
                  else
                    if i.val < 507 then
                      0
                    else
                      10
              else
                if i.val < 511 then
                  if i.val < 509 then
                    0
                  else
                    if i.val < 510 then
                      1
                    else
                      0
                else
                  0
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    0
                  else
                    if i.val < 516 then
                      0
                    else
                      2
                else
                  0
              else
                0
        else
          if i.val < 550 then
            if i.val < 538 then
              0
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    0
                  else
                    if i.val < 540 then
                      0
                    else
                      1
                else
                  0
              else
                0
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    0
                  else
                    if i.val < 552 then
                      0
                    else
                      2
                else
                  if i.val < 554 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    2
                  else
                    if i.val < 564 then
                      1
                    else
                      0
                else
                  0
              else
                0
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                0
              else
                if i.val < 583 then
                  0
                else
                  if i.val < 584 then
                    0
                  else
                    if i.val < 585 then
                      0
                    else
                      5
            else
              0
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    5
                  else
                    0
                else
                  if i.val < 602 then
                    1
                  else
                    0
              else
                if i.val < 607 then
                  if i.val < 605 then
                    0
                  else
                    if i.val < 606 then
                      0
                    else
                      1
                else
                  0
            else
              0
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  0
                else
                  if i.val < 626 then
                    1
                  else
                    0
              else
                0
            else
              if i.val < 640 then
                0
              else
                if i.val < 643 then
                  0
                else
                  if i.val < 644 then
                    0
                  else
                    if i.val < 645 then
                      2
                    else
                      1
          else
            if i.val < 658 then
              if i.val < 652 then
                0
              else
                if i.val < 655 then
                  0
                else
                  if i.val < 656 then
                    1
                  else
                    0
            else
              0
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    0
                  else
                    if i.val < 672 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              if i.val < 688 then
                0
              else
                if i.val < 691 then
                  if i.val < 689 then
                    5
                  else
                    0
                else
                  0
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    0
                  else
                    if i.val < 696 then
                      1
                    else
                      0
                else
                  0
              else
                0
            else
              if i.val < 712 then
                if i.val < 709 then
                  0
                else
                  if i.val < 710 then
                    0
                  else
                    if i.val < 711 then
                      0
                    else
                      1
              else
                0
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                0
              else
                if i.val < 727 then
                  0
                else
                  if i.val < 728 then
                    0
                  else
                    if i.val < 729 then
                      10
                    else
                      0
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    1
                  else
                    0
                else
                  0
              else
                0
          else
            if i.val < 754 then
              if i.val < 748 then
                0
              else
                if i.val < 751 then
                  0
                else
                  if i.val < 752 then
                    2
                  else
                    0
            else
              0

def v1 (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    3
                  else
                    70
                else
                  if i.val < 3 then
                    2
                  else
                    if i.val < 4 then
                      1
                    else
                      0
              else
                if i.val < 8 then
                  if i.val < 6 then
                    6
                  else
                    0
                else
                  if i.val < 9 then
                    0
                  else
                    if i.val < 10 then
                      2
                    else
                      0
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    0
                  else
                    if i.val < 13 then
                      0
                    else
                      1
                else
                  0
              else
                0
          else
            if i.val < 35 then
              0
            else
              if i.val < 41 then
                0
              else
                if i.val < 44 then
                  if i.val < 42 then
                    0
                  else
                    if i.val < 43 then
                      0
                    else
                      2
                else
                  0
        else
          if i.val < 71 then
            0
          else
            if i.val < 83 then
              if i.val < 77 then
                0
              else
                if i.val < 80 then
                  if i.val < 78 then
                    0
                  else
                    if i.val < 79 then
                      0
                    else
                      1
                else
                  0
            else
              if i.val < 89 then
                if i.val < 86 then
                  0
                else
                  if i.val < 87 then
                    3
                  else
                    0
              else
                if i.val < 92 then
                  if i.val < 90 then
                    0
                  else
                    if i.val < 91 then
                      67
                    else
                      2
                else
                  if i.val < 93 then
                    4
                  else
                    if i.val < 94 then
                      0
                    else
                      1
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  0
                else
                  if i.val < 99 then
                    2
                  else
                    0
              else
                0
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    0
                  else
                    if i.val < 109 then
                      1
                    else
                      0
                else
                  0
              else
                if i.val < 116 then
                  if i.val < 114 then
                    2
                  else
                    0
                else
                  if i.val < 117 then
                    0
                  else
                    if i.val < 118 then
                      0
                    else
                      2
          else
            if i.val < 131 then
              0
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    1
                  else
                    0
                else
                  0
              else
                0
        else
          if i.val < 167 then
            0
          else
            if i.val < 179 then
              if i.val < 173 then
                0
              else
                if i.val < 176 then
                  if i.val < 174 then
                    0
                  else
                    if i.val < 175 then
                      0
                    else
                      2
                else
                  0
            else
              0
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            0
          else
            if i.val < 227 then
              0
            else
              if i.val < 233 then
                0
              else
                if i.val < 236 then
                  if i.val < 234 then
                    1
                  else
                    0
                else
                  0
        else
          if i.val < 263 then
            0
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    0
                  else
                    if i.val < 265 then
                      2
                    else
                      0
                else
                  0
              else
                if i.val < 272 then
                  0
                else
                  if i.val < 273 then
                    0
                  else
                    if i.val < 274 then
                      1
                    else
                      0
            else
              0
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              0
            else
              if i.val < 305 then
                if i.val < 302 then
                  0
                else
                  if i.val < 303 then
                    0
                  else
                    if i.val < 304 then
                      0
                    else
                      2
              else
                0
          else
            0
        else
          if i.val < 359 then
            0
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  0
                else
                  if i.val < 363 then
                    0
                  else
                    if i.val < 364 then
                      1
                    else
                      0
              else
                0
            else
              0
  else
    if i.val < 574 then
      if i.val < 478 then
        0
      else
        if i.val < 526 then
          if i.val < 502 then
            0
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  0
                else
                  if i.val < 506 then
                    0
                  else
                    if i.val < 507 then
                      0
                    else
                      2
              else
                0
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    0
                  else
                    if i.val < 516 then
                      0
                    else
                      1
                else
                  0
              else
                0
        else
          if i.val < 550 then
            0
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    0
                  else
                    if i.val < 552 then
                      0
                    else
                      1
                else
                  0
              else
                0
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    1
                  else
                    0
                else
                  0
              else
                0
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                0
              else
                if i.val < 583 then
                  0
                else
                  if i.val < 584 then
                    0
                  else
                    if i.val < 585 then
                      0
                    else
                      2
            else
              0
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    2
                  else
                    0
                else
                  0
              else
                0
            else
              0
        else
          if i.val < 646 then
            if i.val < 634 then
              0
            else
              if i.val < 640 then
                0
              else
                if i.val < 643 then
                  0
                else
                  if i.val < 644 then
                    0
                  else
                    if i.val < 645 then
                      1
                    else
                      0
          else
            0
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              0
            else
              if i.val < 688 then
                0
              else
                if i.val < 691 then
                  if i.val < 689 then
                    2
                  else
                    0
                else
                  0
          else
            0
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                0
              else
                if i.val < 727 then
                  0
                else
                  if i.val < 728 then
                    0
                  else
                    if i.val < 729 then
                      2
                    else
                      0
            else
              0
          else
            if i.val < 754 then
              if i.val < 748 then
                0
              else
                if i.val < 751 then
                  0
                else
                  if i.val < 752 then
                    1
                  else
                    0
            else
              0

def v2 (i : Index) : ℕ :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    0
                  else
                    18
                else
                  0
              else
                0
            else
              0
          else
            0
        else
          if i.val < 71 then
            0
          else
            if i.val < 83 then
              0
            else
              if i.val < 89 then
                0
              else
                if i.val < 92 then
                  if i.val < 90 then
                    0
                  else
                    if i.val < 91 then
                      18
                    else
                      0
                else
                  0
      else
        0
    else
      0
  else
    0

end A165378Data

-- Component: A165378CountCertificate

namespace A165378Data
open scoped BigOperators

def checkVector (f g : Index → ℕ) : Bool :=
  (List.finRange 766).all fun i => f i == g i

lemma checkVector_sound (f g : Index → ℕ) (h : checkVector f g = true) : f = g := by
  funext i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  exact beq_iff_eq.mp hi

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_c1 : checkVector (A165378Count.advance children final) (c1) = true := by
  decide +kernel

lemma count_c1 : A165378Count.advance children final = (c1) :=
  checkVector_sound _ _ check_c1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_c2 : checkVector (A165378Count.advance children c1) (c2) = true := by
  decide +kernel

lemma count_c2 : A165378Count.advance children c1 = (c2) :=
  checkVector_sound _ _ check_c2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_c3 : checkVector (A165378Count.advance children c2) (v0) = true := by
  decide +kernel

lemma count_c3 : A165378Count.advance children c2 = (v0) :=
  checkVector_sound _ _ check_c3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_v0 : checkVector (A165378Count.advance children v0) (fun i => v0 i + v1 i) = true := by
  decide +kernel

lemma count_v0 : A165378Count.advance children v0 = (fun i => v0 i + v1 i) :=
  checkVector_sound _ _ check_v0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_v1 : checkVector (A165378Count.advance children v1) (fun i => v1 i + v2 i) = true := by
  decide +kernel

lemma count_v1 : A165378Count.advance children v1 = (fun i => v1 i + v2 i) :=
  checkVector_sound _ _ check_v1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def check_v2 : checkVector (A165378Count.advance children v2) (v2) = true := by
  decide +kernel

lemma count_v2 : A165378Count.advance children v2 = (v2) :=
  checkVector_sound _ _ check_v2

lemma count_base : A165378Count.count children final 3 = v0 := by
  change A165378Count.advance children (A165378Count.advance children
    (A165378Count.advance children final)) = v0
  rw [count_c1, count_c2, count_c3]

lemma starts_v0 : (∑ i ∈ starts, v0 i) = 158 := by decide +kernel
lemma starts_v1 : (∑ i ∈ starts, v1 i) = 85 := by decide +kernel
lemma starts_v2 : (∑ i ∈ starts, v2 i) = 18 := by decide +kernel

theorem count_formula (n : ℕ) (hn : 3 < n) :
    (∑ i ∈ starts, A165378Count.count children final (n - 1) i) =
      9 * n ^ 2 + 4 * n - 2 :=
  A165378Count.initial_quadratic children final starts v0 v1 v2
    count_base count_v0 count_v1 count_v2 starts_v0 starts_v1 starts_v2 n hn

end A165378Data

-- Component: A165378StateBEq

namespace A165378Proof

/-- Explicit componentwise comparison avoids deciding equality of function fields. -/
def stateEq (s t : State) : Bool :=
  (List.finRange 4).all fun j =>
    (s.row j == t.row j) && ((s.deg j == t.deg j) &&
      ((s.part j == t.part j) && (s.done j == t.done j)))

lemma stateEq_eq_true (s t : State) : stateEq s t = true ↔ s = t := by
  constructor
  · intro h
    have hj (j : Fin 4) : s.row j = t.row j ∧ s.deg j = t.deg j ∧
        s.part j = t.part j ∧ s.done j = t.done j := by
      have he := List.all_eq_true.mp h j (List.mem_finRange j)
      simpa only [Bool.and_eq_true, beq_iff_eq] using he
    have hr : s.row = t.row := funext fun j => (hj j).1
    have hd : s.deg = t.deg := funext fun j => (hj j).2.1
    have hp : s.part = t.part := funext fun j => (hj j).2.2.1
    have hb : s.done = t.done := funext fun j => (hj j).2.2.2
    cases s
    cases t
    cases hr
    cases hd
    cases hp
    cases hb
    rfl
  · rintro rfl
    simp [stateEq]

def optionStateEq : Option State → Option State → Bool
  | none, none => true
  | some s, some t => stateEq s t
  | _, _ => false

lemma optionStateEq_eq_true (s t : Option State) : optionStateEq s t = true ↔ s = t := by
  cases s <;> cases t <;> simp [optionStateEq, stateEq_eq_true]

end A165378Proof

-- Component: A165378InitialTable

namespace A165378Data
open A165378Proof

def startID (i : Fin 16) : Index := ⟨i.val, by omega⟩

lemma mem_starts_iff (i : Index) : i ∈ starts ↔ i.val < 16 := by
  simp only [starts, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    Fin.ext_iff]
  norm_num
  omega

def startCheck (i : Fin 16) : Bool := decide (
  (state (startID i)).row 0 = 0 ∧ (state (startID i)).row 3 = 1 ∧
  4 * ((state (startID i)).row 1).val + ((state (startID i)).row 2).val = i.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def start_checked : (List.finRange 16).all startCheck = true := by decide +kernel

lemma start_facts (i : Index) (hi : i ∈ starts) :
    (state i).row 0 = 0 ∧ (state i).row 3 = 1 ∧
    4 * ((state i).row 1).val + ((state i).row 2).val = i.val := by
  let j : Fin 16 := ⟨i.val, (mem_starts_iff i).mp hi⟩
  have hc := List.all_eq_true.mp start_checked j (List.mem_finRange j)
  exact of_decide_eq_true hc

def headRow (a b : Fin 4) : Row := ![0, a, b, 1]

def headIndex (a b : Fin 4) : Index :=
  ⟨4 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def head_checked : (List.finRange 4).all (fun a =>
    (List.finRange 4).all fun b => decide ((state (headIndex a b)).row = headRow a b)) =
      true := by decide +kernel

lemma head_row (a b : Fin 4) : (state (headIndex a b)).row = headRow a b := by
  have ha := List.all_eq_true.mp head_checked a (List.mem_finRange a)
  have hb := List.all_eq_true.mp ha b (List.mem_finRange b)
  exact of_decide_eq_true hb

lemma starts_rows (r : Row) : (r 0 = 0 ∧ r 3 = 1) ↔
    ∃ i ∈ starts, (state i).row = r := by
  constructor
  · rintro ⟨h0, h3⟩
    refine ⟨headIndex (r 1) (r 2), ?_, ?_⟩
    · rw [mem_starts_iff]
      have := (r 1).isLt
      have := (r 2).isLt
      dsimp [headIndex]
      omega
    · rw [head_row]
      funext j
      fin_cases j <;> simp [headRow, h0, h3]
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(start_facts i hi).1, (start_facts i hi).2.1⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def initial_checked : (List.finRange 16).all (fun j =>
    stateEq (state (startID j)) (initial (state (startID j)).row)) = true := by
  decide +kernel

lemma starts_initial (i : Index) (hi : i ∈ starts) :
    state i = initial (state i).row := by
  let j : Fin 16 := ⟨i.val, (mem_starts_iff i).mp hi⟩
  exact (stateEq_eq_true _ _).mp
    (List.all_eq_true.mp initial_checked j (List.mem_finRange j))

lemma starts_injective (i j : Index) (hi : i ∈ starts) (hj : j ∈ starts)
    (he : (state i).row = (state j).row) : i = j := by
  apply Fin.ext
  rw [← (start_facts i hi).2.2, ← (start_facts j hj).2.2, he]

def finalCheck (i : Index) : Bool :=
  decide (final i = if accepting (state i) then 1 else 0)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
def final_checked : (List.finRange 766).all finalCheck = true := by decide +kernel

lemma final_eq_apply (i : Index) : final i = if accepting (state i) then 1 else 0 := by
  exact of_decide_eq_true (List.all_eq_true.mp final_checked i (List.mem_finRange i))

lemma final_eq : final = fun i => if accepting (state i) then 1 else 0 := funext final_eq_apply

end A165378Data

-- Component: A165378Rows

namespace A165378Data
open A165378Proof

def rowOf (i : Fin 256) (j : Fin 4) : Fin 4 :=
  ⟨(i.val / 4 ^ (3 - j.val)) % 4, Nat.mod_lt _ (by decide)⟩

def rowIndex (r : Row) : Fin 256 :=
  ⟨64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val, by
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    have h2 := (r 2).isLt
    have h3 := (r 3).isLt
    omega⟩

lemma rowOf_rowIndex (r : Row) : rowOf (rowIndex r) = r := by
  funext j
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  apply Fin.ext
  fin_cases j
  · change (64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val) / 64 % 4 = (r 0).val
    omega
  · change (64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val) / 16 % 4 = (r 1).val
    omega
  · change (64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val) / 4 % 4 = (r 2).val
    omega
  · change (64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val) / 1 % 4 = (r 3).val
    omega

lemma rowIndex_injective : Function.Injective rowIndex := by
  intro r s h
  calc
    r = rowOf (rowIndex r) := (rowOf_rowIndex r).symm
    _ = rowOf (rowIndex s) := congrArg rowOf h
    _ = s := rowOf_rowIndex s

end A165378Data

-- Component: A165378FastStep

namespace A165378Proof

def boolImp (a b : Bool) : Bool := !a || b

lemma boolImp_eq_true (a b : Bool) :
    boolImp a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

def lostBool (s : State) (r : Row) (i : Fin 4) : Bool :=
  (List.finRange 4).all fun j => decide (links s r (old i) ≠ links s r (new j))

lemma lostBool_eq_true (s : State) (r : Row) (i : Fin 4) :
    lostBool s r i = true ↔ lost s r i := by
  simp [lostBool, lost, List.all_eq_true]

def permissibleBool (s : State) (r : Row) : Bool :=
  ((List.finRange 4).all fun j => !s.done (r j)) &&
  (((List.finRange 4).all fun j => decide (oldDegrees s r j ≤ 2)) &&
  (((List.finRange 4).all fun j => decide (newDegrees s r j ≤ 2)) &&
  ((List.finRange 4).all fun i => boolImp (lostBool s r i)
    ((List.finRange 8).all fun j => boolImp (decide (color s r j = s.row i))
      (decide (links s r j = links s r (old i)))))))

lemma permissibleBool_eq_true (s : State) (r : Row) :
    permissibleBool s r = true ↔ permissible s r := by
  simp [permissibleBool, permissible, List.all_eq_true, boolImp_eq_true,
    lostBool_eq_true]

def closedBool (s : State) (r : Row) (c : Fin 4) : Bool :=
  (List.finRange 4).any fun i => decide (s.row i = c) && lostBool s r i

lemma closedBool_eq_true (s : State) (r : Row) (c : Fin 4) :
    closedBool s r c = true ↔ ∃ i : Fin 4, s.row i = c ∧ lost s r i := by
  simp [closedBool, List.any_eq_true, lostBool_eq_true]

lemma closedBool_eq_decide (s : State) (r : Row) (c : Fin 4) :
    closedBool s r c = decide (∃ i : Fin 4, s.row i = c ∧ lost s r i) := by
  apply Bool.eq_iff_iff.mpr
  simp [closedBool_eq_true]

def fastAdvance (s : State) (r : Row) : State where
  row := r
  deg := newDegrees s r
  part := normalize (fun i => links s r (new i))
  done := fun c => s.done c || closedBool s r c

lemma fastAdvance_eq (s : State) (r : Row) : fastAdvance s r = advance s r := by
  unfold fastAdvance advance
  congr 1
  funext c
  rw [closedBool_eq_decide]

def fastStep (s : State) (r : Row) : Option State :=
  if permissibleBool s r then some (fastAdvance s r) else none

lemma fastStep_eq (s : State) (r : Row) : fastStep s r = step s r := by
  simp only [fastStep, step, permissibleBool_eq_true, fastAdvance_eq]

end A165378Proof

-- Component: A165378TableLemmas

namespace A165378TableLemmas

variable {S R T : Type*} [DecidableEq R]

def lookup (row : S → R) (xs : List S) (r : R) : Option S :=
  xs.find? (fun j => row j = r)

lemma lookup_eq_some (row : S → R) (xs : List S)
    (h : (xs.map row).Nodup) (r : R) (j : S) :
    lookup row xs r = some j ↔ j ∈ xs ∧ row j = r := by
  constructor
  · intro he
    exact ⟨List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  · rintro ⟨hj, hr⟩
    cases he : lookup row xs r with
    | none =>
      have hf := List.find?_eq_none.mp he j hj
      simp only [hr, decide_true, not_true_eq_false] at hf
    | some k =>
      have hk : k ∈ xs := List.mem_of_find?_eq_some he
      have hkr : row k = r := by simpa using List.find?_some he
      have hkj : k = j := List.inj_on_of_nodup_map h hk hj (hkr.trans hr.symm)
      simp only [hkj]

lemma lookup_map_eq_some (row : S → R) (value : S → T) (xs : List S)
    (h : (xs.map row).Nodup) (r : R) (t : T) :
    (lookup row xs r).map value = some t ↔
      ∃ j ∈ xs, row j = r ∧ value j = t := by
  simp only [Option.map_eq_some_iff, lookup_eq_some row xs h]
  constructor
  · rintro ⟨j, ⟨hj, hr⟩, ht⟩
    exact ⟨j, hj, hr, ht⟩
  · rintro ⟨j, hj, hr, ht⟩
    exact ⟨j, ⟨hj, hr⟩, ht⟩

omit [DecidableEq R] in
lemma child_injective (row : S → R) (childList : S → List S)
    (children : S → Finset S)
    (hmem : ∀ i j, j ∈ childList i ↔ j ∈ children i)
    (hnd : ∀ i, ((childList i).map row).Nodup) :
    ∀ i j k, j ∈ children i → k ∈ children i → row j = row k → j = k := by
  intro i j k hj hk he
  exact List.inj_on_of_nodup_map (hnd i) ((hmem i j).mpr hj) ((hmem i k).mpr hk) he

lemma step_iff_of_lookup (row : S → R) (value : S → T)
    (childList : S → List S) (children : S → Finset S)
    (step : T → R → Option T)
    (hmem : ∀ i j, j ∈ childList i ↔ j ∈ children i)
    (hnd : ∀ i, ((childList i).map row).Nodup)
    (hstep : ∀ i r, step (value i) r = (lookup row (childList i) r).map value) :
    ∀ i r t, step (value i) r = some t ↔
      ∃ j ∈ children i, row j = r ∧ value j = t := by
  intro i r t
  rw [hstep, lookup_map_eq_some row value (childList i) (hnd i)]
  simp only [hmem]

end A165378TableLemmas

-- Component: A165378Keys

namespace A165378Data
open A165378Proof

-- Precomputed row codes avoid repeatedly decoding states in the transition certificate.
def rowKeys (i : Index) : List (Fin 256 × Index) :=
  if i.val < 383 then
    if i.val < 191 then
      if i.val < 95 then
        if i.val < 47 then
          if i.val < 23 then
            if i.val < 11 then
              if i.val < 5 then
                if i.val < 2 then
                  if i.val < 1 then
                    ([(68, 16), (69, 17), (70, 18), (71, 19), (86, 20), (87, 21), (101, 22), (102, 23), (103, 24), (117, 25), (118, 26), (119, 27), (128, 28), (130, 29), (131, 30), (132, 31), (133, 32), (134, 33), (135, 34), (136, 35), (138, 36), (139, 37), (140, 38), (142, 39), (143, 40), (150, 41), (151, 42), (165, 43), (166, 44), (167, 45), (170, 46), (171, 47), (174, 48), (175, 49), (181, 50), (182, 51), (183, 52), (186, 53), (187, 54), (190, 55), (191, 56), (192, 57), (194, 58), (195, 59), (196, 60), (197, 61), (198, 62), (199, 63), (200, 64), (202, 65), (203, 66), (204, 67), (206, 68), (207, 69), (214, 70), (215, 71), (229, 72), (230, 73), (231, 74), (234, 75), (235, 76), (238, 77), (239, 78), (245, 79), (246, 80), (247, 81), (250, 82), (251, 83), (254, 84), (255, 85)] : List (Fin 256 × Index))
                  else
                    ([(0, 86), (2, 87), (3, 88), (4, 89), (5, 90), (6, 91), (7, 92), (8, 93), (10, 94), (11, 95), (12, 96), (14, 97), (15, 98), (16, 99), (17, 100), (18, 101), (19, 102), (20, 103), (22, 104), (23, 105), (24, 106), (25, 107), (26, 108), (27, 109), (28, 110), (29, 111), (30, 112), (31, 113), (32, 114), (34, 115), (35, 116), (36, 117), (37, 118), (38, 119), (39, 120), (40, 121), (42, 122), (43, 123), (44, 124), (46, 125), (47, 126), (48, 127), (50, 128), (51, 129), (52, 130), (53, 131), (54, 132), (55, 133), (56, 134), (58, 135), (59, 136), (60, 137), (62, 138), (63, 139), (89, 140), (90, 141), (91, 142), (93, 143), (94, 144), (95, 145), (101, 22), (102, 23), (103, 24), (117, 25), (118, 26), (119, 27), (150, 146), (151, 147), (153, 148), (154, 149), (155, 150), (157, 151), (158, 152), (159, 153), (165, 43), (166, 44), (167, 45), (170, 46), (171, 47), (174, 48), (175, 49), (181, 50), (182, 51), (183, 52), (186, 53), (187, 54), (190, 55), (191, 56), (214, 154), (215, 155), (217, 156), (218, 157), (219, 158), (221, 159), (222, 160), (223, 161), (229, 72), (230, 73), (231, 74), (234, 75), (235, 76), (238, 77), (239, 78), (245, 79), (246, 80), (247, 81), (250, 82), (251, 83), (254, 84), (255, 85)] : List (Fin 256 × Index))
                else
                  if i.val < 3 then
                    ([(0, 162), (3, 163), (4, 164), (5, 165), (7, 166), (12, 167), (15, 168), (20, 169), (23, 170), (32, 171), (34, 172), (35, 173), (36, 174), (37, 175), (38, 176), (39, 177), (40, 178), (42, 179), (43, 180), (44, 181), (46, 182), (47, 183), (48, 184), (51, 185), (52, 186), (53, 187), (55, 188), (60, 189), (63, 190), (87, 191), (101, 192), (102, 193), (103, 194), (117, 195), (119, 196), (165, 197), (166, 198), (167, 199), (174, 200), (175, 201), (215, 202), (229, 203), (230, 204), (231, 205), (234, 206), (235, 207), (238, 208), (239, 209), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 4 then
                      ([(0, 213), (2, 214), (4, 215), (5, 216), (6, 217), (8, 218), (10, 219), (20, 220), (22, 221), (32, 222), (34, 223), (36, 224), (37, 225), (38, 226), (40, 227), (42, 228), (48, 229), (50, 230), (51, 231), (52, 232), (53, 233), (54, 234), (55, 235), (56, 236), (58, 237), (59, 238), (60, 239), (62, 240), (63, 241), (86, 242), (101, 243), (102, 244), (117, 245), (118, 246), (119, 247), (150, 248), (165, 249), (166, 250), (170, 251), (181, 252), (182, 253), (183, 254), (186, 255), (187, 256), (190, 257), (191, 258), (245, 259), (246, 260), (247, 261), (250, 262), (251, 263)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 8 then
                  if i.val < 6 then
                    ([(101, 264), (102, 265), (103, 266), (105, 267), (106, 268), (107, 269), (109, 270), (110, 271), (111, 272), (117, 273), (118, 274), (119, 275), (121, 276), (122, 277), (123, 278), (125, 279), (126, 280), (127, 281), (165, 43), (166, 44), (167, 45), (170, 46), (171, 47), (174, 48), (175, 49), (181, 50), (182, 51), (183, 52), (186, 53), (187, 54), (190, 55), (191, 56), (229, 72), (230, 73), (231, 74), (234, 75), (235, 76), (238, 77), (239, 78), (245, 79), (246, 80), (247, 81), (250, 82), (251, 83), (254, 84), (255, 85)] : List (Fin 256 × Index))
                  else
                    if i.val < 7 then
                      ([(87, 282), (101, 283), (102, 284), (103, 285), (117, 286), (119, 287)] : List (Fin 256 × Index))
                    else
                      ([(86, 288), (101, 289), (102, 290), (117, 291), (118, 292), (119, 293)] : List (Fin 256 × Index))
                else
                  if i.val < 9 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 10 then
                      ([(93, 294), (95, 295), (117, 195), (119, 196), (150, 296), (151, 297), (153, 298), (154, 299), (155, 300), (157, 301), (158, 302), (159, 303), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (215, 318), (221, 319), (223, 320), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(87, 191), (101, 192), (102, 193), (103, 194), (117, 195), (119, 196), (150, 321), (151, 322), (165, 323), (166, 324), (167, 325), (174, 326), (175, 327), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (215, 202), (229, 203), (230, 204), (231, 205), (234, 206), (235, 207), (238, 208), (239, 209), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
            else
              if i.val < 17 then
                if i.val < 14 then
                  if i.val < 12 then
                    ([(117, 328), (119, 329), (150, 330), (165, 331), (166, 332), (170, 333), (181, 334), (182, 335), (183, 336), (186, 337), (187, 338), (190, 339), (191, 340), (245, 341), (247, 342)] : List (Fin 256 × Index))
                  else
                    if i.val < 13 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(89, 343), (90, 344), (101, 243), (102, 244), (150, 345), (153, 346), (154, 347), (165, 249), (166, 250), (170, 251), (214, 348), (215, 349), (217, 350), (218, 351), (219, 352), (221, 353), (222, 354), (223, 355), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                else
                  if i.val < 15 then
                    ([(101, 370), (102, 371), (165, 372), (166, 373), (215, 374), (229, 375), (230, 376), (231, 377), (234, 378), (235, 379), (238, 380), (239, 381), (245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 16 then
                      ([(86, 242), (101, 243), (102, 244), (117, 245), (118, 246), (119, 247), (150, 248), (165, 249), (166, 250), (170, 251), (181, 252), (182, 253), (183, 254), (186, 255), (187, 256), (190, 257), (191, 258), (214, 385), (215, 386), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 387), (246, 388), (247, 389), (250, 390), (251, 391)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 20 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 21 then
                    ([(171, 392), (186, 393), (187, 394), (235, 395), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 22 then
                      ([(170, 251), (174, 398), (175, 399), (190, 400), (238, 401), (239, 402), (254, 403)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
          else
            if i.val < 35 then
              if i.val < 29 then
                if i.val < 26 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 27 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 28 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(240, 404), (243, 405), (255, 212)] : List (Fin 256 × Index))
              else
                if i.val < 32 then
                  if i.val < 30 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 31 then
                      ([(204, 406), (207, 407)] : List (Fin 256 × Index))
                    else
                      ([(3, 408), (16, 409), (17, 410), (19, 411), (48, 412), (51, 413)] : List (Fin 256 × Index))
                else
                  if i.val < 33 then
                    ([(0, 162), (3, 163), (4, 164), (5, 165), (7, 166), (12, 167), (15, 168), (48, 184), (51, 185), (52, 186), (53, 187), (55, 188), (60, 189), (63, 190), (117, 195), (119, 196), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 34 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (12, 415), (15, 416), (16, 417), (17, 418), (20, 419), (21, 420), (28, 421), (29, 422), (31, 423), (60, 424), (93, 425), (95, 426), (221, 427), (223, 428)] : List (Fin 256 × Index))
            else
              if i.val < 41 then
                if i.val < 38 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 39 then
                    ([(48, 429), (51, 430)] : List (Fin 256 × Index))
                  else
                    if i.val < 40 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (12, 415), (15, 416), (48, 431), (51, 432), (60, 433)] : List (Fin 256 × Index))
              else
                if i.val < 44 then
                  if i.val < 42 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 43 then
                      ([(125, 434)] : List (Fin 256 × Index))
                    else
                      ([(117, 195), (119, 196), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 45 then
                    ([(153, 435), (154, 436), (155, 437), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                  else
                    if i.val < 46 then
                      ([(93, 425), (95, 426), (149, 441), (150, 442), (153, 443), (154, 444), (157, 445), (158, 446), (159, 447), (170, 333), (174, 448), (175, 449), (190, 450), (221, 427), (223, 428)] : List (Fin 256 × Index))
                    else
                      ([(250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
        else
          if i.val < 71 then
            if i.val < 59 then
              if i.val < 53 then
                if i.val < 50 then
                  if i.val < 48 then
                    ([(238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    if i.val < 49 then
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                    else
                      ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
                else
                  if i.val < 51 then
                    ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 52 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(221, 456), (223, 457)] : List (Fin 256 × Index))
              else
                if i.val < 56 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 57 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 58 then
                      ([(160, 458), (162, 459), (170, 251)] : List (Fin 256 × Index))
                    else
                      ([(136, 460), (138, 461)] : List (Fin 256 × Index))
            else
              if i.val < 65 then
                if i.val < 62 then
                  if i.val < 60 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 61 then
                      ([(2, 462), (16, 463), (17, 464), (18, 465), (32, 466), (34, 467)] : List (Fin 256 × Index))
                    else
                      ([(0, 213), (2, 214), (4, 215), (5, 216), (6, 217), (8, 218), (10, 219), (32, 222), (34, 223), (36, 224), (37, 225), (38, 226), (40, 227), (42, 228), (101, 243), (102, 244), (165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
                else
                  if i.val < 63 then
                    ([(0, 414), (8, 468), (10, 469), (16, 417), (17, 418), (20, 419), (21, 420), (24, 470), (25, 471), (26, 472), (40, 473), (89, 474), (90, 475), (153, 476), (154, 477)] : List (Fin 256 × Index))
                  else
                    if i.val < 64 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(32, 478), (34, 479)] : List (Fin 256 × Index))
              else
                if i.val < 68 then
                  if i.val < 66 then
                    ([(0, 414), (8, 468), (10, 469), (32, 480), (34, 481), (40, 482)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  if i.val < 69 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 70 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(105, 483)] : List (Fin 256 × Index))
          else
            if i.val < 83 then
              if i.val < 77 then
                if i.val < 74 then
                  if i.val < 72 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 73 then
                      ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 80 then
                  if i.val < 78 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 79 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                else
                  if i.val < 81 then
                    ([(89, 474), (90, 475), (153, 476), (154, 477), (213, 486), (215, 487), (217, 488), (218, 489), (219, 490), (221, 491), (223, 492), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 82 then
                      ([(221, 496), (222, 497), (223, 498), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                    else
                      ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
            else
              if i.val < 89 then
                if i.val < 86 then
                  if i.val < 84 then
                    ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                  else
                    if i.val < 85 then
                      ([(186, 505), (187, 506)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399)] : List (Fin 256 × Index))
                else
                  if i.val < 87 then
                    ([(160, 507), (162, 508), (163, 509), (170, 46), (171, 47), (174, 48), (175, 49), (176, 510), (178, 511), (179, 512), (186, 53), (187, 54), (190, 55), (191, 56), (224, 513), (226, 514), (227, 515), (234, 75), (235, 76), (238, 77), (239, 78), (240, 516), (242, 517), (243, 518), (250, 82), (251, 83), (254, 84), (255, 85)] : List (Fin 256 × Index))
                  else
                    if i.val < 88 then
                      ([(136, 519), (138, 520), (139, 521), (171, 392), (186, 393), (187, 394), (192, 522), (195, 523), (200, 524), (202, 525), (203, 526), (204, 527), (207, 528), (235, 395), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(128, 529), (130, 530), (136, 531), (138, 532), (140, 533), (142, 534), (143, 535), (170, 251), (174, 398), (175, 399), (190, 400), (204, 536), (206, 537), (207, 538), (238, 401), (239, 402), (254, 403)] : List (Fin 256 × Index))
              else
                if i.val < 92 then
                  if i.val < 90 then
                    ([(2, 539), (3, 540), (16, 541), (17, 542), (18, 543), (19, 544), (32, 545), (34, 546), (35, 547), (48, 548), (50, 549), (51, 550)] : List (Fin 256 × Index))
                  else
                    if i.val < 91 then
                      ([(0, 86), (2, 87), (3, 88), (4, 89), (5, 90), (6, 91), (7, 92), (8, 93), (10, 94), (11, 95), (12, 96), (14, 97), (15, 98), (32, 114), (34, 115), (35, 116), (36, 117), (37, 118), (38, 119), (39, 120), (40, 121), (42, 122), (43, 123), (44, 124), (46, 125), (47, 126), (48, 127), (50, 128), (51, 129), (52, 130), (53, 131), (54, 132), (55, 133), (56, 134), (58, 135), (59, 136), (60, 137), (62, 138), (63, 139), (101, 22), (102, 23), (103, 24), (117, 25), (118, 26), (119, 27), (165, 43), (166, 44), (167, 45), (170, 46), (171, 47), (174, 48), (175, 49), (181, 50), (182, 51), (183, 52), (186, 53), (187, 54), (190, 55), (191, 56), (229, 72), (230, 73), (231, 74), (234, 75), (235, 76), (238, 77), (239, 78), (245, 79), (246, 80), (247, 81), (250, 82), (251, 83), (254, 84), (255, 85)] : List (Fin 256 × Index))
                    else
                      ([(0, 162), (3, 163), (8, 551), (10, 552), (11, 553), (12, 167), (15, 168), (16, 554), (17, 555), (19, 556), (20, 557), (21, 558), (23, 559), (24, 560), (25, 561), (26, 562), (27, 563), (28, 564), (29, 565), (31, 566), (40, 567), (43, 568), (48, 184), (51, 185), (56, 569), (58, 570), (59, 571), (60, 189), (63, 190), (89, 572), (90, 573), (91, 574), (93, 294), (95, 295), (153, 575), (154, 576), (155, 577), (171, 392), (186, 393), (187, 394), (213, 578), (215, 579), (217, 580), (218, 581), (219, 582), (221, 319), (223, 320), (235, 395), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 93 then
                    ([(0, 213), (2, 214), (8, 218), (10, 219), (12, 583), (14, 584), (15, 585), (16, 586), (17, 587), (18, 588), (20, 589), (21, 590), (22, 591), (24, 592), (25, 593), (26, 594), (28, 595), (29, 596), (30, 597), (31, 598), (32, 222), (34, 223), (40, 227), (42, 228), (44, 599), (46, 600), (47, 601), (60, 602), (62, 603), (89, 343), (90, 344), (93, 604), (94, 605), (95, 606), (149, 607), (150, 608), (153, 346), (154, 347), (157, 609), (158, 610), (159, 611), (170, 251), (174, 398), (175, 399), (190, 400), (221, 612), (222, 613), (223, 614), (238, 401), (239, 402), (254, 403)] : List (Fin 256 × Index))
                  else
                    if i.val < 94 then
                      ([(3, 408), (32, 615), (34, 616), (35, 617), (48, 412), (51, 413)] : List (Fin 256 × Index))
                    else
                      ([(0, 162), (3, 163), (8, 551), (10, 552), (11, 553), (12, 167), (15, 168), (32, 171), (34, 172), (35, 173), (40, 618), (43, 619), (44, 181), (46, 182), (47, 183), (48, 184), (51, 185), (56, 569), (58, 570), (59, 571), (60, 189), (63, 190), (174, 200), (175, 201), (186, 393), (187, 394), (235, 620), (238, 208), (239, 209), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
      else
        if i.val < 143 then
          if i.val < 119 then
            if i.val < 107 then
              if i.val < 101 then
                if i.val < 98 then
                  if i.val < 96 then
                    ([(0, 414), (12, 415), (15, 416), (32, 480), (34, 481), (40, 621), (42, 622), (44, 623), (46, 624), (47, 625), (60, 424), (174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    if i.val < 97 then
                      ([(2, 462), (32, 466), (34, 467), (48, 628), (50, 629), (51, 630)] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (8, 468), (10, 469), (40, 473), (48, 431), (51, 432), (56, 631), (58, 632), (59, 633), (60, 634), (63, 635), (186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
                else
                  if i.val < 99 then
                    ([(0, 213), (2, 214), (8, 218), (10, 219), (12, 583), (14, 584), (15, 585), (32, 222), (34, 223), (40, 227), (42, 228), (44, 599), (46, 600), (47, 601), (48, 229), (50, 230), (51, 231), (56, 236), (58, 237), (59, 238), (60, 638), (62, 639), (170, 251), (174, 398), (175, 399), (186, 255), (187, 256), (190, 640), (238, 401), (239, 402), (250, 262), (251, 263)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 104 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 105 then
                    ([(171, 392), (186, 393), (187, 394), (235, 395), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 106 then
                      ([(170, 251), (174, 398), (175, 399), (190, 400), (238, 401), (239, 402), (254, 403)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
            else
              if i.val < 113 then
                if i.val < 110 then
                  if i.val < 108 then
                    ([(87, 282), (101, 283), (102, 284), (103, 285), (117, 286), (119, 287)] : List (Fin 256 × Index))
                  else
                    if i.val < 109 then
                      ([(85, 641), (87, 642), (89, 643), (90, 644), (91, 645), (93, 646), (95, 647), (101, 648), (102, 649), (103, 650), (105, 651), (107, 652), (109, 653), (110, 654), (111, 655), (117, 656), (119, 657), (121, 658), (122, 659), (123, 660), (125, 661), (127, 662), (174, 200), (175, 201), (186, 393), (187, 394), (235, 620), (238, 208), (239, 209), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (93, 664), (95, 665), (101, 666), (102, 667), (105, 668), (106, 669), (109, 670), (110, 671), (111, 672), (125, 434), (174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
                else
                  if i.val < 111 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 112 then
                      ([(86, 288), (101, 289), (102, 290), (117, 291), (118, 292), (119, 293)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674), (105, 483), (117, 675), (119, 676), (121, 677), (122, 678), (123, 679), (125, 680), (127, 681), (186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
              else
                if i.val < 116 then
                  if i.val < 114 then
                    ([(85, 682), (86, 683), (89, 684), (90, 685), (93, 686), (94, 687), (95, 688), (101, 689), (102, 690), (105, 691), (106, 692), (109, 693), (110, 694), (111, 695), (117, 696), (118, 697), (119, 698), (121, 699), (122, 700), (123, 701), (125, 702), (126, 703), (170, 251), (174, 398), (175, 399), (186, 255), (187, 256), (190, 640), (238, 401), (239, 402), (250, 262), (251, 263)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  if i.val < 117 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 118 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(117, 195), (119, 196), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
          else
            if i.val < 131 then
              if i.val < 125 then
                if i.val < 122 then
                  if i.val < 120 then
                    ([(153, 435), (154, 436), (155, 437), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                  else
                    if i.val < 121 then
                      ([(93, 425), (95, 426), (149, 441), (150, 442), (153, 443), (154, 444), (157, 445), (158, 446), (159, 447), (170, 333), (174, 448), (175, 449), (190, 450), (221, 427), (223, 428)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 123 then
                    ([(186, 704), (187, 705), (190, 316), (191, 317), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 124 then
                      ([(174, 706), (175, 707), (190, 450), (238, 451), (239, 452)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 128 then
                  if i.val < 126 then
                    ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                  else
                    if i.val < 127 then
                      ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
            else
              if i.val < 137 then
                if i.val < 134 then
                  if i.val < 132 then
                    ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                  else
                    if i.val < 133 then
                      ([(89, 474), (90, 475), (153, 476), (154, 477), (213, 486), (215, 487), (217, 488), (218, 489), (219, 490), (221, 491), (223, 492), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(221, 496), (222, 497), (223, 498), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                else
                  if i.val < 135 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 136 then
                      ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
              else
                if i.val < 140 then
                  if i.val < 138 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 139 then
                      ([(186, 505), (187, 506), (235, 493), (250, 708), (251, 709)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399), (234, 359), (235, 360), (238, 710), (239, 711)] : List (Fin 256 × Index))
                else
                  if i.val < 141 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 142 then
                      ([(174, 200), (175, 201), (186, 393), (187, 394), (235, 620), (238, 208), (239, 209), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
        else
          if i.val < 167 then
            if i.val < 155 then
              if i.val < 149 then
                if i.val < 146 then
                  if i.val < 144 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 145 then
                      ([(186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399), (186, 255), (187, 256), (190, 640), (238, 401), (239, 402), (250, 262), (251, 263)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 152 then
                  if i.val < 150 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 151 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                else
                  if i.val < 153 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 154 then
                      ([(85, 663), (93, 664), (95, 665), (117, 675), (119, 676), (125, 714)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
            else
              if i.val < 161 then
                if i.val < 158 then
                  if i.val < 156 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 157 then
                      ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674), (101, 666), (102, 667), (105, 717)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 164 then
                  if i.val < 162 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 163 then
                      ([(240, 404), (243, 405), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(204, 406), (207, 407)] : List (Fin 256 × Index))
                else
                  if i.val < 165 then
                    ([(3, 408), (16, 409), (17, 410), (19, 411), (48, 412), (51, 413)] : List (Fin 256 × Index))
                  else
                    if i.val < 166 then
                      ([(0, 162), (3, 163), (4, 164), (5, 165), (7, 166), (12, 167), (15, 168), (48, 184), (51, 185), (52, 186), (53, 187), (55, 188), (60, 189), (63, 190), (117, 195), (119, 196), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (12, 415), (15, 416), (16, 417), (17, 418), (20, 419), (21, 420), (28, 421), (29, 422), (31, 423), (60, 424), (93, 425), (95, 426), (221, 427), (223, 428)] : List (Fin 256 × Index))
          else
            if i.val < 179 then
              if i.val < 173 then
                if i.val < 170 then
                  if i.val < 168 then
                    ([(48, 429), (51, 430)] : List (Fin 256 × Index))
                  else
                    if i.val < 169 then
                      ([(0, 414), (12, 415), (15, 416), (48, 431), (51, 432), (60, 433)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 171 then
                    ([(125, 434)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 176 then
                  if i.val < 174 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 175 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(117, 195), (119, 196), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 177 then
                    ([(153, 435), (154, 436), (155, 437), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                  else
                    if i.val < 178 then
                      ([(93, 425), (95, 426), (149, 441), (150, 442), (153, 443), (154, 444), (157, 445), (158, 446), (159, 447), (170, 333), (174, 448), (175, 449), (190, 450), (221, 427), (223, 428)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
            else
              if i.val < 185 then
                if i.val < 182 then
                  if i.val < 180 then
                    ([(250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 181 then
                      ([(238, 451), (239, 452)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 183 then
                    ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                  else
                    if i.val < 184 then
                      ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 188 then
                  if i.val < 186 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 187 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 189 then
                    ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
    else
      if i.val < 287 then
        if i.val < 239 then
          if i.val < 215 then
            if i.val < 203 then
              if i.val < 197 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 200 then
                  if i.val < 198 then
                    ([(117, 195), (119, 196), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 199 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(93, 425), (95, 426), (221, 427), (223, 428)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
            else
              if i.val < 209 then
                if i.val < 206 then
                  if i.val < 204 then
                    ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                  else
                    if i.val < 205 then
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 212 then
                  if i.val < 210 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 211 then
                      ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                else
                  if i.val < 213 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 214 then
                      ([(160, 458), (162, 459), (170, 251)] : List (Fin 256 × Index))
                    else
                      ([(136, 460), (138, 461)] : List (Fin 256 × Index))
          else
            if i.val < 227 then
              if i.val < 221 then
                if i.val < 218 then
                  if i.val < 216 then
                    ([(2, 462), (16, 463), (17, 464), (18, 465), (32, 466), (34, 467)] : List (Fin 256 × Index))
                  else
                    if i.val < 217 then
                      ([(0, 213), (2, 214), (4, 215), (5, 216), (6, 217), (8, 218), (10, 219), (32, 222), (34, 223), (36, 224), (37, 225), (38, 226), (40, 227), (42, 228), (101, 243), (102, 244), (165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (8, 468), (10, 469), (16, 417), (17, 418), (20, 419), (21, 420), (24, 470), (25, 471), (26, 472), (40, 473), (89, 474), (90, 475), (153, 476), (154, 477)] : List (Fin 256 × Index))
                else
                  if i.val < 219 then
                    ([(32, 478), (34, 479)] : List (Fin 256 × Index))
                  else
                    if i.val < 220 then
                      ([(0, 414), (8, 468), (10, 469), (32, 480), (34, 481), (40, 482)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 224 then
                  if i.val < 222 then
                    ([(105, 483)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  if i.val < 225 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 226 then
                      ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
            else
              if i.val < 233 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 236 then
                  if i.val < 234 then
                    ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                  else
                    if i.val < 235 then
                      ([(89, 474), (90, 475), (153, 476), (154, 477), (213, 486), (215, 487), (217, 488), (218, 489), (219, 490), (221, 491), (223, 492), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(221, 496), (222, 497), (223, 498), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                else
                  if i.val < 237 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 238 then
                      ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
        else
          if i.val < 263 then
            if i.val < 251 then
              if i.val < 245 then
                if i.val < 242 then
                  if i.val < 240 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 241 then
                      ([(186, 505), (187, 506)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 248 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 249 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 250 then
                      ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
            else
              if i.val < 257 then
                if i.val < 254 then
                  if i.val < 252 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 253 then
                      ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 255 then
                    ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 260 then
                  if i.val < 258 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 259 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
                else
                  if i.val < 261 then
                    ([(89, 474), (90, 475), (153, 476), (154, 477)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
          else
            if i.val < 275 then
              if i.val < 269 then
                if i.val < 266 then
                  if i.val < 264 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 265 then
                      ([(117, 195), (119, 196), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(153, 435), (154, 436), (155, 437), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                else
                  if i.val < 267 then
                    ([(93, 425), (95, 426), (149, 441), (150, 442), (153, 443), (154, 444), (157, 445), (158, 446), (159, 447), (170, 333), (174, 448), (175, 449), (190, 450), (221, 427), (223, 428)] : List (Fin 256 × Index))
                  else
                    if i.val < 268 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 704), (187, 705), (190, 316), (191, 317), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
              else
                if i.val < 272 then
                  if i.val < 270 then
                    ([(174, 706), (175, 707), (190, 450), (238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    if i.val < 271 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                else
                  if i.val < 273 then
                    ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
                  else
                    if i.val < 274 then
                      ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                    else
                      ([(89, 474), (90, 475), (153, 476), (154, 477), (213, 486), (215, 487), (217, 488), (218, 489), (219, 490), (221, 491), (223, 492), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
            else
              if i.val < 281 then
                if i.val < 278 then
                  if i.val < 276 then
                    ([(221, 496), (222, 497), (223, 498), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                  else
                    if i.val < 277 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 279 then
                    ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                  else
                    if i.val < 280 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 505), (187, 506), (235, 493), (250, 708), (251, 709)] : List (Fin 256 × Index))
              else
                if i.val < 284 then
                  if i.val < 282 then
                    ([(170, 251), (174, 398), (175, 399), (234, 359), (235, 360), (238, 710), (239, 711)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
      else
        if i.val < 335 then
          if i.val < 311 then
            if i.val < 299 then
              ([] : List (Fin 256 × Index))
            else
              if i.val < 305 then
                if i.val < 302 then
                  if i.val < 300 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 301 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                else
                  if i.val < 303 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 304 then
                      ([(85, 663), (93, 664), (95, 665), (117, 675), (119, 676), (125, 714)] : List (Fin 256 × Index))
                    else
                      ([(117, 195), (119, 196), (165, 304), (166, 305), (167, 306), (170, 307), (171, 308), (174, 309), (175, 310), (181, 311), (182, 312), (183, 313), (186, 314), (187, 315), (190, 316), (191, 317), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
              else
                if i.val < 308 then
                  if i.val < 306 then
                    ([(153, 435), (154, 436), (155, 437), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                  else
                    if i.val < 307 then
                      ([(93, 425), (95, 426), (149, 441), (150, 442), (153, 443), (154, 444), (157, 445), (158, 446), (159, 447), (170, 333), (174, 448), (175, 449), (190, 450), (221, 427), (223, 428)] : List (Fin 256 × Index))
                    else
                      ([(250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 309 then
                    ([(238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    if i.val < 310 then
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                    else
                      ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
          else
            if i.val < 323 then
              if i.val < 317 then
                if i.val < 314 then
                  if i.val < 312 then
                    ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 313 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 320 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 321 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 322 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(125, 434)] : List (Fin 256 × Index))
            else
              if i.val < 329 then
                if i.val < 326 then
                  if i.val < 324 then
                    ([(117, 195), (119, 196), (245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 325 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(93, 425), (95, 426), (221, 427), (223, 428)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 332 then
                  if i.val < 330 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 331 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                else
                  if i.val < 333 then
                    ([(153, 484), (154, 485)] : List (Fin 256 × Index))
                  else
                    if i.val < 334 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
        else
          if i.val < 359 then
            if i.val < 347 then
              if i.val < 341 then
                if i.val < 338 then
                  if i.val < 336 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 337 then
                      ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
            else
              if i.val < 353 then
                if i.val < 350 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 351 then
                    ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                  else
                    if i.val < 352 then
                      ([(85, 663), (89, 673), (90, 674), (101, 666), (102, 667), (105, 717)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 356 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 357 then
                    ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                  else
                    if i.val < 358 then
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
          else
            if i.val < 371 then
              if i.val < 365 then
                if i.val < 362 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 363 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 364 then
                      ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251), (229, 356), (230, 357), (231, 358), (234, 359), (235, 360), (238, 361), (239, 362), (245, 363), (246, 364), (247, 365), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                    else
                      ([(89, 474), (90, 475), (153, 476), (154, 477), (213, 486), (215, 487), (217, 488), (218, 489), (219, 490), (221, 491), (223, 492), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
              else
                if i.val < 368 then
                  if i.val < 366 then
                    ([(221, 496), (222, 497), (223, 498), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                  else
                    if i.val < 367 then
                      ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                else
                  if i.val < 369 then
                    ([(186, 505), (187, 506)] : List (Fin 256 × Index))
                  else
                    if i.val < 370 then
                      ([(170, 251), (174, 398), (175, 399)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
            else
              if i.val < 377 then
                if i.val < 374 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 375 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 376 then
                      ([(165, 331), (166, 332), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(153, 484), (154, 485)] : List (Fin 256 × Index))
              else
                if i.val < 380 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 381 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 382 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(245, 382), (247, 383), (255, 384)] : List (Fin 256 × Index))
  else
    if i.val < 574 then
      if i.val < 478 then
        if i.val < 430 then
          if i.val < 406 then
            if i.val < 394 then
              if i.val < 388 then
                if i.val < 385 then
                  if i.val < 384 then
                    ([(221, 456), (223, 457)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  if i.val < 386 then
                    ([(105, 483)] : List (Fin 256 × Index))
                  else
                    if i.val < 387 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(101, 243), (102, 244), (165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
              else
                if i.val < 391 then
                  if i.val < 389 then
                    ([(89, 474), (90, 475), (153, 476), (154, 477)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
            else
              if i.val < 400 then
                if i.val < 397 then
                  if i.val < 395 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 396 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 398 then
                    ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                  else
                    if i.val < 399 then
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                    else
                      ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
              else
                if i.val < 403 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 404 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 405 then
                      ([(240, 718), (243, 719), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(204, 720), (207, 721)] : List (Fin 256 × Index))
          else
            if i.val < 418 then
              if i.val < 412 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 415 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 416 then
                    ([(48, 429), (51, 430)] : List (Fin 256 × Index))
                  else
                    if i.val < 417 then
                      ([(0, 414), (12, 415), (15, 416)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
            else
              if i.val < 424 then
                if i.val < 421 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 422 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 423 then
                      ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (93, 664), (95, 665)] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
        else
          if i.val < 454 then
            if i.val < 442 then
              ([] : List (Fin 256 × Index))
            else
              if i.val < 448 then
                if i.val < 445 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 446 then
                    ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                  else
                    if i.val < 447 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (93, 664), (95, 665)] : List (Fin 256 × Index))
              else
                if i.val < 451 then
                  if i.val < 449 then
                    ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                  else
                    if i.val < 450 then
                      ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
          else
            if i.val < 466 then
              if i.val < 460 then
                if i.val < 457 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 458 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 459 then
                      ([(160, 722), (162, 723), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(136, 724), (138, 725)] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
            else
              if i.val < 472 then
                if i.val < 469 then
                  if i.val < 467 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 468 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(32, 478), (34, 479)] : List (Fin 256 × Index))
                else
                  if i.val < 470 then
                    ([(0, 414), (8, 468), (10, 469)] : List (Fin 256 × Index))
                  else
                    if i.val < 471 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(101, 715), (102, 716)] : List (Fin 256 × Index))
              else
                if i.val < 475 then
                  if i.val < 473 then
                    ([(85, 663), (89, 673), (90, 674)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
      else
        if i.val < 526 then
          if i.val < 502 then
            if i.val < 490 then
              if i.val < 484 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 487 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 488 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 489 then
                      ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674)] : List (Fin 256 × Index))
            else
              if i.val < 496 then
                if i.val < 493 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 494 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 495 then
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
          else
            if i.val < 514 then
              if i.val < 508 then
                if i.val < 505 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 506 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 507 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(48, 726), (51, 727), (160, 728), (162, 729), (163, 730), (170, 307), (171, 308), (174, 309), (175, 310), (176, 731), (178, 732), (179, 733), (186, 314), (187, 315), (190, 316), (191, 317), (240, 404), (243, 405), (255, 212)] : List (Fin 256 × Index))
              else
                if i.val < 511 then
                  if i.val < 509 then
                    ([(136, 734), (138, 735), (139, 736), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
                  else
                    if i.val < 510 then
                      ([(12, 737), (15, 738), (128, 739), (130, 740), (136, 741), (138, 742), (140, 743), (142, 744), (143, 745), (170, 333), (174, 448), (175, 449), (190, 450), (204, 406), (207, 407)] : List (Fin 256 × Index))
                    else
                      ([(240, 718), (243, 719), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 512 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 513 then
                      ([(204, 720), (207, 721)] : List (Fin 256 × Index))
                    else
                      ([(160, 722), (162, 723), (170, 333)] : List (Fin 256 × Index))
            else
              if i.val < 520 then
                if i.val < 517 then
                  if i.val < 515 then
                    ([(136, 724), (138, 725)] : List (Fin 256 × Index))
                  else
                    if i.val < 516 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(32, 746), (34, 747), (160, 458), (162, 459), (170, 251), (224, 748), (226, 749), (227, 750), (234, 359), (235, 360), (238, 361), (239, 362), (240, 751), (242, 752), (243, 753), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                else
                  if i.val < 518 then
                    ([(8, 754), (10, 755), (136, 460), (138, 461), (192, 756), (195, 757), (200, 758), (202, 759), (203, 760), (204, 761), (207, 762), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 519 then
                      ([(204, 763), (206, 764), (207, 765), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 523 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 524 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 525 then
                      ([(32, 478), (34, 479)] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (8, 468), (10, 469)] : List (Fin 256 × Index))
        else
          if i.val < 550 then
            if i.val < 538 then
              if i.val < 532 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 535 then
                  if i.val < 533 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 534 then
                      ([(48, 429), (51, 430)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 536 then
                    ([(0, 414), (12, 415), (15, 416)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
            else
              if i.val < 544 then
                if i.val < 541 then
                  if i.val < 539 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 540 then
                      ([(171, 392), (186, 393), (187, 394), (235, 395), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399), (190, 400), (238, 401), (239, 402), (254, 403)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
          else
            if i.val < 562 then
              if i.val < 556 then
                if i.val < 553 then
                  if i.val < 551 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 552 then
                      ([(3, 408), (32, 615), (34, 616), (35, 617), (48, 412), (51, 413)] : List (Fin 256 × Index))
                    else
                      ([(0, 162), (3, 163), (8, 551), (10, 552), (11, 553), (12, 167), (15, 168), (48, 184), (51, 185), (56, 569), (58, 570), (59, 571), (60, 189), (63, 190), (186, 393), (187, 394), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 554 then
                    ([(0, 414), (12, 415), (15, 416), (32, 480), (34, 481), (40, 621), (42, 622), (44, 623), (46, 624), (47, 625), (60, 424), (174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 559 then
                  if i.val < 557 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 558 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                else
                  if i.val < 560 then
                    ([(221, 427), (223, 428)] : List (Fin 256 × Index))
                  else
                    if i.val < 561 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(87, 282), (101, 283), (102, 284), (103, 285), (117, 286), (119, 287)] : List (Fin 256 × Index))
            else
              if i.val < 568 then
                if i.val < 565 then
                  if i.val < 563 then
                    ([(85, 641), (87, 642), (89, 643), (90, 644), (91, 645), (93, 646), (95, 647), (117, 656), (119, 657), (121, 658), (122, 659), (123, 660), (125, 661), (127, 662), (186, 393), (187, 394), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                  else
                    if i.val < 564 then
                      ([(85, 663), (93, 664), (95, 665), (101, 666), (102, 667), (105, 668), (106, 669), (109, 670), (110, 671), (111, 672), (125, 434), (174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 566 then
                    ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                  else
                    if i.val < 567 then
                      ([(85, 663), (93, 664), (95, 665), (117, 675), (119, 676), (125, 714)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 571 then
                  if i.val < 569 then
                    ([(190, 450)] : List (Fin 256 × Index))
                  else
                    if i.val < 570 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 572 then
                    ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                  else
                    if i.val < 573 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 393), (187, 394), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
    else
      if i.val < 670 then
        if i.val < 622 then
          if i.val < 598 then
            if i.val < 586 then
              if i.val < 580 then
                if i.val < 577 then
                  if i.val < 575 then
                    ([(174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 583 then
                  if i.val < 581 then
                    ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                  else
                    if i.val < 582 then
                      ([(85, 663), (89, 673), (90, 674)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 584 then
                    ([(2, 462), (32, 466), (34, 467), (48, 628), (50, 629), (51, 630)] : List (Fin 256 × Index))
                  else
                    if i.val < 585 then
                      ([(0, 414), (8, 468), (10, 469), (40, 473), (48, 431), (51, 432), (56, 631), (58, 632), (59, 633), (60, 634), (63, 635), (186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
                    else
                      ([(0, 213), (2, 214), (8, 218), (10, 219), (12, 583), (14, 584), (15, 585), (32, 222), (34, 223), (40, 227), (42, 228), (44, 599), (46, 600), (47, 601), (170, 251), (174, 398), (175, 399), (238, 401), (239, 402)] : List (Fin 256 × Index))
            else
              if i.val < 592 then
                if i.val < 589 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 590 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 591 then
                      ([(165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
                    else
                      ([(153, 476), (154, 477)] : List (Fin 256 × Index))
              else
                if i.val < 595 then
                  if i.val < 593 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 594 then
                      ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674), (101, 666), (102, 667), (105, 717)] : List (Fin 256 × Index))
                else
                  if i.val < 596 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 597 then
                      ([(86, 288), (101, 289), (102, 290), (117, 291), (118, 292), (119, 293)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674), (105, 483), (117, 675), (119, 676), (121, 677), (122, 678), (123, 679), (125, 680), (127, 681), (186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
          else
            if i.val < 610 then
              if i.val < 604 then
                if i.val < 601 then
                  if i.val < 599 then
                    ([(85, 682), (86, 683), (89, 684), (90, 685), (93, 686), (94, 687), (95, 688), (101, 689), (102, 690), (105, 691), (106, 692), (109, 693), (110, 694), (111, 695), (170, 251), (174, 398), (175, 399), (238, 401), (239, 402)] : List (Fin 256 × Index))
                  else
                    if i.val < 600 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                else
                  if i.val < 602 then
                    ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
                  else
                    if i.val < 603 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(235, 493)] : List (Fin 256 × Index))
              else
                if i.val < 607 then
                  if i.val < 605 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 606 then
                      ([(186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
                    else
                      ([(170, 251), (174, 398), (175, 399), (238, 401), (239, 402)] : List (Fin 256 × Index))
                else
                  if i.val < 608 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 609 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(117, 712), (119, 713)] : List (Fin 256 × Index))
            else
              if i.val < 616 then
                if i.val < 613 then
                  if i.val < 611 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 612 then
                      ([(85, 663), (93, 664), (95, 665)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
        else
          if i.val < 646 then
            if i.val < 634 then
              if i.val < 628 then
                if i.val < 625 then
                  if i.val < 623 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 624 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                else
                  if i.val < 626 then
                    ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 631 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 632 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 633 then
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
            else
              if i.val < 640 then
                ([] : List (Fin 256 × Index))
              else
                if i.val < 643 then
                  if i.val < 641 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 642 then
                      ([(245, 210), (247, 211), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(221, 427), (223, 428)] : List (Fin 256 × Index))
                else
                  if i.val < 644 then
                    ([(87, 282), (101, 283), (102, 284), (103, 285), (117, 286), (119, 287)] : List (Fin 256 × Index))
                  else
                    if i.val < 645 then
                      ([(85, 641), (87, 642), (89, 643), (90, 644), (91, 645), (93, 646), (95, 647), (117, 656), (119, 657), (121, 658), (122, 659), (123, 660), (125, 661), (127, 662), (186, 393), (187, 394), (250, 396), (251, 397), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (93, 664), (95, 665), (101, 666), (102, 667), (105, 668), (106, 669), (109, 670), (110, 671), (111, 672), (125, 434), (174, 626), (175, 627), (238, 451), (239, 452)] : List (Fin 256 × Index))
          else
            if i.val < 658 then
              if i.val < 652 then
                if i.val < 649 then
                  if i.val < 647 then
                    ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                  else
                    if i.val < 648 then
                      ([(85, 663), (93, 664), (95, 665), (117, 675), (119, 676), (125, 714)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 655 then
                  if i.val < 653 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 654 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                else
                  if i.val < 656 then
                    ([(170, 333), (174, 448), (175, 449), (186, 337), (187, 338), (190, 455)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
            else
              if i.val < 664 then
                if i.val < 661 then
                  if i.val < 659 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 660 then
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 667 then
                  if i.val < 665 then
                    ([(117, 712), (119, 713)] : List (Fin 256 × Index))
                  else
                    if i.val < 666 then
                      ([(85, 663), (93, 664), (95, 665)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
      else
        if i.val < 718 then
          if i.val < 694 then
            if i.val < 682 then
              if i.val < 676 then
                if i.val < 673 then
                  if i.val < 671 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 672 then
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                    else
                      ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
                else
                  if i.val < 674 then
                    ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                  else
                    if i.val < 675 then
                      ([(85, 663), (89, 673), (90, 674)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
              else
                if i.val < 679 then
                  if i.val < 677 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 678 then
                      ([] : List (Fin 256 × Index))
                    else
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                else
                  if i.val < 680 then
                    ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
            else
              if i.val < 688 then
                if i.val < 685 then
                  if i.val < 683 then
                    ([(165, 249), (166, 250), (170, 251)] : List (Fin 256 × Index))
                  else
                    if i.val < 684 then
                      ([(153, 476), (154, 477)] : List (Fin 256 × Index))
                    else
                      ([(101, 715), (102, 716)] : List (Fin 256 × Index))
                else
                  if i.val < 686 then
                    ([(85, 663), (89, 673), (90, 674), (101, 666), (102, 667), (105, 717)] : List (Fin 256 × Index))
                  else
                    if i.val < 687 then
                      ([(86, 288), (101, 289), (102, 290), (117, 291), (118, 292), (119, 293)] : List (Fin 256 × Index))
                    else
                      ([(85, 663), (89, 673), (90, 674), (105, 483), (117, 675), (119, 676), (121, 677), (122, 678), (123, 679), (125, 680), (127, 681), (186, 505), (187, 506), (250, 636), (251, 637)] : List (Fin 256 × Index))
              else
                if i.val < 691 then
                  if i.val < 689 then
                    ([(85, 682), (86, 683), (89, 684), (90, 685), (93, 686), (94, 687), (95, 688), (101, 689), (102, 690), (105, 691), (106, 692), (109, 693), (110, 694), (111, 695), (170, 251), (174, 398), (175, 399), (238, 401), (239, 402)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
          else
            if i.val < 706 then
              if i.val < 700 then
                if i.val < 697 then
                  if i.val < 695 then
                    ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                  else
                    if i.val < 696 then
                      ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  ([] : List (Fin 256 × Index))
              else
                if i.val < 703 then
                  if i.val < 701 then
                    ([(235, 502), (238, 380), (239, 381), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 702 then
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 704 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 705 then
                      ([(250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(238, 503), (239, 504)] : List (Fin 256 × Index))
            else
              if i.val < 712 then
                if i.val < 709 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 710 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 711 then
                      ([(186, 453), (187, 454)] : List (Fin 256 × Index))
                    else
                      ([(170, 333), (174, 448), (175, 449)] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
        else
          if i.val < 742 then
            if i.val < 730 then
              if i.val < 724 then
                if i.val < 721 then
                  if i.val < 719 then
                    ([(240, 718), (243, 719), (255, 384)] : List (Fin 256 × Index))
                  else
                    if i.val < 720 then
                      ([(204, 720), (207, 721)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 722 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 723 then
                      ([(160, 722), (162, 723), (170, 333)] : List (Fin 256 × Index))
                    else
                      ([(136, 724), (138, 725)] : List (Fin 256 × Index))
              else
                if i.val < 727 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 728 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 729 then
                      ([(48, 726), (51, 727), (160, 728), (162, 729), (163, 730), (170, 307), (171, 308), (174, 309), (175, 310), (176, 731), (178, 732), (179, 733), (186, 314), (187, 315), (190, 316), (191, 317), (240, 404), (243, 405), (255, 212)] : List (Fin 256 × Index))
                    else
                      ([(136, 734), (138, 735), (139, 736), (171, 438), (186, 439), (187, 440)] : List (Fin 256 × Index))
            else
              if i.val < 736 then
                if i.val < 733 then
                  if i.val < 731 then
                    ([(12, 737), (15, 738), (128, 739), (130, 740), (136, 741), (138, 742), (140, 743), (142, 744), (143, 745), (170, 333), (174, 448), (175, 449), (190, 450), (204, 406), (207, 407)] : List (Fin 256 × Index))
                  else
                    if i.val < 732 then
                      ([(240, 718), (243, 719), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 734 then
                    ([(204, 720), (207, 721)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))
          else
            if i.val < 754 then
              if i.val < 748 then
                if i.val < 745 then
                  if i.val < 743 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 744 then
                      ([(48, 429), (51, 430)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 746 then
                    ([(0, 414), (12, 415), (15, 416)] : List (Fin 256 × Index))
                  else
                    ([] : List (Fin 256 × Index))
              else
                if i.val < 751 then
                  if i.val < 749 then
                    ([(160, 722), (162, 723), (170, 333)] : List (Fin 256 × Index))
                  else
                    if i.val < 750 then
                      ([(136, 724), (138, 725)] : List (Fin 256 × Index))
                    else
                      ([] : List (Fin 256 × Index))
                else
                  if i.val < 752 then
                    ([(32, 746), (34, 747), (160, 458), (162, 459), (170, 251), (224, 748), (226, 749), (227, 750), (234, 359), (235, 360), (238, 361), (239, 362), (240, 751), (242, 752), (243, 753), (250, 366), (251, 367), (254, 368), (255, 369)] : List (Fin 256 × Index))
                  else
                    if i.val < 753 then
                      ([(8, 754), (10, 755), (136, 460), (138, 461), (192, 756), (195, 757), (200, 758), (202, 759), (203, 760), (204, 761), (207, 762), (235, 493), (250, 494), (251, 495), (255, 384)] : List (Fin 256 × Index))
                    else
                      ([(204, 763), (206, 764), (207, 765), (238, 499), (239, 500), (254, 501)] : List (Fin 256 × Index))
            else
              if i.val < 760 then
                if i.val < 757 then
                  ([] : List (Fin 256 × Index))
                else
                  if i.val < 758 then
                    ([] : List (Fin 256 × Index))
                  else
                    if i.val < 759 then
                      ([(32, 478), (34, 479)] : List (Fin 256 × Index))
                    else
                      ([(0, 414), (8, 468), (10, 469)] : List (Fin 256 × Index))
              else
                ([] : List (Fin 256 × Index))

def rowKeysCheck (i : Index) : Bool :=
  decide (rowKeys i = (childrenList i).map (fun j => (rowIndex (state j).row, j)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
def rowKeys_checked : (List.finRange 766).all rowKeysCheck = true := by
  decide +kernel

lemma rowKeys_eq (i : Index) :
    rowKeys i = (childrenList i).map (fun j => (rowIndex (state j).row, j)) := by
  have h := List.all_eq_true.mp rowKeys_checked i (List.mem_finRange i)
  exact of_decide_eq_true h

def fastLookup (i : Index) (r : Fin 256) : Option Index :=
  ((rowKeys i).find? (fun p => p.1 = r)).map Prod.snd

lemma fastLookup_eq (i : Index) (r : Fin 256) :
    fastLookup i r =
      A165378TableLemmas.lookup (fun j => rowIndex (state j).row) (childrenList i) r := by
  simp only [fastLookup, rowKeys_eq, List.find?_map, Option.map_map,
    Function.comp_def, A165378TableLemmas.lookup]
  simp

end A165378Data

-- Component: A165378Transition

namespace A165378Data
open A165378Proof


def lookupCode (i : Index) (r : Fin 256) : Option Index :=
  fastLookup i r

def transitionCheck (i : Index) : Bool :=
  (List.finRange 256).all fun r =>
    optionStateEq (fastStep (state i) (rowOf r)) ((lookupCode i r).map state)

lemma transition_of_check (i : Index) (h : transitionCheck i = true) (r : Fin 256) :
    step (state i) (rowOf r) = (lookupCode i r).map state := by
  have he := List.all_eq_true.mp h r (List.mem_finRange r)
  simpa only [fastStep_eq] using (optionStateEq_eq_true _ _).mp he

def TransitionPair (b : Fin 383) : Prop :=
  transitionCheck ⟨2 * b.val, by have := b.isLt; omega⟩ = true ∧
  transitionCheck ⟨2 * b.val + 1, by have := b.isLt; omega⟩ = true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_0 : TransitionPair 0 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_1 : TransitionPair 1 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_2 : TransitionPair 2 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_3 : TransitionPair 3 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_4 : TransitionPair 4 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_5 : TransitionPair 5 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_6 : TransitionPair 6 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_7 : TransitionPair 7 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_8 : TransitionPair 8 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_9 : TransitionPair 9 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_10 : TransitionPair 10 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_11 : TransitionPair 11 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_12 : TransitionPair 12 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_13 : TransitionPair 13 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_14 : TransitionPair 14 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_15 : TransitionPair 15 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_16 : TransitionPair 16 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_17 : TransitionPair 17 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_18 : TransitionPair 18 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_19 : TransitionPair 19 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_20 : TransitionPair 20 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_21 : TransitionPair 21 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_22 : TransitionPair 22 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_23 : TransitionPair 23 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_24 : TransitionPair 24 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_25 : TransitionPair 25 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_26 : TransitionPair 26 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_27 : TransitionPair 27 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_28 : TransitionPair 28 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_29 : TransitionPair 29 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_30 : TransitionPair 30 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_31 : TransitionPair 31 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_32 : TransitionPair 32 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_33 : TransitionPair 33 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_34 : TransitionPair 34 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_35 : TransitionPair 35 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_36 : TransitionPair 36 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_37 : TransitionPair 37 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_38 : TransitionPair 38 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_39 : TransitionPair 39 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_40 : TransitionPair 40 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_41 : TransitionPair 41 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_42 : TransitionPair 42 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_43 : TransitionPair 43 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_44 : TransitionPair 44 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_45 : TransitionPair 45 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_46 : TransitionPair 46 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_47 : TransitionPair 47 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_48 : TransitionPair 48 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_49 : TransitionPair 49 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_50 : TransitionPair 50 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_51 : TransitionPair 51 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_52 : TransitionPair 52 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_53 : TransitionPair 53 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_54 : TransitionPair 54 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_55 : TransitionPair 55 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_56 : TransitionPair 56 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_57 : TransitionPair 57 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_58 : TransitionPair 58 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_59 : TransitionPair 59 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_60 : TransitionPair 60 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_61 : TransitionPair 61 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_62 : TransitionPair 62 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_63 : TransitionPair 63 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_64 : TransitionPair 64 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_65 : TransitionPair 65 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_66 : TransitionPair 66 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_67 : TransitionPair 67 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_68 : TransitionPair 68 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_69 : TransitionPair 69 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_70 : TransitionPair 70 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_71 : TransitionPair 71 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_72 : TransitionPair 72 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_73 : TransitionPair 73 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_74 : TransitionPair 74 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_75 : TransitionPair 75 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_76 : TransitionPair 76 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_77 : TransitionPair 77 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_78 : TransitionPair 78 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_79 : TransitionPair 79 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_80 : TransitionPair 80 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_81 : TransitionPair 81 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_82 : TransitionPair 82 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_83 : TransitionPair 83 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_84 : TransitionPair 84 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_85 : TransitionPair 85 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_86 : TransitionPair 86 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_87 : TransitionPair 87 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_88 : TransitionPair 88 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_89 : TransitionPair 89 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_90 : TransitionPair 90 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_91 : TransitionPair 91 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_92 : TransitionPair 92 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_93 : TransitionPair 93 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_94 : TransitionPair 94 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_95 : TransitionPair 95 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_96 : TransitionPair 96 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_97 : TransitionPair 97 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_98 : TransitionPair 98 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_99 : TransitionPair 99 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_100 : TransitionPair 100 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_101 : TransitionPair 101 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_102 : TransitionPair 102 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_103 : TransitionPair 103 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_104 : TransitionPair 104 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_105 : TransitionPair 105 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_106 : TransitionPair 106 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_107 : TransitionPair 107 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_108 : TransitionPair 108 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_109 : TransitionPair 109 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_110 : TransitionPair 110 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_111 : TransitionPair 111 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_112 : TransitionPair 112 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_113 : TransitionPair 113 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_114 : TransitionPair 114 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_115 : TransitionPair 115 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_116 : TransitionPair 116 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_117 : TransitionPair 117 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_118 : TransitionPair 118 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_119 : TransitionPair 119 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_120 : TransitionPair 120 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_121 : TransitionPair 121 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_122 : TransitionPair 122 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_123 : TransitionPair 123 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_124 : TransitionPair 124 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_125 : TransitionPair 125 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_126 : TransitionPair 126 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_127 : TransitionPair 127 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_128 : TransitionPair 128 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_129 : TransitionPair 129 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_130 : TransitionPair 130 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_131 : TransitionPair 131 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_132 : TransitionPair 132 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_133 : TransitionPair 133 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_134 : TransitionPair 134 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_135 : TransitionPair 135 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_136 : TransitionPair 136 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_137 : TransitionPair 137 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_138 : TransitionPair 138 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_139 : TransitionPair 139 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_140 : TransitionPair 140 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_141 : TransitionPair 141 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_142 : TransitionPair 142 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_143 : TransitionPair 143 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_144 : TransitionPair 144 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_145 : TransitionPair 145 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_146 : TransitionPair 146 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_147 : TransitionPair 147 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_148 : TransitionPair 148 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_149 : TransitionPair 149 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_150 : TransitionPair 150 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_151 : TransitionPair 151 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_152 : TransitionPair 152 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_153 : TransitionPair 153 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_154 : TransitionPair 154 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_155 : TransitionPair 155 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_156 : TransitionPair 156 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_157 : TransitionPair 157 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_158 : TransitionPair 158 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_159 : TransitionPair 159 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_160 : TransitionPair 160 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_161 : TransitionPair 161 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_162 : TransitionPair 162 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_163 : TransitionPair 163 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_164 : TransitionPair 164 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_165 : TransitionPair 165 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_166 : TransitionPair 166 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_167 : TransitionPair 167 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_168 : TransitionPair 168 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_169 : TransitionPair 169 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_170 : TransitionPair 170 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_171 : TransitionPair 171 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_172 : TransitionPair 172 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_173 : TransitionPair 173 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_174 : TransitionPair 174 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_175 : TransitionPair 175 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_176 : TransitionPair 176 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_177 : TransitionPair 177 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_178 : TransitionPair 178 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_179 : TransitionPair 179 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_180 : TransitionPair 180 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_181 : TransitionPair 181 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_182 : TransitionPair 182 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_183 : TransitionPair 183 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_184 : TransitionPair 184 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_185 : TransitionPair 185 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_186 : TransitionPair 186 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_187 : TransitionPair 187 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_188 : TransitionPair 188 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_189 : TransitionPair 189 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_190 : TransitionPair 190 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_191 : TransitionPair 191 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_192 : TransitionPair 192 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_193 : TransitionPair 193 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_194 : TransitionPair 194 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_195 : TransitionPair 195 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_196 : TransitionPair 196 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_197 : TransitionPair 197 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_198 : TransitionPair 198 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_199 : TransitionPair 199 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_200 : TransitionPair 200 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_201 : TransitionPair 201 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_202 : TransitionPair 202 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_203 : TransitionPair 203 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_204 : TransitionPair 204 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_205 : TransitionPair 205 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_206 : TransitionPair 206 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_207 : TransitionPair 207 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_208 : TransitionPair 208 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_209 : TransitionPair 209 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_210 : TransitionPair 210 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_211 : TransitionPair 211 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_212 : TransitionPair 212 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_213 : TransitionPair 213 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_214 : TransitionPair 214 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_215 : TransitionPair 215 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_216 : TransitionPair 216 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_217 : TransitionPair 217 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_218 : TransitionPair 218 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_219 : TransitionPair 219 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_220 : TransitionPair 220 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_221 : TransitionPair 221 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_222 : TransitionPair 222 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_223 : TransitionPair 223 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_224 : TransitionPair 224 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_225 : TransitionPair 225 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_226 : TransitionPair 226 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_227 : TransitionPair 227 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_228 : TransitionPair 228 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_229 : TransitionPair 229 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_230 : TransitionPair 230 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_231 : TransitionPair 231 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_232 : TransitionPair 232 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_233 : TransitionPair 233 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_234 : TransitionPair 234 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_235 : TransitionPair 235 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_236 : TransitionPair 236 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_237 : TransitionPair 237 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_238 : TransitionPair 238 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_239 : TransitionPair 239 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_240 : TransitionPair 240 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_241 : TransitionPair 241 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_242 : TransitionPair 242 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_243 : TransitionPair 243 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_244 : TransitionPair 244 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_245 : TransitionPair 245 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_246 : TransitionPair 246 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_247 : TransitionPair 247 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_248 : TransitionPair 248 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_249 : TransitionPair 249 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_250 : TransitionPair 250 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_251 : TransitionPair 251 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_252 : TransitionPair 252 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_253 : TransitionPair 253 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_254 : TransitionPair 254 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_255 : TransitionPair 255 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_256 : TransitionPair 256 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_257 : TransitionPair 257 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_258 : TransitionPair 258 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_259 : TransitionPair 259 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_260 : TransitionPair 260 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_261 : TransitionPair 261 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_262 : TransitionPair 262 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_263 : TransitionPair 263 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_264 : TransitionPair 264 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_265 : TransitionPair 265 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_266 : TransitionPair 266 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_267 : TransitionPair 267 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_268 : TransitionPair 268 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_269 : TransitionPair 269 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_270 : TransitionPair 270 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_271 : TransitionPair 271 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_272 : TransitionPair 272 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_273 : TransitionPair 273 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_274 : TransitionPair 274 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_275 : TransitionPair 275 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_276 : TransitionPair 276 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_277 : TransitionPair 277 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_278 : TransitionPair 278 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_279 : TransitionPair 279 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_280 : TransitionPair 280 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_281 : TransitionPair 281 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_282 : TransitionPair 282 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_283 : TransitionPair 283 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_284 : TransitionPair 284 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_285 : TransitionPair 285 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_286 : TransitionPair 286 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_287 : TransitionPair 287 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_288 : TransitionPair 288 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_289 : TransitionPair 289 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_290 : TransitionPair 290 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_291 : TransitionPair 291 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_292 : TransitionPair 292 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_293 : TransitionPair 293 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_294 : TransitionPair 294 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_295 : TransitionPair 295 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_296 : TransitionPair 296 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_297 : TransitionPair 297 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_298 : TransitionPair 298 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_299 : TransitionPair 299 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_300 : TransitionPair 300 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_301 : TransitionPair 301 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_302 : TransitionPair 302 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_303 : TransitionPair 303 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_304 : TransitionPair 304 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_305 : TransitionPair 305 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_306 : TransitionPair 306 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_307 : TransitionPair 307 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_308 : TransitionPair 308 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_309 : TransitionPair 309 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_310 : TransitionPair 310 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_311 : TransitionPair 311 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_312 : TransitionPair 312 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_313 : TransitionPair 313 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_314 : TransitionPair 314 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_315 : TransitionPair 315 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_316 : TransitionPair 316 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_317 : TransitionPair 317 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_318 : TransitionPair 318 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_319 : TransitionPair 319 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_320 : TransitionPair 320 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_321 : TransitionPair 321 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_322 : TransitionPair 322 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_323 : TransitionPair 323 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_324 : TransitionPair 324 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_325 : TransitionPair 325 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_326 : TransitionPair 326 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_327 : TransitionPair 327 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_328 : TransitionPair 328 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_329 : TransitionPair 329 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_330 : TransitionPair 330 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_331 : TransitionPair 331 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_332 : TransitionPair 332 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_333 : TransitionPair 333 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_334 : TransitionPair 334 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_335 : TransitionPair 335 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_336 : TransitionPair 336 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_337 : TransitionPair 337 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_338 : TransitionPair 338 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_339 : TransitionPair 339 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_340 : TransitionPair 340 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_341 : TransitionPair 341 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_342 : TransitionPair 342 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_343 : TransitionPair 343 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_344 : TransitionPair 344 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_345 : TransitionPair 345 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_346 : TransitionPair 346 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_347 : TransitionPair 347 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_348 : TransitionPair 348 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_349 : TransitionPair 349 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_350 : TransitionPair 350 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_351 : TransitionPair 351 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_352 : TransitionPair 352 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_353 : TransitionPair 353 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_354 : TransitionPair 354 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_355 : TransitionPair 355 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_356 : TransitionPair 356 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_357 : TransitionPair 357 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_358 : TransitionPair 358 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_359 : TransitionPair 359 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_360 : TransitionPair 360 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_361 : TransitionPair 361 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_362 : TransitionPair 362 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_363 : TransitionPair 363 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_364 : TransitionPair 364 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_365 : TransitionPair 365 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_366 : TransitionPair 366 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_367 : TransitionPair 367 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_368 : TransitionPair 368 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_369 : TransitionPair 369 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_370 : TransitionPair 370 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_371 : TransitionPair 371 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_372 : TransitionPair 372 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_373 : TransitionPair 373 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_374 : TransitionPair 374 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_375 : TransitionPair 375 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_376 : TransitionPair 376 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_377 : TransitionPair 377 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_378 : TransitionPair 378 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_379 : TransitionPair 379 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_380 : TransitionPair 380 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_381 : TransitionPair 381 := by constructor <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 80000000 in
def pair_382 : TransitionPair 382 := by constructor <;> decide +kernel

set_option maxHeartbeats 4000000 in
lemma transition_pairs (b : Fin 383) : TransitionPair b := by
  fin_cases b
  · exact pair_0
  · exact pair_1
  · exact pair_2
  · exact pair_3
  · exact pair_4
  · exact pair_5
  · exact pair_6
  · exact pair_7
  · exact pair_8
  · exact pair_9
  · exact pair_10
  · exact pair_11
  · exact pair_12
  · exact pair_13
  · exact pair_14
  · exact pair_15
  · exact pair_16
  · exact pair_17
  · exact pair_18
  · exact pair_19
  · exact pair_20
  · exact pair_21
  · exact pair_22
  · exact pair_23
  · exact pair_24
  · exact pair_25
  · exact pair_26
  · exact pair_27
  · exact pair_28
  · exact pair_29
  · exact pair_30
  · exact pair_31
  · exact pair_32
  · exact pair_33
  · exact pair_34
  · exact pair_35
  · exact pair_36
  · exact pair_37
  · exact pair_38
  · exact pair_39
  · exact pair_40
  · exact pair_41
  · exact pair_42
  · exact pair_43
  · exact pair_44
  · exact pair_45
  · exact pair_46
  · exact pair_47
  · exact pair_48
  · exact pair_49
  · exact pair_50
  · exact pair_51
  · exact pair_52
  · exact pair_53
  · exact pair_54
  · exact pair_55
  · exact pair_56
  · exact pair_57
  · exact pair_58
  · exact pair_59
  · exact pair_60
  · exact pair_61
  · exact pair_62
  · exact pair_63
  · exact pair_64
  · exact pair_65
  · exact pair_66
  · exact pair_67
  · exact pair_68
  · exact pair_69
  · exact pair_70
  · exact pair_71
  · exact pair_72
  · exact pair_73
  · exact pair_74
  · exact pair_75
  · exact pair_76
  · exact pair_77
  · exact pair_78
  · exact pair_79
  · exact pair_80
  · exact pair_81
  · exact pair_82
  · exact pair_83
  · exact pair_84
  · exact pair_85
  · exact pair_86
  · exact pair_87
  · exact pair_88
  · exact pair_89
  · exact pair_90
  · exact pair_91
  · exact pair_92
  · exact pair_93
  · exact pair_94
  · exact pair_95
  · exact pair_96
  · exact pair_97
  · exact pair_98
  · exact pair_99
  · exact pair_100
  · exact pair_101
  · exact pair_102
  · exact pair_103
  · exact pair_104
  · exact pair_105
  · exact pair_106
  · exact pair_107
  · exact pair_108
  · exact pair_109
  · exact pair_110
  · exact pair_111
  · exact pair_112
  · exact pair_113
  · exact pair_114
  · exact pair_115
  · exact pair_116
  · exact pair_117
  · exact pair_118
  · exact pair_119
  · exact pair_120
  · exact pair_121
  · exact pair_122
  · exact pair_123
  · exact pair_124
  · exact pair_125
  · exact pair_126
  · exact pair_127
  · exact pair_128
  · exact pair_129
  · exact pair_130
  · exact pair_131
  · exact pair_132
  · exact pair_133
  · exact pair_134
  · exact pair_135
  · exact pair_136
  · exact pair_137
  · exact pair_138
  · exact pair_139
  · exact pair_140
  · exact pair_141
  · exact pair_142
  · exact pair_143
  · exact pair_144
  · exact pair_145
  · exact pair_146
  · exact pair_147
  · exact pair_148
  · exact pair_149
  · exact pair_150
  · exact pair_151
  · exact pair_152
  · exact pair_153
  · exact pair_154
  · exact pair_155
  · exact pair_156
  · exact pair_157
  · exact pair_158
  · exact pair_159
  · exact pair_160
  · exact pair_161
  · exact pair_162
  · exact pair_163
  · exact pair_164
  · exact pair_165
  · exact pair_166
  · exact pair_167
  · exact pair_168
  · exact pair_169
  · exact pair_170
  · exact pair_171
  · exact pair_172
  · exact pair_173
  · exact pair_174
  · exact pair_175
  · exact pair_176
  · exact pair_177
  · exact pair_178
  · exact pair_179
  · exact pair_180
  · exact pair_181
  · exact pair_182
  · exact pair_183
  · exact pair_184
  · exact pair_185
  · exact pair_186
  · exact pair_187
  · exact pair_188
  · exact pair_189
  · exact pair_190
  · exact pair_191
  · exact pair_192
  · exact pair_193
  · exact pair_194
  · exact pair_195
  · exact pair_196
  · exact pair_197
  · exact pair_198
  · exact pair_199
  · exact pair_200
  · exact pair_201
  · exact pair_202
  · exact pair_203
  · exact pair_204
  · exact pair_205
  · exact pair_206
  · exact pair_207
  · exact pair_208
  · exact pair_209
  · exact pair_210
  · exact pair_211
  · exact pair_212
  · exact pair_213
  · exact pair_214
  · exact pair_215
  · exact pair_216
  · exact pair_217
  · exact pair_218
  · exact pair_219
  · exact pair_220
  · exact pair_221
  · exact pair_222
  · exact pair_223
  · exact pair_224
  · exact pair_225
  · exact pair_226
  · exact pair_227
  · exact pair_228
  · exact pair_229
  · exact pair_230
  · exact pair_231
  · exact pair_232
  · exact pair_233
  · exact pair_234
  · exact pair_235
  · exact pair_236
  · exact pair_237
  · exact pair_238
  · exact pair_239
  · exact pair_240
  · exact pair_241
  · exact pair_242
  · exact pair_243
  · exact pair_244
  · exact pair_245
  · exact pair_246
  · exact pair_247
  · exact pair_248
  · exact pair_249
  · exact pair_250
  · exact pair_251
  · exact pair_252
  · exact pair_253
  · exact pair_254
  · exact pair_255
  · exact pair_256
  · exact pair_257
  · exact pair_258
  · exact pair_259
  · exact pair_260
  · exact pair_261
  · exact pair_262
  · exact pair_263
  · exact pair_264
  · exact pair_265
  · exact pair_266
  · exact pair_267
  · exact pair_268
  · exact pair_269
  · exact pair_270
  · exact pair_271
  · exact pair_272
  · exact pair_273
  · exact pair_274
  · exact pair_275
  · exact pair_276
  · exact pair_277
  · exact pair_278
  · exact pair_279
  · exact pair_280
  · exact pair_281
  · exact pair_282
  · exact pair_283
  · exact pair_284
  · exact pair_285
  · exact pair_286
  · exact pair_287
  · exact pair_288
  · exact pair_289
  · exact pair_290
  · exact pair_291
  · exact pair_292
  · exact pair_293
  · exact pair_294
  · exact pair_295
  · exact pair_296
  · exact pair_297
  · exact pair_298
  · exact pair_299
  · exact pair_300
  · exact pair_301
  · exact pair_302
  · exact pair_303
  · exact pair_304
  · exact pair_305
  · exact pair_306
  · exact pair_307
  · exact pair_308
  · exact pair_309
  · exact pair_310
  · exact pair_311
  · exact pair_312
  · exact pair_313
  · exact pair_314
  · exact pair_315
  · exact pair_316
  · exact pair_317
  · exact pair_318
  · exact pair_319
  · exact pair_320
  · exact pair_321
  · exact pair_322
  · exact pair_323
  · exact pair_324
  · exact pair_325
  · exact pair_326
  · exact pair_327
  · exact pair_328
  · exact pair_329
  · exact pair_330
  · exact pair_331
  · exact pair_332
  · exact pair_333
  · exact pair_334
  · exact pair_335
  · exact pair_336
  · exact pair_337
  · exact pair_338
  · exact pair_339
  · exact pair_340
  · exact pair_341
  · exact pair_342
  · exact pair_343
  · exact pair_344
  · exact pair_345
  · exact pair_346
  · exact pair_347
  · exact pair_348
  · exact pair_349
  · exact pair_350
  · exact pair_351
  · exact pair_352
  · exact pair_353
  · exact pair_354
  · exact pair_355
  · exact pair_356
  · exact pair_357
  · exact pair_358
  · exact pair_359
  · exact pair_360
  · exact pair_361
  · exact pair_362
  · exact pair_363
  · exact pair_364
  · exact pair_365
  · exact pair_366
  · exact pair_367
  · exact pair_368
  · exact pair_369
  · exact pair_370
  · exact pair_371
  · exact pair_372
  · exact pair_373
  · exact pair_374
  · exact pair_375
  · exact pair_376
  · exact pair_377
  · exact pair_378
  · exact pair_379
  · exact pair_380
  · exact pair_381
  · exact pair_382

lemma transition_checked (i : Index) : transitionCheck i = true := by
  let b : Fin 383 := ⟨i.val / 2, by have := i.isLt; omega⟩
  have hp := transition_pairs b
  have hi : i.val = 2 * b.val ∨ i.val = 2 * b.val + 1 := by dsimp [b]; omega
  rcases hi with hi | hi
  · have hx : (⟨2 * b.val, by have := b.isLt; omega⟩ : Index) = i := Fin.ext hi.symm
    simpa only [hx] using hp.1
  · have hx : (⟨2 * b.val + 1, by have := b.isLt; omega⟩ : Index) = i := Fin.ext hi.symm
    simpa only [hx] using hp.2

end A165378Data

-- Component: A165378Children

namespace A165378Data
open A165378Proof

def childrenRowsCheck : Bool :=
  (List.finRange 766).all fun i =>
    decide (((childrenList i).map fun j => rowIndex (state j).row).Nodup)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
def children_rows_checked : childrenRowsCheck = true := by decide +kernel

lemma children_codes_nodup (i : Index) :
    ((childrenList i).map fun j => rowIndex (state j).row).Nodup := by
  exact of_decide_eq_true (List.all_eq_true.mp children_rows_checked i (List.mem_finRange i))

lemma children_mem (i j : Index) : j ∈ childrenList i ↔ j ∈ children i := by
  simp [children]

lemma child_injective (i j k : Index) (hj : j ∈ children i) (hk : k ∈ children i)
    (he : (state j).row = (state k).row) : j = k :=
  List.inj_on_of_nodup_map (children_codes_nodup i)
    ((children_mem i j).mpr hj) ((children_mem i k).mpr hk) (congrArg rowIndex he)

end A165378Data

-- Component: A165378Table

namespace A165378Data
open A165378Proof

lemma step_iff (i : Index) (r : Row) (t : State) :
    step (state i) r = some t ↔
      ∃ j ∈ children i, (state j).row = r ∧ state j = t := by
  have hs := transition_of_check i (transition_checked i) (rowIndex r)
  rw [rowOf_rowIndex] at hs
  rw [hs, lookupCode, fastLookup_eq, A165378TableLemmas.lookup_map_eq_some
    (fun j => rowIndex (state j).row) state (childrenList i) (children_codes_nodup i)]
  simp only [children_mem, rowIndex_injective.eq_iff]

lemma correctTable : A165378PathBridge.CorrectTable state starts children :=
  ⟨starts_rows, starts_initial, starts_injective, step_iff, child_injective⟩

end A165378Data

theorem OMA.solution : type_of% @OMA.S_oeis_a165378.main := by
  intro n hn
  exact A165378Finish.card_formula A165378Data.correctTable
    A165378Data.final_eq A165378Data.count_formula n hn
