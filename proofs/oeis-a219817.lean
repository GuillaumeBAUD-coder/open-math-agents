import OMAStatements.S_oeis_a219817
import Mathlib

/-!
Proof of Barker's conjectures for OEIS A219817.

Reading the source array row by row as a word of letters (rows of the long direction), the
derived array is a sliding-window map of radius one, and the sorted words form a regular
language: adjacent letters are lexicographically ordered, and each pair of adjacent tracks
carries a three-valued lexicographic comparison status. The library below proves, for any such
window map, that the set of configurations (guessed next letter, last letter, statuses) realised
by an output prefix evolves by an explicit successor relation, and that an output word is a
derived word exactly when a configuration with no next letter is realised. A subset automaton
over configuration codes (`stT`, `nxT`, checked by `decide +kernel`) then turns the number of
derived words into a sum of state counts, which obey a linear recursion. The 10-th difference of
the count vector of every live state vanishes from length 6 on (checked on the table `vecT`
and propagated by linearity), which gives Barker's recurrence; the g.f. follows from the
recurrence and the first terms.
-/


namespace MinNbLib
open Finset

/-! ## Lexicographic order lemmas -/

theorem concat_lt {α : Type*} [LinearOrder α] (a b : α) :
    ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
      (l₁ ++ [a] < l₂ ++ [b] ↔ l₁ < l₂ ∨ (l₁ = l₂ ∧ a < b))
  | [], [], _ => by simp [List.cons_lt_cons_iff]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l₁, y :: l₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.cons_append, List.cons_lt_cons_iff, concat_lt a b l₁ l₂ h, List.cons.injEq]
    constructor
    · rintro (h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩) <;> tauto
    · rintro ((h1 | ⟨rfl, h2⟩) | ⟨⟨rfl, rfl⟩, h3⟩) <;> tauto

/-- Three-valued comparison: 0 for less, 1 for equal, 2 for greater. -/
def cmp3 {α : Type*} [LinearOrder α] (a b : α) : Fin 3 :=
  if a < b then 0 else if a = b then 1 else 2

theorem cmp3_concat {α : Type*} [LinearOrder α] (a b : α) (l₁ l₂ : List α)
    (h : l₁.length = l₂.length) :
    cmp3 (l₁ ++ [a]) (l₂ ++ [b]) = if cmp3 l₁ l₂ = 1 then cmp3 a b else cmp3 l₁ l₂ := by
  have he : l₁ ++ [a] = l₂ ++ [b] ↔ l₁ = l₂ ∧ a = b := by
    constructor
    · intro h'; exact ⟨(List.append_inj h' h).1, by simpa using (List.append_inj h' h).2⟩
    · rintro ⟨rfl, rfl⟩; rfl
  unfold cmp3
  simp only [concat_lt a b l₁ l₂ h, he]
  by_cases h1 : l₁ < l₂
  · have : l₁ ≠ l₂ := ne_of_lt h1
    simp [h1, this]
  · by_cases h2 : l₁ = l₂
    · subst h2; simp
    · simp [h1, h2]

theorem cmp3_ne_two {α : Type*} [LinearOrder α] (a b : α) : cmp3 a b ≠ 2 ↔ a ≤ b := by
  unfold cmp3
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le]
  · subst h; simp
  · simp [not_lt.2 h.le, ne_of_gt h, not_le.2 h]

theorem cmp3_ne_zero {α : Type*} [LinearOrder α] (a b : α) : cmp3 a b ≠ 0 ↔ b ≤ a := by
  unfold cmp3
  rcases lt_trichotomy a b with h | h | h
  · simp [h, not_le.2 h]
  · subst h; simp
  · simp [not_lt.2 h.le, ne_of_gt h, h.le]

/-- `rel d x y` : `x ≤ y` when `d`, else `y ≤ x`. -/
def rel {α : Type*} [LinearOrder α] (d : Bool) (x y : α) : Prop := if d then x ≤ y else y ≤ x

instance {α : Type*} [LinearOrder α] (d : Bool) (x y : α) : Decidable (rel d x y) := by
  unfold rel; split <;> infer_instance

/-- monotone when `d`, antitone otherwise -/
def ordB {α : Type*} [Preorder α] {n : ℕ} (d : Bool) (f : Fin n → α) : Prop :=
  if d then Monotone f else Antitone f

theorem ordB_iff {α : Type*} [LinearOrder α] {n : ℕ} (d : Bool) (f : Fin n → α) :
    ordB d f ↔ ∀ (i : ℕ) (h : i + 1 < n), rel d (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩) := by
  rcases n with _ | n
  · simp only [ordB]; split <;> simp [Monotone, Antitone]
  · cases d
    · simp only [ordB, rel, Bool.false_eq_true, ↓reduceIte, Fin.antitone_iff_succ_le]
      constructor
      · intro h i hi; exact h ⟨i, by omega⟩
      · intro h i; exact h i.1 (by omega)
    · simp only [ordB, rel, ↓reduceIte, Fin.monotone_iff_le_succ]
      constructor
      · intro h i hi; exact h ⟨i, by omega⟩
      · intro h i; exact h i.1 (by omega)


/-! ## Words of letters -/

abbrev Ltr (w m : ℕ) := Fin w → Fin (m + 1)

variable {w m : ℕ}

def track {n : ℕ} (W : Fin n → Ltr w m) (s : Fin w) : List (Fin (m + 1)) :=
  List.ofFn (fun t => W t s)

def sortedW (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) : Prop :=
  ordB dL (fun t => List.ofFn (W t)) ∧ ordB dT (fun s => track W s)

def stW {n : ℕ} (W : Fin n → Ltr w m) (s : Fin w) : Fin 3 :=
  if h : s.1 + 1 < w then cmp3 (track W s) (track W ⟨s.1 + 1, h⟩) else 1

def upd (st : Fin w → Fin 3) (x : Ltr w m) (s : Fin w) : Fin 3 :=
  if h : s.1 + 1 < w then (if st s = 1 then cmp3 (x s) (x ⟨s.1 + 1, h⟩) else st s) else 1

def bad (dT : Bool) : Fin 3 := if dT then 2 else 0

def okSt (dT : Bool) (st : Fin w → Fin 3) : Prop := ∀ s : Fin w, s.1 + 1 < w → st s ≠ bad dT

instance (dT : Bool) (st : Fin w → Fin 3) : Decidable (okSt dT st) := by
  unfold okSt; infer_instance

def lastOpt {n : ℕ} (W : Fin n → Ltr w m) : Option (Ltr w m) :=
  if h : 0 < n then some (W ⟨n - 1, by omega⟩) else none

theorem snoc_lt {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) (k : ℕ) (hk : k < n) :
    (Fin.snoc W x : Fin (n + 1) → Ltr w m) ⟨k, by omega⟩ = W ⟨k, hk⟩ := by
  simp [Fin.snoc, hk]

theorem snoc_eq {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    (Fin.snoc W x : Fin (n + 1) → Ltr w m) ⟨n, by omega⟩ = x := by
  simp [Fin.snoc]

theorem track_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) (s : Fin w) :
    track (Fin.snoc W x : Fin (n + 1) → Ltr w m) s = track W s ++ [x s] := by
  simp only [track, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

theorem stW_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    stW (Fin.snoc W x : Fin (n + 1) → Ltr w m) = upd (stW W) x := by
  funext s
  unfold stW upd
  split
  · rename_i h
    rw [track_snoc, track_snoc, cmp3_concat _ _ _ _ (by simp [track])]
    simp only [dif_pos h]
  · rfl

theorem stW_zero (W : Fin 0 → Ltr w m) : stW W = fun _ => 1 := by
  funext s; unfold stW; split
  · simp [track, cmp3]
  · rfl

theorem lastOpt_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    lastOpt (Fin.snoc W x : Fin (n + 1) → Ltr w m) = some x := by
  simp only [lastOpt, Nat.zero_lt_succ, ↓reduceDIte, Nat.add_sub_cancel]
  rw [snoc_eq]

theorem lastOpt_zero (W : Fin 0 → Ltr w m) : lastOpt W = none := by simp [lastOpt]

theorem ordB_track_iff (dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) :
    ordB dT (fun s => track W s) ↔ okSt dT (stW W) := by
  rw [ordB_iff]
  constructor
  · intro h s hs
    unfold stW bad
    rw [dif_pos hs]
    · have := h s.1 hs
      cases dT
      · simp only [rel, Bool.false_eq_true, ↓reduceIte] at this ⊢
        exact (cmp3_ne_zero _ _).2 this
      · simp only [rel, ↓reduceIte] at this ⊢
        exact (cmp3_ne_two _ _).2 this
  · intro h i hi
    have := h ⟨i, by omega⟩ hi
    simp only [stW, bad, hi, ↓reduceDIte] at this
    cases dT
    · simp only [rel, Bool.false_eq_true, ↓reduceIte] at this ⊢
      exact (cmp3_ne_zero _ _).1 this
    · simp only [rel, ↓reduceIte] at this ⊢
      exact (cmp3_ne_two _ _).1 this

theorem okSt_of_upd (dT : Bool) (st : Fin w → Fin 3) (x : Ltr w m) :
    okSt dT (upd st x) → okSt dT st := by
  intro h s hs
  have := h s hs
  unfold upd at this
  rw [dif_pos hs] at this
  split at this
  · rename_i h1; rw [h1]; cases dT <;> decide
  · exact this


theorem sortedW_snoc (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    sortedW dL dT (Fin.snoc W x : Fin (n + 1) → Ltr w m) ↔
      sortedW dL dT W ∧ (∀ y, lastOpt W = some y → rel dL (List.ofFn y) (List.ofFn x)) ∧
        okSt dT (upd (stW W) x) := by
  unfold sortedW
  rw [ordB_track_iff, ordB_track_iff, stW_snoc, ordB_iff, ordB_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i hi => ?_, okSt_of_upd _ _ _ h2⟩, fun y hy => ?_, h2⟩
    · have := h1 i (by omega)
      rwa [snoc_lt W x i (by omega), snoc_lt W x (i + 1) hi] at this
    · simp only [lastOpt] at hy
      split at hy
      · rename_i hn
        cases hy
        have := h1 (n - 1) (by omega)
        rw [snoc_lt W x (n - 1) (by omega)] at this
        have e : n - 1 + 1 = n := by omega
        simp only [e] at this
        rwa [snoc_eq] at this
      · cases hy
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    refine ⟨fun i hi => ?_, h4⟩
    by_cases hin : i + 1 < n
    · rw [snoc_lt W x i (by omega), snoc_lt W x (i + 1) hin]
      exact h1 i hin
    · have e : i + 1 = n := by omega
      subst e
      rw [snoc_lt W x i (by omega), snoc_eq]
      apply h3
      simp [lastOpt]

instance (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) : Decidable (sortedW dL dT W) := by
  unfold sortedW ordB; split <;> split <;> infer_instance

/-! ## Window outputs -/

def val (o : Option (Ltr w m)) (s : Fin w) : Fin (m + 1) :=
  match o with
  | none => ⊤
  | some y => y s

def pick (dd : Fin 3) (l : Option (Ltr w m)) (x : Ltr w m) (q : Option (Ltr w m)) :
    Option (Ltr w m) :=
  if dd.1 = 0 then l else if dd.1 = 1 then some x else q

section Window
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)]

/-- Output letter at a position whose left, own and right letters are `l`, `x`, `q`. -/
def out (l : Option (Ltr w m)) (x : Ltr w m) (q : Option (Ltr w m)) : Ltr w m := fun s =>
  ((univ : Finset (Fin 3 × Fin w)).filter (fun p => nbL 1 s p.1 p.2)).inf
    (fun p => val (pick p.1 l x q) p.2)

def prevOf {n : ℕ} (W : Fin n → Ltr w m) (t : Fin n) : Option (Ltr w m) :=
  if h : t.1 = 0 then none else some (W ⟨t.1 - 1, by omega⟩)

def nextOf {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) (t : Fin n) :
    Option (Ltr w m) :=
  if h : t.1 + 1 < n then some (W ⟨t.1 + 1, h⟩) else q

/-- Window outputs of `W`, the letter after the end being `q`. -/
def Fs {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) : Fin n → Ltr w m :=
  fun t => out nbL (prevOf W t) (W t) (nextOf q W t)

/-- The neighbourhood minimum of `W` itself. -/
def Fmin {n : ℕ} (W : Fin n → Ltr w m) : Fin n → Ltr w m := fun t s =>
  ((univ : Finset (Fin n × Fin w)).filter (fun p => nbL t s p.1 p.2)).inf (fun p => W p.1 p.2)

theorem Fmin_eq (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    {n : ℕ} (W : Fin n → Ltr w m) : Fmin nbL W = Fs nbL none W := by
  funext t s
  simp only [Fmin, Fs, out]
  apply le_antisymm
  · apply Finset.le_inf
    rintro ⟨dd, s'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [pick]
    fin_cases dd
    · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, ↓reduceIte, prevOf]
      split
      · exact le_top
      · rename_i ht
        simp only [val]
        apply Finset.inf_le (b := ((⟨t.1 - 1, by omega⟩ : Fin n), s'))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnb]; left; exact ⟨by omega, hp⟩
    · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte, val]
      apply Finset.inf_le (b := (t, s'))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hnb]; right; left; exact ⟨rfl, hp⟩
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, nextOf]
      split
      · rename_i ht
        simp only [val]
        apply Finset.inf_le (b := ((⟨t.1 + 1, ht⟩ : Fin n), s'))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnb]; right; right; exact ⟨rfl, hp⟩
      · exact le_top
  · apply Finset.le_inf
    rintro ⟨t', s'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hnb] at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (0, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_zero, ↓reduceIte, prevOf]
      rw [dif_neg (by omega)]
      simp only [val]
      have e : (⟨t.1 - 1, by omega⟩ : Fin n) = t' := Fin.ext (by simp; omega)
      rw [e]
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (1, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte, val]
      have e : t = t' := Fin.ext h1.symm
      rw [e]
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (2, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, nextOf]
      rw [dif_pos (by omega)]
      simp only [val]
      have e : (⟨t.1 + 1, by omega⟩ : Fin n) = t' := Fin.ext (by simp; omega)
      rw [e]

theorem Fs_snoc {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) (x : Ltr w m) :
    Fs nbL q (Fin.snoc W x : Fin (n + 1) → Ltr w m) =
      Fin.snoc (Fs nbL (some x) W) (out nbL (lastOpt W) x q) := by
  funext t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · rw [Fin.snoc_last]
    simp only [Fs, Fin.snoc_last]
    congr 1
    · simp only [prevOf, Fin.val_last, lastOpt]
      by_cases hn : n = 0
      · subst hn; simp
      · rw [dif_neg hn, dif_pos (by omega), snoc_lt W x (n - 1) (by omega)]
    · simp [nextOf]
  · rw [Fin.snoc_castSucc]
    simp only [Fs, Fin.snoc_castSucc]
    congr 1
    · simp only [prevOf, Fin.val_castSucc]
      split
      · rfl
      · rw [snoc_lt W x (i.1 - 1) (by omega)]
    · simp only [nextOf, Fin.val_castSucc]
      by_cases hi : i.1 + 1 < n
      · rw [dif_pos (by omega), dif_pos hi, snoc_lt W x (i.1 + 1) hi]
      · rw [dif_pos (by omega), dif_neg hi]
        have e : i.1 + 1 = n := by omega
        simp only [e]; rw [snoc_eq]


/-! ## Configurations -/

/-- (guessed next letter, last letter, track statuses) -/
abbrev Cfg (w m : ℕ) := Option (Ltr w m) × Option (Ltr w m) × (Fin w → Fin 3)

variable (dL dT : Bool)

def sortedSO {n : ℕ} (W : Fin n → Ltr w m) (q : Option (Ltr w m)) : Prop :=
  sortedW dL dT W ∧ ∀ x, q = some x → sortedW dL dT (Fin.snoc W x : Fin (n + 1) → Ltr w m)

/-- `c` is realized by the output prefix `B`. -/
def Rz {n : ℕ} (B : Fin n → Ltr w m) (c : Cfg w m) : Prop :=
  ∃ W : Fin n → Ltr w m, sortedSO dL dT W c.1 ∧ stW W = c.2.2 ∧ lastOpt W = c.2.1 ∧
    Fs nbL c.1 W = B

def guard (x : Ltr w m) (st' : Fin w → Fin 3) (q' : Option (Ltr w m)) : Prop :=
  ∀ y, q' = some y → rel dL (List.ofFn x) (List.ofFn y) ∧ okSt dT (upd st' y)

def stepRel (c : Cfg w m) (b : Ltr w m) (c' : Cfg w m) : Prop :=
  ∃ x, c.1 = some x ∧ c'.2.1 = some x ∧ c'.2.2 = upd c.2.2 x ∧ out nbL c.2.1 x c'.1 = b ∧
    guard dL dT x c'.2.2 c'.1

theorem snoc_inj {n : ℕ} {B B' : Fin n → Ltr w m} {b b' : Ltr w m}
    (h : (Fin.snoc B b : Fin (n + 1) → Ltr w m) = Fin.snoc B' b') : B = B' ∧ b = b' := by
  constructor
  · have := congrArg Fin.init h; simpa only [Fin.init_snoc] using this
  · have := congrFun h (Fin.last n); simpa only [Fin.snoc_last] using this

theorem Rz_snoc {n : ℕ} (B : Fin n → Ltr w m) (b : Ltr w m) (c' : Cfg w m) :
    Rz nbL dL dT (Fin.snoc B b : Fin (n + 1) → Ltr w m) c' ↔
      ∃ c, Rz nbL dL dT B c ∧ stepRel nbL dL dT c b c' := by
  constructor
  · rintro ⟨W'', ⟨hs1, hs2⟩, hst, hl, hF⟩
    rw [← Fin.snoc_init_self W''] at hs1 hs2 hst hl hF
    set W := Fin.init W''
    set x := W'' (Fin.last n)
    rw [Fs_snoc] at hF
    obtain ⟨hB, hb⟩ := snoc_inj hF
    obtain ⟨hW, _, _⟩ := (sortedW_snoc dL dT W x).1 hs1
    refine ⟨(some x, lastOpt W, stW W), ⟨W, ⟨hW, ?_⟩, rfl, rfl, hB⟩, x, rfl, ?_, ?_, hb, ?_⟩
    · rintro x' ⟨⟩; exact hs1
    · rw [← hl, lastOpt_snoc]
    · rw [← hst, stW_snoc]
    · intro y hy
      obtain ⟨_, h2, h3⟩ := (sortedW_snoc dL dT _ y).1 (hs2 y hy)
      refine ⟨h2 x (lastOpt_snoc W x), ?_⟩
      rw [← hst]; exact h3
  · rintro ⟨c, ⟨W, ⟨hs1, hs2⟩, hst, hl, hF⟩, x, hx, h1, h2, h3, h4⟩
    refine ⟨Fin.snoc W x, ⟨hs2 x hx, fun y hy => ?_⟩, ?_, ?_, ?_⟩
    · rw [sortedW_snoc]
      obtain ⟨g1, g2⟩ := h4 y hy
      refine ⟨hs2 x hx, ?_, ?_⟩
      · intro y' hy'; rw [lastOpt_snoc] at hy'; cases hy'; exact g1
      · rw [stW_snoc, hst, ← h2]; exact g2
    · rw [stW_snoc, hst, h2]
    · rw [lastOpt_snoc, h1]
    · rw [Fs_snoc, ← hx, hF, hl, h3]

def guard0 (q : Option (Ltr w m)) : Prop := ∀ y, q = some y → okSt dT (upd (fun _ => 1) y)

theorem sortedW_zero (W : Fin 0 → Ltr w m) : sortedW dL dT W := by
  refine ⟨?_, ?_⟩
  · rw [ordB_iff]; intro i hi; omega
  · rw [ordB_track_iff, stW_zero]; intro s _; cases dT <;> simp [bad]

theorem Rz_zero (B : Fin 0 → Ltr w m) (c : Cfg w m) :
    Rz nbL dL dT B c ↔ c.2.1 = none ∧ c.2.2 = (fun _ => 1) ∧ guard0 dT c.1 := by
  constructor
  · rintro ⟨W, ⟨_, hs2⟩, hst, hl, _⟩
    refine ⟨by rw [← hl, lastOpt_zero], by rw [← hst, stW_zero], fun y hy => ?_⟩
    have := (sortedW_snoc dL dT W y).1 (hs2 y hy)
    rw [stW_zero] at this; exact this.2.2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨B, ⟨sortedW_zero dL dT B, fun y hy => ?_⟩, by rw [stW_zero, h2], by rw [lastOpt_zero, h1],
      funext (fun i => i.elim0)⟩
    rw [sortedW_snoc]
    refine ⟨sortedW_zero dL dT B, ⟨(fun y' hy' => by rw [lastOpt_zero] at hy'; cases hy'), ?_⟩⟩
    rw [stW_zero]; exact h3 y hy

theorem image_iff (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    {n : ℕ} (B : Fin n → Ltr w m) :
    (∃ W, sortedW dL dT W ∧ Fmin nbL W = B) ↔ ∃ c, Rz nbL dL dT B c ∧ c.1 = none := by
  constructor
  · rintro ⟨W, hW, hF⟩
    refine ⟨(none, lastOpt W, stW W), ⟨W, ⟨hW, fun x hx => by cases hx⟩, rfl, rfl, ?_⟩, rfl⟩
    rw [← hF, Fmin_eq nbL hnb]
  · rintro ⟨c, ⟨W, ⟨hW, _⟩, _, _, hF⟩, hc⟩
    refine ⟨W, hW, ?_⟩
    rw [Fmin_eq nbL hnb, ← hc, hF]


end Window

/-! ## Codes -/

def dec (x : ℕ) : Ltr w m := fun s => ⟨x / (m + 1) ^ s.1 % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

def enc (f : Ltr w m) : ℕ := ∑ i, (f i : ℕ) * (m + 1) ^ (i : ℕ)

theorem enc_eq (f : Ltr w m) : enc f = (finFunctionFinEquiv f : ℕ) := by
  rw [finFunctionFinEquiv_apply]; rfl

theorem dec_enc (f : Ltr w m) : dec (enc f) = f := by
  funext s
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) s
  rw [Equiv.symm_apply_apply] at this
  simp only [dec, enc_eq]
  exact this.symm

theorem enc_lt (f : Ltr w m) : enc f < (m + 1) ^ w := by
  rw [enc_eq]; exact (finFunctionFinEquiv f).2

theorem enc_dec (x : ℕ) (hx : x < (m + 1) ^ w) : enc (dec x : Ltr w m) = x := by
  have h1 : (dec x : Ltr w m) = finFunctionFinEquiv.symm ⟨x, hx⟩ := by
    funext s; apply Fin.ext; rw [finFunctionFinEquiv_symm_apply_val]; rfl
  rw [h1, enc_eq, Equiv.apply_symm_apply]

def decS (z : ℕ) : Fin w → Fin 3 := fun s => ⟨z / 3 ^ s.1 % 3, Nat.mod_lt _ (by norm_num)⟩

def encS (st : Fin w → Fin 3) : ℕ := ∑ i, (st i : ℕ) * 3 ^ (i : ℕ)

theorem decS_encS (st : Fin w → Fin 3) : decS (encS st) = st := by
  funext s
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv st) s
  rw [Equiv.symm_apply_apply] at this
  simp only [decS, encS]
  rw [this, finFunctionFinEquiv_apply]

def decO (x : ℕ) : Option (Ltr w m) := if x = 0 then none else some (dec (x - 1))

def encO : Option (Ltr w m) → ℕ
  | none => 0
  | some f => enc f + 1

theorem decO_encO (o : Option (Ltr w m)) : decO (encO o) = o := by
  cases o <;> simp [decO, encO, dec_enc]

theorem encO_lt (o : Option (Ltr w m)) : encO o < (m + 1) ^ w + 1 := by
  cases o <;> simp [encO, enc_lt]

variable (w m) in
abbrev KO : ℕ := (m + 1) ^ w + 1

def decC (c : ℕ) : Cfg w m :=
  (decO (c % KO w m), decO (c / KO w m % KO w m), decS (c / KO w m / KO w m))

variable (w m) in
def mkC (q l z : ℕ) : ℕ := q + KO w m * (l + KO w m * z)

theorem decC_mkC (q l z : ℕ) (hq : q < KO w m) (hl : l < KO w m) :
    (decC (mkC w m q l z) : Cfg w m) = (decO q, decO l, decS z) := by
  have hK : 0 < KO w m := by positivity
  simp only [decC, mkC]
  have e1 : (q + KO w m * (l + KO w m * z)) % KO w m = q := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  have e2 : (q + KO w m * (l + KO w m * z)) / KO w m = l + KO w m * z := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hq, zero_add]
  rw [e1, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl, Nat.add_mul_div_left _ _ hK,
    Nat.div_eq_of_lt hl, zero_add]

theorem decO_ne_none {q : ℕ} : (decO q : Option (Ltr w m)) = none ↔ q = 0 := by
  unfold decO; split <;> simp_all

section CodeStep
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)] (dL dT : Bool)
variable (outTab : List (List (List ℕ)))

/-- Table lookup for the output letter code of a window (l, x, q). -/
def outL (outTab : List (List (List ℕ))) (l x q : ℕ) : ℕ := ((outTab.getD l []).getD x []).getD q 0

def guardB (x : Ltr w m) (st' : Fin w → Fin 3) (q' : ℕ) : Bool :=
  q' == 0 || (decide (rel dL (List.ofFn x) (List.ofFn (dec (q' - 1) : Ltr w m))) &&
    decide (okSt dT (upd st' (dec (q' - 1) : Ltr w m))))

theorem guardB_iff (x : Ltr w m) (st' : Fin w → Fin 3) (q' : ℕ) :
    guardB dL dT x st' q' = true ↔ guard dL dT x st' (decO q') := by
  unfold guardB guard decO
  by_cases h : q' = 0
  · simp [h]
  · simp [h]

variable (w m) in
/-- Code successors of configuration code `c` on output letter code `b`. -/
def succC (c b : ℕ) : List ℕ :=
  if c % KO w m = 0 then [] else
    ((List.range (KO w m)).filter (fun q' =>
      outL outTab (c / KO w m % KO w m) (c % KO w m - 1) q' == b &&
      guardB dL dT (dec (c % KO w m - 1) : Ltr w m)
        (upd (decS (c / KO w m / KO w m)) (dec (c % KO w m - 1) : Ltr w m)) q')).map
      (fun q' => mkC w m q' (c % KO w m)
        (encS (upd (decS (c / KO w m / KO w m)) (dec (c % KO w m - 1) : Ltr w m))))

open Classical in
noncomputable def δ (b : Ltr w m) (S : Finset (Cfg w m)) : Finset (Cfg w m) :=
  univ.filter (fun c' => ∃ c ∈ S, stepRel nbL dL dT c b c')

variable {outTab} in
theorem succC_spec (hOut : ∀ l < KO w m, ∀ x < (m + 1) ^ w, ∀ q < KO w m,
      outL outTab l x q = enc (out nbL (decO l) (dec x : Ltr w m) (decO q)))
    (c b : ℕ) (hb : b < (m + 1) ^ w) (c' : Cfg w m) :
    stepRel nbL dL dT (decC c) (dec b) c' ↔ ∃ c₂ ∈ succC w m dL dT outTab c b, decC c₂ = c' := by
  obtain ⟨q', l', st'⟩ := c'
  have hq : c % KO w m < KO w m := Nat.mod_lt _ (by positivity)
  have hl : c / KO w m % KO w m < KO w m := Nat.mod_lt _ (by positivity)
  simp only [stepRel, decC, succC]
  by_cases h0 : c % KO w m = 0
  · simp [h0, decO]
  · simp only [h0, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      beq_iff_eq, guardB_iff]
    have hd : (decO (c % KO w m) : Option (Ltr w m)) = some (dec (c % KO w m - 1)) := by
      simp [decO, h0]
    rw [hd]
    constructor
    · rintro ⟨x, ⟨⟩, rfl, rfl, h3, h4⟩
      refine ⟨mkC w m (encO q') (c % KO w m) (encS (upd (decS (c / KO w m / KO w m))
        (dec (c % KO w m - 1)))), ⟨encO q', ⟨encO_lt q', ?_, ?_⟩, rfl⟩, ?_⟩
      · rw [hOut _ hl _ (by have := hq; simp only [KO] at this ⊢; omega) _ (encO_lt q'), decO_encO, h3, enc_dec b hb]
      · rw [decO_encO]; exact h4
      · rw [← decC, decC_mkC _ _ _ (encO_lt q') hq, decO_encO, hd, decS_encS]
    · rintro ⟨c₂, ⟨q₂, ⟨hq₂, h3, h4⟩, rfl⟩, he⟩
      rw [← decC, decC_mkC _ _ _ hq₂ hq, hd, decS_encS] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨_, rfl, rfl, rfl, ?_, h4⟩
      rw [← h3, hOut _ hl _ (by have := hq; simp only [KO] at this ⊢; omega) _ hq₂, dec_enc]

variable {outTab} in
theorem δ_code (hOut : ∀ l < KO w m, ∀ x < (m + 1) ^ w, ∀ q < KO w m,
      outL outTab l x q = enc (out nbL (decO l) (dec x : Ltr w m) (decO q)))
    (L : List ℕ) (b : ℕ) (hb : b < (m + 1) ^ w) :
    δ nbL dL dT (dec b) ((L.map (fun c => (decC c : Cfg w m))).toFinset) =
      ((L.flatMap (fun c => succC w m dL dT outTab c b)).map (fun c => (decC c : Cfg w m))).toFinset := by
  ext c'
  simp only [δ, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map,
    List.mem_flatMap]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hs⟩
    obtain ⟨c₂, h1, h2⟩ := (succC_spec nbL dL dT hOut c b hb c').1 hs
    exact ⟨c₂, ⟨c, hc, h1⟩, h2⟩
  · rintro ⟨c₂, ⟨c, hc, h1⟩, h2⟩
    exact ⟨decC c, ⟨c, hc, rfl⟩, (succC_spec nbL dL dT hOut c b hb c').2 ⟨c₂, h1, h2⟩⟩


end CodeStep

/-! ## Bit masks -/

def maskOf (L : List ℕ) : ℕ := L.foldr (fun c acc => acc ||| (1 <<< c)) 0

theorem testBit_maskOf (L : List ℕ) (j : ℕ) : (maskOf L).testBit j = true ↔ j ∈ L := by
  induction L with
  | nil => simp [maskOf]
  | cons c L ih =>
    simp only [maskOf, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, List.mem_cons]
    tauto

theorem mem_iff_of_mask {L₁ L₂ : List ℕ} (h : maskOf L₁ = maskOf L₂) (j : ℕ) :
    j ∈ L₁ ↔ j ∈ L₂ := by
  rw [← testBit_maskOf, ← testBit_maskOf, h]

theorem toFinset_map_of_mask {α : Type*} [DecidableEq α] (f : ℕ → α) {L₁ L₂ : List ℕ}
    (h : maskOf L₁ = maskOf L₂) : (L₁.map f).toFinset = (L₂.map f).toFinset := by
  ext a; simp only [List.mem_toFinset, List.mem_map, mem_iff_of_mask h]

/-! ## The automaton tables -/

section DFA
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)] (dL dT : Bool)
variable (stT nxT : List (List ℕ)) (D : ℕ) (outTab : List (List (List ℕ)))

variable (w m) in
def SD (d : ℕ) : Finset (Cfg w m) := ((stT.getD d []).map (fun c => (decC c : Cfg w m))).toFinset

def nextD (d b : ℕ) : ℕ := (nxT.getD d []).getD b 0

variable (w m) in
def initC : List ℕ :=
  ((List.range (KO w m)).filter (fun q => q == 0 ||
    decide (okSt dT (upd (fun _ => 1) (dec (q - 1) : Ltr w m))))).map
    (fun q => mkC w m q 0 (encS (fun _ : Fin w => (1 : Fin 3))))

variable (w m) in
def rowOK (d : ℕ) : Bool :=
  (List.range ((m + 1) ^ w)).all (fun b =>
    decide (nextD nxT d b < D) &&
    maskOf ((stT.getD d []).flatMap (fun c => succC w m dL dT outTab c b)) ==
      maskOf (stT.getD (nextD nxT d b) []))

variable (w m) in
def outRowOK (l : ℕ) : Bool :=
  (List.range ((m + 1) ^ w)).all (fun x => (List.range (KO w m)).all (fun q =>
    outL outTab l x q == enc (out nbL (decO l) (dec x : Ltr w m) (decO q))))

variable (w m) in
def checkT : Bool :=
  (List.range (KO w m)).all (fun l => outRowOK w m nbL outTab l) &&
  maskOf (initC w m dT) == maskOf (stT.getD 0 []) && decide (0 < D) &&
  (List.range D).all (fun d => rowOK w m dL dT stT nxT D outTab d)

variable (w m) in
def rowsOK (lo len : ℕ) : Bool :=
  (List.range' lo len).all (fun d => rowOK w m dL dT stT nxT D outTab d)

variable {nbL dL dT stT nxT D outTab} in
theorem rowsOK_spec {lo len : ℕ} (h : rowsOK w m dL dT stT nxT D outTab lo len = true) (d : ℕ)
    (h1 : lo ≤ d) (h2 : d < lo + len) : rowOK w m dL dT stT nxT D outTab d = true := by
  simp only [rowsOK, List.all_eq_true, List.mem_range'] at h
  exact h d ⟨d - lo, by omega, by omega⟩

theorem all_range'_spec {p : ℕ → Bool} {lo len : ℕ} (h : (List.range' lo len).all p = true)
    (d : ℕ) (h1 : lo ≤ d) (h2 : d < lo + len) : p d = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h d ⟨d - lo, by omega, by omega⟩

variable {nbL dL dT stT nxT D outTab} in
theorem checkT_of
    (hO : ∀ l < KO w m, outRowOK w m nbL outTab l = true)
    (h0 : (maskOf (initC w m dT) == maskOf (stT.getD 0 []) && decide (0 < D)) = true)
    (hr : ∀ d < D, rowOK w m dL dT stT nxT D outTab d = true) :
    checkT w m nbL dL dT stT nxT D outTab = true := by
  have hO' : (List.range (KO w m)).all (fun l => outRowOK w m nbL outTab l) = true := by
    simp only [List.all_eq_true, List.mem_range]; exact hO
  simp only [checkT, hO', h0, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hr

variable (w m) in
def run : {n : ℕ} → (Fin n → Ltr w m) → ℕ
  | 0, _ => 0
  | n + 1, B => nextD nxT (run (Fin.init B)) (enc (B (Fin.last n)))

theorem run_snoc {n : ℕ} (B : Fin n → Ltr w m) (x : Ltr w m) :
    run w m nxT (Fin.snoc B x : Fin (n + 1) → Ltr w m) = nextD nxT (run w m nxT B) (enc x) := by
  simp only [run, Fin.init_snoc, Fin.snoc_last]

variable {nbL dL dT stT nxT D outTab}

theorem checkT_spec (hT : checkT w m nbL dL dT stT nxT D outTab = true) :
    (∀ l < KO w m, ∀ x < (m + 1) ^ w, ∀ q < KO w m,
      outL outTab l x q = enc (out nbL (decO l) (dec x : Ltr w m) (decO q))) ∧
    maskOf (initC w m dT) = maskOf (stT.getD 0 []) ∧ 0 < D ∧
    ∀ d < D, ∀ b < (m + 1) ^ w, nextD nxT d b < D ∧
      maskOf ((stT.getD d []).flatMap (fun c => succC w m dL dT outTab c b)) =
        maskOf (stT.getD (nextD nxT d b) []) := by
  simp only [checkT, rowOK, outRowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hT
  obtain ⟨⟨⟨hO, h1⟩, h2⟩, h3⟩ := hT
  exact ⟨hO, h1, h2, fun d hd b hb => h3 d hd b hb⟩

open Classical in
theorem real_run (hT : checkT w m nbL dL dT stT nxT D outTab = true) :
    ∀ {n : ℕ} (B : Fin n → Ltr w m),
      run w m nxT B < D ∧ univ.filter (Rz nbL dL dT B) = SD w m stT (run w m nxT B)
  | 0, B => by
    obtain ⟨_, h1, h2, _⟩ := checkT_spec hT
    refine ⟨h2, ?_⟩
    simp only [run, SD]
    rw [← toFinset_map_of_mask _ h1]
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rz_zero, List.mem_toFinset,
      List.mem_map, initC, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    obtain ⟨q, l, st⟩ := c
    constructor
    · rintro ⟨rfl, rfl, hg⟩
      refine ⟨mkC w m (encO q) 0 (encS (fun _ : Fin w => (1 : Fin 3))),
        ⟨encO q, ⟨encO_lt q, ?_⟩, rfl⟩, ?_⟩
      · cases q with
        | none => left; rfl
        | some y =>
          right
          simp only [encO, Nat.add_sub_cancel, dec_enc]
          exact hg y rfl
      · rw [decC_mkC _ _ _ (encO_lt q) (by positivity), decO_encO, decS_encS]; rfl
    · rintro ⟨c₂, ⟨q₂, ⟨hq, hg⟩, rfl⟩, he⟩
      rw [decC_mkC _ _ _ hq (by positivity), decS_encS] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨by simp [decO], rfl, fun y hy => ?_⟩
      rcases hg with hg | hg
      · subst hg; simp [decO] at hy
      · have hq0 : q₂ ≠ 0 := by rintro rfl; simp [decO] at hy
        simp only [decO, hq0, ↓reduceIte, Option.some.injEq] at hy
        rw [← hy]; exact hg
  | n + 1, B => by
    obtain ⟨hOut, _, _, h3⟩ := checkT_spec hT
    obtain ⟨ih1, ih2⟩ := real_run hT (Fin.init B)
    have hB : B = Fin.snoc (Fin.init B) (B (Fin.last n)) := (Fin.snoc_init_self B).symm
    have hb := enc_lt (B (Fin.last n))
    obtain ⟨g1, g2⟩ := h3 _ ih1 _ hb
    have hrun : run w m nxT B = nextD nxT (run w m nxT (Fin.init B)) (enc (B (Fin.last n))) := rfl
    refine ⟨by rw [hrun]; exact g1, ?_⟩
    rw [hrun, SD, ← toFinset_map_of_mask _ g2, ← δ_code nbL dL dT hOut _ _ hb, dec_enc, ← SD, ← ih2]
    ext c'
    conv_lhs => rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rz_snoc, δ]


variable (w m stT) in
def accB (d : ℕ) : Bool := (stT.getD d []).any (fun c => c % KO w m == 0)

variable (w m nxT) in
/-- Number of output words of length `n` whose run ends in state `d`. -/
def NC (n d : ℕ) : ℕ := (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card

variable (w m nbL dL dT) in
/-- Number of distinct neighbourhood-minimum words of sorted words of length `n`. -/
def AC (n : ℕ) : ℕ := ((univ.filter (fun W : Fin n → Ltr w m => sortedW dL dT W)).image
  (Fmin nbL)).card

open Classical in
theorem AC_eq (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D outTab = true) (n : ℕ) :
    AC w m nbL dL dT n = ∑ d ∈ range D, if accB w m stT d then NC w m nxT n d else 0 := by
  have himg : (univ.filter (fun W : Fin n → Ltr w m => sortedW dL dT W)).image (Fmin nbL) =
      univ.filter (fun B : Fin n → Ltr w m => accB w m stT (run w m nxT B) = true) := by
    ext B
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [image_iff nbL dL dT hnb B]
    obtain ⟨_, h2⟩ := real_run hT B
    constructor
    · rintro ⟨c, hc, hc1⟩
      have : c ∈ univ.filter (Rz nbL dL dT B) := by simp [hc]
      rw [h2, SD] at this
      simp only [List.mem_toFinset, List.mem_map] at this
      obtain ⟨c₀, hc₀, rfl⟩ := this
      simp only [accB, List.any_eq_true, beq_iff_eq]
      refine ⟨c₀, hc₀, ?_⟩
      simp only [decC] at hc1
      exact decO_ne_none.1 hc1
    · intro h
      simp only [accB, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨c₀, hc₀, h0⟩ := h
      have : (decC c₀ : Cfg w m) ∈ univ.filter (Rz nbL dL dT B) := by
        rw [h2, SD]; simp only [List.mem_toFinset, List.mem_map]; exact ⟨c₀, hc₀, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact ⟨_, this, by simp [decC, h0, decO]⟩
  unfold AC
  rw [himg, Finset.card_eq_sum_card_fiberwise (f := fun B => run w m nxT B) (t := range D)]
  · apply Finset.sum_congr rfl
    intro d _
    unfold NC
    split
    · congr 1; ext B
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; assumption, h⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro B hB h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      rw [h] at hB; simp_all
  · intro B _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (real_run hT B).1

theorem sum_enc (g : ℕ → ℕ) :
    ∑ x : Ltr w m, g (enc x) = ∑ b ∈ range ((m + 1) ^ w), g b := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [enc_eq]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun _ => rfl)

theorem NC_zero (d : ℕ) : NC w m nxT 0 d = if d = 0 then 1 else 0 := by
  unfold NC
  split
  · rename_i h; subst h
    rw [Finset.filter_true_of_mem]
    · simp
    · intro B _; rfl
  · rename_i h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _; exact fun h' => h h'.symm

theorem NC_succ (hT : checkT w m nbL dL dT stT nxT D outTab = true) (n d' : ℕ) :
    NC w m nxT (n + 1) d' = ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
      if nextD nxT d b = d' then NC w m nxT n d else 0 := by
  unfold NC
  rw [Finset.card_filter, ← (Fin.snocEquiv (fun _ => Ltr w m)).sum_comp, Fintype.sum_prod_type]
  have hs : ∀ x (y : Fin n → Ltr w m),
      (Fin.snocEquiv (fun _ => Ltr w m)) (x, y) = Fin.snoc y x := fun _ _ => rfl
  simp only [hs, run_snoc]
  have key : ∀ b, ∑ y : Fin n → Ltr w m, (if nextD nxT (run w m nxT y) b = d' then 1 else 0) =
      ∑ d ∈ range D, if nextD nxT d b = d' then
        (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card else 0 := by
    intro b
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range D)
      (g := fun y => run w m nxT y) (fun y _ => by simpa using (real_run hT y).1)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_congr rfl (g := fun _ => if nextD nxT d b = d' then 1 else 0)
      (fun y hy => by simp only [Finset.mem_filter] at hy; rw [hy.2])]
    rw [Finset.sum_const, smul_eq_mul]
    split <;> simp
  rw [Finset.sum_congr rfl (fun x _ => key (enc x)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact sum_enc (fun b => if nextD nxT d b = d' then
    (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card else 0)


/-! ## Count vectors and the annihilation certificate -/


theorem sum_zip_getD {α : Type*} (f : α → ℕ → ℕ) (da : α) :
    ∀ (l1 : List α) (l2 : List ℕ), l1.length = l2.length →
      ((l1.zip l2).map (fun p => f p.1 p.2)).sum =
        ∑ i ∈ range l1.length, f (l1.getD i da) (l2.getD i 0)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, sum_zip_getD f da l1 l2 h,
      List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem count_eq_sum (row : List ℕ) (x : ℕ) :
    row.count x = ∑ b ∈ range row.length, if row.getD b 0 = x then 1 else 0 := by
  induction row with
  | nil => simp
  | cons a row ih =>
    rw [List.count_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, beq_iff_eq]

variable (w m nxT D) in
def stepV (v : List ℕ) : List ℕ :=
  (List.range D).map (fun d' => ((nxT.zip v).map (fun p => p.1.count d' * p.2)).sum)

variable (w m nxT D) in
def stepOK (vecT : List (List ℕ)) (k : ℕ) : Bool :=
  vecT.getD (k + 1) [] == stepV nxT D (vecT.getD k [])

variable (w m nxT D) in
def checkLen (vecT : List (List ℕ)) : Bool :=
  decide (nxT.length = D) && nxT.all (fun r => r.length == (m + 1) ^ w) &&
    vecT.all (fun v => v.length == D)

variable (w m nxT D) in
def checkV (vecT : List (List ℕ)) : Bool :=
  checkLen w m nxT D vecT &&
  vecT.getD 0 [] == (List.range D).map (fun d => if d = 0 then 1 else 0) &&
  (List.range (vecT.length - 1)).all (fun k => stepOK nxT D vecT k)

theorem checkV_of (vecT : List (List ℕ)) (hl : checkLen w m nxT D vecT = true)
    (h0 : (vecT.getD 0 [] == (List.range D).map (fun d => if d = 0 then 1 else 0)) = true)
    (hs : ∀ k < vecT.length - 1, stepOK nxT D vecT k = true) :
    checkV w m nxT D vecT = true := by
  simp only [checkV, hl, h0, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hs

theorem getD_map_range (f : ℕ → ℕ) (D d : ℕ) (hd : d < D) :
    ((List.range D).map f).getD d 0 = f d := by
  rw [List.getD_eq_getElem _ _ (by simpa using hd)]
  simp

theorem stepV_getD (hn : nxT.length = D) (hr : ∀ r ∈ nxT, r.length = (m + 1) ^ w)
    (v : List ℕ) (hv : v.length = D) (d' : ℕ) (hd' : d' < D) :
    (stepV nxT D v).getD d' 0 = ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
      if nextD nxT d b = d' then v.getD d 0 else 0 := by
  rw [stepV, getD_map_range _ _ _ hd',
    sum_zip_getD (fun r x => r.count d' * x) [] nxT v (by rw [hn, hv]), hn]
  apply Finset.sum_congr rfl; intro d hd
  simp only [Finset.mem_range] at hd
  have hrow : (nxT.getD d []).length = (m + 1) ^ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hr _ (List.getElem_mem _)
  rw [count_eq_sum, hrow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  simp only [nextD]
  by_cases h : (nxT.getD d []).getD b 0 = d' <;> simp only [h, ↓reduceIte, one_mul, zero_mul]

theorem vec_spec (hT : checkT w m nbL dL dT stT nxT D outTab = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) :
    ∀ k < vecT.length, ∀ d < D, (vecT.getD k []).getD d 0 = NC w m nxT k d := by
  simp only [checkV, checkLen, stepOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hV
  obtain ⟨⟨⟨⟨hn, hr⟩, hvl⟩, h0⟩, hs⟩ := hV
  intro k
  induction k with
  | zero =>
    intro _ d hd
    rw [h0, getD_map_range _ _ _ hd, NC_zero]
  | succ k ih =>
    intro hk d' hd'
    have hvk : (vecT.getD k []).length = D := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hvl _ (List.getElem_mem _)
    rw [hs k (by omega), stepV_getD hn hr _ hvk d' hd', NC_succ hT]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (by omega) d (by simpa using hd)]

variable (stT) in
def liveB (d : ℕ) : Bool := !(stT.getD d []).isEmpty

variable (w m stT nxT D) in
def checkLive : Bool :=
  (List.range D).all (fun d => (List.range ((m + 1) ^ w)).all (fun b =>
    liveB stT d || !liveB stT (nextD nxT d b)))

variable (w m nxT) in
/-- `e`-th difference of the state counts. -/
def UC (e n d : ℕ) : ℤ :=
  ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ)

theorem UC_succ (hT : checkT w m nbL dL dT stT nxT D outTab = true) (e n d' : ℕ) :
    UC w m nxT e (n + 1) d' = ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
      if nextD nxT d b = d' then UC w m nxT e n d else 0 := by
  unfold UC
  have : ∀ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + 1 + e - i) d' : ℤ) =
      ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w), if nextD nxT d b = d' then
        (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ) else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : n + 1 + e - i = (n + e - i) + 1 := by omega
    rw [e1, NC_succ hT]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    split <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  split <;> simp

theorem UC_zero (hT : checkT w m nbL dL dT stT nxT D outTab = true)
    (hL : checkLive w m stT nxT D = true) (e n₁ : ℕ)
    (h₁ : ∀ d < D, liveB stT d = true → UC w m nxT e n₁ d = 0) :
    ∀ n, n₁ ≤ n → ∀ d < D, liveB stT d = true → UC w m nxT e n d = 0 := by
  simp only [checkLive, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hL
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h₁
  | succ n _ ih =>
    intro d' _ hd'
    rw [UC_succ hT]
    apply Finset.sum_eq_zero; intro d hd
    apply Finset.sum_eq_zero; intro b hb
    simp only [Finset.mem_range] at hd hb
    split
    · rename_i hn
      rcases hL d hd b hb with h | h
      · exact ih d hd h
      · rw [hn] at h; simp [h] at hd'
    · rfl

theorem AC_rec (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D outTab = true)
    (hL : checkLive w m stT nxT D = true) (e n₁ : ℕ)
    (h₁ : ∀ d < D, liveB stT d = true → UC w m nxT e n₁ d = 0) (n : ℕ) (hn : n₁ ≤ n) :
    ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) = 0 := by
  have : ∀ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) =
      ∑ d ∈ range D, if accB w m stT d then
        (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ) else 0 := by
    intro i _
    rw [AC_eq hnb hT]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    split <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_eq_zero; intro d hd
  simp only [Finset.mem_range] at hd
  split
  · rename_i ha
    have hl : liveB stT d = true := by
      simp only [accB, List.any_eq_true] at ha
      obtain ⟨c, hc, _⟩ := ha
      simp only [liveB, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      rintro h; rw [h] at hc; simp at hc
    have := UC_zero hT hL e n₁ h₁ n hn d hd hl
    unfold UC at this
    exact this
  · simp


variable (w m stT D) in
def valsOf (vecT : List (List ℕ)) (k : ℕ) : ℕ :=
  ∑ d ∈ range D, if accB w m stT d then (vecT.getD k []).getD d 0 else 0

theorem AC_vals (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D outTab = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) (k : ℕ) (hk : k < vecT.length) :
    AC w m nbL dL dT k = valsOf w m stT D vecT k := by
  rw [AC_eq hnb hT, valsOf]
  apply Finset.sum_congr rfl; intro d hd
  rw [vec_spec hT vecT hV k hk d (by simpa using hd)]

variable (stT D) in
def checkU (vecT : List (List ℕ)) (e n₁ : ℕ) : Bool :=
  decide (n₁ + e < vecT.length) &&
  (List.range D).all (fun d => !liveB stT d || decide ((∑ i ∈ range (e + 1),
    (-1) ^ i * (e.choose i : ℤ) * ((vecT.getD (n₁ + e - i) []).getD d 0 : ℤ)) = 0))

theorem rec_tables (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D outTab = true)
    (hL : checkLive w m stT nxT D = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) (e n₁ : ℕ) (hU : checkU stT D vecT e n₁ = true)
    (n : ℕ) (hn : n₁ ≤ n) :
    ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) = 0 := by
  simp only [checkU, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hU
  obtain ⟨hlen, hU⟩ := hU
  refine AC_rec hnb hT hL e n₁ (fun d hd hl => ?_) n hn
  rcases hU d hd with h | h
  · rw [h] at hl; cases hl
  · rw [← h]; unfold UC
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    rw [vec_spec hT vecT hV _ (by omega) d hd]

end DFA

/-! ## Generating functions -/

section GF
open PowerSeries

theorem coeff_mk_mul_one_sub_X_pow (c : ℕ → ℚ) (e k : ℕ) :
    coeff k (mk c * (1 - X) ^ e) = ∑ i ∈ range (e + 1),
      if i ≤ k then (-1) ^ i * (e.choose i : ℚ) * c (k - i) else 0 := by
  have h1 : (1 - X : PowerSeries ℚ) ^ e = ∑ i ∈ range (e + 1), C ((-1) ^ i * (e.choose i : ℚ)) * X ^ i := by
    rw [show (1 - X : PowerSeries ℚ) = -X + 1 by ring, add_pow]
    apply Finset.sum_congr rfl; intro i _
    simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
    rw [neg_pow]; ring
  rw [h1, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (C _), ← mul_assoc, coeff_mul_C, coeff_mul_X_pow', coeff_mk]
  split <;> ring

theorem coeff_poly (P : List ℚ) (k : ℕ) :
    coeff k (∑ j ∈ range P.length, C (P.getD j 0) * X ^ j) = P.getD k 0 := by
  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · rename_i h; simp only [Finset.mem_range, not_lt] at h
    rw [List.getD_eq_default _ _ h]

theorem gf_main (a : ℕ → ℕ) (e n₁ K₁ : ℕ) (P : List ℤ)
    (hrec : ∀ n, n₁ ≤ n → ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (a (n + e - i) : ℤ) = 0)
    (hK : n₁ + e ≤ K₁) (hK' : e + 1 ≤ K₁) (hP : P.length ≤ K₁)
    (hsmall : ∀ k < K₁, (∑ i ∈ range (e + 1), if i ≤ k then (-1) ^ i * (e.choose i : ℤ) *
      (if k - i = 0 then 0 else (a (k - i) : ℤ)) else 0) = P.getD k 0) :
    mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ e =
      ∑ j ∈ range P.length, C ((P.getD j 0 : ℤ) : ℚ) * X ^ j := by
  have hP' : ∀ j, (((P.map (Int.cast : ℤ → ℚ)).getD j 0) : ℚ) = ((P.getD j 0 : ℤ) : ℚ) := by
    intro j
    by_cases hj : j < P.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]; simp
    · simp only [not_lt] at hj
      rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ hj]; simp
  have e1 : ∑ j ∈ range P.length, C ((P.getD j 0 : ℤ) : ℚ) * X ^ j =
      ∑ j ∈ range (P.map (Int.cast : ℤ → ℚ)).length,
        C ((P.map (Int.cast : ℤ → ℚ)).getD j 0) * X ^ j := by
    rw [List.length_map]; apply Finset.sum_congr rfl; intro j _; rw [hP']
  rw [e1]
  ext k
  rw [coeff_mk_mul_one_sub_X_pow, coeff_poly, hP']
  by_cases hk : k < K₁
  · rw [← hsmall k hk]; push_cast
    apply Finset.sum_congr rfl; intro i _
    by_cases h1 : i ≤ k
    · by_cases h2 : k - i = 0
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  · simp only [not_lt] at hk
    rw [List.getD_eq_default _ _ (by omega)]
    have := hrec (k - e) (by omega)
    have e2 : k - e + e = k := by omega
    rw [e2] at this
    have e3 : ((0 : ℤ) : ℚ) = ((∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) *
        (a (k - i) : ℤ) : ℤ) : ℚ) := by rw [this]
    rw [e3]; push_cast
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_pos (by omega), if_neg (by omega)]

end GF

/-! ## Arrays read column by column -/

section Transpose
variable (nb : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nb a b c d)]

def nbT (t s t' s' : ℕ) : Prop := nb s t s' t'

instance (t s t' s' : ℕ) : Decidable (nbT nb t s t' s') := by unfold nbT; infer_instance

def sortedT (dL : Bool) {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ ordB dL (fun j => List.ofFn (fun i => A i j))

instance (dL : Bool) {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Decidable (sortedT dL A) := by
  unfold sortedT ordB; split <;> infer_instance

def minT {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Fin w → Fin n → Fin (m + 1) := fun i j =>
  ((univ : Finset (Fin w × Fin n)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

variable (w m) in
def ACT (dL : Bool) (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin w → Fin n → Fin (m + 1) => sortedT dL A)).image (minT nb)).card

def tau {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Fin n → Ltr w m := fun t s => A s t

theorem tau_inj {n : ℕ} : Function.Injective (tau (w := w) (m := m) (n := n)) := by
  intro A B h; funext s t; exact congrFun (congrFun h t) s

theorem Fmin_tau {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) :
    Fmin (nbT nb) (tau A) = tau (minT nb A) := by
  funext t s
  simp only [Fmin, tau, minT, nbT]
  apply le_antisymm
  · apply Finset.le_inf; rintro ⟨i, j⟩ hp
    exact Finset.inf_le (b := (j, i)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩)
  · apply Finset.le_inf; rintro ⟨j, i⟩ hp
    exact Finset.inf_le (b := (i, j)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩)

theorem ACT_eq (dL : Bool) (n : ℕ) : ACT w m nb dL n = AC w m (nbT nb) dL true n := by
  unfold ACT AC
  rw [← Finset.card_image_of_injective _ tau_inj, Finset.image_image]
  have h1 : (tau ∘ minT nb : (Fin w → Fin n → Fin (m + 1)) → Fin n → Ltr w m) =
      Fmin (nbT nb) ∘ tau := by funext A; exact (Fmin_tau nb A).symm
  rw [h1, ← Finset.image_image]
  congr 2
  ext W
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s t => W t s, ⟨h2, h1⟩, rfl⟩

end Transpose

end MinNbLib


namespace OMA.P_oeis_a219817

open OMA.S_oeis_a219817 MinNbLib Finset PowerSeries

theorem a_eq (n : ℕ) : a n = AC 3 2 (nbT nb) false true n := by
  rw [← ACT_eq]
  unfold a ACT IsSorted minNb sortedT minT
  rfl

theorem hnb : ∀ t s t' s', (nbT nb) t s t' s' ↔ (t' + 1 = t ∧ (nbT nb) 1 s 0 s') ∨
    (t' = t ∧ (nbT nb) 1 s 1 s') ∨ (t' = t + 1 ∧ (nbT nb) 1 s 2 s') := by
  intro t s t' s'
  unfold nbT nb
  have e1 : ∀ x : ℕ, (x = x + 1 + 1) = False := fun x => by simp; omega
  have e2 : ∀ x : ℕ, (x + 1 + 1 = x) = False := fun x => by simp; omega
  rcases (by omega : t' + 1 = t ∨ t' = t ∨ t' = t + 1 ∨ (t' ≠ t ∧ t' + 1 ≠ t ∧ t' ≠ t + 1)) with
    h | h | h | ⟨h1, h2, h3⟩
  · subst h; simp [e1, e2]; try tauto
  · subst h; simp [e1, e2]; try tauto
  · subst h; simp [e1, e2]; try tauto
  · simp [h1, h2, h3]

/-- Configuration codes of the automaton states. -/
def stT : List (List ℕ) := [[10192, 10193, 10202, 10205, 10206, 10211, 10214, 10215, 10217, 10218, 10219], [7673, 7676, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 8485, 8488, 8491, 9773, 10109, 10137, 10138, 10220, 10221, 10585, 10949], [8489], [], [7672, 7682, 7685, 7691, 7694, 8494, 8503, 9772, 9782, 9785, 9791, 10118, 10121, 10146, 10147, 10594, 10603, 10958], [8497, 8500, 8506, 8509, 10149, 10597, 10606, 10609, 10961], [8484, 8498, 8507, 10150, 10584, 10598, 10962], [10108, 10127, 10130, 10133, 10155, 10156, 10967], [10158, 10161, 10970], [10136, 10159, 10162, 10971], [10973], [10974], [10948, 10975], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 10220, 10221], [7981, 7984, 7987, 7990, 7993, 7996, 7999, 8002, 8005], [7980, 7985], [7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7421, 7424, 7588, 7589, 7598, 7607, 7673, 7676, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 9773], [7420, 7430, 7433, 7439, 7672, 7682, 7685, 7691, 7694, 9772, 9782, 9785, 9791], [7421, 7424, 7505, 7508, 7511, 7673, 7676, 7757, 7760, 7763, 9773, 10109], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7756, 7766, 7769, 7772, 7775, 7778, 7781, 9772, 9782, 9785, 9791, 10108, 10118, 10121, 10127, 10130, 10133], [8233, 8236, 8239, 8485, 8488, 8491, 9801, 9802, 10585], [8237, 8489], [8242, 8251, 8494, 8503, 9810, 9811, 9819, 9820, 10594, 10603], [8245, 8248, 8254, 8257, 8497, 8500, 8506, 8509, 9813, 9822, 9825, 10597, 10606, 10609], [8232, 8246, 8484, 8498, 8507, 9800, 9814, 10584, 10598], [7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641, 7673, 7676, 8372, 8373, 8382, 8391, 10109], [7672, 7682, 7685, 7691, 7694, 10118, 10121], [10108, 10127, 10130, 10133], [7673, 7676, 10109], [7701, 7702, 7704, 7707, 8485, 8488, 8491, 10137, 10138], [7705, 8489], [7710, 7711, 7719, 7720, 8494, 8503, 10146, 10147], [7713, 7716, 7722, 7725, 8497, 8500, 8506, 8509, 10149], [7700, 7714, 7723, 8484, 8498, 8507, 10150], [10155, 10156], [10158, 10161], [10136, 10159, 10162], [10109], [10118, 10121], [10137, 10138], [10146, 10147], [10149], [10150], [10949], [10958], [10961], [10962], [10967], [10970], [10971], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133, 10220, 10221], [7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 9436, 9437], [7336, 7337, 7346, 7421, 7424, 7588, 7589, 7598, 7607, 7673, 7676, 9773], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 9436, 9437], [7336, 7337, 7346, 7421, 7424, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7673, 7676, 7757, 7760, 7763, 9773, 10109], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7766, 7769, 7772, 9772, 9782, 9785, 9791, 10118, 10121], [7756, 7775, 7778, 7781, 10108, 10127, 10130, 10133], [7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7868, 7869, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 10220, 10221], [7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391, 9436, 9437], [7588, 7589, 7598, 7607, 7673, 7676, 10109], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 9436, 9437], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7868, 7869, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489], [7197, 7198, 7200, 7203, 7206, 7207, 7209, 7212, 7215, 7216, 7218, 7221, 7981, 7984, 7987, 7990, 7993, 7996, 7999, 8002, 8005], [7196, 7201, 7980, 7985], [7421, 7424, 7505, 7508, 7511, 7673, 7676, 7757, 7760, 7763, 9773], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7756, 7766, 7769, 7772, 7775, 7778, 7781, 9772, 9782, 9785, 9791], [7449, 7450, 7452, 7455, 7701, 7702, 7704, 7707, 8233, 8236, 8239, 8485, 8488, 8491, 9801, 9802], [7453, 7705, 8237, 8489], [7458, 7459, 7467, 7468, 7710, 7711, 7719, 7720, 8242, 8251, 8494, 8503, 9810, 9811, 9819, 9820], [7461, 7464, 7470, 7473, 7713, 7716, 7722, 7725, 8245, 8248, 8254, 8257, 8497, 8500, 8506, 8509, 9813, 9822, 9825], [7448, 7462, 7700, 7714, 7723, 8232, 8246, 8484, 8498, 8507, 9800, 9814], [7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641], [7701, 7702, 7704, 7707, 10137, 10138], [7705], [7710, 7711, 7719, 7720, 10146, 10147], [7713, 7716, 7722, 7725, 10149], [7700, 7714, 7723, 10150], [9436, 9437], [7336, 7337, 7346, 9773], [9772, 9782, 9785, 9791], [9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489], [7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389], [9773], [9801, 9802], [9810, 9811, 9819, 9820], [9813, 9822, 9825], [9800, 9814], [10220, 10221], [8120, 8121, 8130], [10585], [10594, 10603], [10597, 10606, 10609], [10584, 10598], [8372, 8373, 8382, 8391], [7673, 7676], [7672, 7682, 7685, 7691, 7694], [8485, 8488, 8491], [8494, 8503], [8497, 8500, 8506, 8509], [8484, 8498, 8507], [7420, 7430, 7433, 7439, 7672, 7682, 7685, 7691, 7694, 9772, 9782, 9785, 9791, 10118, 10121], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7757, 7760, 7763, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7766, 7769, 7772], [7756, 7775, 7778, 7781], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7336, 7337, 7346, 7588, 7589, 7598, 7607, 9436, 9437], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 9436, 9437], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7588, 7589, 7598, 7607, 9436, 9437], [7336, 7337, 7346, 7421, 7424, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7673, 7676, 9773], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 9772, 9782, 9785, 9791], [7588, 7589, 7598, 7607, 7673, 7676, 7757, 7760, 7763, 10109], [7672, 7682, 7685, 7691, 7694, 7766, 7769, 7772, 10118, 10121], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7868, 7869, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133, 10220, 10221], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 7868, 7869, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133], [7336, 7337, 7346, 7421, 7424, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7673, 7676, 7757, 7760, 7763, 9773], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7766, 7769, 7772, 9772, 9782, 9785, 9791], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489], [7197, 7198, 7200, 7203, 7206, 7207, 7209, 7212, 7215, 7216, 7218, 7221], [7196, 7201], [7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7588, 7589, 7598, 7607, 7616, 7617, 7618, 7620, 7623, 7626, 7627, 7629, 7632, 7635, 7636, 7638, 7641], [7449, 7450, 7452, 7455, 7701, 7702, 7704, 7707, 9801, 9802], [7453, 7705], [7458, 7459, 7467, 7468, 7710, 7711, 7719, 7720, 9810, 9811, 9819, 9820], [7461, 7464, 7470, 7473, 7713, 7716, 7722, 7725, 9813, 9822, 9825], [7448, 7462, 7700, 7714, 7723, 9800, 9814], [7084, 7085, 7336, 7337, 7346, 9436, 9437], [7336, 7337, 7346, 7588, 7589, 7598, 7607, 9773], [7336, 7337, 7346, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7364, 7365, 7366, 7368, 7371, 7374, 7375, 7377, 7380, 7383, 7386, 7389, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781], [7673, 7676, 9773, 10109], [7672, 7682, 7685, 7691, 7694, 9772, 9782, 9785, 9791, 10108, 10118, 10121, 10127, 10130, 10133], [7868, 7869, 8120, 8121, 8130], [8120, 8121, 8130, 8372, 8373, 8382, 8391], [7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7084, 7085, 7168, 7169, 7172, 7178, 7187], [7336, 7337, 7346, 7421, 7424, 7588, 7589, 7598, 7607, 7673, 7676], [7420, 7430, 7433, 7439, 7672, 7682, 7685, 7691, 7694], [7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7868, 7869], [7421, 7424, 7505, 7508, 7511, 7673, 7676, 7757, 7760, 7763], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694, 7756, 7766, 7769, 7772, 7775, 7778, 7781], [8233, 8236, 8239, 8485, 8488, 8491], [8242, 8251, 8494, 8503], [8245, 8248, 8254, 8257, 8497, 8500, 8506, 8509], [8232, 8246, 8484, 8498, 8507], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7868, 7869, 8120, 8121, 8130, 8372, 8373, 8382, 8391], [7336, 7337, 7346, 7421, 7424, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7673, 7676], [7420, 7430, 7433, 7439, 7504, 7514, 7517, 7520, 7523, 7526, 7672, 7682, 7685, 7691, 7694], [7588, 7589, 7598, 7607, 7673, 7676, 7757, 7760, 7763], [7672, 7682, 7685, 7691, 7694, 7766, 7769, 7772], [7084, 7085, 7112, 7113, 7114, 7116, 7119, 7122, 7125, 7128, 7131, 7134, 7137, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7504, 7505, 7508, 7511, 7514, 7517, 7520, 7523, 7526, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7756, 7757, 7760, 7763, 7766, 7769, 7772, 7775, 7778, 7781, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133], [7084, 7085, 7336, 7337, 7346, 7588, 7589, 7598, 7607, 9436, 9437], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7336, 7337, 7346, 7421, 7424, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 9436, 9437, 9464, 9465, 9466, 9474, 9477, 9483, 9486, 9489, 9772, 9773, 9782, 9785, 9791, 10108, 10109, 10118, 10121, 10127, 10130, 10133], [7336, 7337, 7346, 7421, 7424, 7588, 7589, 7598, 7607, 7673, 7676, 9773, 10109], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7336, 7337, 7346, 7588, 7589, 7598, 7607], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694, 7868, 7869], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274], [7336, 7337, 7346, 7421, 7424, 7505, 7508, 7511, 7588, 7589, 7598, 7607, 7673, 7676, 7757, 7760, 7763], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7588, 7589, 7598, 7607], [7084, 7085, 7168, 7169, 7172, 7178, 7187, 7252, 7253, 7256, 7259, 7262, 7265, 7271, 7274, 7336, 7337, 7346, 7420, 7421, 7424, 7430, 7433, 7439, 7588, 7589, 7598, 7607, 7672, 7673, 7676, 7682, 7685, 7691, 7694]]

/-- Transitions of the automaton, indexed by output letter code. -/
def nxT : List (List ℕ) := [[1, 2, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 5, 6, 3, 3, 3, 3, 7, 3, 3, 8, 9, 3, 10, 11, 12], [13, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [14, 15, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [16, 3, 3, 3, 3, 3, 3, 3, 3, 17, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [18, 3, 3, 3, 3, 3, 3, 3, 3, 19, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [20, 21, 3, 3, 3, 3, 3, 3, 3, 22, 3, 3, 23, 24, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [25, 3, 3, 3, 3, 3, 3, 3, 3, 26, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [28, 3, 3, 3, 3, 3, 3, 3, 3, 26, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [29, 30, 3, 3, 3, 3, 3, 3, 3, 31, 3, 3, 32, 33, 3, 3, 3, 3, 34, 3, 3, 35, 36, 3, 3, 3, 3], [37, 3, 3, 3, 3, 3, 3, 3, 3, 38, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [39, 3, 3, 3, 3, 3, 3, 3, 3, 40, 3, 3, 41, 42, 3, 3, 3, 3, 34, 3, 3, 35, 36, 3, 3, 3, 3], [43, 3, 3, 3, 3, 3, 3, 3, 3, 44, 3, 3, 45, 46, 3, 3, 3, 3, 47, 3, 3, 48, 49, 3, 10, 11, 12], [50, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [51, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [14, 15, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [52, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [53, 3, 3, 3, 3, 3, 3, 3, 3, 17, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [54, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [55, 3, 3, 3, 3, 3, 3, 3, 3, 56, 3, 3, 3, 3, 3, 3, 3, 3, 57, 3, 3, 3, 3, 3, 3, 3, 3], [58, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [14, 15, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [59, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [18, 3, 3, 3, 3, 3, 3, 3, 3, 19, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [20, 21, 3, 3, 3, 3, 3, 3, 3, 22, 3, 3, 23, 24, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [60, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [53, 3, 3, 3, 3, 3, 3, 3, 3, 17, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [61, 3, 3, 3, 3, 3, 3, 3, 3, 26, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [63, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [64, 65, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [59, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [66, 3, 3, 3, 3, 3, 3, 3, 3, 67, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [68, 69, 3, 3, 3, 3, 3, 3, 3, 70, 3, 3, 71, 72, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [73, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [28, 3, 3, 3, 3, 3, 3, 3, 3, 26, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [74, 75, 3, 3, 3, 3, 3, 3, 3, 76, 3, 3, 77, 78, 3, 3, 3, 3, 34, 3, 3, 35, 36, 3, 3, 3, 3], [79, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [80, 3, 3, 3, 3, 3, 3, 3, 3, 81, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [82, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [83, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [84, 3, 3, 3, 3, 3, 3, 3, 3, 81, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [85, 3, 3, 3, 3, 3, 3, 3, 3, 86, 3, 3, 87, 88, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [89, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [90, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [84, 3, 3, 3, 3, 3, 3, 3, 3, 81, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [91, 3, 3, 3, 3, 3, 3, 3, 3, 92, 3, 3, 93, 94, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [95, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [96, 3, 3, 3, 3, 3, 3, 3, 3, 97, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [98, 2, 3, 3, 3, 3, 3, 3, 3, 99, 3, 3, 100, 101, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [50, 3, 3, 3, 3, 3, 3, 3, 3, 102, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [103, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [52, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [106, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [107, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [108, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [109, 3, 3, 3, 3, 3, 3, 3, 3, 110, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [111, 3, 3, 3, 3, 3, 3, 3, 3, 112, 3, 3, 3, 3, 3, 3, 3, 3, 57, 3, 3, 3, 3, 3, 3, 3, 3], [113, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [114, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [60, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [106, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [106, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [115, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [114, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [64, 65, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [54, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [116, 3, 3, 3, 3, 3, 3, 3, 3, 117, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [63, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [64, 65, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [59, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [18, 3, 3, 3, 3, 3, 3, 3, 3, 19, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [68, 69, 3, 3, 3, 3, 3, 3, 3, 70, 3, 3, 71, 72, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [118, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [119, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [120, 121, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [122, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [66, 3, 3, 3, 3, 3, 3, 3, 3, 67, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [123, 124, 3, 3, 3, 3, 3, 3, 3, 125, 3, 3, 126, 127, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [79, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [128, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [129, 3, 3, 3, 3, 3, 3, 3, 3, 81, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [130, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [131, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [79, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [82, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [122, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [132, 3, 3, 3, 3, 3, 3, 3, 3, 133, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [85, 3, 3, 3, 3, 3, 3, 3, 3, 86, 3, 3, 87, 88, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [89, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [134, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [89, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [135, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [132, 3, 3, 3, 3, 3, 3, 3, 3, 133, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [91, 3, 3, 3, 3, 3, 3, 3, 3, 92, 3, 3, 93, 94, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [136, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [137, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [138, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [140, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [135, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [141, 3, 3, 3, 3, 3, 3, 3, 3, 142, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [143, 21, 3, 3, 3, 3, 3, 3, 3, 144, 3, 3, 145, 146, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [53, 3, 3, 3, 3, 3, 3, 3, 3, 17, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [147, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [148, 3, 3, 3, 3, 3, 3, 3, 3, 149, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [150, 3, 3, 3, 3, 3, 3, 3, 3, 151, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [106, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [107, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [107, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [108, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [109, 3, 3, 3, 3, 3, 3, 3, 3, 110, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [108, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [109, 3, 3, 3, 3, 3, 3, 3, 3, 110, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [113, 3, 3, 3, 3, 3, 3, 3, 3, 102, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [114, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [115, 3, 3, 3, 3, 3, 3, 3, 3, 56, 3, 3, 3, 3, 3, 3, 3, 3, 57, 3, 3, 3, 3, 3, 3, 3, 3], [108, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [109, 3, 3, 3, 3, 3, 3, 3, 3, 110, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [118, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [152, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [118, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [120, 121, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [118, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [119, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [120, 121, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [122, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [18, 3, 3, 3, 3, 3, 3, 3, 3, 19, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [123, 124, 3, 3, 3, 3, 3, 3, 3, 125, 3, 3, 126, 127, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [128, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [153, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [154, 3, 3, 3, 3, 3, 3, 3, 3, 102, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [131, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [155, 3, 3, 3, 3, 3, 3, 3, 3, 102, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [134, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [136, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [136, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [156, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [156, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [138, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [157, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [158, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [159, 3, 3, 3, 3, 3, 3, 3, 3, 104, 3, 3, 3, 3, 3, 3, 3, 3, 105, 3, 3, 3, 3, 3, 3, 3, 3], [140, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [135, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [141, 3, 3, 3, 3, 3, 3, 3, 3, 142, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [143, 21, 3, 3, 3, 3, 3, 3, 3, 144, 3, 3, 145, 146, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [147, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [160, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [148, 3, 3, 3, 3, 3, 3, 3, 3, 149, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [160, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [148, 3, 3, 3, 3, 3, 3, 3, 3, 149, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [152, 3, 3, 3, 3, 3, 3, 3, 3, 56, 3, 3, 3, 3, 3, 3, 3, 3, 57, 3, 3, 3, 3, 3, 3, 3, 3], [153, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [154, 3, 3, 3, 3, 3, 3, 3, 3, 102, 3, 3, 3, 3, 3, 3, 3, 3, 27, 3, 3, 3, 3, 3, 3, 3, 3], [106, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [156, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [157, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [161, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [160, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [161, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], [161, 3, 3, 3, 3, 3, 3, 3, 3, 139, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]]

/-- State count vectors for lengths 0 to 17. -/
def vecT : List (List ℕ) := [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 683, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 19564, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 2, 0, 3, 1, 1, 1, 1, 1, 1, 1, 0, 5, 6, 2, 0, 0, 0, 0, 0, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 531184, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 4, 4, 0, 8, 2, 2, 1, 2, 1, 1, 1, 0, 9, 11, 3, 0, 0, 0, 0, 0, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 1, 6, 2, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 14348394, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 7, 7, 0, 18, 4, 4, 1, 3, 1, 1, 1, 0, 15, 21, 4, 0, 0, 0, 0, 0, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 18, 4, 2, 3, 5, 1, 2, 1, 11, 5, 1, 3, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 7, 1, 9, 3, 1, 2, 3, 3, 3, 3, 6, 1, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 5, 2, 11, 17, 23, 4, 4, 4, 4, 2, 2, 2, 7, 2, 2, 2, 10, 5, 7, 7, 7, 5, 5, 5, 5, 5, 2, 6, 2, 2, 4, 4, 2, 4, 4, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 4, 4, 2, 3, 1, 2, 2, 1, 1, 1, 0, 0], [0, 0, 1, 387419504, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 11, 11, 0, 38, 7, 7, 1, 4, 1, 1, 1, 0, 26, 37, 5, 0, 0, 0, 0, 0, 6, 6, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 38, 7, 4, 8, 13, 1, 2, 1, 21, 8, 1, 4, 4, 4, 4, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 5, 10, 1, 12, 4, 1, 2, 4, 4, 4, 4, 10, 1, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 10, 4, 27, 47, 59, 12, 10, 11, 11, 5, 5, 3, 12, 3, 3, 3, 28, 9, 16, 16, 12, 9, 9, 9, 9, 9, 3, 9, 3, 3, 6, 6, 3, 6, 9, 1, 5, 13, 3, 3, 3, 3, 3, 3, 3, 3, 18, 18, 17, 17, 7, 9, 3, 4, 5, 3, 2, 2, 8, 1], [0, 0, 1, 10460351360, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 16, 16, 0, 74, 11, 11, 1, 5, 1, 1, 1, 0, 43, 60, 6, 0, 0, 0, 0, 0, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 74, 11, 7, 17, 30, 1, 2, 1, 37, 11, 1, 5, 5, 5, 5, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 13, 1, 15, 5, 1, 2, 5, 5, 5, 5, 15, 1, 5, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 16, 7, 55, 106, 130, 29, 23, 27, 27, 13, 13, 4, 18, 4, 4, 4, 61, 14, 30, 30, 18, 14, 14, 14, 14, 14, 4, 12, 4, 4, 8, 8, 4, 8, 16, 1, 14, 37, 4, 4, 4, 4, 4, 4, 4, 7, 62, 62, 47, 47, 16, 18, 6, 6, 11, 6, 3, 3, 37, 11], [0, 0, 1, 282429533110, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 22, 22, 0, 133, 16, 16, 1, 6, 1, 1, 1, 0, 67, 91, 7, 0, 0, 0, 0, 0, 8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 16, 1, 133, 16, 11, 31, 61, 1, 2, 1, 60, 14, 1, 6, 6, 6, 6, 1, 1, 1, 1, 1, 7, 7, 7, 7, 7, 7, 16, 1, 18, 6, 1, 2, 6, 6, 6, 6, 21, 1, 6, 6, 6, 6, 1, 1, 1, 1, 1, 1, 1, 23, 11, 100, 211, 258, 63, 51, 61, 61, 30, 30, 5, 25, 5, 5, 5, 115, 20, 50, 50, 25, 20, 20, 20, 20, 20, 5, 15, 5, 5, 10, 10, 5, 10, 25, 1, 38, 98, 5, 5, 5, 5, 5, 5, 5, 14, 164, 164, 106, 106, 30, 30, 10, 8, 26, 10, 4, 4, 112, 51], [0, 0, 1, 7625597478953, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 29, 29, 0, 223, 22, 22, 1, 7, 1, 1, 1, 0, 99, 131, 8, 0, 0, 0, 0, 0, 9, 9, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 22, 1, 223, 22, 16, 51, 112, 1, 2, 1, 91, 17, 1, 7, 7, 7, 7, 1, 1, 1, 1, 1, 8, 8, 8, 8, 8, 8, 19, 1, 21, 7, 1, 2, 7, 7, 7, 7, 28, 1, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 31, 16, 168, 385, 473, 130, 107, 127, 127, 61, 61, 6, 33, 6, 6, 6, 197, 27, 77, 77, 33, 27, 27, 27, 27, 27, 6, 18, 6, 6, 12, 12, 6, 12, 36, 1, 99, 248, 6, 6, 6, 6, 6, 6, 6, 25, 370, 370, 211, 211, 50, 45, 15, 10, 65, 15, 5, 5, 274, 167], [0, 0, 1, 205891132084062, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 37, 37, 0, 353, 29, 29, 1, 8, 1, 1, 1, 0, 140, 181, 9, 0, 0, 0, 0, 0, 10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 29, 1, 353, 29, 22, 78, 190, 1, 2, 1, 131, 20, 1, 8, 8, 8, 8, 1, 1, 1, 1, 1, 9, 9, 9, 9, 9, 9, 22, 1, 24, 8, 1, 2, 8, 8, 8, 8, 36, 1, 8, 8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 40, 22, 266, 658, 814, 259, 210, 245, 245, 112, 112, 7, 42, 7, 7, 7, 315, 35, 112, 112, 42, 35, 35, 35, 35, 35, 7, 21, 7, 7, 14, 14, 7, 14, 49, 1, 249, 602, 7, 7, 7, 7, 7, 7, 7, 41, 749, 749, 385, 385, 77, 63, 21, 12, 165, 21, 6, 6, 586, 446], [0, 0, 1, 5559060566537275, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 46, 46, 0, 533, 37, 37, 1, 9, 1, 1, 1, 0, 191, 242, 10, 0, 0, 0, 0, 0, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 37, 1, 533, 37, 29, 113, 303, 1, 2, 1, 181, 23, 1, 9, 9, 9, 9, 1, 1, 1, 1, 1, 10, 10, 10, 10, 10, 10, 25, 1, 27, 9, 1, 2, 9, 9, 9, 9, 45, 1, 9, 9, 9, 9, 1, 1, 1, 1, 1, 1, 1, 50, 29, 402, 1068, 1330, 498, 386, 442, 442, 190, 190, 8, 52, 8, 8, 8, 478, 44, 156, 156, 52, 44, 44, 44, 44, 44, 8, 24, 8, 8, 16, 16, 8, 16, 64, 1, 603, 1392, 8, 8, 8, 8, 8, 8, 8, 63, 1400, 1400, 658, 658, 112, 84, 28, 14, 415, 28, 7, 7, 1140, 1038], [0, 0, 1, 150094635296968157, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 56, 56, 0, 774, 46, 46, 1, 10, 1, 1, 1, 0, 253, 315, 11, 0, 0, 0, 0, 0, 12, 12, 12, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 46, 1, 774, 46, 37, 157, 460, 1, 2, 1, 242, 26, 1, 10, 10, 10, 10, 1, 1, 1, 1, 1, 11, 11, 11, 11, 11, 11, 28, 1, 30, 10, 1, 2, 10, 10, 10, 10, 55, 1, 10, 10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 61, 37, 585, 1662, 2081, 921, 669, 753, 753, 303, 303, 9, 63, 9, 9, 9, 696, 54, 210, 210, 63, 54, 54, 54, 54, 54, 9, 27, 9, 9, 18, 18, 9, 18, 81, 1, 1393, 3049, 9, 9, 9, 9, 9, 9, 9, 92, 2460, 2460, 1068, 1068, 156, 108, 36, 16, 1019, 36, 8, 8, 2065, 2185], [0, 0, 1, 4052555153018924460, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 67, 67, 0, 1088, 56, 56, 1, 11, 1, 1, 1, 0, 327, 401, 12, 0, 0, 0, 0, 0, 13, 13, 13, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 56, 1, 1088, 56, 46, 211, 671, 1, 2, 1, 315, 29, 1, 11, 11, 11, 11, 1, 1, 1, 1, 1, 12, 12, 12, 12, 12, 12, 31, 1, 33, 11, 1, 2, 11, 11, 11, 11, 66, 1, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 73, 46, 825, 2497, 3139, 1636, 1102, 1222, 1222, 460, 460, 10, 75, 10, 10, 10, 980, 65, 275, 275, 75, 65, 65, 65, 65, 65, 10, 30, 10, 10, 20, 20, 10, 20, 100, 1, 3050, 6321, 10, 10, 10, 10, 10, 10, 10, 129, 4113, 4113, 1662, 1662, 210, 135, 45, 18, 2413, 45, 9, 9, 3536, 4258], [0, 0, 1, 109418989131512273663, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 79, 79, 0, 1488, 67, 67, 1, 12, 1, 1, 1, 0, 414, 501, 13, 0, 0, 0, 0, 0, 14, 14, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 67, 1, 1488, 67, 56, 276, 947, 1, 2, 1, 401, 32, 1, 12, 12, 12, 12, 1, 1, 1, 1, 1, 13, 13, 13, 13, 13, 13, 34, 1, 36, 12, 1, 2, 12, 12, 12, 12, 78, 1, 12, 12, 12, 12, 1, 1, 1, 1, 1, 1, 1, 86, 56, 1133, 3641, 4589, 2794, 1738, 1903, 1903, 671, 671, 11, 88, 11, 11, 11, 1342, 77, 352, 352, 88, 77, 77, 77, 77, 77, 11, 33, 11, 11, 22, 22, 11, 22, 121, 1, 6322, 12436, 11, 11, 11, 11, 11, 11, 11, 175, 6600, 6600, 2497, 2497, 275, 165, 55, 20, 5464, 55, 10, 10, 5784, 7803], [0, 0, 1, 2954312706550833559192, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 92, 92, 0, 1988, 79, 79, 1, 13, 1, 1, 1, 0, 515, 616, 14, 0, 0, 0, 0, 0, 15, 15, 15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 79, 1, 1988, 79, 67, 353, 1300, 1, 2, 1, 501, 35, 1, 13, 13, 13, 13, 1, 1, 1, 1, 1, 14, 14, 14, 14, 14, 14, 37, 1, 39, 13, 1, 2, 13, 13, 13, 13, 91, 1, 13, 13, 13, 13, 1, 1, 1, 1, 1, 1, 1, 100, 67, 1521, 5174, 6530, 4599, 2641, 2861, 2861, 947, 947, 12, 102, 12, 12, 12, 1795, 90, 442, 442, 102, 90, 90, 90, 90, 90, 12, 36, 12, 12, 24, 24, 12, 24, 144, 1, 12437, 23320, 12, 12, 12, 12, 12, 12, 12, 231, 10230, 10230, 3641, 3641, 352, 198, 66, 22, 11787, 66, 11, 11, 9107, 13597], [0, 0, 1, 79766443076872509638965, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 106, 106, 0, 2603, 92, 92, 1, 14, 1, 1, 1, 0, 631, 747, 15, 0, 0, 0, 0, 0, 16, 16, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 92, 1, 2603, 92, 79, 443, 1743, 1, 2, 1, 616, 38, 1, 14, 14, 14, 14, 1, 1, 1, 1, 1, 15, 15, 15, 15, 15, 15, 40, 1, 42, 14, 1, 2, 14, 14, 14, 14, 105, 1, 14, 14, 14, 14, 1, 1, 1, 1, 1, 1, 1, 115, 79, 2002, 7189, 9076, 7319, 3887, 4173, 4173, 1300, 1300, 13, 117, 13, 13, 13, 2353, 104, 546, 546, 117, 104, 104, 104, 104, 104, 13, 39, 13, 13, 26, 26, 13, 26, 169, 1, 23321, 41881, 13, 13, 13, 13, 13, 13, 13, 298, 15392, 15392, 5174, 5174, 442, 234, 78, 24, 24225, 78, 12, 12, 13882, 22715], [0, 0, 1, 2153693963075557765954407, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 121, 121, 0, 3349, 106, 106, 1, 15, 1, 1, 1, 0, 763, 895, 16, 0, 0, 0, 0, 0, 17, 17, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 106, 1, 3349, 106, 92, 547, 2290, 1, 2, 1, 747, 41, 1, 15, 15, 15, 15, 1, 1, 1, 1, 1, 16, 16, 16, 16, 16, 16, 43, 1, 45, 15, 1, 2, 15, 15, 15, 15, 120, 1, 15, 15, 15, 15, 1, 1, 1, 1, 1, 1, 1, 131, 92, 2590, 9793, 12357, 11298, 5565, 5929, 5929, 1743, 1743, 14, 133, 14, 14, 14, 3031, 119, 665, 665, 133, 119, 119, 119, 119, 119, 14, 42, 14, 14, 28, 28, 14, 28, 196, 1, 41882, 72371, 14, 14, 14, 14, 14, 14, 14, 377, 22568, 22568, 7189, 7189, 546, 273, 91, 26, 47547, 91, 13, 13, 20578, 36609]]

/-- Output letter codes of all windows (left, own, right). -/
def outTab : List (List (List ℕ)) := [[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18], [22, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 18, 18, 18, 21, 22, 22, 21, 22, 22], [26, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 18, 18, 18, 21, 22, 22, 24, 25, 26]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [5, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 3, 4, 4, 3, 4, 5, 0, 0, 0, 3, 4, 4, 3, 4, 5], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [5, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 3, 4, 4, 3, 4, 5, 0, 0, 0, 3, 4, 4, 3, 4, 5]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [5, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 3, 4, 4, 3, 4, 5, 0, 0, 0, 3, 4, 4, 3, 4, 5], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 3, 4, 4, 3, 4, 4, 0, 0, 0, 3, 4, 4, 3, 4, 4], [8, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 3, 4, 4, 3, 4, 5, 0, 0, 0, 3, 4, 4, 6, 7, 8]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [17, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 15, 16, 17]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18], [22, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 18, 18, 18, 21, 22, 22, 21, 22, 22], [22, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 18, 18, 18, 21, 22, 22, 21, 22, 22]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [14, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 9, 9, 9, 12, 13, 13, 12, 13, 14], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [13, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 9, 9, 9, 12, 13, 13, 12, 13, 13], [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 18, 18, 18, 18, 18, 18, 18], [22, 0, 0, 0, 0, 1, 1, 0, 1, 1, 9, 9, 9, 12, 13, 13, 12, 13, 13, 18, 18, 18, 21, 22, 22, 21, 22, 22], [26, 0, 0, 0, 0, 1, 1, 0, 1, 2, 9, 9, 9, 12, 13, 13, 12, 13, 14, 18, 18, 18, 21, 22, 22, 24, 25, 26]]]

theorem hT0 : (maskOf (initC 3 2 true) == maskOf (stT.getD 0 []) && decide (0 < 162)) = true := by
  decide +kernel

theorem hO0 : (List.range' 0 7).all (outRowOK 3 2 (nbT nb) outTab) = true := by
  decide +kernel

theorem hO1 : (List.range' 7 7).all (outRowOK 3 2 (nbT nb) outTab) = true := by
  decide +kernel

theorem hO2 : (List.range' 14 7).all (outRowOK 3 2 (nbT nb) outTab) = true := by
  decide +kernel

theorem hO3 : (List.range' 21 7).all (outRowOK 3 2 (nbT nb) outTab) = true := by
  decide +kernel

theorem hR0 : rowsOK 3 2 false true stT nxT 162 outTab 0 52 = true := by decide +kernel

theorem hR1 : rowsOK 3 2 false true stT nxT 162 outTab 52 21 = true := by decide +kernel

theorem hR2 : rowsOK 3 2 false true stT nxT 162 outTab 73 42 = true := by decide +kernel

theorem hR3 : rowsOK 3 2 false true stT nxT 162 outTab 115 24 = true := by decide +kernel

theorem hR4 : rowsOK 3 2 false true stT nxT 162 outTab 139 23 = true := by decide +kernel

theorem hT : checkT 3 2 (nbT nb) false true stT nxT 162 outTab = true :=
  checkT_of (fun l hl =>
    if h0 : l < 7 then all_range'_spec hO0 l (by omega) h0 else
    if h1 : l < 14 then all_range'_spec hO1 l (by omega) h1 else
    if h2 : l < 21 then all_range'_spec hO2 l (by omega) h2 else
    all_range'_spec hO3 l (by omega) (Nat.lt_of_lt_of_le hl (by decide)))
  hT0 (fun d hd =>
    if h0 : d < 52 then rowsOK_spec hR0 d (by omega) h0 else
    if h1 : d < 73 then rowsOK_spec hR1 d (by omega) h1 else
    if h2 : d < 115 then rowsOK_spec hR2 d (by omega) h2 else
    if h3 : d < 139 then rowsOK_spec hR3 d (by omega) h3 else
    rowsOK_spec hR4 d (by omega) (by omega))

theorem hL : checkLive 3 2 stT nxT 162 = true := by decide +kernel

theorem hVL : checkLen 3 2 nxT 162 vecT = true := by decide +kernel

theorem hV0 : (vecT.getD 0 [] == (List.range 162).map (fun d => if d = 0 then 1 else 0)) = true := by
  decide +kernel

theorem hS0 : (List.range' 0 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS1 : (List.range' 2 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS2 : (List.range' 4 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS3 : (List.range' 6 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS4 : (List.range' 8 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS5 : (List.range' 10 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS6 : (List.range' 12 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS7 : (List.range' 14 2).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hS8 : (List.range' 16 1).all (stepOK nxT 162 vecT) = true := by
  decide +kernel

theorem hV : checkV 3 2 nxT 162 vecT = true :=
  checkV_of vecT hVL hV0 (fun d hd =>
    if h0 : d < 2 then all_range'_spec hS0 d (by omega) h0 else
    if h1 : d < 4 then all_range'_spec hS1 d (by omega) h1 else
    if h2 : d < 6 then all_range'_spec hS2 d (by omega) h2 else
    if h3 : d < 8 then all_range'_spec hS3 d (by omega) h3 else
    if h4 : d < 10 then all_range'_spec hS4 d (by omega) h4 else
    if h5 : d < 12 then all_range'_spec hS5 d (by omega) h5 else
    if h6 : d < 14 then all_range'_spec hS6 d (by omega) h6 else
    if h7 : d < 16 then all_range'_spec hS7 d (by omega) h7 else
    all_range'_spec hS8 d (by omega) (Nat.lt_of_lt_of_le hd (by decide +kernel)))

theorem hU : checkU stT 162 vecT 10 6 = true := by decide +kernel

theorem v0 : a 0 = 1 := by rw [a_eq, AC_vals hnb hT vecT hV 0 (by decide)]; decide +kernel
theorem v1 : a 1 = 6 := by rw [a_eq, AC_vals hnb hT vecT hV 1 (by decide)]; decide +kernel
theorem v2 : a 2 = 16 := by rw [a_eq, AC_vals hnb hT vecT hV 2 (by decide)]; decide +kernel
theorem v3 : a 3 = 62 := by rw [a_eq, AC_vals hnb hT vecT hV 3 (by decide)]; decide +kernel
theorem v4 : a 4 = 165 := by rw [a_eq, AC_vals hnb hT vecT hV 4 (by decide)]; decide +kernel
theorem v5 : a 5 = 377 := by rw [a_eq, AC_vals hnb hT vecT hV 5 (by decide)]; decide +kernel
theorem v6 : a 6 = 795 := by rw [a_eq, AC_vals hnb hT vecT hV 6 (by decide)]; decide +kernel
theorem v7 : a 7 = 1588 := by rw [a_eq, AC_vals hnb hT vecT hV 7 (by decide)]; decide +kernel
theorem v8 : a 8 = 3039 := by rw [a_eq, AC_vals hnb hT vecT hV 8 (by decide)]; decide +kernel
theorem v9 : a 9 = 5612 := by rw [a_eq, AC_vals hnb hT vecT hV 9 (by decide)]; decide +kernel
theorem v10 : a 10 = 10061 := by rw [a_eq, AC_vals hnb hT vecT hV 10 (by decide)]; decide +kernel
theorem v11 : a 11 = 17603 := by rw [a_eq, AC_vals hnb hT vecT hV 11 (by decide)]; decide +kernel
theorem v12 : a 12 = 30184 := by rw [a_eq, AC_vals hnb hT vecT hV 12 (by decide)]; decide +kernel
theorem v13 : a 13 = 50875 := by rw [a_eq, AC_vals hnb hT vecT hV 13 (by decide)]; decide +kernel
theorem v14 : a 14 = 84444 := by rw [a_eq, AC_vals hnb hT vecT hV 14 (by decide)]; decide +kernel
theorem v15 : a 15 = 138160 := by rw [a_eq, AC_vals hnb hT vecT hV 15 (by decide)]; decide +kernel
theorem v16 : a 16 = 222896 := by rw [a_eq, AC_vals hnb hT vecT hV 16 (by decide)]; decide +kernel
theorem v17 : a 17 = 354610 := by rw [a_eq, AC_vals hnb hT vecT hV 17 (by decide)]; decide +kernel

theorem hrec (n : ℕ) (hn : 6 ≤ n) :
    ∑ i ∈ range (10 + 1), (-1) ^ i * ((10 : ℕ).choose i : ℤ) * (a (n + 10 - i) : ℤ) = 0 := by
  have := rec_tables hnb hT hL vecT hV 10 6 hU n hn
  simpa only [a_eq] using this

theorem hsmall : ∀ k < 16, (∑ i ∈ range (10 + 1), if i ≤ k then (-1) ^ i * ((10 : ℕ).choose i : ℤ) *
    (if k - i = 0 then 0 else (a (k - i) : ℤ)) else 0) = ([0, 6, -44, 172, -455, 857, -1142, 1051, -640, 242, -48, -1, 4, -1] : List ℤ).getD k 0 := by
  intro k hk
  interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.choose, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
    X * (6 - 44 * X + 172 * X ^ 2 - 455 * X ^ 3 + 857 * X ^ 4 - 1142 * X ^ 5 + 1051 * X ^ 6 - 640 * X ^ 7 + 242 * X ^ 8 - 48 * X ^ 9 - X ^ 10 + 4 * X ^ 11 - X ^ 12) := by
  rw [gf_main a 10 6 16 [0, 6, -44, 172, -455, 857, -1142, 1051, -640, 242, -48, -1, 4, -1] hrec (by norm_num) (by norm_num) (by norm_num) hsmall]
  simp [Finset.sum_range_succ]
  ring

theorem rec (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  by_cases h : 16 ≤ n
  · have := hrec (n - 10) (by omega)
    have e0 : n - 10 + 10 = n := by omega
    simp only [e0] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num [Nat.choose] at this
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]

end OMA.P_oeis_a219817

theorem OMA.solution : type_of% @OMA.S_oeis_a219817.main :=
  ⟨OMA.P_oeis_a219817.gf, OMA.P_oeis_a219817.rec⟩
