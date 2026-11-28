import OMAStatements.S_oeis_a208640
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Tauto
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-! Exact finite-state enumeration of the binary arrays in A208640.
The array/word correspondence and raw-index transition implementation are proved universally.
All finite data are verified by ordinary Lean kernel reduction. -/

namespace A208640Proof

abbrev Col := Fin 5 → Fin 2
abbrev State := Option Col × Col

def leftCount (p : Option Col) (q : Col) (i : Fin 4) : ℕ :=
  match p with
  | none => 0
  | some p => if p i.succ = q i.succ then 1 else 0

def upperCount (q : Col) (i : Fin 4) : ℕ :=
  if q i.castSucc = q i.succ then 1 else 0

def rightCount (q : Col) (r : Option Col) (i : Fin 4) : ℕ :=
  match r with
  | none => 0
  | some r => if r i.castSucc = q i.succ then 1 else 0

def localOK (p : Option Col) (q : Col) (r : Option Col) : Prop :=
  ∀ i : Fin 4, leftCount p q i + upperCount q i + rightCount q r i ≤ 1

instance (p : Option Col) (q : Col) (r : Option Col) : Decidable (localOK p q r) :=
  inferInstanceAs (Decidable (∀ i : Fin 4,
    leftCount p q i + upperCount q i + rightCount q r i ≤ 1))

def step (s : State) (r : Col) : Option State :=
  if localOK s.1 s.2 (some r) then some (some s.2, r) else none

def accept (s : State) : Prop := localOK s.1 s.2 none

instance (s : State) : Decidable (accept s) :=
  inferInstanceAs (Decidable (localOK s.1 s.2 none))

def decode (c : Fin 32) (i : Fin 5) : Fin 2 :=
  ⟨c.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩

def allCols : List Col := List.ofFn decode

theorem decode_injective : Function.Injective decode := by
  decide +kernel

noncomputable def colEquiv : Fin 32 ≃ Col :=
  Equiv.ofBijective decode
    ((Fintype.bijective_iff_injective_and_card decode).mpr
      ⟨decode_injective, by simp [Col]⟩)

theorem sum_allCols (f : Col → ℕ) :
    (allCols.map f).sum = ∑ q : Col, f q := by
  rw [allCols, List.map_ofFn, List.sum_ofFn]
  exact colEquiv.sum_comp f

def initialStates : List State :=
  (allCols.filter fun q => q 0 = 0).map fun q => (none, q)

def successors (s : State) : List State := allCols.filterMap (step s)

end A208640Proof

namespace A208640Count

variable {S : Type*}

def paths (succ : S → List S) (accepted : S → ℕ) : ℕ → S → ℕ
  | 0, s => accepted s
  | n + 1, s => ((succ s).map (paths succ accepted n)).sum

lemma sum_balance (L : List S) (f₀ f₁ f₂ f₃ f₄ f₅ : S → ℕ)
    (h : ∀ s, f₅ s + 14 * f₃ s + 9 * f₁ s =
      6 * f₄ s + 16 * f₂ s + 2 * f₀ s) :
    (L.map f₅).sum + 14 * (L.map f₃).sum + 9 * (L.map f₁).sum =
      6 * (L.map f₄).sum + 16 * (L.map f₂).sum + 2 * (L.map f₀).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs := h s
    omega

theorem paths_recurrence (succ : S → List S) (accepted : S → ℕ)
    (hbase : ∀ s,
      paths succ accepted 7 s + 14 * paths succ accepted 5 s +
        9 * paths succ accepted 3 s =
      6 * paths succ accepted 6 s + 16 * paths succ accepted 4 s +
        2 * paths succ accepted 2 s) :
    ∀ n s, paths succ accepted (n + 7) s + 14 * paths succ accepted (n + 5) s +
        9 * paths succ accepted (n + 3) s =
      6 * paths succ accepted (n + 6) s + 16 * paths succ accepted (n + 4) s +
        2 * paths succ accepted (n + 2) s := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accepted (n + 7))).sum +
        14 * ((succ s).map (paths succ accepted (n + 5))).sum +
        9 * ((succ s).map (paths succ accepted (n + 3))).sum =
      6 * ((succ s).map (paths succ accepted (n + 6))).sum +
        16 * ((succ s).map (paths succ accepted (n + 4))).sum +
        2 * ((succ s).map (paths succ accepted (n + 2))).sum
    exact sum_balance (succ s) (paths succ accepted (n + 2))
      (paths succ accepted (n + 3)) (paths succ accepted (n + 4))
      (paths succ accepted (n + 5)) (paths succ accepted (n + 6))
      (paths succ accepted (n + 7)) ih

theorem paths_eq_vectors (succ : S → List S) (accepted : S → ℕ)
    (v : Fin 8 → S → ℕ) (hzero : ∀ s, v 0 s = accepted s)
    (hnext : ∀ k : Fin 7, ∀ s,
      ((succ s).map (v k.castSucc)).sum = v k.succ s) :
    ∀ k : Fin 8, ∀ s, paths succ accepted k.val s = v k s := by
  intro k
  induction k using Fin.induction with
  | zero => intro s; exact (hzero s).symm
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accepted k.val)).sum = v k.succ s
    rw [show paths succ accepted k.val = v k.castSucc from funext ih]
    exact hnext k s

end A208640Count

namespace A208640Proof

open scoped BigOperators

def runFrom (s : State) : List Col → Option State
  | [] => some s
  | r :: w => (step s r).bind (fun t => runFrom t w)

def GoodFrom (s : State) (w : List Col) : Prop :=
  ∃ t, runFrom s w = some t ∧ accept t

def listColumnsOK (p : Option Col) : List Col → Prop
  | [] => True
  | q :: w => localOK p q w.head? ∧ listColumnsOK (some q) w

def previousCol {n : ℕ} (p : Option Col) (w : Fin n → Col) (j : Fin n) : Option Col :=
  if h : 0 < j.val then some (w ⟨j.val - 1, by omega⟩) else p

def followingCol {n : ℕ} (w : Fin n → Col) (j : Fin n) : Option Col :=
  if h : j.val + 1 < n then some (w ⟨j.val + 1, h⟩) else none

def ColumnsOK {n : ℕ} (p : Option Col) (w : Fin n → Col) : Prop :=
  ∀ j, localOK (previousCol p w j) (w j) (followingCol w j)

@[simp] theorem goodFrom_nil (s : State) : GoodFrom s [] ↔ accept s := by
  simp [GoodFrom, runFrom]

theorem goodFrom_cons (p : Option Col) (q r : Col) (w : List Col) :
    GoodFrom (p, q) (r :: w) ↔
      localOK p q (some r) ∧ GoodFrom (some q, r) w := by
  by_cases h : localOK p q (some r)
  · simp [GoodFrom, runFrom, step, h]
  · simp [GoodFrom, runFrom, step, h]

theorem goodFrom_iff_list (p : Option Col) (q : Col) (w : List Col) :
    GoodFrom (p, q) w ↔ listColumnsOK p (q :: w) := by
  induction w generalizing p q with
  | nil => simp [listColumnsOK, accept]
  | cons r w ih =>
    rw [goodFrom_cons, ih]
    rfl

@[simp] theorem previousCol_cons_zero {n : ℕ} (p : Option Col) (q : Col)
    (w : Fin n → Col) : previousCol p (Fin.cons q w) 0 = p := by
  simp [previousCol]

@[simp] theorem previousCol_cons_succ {n : ℕ} (p : Option Col) (q : Col)
    (w : Fin n → Col) (j : Fin n) :
    previousCol p (Fin.cons q w) j.succ = previousCol (some q) w j := by
  by_cases h : 0 < j.val
  · simp only [previousCol, Fin.val_succ, Nat.succ_pos, dif_pos, h]
    congr 1
    have he : (⟨j.val + 1 - 1, by omega⟩ : Fin (n + 1)) =
        (⟨j.val - 1, by omega⟩ : Fin n).succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [he, Fin.cons_succ]
  · have hj : j.val = 0 := by omega
    simp [previousCol, hj]

@[simp] theorem followingCol_cons_succ {n : ℕ} (q : Col) (w : Fin n → Col)
    (j : Fin n) : followingCol (Fin.cons q w) j.succ = followingCol w j := by
  by_cases h : j.val + 1 < n
  · simp only [followingCol, Fin.val_succ, show j.val + 1 + 1 < n + 1 by omega,
      dif_pos, h]
    congr 1
  · simp [followingCol, h, show ¬j.val + 1 + 1 < n + 1 by omega]

@[simp] theorem followingCol_cons_zero {n : ℕ} (q : Col) (w : Fin n → Col) :
    followingCol (Fin.cons q w) 0 = (List.ofFn w).head? := by
  cases n with
  | zero => simp [followingCol]
  | succ n =>
    simp [followingCol, List.ofFn_succ, show (⟨1, by omega⟩ : Fin (n + 2)) =
      (0 : Fin (n + 1)).succ by rfl]

theorem columnsOK_cons {n : ℕ} (p : Option Col) (q : Col) (w : Fin n → Col) :
    ColumnsOK p (Fin.cons q w) ↔
      localOK p q (List.ofFn w).head? ∧ ColumnsOK (some q) w := by
  unfold ColumnsOK
  rw [Fin.forall_fin_succ]
  simp only [previousCol_cons_zero, Fin.cons_zero, followingCol_cons_zero,
    previousCol_cons_succ, Fin.cons_succ, followingCol_cons_succ]

theorem columnsOK_iff_list {n : ℕ} (p : Option Col) (w : Fin n → Col) :
    ColumnsOK p w ↔ listColumnsOK p (List.ofFn w) := by
  induction n generalizing p with
  | zero => simp [ColumnsOK, listColumnsOK]
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    rw [hw, columnsOK_cons, ih]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, listColumnsOK]

theorem goodFrom_iff_columns {n : ℕ} (p : Option Col) (q : Col) (w : Fin n → Col) :
    GoodFrom (p, q) (List.ofFn w) ↔ ColumnsOK p (Fin.cons q w) := by
  rw [columnsOK_iff_list, goodFrom_iff_list]
  simp [List.ofFn_succ]

theorem card_words_succ {A : Type*} [Fintype A] (n : ℕ)
    (P : (Fin (n + 1) → A) → Prop) :
    Nat.card {w : Fin (n + 1) → A // P w} =
      ∑ a : A, Nat.card {v : Fin n → A // P (Fin.cons a v)} := by
  classical
  calc
    _ = Nat.card {p : A × (Fin n → A) // P (Fin.cons p.1 p.2)} :=
      Nat.card_congr ((Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm.subtypeEquiv
        (by intro w; simp [Fin.consEquiv]))
    _ = Nat.card (Σ a : A, {v : Fin n → A // P (Fin.cons a v)}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a v => P (Fin.cons a v)))
    _ = _ := Nat.card_sigma

noncomputable def suffixCount (s : State) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Col // GoodFrom s (List.ofFn w)}

theorem suffixCount_zero (s : State) :
    suffixCount s 0 = if accept s then 1 else 0 := by
  classical
  by_cases h : accept s <;> simp [suffixCount, h, Nat.card_eq_fintype_card]

theorem suffixCount_succ (s : State) (n : ℕ) :
    suffixCount s (n + 1) =
      ∑ q : Col, (step s q).elim 0 (fun t => suffixCount t n) := by
  classical
  unfold suffixCount
  rw [card_words_succ]
  apply Finset.sum_congr rfl
  intro q _
  cases h : step s q with
  | none => simp [GoodFrom, runFrom, h, Nat.card_eq_fintype_card]
  | some t => simp [GoodFrom, runFrom, h]

lemma sum_filterMap {A B : Type*} (L : List A) (f : A → Option B) (g : B → ℕ) :
    ((L.filterMap f).map g).sum = (L.map (fun a => (f a).elim 0 g)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : f a <;> simp [h, ih]

theorem suffixCount_eq_paths {I : Type*}
    (state : I → State) (succ : I → List I) (accepted : I → ℕ)
    (hstep : ∀ i, allCols.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, (if accept (state i) then 1 else 0) = accepted i) :
    ∀ n i, suffixCount (state i) n = A208640Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_allCols, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A208640Count.paths succ accepted n from funext ih]
    rfl

end A208640Proof

namespace A208640Proof
open OMA.S_oeis_a208640

theorem rowMajorNew_iff {n : ℕ} (hn : 0 < n)
    (x : Fin 5 → Fin n → Fin 2) :
    RowMajorNew x ↔ x 0 ⟨0, hn⟩ = 0 := by
  constructor
  · intro h
    by_contra hx
    have hxv : (x 0 ⟨0, hn⟩).val ≠ 0 := by
      intro he
      exact hx (Fin.ext he)
    have hp : (0 : Fin 2) < x 0 ⟨0, hn⟩ := by
      change 0 < (x 0 ⟨0, hn⟩).val
      omega
    obtain ⟨i, j, hi, _⟩ := h 0 ⟨0, hn⟩ 0 hp
    rcases hi with hi | ⟨_, hj⟩
    · change i.val < 0 at hi
      omega
    · change j.val < 0 at hj
      omega
  · intro h i j u hu
    have hu0 : u = 0 := by
      apply Fin.ext
      have hx := (x i j).isLt
      change u.val < (x i j).val at hu
      omega
    subst u
    refine ⟨0, ⟨0, hn⟩, ?_, h⟩
    by_cases hi : i = 0
    · right
      refine ⟨hi.symm, ?_⟩
      by_cases hj : j = ⟨0, hn⟩
      · subst i
        subst j
        simp [h] at hu
      · have hjv : j.val ≠ 0 := by
          intro he
          exact hj (Fin.ext he)
        change 0 < j.val
        omega
    · left
      have hiv : i.val ≠ 0 := by
        intro he
        exact hi (Fin.ext he)
      change 0 < i.val
      omega

private theorem count_unique {α : Type*} [Fintype α] [DecidableEq α]
    (R P : α → Prop) [DecidablePred R] [DecidablePred P] (a : α)
    (hR : ∀ b, R b ↔ b = a) :
    ((Finset.univ : Finset α).filter (fun b => R b ∧ P b)).card =
      if P a then 1 else 0 := by
  classical
  have hs : (Finset.univ : Finset α).filter (fun b => R b ∧ P b) =
      if P a then {a} else ∅ := by
    ext b
    by_cases hb : b = a
    · subst b
      by_cases hp : P a <;> simp [hR, hp]
    · have hr : ¬ R b := fun h => hb ((hR b).mp h)
      by_cases hp : P a <;> simp [hb, hr, hp]
  rw [hs]
  split_ifs <;> simp

def leftSet {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) :=
  (Finset.univ : Finset (Fin 5 × Fin n)).filter fun p =>
    (p.1 = i ∧ p.2.val + 1 = j.val) ∧ x p.1 p.2 = x i j

def upperSet {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) :=
  (Finset.univ : Finset (Fin 5 × Fin n)).filter fun p =>
    (p.1.val + 1 = i.val ∧ p.2 = j) ∧ x p.1 p.2 = x i j

def rightSet {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) :=
  (Finset.univ : Finset (Fin 5 × Fin n)).filter fun p =>
    (p.1.val + 1 = i.val ∧ p.2.val = j.val + 1) ∧ x p.1 p.2 = x i j

theorem eqNbrs_split {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) :
    eqNbrs x i j = (leftSet x i j).card + (upperSet x i j).card +
      (rightSet x i j).card := by
  classical
  have hlu : Disjoint (leftSet x i j) (upperSet x i j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2.1.1
    have hq' := (Finset.mem_filter.mp hq).2.1.1
    have hh := congrArg Fin.val hp'
    omega
  have hlr : Disjoint (leftSet x i j) (rightSet x i j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2.1.1
    have hq' := (Finset.mem_filter.mp hq).2.1.1
    have hh := congrArg Fin.val hp'
    omega
  have hur : Disjoint (upperSet x i j) (rightSet x i j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2.1.2
    have hq' := (Finset.mem_filter.mp hq).2.1.2
    have hh := congrArg Fin.val hp'
    omega
  have hboth : Disjoint (leftSet x i j ∪ upperSet x i j) (rightSet x i j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.disjoint_left.mp hlr hp hq
    · exact Finset.disjoint_left.mp hur hp hq
  have he : ((Finset.univ : Finset (Fin 5 × Fin n)).filter (fun p =>
      ((p.1 = i ∧ p.2.val + 1 = j.val) ∨ (p.1.val + 1 = i.val ∧ p.2 = j) ∨
        (p.1.val + 1 = i.val ∧ p.2.val = j.val + 1)) ∧ x p.1 p.2 = x i j)) =
      leftSet x i j ∪ upperSet x i j ∪ rightSet x i j := by
    ext p
    simp only [leftSet, upperSet, rightSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    tauto
  rw [eqNbrs, he, Finset.card_union_of_disjoint hboth, Finset.card_union_of_disjoint hlu]

def leftMatches {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) : ℕ :=
  if h : 0 < j.val then
    if x i ⟨j.val - 1, by have := j.isLt; omega⟩ = x i j then 1 else 0
  else 0

theorem card_leftSet {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 5) (j : Fin n) :
    (leftSet x i j).card = leftMatches x i j := by
  classical
  by_cases hj : 0 < j.val
  · let jp : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
    unfold leftSet leftMatches
    rw [dif_pos hj]
    apply count_unique _ _ (i, jp)
    intro p
    constructor
    · rintro ⟨hr, hc⟩
      apply Prod.ext hr
      apply Fin.ext
      dsimp [jp]
      omega
    · intro hp
      subst p
      exact ⟨rfl, by dsimp [jp]; omega⟩
  · have hs : leftSet x i j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hcol := (Finset.mem_filter.mp hp).2.1.2
      omega
    simp [hs, leftMatches, hj]

theorem card_upperSet_succ {n : ℕ} (x : Fin 5 → Fin n → Fin 2)
    (i : Fin 4) (j : Fin n) :
    (upperSet x i.succ j).card = if x i.castSucc j = x i.succ j then 1 else 0 := by
  unfold upperSet
  apply count_unique _ _ (i.castSucc, j)
  intro p
  constructor
  · rintro ⟨hr, hc⟩
    apply Prod.ext _ hc
    apply Fin.ext
    change p.1.val = i.val
    change p.1.val + 1 = i.val + 1 at hr
    omega
  · intro hp
    subst p
    exact ⟨rfl, rfl⟩

def rightMatches {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (i : Fin 4) (j : Fin n) : ℕ :=
  if h : j.val + 1 < n then
    if x i.castSucc ⟨j.val + 1, h⟩ = x i.succ j then 1 else 0
  else 0

theorem card_rightSet_succ {n : ℕ} (x : Fin 5 → Fin n → Fin 2)
    (i : Fin 4) (j : Fin n) :
    (rightSet x i.succ j).card = rightMatches x i j := by
  classical
  by_cases hj : j.val + 1 < n
  · unfold rightSet rightMatches
    rw [dif_pos hj]
    apply count_unique _ _ (i.castSucc, (⟨j.val + 1, hj⟩ : Fin n))
    intro p
    constructor
    · rintro ⟨hr, hc⟩
      apply Prod.ext
      · apply Fin.ext
        change p.1.val = i.val
        change p.1.val + 1 = i.val + 1 at hr
        omega
      · exact Fin.ext hc
    · intro hp
      subst p
      exact ⟨rfl, rfl⟩
  · have hs : rightSet x i.succ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hcol := (Finset.mem_filter.mp hp).2.1.2
      have hpcol := p.2.isLt
      omega
    simp [hs, rightMatches, hj]

theorem eqNbrs_succ {n : ℕ} (x : Fin 5 → Fin n → Fin 2)
    (i : Fin 4) (j : Fin n) :
    eqNbrs x i.succ j = leftMatches x i.succ j +
      (if x i.castSucc j = x i.succ j then 1 else 0) + rightMatches x i j := by
  rw [eqNbrs_split, card_leftSet, card_upperSet_succ, card_rightSet_succ]

theorem eqNbrs_zero_le {n : ℕ} (x : Fin 5 → Fin n → Fin 2) (j : Fin n) :
    eqNbrs x 0 j ≤ 1 := by
  have hu : upperSet x 0 j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2.1.1
    change p.1.val + 1 = 0 at hh
    omega
  have hr : rightSet x 0 j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2.1.1
    change p.1.val + 1 = 0 at hh
    omega
  simp only [eqNbrs_split, hu, hr, Finset.card_empty, add_zero, card_leftSet]
  unfold leftMatches
  split_ifs <;> omega

theorem rowMajorNew_iff_zero {n : ℕ} (x : Fin 5 → Fin (n + 1) → Fin 2) :
    RowMajorNew x ↔ x 0 0 = 0 :=
  rowMajorNew_iff (Nat.succ_pos n) x

theorem eqNbrs_succ_local {n : ℕ} (x : Fin 5 → Fin n → Fin 2)
    (i : Fin 4) (j : Fin n) :
    eqNbrs x i.succ j =
      leftCount (previousCol none (fun j i => x i j) j) (fun i => x i j) i +
      upperCount (fun i => x i j) i +
      rightCount (fun i => x i j) (followingCol (fun j i => x i j) j) i := by
  rw [eqNbrs_succ]
  have hl : leftMatches x i.succ j =
      leftCount (previousCol none (fun j i => x i j) j) (fun i => x i j) i := by
    by_cases hj : 0 < j.val <;> simp [leftMatches, previousCol, leftCount, hj]
  have hr : rightMatches x i j =
      rightCount (fun i => x i j) (followingCol (fun j i => x i j) j) i := by
    by_cases hj : j.val + 1 < n <;> simp [rightMatches, followingCol, rightCount, hj]
  rw [hl, hr]
  rfl

theorem cond_iff_columns {n : ℕ} (x : Fin 5 → Fin n → Fin 2) :
    Cond x ↔ ColumnsOK none (fun j i => x i j) := by
  constructor
  · intro h j i
    rw [← eqNbrs_succ_local]
    exact h i.succ j
  · intro h i j
    refine Fin.cases ?_ ?_ i
    · exact eqNbrs_zero_le x j
    · intro k
      rw [eqNbrs_succ_local]
      exact h j k

end A208640Proof

namespace A208640Proof

open scoped BigOperators
open OMA.S_oeis_a208640

def arrayColumnEquiv (n : ℕ) : (Fin 5 → Fin n → Fin 2) ≃ (Fin n → Col) where
  toFun x j i := x i j
  invFun w i j := w j i
  left_inv _ := rfl
  right_inv _ := rfl

theorem a_succ_eq_columnCount (n : ℕ) :
    a (n + 1) = Nat.card {w : Fin (n + 1) → Col // ColumnsOK none w ∧ w 0 0 = 0} := by
  classical
  calc
    _ = Nat.card {x : Fin 5 → Fin (n + 1) → Fin 2 // Cond x ∧ RowMajorNew x} := by
      simp [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := Nat.card_congr ((arrayColumnEquiv (n + 1)).subtypeEquiv (by
      intro x
      change Cond x ∧ RowMajorNew x ↔ ColumnsOK none (fun j i => x i j) ∧ x 0 0 = 0
      rw [cond_iff_columns, rowMajorNew_iff_zero]))

theorem a_succ_eq_suffix (n : ℕ) :
    a (n + 1) = ∑ q : Col, if q 0 = 0 then suffixCount (none, q) n else 0 := by
  classical
  rw [a_succ_eq_columnCount, card_words_succ]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q 0 = 0
  · rw [if_pos hq]
    unfold suffixCount
    apply Nat.card_congr (Equiv.subtypeEquivRight _)
    intro w
    simp only [Fin.cons_zero, hq, and_true]
    exact (goodFrom_iff_columns none q w).symm
  · simp [hq, Nat.card_eq_fintype_card]

lemma sum_filter (L : List Col) (f : Col → ℕ) :
    ((L.filter fun q => q 0 = 0).map f).sum =
      (L.map fun q => if q 0 = 0 then f q else 0).sum := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    by_cases hq : q 0 = 0 <;> simp [hq, ih]

theorem a_succ_eq_initialStates (n : ℕ) :
    a (n + 1) = (initialStates.map fun s => suffixCount s n).sum := by
  rw [a_succ_eq_suffix, initialStates, List.map_map, sum_filter, sum_allCols]
  rfl

end A208640Proof

namespace A208640Table
open A208640Proof

abbrev Index := Fin 1056
def index (n : ℕ) : Index := ⟨n % 1056, Nat.mod_lt _ (by decide)⟩

def state (i : Index) : State :=
  (if i.val / 32 = 0 then none else
    some (decode ⟨i.val / 32 - 1, by omega⟩),
   decode ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩)

def succ (i : Index) : List Index :=
  (if i.val < 528 then (if i.val < 264 then (if i.val < 132 then (if i.val < 66 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [index 47, index 63] else [index 78, index 79, index 94, index 95]) else (if i.val < 3 then [index 108, index 109, index 110, index 111, index 124, index 125, index 126, index 127] else [index 140, index 142, index 156, index 158])) else (if i.val < 6 then (if i.val < 5 then [index 169, index 171, index 173, index 175, index 185, index 187, index 189, index 191] else [index 200, index 201, index 202, index 203, index 204, index 205, index 206, index 207, index 216, index 217, index 218, index 219, index 220, index 221, index 222, index 223]) else (if i.val < 7 then [index 232, index 233, index 236, index 237, index 248, index 249, index 252, index 253] else [index 264, index 268, index 280, index 284]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [index 291, index 295, index 299, index 303, index 307, index 311, index 315, index 319] else [index 322, index 323, index 326, index 327, index 330, index 331, index 334, index 335, index 338, index 339, index 342, index 343, index 346, index 347, index 350, index 351]) else (if i.val < 11 then [index 352, index 353, index 354, index 355, index 356, index 357, index 358, index 359, index 360, index 361, index 362, index 363, index 364, index 365, index 366, index 367, index 368, index 369, index 370, index 371, index 372, index 373, index 374, index 375, index 376, index 377, index 378, index 379, index 380, index 381, index 382, index 383] else [index 384, index 386, index 388, index 390, index 392, index 394, index 396, index 398, index 400, index 402, index 404, index 406, index 408, index 410, index 412, index 414])) else (if i.val < 14 then (if i.val < 13 then [index 417, index 419, index 425, index 427, index 433, index 435, index 441, index 443] else [index 448, index 449, index 450, index 451, index 456, index 457, index 458, index 459, index 464, index 465, index 466, index 467, index 472, index 473, index 474, index 475]) else (if i.val < 15 then [index 480, index 481, index 488, index 489, index 496, index 497, index 504, index 505] else [index 512, index 520, index 528, index 536])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [index 551, index 559, index 567, index 575] else [index 582, index 583, index 590, index 591, index 598, index 599, index 606, index 607]) else (if i.val < 19 then [index 612, index 613, index 614, index 615, index 620, index 621, index 622, index 623, index 628, index 629, index 630, index 631, index 636, index 637, index 638, index 639] else [index 644, index 646, index 652, index 654, index 660, index 662, index 668, index 670])) else (if i.val < 22 then (if i.val < 21 then [index 673, index 675, index 677, index 679, index 681, index 683, index 685, index 687, index 689, index 691, index 693, index 695, index 697, index 699, index 701, index 703] else [index 704, index 705, index 706, index 707, index 708, index 709, index 710, index 711, index 712, index 713, index 714, index 715, index 716, index 717, index 718, index 719, index 720, index 721, index 722, index 723, index 724, index 725, index 726, index 727, index 728, index 729, index 730, index 731, index 732, index 733, index 734, index 735]) else (if i.val < 23 then [index 736, index 737, index 740, index 741, index 744, index 745, index 748, index 749, index 752, index 753, index 756, index 757, index 760, index 761, index 764, index 765] else [index 768, index 772, index 776, index 780, index 784, index 788, index 792, index 796]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [index 803, index 807, index 819, index 823] else [index 834, index 835, index 838, index 839, index 850, index 851, index 854, index 855]) else (if i.val < 27 then [index 864, index 865, index 866, index 867, index 868, index 869, index 870, index 871, index 880, index 881, index 882, index 883, index 884, index 885, index 886, index 887] else [index 896, index 898, index 900, index 902, index 912, index 914, index 916, index 918])) else (if i.val < 30 then (if i.val < 29 then [index 929, index 931, index 945, index 947] else [index 960, index 961, index 962, index 963, index 976, index 977, index 978, index 979]) else (if i.val < 31 then [index 992, index 993, index 1008, index 1009] else (if i.val < 32 then [index 1024, index 1040] else [])))))) else (if i.val < 49 then (if i.val < 41 then [] else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then [] else [index 362, index 363, index 366, index 367, index 378, index 379, index 382, index 383]) else (if i.val < 44 then [index 394, index 398, index 410, index 414] else [])) else (if i.val < 47 then (if i.val < 46 then [index 457, index 459, index 473, index 475] else [index 488, index 489, index 504, index 505]) else (if i.val < 48 then [index 520, index 536] else [])))) else (if i.val < 57 then (if i.val < 53 then [] else (if i.val < 55 then (if i.val < 54 then [index 709, index 711, index 717, index 719, index 725, index 727, index 733, index 735] else [index 740, index 741, index 748, index 749, index 756, index 757, index 764, index 765]) else (if i.val < 56 then [index 772, index 780, index 788, index 796] else []))) else (if i.val < 61 then (if i.val < 59 then (if i.val < 58 then [] else [index 866, index 867, index 870, index 871, index 882, index 883, index 886, index 887]) else (if i.val < 60 then [index 898, index 902, index 914, index 918] else [])) else (if i.val < 63 then (if i.val < 62 then [index 961, index 963, index 977, index 979] else [index 992, index 993, index 1008, index 1009]) else (if i.val < 64 then [index 1024, index 1040] else [])))))) else (if i.val < 99 then (if i.val < 82 then (if i.val < 74 then [] else (if i.val < 78 then (if i.val < 76 then (if i.val < 75 then [index 362, index 363, index 366, index 367, index 378, index 379, index 382, index 383] else [index 394, index 398, index 410, index 414]) else (if i.val < 77 then [] else [index 457, index 459, index 473, index 475])) else (if i.val < 80 then (if i.val < 79 then [index 488, index 489, index 504, index 505] else [index 520, index 536]) else []))) else (if i.val < 90 then (if i.val < 86 then (if i.val < 84 then [] else (if i.val < 85 then [] else [index 709, index 711, index 717, index 719, index 725, index 727, index 733, index 735])) else (if i.val < 88 then (if i.val < 87 then [index 740, index 741, index 748, index 749, index 756, index 757, index 764, index 765] else [index 772, index 780, index 788, index 796]) else [])) else (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then [index 866, index 867, index 870, index 871, index 882, index 883, index 886, index 887] else [index 898, index 902, index 914, index 918]) else (if i.val < 93 then [] else [index 961, index 963, index 977, index 979])) else (if i.val < 96 then (if i.val < 95 then [index 992, index 993, index 1008, index 1009] else [index 1024, index 1040]) else [])))) else (if i.val < 115 then (if i.val < 107 then (if i.val < 103 then [] else (if i.val < 105 then [] else (if i.val < 106 then [] else [index 362, index 366, index 378, index 382]))) else (if i.val < 111 then (if i.val < 109 then (if i.val < 108 then [] else [index 425, index 427, index 441, index 443]) else (if i.val < 110 then [index 456, index 457, index 458, index 459, index 472, index 473, index 474, index 475] else [index 488, index 504])) else [])) else (if i.val < 123 then (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then [] else [index 677, index 679, index 685, index 687, index 693, index 695, index 701, index 703]) else (if i.val < 118 then [index 708, index 709, index 710, index 711, index 716, index 717, index 718, index 719, index 724, index 725, index 726, index 727, index 732, index 733, index 734, index 735] else [index 740, index 748, index 756, index 764])) else (if i.val < 121 then [] else (if i.val < 122 then [] else [index 866, index 870, index 882, index 886]))) else (if i.val < 127 then (if i.val < 125 then (if i.val < 124 then [] else [index 929, index 931, index 945, index 947]) else (if i.val < 126 then [index 960, index 961, index 962, index 963, index 976, index 977, index 978, index 979] else [index 992, index 1008])) else []))))) else (if i.val < 198 then (if i.val < 165 then (if i.val < 148 then (if i.val < 140 then (if i.val < 136 then [] else (if i.val < 138 then [] else (if i.val < 139 then [index 362, index 366, index 378, index 382] else []))) else (if i.val < 144 then (if i.val < 142 then (if i.val < 141 then [index 425, index 427, index 441, index 443] else [index 456, index 457, index 458, index 459, index 472, index 473, index 474, index 475]) else (if i.val < 143 then [index 488, index 504] else [])) else [])) else (if i.val < 156 then (if i.val < 152 then (if i.val < 150 then (if i.val < 149 then [index 677, index 679, index 685, index 687, index 693, index 695, index 701, index 703] else [index 708, index 709, index 710, index 711, index 716, index 717, index 718, index 719, index 724, index 725, index 726, index 727, index 732, index 733, index 734, index 735]) else (if i.val < 151 then [index 740, index 748, index 756, index 764] else [])) else (if i.val < 154 then [] else (if i.val < 155 then [index 866, index 870, index 882, index 886] else []))) else (if i.val < 160 then (if i.val < 158 then (if i.val < 157 then [index 929, index 931, index 945, index 947] else [index 960, index 961, index 962, index 963, index 976, index 977, index 978, index 979]) else (if i.val < 159 then [index 992, index 1008] else [])) else []))) else (if i.val < 181 then (if i.val < 173 then (if i.val < 169 then [] else (if i.val < 171 then (if i.val < 170 then [index 331, index 335, index 347, index 351] else [index 360, index 361, index 362, index 363, index 364, index 365, index 366, index 367, index 376, index 377, index 378, index 379, index 380, index 381, index 382, index 383]) else (if i.val < 172 then [index 392, index 394, index 396, index 398, index 408, index 410, index 412, index 414] else []))) else (if i.val < 177 then (if i.val < 175 then (if i.val < 174 then [index 457, index 473] else []) else []) else [])) else (if i.val < 189 then (if i.val < 185 then (if i.val < 183 then (if i.val < 182 then [index 709, index 717, index 725, index 733] else []) else []) else (if i.val < 187 then (if i.val < 186 then [index 835, index 839, index 851, index 855] else [index 864, index 865, index 866, index 867, index 868, index 869, index 870, index 871, index 880, index 881, index 882, index 883, index 884, index 885, index 886, index 887]) else (if i.val < 188 then [index 896, index 898, index 900, index 902, index 912, index 914, index 916, index 918] else []))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then [index 961, index 977] else []) else []) else [])))) else (if i.val < 231 then (if i.val < 214 then (if i.val < 206 then (if i.val < 202 then (if i.val < 200 then [] else (if i.val < 201 then [] else [index 331, index 335, index 347, index 351])) else (if i.val < 204 then (if i.val < 203 then [index 360, index 361, index 362, index 363, index 364, index 365, index 366, index 367, index 376, index 377, index 378, index 379, index 380, index 381, index 382, index 383] else [index 392, index 394, index 396, index 398, index 408, index 410, index 412, index 414]) else (if i.val < 205 then [] else [index 457, index 473]))) else (if i.val < 210 then [] else (if i.val < 212 then [] else (if i.val < 213 then [] else [index 709, index 717, index 725, index 733])))) else (if i.val < 222 then (if i.val < 218 then (if i.val < 216 then [] else (if i.val < 217 then [] else [index 835, index 839, index 851, index 855])) else (if i.val < 220 then (if i.val < 219 then [index 864, index 865, index 866, index 867, index 868, index 869, index 870, index 871, index 880, index 881, index 882, index 883, index 884, index 885, index 886, index 887] else [index 896, index 898, index 900, index 902, index 912, index 914, index 916, index 918]) else (if i.val < 221 then [] else [index 961, index 977]))) else [])) else (if i.val < 247 then (if i.val < 239 then (if i.val < 235 then (if i.val < 233 then (if i.val < 232 then [] else [index 299, index 303, index 315, index 319]) else (if i.val < 234 then [index 330, index 331, index 334, index 335, index 346, index 347, index 350, index 351] else [index 360, index 362, index 364, index 366, index 376, index 378, index 380, index 382])) else (if i.val < 237 then (if i.val < 236 then [] else [index 425, index 441]) else (if i.val < 238 then [index 456, index 457, index 472, index 473] else []))) else (if i.val < 243 then [] else (if i.val < 245 then (if i.val < 244 then [] else [index 677, index 685, index 693, index 701]) else (if i.val < 246 then [index 708, index 709, index 716, index 717, index 724, index 725, index 732, index 733] else [])))) else (if i.val < 255 then (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then [] else [index 803, index 807, index 819, index 823]) else (if i.val < 250 then [index 834, index 835, index 838, index 839, index 850, index 851, index 854, index 855] else [index 864, index 866, index 868, index 870, index 880, index 882, index 884, index 886])) else (if i.val < 253 then (if i.val < 252 then [] else [index 929, index 945]) else (if i.val < 254 then [index 960, index 961, index 976, index 977] else []))) else []))))) else (if i.val < 396 then (if i.val < 330 then (if i.val < 297 then (if i.val < 280 then (if i.val < 272 then (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then [index 299, index 303, index 315, index 319] else [index 330, index 331, index 334, index 335, index 346, index 347, index 350, index 351]) else (if i.val < 267 then [index 360, index 362, index 364, index 366, index 376, index 378, index 380, index 382] else [])) else (if i.val < 270 then (if i.val < 269 then [index 425, index 441] else [index 456, index 457, index 472, index 473]) else [])) else (if i.val < 276 then [] else (if i.val < 278 then (if i.val < 277 then [index 677, index 685, index 693, index 701] else [index 708, index 709, index 716, index 717, index 724, index 725, index 732, index 733]) else []))) else (if i.val < 288 then (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then [index 803, index 807, index 819, index 823] else [index 834, index 835, index 838, index 839, index 850, index 851, index 854, index 855]) else (if i.val < 283 then [index 864, index 866, index 868, index 870, index 880, index 882, index 884, index 886] else [])) else (if i.val < 286 then (if i.val < 285 then [index 929, index 945] else [index 960, index 961, index 976, index 977]) else [])) else [])) else (if i.val < 313 then (if i.val < 305 then (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then [] else [index 362, index 363, index 378, index 379]) else (if i.val < 300 then [index 394, index 410] else [])) else []) else (if i.val < 309 then (if i.val < 307 then (if i.val < 306 then [] else [index 614, index 615, index 622, index 623, index 630, index 631, index 638, index 639]) else (if i.val < 308 then [index 646, index 654, index 662, index 670] else [])) else (if i.val < 311 then (if i.val < 310 then [index 705, index 707, index 709, index 711, index 713, index 715, index 717, index 719, index 721, index 723, index 725, index 727, index 729, index 731, index 733, index 735] else [index 736, index 737, index 740, index 741, index 744, index 745, index 748, index 749, index 752, index 753, index 756, index 757, index 760, index 761, index 764, index 765]) else (if i.val < 312 then [index 768, index 772, index 776, index 780, index 784, index 788, index 792, index 796] else [])))) else (if i.val < 321 then (if i.val < 317 then (if i.val < 315 then (if i.val < 314 then [] else [index 866, index 867, index 882, index 883]) else (if i.val < 316 then [index 898, index 914] else [])) else []) else []))) else (if i.val < 363 then (if i.val < 346 then (if i.val < 338 then (if i.val < 334 then (if i.val < 332 then (if i.val < 331 then [index 362, index 363, index 378, index 379] else [index 394, index 410]) else []) else []) else (if i.val < 342 then (if i.val < 340 then (if i.val < 339 then [index 614, index 615, index 622, index 623, index 630, index 631, index 638, index 639] else [index 646, index 654, index 662, index 670]) else (if i.val < 341 then [] else [index 705, index 707, index 709, index 711, index 713, index 715, index 717, index 719, index 721, index 723, index 725, index 727, index 729, index 731, index 733, index 735])) else (if i.val < 344 then (if i.val < 343 then [index 736, index 737, index 740, index 741, index 744, index 745, index 748, index 749, index 752, index 753, index 756, index 757, index 760, index 761, index 764, index 765] else [index 768, index 772, index 776, index 780, index 784, index 788, index 792, index 796]) else []))) else (if i.val < 354 then (if i.val < 350 then (if i.val < 348 then (if i.val < 347 then [index 866, index 867, index 882, index 883] else [index 898, index 914]) else []) else []) else (if i.val < 358 then [] else (if i.val < 360 then [] else (if i.val < 361 then [] else (if i.val < 362 then [] else [index 362, index 378])))))) else (if i.val < 379 then (if i.val < 371 then (if i.val < 367 then [] else (if i.val < 369 then [] else (if i.val < 370 then [] else [index 614, index 622, index 630, index 638]))) else (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then [] else [index 673, index 675, index 677, index 679, index 681, index 683, index 685, index 687, index 689, index 691, index 693, index 695, index 697, index 699, index 701, index 703]) else (if i.val < 374 then [index 704, index 705, index 706, index 707, index 708, index 709, index 710, index 711, index 712, index 713, index 714, index 715, index 716, index 717, index 718, index 719, index 720, index 721, index 722, index 723, index 724, index 725, index 726, index 727, index 728, index 729, index 730, index 731, index 732, index 733, index 734, index 735] else [index 736, index 740, index 744, index 748, index 752, index 756, index 760, index 764])) else (if i.val < 377 then [] else (if i.val < 378 then [] else [index 866, index 882])))) else (if i.val < 387 then [] else (if i.val < 391 then [] else (if i.val < 393 then [] else (if i.val < 394 then [] else (if i.val < 395 then [index 362, index 378] else [])))))))) else (if i.val < 462 then (if i.val < 429 then (if i.val < 412 then (if i.val < 404 then (if i.val < 400 then [] else (if i.val < 402 then [] else (if i.val < 403 then [index 614, index 622, index 630, index 638] else []))) else (if i.val < 408 then (if i.val < 406 then (if i.val < 405 then [index 673, index 675, index 677, index 679, index 681, index 683, index 685, index 687, index 689, index 691, index 693, index 695, index 697, index 699, index 701, index 703] else [index 704, index 705, index 706, index 707, index 708, index 709, index 710, index 711, index 712, index 713, index 714, index 715, index 716, index 717, index 718, index 719, index 720, index 721, index 722, index 723, index 724, index 725, index 726, index 727, index 728, index 729, index 730, index 731, index 732, index 733, index 734, index 735]) else (if i.val < 407 then [index 736, index 740, index 744, index 748, index 752, index 756, index 760, index 764] else [])) else (if i.val < 410 then [] else (if i.val < 411 then [index 866, index 882] else [])))) else (if i.val < 420 then [] else (if i.val < 424 then [] else (if i.val < 426 then (if i.val < 425 then [] else [index 331, index 347]) else (if i.val < 427 then [index 360, index 361, index 362, index 363, index 376, index 377, index 378, index 379] else (if i.val < 428 then [index 392, index 394, index 408, index 410] else [])))))) else (if i.val < 445 then (if i.val < 437 then (if i.val < 433 then [] else (if i.val < 435 then (if i.val < 434 then [index 583, index 591, index 599, index 607] else [index 612, index 613, index 614, index 615, index 620, index 621, index 622, index 623, index 628, index 629, index 630, index 631, index 636, index 637, index 638, index 639]) else (if i.val < 436 then [index 644, index 646, index 652, index 654, index 660, index 662, index 668, index 670] else []))) else (if i.val < 441 then (if i.val < 439 then (if i.val < 438 then [index 705, index 709, index 713, index 717, index 721, index 725, index 729, index 733] else []) else []) else (if i.val < 443 then (if i.val < 442 then [index 835, index 851] else [index 864, index 865, index 866, index 867, index 880, index 881, index 882, index 883]) else (if i.val < 444 then [index 896, index 898, index 912, index 914] else [])))) else (if i.val < 453 then [] else (if i.val < 457 then [] else (if i.val < 459 then (if i.val < 458 then [index 331, index 347] else [index 360, index 361, index 362, index 363, index 376, index 377, index 378, index 379]) else (if i.val < 460 then [index 392, index 394, index 408, index 410] else [])))))) else (if i.val < 495 then (if i.val < 478 then (if i.val < 470 then (if i.val < 466 then (if i.val < 464 then [] else (if i.val < 465 then [] else [index 583, index 591, index 599, index 607])) else (if i.val < 468 then (if i.val < 467 then [index 612, index 613, index 614, index 615, index 620, index 621, index 622, index 623, index 628, index 629, index 630, index 631, index 636, index 637, index 638, index 639] else [index 644, index 646, index 652, index 654, index 660, index 662, index 668, index 670]) else (if i.val < 469 then [] else [index 705, index 709, index 713, index 717, index 721, index 725, index 729, index 733]))) else (if i.val < 474 then (if i.val < 472 then [] else (if i.val < 473 then [] else [index 835, index 851])) else (if i.val < 476 then (if i.val < 475 then [index 864, index 865, index 866, index 867, index 880, index 881, index 882, index 883] else [index 896, index 898, index 912, index 914]) else []))) else (if i.val < 486 then [] else (if i.val < 490 then (if i.val < 488 then [] else (if i.val < 489 then [index 299, index 315] else [index 330, index 331, index 346, index 347])) else (if i.val < 492 then (if i.val < 491 then [index 360, index 362, index 376, index 378] else []) else [])))) else (if i.val < 511 then (if i.val < 503 then (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then [] else [index 551, index 559, index 567, index 575]) else (if i.val < 498 then [index 582, index 583, index 590, index 591, index 598, index 599, index 606, index 607] else [index 612, index 614, index 620, index 622, index 628, index 630, index 636, index 638])) else (if i.val < 501 then (if i.val < 500 then [] else [index 673, index 677, index 681, index 685, index 689, index 693, index 697, index 701]) else (if i.val < 502 then [index 704, index 705, index 708, index 709, index 712, index 713, index 716, index 717, index 720, index 721, index 724, index 725, index 728, index 729, index 732, index 733] else []))) else (if i.val < 507 then (if i.val < 505 then (if i.val < 504 then [] else [index 803, index 819]) else (if i.val < 506 then [index 834, index 835, index 850, index 851] else [index 864, index 866, index 880, index 882])) else [])) else (if i.val < 519 then [] else (if i.val < 523 then (if i.val < 521 then (if i.val < 520 then [] else [index 299, index 315]) else (if i.val < 522 then [index 330, index 331, index 346, index 347] else [index 360, index 362, index 376, index 378])) else []))))))) else (if i.val < 792 then (if i.val < 660 then (if i.val < 594 then (if i.val < 561 then (if i.val < 544 then (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then [index 551, index 559, index 567, index 575] else [index 582, index 583, index 590, index 591, index 598, index 599, index 606, index 607]) else (if i.val < 531 then [index 612, index 614, index 620, index 622, index 628, index 630, index 636, index 638] else [])) else (if i.val < 534 then (if i.val < 533 then [index 673, index 677, index 681, index 685, index 689, index 693, index 697, index 701] else [index 704, index 705, index 708, index 709, index 712, index 713, index 716, index 717, index 720, index 721, index 724, index 725, index 728, index 729, index 732, index 733]) else [])) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then [index 803, index 819] else [index 834, index 835, index 850, index 851]) else (if i.val < 539 then [index 864, index 866, index 880, index 882] else [])) else [])) else (if i.val < 552 then (if i.val < 548 then [] else (if i.val < 550 then (if i.val < 549 then [] else [index 205, index 207, index 221, index 223]) else (if i.val < 551 then [index 236, index 237, index 252, index 253] else [index 268, index 284]))) else (if i.val < 556 then (if i.val < 554 then [] else (if i.val < 555 then [index 354, index 355, index 358, index 359, index 362, index 363, index 366, index 367, index 370, index 371, index 374, index 375, index 378, index 379, index 382, index 383] else [index 386, index 390, index 394, index 398, index 402, index 406, index 410, index 414])) else (if i.val < 558 then (if i.val < 557 then [] else [index 449, index 451, index 457, index 459, index 465, index 467, index 473, index 475]) else (if i.val < 559 then [index 480, index 481, index 488, index 489, index 496, index 497, index 504, index 505] else (if i.val < 560 then [index 512, index 520, index 528, index 536] else [])))))) else (if i.val < 577 then (if i.val < 569 then (if i.val < 565 then [] else (if i.val < 567 then (if i.val < 566 then [index 709, index 711, index 725, index 727] else [index 740, index 741, index 756, index 757]) else (if i.val < 568 then [index 772, index 788] else []))) else []) else (if i.val < 585 then (if i.val < 581 then [] else (if i.val < 583 then (if i.val < 582 then [index 205, index 207, index 221, index 223] else [index 236, index 237, index 252, index 253]) else (if i.val < 584 then [index 268, index 284] else []))) else (if i.val < 589 then (if i.val < 587 then (if i.val < 586 then [] else [index 354, index 355, index 358, index 359, index 362, index 363, index 366, index 367, index 370, index 371, index 374, index 375, index 378, index 379, index 382, index 383]) else (if i.val < 588 then [index 386, index 390, index 394, index 398, index 402, index 406, index 410, index 414] else [])) else (if i.val < 591 then (if i.val < 590 then [index 449, index 451, index 457, index 459, index 465, index 467, index 473, index 475] else [index 480, index 481, index 488, index 489, index 496, index 497, index 504, index 505]) else (if i.val < 592 then [index 512, index 520, index 528, index 536] else [])))))) else (if i.val < 627 then (if i.val < 610 then (if i.val < 602 then (if i.val < 598 then (if i.val < 596 then [] else (if i.val < 597 then [] else [index 709, index 711, index 725, index 727])) else (if i.val < 600 then (if i.val < 599 then [index 740, index 741, index 756, index 757] else [index 772, index 788]) else [])) else []) else (if i.val < 618 then (if i.val < 614 then (if i.val < 612 then [] else (if i.val < 613 then [index 173, index 175, index 189, index 191] else [index 204, index 205, index 206, index 207, index 220, index 221, index 222, index 223])) else (if i.val < 616 then (if i.val < 615 then [index 236, index 252] else []) else [])) else (if i.val < 622 then (if i.val < 620 then (if i.val < 619 then [index 354, index 358, index 362, index 366, index 370, index 374, index 378, index 382] else []) else (if i.val < 621 then [index 417, index 419, index 425, index 427, index 433, index 435, index 441, index 443] else [index 448, index 449, index 450, index 451, index 456, index 457, index 458, index 459, index 464, index 465, index 466, index 467, index 472, index 473, index 474, index 475])) else (if i.val < 624 then (if i.val < 623 then [index 480, index 488, index 496, index 504] else []) else [])))) else (if i.val < 643 then (if i.val < 635 then (if i.val < 631 then (if i.val < 629 then (if i.val < 628 then [] else [index 677, index 679, index 693, index 695]) else (if i.val < 630 then [index 708, index 709, index 710, index 711, index 724, index 725, index 726, index 727] else [index 740, index 756])) else []) else []) else (if i.val < 651 then (if i.val < 647 then (if i.val < 645 then (if i.val < 644 then [] else [index 173, index 175, index 189, index 191]) else (if i.val < 646 then [index 204, index 205, index 206, index 207, index 220, index 221, index 222, index 223] else [index 236, index 252])) else (if i.val < 649 then [] else (if i.val < 650 then [] else [index 354, index 358, index 362, index 366, index 370, index 374, index 378, index 382]))) else (if i.val < 655 then (if i.val < 653 then (if i.val < 652 then [] else [index 417, index 419, index 425, index 427, index 433, index 435, index 441, index 443]) else (if i.val < 654 then [index 448, index 449, index 450, index 451, index 456, index 457, index 458, index 459, index 464, index 465, index 466, index 467, index 472, index 473, index 474, index 475] else [index 480, index 488, index 496, index 504])) else []))))) else (if i.val < 726 then (if i.val < 693 then (if i.val < 676 then (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then (if i.val < 661 then [index 677, index 679, index 693, index 695] else [index 708, index 709, index 710, index 711, index 724, index 725, index 726, index 727]) else (if i.val < 663 then [index 740, index 756] else [])) else []) else []) else (if i.val < 684 then (if i.val < 680 then (if i.val < 678 then (if i.val < 677 then [] else [index 205, index 221]) else []) else (if i.val < 682 then (if i.val < 681 then [] else [index 323, index 327, index 331, index 335, index 339, index 343, index 347, index 351]) else (if i.val < 683 then [index 352, index 353, index 354, index 355, index 356, index 357, index 358, index 359, index 360, index 361, index 362, index 363, index 364, index 365, index 366, index 367, index 368, index 369, index 370, index 371, index 372, index 373, index 374, index 375, index 376, index 377, index 378, index 379, index 380, index 381, index 382, index 383] else [index 384, index 386, index 388, index 390, index 392, index 394, index 396, index 398, index 400, index 402, index 404, index 406, index 408, index 410, index 412, index 414]))) else (if i.val < 688 then (if i.val < 686 then (if i.val < 685 then [] else [index 449, index 457, index 465, index 473]) else []) else []))) else (if i.val < 709 then (if i.val < 701 then (if i.val < 697 then (if i.val < 695 then (if i.val < 694 then [index 709, index 725] else []) else []) else []) else []) else (if i.val < 717 then (if i.val < 713 then (if i.val < 711 then (if i.val < 710 then [index 205, index 221] else []) else []) else (if i.val < 715 then (if i.val < 714 then [index 323, index 327, index 331, index 335, index 339, index 343, index 347, index 351] else [index 352, index 353, index 354, index 355, index 356, index 357, index 358, index 359, index 360, index 361, index 362, index 363, index 364, index 365, index 366, index 367, index 368, index 369, index 370, index 371, index 372, index 373, index 374, index 375, index 376, index 377, index 378, index 379, index 380, index 381, index 382, index 383]) else (if i.val < 716 then [index 384, index 386, index 388, index 390, index 392, index 394, index 396, index 398, index 400, index 402, index 404, index 406, index 408, index 410, index 412, index 414] else []))) else (if i.val < 721 then (if i.val < 719 then (if i.val < 718 then [index 449, index 457, index 465, index 473] else []) else []) else (if i.val < 723 then [] else (if i.val < 724 then [] else (if i.val < 725 then [] else [index 709, index 725]))))))) else (if i.val < 759 then (if i.val < 742 then (if i.val < 734 then [] else (if i.val < 738 then [] else (if i.val < 740 then [] else (if i.val < 741 then [index 173, index 189] else [index 204, index 205, index 220, index 221])))) else (if i.val < 750 then (if i.val < 746 then (if i.val < 744 then [] else (if i.val < 745 then [index 291, index 295, index 299, index 303, index 307, index 311, index 315, index 319] else [index 322, index 323, index 326, index 327, index 330, index 331, index 334, index 335, index 338, index 339, index 342, index 343, index 346, index 347, index 350, index 351])) else (if i.val < 748 then (if i.val < 747 then [index 352, index 354, index 356, index 358, index 360, index 362, index 364, index 366, index 368, index 370, index 372, index 374, index 376, index 378, index 380, index 382] else []) else (if i.val < 749 then [index 417, index 425, index 433, index 441] else [index 448, index 449, index 456, index 457, index 464, index 465, index 472, index 473]))) else (if i.val < 754 then [] else (if i.val < 756 then [] else (if i.val < 757 then [index 677, index 693] else (if i.val < 758 then [index 708, index 709, index 724, index 725] else [])))))) else (if i.val < 775 then (if i.val < 767 then [] else (if i.val < 771 then [] else (if i.val < 773 then (if i.val < 772 then [] else [index 173, index 189]) else (if i.val < 774 then [index 204, index 205, index 220, index 221] else [])))) else (if i.val < 783 then (if i.val < 779 then (if i.val < 777 then (if i.val < 776 then [] else [index 291, index 295, index 299, index 303, index 307, index 311, index 315, index 319]) else (if i.val < 778 then [index 322, index 323, index 326, index 327, index 330, index 331, index 334, index 335, index 338, index 339, index 342, index 343, index 346, index 347, index 350, index 351] else [index 352, index 354, index 356, index 358, index 360, index 362, index 364, index 366, index 368, index 370, index 372, index 374, index 376, index 378, index 380, index 382])) else (if i.val < 781 then (if i.val < 780 then [] else [index 417, index 425, index 433, index 441]) else (if i.val < 782 then [index 448, index 449, index 456, index 457, index 464, index 465, index 472, index 473] else []))) else (if i.val < 787 then [] else (if i.val < 789 then (if i.val < 788 then [] else [index 677, index 693]) else (if i.val < 790 then [index 708, index 709, index 724, index 725] else [])))))))) else (if i.val < 924 then (if i.val < 858 then (if i.val < 825 then (if i.val < 808 then (if i.val < 800 then [] else (if i.val < 804 then (if i.val < 802 then [] else (if i.val < 803 then [index 110, index 111, index 126, index 127] else [index 142, index 158])) else (if i.val < 806 then (if i.val < 805 then [] else [index 201, index 203, index 205, index 207, index 217, index 219, index 221, index 223]) else (if i.val < 807 then [index 232, index 233, index 236, index 237, index 248, index 249, index 252, index 253] else [index 264, index 268, index 280, index 284])))) else (if i.val < 816 then (if i.val < 812 then (if i.val < 810 then [] else (if i.val < 811 then [index 354, index 355, index 362, index 363, index 370, index 371, index 378, index 379] else [index 386, index 394, index 402, index 410])) else []) else (if i.val < 820 then (if i.val < 818 then [] else (if i.val < 819 then [index 614, index 615, index 630, index 631] else [index 646, index 662])) else (if i.val < 822 then (if i.val < 821 then [] else [index 705, index 707, index 709, index 711, index 721, index 723, index 725, index 727]) else (if i.val < 823 then [index 736, index 737, index 740, index 741, index 752, index 753, index 756, index 757] else (if i.val < 824 then [index 768, index 772, index 784, index 788] else [])))))) else (if i.val < 841 then (if i.val < 833 then [] else (if i.val < 837 then (if i.val < 835 then (if i.val < 834 then [] else [index 110, index 111, index 126, index 127]) else (if i.val < 836 then [index 142, index 158] else [])) else (if i.val < 839 then (if i.val < 838 then [index 201, index 203, index 205, index 207, index 217, index 219, index 221, index 223] else [index 232, index 233, index 236, index 237, index 248, index 249, index 252, index 253]) else (if i.val < 840 then [index 264, index 268, index 280, index 284] else [])))) else (if i.val < 849 then (if i.val < 845 then (if i.val < 843 then (if i.val < 842 then [] else [index 354, index 355, index 362, index 363, index 370, index 371, index 378, index 379]) else (if i.val < 844 then [index 386, index 394, index 402, index 410] else [])) else []) else (if i.val < 853 then (if i.val < 851 then (if i.val < 850 then [] else [index 614, index 615, index 630, index 631]) else (if i.val < 852 then [index 646, index 662] else [])) else (if i.val < 855 then (if i.val < 854 then [index 705, index 707, index 709, index 711, index 721, index 723, index 725, index 727] else [index 736, index 737, index 740, index 741, index 752, index 753, index 756, index 757]) else (if i.val < 856 then [index 768, index 772, index 784, index 788] else [])))))) else (if i.val < 891 then (if i.val < 874 then (if i.val < 866 then [] else (if i.val < 870 then (if i.val < 868 then (if i.val < 867 then [index 110, index 126] else []) else (if i.val < 869 then [index 169, index 171, index 173, index 175, index 185, index 187, index 189, index 191] else [index 200, index 201, index 202, index 203, index 204, index 205, index 206, index 207, index 216, index 217, index 218, index 219, index 220, index 221, index 222, index 223])) else (if i.val < 872 then (if i.val < 871 then [index 232, index 236, index 248, index 252] else []) else []))) else (if i.val < 882 then (if i.val < 878 then (if i.val < 876 then (if i.val < 875 then [index 354, index 362, index 370, index 378] else []) else []) else []) else (if i.val < 886 then (if i.val < 884 then (if i.val < 883 then [index 614, index 630] else []) else (if i.val < 885 then [index 673, index 675, index 677, index 679, index 689, index 691, index 693, index 695] else [index 704, index 705, index 706, index 707, index 708, index 709, index 710, index 711, index 720, index 721, index 722, index 723, index 724, index 725, index 726, index 727])) else (if i.val < 888 then (if i.val < 887 then [index 736, index 740, index 752, index 756] else []) else [])))) else (if i.val < 907 then (if i.val < 899 then (if i.val < 895 then [] else (if i.val < 897 then [] else (if i.val < 898 then [] else [index 110, index 126]))) else (if i.val < 903 then (if i.val < 901 then (if i.val < 900 then [] else [index 169, index 171, index 173, index 175, index 185, index 187, index 189, index 191]) else (if i.val < 902 then [index 200, index 201, index 202, index 203, index 204, index 205, index 206, index 207, index 216, index 217, index 218, index 219, index 220, index 221, index 222, index 223] else [index 232, index 236, index 248, index 252])) else (if i.val < 905 then [] else (if i.val < 906 then [] else [index 354, index 362, index 370, index 378])))) else (if i.val < 915 then (if i.val < 911 then [] else (if i.val < 913 then [] else (if i.val < 914 then [] else [index 614, index 630]))) else (if i.val < 919 then (if i.val < 917 then (if i.val < 916 then [] else [index 673, index 675, index 677, index 679, index 689, index 691, index 693, index 695]) else (if i.val < 918 then [index 704, index 705, index 706, index 707, index 708, index 709, index 710, index 711, index 720, index 721, index 722, index 723, index 724, index 725, index 726, index 727] else [index 736, index 740, index 752, index 756])) else []))))) else (if i.val < 990 then (if i.val < 957 then (if i.val < 940 then (if i.val < 932 then (if i.val < 928 then [] else (if i.val < 930 then (if i.val < 929 then [] else [index 79, index 95]) else (if i.val < 931 then [index 108, index 109, index 110, index 111, index 124, index 125, index 126, index 127] else [index 140, index 142, index 156, index 158]))) else (if i.val < 936 then (if i.val < 934 then (if i.val < 933 then [] else [index 201, index 205, index 217, index 221]) else []) else (if i.val < 938 then (if i.val < 937 then [] else [index 323, index 331, index 339, index 347]) else (if i.val < 939 then [index 352, index 353, index 354, index 355, index 360, index 361, index 362, index 363, index 368, index 369, index 370, index 371, index 376, index 377, index 378, index 379] else [index 384, index 386, index 392, index 394, index 400, index 402, index 408, index 410])))) else (if i.val < 948 then (if i.val < 944 then [] else (if i.val < 946 then (if i.val < 945 then [] else [index 583, index 599]) else (if i.val < 947 then [index 612, index 613, index 614, index 615, index 628, index 629, index 630, index 631] else [index 644, index 646, index 660, index 662]))) else (if i.val < 952 then (if i.val < 950 then (if i.val < 949 then [] else [index 705, index 709, index 721, index 725]) else []) else []))) else (if i.val < 973 then (if i.val < 965 then (if i.val < 961 then [] else (if i.val < 963 then (if i.val < 962 then [index 79, index 95] else [index 108, index 109, index 110, index 111, index 124, index 125, index 126, index 127]) else (if i.val < 964 then [index 140, index 142, index 156, index 158] else []))) else (if i.val < 969 then (if i.val < 967 then (if i.val < 966 then [index 201, index 205, index 217, index 221] else []) else []) else (if i.val < 971 then (if i.val < 970 then [index 323, index 331, index 339, index 347] else [index 352, index 353, index 354, index 355, index 360, index 361, index 362, index 363, index 368, index 369, index 370, index 371, index 376, index 377, index 378, index 379]) else (if i.val < 972 then [index 384, index 386, index 392, index 394, index 400, index 402, index 408, index 410] else [])))) else (if i.val < 981 then (if i.val < 977 then [] else (if i.val < 979 then (if i.val < 978 then [index 583, index 599] else [index 612, index 613, index 614, index 615, index 628, index 629, index 630, index 631]) else (if i.val < 980 then [index 644, index 646, index 660, index 662] else []))) else (if i.val < 985 then (if i.val < 983 then (if i.val < 982 then [index 705, index 709, index 721, index 725] else []) else []) else [])))) else (if i.val < 1023 then (if i.val < 1006 then (if i.val < 998 then (if i.val < 994 then (if i.val < 992 then [] else (if i.val < 993 then [index 47, index 63] else [index 78, index 79, index 94, index 95])) else (if i.val < 996 then (if i.val < 995 then [index 108, index 110, index 124, index 126] else []) else (if i.val < 997 then [index 169, index 173, index 185, index 189] else [index 200, index 201, index 204, index 205, index 216, index 217, index 220, index 221]))) else (if i.val < 1002 then (if i.val < 1000 then [] else (if i.val < 1001 then [index 291, index 299, index 307, index 315] else [index 322, index 323, index 330, index 331, index 338, index 339, index 346, index 347])) else (if i.val < 1004 then (if i.val < 1003 then [index 352, index 354, index 360, index 362, index 368, index 370, index 376, index 378] else []) else []))) else (if i.val < 1014 then (if i.val < 1010 then (if i.val < 1008 then [] else (if i.val < 1009 then [index 551, index 567] else [index 582, index 583, index 598, index 599])) else (if i.val < 1012 then (if i.val < 1011 then [index 612, index 614, index 628, index 630] else []) else (if i.val < 1013 then [index 673, index 677, index 689, index 693] else [index 704, index 705, index 708, index 709, index 720, index 721, index 724, index 725]))) else [])) else (if i.val < 1039 then (if i.val < 1031 then (if i.val < 1027 then (if i.val < 1025 then (if i.val < 1024 then [] else [index 47, index 63]) else (if i.val < 1026 then [index 78, index 79, index 94, index 95] else [index 108, index 110, index 124, index 126])) else (if i.val < 1029 then (if i.val < 1028 then [] else [index 169, index 173, index 185, index 189]) else (if i.val < 1030 then [index 200, index 201, index 204, index 205, index 216, index 217, index 220, index 221] else []))) else (if i.val < 1035 then (if i.val < 1033 then (if i.val < 1032 then [] else [index 291, index 299, index 307, index 315]) else (if i.val < 1034 then [index 322, index 323, index 330, index 331, index 338, index 339, index 346, index 347] else [index 352, index 354, index 360, index 362, index 368, index 370, index 376, index 378])) else [])) else (if i.val < 1047 then (if i.val < 1043 then (if i.val < 1041 then (if i.val < 1040 then [] else [index 551, index 567]) else (if i.val < 1042 then [index 582, index 583, index 598, index 599] else [index 612, index 614, index 628, index 630])) else (if i.val < 1045 then (if i.val < 1044 then [] else [index 673, index 677, index 689, index 693]) else (if i.val < 1046 then [index 704, index 705, index 708, index 709, index 720, index 721, index 724, index 725] else []))) else [])))))))

def initial : List Index := [index 0, index 2, index 4, index 6, index 8, index 10, index 12, index 14, index 16, index 18, index 20, index 22, index 24, index 26, index 28, index 30]

def vectorClass (i : Index) : ℕ :=
  (if i.val < 528 then (if i.val < 264 then (if i.val < 132 then (if i.val < 66 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 8) else (if i.val < 3 then 16 else 7)) else (if i.val < 6 then (if i.val < 5 then 13 else 19) else (if i.val < 7 then 17 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 18) else (if i.val < 11 then 15 else 9)) else (if i.val < 14 then (if i.val < 13 then 12 else 20) else (if i.val < 15 then 14 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 14) else (if i.val < 19 then 20 else 12)) else (if i.val < 22 then (if i.val < 21 then 9 else 15) else (if i.val < 23 then 18 else 5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 17) else (if i.val < 27 then 19 else 13)) else (if i.val < 30 then (if i.val < 29 then 7 else 16) else (if i.val < 31 then 8 else (if i.val < 32 then 1 else 0)))))) else (if i.val < 49 then (if i.val < 41 then 0 else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 0 else 1) else (if i.val < 44 then 1 else 0)) else (if i.val < 47 then (if i.val < 46 then 3 else 6) else (if i.val < 48 then 1 else 0)))) else (if i.val < 57 then (if i.val < 53 then 0 else (if i.val < 55 then (if i.val < 54 then 2 else 11) else (if i.val < 56 then 2 else 0))) else (if i.val < 61 then (if i.val < 59 then (if i.val < 58 then 0 else 4) else (if i.val < 60 then 4 else 0)) else (if i.val < 63 then (if i.val < 62 then 7 else 8) else (if i.val < 64 then 1 else 0)))))) else (if i.val < 99 then (if i.val < 82 then (if i.val < 74 then 0 else (if i.val < 78 then (if i.val < 76 then 1 else (if i.val < 77 then 0 else 3)) else (if i.val < 80 then (if i.val < 79 then 6 else 1) else 0))) else (if i.val < 90 then (if i.val < 86 then (if i.val < 84 then 0 else (if i.val < 85 then 0 else 2)) else (if i.val < 88 then (if i.val < 87 then 11 else 2) else 0)) else (if i.val < 94 then (if i.val < 92 then 4 else (if i.val < 93 then 0 else 7)) else (if i.val < 96 then (if i.val < 95 then 8 else 1) else 0)))) else (if i.val < 115 then (if i.val < 107 then (if i.val < 103 then 0 else (if i.val < 105 then 0 else (if i.val < 106 then 0 else 1))) else (if i.val < 111 then (if i.val < 109 then (if i.val < 108 then 0 else 3) else (if i.val < 110 then 10 else 1)) else 0)) else (if i.val < 123 then (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then 0 else 2) else 2) else (if i.val < 121 then 0 else (if i.val < 122 then 0 else 4))) else (if i.val < 127 then (if i.val < 125 then (if i.val < 124 then 0 else 7) else (if i.val < 126 then 16 else 1)) else 0))))) else (if i.val < 198 then (if i.val < 165 then (if i.val < 148 then (if i.val < 140 then (if i.val < 136 then 0 else (if i.val < 138 then 0 else (if i.val < 139 then 1 else 0))) else (if i.val < 144 then (if i.val < 142 then (if i.val < 141 then 3 else 10) else (if i.val < 143 then 1 else 0)) else 0)) else (if i.val < 156 then (if i.val < 152 then (if i.val < 150 then 2 else (if i.val < 151 then 2 else 0)) else (if i.val < 154 then 0 else (if i.val < 155 then 4 else 0))) else (if i.val < 160 then (if i.val < 158 then (if i.val < 157 then 7 else 16) else (if i.val < 159 then 1 else 0)) else 0))) else (if i.val < 181 then (if i.val < 173 then (if i.val < 169 then 0 else (if i.val < 171 then 1 else (if i.val < 172 then 1 else 0))) else (if i.val < 177 then (if i.val < 175 then (if i.val < 174 then 1 else 0) else 0) else 0)) else (if i.val < 189 then (if i.val < 185 then (if i.val < 183 then (if i.val < 182 then 2 else 0) else 0) else (if i.val < 187 then (if i.val < 186 then 4 else 19) else (if i.val < 188 then 13 else 0))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then 1 else 0) else 0) else 0)))) else (if i.val < 231 then (if i.val < 214 then (if i.val < 206 then (if i.val < 202 then (if i.val < 200 then 0 else (if i.val < 201 then 0 else 1)) else (if i.val < 204 then 1 else (if i.val < 205 then 0 else 1))) else (if i.val < 210 then 0 else (if i.val < 212 then 0 else (if i.val < 213 then 0 else 2)))) else (if i.val < 222 then (if i.val < 218 then (if i.val < 216 then 0 else (if i.val < 217 then 0 else 4)) else (if i.val < 220 then (if i.val < 219 then 19 else 13) else (if i.val < 221 then 0 else 1))) else 0)) else (if i.val < 247 then (if i.val < 239 then (if i.val < 235 then (if i.val < 233 then (if i.val < 232 then 0 else 1) else (if i.val < 234 then 3 else 1)) else (if i.val < 237 then (if i.val < 236 then 0 else 1) else (if i.val < 238 then 1 else 0))) else (if i.val < 243 then 0 else (if i.val < 245 then (if i.val < 244 then 0 else 2) else (if i.val < 246 then 2 else 0)))) else (if i.val < 255 then (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then 0 else 4) else (if i.val < 250 then 17 else 13)) else (if i.val < 253 then (if i.val < 252 then 0 else 1) else (if i.val < 254 then 1 else 0))) else 0))))) else (if i.val < 396 then (if i.val < 330 then (if i.val < 297 then (if i.val < 280 then (if i.val < 272 then (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then 1 else 3) else (if i.val < 267 then 1 else 0)) else (if i.val < 270 then 1 else 0)) else (if i.val < 276 then 0 else (if i.val < 278 then 2 else 0))) else (if i.val < 288 then (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then 4 else 17) else (if i.val < 283 then 13 else 0)) else (if i.val < 286 then 1 else 0)) else 0)) else (if i.val < 313 then (if i.val < 305 then (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then 0 else 1) else (if i.val < 300 then 1 else 0)) else 0) else (if i.val < 309 then (if i.val < 307 then (if i.val < 306 then 0 else 2) else (if i.val < 308 then 2 else 0)) else (if i.val < 311 then (if i.val < 310 then 9 else 18) else (if i.val < 312 then 5 else 0)))) else (if i.val < 321 then (if i.val < 317 then (if i.val < 315 then (if i.val < 314 then 0 else 1) else (if i.val < 316 then 1 else 0)) else 0) else 0))) else (if i.val < 363 then (if i.val < 346 then (if i.val < 338 then (if i.val < 334 then (if i.val < 332 then 1 else 0) else 0) else (if i.val < 342 then (if i.val < 340 then 2 else (if i.val < 341 then 0 else 9)) else (if i.val < 344 then (if i.val < 343 then 18 else 5) else 0))) else (if i.val < 354 then (if i.val < 350 then (if i.val < 348 then 1 else 0) else 0) else (if i.val < 358 then 0 else (if i.val < 360 then 0 else (if i.val < 361 then 0 else (if i.val < 362 then 0 else 1)))))) else (if i.val < 379 then (if i.val < 371 then (if i.val < 367 then 0 else (if i.val < 369 then 0 else (if i.val < 370 then 0 else 2))) else (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then 0 else 9) else (if i.val < 374 then 15 else 5)) else (if i.val < 377 then 0 else (if i.val < 378 then 0 else 1)))) else (if i.val < 387 then 0 else (if i.val < 391 then 0 else (if i.val < 393 then 0 else (if i.val < 394 then 0 else (if i.val < 395 then 1 else 0)))))))) else (if i.val < 462 then (if i.val < 429 then (if i.val < 412 then (if i.val < 404 then (if i.val < 400 then 0 else (if i.val < 402 then 0 else (if i.val < 403 then 2 else 0))) else (if i.val < 408 then (if i.val < 406 then (if i.val < 405 then 9 else 15) else (if i.val < 407 then 5 else 0)) else (if i.val < 410 then 0 else (if i.val < 411 then 1 else 0)))) else (if i.val < 420 then 0 else (if i.val < 424 then 0 else (if i.val < 426 then (if i.val < 425 then 0 else 1) else (if i.val < 427 then 1 else (if i.val < 428 then 1 else 0)))))) else (if i.val < 445 then (if i.val < 437 then (if i.val < 433 then 0 else (if i.val < 435 then (if i.val < 434 then 2 else 20) else (if i.val < 436 then 12 else 0))) else (if i.val < 441 then (if i.val < 439 then (if i.val < 438 then 5 else 0) else 0) else (if i.val < 443 then 1 else (if i.val < 444 then 1 else 0)))) else (if i.val < 453 then 0 else (if i.val < 457 then 0 else (if i.val < 459 then 1 else (if i.val < 460 then 1 else 0)))))) else (if i.val < 495 then (if i.val < 478 then (if i.val < 470 then (if i.val < 466 then (if i.val < 464 then 0 else (if i.val < 465 then 0 else 2)) else (if i.val < 468 then (if i.val < 467 then 20 else 12) else (if i.val < 469 then 0 else 5))) else (if i.val < 474 then (if i.val < 472 then 0 else (if i.val < 473 then 0 else 1)) else (if i.val < 476 then 1 else 0))) else (if i.val < 486 then 0 else (if i.val < 490 then (if i.val < 488 then 0 else (if i.val < 489 then 1 else 3)) else (if i.val < 492 then (if i.val < 491 then 1 else 0) else 0)))) else (if i.val < 511 then (if i.val < 503 then (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then 0 else 2) else (if i.val < 498 then 14 else 12)) else (if i.val < 501 then (if i.val < 500 then 0 else 5) else (if i.val < 502 then 5 else 0))) else (if i.val < 507 then (if i.val < 505 then (if i.val < 504 then 0 else 1) else (if i.val < 506 then 3 else 1)) else 0)) else (if i.val < 519 then 0 else (if i.val < 523 then (if i.val < 521 then (if i.val < 520 then 0 else 1) else (if i.val < 522 then 3 else 1)) else 0))))))) else (if i.val < 792 then (if i.val < 660 then (if i.val < 594 then (if i.val < 561 then (if i.val < 544 then (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then 2 else 14) else (if i.val < 531 then 12 else 0)) else (if i.val < 534 then 5 else 0)) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then 1 else 3) else (if i.val < 539 then 1 else 0)) else 0)) else (if i.val < 552 then (if i.val < 548 then 0 else (if i.val < 550 then (if i.val < 549 then 0 else 1) else (if i.val < 551 then 3 else 1))) else (if i.val < 556 then (if i.val < 554 then 0 else 5) else (if i.val < 558 then (if i.val < 557 then 0 else 12) else (if i.val < 559 then 14 else (if i.val < 560 then 2 else 0)))))) else (if i.val < 577 then (if i.val < 569 then (if i.val < 565 then 0 else (if i.val < 567 then (if i.val < 566 then 1 else 3) else (if i.val < 568 then 1 else 0))) else 0) else (if i.val < 585 then (if i.val < 581 then 0 else (if i.val < 583 then (if i.val < 582 then 1 else 3) else (if i.val < 584 then 1 else 0))) else (if i.val < 589 then (if i.val < 587 then (if i.val < 586 then 0 else 5) else (if i.val < 588 then 5 else 0)) else (if i.val < 591 then (if i.val < 590 then 12 else 14) else (if i.val < 592 then 2 else 0)))))) else (if i.val < 627 then (if i.val < 610 then (if i.val < 602 then (if i.val < 598 then (if i.val < 596 then 0 else (if i.val < 597 then 0 else 1)) else (if i.val < 600 then (if i.val < 599 then 3 else 1) else 0)) else 0) else (if i.val < 618 then (if i.val < 614 then (if i.val < 612 then 0 else 1) else (if i.val < 616 then (if i.val < 615 then 1 else 0) else 0)) else (if i.val < 622 then (if i.val < 620 then (if i.val < 619 then 5 else 0) else (if i.val < 621 then 12 else 20)) else (if i.val < 624 then (if i.val < 623 then 2 else 0) else 0)))) else (if i.val < 643 then (if i.val < 635 then (if i.val < 631 then (if i.val < 629 then (if i.val < 628 then 0 else 1) else 1) else 0) else 0) else (if i.val < 651 then (if i.val < 647 then (if i.val < 645 then (if i.val < 644 then 0 else 1) else 1) else (if i.val < 649 then 0 else (if i.val < 650 then 0 else 5))) else (if i.val < 655 then (if i.val < 653 then (if i.val < 652 then 0 else 12) else (if i.val < 654 then 20 else 2)) else 0))))) else (if i.val < 726 then (if i.val < 693 then (if i.val < 676 then (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then 1 else (if i.val < 663 then 1 else 0)) else 0) else 0) else (if i.val < 684 then (if i.val < 680 then (if i.val < 678 then (if i.val < 677 then 0 else 1) else 0) else (if i.val < 682 then (if i.val < 681 then 0 else 5) else (if i.val < 683 then 15 else 9))) else (if i.val < 688 then (if i.val < 686 then (if i.val < 685 then 0 else 2) else 0) else 0))) else (if i.val < 709 then (if i.val < 701 then (if i.val < 697 then (if i.val < 695 then (if i.val < 694 then 1 else 0) else 0) else 0) else 0) else (if i.val < 717 then (if i.val < 713 then (if i.val < 711 then (if i.val < 710 then 1 else 0) else 0) else (if i.val < 715 then (if i.val < 714 then 5 else 15) else (if i.val < 716 then 9 else 0))) else (if i.val < 721 then (if i.val < 719 then (if i.val < 718 then 2 else 0) else 0) else (if i.val < 723 then 0 else (if i.val < 724 then 0 else (if i.val < 725 then 0 else 1))))))) else (if i.val < 759 then (if i.val < 742 then (if i.val < 734 then 0 else (if i.val < 738 then 0 else (if i.val < 740 then 0 else 1))) else (if i.val < 750 then (if i.val < 746 then (if i.val < 744 then 0 else (if i.val < 745 then 5 else 18)) else (if i.val < 748 then (if i.val < 747 then 9 else 0) else 2)) else (if i.val < 754 then 0 else (if i.val < 756 then 0 else (if i.val < 757 then 1 else (if i.val < 758 then 1 else 0)))))) else (if i.val < 775 then (if i.val < 767 then 0 else (if i.val < 771 then 0 else (if i.val < 773 then (if i.val < 772 then 0 else 1) else (if i.val < 774 then 1 else 0)))) else (if i.val < 783 then (if i.val < 779 then (if i.val < 777 then (if i.val < 776 then 0 else 5) else (if i.val < 778 then 18 else 9)) else (if i.val < 781 then (if i.val < 780 then 0 else 2) else (if i.val < 782 then 2 else 0))) else (if i.val < 787 then 0 else (if i.val < 789 then (if i.val < 788 then 0 else 1) else (if i.val < 790 then 1 else 0)))))))) else (if i.val < 924 then (if i.val < 858 then (if i.val < 825 then (if i.val < 808 then (if i.val < 800 then 0 else (if i.val < 804 then (if i.val < 802 then 0 else 1) else (if i.val < 806 then (if i.val < 805 then 0 else 13) else (if i.val < 807 then 17 else 4)))) else (if i.val < 816 then (if i.val < 812 then (if i.val < 810 then 0 else 2) else 0) else (if i.val < 820 then (if i.val < 818 then 0 else 1) else (if i.val < 822 then (if i.val < 821 then 0 else 1) else (if i.val < 823 then 3 else (if i.val < 824 then 1 else 0)))))) else (if i.val < 841 then (if i.val < 833 then 0 else (if i.val < 837 then (if i.val < 835 then (if i.val < 834 then 0 else 1) else (if i.val < 836 then 1 else 0)) else (if i.val < 839 then (if i.val < 838 then 13 else 17) else (if i.val < 840 then 4 else 0)))) else (if i.val < 849 then (if i.val < 845 then (if i.val < 843 then (if i.val < 842 then 0 else 2) else (if i.val < 844 then 2 else 0)) else 0) else (if i.val < 853 then (if i.val < 851 then (if i.val < 850 then 0 else 1) else (if i.val < 852 then 1 else 0)) else (if i.val < 855 then (if i.val < 854 then 1 else 3) else (if i.val < 856 then 1 else 0)))))) else (if i.val < 891 then (if i.val < 874 then (if i.val < 866 then 0 else (if i.val < 870 then (if i.val < 868 then (if i.val < 867 then 1 else 0) else (if i.val < 869 then 13 else 19)) else (if i.val < 872 then (if i.val < 871 then 4 else 0) else 0))) else (if i.val < 882 then (if i.val < 878 then (if i.val < 876 then (if i.val < 875 then 2 else 0) else 0) else 0) else (if i.val < 886 then (if i.val < 884 then (if i.val < 883 then 1 else 0) else 1) else (if i.val < 888 then (if i.val < 887 then 1 else 0) else 0)))) else (if i.val < 907 then (if i.val < 899 then (if i.val < 895 then 0 else (if i.val < 897 then 0 else (if i.val < 898 then 0 else 1))) else (if i.val < 903 then (if i.val < 901 then (if i.val < 900 then 0 else 13) else (if i.val < 902 then 19 else 4)) else (if i.val < 905 then 0 else (if i.val < 906 then 0 else 2)))) else (if i.val < 915 then (if i.val < 911 then 0 else (if i.val < 913 then 0 else (if i.val < 914 then 0 else 1))) else (if i.val < 919 then (if i.val < 917 then (if i.val < 916 then 0 else 1) else 1) else 0))))) else (if i.val < 990 then (if i.val < 957 then (if i.val < 940 then (if i.val < 932 then (if i.val < 928 then 0 else (if i.val < 930 then (if i.val < 929 then 0 else 1) else (if i.val < 931 then 16 else 7))) else (if i.val < 936 then (if i.val < 934 then (if i.val < 933 then 0 else 4) else 0) else (if i.val < 938 then (if i.val < 937 then 0 else 2) else 2))) else (if i.val < 948 then (if i.val < 944 then 0 else (if i.val < 946 then (if i.val < 945 then 0 else 1) else (if i.val < 947 then 10 else 3))) else (if i.val < 952 then (if i.val < 950 then (if i.val < 949 then 0 else 1) else 0) else 0))) else (if i.val < 973 then (if i.val < 965 then (if i.val < 961 then 0 else (if i.val < 963 then (if i.val < 962 then 1 else 16) else (if i.val < 964 then 7 else 0))) else (if i.val < 969 then (if i.val < 967 then (if i.val < 966 then 4 else 0) else 0) else (if i.val < 971 then 2 else (if i.val < 972 then 2 else 0)))) else (if i.val < 981 then (if i.val < 977 then 0 else (if i.val < 979 then (if i.val < 978 then 1 else 10) else (if i.val < 980 then 3 else 0))) else (if i.val < 985 then (if i.val < 983 then (if i.val < 982 then 1 else 0) else 0) else 0)))) else (if i.val < 1023 then (if i.val < 1006 then (if i.val < 998 then (if i.val < 994 then (if i.val < 992 then 0 else (if i.val < 993 then 1 else 8)) else (if i.val < 996 then (if i.val < 995 then 7 else 0) else 4)) else (if i.val < 1002 then (if i.val < 1000 then 0 else (if i.val < 1001 then 2 else 11)) else (if i.val < 1004 then (if i.val < 1003 then 2 else 0) else 0))) else (if i.val < 1014 then (if i.val < 1010 then (if i.val < 1008 then 0 else (if i.val < 1009 then 1 else 6)) else (if i.val < 1012 then (if i.val < 1011 then 3 else 0) else 1)) else 0)) else (if i.val < 1039 then (if i.val < 1031 then (if i.val < 1027 then (if i.val < 1025 then (if i.val < 1024 then 0 else 1) else (if i.val < 1026 then 8 else 7)) else (if i.val < 1029 then (if i.val < 1028 then 0 else 4) else (if i.val < 1030 then 4 else 0))) else (if i.val < 1035 then (if i.val < 1033 then (if i.val < 1032 then 0 else 2) else (if i.val < 1034 then 11 else 2)) else 0)) else (if i.val < 1047 then (if i.val < 1043 then (if i.val < 1041 then (if i.val < 1040 then 0 else 1) else (if i.val < 1042 then 6 else 3)) else (if i.val < 1045 then (if i.val < 1044 then 0 else 1) else (if i.val < 1046 then 1 else 0))) else 0)))))))

def value0 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 1) else 1) else 1) else 1)

def v0 (i : Index) : ℕ := value0 (vectorClass i)

def value1 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 2) else (if c < 3 then 3 else 4)) else (if c < 7 then 4 else (if c < 8 then 4 else (if c < 9 then 4 else 5)))) else (if c < 15 then 6 else (if c < 18 then (if c < 16 then 6 else (if c < 17 then 6 else 8)) else (if c < 19 then 8 else (if c < 20 then 8 else 9)))))

def v1 (i : Index) : ℕ := value1 (vectorClass i)

def value2 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 4) else (if c < 3 then 7 else (if c < 4 then 8 else 10))) else (if c < 7 then (if c < 6 then 11 else 12) else (if c < 8 then 12 else (if c < 9 then 12 else 16)))) else (if c < 15 then (if c < 12 then (if c < 11 then 12 else 14) else (if c < 13 then 17 else (if c < 14 then 18 else 21))) else (if c < 18 then (if c < 16 then 22 else (if c < 17 then 24 else 26)) else (if c < 19 then 26 else (if c < 20 then 28 else 30)))))

def v2 (i : Index) : ℕ := value2 (vectorClass i)

def value3 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 8) else (if c < 3 then 15 else (if c < 4 then 16 else 22))) else (if c < 7 then (if c < 6 then 26 else 24) else (if c < 8 then 28 else (if c < 9 then 32 else 42)))) else (if c < 15 then (if c < 12 then (if c < 11 then 24 else 30) else (if c < 13 then 40 else (if c < 14 then 44 else 52))) else (if c < 18 then 64 else (if c < 19 then 67 else (if c < 20 then 76 else 78)))))

def v3 (i : Index) : ℕ := value3 (vectorClass i)

def value4 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 16) else (if c < 3 then 31 else (if c < 4 then 32 else 46))) else (if c < 7 then (if c < 6 then 57 else 48) else (if c < 8 then 60 else (if c < 9 then 72 else 99)))) else (if c < 15 then (if c < 12 then (if c < 11 then 48 else 62) else (if c < 13 then 87 else (if c < 14 then 98 else 115))) else (if c < 18 then (if c < 16 then 163 else (if c < 17 then 148 else 142)) else (if c < 19 then 155 else (if c < 20 then 182 else 181)))))

def v4 (i : Index) : ℕ := value4 (vectorClass i)

def value5 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 32) else (if c < 3 then 63 else (if c < 4 then 64 else 94))) else (if c < 7 then (if c < 6 then 120 else 96) else (if c < 8 then 124 else (if c < 9 then 152 else 219)))) else (if c < 15 then (if c < 12 then (if c < 11 then 96 else 126) else (if c < 13 then 182 else (if c < 14 then 208 else 242))) else (if c < 18 then (if c < 16 then 382 else (if c < 17 then 320 else 300)) else (if c < 19 then 338 else (if c < 20 then 406 else 395)))))

def v5 (i : Index) : ℕ := value5 (vectorClass i)

def value6 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 64) else (if c < 3 then 127 else (if c < 4 then 128 else 190))) else (if c < 7 then (if c < 6 then 247 else 192) else (if c < 8 then 252 else (if c < 9 then 312 else 466)))) else (if c < 15 then (if c < 12 then (if c < 11 then 192 else 254) else (if c < 13 then 373 else (if c < 14 then 430 else 497))) else (if c < 18 then (if c < 16 then 848 else (if c < 17 then 668 else 618)) else (if c < 19 then 712 else (if c < 20 then 868 else 832)))))

def v6 (i : Index) : ℕ := value6 (vectorClass i)

def value7 (c : ℕ) : ℕ :=
  (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0 else 128) else (if c < 3 then 255 else (if c < 4 then 256 else 382))) else (if c < 7 then (if c < 6 then 502 else 384) else (if c < 8 then 508 else (if c < 9 then 632 else 968)))) else (if c < 15 then (if c < 12 then (if c < 11 then 384 else 510) else (if c < 13 then 756 else (if c < 14 then 876 else 1008))) else (if c < 18 then (if c < 16 then 1816 else (if c < 17 then 1368 else 1256)) else (if c < 19 then 1469 else (if c < 20 then 1808 else 1716)))))

def v7 (i : Index) : ℕ := value7 (vectorClass i)

def accepted : Index → ℕ := v0

def vector (k : Fin 8) : Index → ℕ :=
  match k.val with
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | 3 => v3
  | 4 => v4
  | 5 => v5
  | 6 => v6
  | _ => v7

end A208640Table

namespace A208640Table
open A208640Proof

def nextIndex (i : Index) (r : Fin 32) : Index :=
  ⟨(i.val % 32 + 1) * 32 + r.val, by
    have hi := Nat.mod_lt i.val (by decide : 0 < 32)
    omega⟩

theorem state_nextIndex (i : Index) (r : Fin 32) :
    state (nextIndex i r) = (some (state i).2, decode r) := by
  have hdiv : (nextIndex i r).val / 32 = i.val % 32 + 1 := by
    dsimp [nextIndex]
    omega
  have hmod : (nextIndex i r).val % 32 = r.val := by
    dsimp [nextIndex]
    omega
  have hn : i.val % 32 + 1 ≠ 0 := by omega
  simp only [state, hdiv, hmod, hn, ↓reduceIte, Nat.add_sub_cancel_right]

def rawStep (i : Index) (r : Fin 32) : Option Index :=
  if localOK (state i).1 (state i).2 (some (decode r)) then
    some (nextIndex i r) else none

theorem rawStep_correct (i : Index) (r : Fin 32) :
    (rawStep i r).map state = step (state i) (decode r) := by
  by_cases h : localOK (state i).1 (state i).2 (some (decode r))
  · simp [rawStep, step, h, state_nextIndex]
  · simp [rawStep, step, h]

def rawSuccessors (i : Index) : List Index :=
  (List.finRange 32).filterMap (rawStep i)

theorem rawSuccessors_correct (i : Index) :
    allCols.filterMap (step (state i)) = (rawSuccessors i).map state := by
  simp only [allCols, List.ofFn_eq_map, List.filterMap_map,
    rawSuccessors, List.map_filterMap]
  congr 1
  funext r
  exact (rawStep_correct i r).symm

end A208640Table

namespace A208640Table
open A208640Proof

def Certified (i : Index) : Prop :=
  rawSuccessors i = succ i ∧
  (if accept (state i) then 1 else 0) = accepted i ∧
  (∀ k : Fin 7, ((succ i).map (vector k.castSucc)).sum = vector k.succ i) ∧
  v7 i + 14 * v5 i + 9 * v3 i = 6 * v6 i + 16 * v4 i + 2 * v2 i

instance (i : Index) : Decidable (Certified i) := by unfold Certified; infer_instance

def Block (k : Fin 132) : Prop := ∀ j : Fin 8, Certified (index (8 * k.val + j.val))

instance (k : Fin 132) : Decidable (Block k) := by unfold Block; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certified_blocks : ∀ k : Fin 132, Block k := by
  have b0 : Block 0 := by decide +kernel
  have b1 : Block 1 := by decide +kernel
  have b2 : Block 2 := by decide +kernel
  have b3 : Block 3 := by decide +kernel
  have b4 : Block 4 := by decide +kernel
  have b5 : Block 5 := by decide +kernel
  have b6 : Block 6 := by decide +kernel
  have b7 : Block 7 := by decide +kernel
  have b8 : Block 8 := by decide +kernel
  have b9 : Block 9 := by decide +kernel
  have b10 : Block 10 := by decide +kernel
  have b11 : Block 11 := by decide +kernel
  have b12 : Block 12 := by decide +kernel
  have b13 : Block 13 := by decide +kernel
  have b14 : Block 14 := by decide +kernel
  have b15 : Block 15 := by decide +kernel
  have b16 : Block 16 := by decide +kernel
  have b17 : Block 17 := by decide +kernel
  have b18 : Block 18 := by decide +kernel
  have b19 : Block 19 := by decide +kernel
  have b20 : Block 20 := by decide +kernel
  have b21 : Block 21 := by decide +kernel
  have b22 : Block 22 := by decide +kernel
  have b23 : Block 23 := by decide +kernel
  have b24 : Block 24 := by decide +kernel
  have b25 : Block 25 := by decide +kernel
  have b26 : Block 26 := by decide +kernel
  have b27 : Block 27 := by decide +kernel
  have b28 : Block 28 := by decide +kernel
  have b29 : Block 29 := by decide +kernel
  have b30 : Block 30 := by decide +kernel
  have b31 : Block 31 := by decide +kernel
  have b32 : Block 32 := by decide +kernel
  have b33 : Block 33 := by decide +kernel
  have b34 : Block 34 := by decide +kernel
  have b35 : Block 35 := by decide +kernel
  have b36 : Block 36 := by decide +kernel
  have b37 : Block 37 := by decide +kernel
  have b38 : Block 38 := by decide +kernel
  have b39 : Block 39 := by decide +kernel
  have b40 : Block 40 := by decide +kernel
  have b41 : Block 41 := by decide +kernel
  have b42 : Block 42 := by decide +kernel
  have b43 : Block 43 := by decide +kernel
  have b44 : Block 44 := by decide +kernel
  have b45 : Block 45 := by decide +kernel
  have b46 : Block 46 := by decide +kernel
  have b47 : Block 47 := by decide +kernel
  have b48 : Block 48 := by decide +kernel
  have b49 : Block 49 := by decide +kernel
  have b50 : Block 50 := by decide +kernel
  have b51 : Block 51 := by decide +kernel
  have b52 : Block 52 := by decide +kernel
  have b53 : Block 53 := by decide +kernel
  have b54 : Block 54 := by decide +kernel
  have b55 : Block 55 := by decide +kernel
  have b56 : Block 56 := by decide +kernel
  have b57 : Block 57 := by decide +kernel
  have b58 : Block 58 := by decide +kernel
  have b59 : Block 59 := by decide +kernel
  have b60 : Block 60 := by decide +kernel
  have b61 : Block 61 := by decide +kernel
  have b62 : Block 62 := by decide +kernel
  have b63 : Block 63 := by decide +kernel
  have b64 : Block 64 := by decide +kernel
  have b65 : Block 65 := by decide +kernel
  have b66 : Block 66 := by decide +kernel
  have b67 : Block 67 := by decide +kernel
  have b68 : Block 68 := by decide +kernel
  have b69 : Block 69 := by decide +kernel
  have b70 : Block 70 := by decide +kernel
  have b71 : Block 71 := by decide +kernel
  have b72 : Block 72 := by decide +kernel
  have b73 : Block 73 := by decide +kernel
  have b74 : Block 74 := by decide +kernel
  have b75 : Block 75 := by decide +kernel
  have b76 : Block 76 := by decide +kernel
  have b77 : Block 77 := by decide +kernel
  have b78 : Block 78 := by decide +kernel
  have b79 : Block 79 := by decide +kernel
  have b80 : Block 80 := by decide +kernel
  have b81 : Block 81 := by decide +kernel
  have b82 : Block 82 := by decide +kernel
  have b83 : Block 83 := by decide +kernel
  have b84 : Block 84 := by decide +kernel
  have b85 : Block 85 := by decide +kernel
  have b86 : Block 86 := by decide +kernel
  have b87 : Block 87 := by decide +kernel
  have b88 : Block 88 := by decide +kernel
  have b89 : Block 89 := by decide +kernel
  have b90 : Block 90 := by decide +kernel
  have b91 : Block 91 := by decide +kernel
  have b92 : Block 92 := by decide +kernel
  have b93 : Block 93 := by decide +kernel
  have b94 : Block 94 := by decide +kernel
  have b95 : Block 95 := by decide +kernel
  have b96 : Block 96 := by decide +kernel
  have b97 : Block 97 := by decide +kernel
  have b98 : Block 98 := by decide +kernel
  have b99 : Block 99 := by decide +kernel
  have b100 : Block 100 := by decide +kernel
  have b101 : Block 101 := by decide +kernel
  have b102 : Block 102 := by decide +kernel
  have b103 : Block 103 := by decide +kernel
  have b104 : Block 104 := by decide +kernel
  have b105 : Block 105 := by decide +kernel
  have b106 : Block 106 := by decide +kernel
  have b107 : Block 107 := by decide +kernel
  have b108 : Block 108 := by decide +kernel
  have b109 : Block 109 := by decide +kernel
  have b110 : Block 110 := by decide +kernel
  have b111 : Block 111 := by decide +kernel
  have b112 : Block 112 := by decide +kernel
  have b113 : Block 113 := by decide +kernel
  have b114 : Block 114 := by decide +kernel
  have b115 : Block 115 := by decide +kernel
  have b116 : Block 116 := by decide +kernel
  have b117 : Block 117 := by decide +kernel
  have b118 : Block 118 := by decide +kernel
  have b119 : Block 119 := by decide +kernel
  have b120 : Block 120 := by decide +kernel
  have b121 : Block 121 := by decide +kernel
  have b122 : Block 122 := by decide +kernel
  have b123 : Block 123 := by decide +kernel
  have b124 : Block 124 := by decide +kernel
  have b125 : Block 125 := by decide +kernel
  have b126 : Block 126 := by decide +kernel
  have b127 : Block 127 := by decide +kernel
  have b128 : Block 128 := by decide +kernel
  have b129 : Block 129 := by decide +kernel
  have b130 : Block 130 := by decide +kernel
  have b131 : Block 131 := by decide +kernel
  intro k
  fin_cases k <;> assumption

theorem certified (i : Index) : Certified i := by
  have h := certified_blocks ⟨i.val / 8, by omega⟩ ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : index (8 * (i.val / 8) + i.val % 8) = i := by
    apply Fin.ext; dsimp [index]; omega
  simpa only [he] using h

theorem step_table (i : Index) :
    allCols.filterMap (step (state i)) = (succ i).map state :=
  (rawSuccessors_correct i).trans (congrArg (List.map state) (certified i).1)

theorem accept_table (i : Index) :
    (if accept (state i) then 1 else 0) = accepted i := (certified i).2.1

theorem vector_next (k : Fin 7) (i : Index) :
    ((succ i).map (vector k.castSucc)).sum = vector k.succ i := (certified i).2.2.1 k

theorem vector_balance (i : Index) :
    v7 i + 14 * v5 i + 9 * v3 i = 6 * v6 i + 16 * v4 i + 2 * v2 i :=
  (certified i).2.2.2

theorem initial_table : initialStates = initial.map state := by decide +kernel

end A208640Table

namespace A208640Table
open A208640Count

def indexedCount (n : ℕ) : ℕ := (initial.map (paths succ accepted n)).sum

theorem paths_vector (k : Fin 8) (i : Index) :
    paths succ accepted k.val i = vector k i :=
  paths_eq_vectors succ accepted vector (fun _ => rfl) vector_next k i

theorem paths_base (i : Index) :
    paths succ accepted 7 i + 14 * paths succ accepted 5 i + 9 * paths succ accepted 3 i =
    6 * paths succ accepted 6 i + 16 * paths succ accepted 4 i + 2 * paths succ accepted 2 i := by
  rw [paths_vector (⟨7, by decide⟩ : Fin 8), paths_vector (⟨5, by decide⟩ : Fin 8), paths_vector (⟨3, by decide⟩ : Fin 8),
    paths_vector (⟨6, by decide⟩ : Fin 8), paths_vector (⟨4, by decide⟩ : Fin 8), paths_vector (⟨2, by decide⟩ : Fin 8)]
  exact vector_balance i

theorem indexed_recurrence (n : ℕ) :
    indexedCount (n + 7) + 14 * indexedCount (n + 5) + 9 * indexedCount (n + 3) =
      6 * indexedCount (n + 6) + 16 * indexedCount (n + 4) + 2 * indexedCount (n + 2) :=
  sum_balance initial (paths succ accepted (n + 2))
    (paths succ accepted (n + 3)) (paths succ accepted (n + 4))
    (paths succ accepted (n + 5)) (paths succ accepted (n + 6))
    (paths succ accepted (n + 7))
    (paths_recurrence succ accepted paths_base n)

theorem vector_initial_values :
    (initial.map v0).sum = 16 ∧ (initial.map v1).sum = 89 ∧
    (initial.map v2).sum = 284 ∧ (initial.map v3).sum = 722 ∧
    (initial.map v4).sum = 1652 ∧ (initial.map v5).sum = 3577 ∧
    (initial.map v6).sum = 7504 := by
  decide +kernel

theorem indexedCount_vector (k : Fin 8) :
    indexedCount k.val = (initial.map (vector k)).sum := by
  unfold indexedCount
  rw [show paths succ accepted k.val = vector k from funext (paths_vector k)]

theorem indexed_initial_values :
    indexedCount 0 = 16 ∧ indexedCount 1 = 89 ∧ indexedCount 2 = 284 ∧
    indexedCount 3 = 722 ∧ indexedCount 4 = 1652 ∧ indexedCount 5 = 3577 ∧
    indexedCount 6 = 7504 := by
  rw [indexedCount_vector (⟨0, by decide⟩ : Fin 8), indexedCount_vector (⟨1, by decide⟩ : Fin 8),
    indexedCount_vector (⟨2, by decide⟩ : Fin 8), indexedCount_vector (⟨3, by decide⟩ : Fin 8),
    indexedCount_vector (⟨4, by decide⟩ : Fin 8), indexedCount_vector (⟨5, by decide⟩ : Fin 8),
    indexedCount_vector (⟨6, by decide⟩ : Fin 8)]
  exact vector_initial_values

end A208640Table

namespace A208640Proof

open OMA.S_oeis_a208640

theorem a_succ_eq_indexedCount (n : ℕ) : a (n + 1) = A208640Table.indexedCount n := by
  rw [a_succ_eq_initialStates, A208640Table.initial_table, List.map_map]
  change (A208640Table.initial.map
    (fun i => suffixCount (A208640Table.state i) n)).sum = _
  rw [show (fun i => suffixCount (A208640Table.state i) n) =
      A208640Count.paths A208640Table.succ A208640Table.accepted n from
    funext (suffixCount_eq_paths A208640Table.state A208640Table.succ
      A208640Table.accepted A208640Table.step_table A208640Table.accept_table n)]
  rfl

theorem a_initial_values :
    a 1 = 16 ∧ a 2 = 89 ∧ a 3 = 284 ∧ a 4 = 722 ∧
    a 5 = 1652 ∧ a 6 = 3577 ∧ a 7 = 7504 := by
  rw [a_succ_eq_indexedCount 0, a_succ_eq_indexedCount 1, a_succ_eq_indexedCount 2,
    a_succ_eq_indexedCount 3, a_succ_eq_indexedCount 4, a_succ_eq_indexedCount 5,
    a_succ_eq_indexedCount 6]
  exact A208640Table.indexed_initial_values

theorem a_recurrence (n : ℕ) (hn : 3 ≤ n) :
    a (n + 5) + 14 * a (n + 3) + 9 * a (n + 1) =
      6 * a (n + 4) + 16 * a (n + 2) + 2 * a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := A208640Table.indexed_recurrence k
  simpa only [show 3 + k + 5 = (k + 7) + 1 by omega,
    show 3 + k + 3 = (k + 5) + 1 by omega,
    show 3 + k + 1 = (k + 3) + 1 by omega,
    show 3 + k + 4 = (k + 6) + 1 by omega,
    show 3 + k + 2 = (k + 4) + 1 by omega,
    show 3 + k = (k + 2) + 1 by omega, a_succ_eq_indexedCount] using h

end A208640Proof

namespace A208640Formula

open PowerSeries

variable (a : ℕ → ℕ)
variable (h1 : a 1 = 16) (h2 : a 2 = 89) (h3 : a 3 = 284)
variable (h4 : a 4 = 722) (h5 : a 5 = 1652) (h6 : a 6 = 3577) (h7 : a 7 = 7504)
variable (hs : ∀ n : ℕ, 3 ≤ n →
  a (n + 5) + 14 * a (n + 3) + 9 * a (n + 1) =
    6 * a (n + 4) + 16 * a (n + 2) + 2 * a n)

noncomputable def closed (n : ℕ) : ℚ :=
  -84 + 63 * 2 ^ n - 191 * n / 6 - 4 * n ^ 2 - n ^ 3 / 6

private theorem closed_recurrence (n : ℕ) :
    closed (n + 5) + 14 * closed (n + 3) + 9 * closed (n + 1) =
      6 * closed (n + 4) + 16 * closed (n + 2) + 2 * closed n := by
  simp only [closed, pow_add, Nat.cast_add, Nat.cast_ofNat]
  ring

include h3 h4 h5 h6 h7 hs in
theorem closed_formula (n : ℕ) (hn : 2 < n) : (a n : ℚ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn7 : n ≤ 7
    · have hn3 : 3 ≤ n := by omega
      interval_cases n <;> norm_num [h3, h4, h5, h6, h7, closed]
    · let m := n - 5
      have hm : 3 ≤ m := by dsimp [m]; omega
      have heq : n = m + 5 := by dsimp [m]; omega
      have hi (k : ℕ) (hk : k < 5) : (a (m + k) : ℚ) = closed (m + k) :=
        ih (m + k) (by dsimp [m]; omega) (by omega)
      have hq : (a (m + 5) : ℚ) + 14 * a (m + 3) + 9 * a (m + 1) =
          6 * a (m + 4) + 16 * a (m + 2) + 2 * a m := by
        exact_mod_cast hs m hm
      have hi0 : (a m : ℚ) = closed m := by simpa using hi 0 (by decide)
      rw [hi 3 (by decide), hi 1 (by decide), hi 4 (by decide),
        hi 2 (by decide), hi0] at hq
      rw [heq]
      linarith [closed_recurrence m]

include h1 h2 h3 h4 h5 h6 h7 hs in
theorem generating_function :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 4 * (1 - 2 * X)) =
      X * (16 - 7 * X - 26 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 - 2 * X ^ 5 - 4 * X ^ 6) := by
  let g : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)
  change g * ((1 - X) ^ 4 * (1 - 2 * X)) = _
  have hl : g * ((1 - X) ^ 4 * (1 - 2 * X)) =
      g * X ^ 0 - 6 • (g * X ^ 1) + 14 • (g * X ^ 2) - 16 • (g * X ^ 3)
        + 9 • (g * X ^ 4) - 2 • (g * X ^ 5) := by
    simp only [nsmul_eq_mul]
    ring
  have hr : (X : PowerSeries ℚ) *
      (16 - 7 * X - 26 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 - 2 * X ^ 5 - 4 * X ^ 6) =
      16 • X ^ 1 - 7 • X ^ 2 - 26 • X ^ 3 + 8 • X ^ 4
        + 16 • X ^ 5 - 2 • X ^ 6 - 4 • X ^ 7 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_nsmul]
  by_cases hn : n ≤ 7
  · interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk,
        h1, h2, h3, h4, h5, h6, h7]
  · have hc (k : ℕ) (hk : k < n) : coeff n (g * X ^ k) = (a (n - k) : ℚ) := by
      rw [coeff_mul_X_pow', if_pos (by omega)]
      simp only [g, coeff_mk]
      rw [if_neg (by omega)]
    have hx (k : ℕ) (hk : k < n) : coeff n (X ^ k : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    simp (disch := omega) only [hc, hx, nsmul_eq_mul, mul_zero, add_zero,
      sub_zero, Nat.sub_zero]
    norm_num only [Nat.cast_ofNat]
    have hrec := hs (n - 5) (by omega)
    have heq (k : ℕ) (hk : k ≤ 5) : n - 5 + k = n - (5 - k) := by omega
    rw [heq 5 (by decide), heq 3 (by decide), heq 1 (by decide),
      heq 4 (by decide), heq 2 (by decide)] at hrec
    norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at hrec
    have hq : (a n : ℚ) + 14 * a (n - 2) + 9 * a (n - 4) =
        6 * a (n - 1) + 16 * a (n - 3) + 2 * a (n - 5) := by
      exact_mod_cast hrec
    linarith

include h1 h2 h3 h4 h5 h6 h7 hs in
theorem of_recurrence :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 4 * (1 - 2 * X)) =
      X * (16 - 7 * X - 26 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 - 2 * X ^ 5 - 4 * X ^ 6) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) =
      -84 + 63 * 2 ^ n - 191 * n / 6 - 4 * n ^ 2 - n ^ 3 / 6 := by
  exact ⟨generating_function a h1 h2 h3 h4 h5 h6 h7 hs,
    closed_formula a h3 h4 h5 h6 h7 hs⟩

end A208640Formula

theorem OMA.solution : type_of% @OMA.S_oeis_a208640.main := by
  rcases A208640Proof.a_initial_values with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact A208640Formula.of_recurrence OMA.S_oeis_a208640.a h1 h2 h3 h4 h5 h6 h7
    A208640Proof.a_recurrence
