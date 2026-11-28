import OMAStatements.S_oeis_a224040
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
A224040: exact enumeration of four-row binary arrays with nondecreasing
rows and diagonals and unimodal antidiagonals.

A three-column history suffices to check all constraints introduced by
prepending a column. An exact semantic and cardinality correspondence
identifies the canonical array count with paths in a closed 177-state
table. Kernel checks certify every transition and nine count vectors.
The fifth finite difference vanishes from suffix length three; linear
induction propagates this identity to every length.

Source: https://oeis.org/A224040
Array definition: R. H. Hardin (2013).
Generating-function and recurrence conjectures: Colin Barker (2018).
The canonical statement is unchanged from statement PR34887.
The generic counting infrastructure is adapted from our independent
A223840 proof in PR40005; the array predicate and state certificate differ.
-/

namespace A224040Proof
open OMA.S_oeis_a224040
abbrev Col := Fin 4 → Fin 2

def uniCheck (l : List ℕ) : Bool :=
  (List.range (l.length + 1)).any fun m =>
    decide ((l.take m).Pairwise (· ≤ ·) ∧ (l.drop m).Pairwise (· ≥ ·))

def adjacent (u v : Col) : Prop :=
  (∀ i : Fin 4, u i ≤ v i) ∧ (∀ i : Fin 3, u i.castSucc ≤ v i.succ)
instance (u v : Col) : Decidable (adjacent u v) := inferInstanceAs
  (Decidable ((∀ i : Fin 4, u i ≤ v i) ∧ (∀ i : Fin 3, u i.castSucc ≤ v i.succ)))

structure State where
  history : List Col

def columnValues (c : Col) : List ℕ := List.ofFn fun i => (c i).val

theorem columnValues_injective : Function.Injective columnValues := by
  intro c d h
  have hf := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun hf i)

theorem state_eq_iff (s t : State) : s = t ↔
    s.history.map columnValues = t.history.map columnValues := by
  constructor
  · rintro rfl; rfl
  · intro hh
    have hh' : s.history = t.history :=
      (List.map_injective_iff.mpr columnValues_injective) hh
    cases s
    cases t
    cases hh'
    rfl

instance instDecidableEqState : DecidableEq State := fun s t =>
  decidable_of_iff _ (state_eq_iff s t).symm

def start : State := ⟨[]⟩

def headOK (s : State) (c : Col) : Prop :=
  match s.history with
  | [] => True
  | d :: _ => adjacent c d
instance instDecidableHeadOK : (s : State) → (c : Col) → Decidable (headOK s c)
  | ⟨[]⟩, _ => inferInstanceAs (Decidable True)
  | ⟨d :: _⟩, c => inferInstanceAs (Decidable (adjacent c d))

def localOK (s : State) (c : Col) : Prop :=
  headOK s c ∧ (∀ i : Fin 4, uniCheck (adiagFrom (c :: s.history) i.val) = true)
instance (s : State) (c : Col) : Decidable (localOK s c) := inferInstanceAs
  (Decidable (headOK s c ∧ (∀ i : Fin 4, uniCheck (adiagFrom (c :: s.history) i.val) = true)))

def nextState (s : State) (c : Col) : State := ⟨(c :: s.history).take 3⟩
def step (s : State) (c : Col) : Option State :=
  if localOK s c then some (nextState s c) else none

def decode (c : Fin 16) (i : Fin 4) : Fin 2 :=
  ⟨c.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩
def allCols : List Col := List.ofFn decode
theorem decode_injective : Function.Injective decode := by decide +kernel
noncomputable def colEquiv : Fin 16 ≃ Col :=
  Equiv.ofBijective decode
    ((Fintype.bijective_iff_injective_and_card decode).mpr
      ⟨decode_injective, by simp⟩)
theorem sum_allCols (f : Col → ℕ) :
    (allCols.map f).sum = ∑ c : Col, f c := by
  rw [allCols, List.map_ofFn, List.sum_ofFn]
  exact colEquiv.sum_comp f

def successors (s : State) : List State := allCols.filterMap (step s)
end A224040Proof

namespace A224040Proof
open OMA.S_oeis_a224040

theorem unimodal_nil : Unimodal [] := ⟨0, by simp⟩

theorem unimodal_tail {b : ℕ} {l : List ℕ} (h : Unimodal (b :: l)) :
    Unimodal l := by
  obtain ⟨m, hu, hd⟩ := h
  cases m with
  | zero =>
      refine ⟨0, by simp, ?_⟩
      simpa using hd.tail
  | succ m =>
      refine ⟨m, ?_, ?_⟩
      · simpa using hu.tail
      · simpa using hd

theorem unimodal_drop (j : ℕ) {l : List ℕ} (h : Unimodal l) :
    Unimodal (l.drop j) := by
  induction j generalizing l with
  | zero => simpa using h
  | succ j ih =>
      cases l with
      | nil => simpa using unimodal_nil
      | cons b l => simpa using ih (unimodal_tail h)

theorem uniCheck_eq_true_iff (l : List ℕ) : uniCheck l = true ↔ Unimodal l := by
  simp only [uniCheck, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨m, _, hu, hd⟩
    exact ⟨m, hu, hd⟩
  · rintro ⟨m, hu, hd⟩
    by_cases hm : m ≤ l.length
    · exact ⟨m, by omega, hu, hd⟩
    · refine ⟨l.length, by omega, ?_, by simp⟩
      simpa [List.take_of_length_le (by omega : l.length ≤ m)] using hu

end A224040Proof

namespace A224040Proof
open OMA.S_oeis_a224040

theorem isSolution_tail {c : Col} {l : List Col}
    (h : IsSolution (c :: l)) : IsSolution l := by
  refine ⟨h.1.tail, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · apply unimodal_tail (b := (c 1 : ℕ))
      simpa [adiagFrom] using h.2.1 1 (by decide)
    · apply unimodal_tail (b := (c 2 : ℕ))
      simpa [adiagFrom] using h.2.1 2 (by decide)
    · apply unimodal_tail (b := (c 3 : ℕ))
      simpa [adiagFrom] using h.2.1 3 (by decide)
    · simpa only [List.drop_succ_cons, List.drop_zero] using h.2.2 1
  · intro j
    simpa only [List.drop_succ_cons] using h.2.2 (j + 1)

theorem isSolution_cons_iff (c : Col) (l : List Col) :
    IsSolution (c :: l) ↔
      (∀ d ∈ l.head?, (∀ i : Fin 4, c i ≤ d i) ∧
        (∀ i : Fin 3, c i.castSucc ≤ d i.succ)) ∧
      (∀ i : Fin 4, Unimodal (adiagFrom (c :: l) i.val)) ∧ IsSolution l := by
  constructor
  · intro h
    exact ⟨(List.isChain_cons.mp h.1).1, fun i => h.2.1 i.val i.isLt,
      isSolution_tail h⟩
  · rintro ⟨hc, ha, hl⟩
    refine ⟨List.isChain_cons.mpr ⟨hc, hl.1⟩, ?_, ?_⟩
    · intro i hi
      exact ha ⟨i, hi⟩
    · intro j
      cases j with
      | zero => simpa using ha (3 : Fin 4)
      | succ j => simpa only [List.drop_succ_cons] using hl.2.2 j

theorem adiagFrom_take (l : List Col) (i k : ℕ) (hk : i < k) :
    adiagFrom (l.take k) i = adiagFrom l i := by
  induction l generalizing i k with
  | nil => simp [adiagFrom]
  | cons c l ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [List.take_succ_cons, adiagFrom]
      split_ifs with hi hz
      · rfl
      · rw [ih (i - 1) k (by omega)]
      · rfl

theorem adiagFrom_cons_take (c : Col) (l : List Col) (i : Fin 4) :
    adiagFrom (c :: l.take 3) i.val = adiagFrom (c :: l) i.val := by
  simpa only [List.take_succ_cons] using adiagFrom_take (c :: l) i.val 4 i.isLt

end A224040Proof

namespace A224040Proof

def runFrom (s : State) : List Col → Option State
  | [] => some s
  | c :: l => (step s c).bind (fun t => runFrom t l)

def run : List Col → Option State
  | [] => some start
  | c :: l => (run l).bind (fun s => step s c)

theorem runFrom_append (s : State) (l r : List Col) :
    runFrom s (l ++ r) = (runFrom s l).bind (fun t => runFrom t r) := by
  induction l generalizing s with
  | nil => rfl
  | cons c l ih =>
      cases he : step s c <;> simp [runFrom, he, ih]

theorem run_eq_reverse (l : List Col) : run l = runFrom start l.reverse := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      rw [run, List.reverse_cons, runFrom_append, ih]
      congr 1
      funext s
      simp [runFrom]

end A224040Proof

namespace A224040Proof
open OMA.S_oeis_a224040

theorem run_tracks {l : List Col} {s : State} (h : run l = some s) :
    s.history = l.take 3 := by
  induction l generalizing s with
  | nil =>
      have hs : start = s := by simpa [run] using h
      subst s
      rfl
  | cons c l ih =>
      cases ht : run l with
      | none => simp [run, ht] at h
      | some t =>
          have hs : step t c = some s := by simpa [run, ht] using h
          have htrack := ih ht
          by_cases hok : localOK t c
          · have he : nextState t c = s := by simpa [step, hok] using hs
            subst s
            simp [nextState, htrack, List.take_take]
          · simp [step, hok] at hs

theorem localOK_iff_tracks {l : List Col} {s : State}
    (ht : s.history = l.take 3) (c : Col) :
    localOK s c ↔
      (∀ d ∈ l.head?, (∀ i : Fin 4, c i ≤ d i) ∧
        (∀ i : Fin 3, c i.castSucc ≤ d i.succ)) ∧
      (∀ i : Fin 4, Unimodal (adiagFrom (c :: l) i.val)) := by
  simp only [localOK, ht, uniCheck_eq_true_iff, adiagFrom_cons_take]
  apply and_congr_left
  intro _
  cases l <;> simp [headOK, ht, adjacent]

theorem run_correct (l : List Col) : (run l).isSome = true ↔ IsSolution l := by
  induction l with
  | nil => simp [run, IsSolution, adiagFrom, unimodal_nil]
  | cons c l ih =>
      cases ht : run l with
      | none =>
          constructor
          · simp [run, ht]
          · intro h
            have := ih.mpr (isSolution_tail h)
            simp [ht] at this
      | some s =>
          have hl : IsSolution l := ih.mp (by simp [ht])
          calc
            (run (c :: l)).isSome = true ↔ localOK s c := by
              simp only [run, ht, Option.bind_some]
              by_cases hok : localOK s c <;> simp [step, hok]
            _ ↔ _ := localOK_iff_tracks (run_tracks ht) c
            _ ↔ IsSolution (c :: l) := by
              rw [isSolution_cons_iff]
              simp [hl]

end A224040Proof

namespace A224040Count
variable {S : Type*}
def paths (succ : S → List S) (accepted : S → ℕ) : ℕ → S → ℕ
  | 0, s => accepted s
  | n + 1, s => ((succ s).map (paths succ accepted n)).sum

lemma sum_balance (L : List S) (f : Fin 9 → S → ℕ)
    (h : ∀ s, f 8 s + 10 * f 6 s + 5 * f 4 s =
      5 * f 7 s + 10 * f 5 s + f 3 s) :
    (L.map (f 8)).sum + 10 * (L.map (f 6)).sum + 5 * (L.map (f 4)).sum =
      5 * (L.map (f 7)).sum + 10 * (L.map (f 5)).sum + (L.map (f 3)).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs := h s
    omega

theorem paths_recurrence (succ : S → List S) (accepted : S → ℕ)
    (hbase : ∀ s, paths succ accepted 8 s + 10 * paths succ accepted 6 s + 5 * paths succ accepted 4 s =
      5 * paths succ accepted 7 s + 10 * paths succ accepted 5 s + paths succ accepted 3 s) :
    ∀ n s, paths succ accepted (n + 8) s + 10 * paths succ accepted (n + 6) s + 5 * paths succ accepted (n + 4) s =
      5 * paths succ accepted (n + 7) s + 10 * paths succ accepted (n + 5) s + paths succ accepted (n + 3) s := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accepted (n + 8))).sum + 10 * ((succ s).map (paths succ accepted (n + 6))).sum + 5 * ((succ s).map (paths succ accepted (n + 4))).sum =
      5 * ((succ s).map (paths succ accepted (n + 7))).sum + 10 * ((succ s).map (paths succ accepted (n + 5))).sum + ((succ s).map (paths succ accepted (n + 3))).sum
    exact sum_balance (succ s) (fun k => paths succ accepted (n + k.val)) ih

theorem paths_eq_vectors (succ : S → List S) (accepted : S → ℕ)
    (v : Fin 9 → S → ℕ) (hzero : ∀ s, v 0 s = accepted s)
    (hnext : ∀ k : Fin 8, ∀ s,
      ((succ s).map (v k.castSucc)).sum = v k.succ s) :
    ∀ k : Fin 9, ∀ s, paths succ accepted k.val s = v k s := by
  intro k
  induction k using Fin.induction with
  | zero => intro s; exact (hzero s).symm
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accepted k.val)).sum = v k.succ s
    rw [show paths succ accepted k.val = v k.castSucc from funext ih]
    exact hnext k s
end A224040Count

namespace A224040Proof
open OMA.S_oeis_a224040

open scoped BigOperators

theorem card_lists {A : Type*} (n : ℕ) (P : List A → Prop) :
    Nat.card {w : List A // w.length = n ∧ P w} =
      Nat.card {w : Fin n → A // P (List.ofFn w)} := by
  let e : {w : List A // w.length = n ∧ P w} ≃
      {v : List.Vector A n // P v.val} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun w : List A => w.length = n) P).symm
  apply Nat.card_congr
  refine e.trans ((Equiv.vectorEquivFin A n).subtypeEquiv ?_)
  intro v
  change P v.val ↔ P (List.ofFn v.get)
  have hv : List.ofFn v.get = v.val := by
    calc
      List.ofFn v.get = v.toList := by
        simpa only [List.Vector.toList_ofFn] using
          congrArg List.Vector.toList (List.Vector.ofFn_get v)
      _ = v.val := by cases v; rfl
  rw [hv]

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
  Nat.card {w : Fin n → Col // (runFrom s (List.ofFn w)).isSome = true}

lemma suffixCount_zero (s : State) : suffixCount s 0 = 1 := by
  simp [suffixCount, runFrom, Nat.card_eq_fintype_card]

lemma suffixCount_succ (s : State) (n : ℕ) :
    suffixCount s (n + 1) =
      ∑ c : Col, (step s c).elim 0 (fun t => suffixCount t n) := by
  classical
  unfold suffixCount
  rw [card_words_succ]
  apply Finset.sum_congr rfl
  intro c _
  cases h : step s c with
  | none => simp [runFrom, h, Nat.card_eq_fintype_card]
  | some t => simp [runFrom, h]

lemma sum_filterMap {A B : Type*} (L : List A) (f : A → Option B) (g : B → ℕ) :
    ((L.filterMap f).map g).sum = (L.map (fun a => (f a).elim 0 g)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : f a <;> simp [h, ih]

variable {I : Type*}

theorem suffixCount_eq_paths
    (state : I → State) (succ : I → List I) (accepted : I → ℕ)
    (hstep : ∀ i, allCols.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, 1 = accepted i) :
    ∀ n i, suffixCount (state i) n = A224040Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_allCols, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A224040Count.paths succ accepted n from funext ih]
    rfl

theorem a_eq_suffix
    (hcorrect : ∀ l, (run l).isSome = true ↔ IsSolution l) (n : ℕ) :
    a n = suffixCount start n := by
  let e : {l : List Col // l.length = n ∧ IsSolution l} ≃
      {l : List Col // l.length = n ∧ (runFrom start l).isSome = true} := {
    toFun := fun l => ⟨l.val.reverse, by
      refine ⟨by simpa using l.property.1, ?_⟩
      rw [← run_eq_reverse]
      exact (hcorrect l.val).mpr l.property.2⟩
    invFun := fun l => ⟨l.val.reverse, by
      refine ⟨by simpa using l.property.1, ?_⟩
      apply (hcorrect l.val.reverse).mp
      rw [run_eq_reverse, List.reverse_reverse]
      exact l.property.2⟩
    left_inv := by intro l; apply Subtype.ext; simp
    right_inv := by intro l; apply Subtype.ext; simp }
  calc
    a n = Nat.card {l : List Col // l.length = n ∧
        (runFrom start l).isSome = true} := Nat.card_congr e
    _ = suffixCount start n := by rw [card_lists]; rfl

theorem a_eq_paths
    (hcorrect : ∀ l, (run l).isSome = true ↔ IsSolution l)
    (state : I → State) (succ : I → List I) (accepted : I → ℕ) (initial : I)
    (hstep : ∀ i, allCols.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, 1 = accepted i) (hstart : state initial = start) (n : ℕ) :
    a n = A224040Count.paths succ accepted n initial := by
  rw [a_eq_suffix hcorrect, ← hstart]
  exact suffixCount_eq_paths state succ accepted hstep haccept n initial

end A224040Proof

namespace A224040Table
open A224040Proof
def codes (i : Fin 177) : List ℕ :=
  (if i.val < 88 then (if i.val < 44 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else (if i.val < 4 then [2] else [3]))) else (if i.val < 8 then (if i.val < 6 then [4] else (if i.val < 7 then [5] else [6])) else (if i.val < 9 then [7] else (if i.val < 10 then [8] else [9])))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then [10] else [11]) else (if i.val < 14 then [12] else (if i.val < 15 then [13] else [14]))) else (if i.val < 19 then (if i.val < 17 then [15] else (if i.val < 18 then [0, 0] else [0, 1])) else (if i.val < 20 then [0, 2] else (if i.val < 21 then [0, 3] else [1, 3]))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then [0, 4] else [0, 5]) else (if i.val < 25 then [0, 6] else (if i.val < 26 then [2, 6] else [0, 7]))) else (if i.val < 30 then (if i.val < 28 then [1, 7] else (if i.val < 29 then [2, 7] else [3, 7])) else (if i.val < 31 then [0, 8] else (if i.val < 32 then [8, 8] else [0, 9])))) else (if i.val < 38 then (if i.val < 35 then (if i.val < 34 then [8, 9] else [0, 10]) else (if i.val < 36 then [8, 10] else (if i.val < 37 then [0, 11] else [1, 11]))) else (if i.val < 41 then (if i.val < 39 then [8, 11] else (if i.val < 40 then [9, 11] else [0, 12])) else (if i.val < 42 then [4, 12] else (if i.val < 43 then [8, 12] else [12, 12])))))) else (if i.val < 66 then (if i.val < 55 then (if i.val < 49 then (if i.val < 46 then (if i.val < 45 then [0, 13] else [4, 13]) else (if i.val < 47 then [8, 13] else (if i.val < 48 then [12, 13] else [0, 14]))) else (if i.val < 52 then (if i.val < 50 then [2, 14] else (if i.val < 51 then [4, 14] else [6, 14])) else (if i.val < 53 then [8, 14] else (if i.val < 54 then [10, 14] else [12, 14])))) else (if i.val < 60 then (if i.val < 57 then (if i.val < 56 then [14, 14] else [0, 15]) else (if i.val < 58 then [1, 15] else (if i.val < 59 then [2, 15] else [3, 15]))) else (if i.val < 63 then (if i.val < 61 then [4, 15] else (if i.val < 62 then [5, 15] else [6, 15])) else (if i.val < 64 then [7, 15] else (if i.val < 65 then [8, 15] else [9, 15]))))) else (if i.val < 77 then (if i.val < 71 then (if i.val < 68 then (if i.val < 67 then [10, 15] else [11, 15]) else (if i.val < 69 then [12, 15] else (if i.val < 70 then [13, 15] else [14, 15]))) else (if i.val < 74 then (if i.val < 72 then [15, 15] else (if i.val < 73 then [0, 0, 0] else [0, 0, 1])) else (if i.val < 75 then [0, 0, 2] else (if i.val < 76 then [0, 0, 3] else [0, 1, 3])))) else (if i.val < 82 then (if i.val < 79 then (if i.val < 78 then [0, 0, 4] else [0, 0, 5]) else (if i.val < 80 then [0, 0, 6] else (if i.val < 81 then [0, 2, 6] else [0, 0, 7]))) else (if i.val < 85 then (if i.val < 83 then [0, 1, 7] else (if i.val < 84 then [0, 2, 7] else [0, 3, 7])) else (if i.val < 86 then [1, 3, 7] else (if i.val < 87 then [0, 0, 8] else [0, 8, 8]))))))) else (if i.val < 132 then (if i.val < 110 then (if i.val < 99 then (if i.val < 93 then (if i.val < 90 then (if i.val < 89 then [8, 8, 8] else [0, 0, 9]) else (if i.val < 91 then [0, 8, 9] else (if i.val < 92 then [8, 8, 9] else [0, 0, 10]))) else (if i.val < 96 then (if i.val < 94 then [0, 8, 10] else (if i.val < 95 then [0, 0, 11] else [0, 1, 11])) else (if i.val < 97 then [0, 8, 11] else (if i.val < 98 then [0, 9, 11] else [0, 0, 12])))) else (if i.val < 104 then (if i.val < 101 then (if i.val < 100 then [0, 4, 12] else [0, 8, 12]) else (if i.val < 102 then [8, 8, 12] else (if i.val < 103 then [0, 12, 12] else [4, 12, 12]))) else (if i.val < 107 then (if i.val < 105 then [8, 12, 12] else (if i.val < 106 then [12, 12, 12] else [0, 0, 13])) else (if i.val < 108 then [0, 4, 13] else (if i.val < 109 then [0, 8, 13] else [8, 8, 13]))))) else (if i.val < 121 then (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then [0, 12, 13] else [8, 12, 13]) else (if i.val < 113 then [0, 0, 14] else (if i.val < 114 then [0, 2, 14] else [0, 4, 14]))) else (if i.val < 118 then (if i.val < 116 then [0, 6, 14] else (if i.val < 117 then [2, 6, 14] else [0, 8, 14])) else (if i.val < 119 then [0, 10, 14] else (if i.val < 120 then [0, 12, 14] else [4, 12, 14])))) else (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then [8, 12, 14] else [12, 12, 14]) else (if i.val < 124 then [0, 14, 14] else (if i.val < 125 then [2, 14, 14] else [4, 14, 14]))) else (if i.val < 129 then (if i.val < 127 then [6, 14, 14] else (if i.val < 128 then [8, 14, 14] else [10, 14, 14])) else (if i.val < 130 then [12, 14, 14] else (if i.val < 131 then [14, 14, 14] else [0, 0, 15])))))) else (if i.val < 154 then (if i.val < 143 then (if i.val < 137 then (if i.val < 134 then (if i.val < 133 then [0, 1, 15] else [0, 2, 15]) else (if i.val < 135 then [0, 3, 15] else (if i.val < 136 then [1, 3, 15] else [0, 4, 15]))) else (if i.val < 140 then (if i.val < 138 then [0, 5, 15] else (if i.val < 139 then [0, 6, 15] else [2, 6, 15])) else (if i.val < 141 then [0, 7, 15] else (if i.val < 142 then [1, 7, 15] else [2, 7, 15])))) else (if i.val < 148 then (if i.val < 145 then (if i.val < 144 then [3, 7, 15] else [0, 8, 15]) else (if i.val < 146 then [0, 9, 15] else (if i.val < 147 then [0, 10, 15] else [0, 11, 15]))) else (if i.val < 151 then (if i.val < 149 then [1, 11, 15] else (if i.val < 150 then [0, 12, 15] else [8, 12, 15])) else (if i.val < 152 then [0, 13, 15] else (if i.val < 153 then [8, 13, 15] else [0, 14, 15]))))) else (if i.val < 165 then (if i.val < 159 then (if i.val < 156 then (if i.val < 155 then [2, 14, 15] else [4, 14, 15]) else (if i.val < 157 then [6, 14, 15] else (if i.val < 158 then [8, 14, 15] else [10, 14, 15]))) else (if i.val < 162 then (if i.val < 160 then [12, 14, 15] else (if i.val < 161 then [14, 14, 15] else [0, 15, 15])) else (if i.val < 163 then [1, 15, 15] else (if i.val < 164 then [2, 15, 15] else [3, 15, 15])))) else (if i.val < 171 then (if i.val < 168 then (if i.val < 166 then [4, 15, 15] else (if i.val < 167 then [5, 15, 15] else [6, 15, 15])) else (if i.val < 169 then [7, 15, 15] else (if i.val < 170 then [8, 15, 15] else [9, 15, 15]))) else (if i.val < 174 then (if i.val < 172 then [10, 15, 15] else (if i.val < 173 then [11, 15, 15] else [12, 15, 15])) else (if i.val < 175 then [13, 15, 15] else (if i.val < 176 then [14, 15, 15] else [15, 15, 15]))))))))
def state (i : Fin 177) : State :=
  ⟨(codes i).map (fun c => decode ⟨c % 16, Nat.mod_lt _ (by decide)⟩)⟩
def succ (i : Fin 177) : List (Fin 177) :=
  (if i.val < 88 then (if i.val < 44 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] else [17]) else (if i.val < 3 then [18] else (if i.val < 4 then [19] else [20, 21]))) else (if i.val < 8 then (if i.val < 6 then [22] else (if i.val < 7 then [23] else [24, 25])) else (if i.val < 9 then [26, 27, 28, 29] else (if i.val < 10 then [30, 31] else [32, 33])))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then [34, 35] else [36, 37, 38, 39]) else (if i.val < 14 then [40, 41, 42, 43] else (if i.val < 15 then [44, 45, 46, 47] else [48, 49, 50, 51, 52, 53, 54, 55]))) else (if i.val < 19 then (if i.val < 17 then [56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71] else (if i.val < 18 then [72] else [73])) else (if i.val < 20 then [74] else (if i.val < 21 then [75] else [76]))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then [77] else [78]) else (if i.val < 25 then [79] else (if i.val < 26 then [80] else [81]))) else (if i.val < 30 then (if i.val < 28 then [82] else (if i.val < 29 then [83] else [84, 85])) else (if i.val < 31 then [86] else (if i.val < 32 then [87, 88] else [89])))) else (if i.val < 38 then (if i.val < 35 then (if i.val < 34 then [90, 91] else [92]) else (if i.val < 36 then [93] else (if i.val < 37 then [94] else [95]))) else (if i.val < 41 then (if i.val < 39 then [96] else (if i.val < 40 then [97] else [98])) else (if i.val < 42 then [99] else (if i.val < 43 then [100, 101] else [102, 103, 104, 105])))))) else (if i.val < 66 then (if i.val < 55 then (if i.val < 49 then (if i.val < 46 then (if i.val < 45 then [106] else [107]) else (if i.val < 47 then [108, 109] else (if i.val < 48 then [110, 111] else [112]))) else (if i.val < 52 then (if i.val < 50 then [113] else (if i.val < 51 then [114] else [115, 116])) else (if i.val < 53 then [117] else (if i.val < 54 then [118] else [119, 120, 121, 122])))) else (if i.val < 60 then (if i.val < 57 then (if i.val < 56 then [123, 124, 125, 126, 127, 128, 129, 130] else [131]) else (if i.val < 58 then [132] else (if i.val < 59 then [133] else [134, 135]))) else (if i.val < 63 then (if i.val < 61 then [136] else (if i.val < 62 then [137] else [138, 139])) else (if i.val < 64 then [140, 141, 142, 143] else (if i.val < 65 then [144] else [145]))))) else (if i.val < 77 then (if i.val < 71 then (if i.val < 68 then (if i.val < 67 then [146] else [147, 148]) else (if i.val < 69 then [149, 150] else (if i.val < 70 then [151, 152] else [153, 154, 155, 156, 157, 158, 159, 160]))) else (if i.val < 74 then (if i.val < 72 then [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176] else (if i.val < 73 then [72] else [72])) else (if i.val < 75 then [72] else (if i.val < 76 then [72] else [73])))) else (if i.val < 82 then (if i.val < 79 then (if i.val < 78 then [72] else [72]) else (if i.val < 80 then [72] else (if i.val < 81 then [74] else [72]))) else (if i.val < 85 then (if i.val < 83 then [73] else (if i.val < 84 then [74] else [75])) else (if i.val < 86 then [76] else (if i.val < 87 then [72] else [86]))))))) else (if i.val < 132 then (if i.val < 110 then (if i.val < 99 then (if i.val < 93 then (if i.val < 90 then (if i.val < 89 then [87, 88] else [72]) else (if i.val < 91 then [86] else (if i.val < 92 then [87] else [72]))) else (if i.val < 96 then (if i.val < 94 then [86] else (if i.val < 95 then [72] else [73])) else (if i.val < 97 then [86] else (if i.val < 98 then [89] else [72])))) else (if i.val < 104 then (if i.val < 101 then (if i.val < 100 then [77] else [86]) else (if i.val < 102 then [87, 88] else (if i.val < 103 then [98] else [99]))) else (if i.val < 107 then (if i.val < 105 then [100, 101] else (if i.val < 106 then [102, 103, 104, 105] else [72])) else (if i.val < 108 then [77] else (if i.val < 109 then [86] else [87]))))) else (if i.val < 121 then (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then [98] else [100]) else (if i.val < 113 then [72] else (if i.val < 114 then [74] else [77]))) else (if i.val < 118 then (if i.val < 116 then [79] else (if i.val < 117 then [80] else [86])) else (if i.val < 119 then [92] else (if i.val < 120 then [98] else [99])))) else (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then [100, 101] else [102, 103, 104, 105]) else (if i.val < 124 then [112] else (if i.val < 125 then [113] else [114]))) else (if i.val < 129 then (if i.val < 127 then [115, 116] else (if i.val < 128 then [117] else [118])) else (if i.val < 130 then [119, 120, 121, 122] else (if i.val < 131 then [123, 124, 125, 126, 127, 128, 129, 130] else [72])))))) else (if i.val < 154 then (if i.val < 143 then (if i.val < 137 then (if i.val < 134 then (if i.val < 133 then [73] else [74]) else (if i.val < 135 then [75] else (if i.val < 136 then [76] else [77]))) else (if i.val < 140 then (if i.val < 138 then [78] else (if i.val < 139 then [79] else [80])) else (if i.val < 141 then [81] else (if i.val < 142 then [82] else [83])))) else (if i.val < 148 then (if i.val < 145 then (if i.val < 144 then [84, 85] else [86]) else (if i.val < 146 then [89] else (if i.val < 147 then [92] else [94]))) else (if i.val < 151 then (if i.val < 149 then [95] else (if i.val < 150 then [98] else [100])) else (if i.val < 152 then [106] else (if i.val < 153 then [108] else [112]))))) else (if i.val < 165 then (if i.val < 159 then (if i.val < 156 then (if i.val < 155 then [113] else [114]) else (if i.val < 157 then [115, 116] else (if i.val < 158 then [117] else [118]))) else (if i.val < 162 then (if i.val < 160 then [119, 120, 121, 122] else (if i.val < 161 then [123, 124, 125, 126, 127, 128, 129, 130] else [131])) else (if i.val < 163 then [132] else (if i.val < 164 then [133] else [134, 135])))) else (if i.val < 171 then (if i.val < 168 then (if i.val < 166 then [136] else (if i.val < 167 then [137] else [138, 139])) else (if i.val < 169 then [140, 141, 142, 143] else (if i.val < 170 then [144] else [145]))) else (if i.val < 174 then (if i.val < 172 then [146] else (if i.val < 173 then [147, 148] else [149, 150])) else (if i.val < 175 then [151, 152] else (if i.val < 176 then [153, 154, 155, 156, 157, 158, 159, 160] else [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]))))))))
def vectors (i : Fin 177) : List ℕ :=
  (if i.val < 88 then (if i.val < 44 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [1, 16, 55, 105, 168, 252, 363, 508, 695] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 3 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 4 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 8 then (if i.val < 6 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 7 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 9 then [1, 4, 5, 5, 5, 5, 5, 5, 5] else (if i.val < 10 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else [1, 2, 3, 3, 3, 3, 3, 3, 3])))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 4, 4, 4, 4, 4, 4, 4]) else (if i.val < 14 then [1, 4, 8, 13, 19, 26, 34, 43, 53] else (if i.val < 15 then [1, 4, 6, 6, 6, 6, 6, 6, 6] else [1, 8, 19, 34, 54, 80, 113, 154, 204]))) else (if i.val < 19 then (if i.val < 17 then [1, 16, 46, 88, 145, 222, 325, 461, 638] else (if i.val < 18 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 20 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 21 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 25 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 26 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 30 then (if i.val < 28 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 29 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 31 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 32 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 38 then (if i.val < 35 then (if i.val < 34 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 36 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 37 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 41 then (if i.val < 39 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 40 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 42 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 43 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else [1, 4, 8, 13, 19, 26, 34, 43, 53])))))) else (if i.val < 66 then (if i.val < 55 then (if i.val < 49 then (if i.val < 46 then (if i.val < 45 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 47 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 48 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 52 then (if i.val < 50 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 51 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 53 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 54 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 4, 8, 13, 19, 26, 34, 43, 53])))) else (if i.val < 60 then (if i.val < 57 then (if i.val < 56 then [1, 8, 19, 34, 54, 80, 113, 154, 204] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 58 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 59 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 63 then (if i.val < 61 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 62 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 64 then [1, 4, 5, 5, 5, 5, 5, 5, 5] else (if i.val < 65 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 77 then (if i.val < 71 then (if i.val < 68 then (if i.val < 67 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 69 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 70 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204]))) else (if i.val < 74 then (if i.val < 72 then [1, 16, 46, 88, 145, 222, 325, 461, 638] else (if i.val < 73 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 75 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 76 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 82 then (if i.val < 79 then (if i.val < 78 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 80 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 81 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 85 then (if i.val < 83 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 84 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 86 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 87 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))))))) else (if i.val < 132 then (if i.val < 110 then (if i.val < 99 then (if i.val < 93 then (if i.val < 90 then (if i.val < 89 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 91 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 92 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 96 then (if i.val < 94 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 95 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 97 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 98 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 104 then (if i.val < 101 then (if i.val < 100 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 102 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else (if i.val < 103 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 107 then (if i.val < 105 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else (if i.val < 106 then [1, 4, 8, 13, 19, 26, 34, 43, 53] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 108 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 109 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 121 then (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 113 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 114 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 118 then (if i.val < 116 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 117 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 119 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 120 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then [1, 2, 3, 4, 5, 6, 7, 8, 9] else [1, 4, 8, 13, 19, 26, 34, 43, 53]) else (if i.val < 124 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 125 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 129 then (if i.val < 127 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 128 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 130 then [1, 4, 8, 13, 19, 26, 34, 43, 53] else (if i.val < 131 then [1, 8, 19, 34, 54, 80, 113, 154, 204] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 154 then (if i.val < 143 then (if i.val < 137 then (if i.val < 134 then (if i.val < 133 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 135 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 136 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 140 then (if i.val < 138 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 139 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 141 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 142 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 148 then (if i.val < 145 then (if i.val < 144 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 146 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 147 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 151 then (if i.val < 149 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 150 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 152 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 153 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 165 then (if i.val < 159 then (if i.val < 156 then (if i.val < 155 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 157 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 158 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 162 then (if i.val < 160 then [1, 4, 8, 13, 19, 26, 34, 43, 53] else (if i.val < 161 then [1, 8, 19, 34, 54, 80, 113, 154, 204] else [1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 163 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 164 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])))) else (if i.val < 171 then (if i.val < 168 then (if i.val < 166 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 167 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 169 then [1, 4, 5, 5, 5, 5, 5, 5, 5] else (if i.val < 170 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 174 then (if i.val < 172 then [1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 173 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 175 then [1, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 176 then [1, 8, 19, 34, 54, 80, 113, 154, 204] else [1, 16, 46, 88, 145, 222, 325, 461, 638]))))))))
def v (k : Fin 9) (i : Fin 177) : ℕ := (vectors i)[k.val]!
def accepted (_ : Fin 177) : ℕ := 1
end A224040Table

namespace A224040Certificate
open A224040Proof A224040Table A224040Count

def tableIndex (n : ℕ) : Fin 177 := ⟨n % 177, Nat.mod_lt _ (by decide)⟩
def LocalCheck (i : Fin 177) : Prop :=
  allCols.filterMap (step (state i)) = (succ i).map state
def NumericCheck (s : Fin 177) : Prop :=
  v 0 s = 1 ∧ (∀ k : Fin 8, ((succ s).map (v k.castSucc)).sum = v k.succ s) ∧
  v 8 s + 10 * v 6 s + 5 * v 4 s = 5 * v 7 s + 10 * v 5 s + v 3 s
instance (i : Fin 177) : Decidable (LocalCheck i) := inferInstanceAs
  (Decidable (allCols.filterMap (step (state i)) = (succ i).map state))
instance (i : Fin 177) : Decidable (NumericCheck i) := by unfold NumericCheck; infer_instance

def LocalBlock (b : ℕ) : Prop := ∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))
def NumericBlock (b : ℕ) : Prop := ∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))
instance (b : ℕ) : Decidable (LocalBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))))
instance (b : ℕ) : Decidable (NumericBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem numeric_blocks : ∀ b : Fin 23, NumericBlock b.val := by
  have h0 : NumericBlock 0 := by decide +kernel
  have h1 : NumericBlock 1 := by decide +kernel
  have h2 : NumericBlock 2 := by decide +kernel
  have h3 : NumericBlock 3 := by decide +kernel
  have h4 : NumericBlock 4 := by decide +kernel
  have h5 : NumericBlock 5 := by decide +kernel
  have h6 : NumericBlock 6 := by decide +kernel
  have h7 : NumericBlock 7 := by decide +kernel
  have h8 : NumericBlock 8 := by decide +kernel
  have h9 : NumericBlock 9 := by decide +kernel
  have h10 : NumericBlock 10 := by decide +kernel
  have h11 : NumericBlock 11 := by decide +kernel
  have h12 : NumericBlock 12 := by decide +kernel
  have h13 : NumericBlock 13 := by decide +kernel
  have h14 : NumericBlock 14 := by decide +kernel
  have h15 : NumericBlock 15 := by decide +kernel
  have h16 : NumericBlock 16 := by decide +kernel
  have h17 : NumericBlock 17 := by decide +kernel
  have h18 : NumericBlock 18 := by decide +kernel
  have h19 : NumericBlock 19 := by decide +kernel
  have h20 : NumericBlock 20 := by decide +kernel
  have h21 : NumericBlock 21 := by decide +kernel
  have h22 : NumericBlock 22 := by decide +kernel
  intro b
  fin_cases b <;> assumption

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem local_blocks : ∀ b : Fin 23, LocalBlock b.val := by
  have h0 : LocalBlock 0 := by decide +kernel
  have h1 : LocalBlock 1 := by decide +kernel
  have h2 : LocalBlock 2 := by decide +kernel
  have h3 : LocalBlock 3 := by decide +kernel
  have h4 : LocalBlock 4 := by decide +kernel
  have h5 : LocalBlock 5 := by decide +kernel
  have h6 : LocalBlock 6 := by decide +kernel
  have h7 : LocalBlock 7 := by decide +kernel
  have h8 : LocalBlock 8 := by decide +kernel
  have h9 : LocalBlock 9 := by decide +kernel
  have h10 : LocalBlock 10 := by decide +kernel
  have h11 : LocalBlock 11 := by decide +kernel
  have h12 : LocalBlock 12 := by decide +kernel
  have h13 : LocalBlock 13 := by decide +kernel
  have h14 : LocalBlock 14 := by decide +kernel
  have h15 : LocalBlock 15 := by decide +kernel
  have h16 : LocalBlock 16 := by decide +kernel
  have h17 : LocalBlock 17 := by decide +kernel
  have h18 : LocalBlock 18 := by decide +kernel
  have h19 : LocalBlock 19 := by decide +kernel
  have h20 : LocalBlock 20 := by decide +kernel
  have h21 : LocalBlock 21 := by decide +kernel
  have h22 : LocalBlock 22 := by decide +kernel
  intro b
  fin_cases b <;> assumption

theorem covered (P : Fin 177 → Prop)
    (h : ∀ b : Fin 23, ∀ j : Fin 8, P (tableIndex (8 * b.val + j.val))) :
    ∀ i, P i := by
  intro i
  let b : Fin 23 := ⟨i.val / 8, by omega⟩
  let j : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : tableIndex (8 * b.val + j.val) = i := by
    apply Fin.ext
    simp only [tableIndex, b, j]
    omega
  simpa only [he] using h b j

theorem local_table (i : Fin 177) :
    allCols.filterMap (step (state i)) = (succ i).map state :=
  covered LocalCheck local_blocks i

theorem numeric_table (i : Fin 177) : NumericCheck i :=
  covered NumericCheck numeric_blocks i

theorem state_zero : state 0 = start := by decide +kernel

theorem paths_vectors (k : Fin 9) (i : Fin 177) :
    paths succ accepted k.val i = v k i :=
  paths_eq_vectors succ accepted v (fun s => (numeric_table s).1)
    (fun k s => (numeric_table s).2.1 k) k i

theorem recurrence_base (s : Fin 177) :
    paths succ accepted 8 s + 10 * paths succ accepted 6 s + 5 * paths succ accepted 4 s =
      5 * paths succ accepted 7 s + 10 * paths succ accepted 5 s + paths succ accepted 3 s := by
  have hv (n : Fin 9) := paths_vectors n s
  change paths succ accepted (8 : Fin 9).val s + 10 * paths succ accepted (6 : Fin 9).val s +
      5 * paths succ accepted (4 : Fin 9).val s =
      5 * paths succ accepted (7 : Fin 9).val s + 10 * paths succ accepted (5 : Fin 9).val s +
      paths succ accepted (3 : Fin 9).val s
  simp only [hv]
  exact (numeric_table s).2.2
end A224040Certificate

namespace A224040Table
open A224040Count A224040Certificate

def indexedCount (n : ℕ) : ℕ := paths succ accepted n 0

theorem indexed_vector (k : Fin 9) : indexedCount k.val = v k 0 := paths_vectors k 0

theorem initial_1 : indexedCount 1 = 16 := by
  have h := indexed_vector (1 : Fin 9)
  have hv : v 1 0 = 16 := by decide +kernel
  exact h.trans hv

theorem initial_2 : indexedCount 2 = 55 := by
  have h := indexed_vector (2 : Fin 9)
  have hv : v 2 0 = 55 := by decide +kernel
  exact h.trans hv

theorem initial_3 : indexedCount 3 = 105 := by
  have h := indexed_vector (3 : Fin 9)
  have hv : v 3 0 = 105 := by decide +kernel
  exact h.trans hv

theorem initial_4 : indexedCount 4 = 168 := by
  have h := indexed_vector (4 : Fin 9)
  have hv : v 4 0 = 168 := by decide +kernel
  exact h.trans hv

theorem initial_5 : indexedCount 5 = 252 := by
  have h := indexed_vector (5 : Fin 9)
  have hv : v 5 0 = 252 := by decide +kernel
  exact h.trans hv

theorem initial_6 : indexedCount 6 = 363 := by
  have h := indexed_vector (6 : Fin 9)
  have hv : v 6 0 = 363 := by decide +kernel
  exact h.trans hv

theorem initial_7 : indexedCount 7 = 508 := by
  have h := indexed_vector (7 : Fin 9)
  have hv : v 7 0 = 508 := by decide +kernel
  exact h.trans hv

theorem initial_8 : indexedCount 8 = 695 := by
  have h := indexed_vector (8 : Fin 9)
  have hv : v 8 0 = 695 := by decide +kernel
  exact h.trans hv

theorem indexed_recurrence (n : ℕ) :
    indexedCount (n + 8) + 10 * indexedCount (n + 6) + 5 * indexedCount (n + 4) =
      5 * indexedCount (n + 7) + 10 * indexedCount (n + 5) + indexedCount (n + 3) :=
  paths_recurrence succ accepted recurrence_base n 0
end A224040Table

namespace A224040Formula
open PowerSeries

theorem integer_recurrence (a : ℕ → ℕ)
    (hs : ∀ n : ℕ, a (n + 8) + 10 * a (n + 6) + 5 * a (n + 4) =
      5 * a (n + 7) + 10 * a (n + 5) + a (n + 3))
    (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  have h := hs (n - 8)
  have heq (k : ℕ) (hk : k ≤ 8) : n - 8 + k = n - (8 - k) := by omega
  rw [heq 8 (by decide), heq 6 (by decide), heq 4 (by decide),
    heq 7 (by decide), heq 5 (by decide), heq 3 (by decide)] at h
  norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at h
  have hz : (a n : ℤ) + 10 * a (n - 2) + 5 * a (n - 4) =
      5 * a (n - 1) + 10 * a (n - 3) + a (n - 5) := by exact_mod_cast h
  linarith

theorem generating_function (a : ℕ → ℕ)
    (h1 : a 1 = 16) (h2 : a 2 = 55) (h3 : a 3 = 105)
    (h4 : a 4 = 168) (h5 : a 5 = 252) (h6 : a 6 = 363) (h7 : a 7 = 508)
    (hs : ∀ n : ℕ, a (n + 8) + 10 * a (n + 6) + 5 * a (n + 4) =
      5 * a (n + 7) + 10 * a (n + 5) + a (n + 3)) :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 +
        3 * X ^ 6 := by
  let g : PowerSeries ℚ := PowerSeries.mk fun n => (a (n + 1) : ℚ)
  change g * (1 - X) ^ 5 = _
  have hl : g * (1 - X) ^ 5 =
      g * X ^ 0 - 5 • (g * X ^ 1) + 10 • (g * X ^ 2) - 10 • (g * X ^ 3) +
      5 • (g * X ^ 4) - g * X ^ 5 := by
    simp only [nsmul_eq_mul]
    ring
  have hr : (16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 -
      8 * X ^ 5 + 3 * X ^ 6 : PowerSeries ℚ) =
      16 • X ^ 0 - 25 • X ^ 1 - 10 • X ^ 2 + 33 • X ^ 3 - 8 • X ^ 4 -
      8 • X ^ 5 + 3 • X ^ 6 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_nsmul]
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk,
        h1, h2, h3, h4, h5, h6, h7]
  · have hc (k : ℕ) (hk : k ≤ n) : coeff n (g * X ^ k) = (a (n - k + 1) : ℚ) := by
      rw [coeff_mul_X_pow', if_pos hk]
      simp only [g, coeff_mk]
    have hx (k : ℕ) (hk : k < n) : coeff n (X ^ k : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    simp (disch := omega) only [hc, hx, nsmul_eq_mul, mul_zero, add_zero,
      sub_zero, Nat.sub_zero]
    norm_num only [Nat.cast_ofNat]
    have hrec := hs (n - 7)
    have heq (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 8) : n - 7 + k = n - (8 - k) + 1 := by omega
    rw [heq 8 (by omega), heq 6 (by omega), heq 4 (by omega),
      heq 7 (by omega), heq 5 (by omega), heq 3 (by omega)] at hrec
    norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at hrec
    have hq : (a (n + 1) : ℚ) + 10 * a (n - 2 + 1) + 5 * a (n - 4 + 1) =
      5 * a (n - 1 + 1) + 10 * a (n - 3 + 1) + a (n - 5 + 1) := by
      exact_mod_cast hrec
    linarith

theorem of_recurrence (a : ℕ → ℕ)
    (h1 : a 1 = 16) (h2 : a 2 = 55) (h3 : a 3 = 105)
    (h4 : a 4 = 168) (h5 : a 5 = 252) (h6 : a 6 = 363) (h7 : a 7 = 508)
    (hs : ∀ n : ℕ, a (n + 8) + 10 * a (n + 6) + 5 * a (n + 4) =
      5 * a (n + 7) + 10 * a (n + 5) + a (n + 3)) :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 + 3 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  exact ⟨generating_function a h1 h2 h3 h4 h5 h6 h7 hs, integer_recurrence a hs⟩

end A224040Formula

namespace A224040Proof
open OMA.S_oeis_a224040 A224040Table A224040Certificate PowerSeries

theorem a_eq_indexed (n : ℕ) : a n = indexedCount n :=
  a_eq_paths run_correct state succ accepted 0 local_table (fun _ => rfl) state_zero n

theorem result :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 + 3 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  have ha : a = indexedCount := funext a_eq_indexed
  rw [ha]
  exact A224040Formula.of_recurrence indexedCount initial_1 initial_2 initial_3
    initial_4 initial_5 initial_6 initial_7 indexed_recurrence

end A224040Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a224040.main := by
  exact A224040Proof.result
