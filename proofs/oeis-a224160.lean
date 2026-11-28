import OMAStatements.S_oeis_a224160
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn
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
A224160: four-row binary arrays with unimodal rows and diagonals and
nondecreasing antidiagonals. Four three-phase row automata and a
three-column history give a closed table of 488 states. The exact array
predicate is equivalent to successful runs. Fifteen kernel-checked count
vectors establish the ninth finite-difference identity from suffix length
five; linear induction extends it to all lengths.

Source: https://oeis.org/A224160
Array definition: R. H. Hardin (2013).
Generating-function and recurrence conjectures: Colin Barker (2018).
The canonical statement, contributed by @physbuzz, is unchanged.
-/

namespace A224160Proof
open OMA.S_oeis_a224160
abbrev Col := Fin 4 → Fin 2

def phaseOK (p : Fin 3) (b : Fin 2) : Prop := ¬ (p = 2 ∧ b = 1)
instance (p : Fin 3) (b : Fin 2) : Decidable (phaseOK p b) :=
  inferInstanceAs (Decidable (¬ (p = 2 ∧ b = 1)))
def phaseNext (p : Fin 3) (b : Fin 2) : Fin 3 :=
  if b = 1 then 1 else if p = 1 then 2 else p
def phaseStep (p : Fin 3) (b : Fin 2) : Option (Fin 3) :=
  if phaseOK p b then some (phaseNext p b) else none
def foldPhase : List (Fin 2) → Option (Fin 3)
  | [] => some 0
  | b :: l => (foldPhase l).bind (fun p => phaseStep p b)

def uniCheck (l : List ℕ) : Bool :=
  (List.range (l.length + 1)).any fun m =>
    decide ((l.take m).Pairwise (· ≤ ·) ∧ (l.drop m).Pairwise (· ≥ ·))
structure State where
  phase : Fin 4 → Fin 3
  history : List Col

def columnValues (c : Col) : List ℕ := List.ofFn fun i => (c i).val

theorem columnValues_injective : Function.Injective columnValues := by
  intro c d h
  have hf := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun hf i)

theorem state_eq_iff (s t : State) : s = t ↔
    (∀ i, s.phase i = t.phase i) ∧
      s.history.map columnValues = t.history.map columnValues := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, rfl⟩
  · rintro ⟨hp, hh⟩
    have hp' : s.phase = t.phase := funext hp
    have hh' : s.history = t.history :=
      (List.map_injective_iff.mpr columnValues_injective) hh
    cases s
    cases t
    cases hp'
    cases hh'
    rfl

instance instDecidableEqState : DecidableEq State := fun s t =>
  decidable_of_iff _ (state_eq_iff s t).symm


def start : State := ⟨fun _ => 0, []⟩
def adjacent (u v : Col) : Prop := ∀ i : Fin 3, v i.castSucc ≤ u i.succ
instance (u v : Col) : Decidable (adjacent u v) :=
  inferInstanceAs (Decidable (∀ i : Fin 3, v i.castSucc ≤ u i.succ))
def headOK (s : State) (c : Col) : Prop :=
  match s.history with
  | [] => True
  | d :: _ => adjacent c d
instance instDecidableHeadOK : (s : State) → (c : Col) → Decidable (headOK s c)
  | ⟨_, []⟩, _ => inferInstanceAs (Decidable True)
  | ⟨_, d :: _⟩, c => inferInstanceAs (Decidable (adjacent c d))
def localOK (s : State) (c : Col) : Prop :=
  headOK s c ∧ (∀ i : Fin 4, phaseOK (s.phase i) (c i)) ∧
    (∀ i : Fin 4, uniCheck (diagFrom (c :: s.history) i.val) = true)
instance (s : State) (c : Col) : Decidable (localOK s c) :=
  inferInstanceAs (Decidable (headOK s c ∧ (∀ i : Fin 4, phaseOK (s.phase i) (c i)) ∧
    (∀ i : Fin 4, uniCheck (diagFrom (c :: s.history) i.val) = true)))
def nextState (s : State) (c : Col) : State :=
  ⟨fun i => phaseNext (s.phase i) (c i), (c :: s.history).take 3⟩
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
end A224160Proof

namespace A224160Proof
open OMA.S_oeis_a224160

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

theorem unimodal_zero_cons (l : List ℕ) : Unimodal (0 :: l) ↔ Unimodal l := by
  constructor
  · exact unimodal_tail
  · rintro ⟨m, hu, hd⟩
    refine ⟨m + 1, ?_, ?_⟩
    · simpa using List.pairwise_cons.mpr ⟨fun _ _ => Nat.zero_le _, hu⟩
    · simpa using hd

theorem decreasing_zero_cons (l : List ℕ) :
    (0 :: l).Pairwise (· ≥ ·) ↔ ∀ x ∈ l, x = 0 := by
  constructor
  · intro h x hx
    have := (List.pairwise_cons.mp h).1 x hx
    omega
  · intro h
    apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_of_forall_mem_list ?_⟩
    · intro x hx
      rw [h x hx]
    · intro x hx y hy
      rw [h x hx, h y hy]

theorem decreasing_one_cons {l : List ℕ} (hl : ∀ x ∈ l, x ≤ 1) :
    (1 :: l).Pairwise (· ≥ ·) ↔ l.Pairwise (· ≥ ·) := by
  rw [List.pairwise_cons]
  exact and_iff_right hl

theorem unimodal_one_cons {l : List ℕ} (hl : ∀ x ∈ l, x ≤ 1) :
    Unimodal (1 :: l) ↔ l.Pairwise (· ≥ ·) := by
  constructor
  · rintro ⟨m, hu, hd⟩
    cases m with
    | zero => simpa using hd.tail
    | succ m =>
        have hu' : ∀ x ∈ l.take m, 1 ≤ x :=
          (List.pairwise_cons.mp (by simpa using hu)).1
        have hd' : (l.drop m).Pairwise (· ≥ ·) := by simpa using hd
        rw [← List.take_append_drop m l, List.pairwise_append]
        refine ⟨List.pairwise_of_forall_mem_list ?_, hd', ?_⟩
        · intro x hx y hy
          exact (hl y (List.mem_of_mem_take hy)).trans (hu' x hx)
        · intro x hx y hy
          exact (hl y (List.mem_of_mem_drop hy)).trans (hu' x hx)
  · intro h
    exact ⟨1, by simp, by simpa using h⟩

end A224160Proof

namespace A224160Proof
open OMA.S_oeis_a224160

theorem isSolution_tail {c : Col} {l : List Col}
    (h : IsSolution (c :: l)) : IsSolution l := by
  refine ⟨?_, h.2.1.tail, ?_, ?_⟩
  · intro i
    apply unimodal_tail
    simpa only [List.map_cons] using h.1 i
  · intro i hi
    interval_cases i
    · simpa only [List.drop_succ_cons, List.drop_zero] using h.2.2.2 1
    · apply unimodal_tail (b := (c 0 : ℕ))
      simpa [diagFrom] using h.2.2.1 0 (by decide)
    · apply unimodal_tail (b := (c 1 : ℕ))
      simpa [diagFrom] using h.2.2.1 1 (by decide)
    · apply unimodal_tail (b := (c 2 : ℕ))
      simpa [diagFrom] using h.2.2.1 2 (by decide)
  · intro j
    simpa only [List.drop_succ_cons] using h.2.2.2 (j + 1)

theorem isSolution_cons_iff (c : Col) (l : List Col) :
    IsSolution (c :: l) ↔ (∀ d ∈ l.head?, adjacent c d) ∧
      (∀ i : Fin 4, Unimodal ((c i : ℕ) :: l.map fun d => (d i : ℕ))) ∧
      (∀ i : Fin 4, Unimodal (diagFrom (c :: l) i.val)) ∧ IsSolution l := by
  constructor
  · intro h
    exact ⟨(List.isChain_cons.mp h.2.1).1,
      by simpa only [List.map_cons] using h.1,
      fun i => h.2.2.1 i.val i.isLt, isSolution_tail h⟩
  · rintro ⟨hc, hr, hd, hl⟩
    refine ⟨?_, List.isChain_cons.mpr ⟨hc, hl.2.1⟩, ?_, ?_⟩
    · simpa only [List.map_cons] using hr
    · intro i hi
      exact hd ⟨i, hi⟩
    · intro j
      cases j with
      | zero => simpa using hd (0 : Fin 4)
      | succ j => simpa only [List.drop_succ_cons] using hl.2.2.2 j

theorem diagFrom_take (l : List Col) (i k : ℕ) (hk : 4 ≤ i + k) :
    diagFrom (l.take k) i = diagFrom l i := by
  induction l generalizing i k with
  | nil => simp [diagFrom]
  | cons c l ih =>
    cases k with
    | zero => simp [diagFrom, show ¬ i < 4 by omega]
    | succ k =>
      simp only [List.take_succ_cons, diagFrom]
      split_ifs with hi
      · rw [ih (i + 1) k (by omega)]
      · rfl

theorem diagFrom_cons_take (c : Col) (l : List Col) (i : Fin 4) :
    diagFrom (c :: l.take 3) i.val = diagFrom (c :: l) i.val := by
  simpa only [List.take_succ_cons] using diagFrom_take (c :: l) i.val 4 (by omega)

end A224160Proof

namespace A224160Proof
open OMA.S_oeis_a224160

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

theorem binary_bound (l : List (Fin 2)) :
    ∀ x ∈ l.map (fun b : Fin 2 => (b : ℕ)), x ≤ 1 := by
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  have := b.is_lt
  omega

theorem binary_all_zero (l : List (Fin 2)) :
    (∀ x ∈ l.map (fun b : Fin 2 => (b : ℕ)), x = 0) ↔ ∀ b ∈ l, b = 0 := by
  constructor
  · intro h b hb
    apply Fin.ext
    exact h b (List.mem_map.mpr ⟨b, hb, rfl⟩)
  · intro h x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [h b hb]
    rfl

theorem foldPhase_spec (l : List (Fin 2)) :
    (foldPhase l = some 0 ↔ ∀ b ∈ l, b = 0) ∧
    ((foldPhase l = some 0 ∨ foldPhase l = some 1) ↔
      (l.map (fun b : Fin 2 => (b : ℕ))).Pairwise (· ≥ ·)) ∧
    ((foldPhase l).isSome = true ↔ Unimodal (l.map (fun b : Fin 2 => (b : ℕ)))) := by
  induction l with
  | nil => simp [foldPhase, unimodal_nil]
  | cons b l ih =>
      rcases ih with ⟨hz, hd, hu⟩
      fin_cases b
      · norm_num only [foldPhase, List.map_cons, List.forall_mem_cons,
          decreasing_zero_cons, unimodal_zero_cons]
        simp only [binary_all_zero, ← hz, ← hu]
        cases he : foldPhase l with
        | none => decide
        | some p => fin_cases p <;> decide
      · norm_num only [foldPhase, List.map_cons, List.forall_mem_cons]
        simp only [decreasing_one_cons (binary_bound l), unimodal_one_cons (binary_bound l),
          ← hd, ← hz]
        cases he : foldPhase l with
        | none => decide
        | some p => fin_cases p <;> decide

theorem foldPhase_correct (l : List (Fin 2)) :
    (foldPhase l).isSome = true ↔ Unimodal (l.map (fun b : Fin 2 => (b : ℕ))) :=
  (foldPhase_spec l).2.2

theorem phaseOK_iff {l : List (Fin 2)} {p : Fin 3} (h : foldPhase l = some p)
    (b : Fin 2) : phaseOK p b ↔ Unimodal ((b : ℕ) :: l.map (fun x : Fin 2 => (x : ℕ))) := by
  have hc := foldPhase_correct (b :: l)
  by_cases hok : phaseOK p b <;> simpa [foldPhase, h, phaseStep, hok] using hc

end A224160Proof

namespace A224160Proof

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

end A224160Proof

namespace A224160Proof
open OMA.S_oeis_a224160

def Tracks (s : State) (l : List Col) : Prop :=
  s.history = l.take 3 ∧
    ∀ i : Fin 4, foldPhase (l.map fun c => c i) = some (s.phase i)

theorem run_tracks {l : List Col} {s : State} (h : run l = some s) : Tracks s l := by
  induction l generalizing s with
  | nil =>
      have hs : start = s := by simpa [run] using h
      subst s
      exact ⟨rfl, fun _ => rfl⟩
  | cons c l ih =>
      cases ht : run l with
      | none => simp [run, ht] at h
      | some t =>
          have hs : step t c = some s := by simpa [run, ht] using h
          have htrack := ih ht
          by_cases hok : localOK t c
          · have he : nextState t c = s := by simpa [step, hok] using hs
            subst s
            refine ⟨?_, ?_⟩
            · simp [nextState, htrack.1, List.take_take]
            · intro i
              simp only [List.map_cons, foldPhase, htrack.2 i, Option.bind_some]
              simp [phaseStep, hok.2.1 i, nextState]
          · simp [step, hok] at hs

theorem localOK_iff_tracks {l : List Col} {s : State} (ht : Tracks s l) (c : Col) :
    localOK s c ↔ (∀ d ∈ l.head?, adjacent c d) ∧
      (∀ i : Fin 4, Unimodal ((c i : ℕ) :: l.map fun d => (d i : ℕ))) ∧
      (∀ i : Fin 4, Unimodal (diagFrom (c :: l) i.val)) := by
  simp only [localOK, ht.1, uniCheck_eq_true_iff, diagFrom_cons_take]
  apply and_congr
  · cases l <;> simp [headOK, ht.1]
  · apply and_congr_left
    intro _
    apply forall_congr'
    intro i
    simpa only [List.map_map, Function.comp_def] using phaseOK_iff (ht.2 i) (c i)

theorem run_correct (l : List Col) : (run l).isSome = true ↔ IsSolution l := by
  induction l with
  | nil => simp [run, IsSolution, diagFrom, unimodal_nil]
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

end A224160Proof

namespace A224160Count
variable {S : Type*}
def paths (succ : S → List S) (accepted : S → ℕ) : ℕ → S → ℕ
  | 0, s => accepted s
  | n + 1, s => ((succ s).map (paths succ accepted n)).sum

lemma sum_balance (L : List S) (f : Fin 15 → S → ℕ)
    (h : ∀ s, f 14 s + 36 * f 12 s + 126 * f 10 s + 84 * f 8 s + 9 * f 6 s =
      9 * f 13 s + 84 * f 11 s + 126 * f 9 s + 36 * f 7 s + f 5 s) :
    (L.map (f 14)).sum + 36 * (L.map (f 12)).sum + 126 * (L.map (f 10)).sum + 84 * (L.map (f 8)).sum + 9 * (L.map (f 6)).sum =
      9 * (L.map (f 13)).sum + 84 * (L.map (f 11)).sum + 126 * (L.map (f 9)).sum + 36 * (L.map (f 7)).sum + (L.map (f 5)).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs := h s
    omega

theorem paths_recurrence (succ : S → List S) (accepted : S → ℕ)
    (hbase : ∀ s, paths succ accepted 14 s + 36 * paths succ accepted 12 s + 126 * paths succ accepted 10 s + 84 * paths succ accepted 8 s + 9 * paths succ accepted 6 s =
      9 * paths succ accepted 13 s + 84 * paths succ accepted 11 s + 126 * paths succ accepted 9 s + 36 * paths succ accepted 7 s + paths succ accepted 5 s) :
    ∀ n s, paths succ accepted (n + 14) s + 36 * paths succ accepted (n + 12) s + 126 * paths succ accepted (n + 10) s + 84 * paths succ accepted (n + 8) s + 9 * paths succ accepted (n + 6) s =
      9 * paths succ accepted (n + 13) s + 84 * paths succ accepted (n + 11) s + 126 * paths succ accepted (n + 9) s + 36 * paths succ accepted (n + 7) s + paths succ accepted (n + 5) s := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accepted (n + 14))).sum + 36 * ((succ s).map (paths succ accepted (n + 12))).sum + 126 * ((succ s).map (paths succ accepted (n + 10))).sum + 84 * ((succ s).map (paths succ accepted (n + 8))).sum + 9 * ((succ s).map (paths succ accepted (n + 6))).sum =
      9 * ((succ s).map (paths succ accepted (n + 13))).sum + 84 * ((succ s).map (paths succ accepted (n + 11))).sum + 126 * ((succ s).map (paths succ accepted (n + 9))).sum + 36 * ((succ s).map (paths succ accepted (n + 7))).sum + ((succ s).map (paths succ accepted (n + 5))).sum
    exact sum_balance (succ s) (fun k => paths succ accepted (n + k.val)) ih

theorem paths_eq_vectors (succ : S → List S) (accepted : S → ℕ)
    (v : Fin 15 → S → ℕ) (hzero : ∀ s, v 0 s = accepted s)
    (hnext : ∀ k : Fin 14, ∀ s,
      ((succ s).map (v k.castSucc)).sum = v k.succ s) :
    ∀ k : Fin 15, ∀ s, paths succ accepted k.val s = v k s := by
  intro k
  induction k using Fin.induction with
  | zero => intro s; exact (hzero s).symm
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accepted k.val)).sum = v k.succ s
    rw [show paths succ accepted k.val = v k.castSucc from funext ih]
    exact hnext k s
end A224160Count

namespace A224160Proof
open OMA.S_oeis_a224160

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
    ∀ n i, suffixCount (state i) n = A224160Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_allCols, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A224160Count.paths succ accepted n from funext ih]
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
    a n = A224160Count.paths succ accepted n initial := by
  rw [a_eq_suffix hcorrect, ← hstart]
  exact suffixCount_eq_paths state succ accepted hstep haccept n initial

end A224160Proof

namespace A224160Table
open A224160Proof
def codes (i : Fin 488) : ℕ × List ℕ :=
  (if i.val < 244 then (if i.val < 122 then (if i.val < 61 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (0, []) else (if i.val < 2 then (0, [0]) else (1, [1]))) else (if i.val < 5 then (if i.val < 4 then (3, [2]) else (4, [3])) else (if i.val < 6 then (9, [4]) else (10, [5])))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then (12, [6]) else (13, [7])) else (if i.val < 10 then (27, [8]) else (28, [9]))) else (if i.val < 13 then (if i.val < 12 then (30, [10]) else (31, [11])) else (if i.val < 14 then (36, [12]) else (37, [13]))))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then (39, [14]) else (if i.val < 17 then (40, [15]) else (0, [0, 0]))) else (if i.val < 20 then (if i.val < 19 then (1, [1, 0]) else (3, [2, 0])) else (if i.val < 21 then (4, [3, 0]) else (9, [4, 0])))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then (10, [5, 0]) else (12, [6, 0])) else (if i.val < 25 then (13, [7, 0]) else (27, [8, 0]))) else (if i.val < 28 then (if i.val < 27 then (28, [9, 0]) else (30, [10, 0])) else (if i.val < 29 then (31, [11, 0]) else (36, [12, 0])))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then (37, [13, 0]) else (if i.val < 32 then (39, [14, 0]) else (40, [15, 0]))) else (if i.val < 35 then (if i.val < 34 then (5, [2, 1]) else (4, [3, 1])) else (if i.val < 36 then (14, [6, 1]) else (13, [7, 1])))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then (32, [10, 1]) else (31, [11, 1])) else (if i.val < 40 then (41, [14, 1]) else (40, [15, 1]))) else (if i.val < 43 then (if i.val < 42 then (15, [4, 2]) else (16, [5, 2])) else (if i.val < 44 then (12, [6, 2]) else (13, [7, 2]))))) else (if i.val < 53 then (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (42, [12, 2]) else (43, [13, 2])) else (if i.val < 48 then (39, [14, 2]) else (40, [15, 2]))) else (if i.val < 51 then (if i.val < 50 then (14, [6, 3]) else (13, [7, 3])) else (if i.val < 52 then (41, [14, 3]) else (40, [15, 3])))) else (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then (45, [8, 4]) else (46, [9, 4])) else (if i.val < 56 then (48, [10, 4]) else (49, [11, 4]))) else (if i.val < 59 then (if i.val < 58 then (36, [12, 4]) else (37, [13, 4])) else (if i.val < 60 then (39, [14, 4]) else (40, [15, 4]))))))) else (if i.val < 91 then (if i.val < 76 then (if i.val < 68 then (if i.val < 64 then (if i.val < 62 then (50, [10, 5]) else (if i.val < 63 then (49, [11, 5]) else (41, [14, 5]))) else (if i.val < 66 then (if i.val < 65 then (40, [15, 5]) else (42, [12, 6])) else (if i.val < 67 then (43, [13, 6]) else (39, [14, 6])))) else (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then (40, [15, 6]) else (41, [14, 7])) else (if i.val < 71 then (40, [15, 7]) else (54, [0, 8]))) else (if i.val < 74 then (if i.val < 73 then (55, [1, 8]) else (57, [2, 8])) else (if i.val < 75 then (58, [3, 8]) else (63, [4, 8]))))) else (if i.val < 83 then (if i.val < 79 then (if i.val < 77 then (64, [5, 8]) else (if i.val < 78 then (66, [6, 8]) else (67, [7, 8]))) else (if i.val < 81 then (if i.val < 80 then (27, [8, 8]) else (28, [9, 8])) else (if i.val < 82 then (30, [10, 8]) else (31, [11, 8])))) else (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then (36, [12, 8]) else (37, [13, 8])) else (if i.val < 86 then (39, [14, 8]) else (40, [15, 8]))) else (if i.val < 89 then (if i.val < 88 then (59, [2, 9]) else (58, [3, 9])) else (if i.val < 90 then (68, [6, 9]) else (67, [7, 9])))))) else (if i.val < 106 then (if i.val < 98 then (if i.val < 94 then (if i.val < 92 then (32, [10, 9]) else (if i.val < 93 then (31, [11, 9]) else (41, [14, 9]))) else (if i.val < 96 then (if i.val < 95 then (40, [15, 9]) else (69, [4, 10])) else (if i.val < 97 then (70, [5, 10]) else (66, [6, 10])))) else (if i.val < 102 then (if i.val < 100 then (if i.val < 99 then (67, [7, 10]) else (42, [12, 10])) else (if i.val < 101 then (43, [13, 10]) else (39, [14, 10]))) else (if i.val < 104 then (if i.val < 103 then (40, [15, 10]) else (68, [6, 11])) else (if i.val < 105 then (67, [7, 11]) else (41, [14, 11]))))) else (if i.val < 114 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then (40, [15, 11]) else (45, [8, 12])) else (if i.val < 109 then (46, [9, 12]) else (48, [10, 12]))) else (if i.val < 112 then (if i.val < 111 then (49, [11, 12]) else (36, [12, 12])) else (if i.val < 113 then (37, [13, 12]) else (39, [14, 12])))) else (if i.val < 118 then (if i.val < 116 then (if i.val < 115 then (40, [15, 12]) else (50, [10, 13])) else (if i.val < 117 then (49, [11, 13]) else (41, [14, 13]))) else (if i.val < 120 then (if i.val < 119 then (40, [15, 13]) else (42, [12, 14])) else (if i.val < 121 then (43, [13, 14]) else (39, [14, 14])))))))) else (if i.val < 183 then (if i.val < 152 then (if i.val < 137 then (if i.val < 129 then (if i.val < 125 then (if i.val < 123 then (40, [15, 14]) else (if i.val < 124 then (41, [14, 15]) else (40, [15, 15]))) else (if i.val < 127 then (if i.val < 126 then (0, [0, 0, 0]) else (1, [1, 0, 0])) else (if i.val < 128 then (3, [2, 0, 0]) else (4, [3, 0, 0])))) else (if i.val < 133 then (if i.val < 131 then (if i.val < 130 then (9, [4, 0, 0]) else (10, [5, 0, 0])) else (if i.val < 132 then (12, [6, 0, 0]) else (13, [7, 0, 0]))) else (if i.val < 135 then (if i.val < 134 then (27, [8, 0, 0]) else (28, [9, 0, 0])) else (if i.val < 136 then (30, [10, 0, 0]) else (31, [11, 0, 0]))))) else (if i.val < 144 then (if i.val < 140 then (if i.val < 138 then (36, [12, 0, 0]) else (if i.val < 139 then (37, [13, 0, 0]) else (39, [14, 0, 0]))) else (if i.val < 142 then (if i.val < 141 then (40, [15, 0, 0]) else (5, [2, 1, 0])) else (if i.val < 143 then (4, [3, 1, 0]) else (14, [6, 1, 0])))) else (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then (13, [7, 1, 0]) else (32, [10, 1, 0])) else (if i.val < 147 then (31, [11, 1, 0]) else (41, [14, 1, 0]))) else (if i.val < 150 then (if i.val < 149 then (40, [15, 1, 0]) else (15, [4, 2, 0])) else (if i.val < 151 then (16, [5, 2, 0]) else (12, [6, 2, 0])))))) else (if i.val < 167 then (if i.val < 159 then (if i.val < 155 then (if i.val < 153 then (13, [7, 2, 0]) else (if i.val < 154 then (42, [12, 2, 0]) else (43, [13, 2, 0]))) else (if i.val < 157 then (if i.val < 156 then (39, [14, 2, 0]) else (40, [15, 2, 0])) else (if i.val < 158 then (14, [6, 3, 0]) else (13, [7, 3, 0])))) else (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then (41, [14, 3, 0]) else (40, [15, 3, 0])) else (if i.val < 162 then (45, [8, 4, 0]) else (46, [9, 4, 0]))) else (if i.val < 165 then (if i.val < 164 then (48, [10, 4, 0]) else (49, [11, 4, 0])) else (if i.val < 166 then (36, [12, 4, 0]) else (37, [13, 4, 0]))))) else (if i.val < 175 then (if i.val < 171 then (if i.val < 169 then (if i.val < 168 then (39, [14, 4, 0]) else (40, [15, 4, 0])) else (if i.val < 170 then (50, [10, 5, 0]) else (49, [11, 5, 0]))) else (if i.val < 173 then (if i.val < 172 then (41, [14, 5, 0]) else (40, [15, 5, 0])) else (if i.val < 174 then (42, [12, 6, 0]) else (43, [13, 6, 0])))) else (if i.val < 179 then (if i.val < 177 then (if i.val < 176 then (39, [14, 6, 0]) else (40, [15, 6, 0])) else (if i.val < 178 then (41, [14, 7, 0]) else (40, [15, 7, 0]))) else (if i.val < 181 then (if i.val < 180 then (54, [0, 8, 0]) else (55, [1, 8, 0])) else (if i.val < 182 then (57, [2, 8, 0]) else (58, [3, 8, 0]))))))) else (if i.val < 213 then (if i.val < 198 then (if i.val < 190 then (if i.val < 186 then (if i.val < 184 then (63, [4, 8, 0]) else (if i.val < 185 then (64, [5, 8, 0]) else (66, [6, 8, 0]))) else (if i.val < 188 then (if i.val < 187 then (67, [7, 8, 0]) else (27, [8, 8, 0])) else (if i.val < 189 then (28, [9, 8, 0]) else (30, [10, 8, 0])))) else (if i.val < 194 then (if i.val < 192 then (if i.val < 191 then (31, [11, 8, 0]) else (36, [12, 8, 0])) else (if i.val < 193 then (37, [13, 8, 0]) else (39, [14, 8, 0]))) else (if i.val < 196 then (if i.val < 195 then (40, [15, 8, 0]) else (59, [2, 9, 0])) else (if i.val < 197 then (58, [3, 9, 0]) else (68, [6, 9, 0]))))) else (if i.val < 205 then (if i.val < 201 then (if i.val < 199 then (67, [7, 9, 0]) else (if i.val < 200 then (32, [10, 9, 0]) else (31, [11, 9, 0]))) else (if i.val < 203 then (if i.val < 202 then (41, [14, 9, 0]) else (40, [15, 9, 0])) else (if i.val < 204 then (69, [4, 10, 0]) else (70, [5, 10, 0])))) else (if i.val < 209 then (if i.val < 207 then (if i.val < 206 then (66, [6, 10, 0]) else (67, [7, 10, 0])) else (if i.val < 208 then (42, [12, 10, 0]) else (43, [13, 10, 0]))) else (if i.val < 211 then (if i.val < 210 then (39, [14, 10, 0]) else (40, [15, 10, 0])) else (if i.val < 212 then (68, [6, 11, 0]) else (67, [7, 11, 0])))))) else (if i.val < 228 then (if i.val < 220 then (if i.val < 216 then (if i.val < 214 then (41, [14, 11, 0]) else (if i.val < 215 then (40, [15, 11, 0]) else (45, [8, 12, 0]))) else (if i.val < 218 then (if i.val < 217 then (46, [9, 12, 0]) else (48, [10, 12, 0])) else (if i.val < 219 then (49, [11, 12, 0]) else (36, [12, 12, 0])))) else (if i.val < 224 then (if i.val < 222 then (if i.val < 221 then (37, [13, 12, 0]) else (39, [14, 12, 0])) else (if i.val < 223 then (40, [15, 12, 0]) else (50, [10, 13, 0]))) else (if i.val < 226 then (if i.val < 225 then (49, [11, 13, 0]) else (41, [14, 13, 0])) else (if i.val < 227 then (40, [15, 13, 0]) else (42, [12, 14, 0]))))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (if i.val < 229 then (43, [13, 14, 0]) else (39, [14, 14, 0])) else (if i.val < 231 then (40, [15, 14, 0]) else (41, [14, 15, 0]))) else (if i.val < 234 then (if i.val < 233 then (40, [15, 15, 0]) else (17, [4, 2, 1])) else (if i.val < 235 then (14, [6, 2, 1]) else (44, [12, 2, 1])))) else (if i.val < 240 then (if i.val < 238 then (if i.val < 237 then (41, [14, 2, 1]) else (14, [6, 3, 1])) else (if i.val < 239 then (13, [7, 3, 1]) else (41, [14, 3, 1]))) else (if i.val < 242 then (if i.val < 241 then (40, [15, 3, 1]) else (44, [12, 6, 1])) else (if i.val < 243 then (41, [14, 6, 1]) else (41, [14, 7, 1]))))))))) else (if i.val < 366 then (if i.val < 305 then (if i.val < 274 then (if i.val < 259 then (if i.val < 251 then (if i.val < 247 then (if i.val < 245 then (40, [15, 7, 1]) else (if i.val < 246 then (71, [4, 10, 1]) else (68, [6, 10, 1]))) else (if i.val < 249 then (if i.val < 248 then (44, [12, 10, 1]) else (41, [14, 10, 1])) else (if i.val < 250 then (68, [6, 11, 1]) else (67, [7, 11, 1])))) else (if i.val < 255 then (if i.val < 253 then (if i.val < 252 then (41, [14, 11, 1]) else (40, [15, 11, 1])) else (if i.val < 254 then (44, [12, 14, 1]) else (41, [14, 14, 1]))) else (if i.val < 257 then (if i.val < 256 then (41, [14, 15, 1]) else (40, [15, 15, 1])) else (if i.val < 258 then (51, [8, 4, 2]) else (52, [9, 4, 2]))))) else (if i.val < 266 then (if i.val < 262 then (if i.val < 260 then (42, [12, 4, 2]) else (if i.val < 261 then (43, [13, 4, 2]) else (42, [12, 6, 2]))) else (if i.val < 264 then (if i.val < 263 then (43, [13, 6, 2]) else (39, [14, 6, 2])) else (if i.val < 265 then (40, [15, 6, 2]) else (41, [14, 7, 2])))) else (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then (40, [15, 7, 2]) else (51, [8, 12, 2])) else (if i.val < 269 then (52, [9, 12, 2]) else (42, [12, 12, 2]))) else (if i.val < 272 then (if i.val < 271 then (43, [13, 12, 2]) else (42, [12, 14, 2])) else (if i.val < 273 then (43, [13, 14, 2]) else (39, [14, 14, 2])))))) else (if i.val < 289 then (if i.val < 281 then (if i.val < 277 then (if i.val < 275 then (40, [15, 14, 2]) else (if i.val < 276 then (41, [14, 15, 2]) else (40, [15, 15, 2]))) else (if i.val < 279 then (if i.val < 278 then (44, [12, 6, 3]) else (41, [14, 6, 3])) else (if i.val < 280 then (41, [14, 7, 3]) else (40, [15, 7, 3])))) else (if i.val < 285 then (if i.val < 283 then (if i.val < 282 then (44, [12, 14, 3]) else (41, [14, 14, 3])) else (if i.val < 284 then (41, [14, 15, 3]) else (40, [15, 15, 3]))) else (if i.val < 287 then (if i.val < 286 then (72, [0, 8, 4]) else (75, [2, 8, 4])) else (if i.val < 288 then (45, [8, 8, 4]) else (48, [10, 8, 4]))))) else (if i.val < 297 then (if i.val < 293 then (if i.val < 291 then (if i.val < 290 then (77, [2, 9, 4]) else (50, [10, 9, 4])) else (if i.val < 292 then (45, [8, 12, 4]) else (48, [10, 12, 4]))) else (if i.val < 295 then (if i.val < 294 then (36, [12, 12, 4]) else (39, [14, 12, 4])) else (if i.val < 296 then (50, [10, 13, 4]) else (41, [14, 13, 4])))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then (42, [12, 14, 4]) else (43, [13, 14, 4])) else (if i.val < 300 then (39, [14, 14, 4]) else (40, [15, 14, 4]))) else (if i.val < 303 then (if i.val < 302 then (41, [14, 15, 4]) else (40, [15, 15, 4])) else (if i.val < 304 then (44, [12, 14, 5]) else (41, [14, 14, 5]))))))) else (if i.val < 335 then (if i.val < 320 then (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (41, [14, 15, 5]) else (if i.val < 307 then (40, [15, 15, 5]) else (51, [8, 12, 6]))) else (if i.val < 310 then (if i.val < 309 then (42, [12, 12, 6]) else (42, [12, 14, 6])) else (if i.val < 311 then (43, [13, 14, 6]) else (39, [14, 14, 6])))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then (40, [15, 14, 6]) else (41, [14, 15, 6])) else (if i.val < 315 then (40, [15, 15, 6]) else (44, [12, 14, 7]))) else (if i.val < 318 then (if i.val < 317 then (41, [14, 14, 7]) else (41, [14, 15, 7])) else (if i.val < 319 then (40, [15, 15, 7]) else (54, [0, 0, 8]))))) else (if i.val < 327 then (if i.val < 323 then (if i.val < 321 then (55, [1, 0, 8]) else (if i.val < 322 then (63, [4, 0, 8]) else (64, [5, 0, 8]))) else (if i.val < 325 then (if i.val < 324 then (69, [4, 2, 8]) else (70, [5, 2, 8])) else (if i.val < 326 then (54, [0, 8, 8]) else (55, [1, 8, 8])))) else (if i.val < 331 then (if i.val < 329 then (if i.val < 328 then (63, [4, 8, 8]) else (64, [5, 8, 8])) else (if i.val < 330 then (27, [8, 8, 8]) else (28, [9, 8, 8]))) else (if i.val < 333 then (if i.val < 332 then (36, [12, 8, 8]) else (37, [13, 8, 8])) else (if i.val < 334 then (69, [4, 10, 8]) else (70, [5, 10, 8])))))) else (if i.val < 350 then (if i.val < 342 then (if i.val < 338 then (if i.val < 336 then (42, [12, 10, 8]) else (if i.val < 337 then (43, [13, 10, 8]) else (45, [8, 12, 8]))) else (if i.val < 340 then (if i.val < 339 then (46, [9, 12, 8]) else (48, [10, 12, 8])) else (if i.val < 341 then (49, [11, 12, 8]) else (36, [12, 12, 8])))) else (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then (37, [13, 12, 8]) else (39, [14, 12, 8])) else (if i.val < 345 then (40, [15, 12, 8]) else (50, [10, 13, 8]))) else (if i.val < 348 then (if i.val < 347 then (49, [11, 13, 8]) else (41, [14, 13, 8])) else (if i.val < 349 then (40, [15, 13, 8]) else (42, [12, 14, 8]))))) else (if i.val < 358 then (if i.val < 354 then (if i.val < 352 then (if i.val < 351 then (43, [13, 14, 8]) else (39, [14, 14, 8])) else (if i.val < 353 then (40, [15, 14, 8]) else (41, [14, 15, 8]))) else (if i.val < 356 then (if i.val < 355 then (40, [15, 15, 8]) else (71, [4, 2, 9])) else (if i.val < 357 then (71, [4, 10, 9]) else (44, [12, 10, 9])))) else (if i.val < 362 then (if i.val < 360 then (if i.val < 359 then (44, [12, 14, 9]) else (41, [14, 14, 9])) else (if i.val < 361 then (41, [14, 15, 9]) else (40, [15, 15, 9]))) else (if i.val < 364 then (if i.val < 363 then (51, [8, 12, 10]) else (52, [9, 12, 10])) else (if i.val < 365 then (42, [12, 12, 10]) else (43, [13, 12, 10])))))))) else (if i.val < 427 then (if i.val < 396 then (if i.val < 381 then (if i.val < 373 then (if i.val < 369 then (if i.val < 367 then (42, [12, 14, 10]) else (if i.val < 368 then (43, [13, 14, 10]) else (39, [14, 14, 10]))) else (if i.val < 371 then (if i.val < 370 then (40, [15, 14, 10]) else (41, [14, 15, 10])) else (if i.val < 372 then (40, [15, 15, 10]) else (44, [12, 14, 11])))) else (if i.val < 377 then (if i.val < 375 then (if i.val < 374 then (41, [14, 14, 11]) else (41, [14, 15, 11])) else (if i.val < 376 then (40, [15, 15, 11]) else (72, [0, 8, 12]))) else (if i.val < 379 then (if i.val < 378 then (45, [8, 8, 12]) else (45, [8, 12, 12])) else (if i.val < 380 then (48, [10, 12, 12]) else (36, [12, 12, 12]))))) else (if i.val < 388 then (if i.val < 384 then (if i.val < 382 then (39, [14, 12, 12]) else (if i.val < 383 then (50, [10, 13, 12]) else (41, [14, 13, 12]))) else (if i.val < 386 then (if i.val < 385 then (42, [12, 14, 12]) else (43, [13, 14, 12])) else (if i.val < 387 then (39, [14, 14, 12]) else (40, [15, 14, 12])))) else (if i.val < 392 then (if i.val < 390 then (if i.val < 389 then (41, [14, 15, 12]) else (40, [15, 15, 12])) else (if i.val < 391 then (44, [12, 14, 13]) else (41, [14, 14, 13]))) else (if i.val < 394 then (if i.val < 393 then (41, [14, 15, 13]) else (40, [15, 15, 13])) else (if i.val < 395 then (51, [8, 12, 14]) else (42, [12, 12, 14])))))) else (if i.val < 411 then (if i.val < 403 then (if i.val < 399 then (if i.val < 397 then (42, [12, 14, 14]) else (if i.val < 398 then (43, [13, 14, 14]) else (39, [14, 14, 14]))) else (if i.val < 401 then (if i.val < 400 then (40, [15, 14, 14]) else (41, [14, 15, 14])) else (if i.val < 402 then (40, [15, 15, 14]) else (44, [12, 14, 15])))) else (if i.val < 407 then (if i.val < 405 then (if i.val < 404 then (41, [14, 14, 15]) else (41, [14, 15, 15])) else (if i.val < 406 then (40, [15, 15, 15]) else (53, [8, 4, 2]))) else (if i.val < 409 then (if i.val < 408 then (44, [12, 4, 2]) else (44, [12, 6, 2])) else (if i.val < 410 then (41, [14, 6, 2]) else (53, [8, 12, 2]))))) else (if i.val < 419 then (if i.val < 415 then (if i.val < 413 then (if i.val < 412 then (44, [12, 12, 2]) else (44, [12, 14, 2])) else (if i.val < 414 then (41, [14, 14, 2]) else (53, [8, 12, 6]))) else (if i.val < 417 then (if i.val < 416 then (44, [12, 12, 6]) else (44, [12, 14, 6])) else (if i.val < 418 then (41, [14, 14, 6]) else (53, [8, 12, 10])))) else (if i.val < 423 then (if i.val < 421 then (if i.val < 420 then (44, [12, 12, 10]) else (44, [12, 14, 10])) else (if i.val < 422 then (41, [14, 14, 10]) else (53, [8, 12, 14]))) else (if i.val < 425 then (if i.val < 424 then (44, [12, 12, 14]) else (44, [12, 14, 14])) else (if i.val < 426 then (41, [14, 14, 14]) else (78, [0, 8, 4]))))))) else (if i.val < 457 then (if i.val < 442 then (if i.val < 434 then (if i.val < 430 then (if i.val < 428 then (51, [8, 8, 4]) else (if i.val < 429 then (51, [8, 12, 4]) else (42, [12, 12, 4]))) else (if i.val < 432 then (if i.val < 431 then (78, [0, 8, 12]) else (51, [8, 8, 12])) else (if i.val < 433 then (51, [8, 12, 12]) else (42, [12, 12, 12])))) else (if i.val < 438 then (if i.val < 436 then (if i.val < 435 then (72, [0, 0, 8]) else (73, [1, 0, 8])) else (if i.val < 437 then (72, [0, 8, 8]) else (73, [1, 8, 8]))) else (if i.val < 440 then (if i.val < 439 then (45, [8, 8, 8]) else (46, [9, 8, 8])) else (if i.val < 441 then (54, [0, 0, 0]) else (57, [2, 0, 0]))))) else (if i.val < 449 then (if i.val < 445 then (if i.val < 443 then (63, [4, 0, 0]) else (if i.val < 444 then (66, [6, 0, 0]) else (59, [2, 1, 0]))) else (if i.val < 447 then (if i.val < 446 then (68, [6, 1, 0]) else (80, [0, 8, 4])) else (if i.val < 448 then (53, [8, 8, 4]) else (53, [8, 12, 4])))) else (if i.val < 453 then (if i.val < 451 then (if i.val < 450 then (44, [12, 12, 4]) else (80, [0, 8, 12])) else (if i.val < 452 then (53, [8, 8, 12]) else (53, [8, 12, 12]))) else (if i.val < 455 then (if i.val < 454 then (44, [12, 12, 12]) else (78, [0, 0, 8])) else (if i.val < 456 then (79, [1, 0, 8]) else (78, [0, 8, 8])))))) else (if i.val < 472 then (if i.val < 464 then (if i.val < 460 then (if i.val < 458 then (79, [1, 8, 8]) else (if i.val < 459 then (51, [8, 8, 8]) else (52, [9, 8, 8]))) else (if i.val < 462 then (if i.val < 461 then (72, [0, 0, 0]) else (75, [2, 0, 0])) else (if i.val < 463 then (77, [2, 1, 0]) else (55, [1, 0, 0])))) else (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then (58, [3, 0, 0]) else (64, [5, 0, 0])) else (if i.val < 467 then (67, [7, 0, 0]) else (69, [4, 2, 0]))) else (if i.val < 470 then (if i.val < 469 then (70, [5, 2, 0]) else (66, [6, 2, 0])) else (if i.val < 471 then (67, [7, 2, 0]) else (71, [4, 2, 1]))))) else (if i.val < 480 then (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then (68, [6, 2, 1]) else (80, [0, 0, 8])) else (if i.val < 475 then (80, [0, 8, 8]) else (53, [8, 8, 8]))) else (if i.val < 478 then (if i.val < 477 then (78, [0, 0, 0]) else (73, [1, 0, 0])) else (if i.val < 479 then (76, [3, 0, 0]) else (58, [3, 1, 0])))) else (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then (67, [7, 1, 0]) else (68, [6, 3, 0])) else (if i.val < 483 then (67, [7, 3, 0]) else (80, [0, 0, 0]))) else (if i.val < 486 then (if i.val < 485 then (79, [1, 0, 0]) else (76, [3, 1, 0])) else (if i.val < 487 then (68, [6, 3, 1]) else (67, [7, 3, 1]))))))))))
def state (i : Fin 488) : State :=
  ⟨(fun j => ⟨(codes i).1 / 3 ^ j.val % 3, Nat.mod_lt _ (by decide)⟩),
    (codes i).2.map (fun c => decode ⟨c % 16, Nat.mod_lt _ (by decide)⟩)⟩
def succ (i : Fin 488) : List (Fin 488) :=
  (if i.val < 244 then (if i.val < 122 then (if i.val < 61 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] else (if i.val < 2 then [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] else [33, 34, 35, 36, 37, 38, 39, 40])) else (if i.val < 5 then (if i.val < 4 then [41, 42, 43, 44, 45, 46, 47, 48] else [49, 50, 51, 52]) else (if i.val < 6 then [53, 54, 55, 56, 57, 58, 59, 60] else [61, 62, 63, 64]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then [65, 66, 67, 68] else [69, 70]) else (if i.val < 10 then [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86] else [87, 88, 89, 90, 91, 92, 93, 94])) else (if i.val < 13 then (if i.val < 12 then [95, 96, 97, 98, 99, 100, 101, 102] else [103, 104, 105, 106]) else (if i.val < 14 then [107, 108, 109, 110, 111, 112, 113, 114] else [115, 116, 117, 118])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then [119, 120, 121, 122] else (if i.val < 17 then [123, 124] else [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140])) else (if i.val < 20 then (if i.val < 19 then [141, 142, 143, 144, 145, 146, 147, 148] else [149, 150, 151, 152, 153, 154, 155, 156]) else (if i.val < 21 then [157, 158, 159, 160] else [161, 162, 163, 164, 165, 166, 167, 168]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then [169, 170, 171, 172] else [173, 174, 175, 176]) else (if i.val < 25 then [177, 178] else [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])) else (if i.val < 28 then (if i.val < 27 then [195, 196, 197, 198, 199, 200, 201, 202] else [203, 204, 205, 206, 207, 208, 209, 210]) else (if i.val < 29 then [211, 212, 213, 214] else [215, 216, 217, 218, 219, 220, 221, 222]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then [223, 224, 225, 226] else (if i.val < 32 then [227, 228, 229, 230] else [231, 232])) else (if i.val < 35 then (if i.val < 34 then [233, 234, 235, 236] else [237, 238, 239, 240]) else (if i.val < 36 then [241, 242] else [243, 244]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then [245, 246, 247, 248] else [249, 250, 251, 252]) else (if i.val < 40 then [253, 254] else [255, 256])) else (if i.val < 43 then (if i.val < 42 then [257, 258, 259, 260] else []) else (if i.val < 44 then [261, 262, 263, 264] else [265, 266])))) else (if i.val < 53 then (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then [267, 268, 269, 270] else []) else (if i.val < 48 then [271, 272, 273, 274] else [275, 276])) else (if i.val < 51 then (if i.val < 50 then [277, 278] else [279, 280]) else (if i.val < 52 then [281, 282] else [283, 284]))) else (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then [285, 286, 287, 288] else [289, 290]) else (if i.val < 56 then [] else [])) else (if i.val < 59 then (if i.val < 58 then [291, 292, 293, 294] else [295, 296]) else (if i.val < 60 then [297, 298, 299, 300] else [301, 302])))))) else (if i.val < 91 then (if i.val < 76 then (if i.val < 68 then (if i.val < 64 then (if i.val < 62 then [] else (if i.val < 63 then [] else [303, 304])) else (if i.val < 66 then (if i.val < 65 then [305, 306] else [307, 308]) else (if i.val < 67 then [] else [309, 310, 311, 312]))) else (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then [313, 314] else [315, 316]) else (if i.val < 71 then [317, 318] else [319, 320, 321, 322])) else (if i.val < 74 then (if i.val < 73 then [] else [323, 324]) else (if i.val < 75 then [] else [])))) else (if i.val < 83 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 81 then (if i.val < 80 then [325, 326, 327, 328, 329, 330, 331, 332] else []) else (if i.val < 82 then [333, 334, 335, 336] else []))) else (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then [337, 338, 339, 340, 341, 342, 343, 344] else [345, 346, 347, 348]) else (if i.val < 86 then [349, 350, 351, 352] else [353, 354])) else (if i.val < 89 then (if i.val < 88 then [355] else []) else (if i.val < 90 then [] else []))))) else (if i.val < 106 then (if i.val < 98 then (if i.val < 94 then (if i.val < 92 then [356, 357] else (if i.val < 93 then [] else [358, 359])) else (if i.val < 96 then (if i.val < 95 then [360, 361] else []) else (if i.val < 97 then [] else []))) else (if i.val < 102 then (if i.val < 100 then (if i.val < 99 then [] else [362, 363, 364, 365]) else (if i.val < 101 then [] else [366, 367, 368, 369])) else (if i.val < 104 then (if i.val < 103 then [370, 371] else []) else (if i.val < 105 then [] else [372, 373])))) else (if i.val < 114 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then [374, 375] else [376, 377]) else (if i.val < 109 then [] else [])) else (if i.val < 112 then (if i.val < 111 then [] else [378, 379, 380, 381]) else (if i.val < 113 then [382, 383] else [384, 385, 386, 387]))) else (if i.val < 118 then (if i.val < 116 then (if i.val < 115 then [388, 389] else []) else (if i.val < 117 then [] else [390, 391])) else (if i.val < 120 then (if i.val < 119 then [392, 393] else [394, 395]) else (if i.val < 121 then [] else [396, 397, 398, 399]))))))) else (if i.val < 183 then (if i.val < 152 then (if i.val < 137 then (if i.val < 129 then (if i.val < 125 then (if i.val < 123 then [400, 401] else (if i.val < 124 then [402, 403] else [404, 405])) else (if i.val < 127 then (if i.val < 126 then [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140] else [141, 142, 143, 144, 145, 146, 147, 148]) else (if i.val < 128 then [149, 150, 151, 152, 153, 154, 155, 156] else [157, 158, 159, 160]))) else (if i.val < 133 then (if i.val < 131 then (if i.val < 130 then [161, 162, 163, 164, 165, 166, 167, 168] else [169, 170, 171, 172]) else (if i.val < 132 then [173, 174, 175, 176] else [177, 178])) else (if i.val < 135 then (if i.val < 134 then [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194] else [195, 196, 197, 198, 199, 200, 201, 202]) else (if i.val < 136 then [203, 204, 205, 206, 207, 208, 209, 210] else [211, 212, 213, 214])))) else (if i.val < 144 then (if i.val < 140 then (if i.val < 138 then [215, 216, 217, 218, 219, 220, 221, 222] else (if i.val < 139 then [223, 224, 225, 226] else [227, 228, 229, 230])) else (if i.val < 142 then (if i.val < 141 then [231, 232] else [233, 234, 235, 236]) else (if i.val < 143 then [237, 238, 239, 240] else [241, 242]))) else (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [243, 244] else [245, 246, 247, 248]) else (if i.val < 147 then [249, 250, 251, 252] else [253, 254])) else (if i.val < 150 then (if i.val < 149 then [255, 256] else [257, 258, 259, 260]) else (if i.val < 151 then [] else [261, 262, 263, 264]))))) else (if i.val < 167 then (if i.val < 159 then (if i.val < 155 then (if i.val < 153 then [265, 266] else (if i.val < 154 then [267, 268, 269, 270] else [])) else (if i.val < 157 then (if i.val < 156 then [271, 272, 273, 274] else [275, 276]) else (if i.val < 158 then [277, 278] else [279, 280]))) else (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then [281, 282] else [283, 284]) else (if i.val < 162 then [285, 286, 287, 288] else [289, 290])) else (if i.val < 165 then (if i.val < 164 then [] else []) else (if i.val < 166 then [291, 292, 293, 294] else [295, 296])))) else (if i.val < 175 then (if i.val < 171 then (if i.val < 169 then (if i.val < 168 then [297, 298, 299, 300] else [301, 302]) else (if i.val < 170 then [] else [])) else (if i.val < 173 then (if i.val < 172 then [303, 304] else [305, 306]) else (if i.val < 174 then [307, 308] else []))) else (if i.val < 179 then (if i.val < 177 then (if i.val < 176 then [309, 310, 311, 312] else [313, 314]) else (if i.val < 178 then [315, 316] else [317, 318])) else (if i.val < 181 then (if i.val < 180 then [319, 320, 321, 322] else []) else (if i.val < 182 then [323, 324] else [])))))) else (if i.val < 213 then (if i.val < 198 then (if i.val < 190 then (if i.val < 186 then (if i.val < 184 then [] else (if i.val < 185 then [] else [])) else (if i.val < 188 then (if i.val < 187 then [] else [325, 326, 327, 328, 329, 330, 331, 332]) else (if i.val < 189 then [] else [333, 334, 335, 336]))) else (if i.val < 194 then (if i.val < 192 then (if i.val < 191 then [] else [337, 338, 339, 340, 341, 342, 343, 344]) else (if i.val < 193 then [345, 346, 347, 348] else [349, 350, 351, 352])) else (if i.val < 196 then (if i.val < 195 then [353, 354] else [355]) else (if i.val < 197 then [] else [])))) else (if i.val < 205 then (if i.val < 201 then (if i.val < 199 then [] else (if i.val < 200 then [356, 357] else [])) else (if i.val < 203 then (if i.val < 202 then [358, 359] else [360, 361]) else (if i.val < 204 then [] else []))) else (if i.val < 209 then (if i.val < 207 then (if i.val < 206 then [] else []) else (if i.val < 208 then [362, 363, 364, 365] else [])) else (if i.val < 211 then (if i.val < 210 then [366, 367, 368, 369] else [370, 371]) else (if i.val < 212 then [] else []))))) else (if i.val < 228 then (if i.val < 220 then (if i.val < 216 then (if i.val < 214 then [372, 373] else (if i.val < 215 then [374, 375] else [376, 377])) else (if i.val < 218 then (if i.val < 217 then [] else []) else (if i.val < 219 then [] else [378, 379, 380, 381]))) else (if i.val < 224 then (if i.val < 222 then (if i.val < 221 then [382, 383] else [384, 385, 386, 387]) else (if i.val < 223 then [388, 389] else [])) else (if i.val < 226 then (if i.val < 225 then [] else [390, 391]) else (if i.val < 227 then [392, 393] else [394, 395])))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (if i.val < 229 then [] else [396, 397, 398, 399]) else (if i.val < 231 then [400, 401] else [402, 403])) else (if i.val < 234 then (if i.val < 233 then [404, 405] else [406, 407]) else (if i.val < 235 then [408, 409] else [410, 411]))) else (if i.val < 240 then (if i.val < 238 then (if i.val < 237 then [412, 413] else [277, 278]) else (if i.val < 239 then [279, 280] else [281, 282])) else (if i.val < 242 then (if i.val < 241 then [283, 284] else [414, 415]) else (if i.val < 243 then [416, 417] else [315, 316])))))))) else (if i.val < 366 then (if i.val < 305 then (if i.val < 274 then (if i.val < 259 then (if i.val < 251 then (if i.val < 247 then (if i.val < 245 then [317, 318] else (if i.val < 246 then [] else [])) else (if i.val < 249 then (if i.val < 248 then [418, 419] else [420, 421]) else (if i.val < 250 then [] else []))) else (if i.val < 255 then (if i.val < 253 then (if i.val < 252 then [372, 373] else [374, 375]) else (if i.val < 254 then [422, 423] else [424, 425])) else (if i.val < 257 then (if i.val < 256 then [402, 403] else [404, 405]) else (if i.val < 258 then [426, 427] else [])))) else (if i.val < 266 then (if i.val < 262 then (if i.val < 260 then [428, 429] else (if i.val < 261 then [] else [307, 308])) else (if i.val < 264 then (if i.val < 263 then [] else [309, 310, 311, 312]) else (if i.val < 265 then [313, 314] else [315, 316]))) else (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then [317, 318] else [430, 431]) else (if i.val < 269 then [] else [432, 433])) else (if i.val < 272 then (if i.val < 271 then [] else [394, 395]) else (if i.val < 273 then [] else [396, 397, 398, 399]))))) else (if i.val < 289 then (if i.val < 281 then (if i.val < 277 then (if i.val < 275 then [400, 401] else (if i.val < 276 then [402, 403] else [404, 405])) else (if i.val < 279 then (if i.val < 278 then [414, 415] else [416, 417]) else (if i.val < 280 then [315, 316] else [317, 318]))) else (if i.val < 285 then (if i.val < 283 then (if i.val < 282 then [422, 423] else [424, 425]) else (if i.val < 284 then [402, 403] else [404, 405])) else (if i.val < 287 then (if i.val < 286 then [434, 435] else []) else (if i.val < 288 then [436, 437, 438, 439] else [])))) else (if i.val < 297 then (if i.val < 293 then (if i.val < 291 then (if i.val < 290 then [] else []) else (if i.val < 292 then [376, 377] else [])) else (if i.val < 295 then (if i.val < 294 then [378, 379, 380, 381] else [384, 385, 386, 387]) else (if i.val < 296 then [] else [390, 391]))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then [394, 395] else []) else (if i.val < 300 then [396, 397, 398, 399] else [400, 401])) else (if i.val < 303 then (if i.val < 302 then [402, 403] else [404, 405]) else (if i.val < 304 then [422, 423] else [424, 425])))))) else (if i.val < 335 then (if i.val < 320 then (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then [402, 403] else (if i.val < 307 then [404, 405] else [430, 431])) else (if i.val < 310 then (if i.val < 309 then [432, 433] else [394, 395]) else (if i.val < 311 then [] else [396, 397, 398, 399]))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then [400, 401] else [402, 403]) else (if i.val < 315 then [404, 405] else [422, 423])) else (if i.val < 318 then (if i.val < 317 then [424, 425] else [402, 403]) else (if i.val < 319 then [404, 405] else [440, 441, 442, 443])))) else (if i.val < 327 then (if i.val < 323 then (if i.val < 321 then [444, 445] else (if i.val < 322 then [] else [])) else (if i.val < 325 then (if i.val < 324 then [] else []) else (if i.val < 326 then [319, 321] else []))) else (if i.val < 331 then (if i.val < 329 then (if i.val < 328 then [] else []) else (if i.val < 330 then [325, 327, 329, 331] else [])) else (if i.val < 333 then (if i.val < 332 then [337, 339, 341, 343] else [345, 347]) else (if i.val < 334 then [] else []))))) else (if i.val < 350 then (if i.val < 342 then (if i.val < 338 then (if i.val < 336 then [362, 364] else (if i.val < 337 then [] else [376, 377])) else (if i.val < 340 then (if i.val < 339 then [] else []) else (if i.val < 341 then [] else [378, 379, 380, 381]))) else (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then [382, 383] else [384, 385, 386, 387]) else (if i.val < 345 then [388, 389] else [])) else (if i.val < 348 then (if i.val < 347 then [] else [390, 391]) else (if i.val < 349 then [392, 393] else [394, 395])))) else (if i.val < 358 then (if i.val < 354 then (if i.val < 352 then (if i.val < 351 then [] else [396, 397, 398, 399]) else (if i.val < 353 then [400, 401] else [402, 403])) else (if i.val < 356 then (if i.val < 355 then [404, 405] else []) else (if i.val < 357 then [] else [418, 419]))) else (if i.val < 362 then (if i.val < 360 then (if i.val < 359 then [422, 423] else [424, 425]) else (if i.val < 361 then [402, 403] else [404, 405])) else (if i.val < 364 then (if i.val < 363 then [430, 431] else []) else (if i.val < 365 then [432, 433] else []))))))) else (if i.val < 427 then (if i.val < 396 then (if i.val < 381 then (if i.val < 373 then (if i.val < 369 then (if i.val < 367 then [394, 395] else (if i.val < 368 then [] else [396, 397, 398, 399])) else (if i.val < 371 then (if i.val < 370 then [400, 401] else [402, 403]) else (if i.val < 372 then [404, 405] else [422, 423]))) else (if i.val < 377 then (if i.val < 375 then (if i.val < 374 then [424, 425] else [402, 403]) else (if i.val < 376 then [404, 405] else [434])) else (if i.val < 379 then (if i.val < 378 then [436, 438] else [376, 377]) else (if i.val < 380 then [] else [378, 379, 380, 381])))) else (if i.val < 388 then (if i.val < 384 then (if i.val < 382 then [384, 385, 386, 387] else (if i.val < 383 then [] else [390, 391])) else (if i.val < 386 then (if i.val < 385 then [394, 395] else []) else (if i.val < 387 then [396, 397, 398, 399] else [400, 401]))) else (if i.val < 392 then (if i.val < 390 then (if i.val < 389 then [402, 403] else [404, 405]) else (if i.val < 391 then [422, 423] else [424, 425])) else (if i.val < 394 then (if i.val < 393 then [402, 403] else [404, 405]) else (if i.val < 395 then [430, 431] else [432, 433]))))) else (if i.val < 411 then (if i.val < 403 then (if i.val < 399 then (if i.val < 397 then [394, 395] else (if i.val < 398 then [] else [396, 397, 398, 399])) else (if i.val < 401 then (if i.val < 400 then [400, 401] else [402, 403]) else (if i.val < 402 then [404, 405] else [422, 423]))) else (if i.val < 407 then (if i.val < 405 then (if i.val < 404 then [424, 425] else [402, 403]) else (if i.val < 406 then [404, 405] else [446, 447])) else (if i.val < 409 then (if i.val < 408 then [448, 449] else [414, 415]) else (if i.val < 410 then [416, 417] else [450, 451])))) else (if i.val < 419 then (if i.val < 415 then (if i.val < 413 then (if i.val < 412 then [452, 453] else [422, 423]) else (if i.val < 414 then [424, 425] else [450, 451])) else (if i.val < 417 then (if i.val < 416 then [452, 453] else [422, 423]) else (if i.val < 418 then [424, 425] else [450, 451]))) else (if i.val < 423 then (if i.val < 421 then (if i.val < 420 then [452, 453] else [422, 423]) else (if i.val < 422 then [424, 425] else [450, 451])) else (if i.val < 425 then (if i.val < 424 then [452, 453] else [422, 423]) else (if i.val < 426 then [424, 425] else [454, 455])))))) else (if i.val < 457 then (if i.val < 442 then (if i.val < 434 then (if i.val < 430 then (if i.val < 428 then [456, 457, 458, 459] else (if i.val < 429 then [430, 431] else [432, 433])) else (if i.val < 432 then (if i.val < 431 then [454] else [456, 458]) else (if i.val < 433 then [430, 431] else [432, 433]))) else (if i.val < 438 then (if i.val < 436 then (if i.val < 435 then [460, 461] else [462]) else (if i.val < 437 then [434] else [])) else (if i.val < 440 then (if i.val < 439 then [436, 438] else []) else (if i.val < 441 then [440, 463, 441, 464, 442, 465, 443, 466] else [467, 468, 469, 470])))) else (if i.val < 449 then (if i.val < 445 then (if i.val < 443 then [] else (if i.val < 444 then [] else [471, 472])) else (if i.val < 447 then (if i.val < 446 then [] else [473]) else (if i.val < 448 then [474, 475] else [450, 451]))) else (if i.val < 453 then (if i.val < 451 then (if i.val < 450 then [452, 453] else [473]) else (if i.val < 452 then [474, 475] else [450, 451])) else (if i.val < 455 then (if i.val < 454 then [452, 453] else [476]) else (if i.val < 456 then [] else [454]))))) else (if i.val < 472 then (if i.val < 464 then (if i.val < 460 then (if i.val < 458 then [] else (if i.val < 459 then [456, 458] else [])) else (if i.val < 462 then (if i.val < 461 then [460, 477, 461, 478] else []) else (if i.val < 463 then [] else [444, 479, 445, 480]))) else (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then [481, 482] else []) else (if i.val < 467 then [] else [])) else (if i.val < 470 then (if i.val < 469 then [] else []) else (if i.val < 471 then [] else [])))) else (if i.val < 480 then (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then [] else [483]) else (if i.val < 475 then [473] else [474, 475])) else (if i.val < 478 then (if i.val < 477 then [476, 484] else [462, 485]) else (if i.val < 479 then [] else [486, 487]))) else (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then [] else []) else (if i.val < 483 then [] else [483])) else (if i.val < 486 then (if i.val < 485 then [] else []) else (if i.val < 487 then [] else [])))))))))
def vectors (i : Fin 488) : List ℕ :=
  (if i.val < 244 then (if i.val < 122 then (if i.val < 61 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [1, 16, 108, 281, 574, 1156, 2271, 4339, 8008, 14257, 24519, 40840, 66082, 104179, 160456] else (if i.val < 2 then [1, 16, 108, 281, 574, 1156, 2271, 4339, 8008, 14257, 24519, 40840, 66082, 104179, 160456] else [1, 8, 24, 40, 80, 155, 285, 495, 815, 1280, 1930, 2810, 3970, 5465, 7355])) else (if i.val < 5 then (if i.val < 4 then [1, 8, 20, 32, 65, 116, 212, 376, 644, 1064, 1698, 2624, 3938, 5756, 8216] else [1, 4, 8, 16, 32, 62, 114, 198, 326, 512, 772, 1124, 1588, 2186, 2942]) else (if i.val < 6 then [1, 8, 18, 30, 55, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 10 then [1, 16, 36, 50, 103, 203, 384, 696, 1222, 2087, 3477, 5664, 9038, 14147, 21746] else [1, 8, 7, 10, 20, 38, 68, 115, 185, 285, 423, 608, 850, 1160, 1550])) else (if i.val < 13 then (if i.val < 12 then [1, 8, 10, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 14 then [1, 8, 14, 27, 54, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else (if i.val < 17 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 16, 108, 281, 574, 1156, 2271, 4339, 8008, 14257, 24519, 40840, 66082, 104179, 160456])) else (if i.val < 20 then (if i.val < 19 then [1, 8, 24, 40, 80, 155, 285, 495, 815, 1280, 1930, 2810, 3970, 5465, 7355] else [1, 8, 20, 32, 65, 116, 212, 376, 644, 1064, 1698, 2624, 3938, 5756, 8216]) else (if i.val < 21 then [1, 4, 8, 16, 32, 62, 114, 198, 326, 512, 772, 1124, 1588, 2186, 2942] else [1, 8, 18, 30, 55, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 25 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 16, 36, 50, 103, 203, 384, 696, 1222, 2087, 3477, 5664, 9038, 14147, 21746])) else (if i.val < 28 then (if i.val < 27 then [1, 8, 7, 10, 20, 38, 68, 115, 185, 285, 423, 608, 850, 1160, 1550] else [1, 8, 10, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 29 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 8, 14, 27, 54, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else (if i.val < 32 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 35 then (if i.val < 34 then [1, 4, 8, 16, 30, 52, 84, 128, 186, 260, 352, 464, 598, 756, 940] else [1, 4, 8, 16, 32, 62, 114, 198, 326, 512, 772, 1124, 1588, 2186, 2942]) else (if i.val < 36 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then [1, 4, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 40 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 43 then (if i.val < 42 then [1, 4, 4, 10, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 44 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])))) else (if i.val < 53 then (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then [1, 4, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 48 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 51 then (if i.val < 50 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 52 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then [1, 4, 6, 6, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 56 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 59 then (if i.val < 58 then [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647] else [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378]) else (if i.val < 60 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])))))) else (if i.val < 91 then (if i.val < 76 then (if i.val < 68 then (if i.val < 64 then (if i.val < 62 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 63 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 66 then (if i.val < 65 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 67 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))) else (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 71 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 6, 14, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22])) else (if i.val < 74 then (if i.val < 73 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 75 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 83 then (if i.val < 79 then (if i.val < 77 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 78 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 81 then (if i.val < 80 then [1, 8, 12, 26, 61, 125, 236, 424, 744, 1285, 2188, 3670, 6055, 9813, 15608] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 82 then [1, 4, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then [1, 8, 14, 27, 54, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 86 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 89 then (if i.val < 88 then [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 90 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) else (if i.val < 106 then (if i.val < 98 then (if i.val < 94 then (if i.val < 92 then [1, 2, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92] else (if i.val < 93 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 96 then (if i.val < 95 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 97 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 102 then (if i.val < 100 then (if i.val < 99 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 101 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108])) else (if i.val < 104 then (if i.val < 103 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 105 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])))) else (if i.val < 114 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69]) else (if i.val < 109 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 112 then (if i.val < 111 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647]) else (if i.val < 113 then [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))) else (if i.val < 118 then (if i.val < 116 then (if i.val < 115 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 117 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 120 then (if i.val < 119 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 121 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))))))) else (if i.val < 183 then (if i.val < 152 then (if i.val < 137 then (if i.val < 129 then (if i.val < 125 then (if i.val < 123 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else (if i.val < 124 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 127 then (if i.val < 126 then [1, 16, 108, 281, 574, 1156, 2271, 4339, 8008, 14257, 24519, 40840, 66082, 104179, 160456] else [1, 8, 24, 40, 80, 155, 285, 495, 815, 1280, 1930, 2810, 3970, 5465, 7355]) else (if i.val < 128 then [1, 8, 20, 32, 65, 116, 212, 376, 644, 1064, 1698, 2624, 3938, 5756, 8216] else [1, 4, 8, 16, 32, 62, 114, 198, 326, 512, 772, 1124, 1588, 2186, 2942]))) else (if i.val < 133 then (if i.val < 131 then (if i.val < 130 then [1, 8, 18, 30, 55, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 132 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 135 then (if i.val < 134 then [1, 16, 36, 50, 103, 203, 384, 696, 1222, 2087, 3477, 5664, 9038, 14147, 21746] else [1, 8, 7, 10, 20, 38, 68, 115, 185, 285, 423, 608, 850, 1160, 1550]) else (if i.val < 136 then [1, 8, 10, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])))) else (if i.val < 144 then (if i.val < 140 then (if i.val < 138 then [1, 8, 14, 27, 54, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039] else (if i.val < 139 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108])) else (if i.val < 142 then (if i.val < 141 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 8, 16, 30, 52, 84, 128, 186, 260, 352, 464, 598, 756, 940]) else (if i.val < 143 then [1, 4, 8, 16, 32, 62, 114, 198, 326, 512, 772, 1124, 1588, 2186, 2942] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]))) else (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 147 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 150 then (if i.val < 149 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 4, 10, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 151 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))))) else (if i.val < 167 then (if i.val < 159 then (if i.val < 155 then (if i.val < 153 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else (if i.val < 154 then [1, 4, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 157 then (if i.val < 156 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 158 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 162 then [1, 4, 6, 6, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 165 then (if i.val < 164 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 166 then [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647] else [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378])))) else (if i.val < 175 then (if i.val < 171 then (if i.val < 169 then (if i.val < 168 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 170 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 173 then (if i.val < 172 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 174 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 179 then (if i.val < 177 then (if i.val < 176 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 178 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 181 then (if i.val < 180 then [1, 4, 6, 14, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 182 then [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) else (if i.val < 213 then (if i.val < 198 then (if i.val < 190 then (if i.val < 186 then (if i.val < 184 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 185 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 188 then (if i.val < 187 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 8, 12, 26, 61, 125, 236, 424, 744, 1285, 2188, 3670, 6055, 9813, 15608]) else (if i.val < 189 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137]))) else (if i.val < 194 then (if i.val < 192 then (if i.val < 191 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 8, 14, 27, 54, 106, 201, 365, 638, 1079, 1772, 2833, 4418, 6732, 10039]) else (if i.val < 193 then [1, 4, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108])) else (if i.val < 196 then (if i.val < 195 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 197 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 205 then (if i.val < 201 then (if i.val < 199 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 200 then [1, 2, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 203 then (if i.val < 202 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 204 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 209 then (if i.val < 207 then (if i.val < 206 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 208 then [1, 4, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 211 then (if i.val < 210 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 212 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) else (if i.val < 228 then (if i.val < 220 then (if i.val < 216 then (if i.val < 214 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else (if i.val < 215 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69])) else (if i.val < 218 then (if i.val < 217 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 219 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647]))) else (if i.val < 224 then (if i.val < 222 then (if i.val < 221 then [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 223 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 226 then (if i.val < 225 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 227 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161])))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (if i.val < 229 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 231 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 234 then (if i.val < 233 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 235 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]))) else (if i.val < 240 then (if i.val < 238 then (if i.val < 237 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 239 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 242 then (if i.val < 241 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 243 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])))))))) else (if i.val < 366 then (if i.val < 305 then (if i.val < 274 then (if i.val < 259 then (if i.val < 251 then (if i.val < 247 then (if i.val < 245 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else (if i.val < 246 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 249 then (if i.val < 248 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 250 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 255 then (if i.val < 253 then (if i.val < 252 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 254 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 257 then (if i.val < 256 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 258 then [1, 2, 6, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 266 then (if i.val < 262 then (if i.val < 260 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else (if i.val < 261 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161])) else (if i.val < 264 then (if i.val < 263 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 265 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]))) else (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26]) else (if i.val < 269 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161])) else (if i.val < 272 then (if i.val < 271 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 273 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))))) else (if i.val < 289 then (if i.val < 281 then (if i.val < 277 then (if i.val < 275 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else (if i.val < 276 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 279 then (if i.val < 278 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 280 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 285 then (if i.val < 283 then (if i.val < 282 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 284 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 287 then (if i.val < 286 then [1, 2, 3, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 288 then [1, 4, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 297 then (if i.val < 293 then (if i.val < 291 then (if i.val < 290 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 292 then [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 295 then (if i.val < 294 then [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 296 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 300 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 303 then (if i.val < 302 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 304 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])))))) else (if i.val < 335 then (if i.val < 320 then (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else (if i.val < 307 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26])) else (if i.val < 310 then (if i.val < 309 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]) else (if i.val < 311 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 315 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106])) else (if i.val < 318 then (if i.val < 317 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 319 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 4, 12, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22])))) else (if i.val < 327 then (if i.val < 323 then (if i.val < 321 then [1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 322 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 325 then (if i.val < 324 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 326 then [1, 2, 4, 12, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 331 then (if i.val < 329 then (if i.val < 328 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 330 then [1, 4, 10, 24, 57, 117, 221, 398, 702, 1221, 2095, 3540, 5879, 9581, 15309] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 333 then (if i.val < 332 then [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647] else [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378]) else (if i.val < 334 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) else (if i.val < 350 then (if i.val < 342 then (if i.val < 338 then (if i.val < 336 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else (if i.val < 337 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69])) else (if i.val < 340 then (if i.val < 339 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 341 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647]))) else (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then [1, 2, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 345 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 348 then (if i.val < 347 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 349 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161])))) else (if i.val < 358 then (if i.val < 354 then (if i.val < 352 then (if i.val < 351 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108]) else (if i.val < 353 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 356 then (if i.val < 355 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 357 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]))) else (if i.val < 362 then (if i.val < 360 then (if i.val < 359 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 361 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471])) else (if i.val < 364 then (if i.val < 363 then [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 365 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))) else (if i.val < 427 then (if i.val < 396 then (if i.val < 381 then (if i.val < 373 then (if i.val < 369 then (if i.val < 367 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else (if i.val < 368 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108])) else (if i.val < 371 then (if i.val < 370 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 372 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]))) else (if i.val < 377 then (if i.val < 375 then (if i.val < 374 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 376 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 1, 2, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6])) else (if i.val < 379 then (if i.val < 378 then [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69]) else (if i.val < 380 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 10, 21, 42, 82, 155, 282, 497, 852, 1423, 2317, 3680, 5706, 8647])))) else (if i.val < 388 then (if i.val < 384 then (if i.val < 382 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else (if i.val < 383 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 386 then (if i.val < 385 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 387 then [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]))) else (if i.val < 392 then (if i.val < 390 then (if i.val < 389 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 391 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470])) else (if i.val < 394 then (if i.val < 393 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471]) else (if i.val < 395 then [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]))))) else (if i.val < 411 then (if i.val < 403 then (if i.val < 399 then (if i.val < 397 then [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161] else (if i.val < 398 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 8, 16, 31, 58, 106, 188, 322, 532, 849, 1312, 1969, 2878, 4108])) else (if i.val < 401 then (if i.val < 400 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 402 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]))) else (if i.val < 407 then (if i.val < 405 then (if i.val < 404 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470]) else (if i.val < 406 then [1, 2, 4, 8, 16, 31, 57, 99, 163, 256, 386, 562, 794, 1093, 1471] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) else (if i.val < 409 then (if i.val < 408 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 410 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])))) else (if i.val < 419 then (if i.val < 415 then (if i.val < 413 then (if i.val < 412 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 414 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) else (if i.val < 417 then (if i.val < 416 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 418 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]))) else (if i.val < 423 then (if i.val < 421 then (if i.val < 420 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 422 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) else (if i.val < 425 then (if i.val < 424 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106]) else (if i.val < 426 then [1, 2, 4, 8, 15, 26, 42, 64, 93, 130, 176, 232, 299, 378, 470] else [1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))))) else (if i.val < 457 then (if i.val < 442 then (if i.val < 434 then (if i.val < 430 then (if i.val < 428 then [1, 4, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else (if i.val < 429 then [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161])) else (if i.val < 432 then (if i.val < 431 then [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26]) else (if i.val < 433 then [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 2, 4, 7, 11, 17, 25, 35, 47, 61, 77, 95, 115, 137, 161]))) else (if i.val < 438 then (if i.val < 436 then (if i.val < 435 then [1, 2, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 437 then [1, 1, 2, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 440 then (if i.val < 439 then [1, 2, 3, 5, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 441 then [1, 8, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22] else [1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 449 then (if i.val < 445 then (if i.val < 443 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 444 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 447 then (if i.val < 446 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 448 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]))) else (if i.val < 453 then (if i.val < 451 then (if i.val < 450 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 452 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) else (if i.val < 455 then (if i.val < 454 then [1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92, 106] else [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 456 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))))) else (if i.val < 472 then (if i.val < 464 then (if i.val < 460 then (if i.val < 458 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else (if i.val < 459 then [1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 462 then (if i.val < 461 then [1, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 463 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 467 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) else (if i.val < 470 then (if i.val < 469 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 471 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) else (if i.val < 480 then (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 475 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) else (if i.val < 478 then (if i.val < 477 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 479 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) else (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 483 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 486 then (if i.val < 485 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) else (if i.val < 487 then [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))))))
def v (k : Fin 15) (i : Fin 488) : ℕ := (vectors i)[k.val]!
def accepted (_ : Fin 488) : ℕ := 1
end A224160Table

namespace A224160Certificate
open A224160Proof A224160Table A224160Count

def tableIndex (n : ℕ) : Fin 488 := ⟨n % 488, Nat.mod_lt _ (by decide)⟩
def LocalCheck (i : Fin 488) : Prop :=
  allCols.filterMap (step (state i)) = (succ i).map state
def NumericCheck (s : Fin 488) : Prop :=
  v 0 s = 1 ∧ (∀ k : Fin 14, ((succ s).map (v k.castSucc)).sum = v k.succ s) ∧
  v 14 s + 36 * v 12 s + 126 * v 10 s + 84 * v 8 s + 9 * v 6 s =
      9 * v 13 s + 84 * v 11 s + 126 * v 9 s + 36 * v 7 s + v 5 s
instance (i : Fin 488) : Decidable (LocalCheck i) := inferInstanceAs
  (Decidable (allCols.filterMap (step (state i)) = (succ i).map state))
instance (i : Fin 488) : Decidable (NumericCheck i) := by unfold NumericCheck; infer_instance

def LocalBlock (b : ℕ) : Prop := ∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))
def NumericBlock (b : ℕ) : Prop := ∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))
instance (b : ℕ) : Decidable (LocalBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))))
instance (b : ℕ) : Decidable (NumericBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_0 : PLift (NumericBlock 0) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_1 : PLift (NumericBlock 1) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_2 : PLift (NumericBlock 2) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_3 : PLift (NumericBlock 3) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_4 : PLift (NumericBlock 4) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_5 : PLift (NumericBlock 5) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_6 : PLift (NumericBlock 6) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_7 : PLift (NumericBlock 7) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_8 : PLift (NumericBlock 8) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_9 : PLift (NumericBlock 9) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_10 : PLift (NumericBlock 10) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_11 : PLift (NumericBlock 11) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_12 : PLift (NumericBlock 12) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_13 : PLift (NumericBlock 13) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_14 : PLift (NumericBlock 14) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_15 : PLift (NumericBlock 15) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_16 : PLift (NumericBlock 16) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_17 : PLift (NumericBlock 17) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_18 : PLift (NumericBlock 18) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_19 : PLift (NumericBlock 19) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_20 : PLift (NumericBlock 20) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_21 : PLift (NumericBlock 21) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_22 : PLift (NumericBlock 22) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_23 : PLift (NumericBlock 23) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_24 : PLift (NumericBlock 24) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_25 : PLift (NumericBlock 25) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_26 : PLift (NumericBlock 26) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_27 : PLift (NumericBlock 27) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_28 : PLift (NumericBlock 28) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_29 : PLift (NumericBlock 29) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_30 : PLift (NumericBlock 30) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_31 : PLift (NumericBlock 31) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_32 : PLift (NumericBlock 32) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_33 : PLift (NumericBlock 33) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_34 : PLift (NumericBlock 34) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_35 : PLift (NumericBlock 35) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_36 : PLift (NumericBlock 36) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_37 : PLift (NumericBlock 37) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_38 : PLift (NumericBlock 38) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_39 : PLift (NumericBlock 39) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_40 : PLift (NumericBlock 40) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_41 : PLift (NumericBlock 41) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_42 : PLift (NumericBlock 42) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_43 : PLift (NumericBlock 43) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_44 : PLift (NumericBlock 44) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_45 : PLift (NumericBlock 45) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_46 : PLift (NumericBlock 46) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_47 : PLift (NumericBlock 47) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_48 : PLift (NumericBlock 48) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_49 : PLift (NumericBlock 49) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_50 : PLift (NumericBlock 50) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_51 : PLift (NumericBlock 51) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_52 : PLift (NumericBlock 52) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_53 : PLift (NumericBlock 53) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_54 : PLift (NumericBlock 54) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_55 : PLift (NumericBlock 55) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_56 : PLift (NumericBlock 56) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_57 : PLift (NumericBlock 57) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_58 : PLift (NumericBlock 58) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_59 : PLift (NumericBlock 59) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_block_60 : PLift (NumericBlock 60) := ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem numeric_blocks : ∀ b : Fin 61, NumericBlock b.val := by
  intro b
  fin_cases b
  · exact numeric_block_0.down
  · exact numeric_block_1.down
  · exact numeric_block_2.down
  · exact numeric_block_3.down
  · exact numeric_block_4.down
  · exact numeric_block_5.down
  · exact numeric_block_6.down
  · exact numeric_block_7.down
  · exact numeric_block_8.down
  · exact numeric_block_9.down
  · exact numeric_block_10.down
  · exact numeric_block_11.down
  · exact numeric_block_12.down
  · exact numeric_block_13.down
  · exact numeric_block_14.down
  · exact numeric_block_15.down
  · exact numeric_block_16.down
  · exact numeric_block_17.down
  · exact numeric_block_18.down
  · exact numeric_block_19.down
  · exact numeric_block_20.down
  · exact numeric_block_21.down
  · exact numeric_block_22.down
  · exact numeric_block_23.down
  · exact numeric_block_24.down
  · exact numeric_block_25.down
  · exact numeric_block_26.down
  · exact numeric_block_27.down
  · exact numeric_block_28.down
  · exact numeric_block_29.down
  · exact numeric_block_30.down
  · exact numeric_block_31.down
  · exact numeric_block_32.down
  · exact numeric_block_33.down
  · exact numeric_block_34.down
  · exact numeric_block_35.down
  · exact numeric_block_36.down
  · exact numeric_block_37.down
  · exact numeric_block_38.down
  · exact numeric_block_39.down
  · exact numeric_block_40.down
  · exact numeric_block_41.down
  · exact numeric_block_42.down
  · exact numeric_block_43.down
  · exact numeric_block_44.down
  · exact numeric_block_45.down
  · exact numeric_block_46.down
  · exact numeric_block_47.down
  · exact numeric_block_48.down
  · exact numeric_block_49.down
  · exact numeric_block_50.down
  · exact numeric_block_51.down
  · exact numeric_block_52.down
  · exact numeric_block_53.down
  · exact numeric_block_54.down
  · exact numeric_block_55.down
  · exact numeric_block_56.down
  · exact numeric_block_57.down
  · exact numeric_block_58.down
  · exact numeric_block_59.down
  · exact numeric_block_60.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_0 : PLift (LocalBlock 0) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_1 : PLift (LocalBlock 1) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_2 : PLift (LocalBlock 2) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_3 : PLift (LocalBlock 3) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_4 : PLift (LocalBlock 4) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_5 : PLift (LocalBlock 5) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_6 : PLift (LocalBlock 6) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_7 : PLift (LocalBlock 7) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_8 : PLift (LocalBlock 8) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_9 : PLift (LocalBlock 9) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_10 : PLift (LocalBlock 10) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_11 : PLift (LocalBlock 11) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_12 : PLift (LocalBlock 12) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_13 : PLift (LocalBlock 13) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_14 : PLift (LocalBlock 14) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_15 : PLift (LocalBlock 15) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_16 : PLift (LocalBlock 16) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_17 : PLift (LocalBlock 17) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_18 : PLift (LocalBlock 18) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_19 : PLift (LocalBlock 19) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_20 : PLift (LocalBlock 20) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_21 : PLift (LocalBlock 21) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_22 : PLift (LocalBlock 22) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_23 : PLift (LocalBlock 23) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_24 : PLift (LocalBlock 24) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_25 : PLift (LocalBlock 25) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_26 : PLift (LocalBlock 26) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_27 : PLift (LocalBlock 27) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_28 : PLift (LocalBlock 28) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_29 : PLift (LocalBlock 29) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_30 : PLift (LocalBlock 30) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_31 : PLift (LocalBlock 31) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_32 : PLift (LocalBlock 32) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_33 : PLift (LocalBlock 33) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_34 : PLift (LocalBlock 34) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_35 : PLift (LocalBlock 35) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_36 : PLift (LocalBlock 36) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_37 : PLift (LocalBlock 37) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_38 : PLift (LocalBlock 38) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_39 : PLift (LocalBlock 39) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_40 : PLift (LocalBlock 40) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_41 : PLift (LocalBlock 41) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_42 : PLift (LocalBlock 42) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_43 : PLift (LocalBlock 43) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_44 : PLift (LocalBlock 44) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_45 : PLift (LocalBlock 45) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_46 : PLift (LocalBlock 46) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_47 : PLift (LocalBlock 47) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_48 : PLift (LocalBlock 48) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_49 : PLift (LocalBlock 49) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_50 : PLift (LocalBlock 50) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_51 : PLift (LocalBlock 51) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_52 : PLift (LocalBlock 52) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_53 : PLift (LocalBlock 53) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_54 : PLift (LocalBlock 54) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_55 : PLift (LocalBlock 55) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_56 : PLift (LocalBlock 56) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_57 : PLift (LocalBlock 57) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_58 : PLift (LocalBlock 58) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_59 : PLift (LocalBlock 59) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_block_60 : PLift (LocalBlock 60) := ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem local_blocks : ∀ b : Fin 61, LocalBlock b.val := by
  intro b
  fin_cases b
  · exact local_block_0.down
  · exact local_block_1.down
  · exact local_block_2.down
  · exact local_block_3.down
  · exact local_block_4.down
  · exact local_block_5.down
  · exact local_block_6.down
  · exact local_block_7.down
  · exact local_block_8.down
  · exact local_block_9.down
  · exact local_block_10.down
  · exact local_block_11.down
  · exact local_block_12.down
  · exact local_block_13.down
  · exact local_block_14.down
  · exact local_block_15.down
  · exact local_block_16.down
  · exact local_block_17.down
  · exact local_block_18.down
  · exact local_block_19.down
  · exact local_block_20.down
  · exact local_block_21.down
  · exact local_block_22.down
  · exact local_block_23.down
  · exact local_block_24.down
  · exact local_block_25.down
  · exact local_block_26.down
  · exact local_block_27.down
  · exact local_block_28.down
  · exact local_block_29.down
  · exact local_block_30.down
  · exact local_block_31.down
  · exact local_block_32.down
  · exact local_block_33.down
  · exact local_block_34.down
  · exact local_block_35.down
  · exact local_block_36.down
  · exact local_block_37.down
  · exact local_block_38.down
  · exact local_block_39.down
  · exact local_block_40.down
  · exact local_block_41.down
  · exact local_block_42.down
  · exact local_block_43.down
  · exact local_block_44.down
  · exact local_block_45.down
  · exact local_block_46.down
  · exact local_block_47.down
  · exact local_block_48.down
  · exact local_block_49.down
  · exact local_block_50.down
  · exact local_block_51.down
  · exact local_block_52.down
  · exact local_block_53.down
  · exact local_block_54.down
  · exact local_block_55.down
  · exact local_block_56.down
  · exact local_block_57.down
  · exact local_block_58.down
  · exact local_block_59.down
  · exact local_block_60.down

theorem covered (P : Fin 488 → Prop)
    (h : ∀ b : Fin 61, ∀ j : Fin 8, P (tableIndex (8 * b.val + j.val))) :
    ∀ i, P i := by
  intro i
  let b : Fin 61 := ⟨i.val / 8, by omega⟩
  let j : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : tableIndex (8 * b.val + j.val) = i := by
    apply Fin.ext
    simp only [tableIndex, b, j]
    omega
  simpa only [he] using h b j

theorem local_table (i : Fin 488) :
    allCols.filterMap (step (state i)) = (succ i).map state :=
  covered LocalCheck local_blocks i

theorem numeric_table (i : Fin 488) : NumericCheck i :=
  covered NumericCheck numeric_blocks i

theorem state_zero : state 0 = start := by decide +kernel

theorem paths_vectors (k : Fin 15) (i : Fin 488) :
    paths succ accepted k.val i = v k i :=
  paths_eq_vectors succ accepted v (fun s => (numeric_table s).1)
    (fun k s => (numeric_table s).2.1 k) k i

theorem recurrence_base (s : Fin 488) :
    paths succ accepted 14 s + 36 * paths succ accepted 12 s + 126 * paths succ accepted 10 s + 84 * paths succ accepted 8 s + 9 * paths succ accepted 6 s =
      9 * paths succ accepted 13 s + 84 * paths succ accepted 11 s + 126 * paths succ accepted 9 s + 36 * paths succ accepted 7 s + paths succ accepted 5 s := by
  have hv (n : Fin 15) := paths_vectors n s
  change paths succ accepted (14 : Fin 15).val s + 36 * paths succ accepted (12 : Fin 15).val s + 126 * paths succ accepted (10 : Fin 15).val s + 84 * paths succ accepted (8 : Fin 15).val s + 9 * paths succ accepted (6 : Fin 15).val s =
      9 * paths succ accepted (13 : Fin 15).val s + 84 * paths succ accepted (11 : Fin 15).val s + 126 * paths succ accepted (9 : Fin 15).val s + 36 * paths succ accepted (7 : Fin 15).val s + paths succ accepted (5 : Fin 15).val s
  simp only [hv]
  exact (numeric_table s).2.2
end A224160Certificate

namespace A224160Table
open A224160Count A224160Certificate

def indexedCount (n : ℕ) : ℕ := paths succ accepted n 0

theorem indexed_vector (k : Fin 15) : indexedCount k.val = v k 0 :=
  paths_vectors k 0

theorem initial_1 : indexedCount 1 = 16 := by
  have h := indexed_vector (1 : Fin 15)
  have hv : v 1 0 = 16 := by decide +kernel
  exact h.trans hv

theorem initial_2 : indexedCount 2 = 108 := by
  have h := indexed_vector (2 : Fin 15)
  have hv : v 2 0 = 108 := by decide +kernel
  exact h.trans hv

theorem initial_3 : indexedCount 3 = 281 := by
  have h := indexed_vector (3 : Fin 15)
  have hv : v 3 0 = 281 := by decide +kernel
  exact h.trans hv

theorem initial_4 : indexedCount 4 = 574 := by
  have h := indexed_vector (4 : Fin 15)
  have hv : v 4 0 = 574 := by decide +kernel
  exact h.trans hv

theorem initial_5 : indexedCount 5 = 1156 := by
  have h := indexed_vector (5 : Fin 15)
  have hv : v 5 0 = 1156 := by decide +kernel
  exact h.trans hv

theorem initial_6 : indexedCount 6 = 2271 := by
  have h := indexed_vector (6 : Fin 15)
  have hv : v 6 0 = 2271 := by decide +kernel
  exact h.trans hv

theorem initial_7 : indexedCount 7 = 4339 := by
  have h := indexed_vector (7 : Fin 15)
  have hv : v 7 0 = 4339 := by decide +kernel
  exact h.trans hv

theorem initial_8 : indexedCount 8 = 8008 := by
  have h := indexed_vector (8 : Fin 15)
  have hv : v 8 0 = 8008 := by decide +kernel
  exact h.trans hv

theorem initial_9 : indexedCount 9 = 14257 := by
  have h := indexed_vector (9 : Fin 15)
  have hv : v 9 0 = 14257 := by decide +kernel
  exact h.trans hv

theorem initial_10 : indexedCount 10 = 24519 := by
  have h := indexed_vector (10 : Fin 15)
  have hv : v 10 0 = 24519 := by decide +kernel
  exact h.trans hv

theorem initial_11 : indexedCount 11 = 40840 := by
  have h := indexed_vector (11 : Fin 15)
  have hv : v 11 0 = 40840 := by decide +kernel
  exact h.trans hv

theorem initial_12 : indexedCount 12 = 66082 := by
  have h := indexed_vector (12 : Fin 15)
  have hv : v 12 0 = 66082 := by decide +kernel
  exact h.trans hv

theorem initial_13 : indexedCount 13 = 104179 := by
  have h := indexed_vector (13 : Fin 15)
  have hv : v 13 0 = 104179 := by decide +kernel
  exact h.trans hv

theorem initial_14 : indexedCount 14 = 160456 := by
  have h := indexed_vector (14 : Fin 15)
  have hv : v 14 0 = 160456 := by decide +kernel
  exact h.trans hv

theorem indexed_recurrence (n : ℕ) :
    indexedCount (n + 14) + 36 * indexedCount (n + 12) + 126 * indexedCount (n + 10) + 84 * indexedCount (n + 8) + 9 * indexedCount (n + 6) =
      9 * indexedCount (n + 13) + 84 * indexedCount (n + 11) + 126 * indexedCount (n + 9) + 36 * indexedCount (n + 7) + indexedCount (n + 5) :=
  paths_recurrence succ accepted recurrence_base n 0
end A224160Table

namespace A224160Formula
open PowerSeries
theorem integer_recurrence (a : ℕ → ℕ)
    (hs : ∀ n : ℕ,
  a (n + 14) + 36 * a (n + 12) + 126 * a (n + 10) +
    84 * a (n + 8) + 9 * a (n + 6) =
  9 * a (n + 13) + 84 * a (n + 11) + 126 * a (n + 9) +
    36 * a (n + 7) + a (n + 5)) (n : ℕ) (hn : 13 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) +
      36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  have h := hs (n - 14)
  have heq (k : ℕ) (hk : k ≤ 14) : n - 14 + k = n - (14 - k) := by omega
  rw [heq 14 (by decide), heq 12 (by decide), heq 10 (by decide),
    heq 8 (by decide), heq 6 (by decide), heq 13 (by decide),
    heq 11 (by decide), heq 9 (by decide), heq 7 (by decide),
    heq 5 (by decide)] at h
  norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at h
  have hz : (a n : ℤ) + 36 * a (n - 2) + 126 * a (n - 4) +
      84 * a (n - 6) + 9 * a (n - 8) =
    9 * a (n - 1) + 84 * a (n - 3) + 126 * a (n - 5) +
      36 * a (n - 7) + a (n - 9) := by exact_mod_cast h
  linarith

theorem generating_function (a : ℕ → ℕ)
(h1 : a 1 = 16) (h2 : a 2 = 108) (h3 : a 3 = 281)
(h4 : a 4 = 574) (h5 : a 5 = 1156) (h6 : a 6 = 2271)
(h7 : a 7 = 4339) (h8 : a 8 = 8008) (h9 : a 9 = 14257)
(h10 : a 10 = 24519) (h11 : a 11 = 40840) (h12 : a 12 = 66082)
(h13 : a 13 = 104179)
(hs : ∀ n : ℕ,
  a (n + 14) + 36 * a (n + 12) + 126 * a (n + 10) +
    84 * a (n + 8) + 9 * a (n + 6) =
  9 * a (n + 13) + 84 * a (n + 11) + 126 * a (n + 9) +
    36 * a (n + 7) + a (n + 5)) :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      16 - 36 * X - 115 * X ^ 2 + 589 * X ^ 3 - 950 * X ^ 4 + 519 * X ^ 5 +
        442 * X ^ 6 - 977 * X ^ 7 + 817 * X ^ 8 - 436 * X ^ 9 + 178 * X ^ 10 -
        55 * X ^ 11 + 9 * X ^ 12 := by
  let g : PowerSeries ℚ := PowerSeries.mk fun n => (a (n + 1) : ℚ)
  change g * (1 - X) ^ 9 = _
  have hl : g * (1 - X) ^ 9 =
      g * X ^ 0 - 9 • (g * X ^ 1) + 36 • (g * X ^ 2) - 84 • (g * X ^ 3) +
      126 • (g * X ^ 4) - 126 • (g * X ^ 5) + 84 • (g * X ^ 6) -
      36 • (g * X ^ 7) + 9 • (g * X ^ 8) - g * X ^ 9 := by
    simp only [nsmul_eq_mul]
    ring
  have hr : (16 - 36 * X - 115 * X ^ 2 + 589 * X ^ 3 - 950 * X ^ 4 +
      519 * X ^ 5 + 442 * X ^ 6 - 977 * X ^ 7 + 817 * X ^ 8 - 436 * X ^ 9 +
      178 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12 : PowerSeries ℚ) =
      16 • X ^ 0 - 36 • X ^ 1 - 115 • X ^ 2 + 589 • X ^ 3 - 950 • X ^ 4 +
        519 • X ^ 5 + 442 • X ^ 6 - 977 • X ^ 7 + 817 • X ^ 8 - 436 • X ^ 9 +
        178 • X ^ 10 - 55 • X ^ 11 + 9 • X ^ 12 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_nsmul]
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · have hc (k : ℕ) (hk : k ≤ n) : coeff n (g * X ^ k) = (a (n - k + 1) : ℚ) := by
      rw [coeff_mul_X_pow', if_pos hk]
      simp only [g, coeff_mk]
    have hx (k : ℕ) (hk : k < n) : coeff n (X ^ k : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    simp (disch := omega) only [hc, hx, nsmul_eq_mul, mul_zero, add_zero,
      sub_zero, Nat.sub_zero]
    norm_num only [Nat.cast_ofNat]
    have hrec := hs (n - 13)
    have heq (k : ℕ) (hk : 5 ≤ k ∧ k ≤ 14) : n - 13 + k = n - (14 - k) + 1 := by omega
    rw [heq 14 (by omega), heq 12 (by omega), heq 10 (by omega),
      heq 8 (by omega), heq 6 (by omega), heq 13 (by omega),
      heq 11 (by omega), heq 9 (by omega), heq 7 (by omega),
      heq 5 (by omega)] at hrec
    norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at hrec
    have hq : (a (n + 1) : ℚ) + 36 * a (n - 2 + 1) + 126 * a (n - 4 + 1) +
        84 * a (n - 6 + 1) + 9 * a (n - 8 + 1) =
      9 * a (n - 1 + 1) + 84 * a (n - 3 + 1) + 126 * a (n - 5 + 1) +
        36 * a (n - 7 + 1) + a (n - 9 + 1) := by exact_mod_cast hrec
    linarith

theorem of_recurrence (a : ℕ → ℕ)
(h1 : a 1 = 16) (h2 : a 2 = 108) (h3 : a 3 = 281)
(h4 : a 4 = 574) (h5 : a 5 = 1156) (h6 : a 6 = 2271)
(h7 : a 7 = 4339) (h8 : a 8 = 8008) (h9 : a 9 = 14257)
(h10 : a 10 = 24519) (h11 : a 11 = 40840) (h12 : a 12 = 66082)
(h13 : a 13 = 104179)
(hs : ∀ n : ℕ,
  a (n + 14) + 36 * a (n + 12) + 126 * a (n + 10) +
    84 * a (n + 8) + 9 * a (n + 6) =
  9 * a (n + 13) + 84 * a (n + 11) + 126 * a (n + 9) +
    36 * a (n + 7) + a (n + 5)) :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      16 - 36 * X - 115 * X ^ 2 + 589 * X ^ 3 - 950 * X ^ 4 + 519 * X ^ 5 +
        442 * X ^ 6 - 977 * X ^ 7 + 817 * X ^ 8 - 436 * X ^ 9 + 178 * X ^ 10 -
        55 * X ^ 11 + 9 * X ^ 12) ∧
    (∀ n > 13, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) +
      36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  exact ⟨generating_function a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs,
    integer_recurrence a hs⟩
end A224160Formula

namespace A224160Proof
open OMA.S_oeis_a224160 A224160Table A224160Certificate PowerSeries

theorem a_eq_indexed (n : ℕ) : a n = indexedCount n :=
  a_eq_paths run_correct state succ accepted 0 local_table (fun _ => rfl) state_zero n

theorem result :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      16 - 36 * X - 115 * X ^ 2 + 589 * X ^ 3 - 950 * X ^ 4 + 519 * X ^ 5 + 442 * X ^ 6 - 977 * X ^ 7 + 817 * X ^ 8 - 436 * X ^ 9 + 178 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12) ∧
    (∀ n > 13, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  have ha : a = indexedCount := funext a_eq_indexed
  rw [ha]
  exact A224160Formula.of_recurrence indexedCount initial_1 initial_2 initial_3
    initial_4 initial_5 initial_6 initial_7 initial_8 initial_9 initial_10 initial_11
    initial_12 initial_13 indexed_recurrence

end A224160Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a224160.main := by
  exact A224160Proof.result
