import OMAStatements.S_oeis_a223840
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.List.Pairwise
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
A223840: exact enumeration of four-row binary arrays with nondecreasing
columns and unimodal rows, diagonals, and antidiagonals.

Four three-phase row automata and a three-column history give a finite
closed table of 154 states. The checked transition lists preserve every
column choice. A proved array/word correspondence identifies the original
cardinality with path counts. Thirteen checked count vectors give a ninth
finite-difference identity, propagated to every length by linear induction.

Source: https://oeis.org/A223840
Array definition: R. H. Hardin (2013).
Generating-function and recurrence conjectures: Colin Barker (2018).
Diagonal wording correction: Andrew Howroyd (2025).
The canonical statement is unchanged from statement PR34847.
-/

namespace A223840Proof
open OMA.S_oeis_a223840
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
def monoCol (c : Col) : Prop := ∀ i : Fin 3, c i.castSucc ≤ c i.succ
instance (c : Col) : Decidable (monoCol c) :=
  inferInstanceAs (Decidable (∀ i : Fin 3, c i.castSucc ≤ c i.succ))
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
def localOK (s : State) (c : Col) : Prop :=
  monoCol c ∧ (∀ i : Fin 4, phaseOK (s.phase i) (c i)) ∧
  (∀ i : Fin 4, uniCheck (adiagFrom (c :: s.history) i.val) = true) ∧
  (∀ i : Fin 4, uniCheck (diagFrom (c :: s.history) i.val) = true)
instance (s : State) (c : Col) : Decidable (localOK s c) :=
  inferInstanceAs (Decidable (monoCol c ∧ (∀ i : Fin 4, phaseOK (s.phase i) (c i)) ∧
    (∀ i : Fin 4, uniCheck (adiagFrom (c :: s.history) i.val) = true) ∧
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
end A223840Proof

namespace A223840Proof
open OMA.S_oeis_a223840

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

end A223840Proof

namespace A223840Proof
open OMA.S_oeis_a223840

theorem isSolution_tail {c : Col} {l : List Col}
    (h : IsSolution (c :: l)) : IsSolution l := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd i
    exact h.1 d (List.mem_cons_of_mem c hd) i
  · intro i
    apply unimodal_tail
    simpa only [List.map_cons] using h.2.1 i
  · intro i hi
    interval_cases i
    · apply unimodal_tail (b := (c 1 : ℕ))
      simpa [adiagFrom] using h.2.2.1 1 (by decide)
    · apply unimodal_tail (b := (c 2 : ℕ))
      simpa [adiagFrom] using h.2.2.1 2 (by decide)
    · apply unimodal_tail (b := (c 3 : ℕ))
      simpa [adiagFrom] using h.2.2.1 3 (by decide)
    · simpa only [List.drop_succ_cons, List.drop_zero] using h.2.2.2.1 1
  · intro j
    simpa only [List.drop_succ_cons] using h.2.2.2.1 (j + 1)
  · intro i hi
    interval_cases i
    · simpa only [List.drop_succ_cons, List.drop_zero] using h.2.2.2.2.2 1
    · apply unimodal_tail (b := (c 0 : ℕ))
      simpa [diagFrom] using h.2.2.2.2.1 0 (by decide)
    · apply unimodal_tail (b := (c 1 : ℕ))
      simpa [diagFrom] using h.2.2.2.2.1 1 (by decide)
    · apply unimodal_tail (b := (c 2 : ℕ))
      simpa [diagFrom] using h.2.2.2.2.1 2 (by decide)
  · intro j
    simpa only [List.drop_succ_cons] using h.2.2.2.2.2 (j + 1)

theorem isSolution_cons_iff (c : Col) (l : List Col) :
    IsSolution (c :: l) ↔ monoCol c ∧
      (∀ i : Fin 4, Unimodal ((c i : ℕ) :: l.map fun d => (d i : ℕ))) ∧
      (∀ i : Fin 4, Unimodal (adiagFrom (c :: l) i.val)) ∧
      (∀ i : Fin 4, Unimodal (diagFrom (c :: l) i.val)) ∧ IsSolution l := by
  constructor
  · intro h
    exact ⟨h.1 c (by simp), by simpa only [List.map_cons] using h.2.1,
      fun i => h.2.2.1 i.val i.isLt,
      fun i => h.2.2.2.2.1 i.val i.isLt, isSolution_tail h⟩
  · rintro ⟨hc, hr, ha, hd, hl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hmem i
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hc i
      · exact hl.1 d hmem i
    · simpa only [List.map_cons] using hr
    · intro i hi
      exact ha ⟨i, hi⟩
    · intro j
      cases j with
      | zero => simpa using ha (3 : Fin 4)
      | succ j => simpa only [List.drop_succ_cons] using hl.2.2.2.1 j
    · intro i hi
      exact hd ⟨i, hi⟩
    · intro j
      cases j with
      | zero => simpa using hd (0 : Fin 4)
      | succ j => simpa only [List.drop_succ_cons] using hl.2.2.2.2.2 j

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

theorem adiagFrom_cons_take (c : Col) (l : List Col) (i : Fin 4) :
    adiagFrom (c :: l.take 3) i.val = adiagFrom (c :: l) i.val := by
  simpa only [List.take_succ_cons] using adiagFrom_take (c :: l) i.val 4 i.isLt

theorem diagFrom_cons_take (c : Col) (l : List Col) (i : Fin 4) :
    diagFrom (c :: l.take 3) i.val = diagFrom (c :: l) i.val := by
  simpa only [List.take_succ_cons] using diagFrom_take (c :: l) i.val 4 (by omega)

end A223840Proof

namespace A223840Proof
open OMA.S_oeis_a223840

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

end A223840Proof

namespace A223840Proof

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

end A223840Proof

namespace A223840Proof
open OMA.S_oeis_a223840

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
    localOK s c ↔ monoCol c ∧
      (∀ i : Fin 4, Unimodal ((c i : ℕ) :: l.map fun d => (d i : ℕ))) ∧
      (∀ i : Fin 4, Unimodal (adiagFrom (c :: l) i.val)) ∧
      (∀ i : Fin 4, Unimodal (diagFrom (c :: l) i.val)) := by
  simp only [localOK, ht.1, uniCheck_eq_true_iff,
    adiagFrom_cons_take, diagFrom_cons_take]
  apply and_congr_right
  intro _
  apply and_congr
  · apply forall_congr'
    intro i
    simpa only [List.map_map, Function.comp_def] using phaseOK_iff (ht.2 i) (c i)
  · rfl

theorem run_correct (l : List Col) : (run l).isSome = true ↔ IsSolution l := by
  induction l with
  | nil => simp [run, IsSolution, adiagFrom, diagFrom, unimodal_nil]
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

end A223840Proof

namespace A223840Count
variable {S : Type*}
def paths (succ : S → List S) (accepted : S → ℕ) : ℕ → S → ℕ
  | 0, s => accepted s
  | n + 1, s => ((succ s).map (paths succ accepted n)).sum

lemma sum_balance (L : List S) (f : Fin 13 → S → ℕ)
    (h : ∀ s, f 12 s + 36 * f 10 s + 126 * f 8 s + 84 * f 6 s + 9 * f 4 s =
      9 * f 11 s + 84 * f 9 s + 126 * f 7 s + 36 * f 5 s + f 3 s) :
    (L.map (f 12)).sum + 36 * (L.map (f 10)).sum + 126 * (L.map (f 8)).sum + 84 * (L.map (f 6)).sum + 9 * (L.map (f 4)).sum =
      9 * (L.map (f 11)).sum + 84 * (L.map (f 9)).sum + 126 * (L.map (f 7)).sum + 36 * (L.map (f 5)).sum + (L.map (f 3)).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs := h s
    omega

theorem paths_recurrence (succ : S → List S) (accepted : S → ℕ)
    (hbase : ∀ s, paths succ accepted 12 s + 36 * paths succ accepted 10 s + 126 * paths succ accepted 8 s + 84 * paths succ accepted 6 s + 9 * paths succ accepted 4 s =
      9 * paths succ accepted 11 s + 84 * paths succ accepted 9 s + 126 * paths succ accepted 7 s + 36 * paths succ accepted 5 s + paths succ accepted 3 s) :
    ∀ n s, paths succ accepted (n + 12) s + 36 * paths succ accepted (n + 10) s + 126 * paths succ accepted (n + 8) s + 84 * paths succ accepted (n + 6) s + 9 * paths succ accepted (n + 4) s =
      9 * paths succ accepted (n + 11) s + 84 * paths succ accepted (n + 9) s + 126 * paths succ accepted (n + 7) s + 36 * paths succ accepted (n + 5) s + paths succ accepted (n + 3) s := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accepted (n + 12))).sum + 36 * ((succ s).map (paths succ accepted (n + 10))).sum + 126 * ((succ s).map (paths succ accepted (n + 8))).sum + 84 * ((succ s).map (paths succ accepted (n + 6))).sum + 9 * ((succ s).map (paths succ accepted (n + 4))).sum =
      9 * ((succ s).map (paths succ accepted (n + 11))).sum + 84 * ((succ s).map (paths succ accepted (n + 9))).sum + 126 * ((succ s).map (paths succ accepted (n + 7))).sum + 36 * ((succ s).map (paths succ accepted (n + 5))).sum + ((succ s).map (paths succ accepted (n + 3))).sum
    exact sum_balance (succ s) (fun k => paths succ accepted (n + k.val)) ih

theorem paths_eq_vectors (succ : S → List S) (accepted : S → ℕ)
    (v : Fin 13 → S → ℕ) (hzero : ∀ s, v 0 s = accepted s)
    (hnext : ∀ k : Fin 12, ∀ s,
      ((succ s).map (v k.castSucc)).sum = v k.succ s) :
    ∀ k : Fin 13, ∀ s, paths succ accepted k.val s = v k s := by
  intro k
  induction k using Fin.induction with
  | zero => intro s; exact (hzero s).symm
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accepted k.val)).sum = v k.succ s
    rw [show paths succ accepted k.val = v k.castSucc from funext ih]
    exact hnext k s
end A223840Count

namespace A223840Proof
open OMA.S_oeis_a223840

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
    ∀ n i, suffixCount (state i) n = A223840Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_allCols, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A223840Count.paths succ accepted n from funext ih]
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
    a n = A223840Count.paths succ accepted n initial := by
  rw [a_eq_suffix hcorrect, ← hstart]
  exact suffixCount_eq_paths state succ accepted hstep haccept n initial

end A223840Proof

namespace A223840Table
open A223840Proof
def codes (i : Fin 154) : ℕ × List ℕ :=
  (if i.val < 77 then (if i.val < 38 then (if i.val < 19 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, []) else (0, [0])) else (if i.val < 3 then (27, [8]) else (36, [12]))) else (if i.val < 6 then (if i.val < 5 then (39, [14]) else (40, [15])) else (if i.val < 7 then (0, [0, 0]) else (if i.val < 8 then (27, [8, 0]) else (36, [12, 0]))))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then (39, [14, 0]) else (40, [15, 0])) else (if i.val < 12 then (54, [0, 8]) else (if i.val < 13 then (27, [8, 8]) else (36, [12, 8])))) else (if i.val < 16 then (if i.val < 15 then (39, [14, 8]) else (40, [15, 8])) else (if i.val < 17 then (72, [0, 12]) else (if i.val < 18 then (45, [8, 12]) else (36, [12, 12])))))) else (if i.val < 28 then (if i.val < 23 then (if i.val < 21 then (if i.val < 20 then (39, [14, 12]) else (40, [15, 12])) else (if i.val < 22 then (78, [0, 14]) else (51, [8, 14]))) else (if i.val < 25 then (if i.val < 24 then (42, [12, 14]) else (39, [14, 14])) else (if i.val < 26 then (40, [15, 14]) else (if i.val < 27 then (80, [0, 15]) else (53, [8, 15]))))) else (if i.val < 33 then (if i.val < 30 then (if i.val < 29 then (44, [12, 15]) else (41, [14, 15])) else (if i.val < 31 then (40, [15, 15]) else (if i.val < 32 then (0, [0, 0, 0]) else (27, [8, 0, 0])))) else (if i.val < 35 then (if i.val < 34 then (36, [12, 0, 0]) else (39, [14, 0, 0])) else (if i.val < 36 then (40, [15, 0, 0]) else (if i.val < 37 then (54, [0, 8, 0]) else (27, [8, 8, 0]))))))) else (if i.val < 57 then (if i.val < 47 then (if i.val < 42 then (if i.val < 40 then (if i.val < 39 then (36, [12, 8, 0]) else (39, [14, 8, 0])) else (if i.val < 41 then (40, [15, 8, 0]) else (72, [0, 12, 0]))) else (if i.val < 44 then (if i.val < 43 then (45, [8, 12, 0]) else (36, [12, 12, 0])) else (if i.val < 45 then (39, [14, 12, 0]) else (if i.val < 46 then (40, [15, 12, 0]) else (78, [0, 14, 0]))))) else (if i.val < 52 then (if i.val < 49 then (if i.val < 48 then (51, [8, 14, 0]) else (42, [12, 14, 0])) else (if i.val < 50 then (39, [14, 14, 0]) else (if i.val < 51 then (40, [15, 14, 0]) else (80, [0, 15, 0])))) else (if i.val < 54 then (if i.val < 53 then (53, [8, 15, 0]) else (44, [12, 15, 0])) else (if i.val < 55 then (41, [14, 15, 0]) else (if i.val < 56 then (40, [15, 15, 0]) else (54, [0, 0, 8])))))) else (if i.val < 67 then (if i.val < 62 then (if i.val < 59 then (if i.val < 58 then (54, [0, 8, 8]) else (27, [8, 8, 8])) else (if i.val < 60 then (36, [12, 8, 8]) else (if i.val < 61 then (72, [0, 12, 8]) else (45, [8, 12, 8])))) else (if i.val < 64 then (if i.val < 63 then (36, [12, 12, 8]) else (39, [14, 12, 8])) else (if i.val < 65 then (40, [15, 12, 8]) else (if i.val < 66 then (78, [0, 14, 8]) else (51, [8, 14, 8]))))) else (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then (42, [12, 14, 8]) else (39, [14, 14, 8])) else (if i.val < 70 then (40, [15, 14, 8]) else (if i.val < 71 then (80, [0, 15, 8]) else (53, [8, 15, 8])))) else (if i.val < 74 then (if i.val < 73 then (44, [12, 15, 8]) else (41, [14, 15, 8])) else (if i.val < 75 then (40, [15, 15, 8]) else (if i.val < 76 then (72, [0, 0, 12]) else (72, [0, 8, 12])))))))) else (if i.val < 115 then (if i.val < 96 then (if i.val < 86 then (if i.val < 81 then (if i.val < 79 then (if i.val < 78 then (45, [8, 8, 12]) else (72, [0, 12, 12])) else (if i.val < 80 then (45, [8, 12, 12]) else (36, [12, 12, 12]))) else (if i.val < 83 then (if i.val < 82 then (39, [14, 12, 12]) else (78, [0, 14, 12])) else (if i.val < 84 then (51, [8, 14, 12]) else (if i.val < 85 then (42, [12, 14, 12]) else (39, [14, 14, 12]))))) else (if i.val < 91 then (if i.val < 88 then (if i.val < 87 then (40, [15, 14, 12]) else (80, [0, 15, 12])) else (if i.val < 89 then (53, [8, 15, 12]) else (if i.val < 90 then (44, [12, 15, 12]) else (41, [14, 15, 12])))) else (if i.val < 93 then (if i.val < 92 then (40, [15, 15, 12]) else (78, [0, 0, 14])) else (if i.val < 94 then (78, [0, 8, 14]) else (if i.val < 95 then (78, [0, 12, 14]) else (51, [8, 12, 14])))))) else (if i.val < 105 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then (42, [12, 12, 14]) else (78, [0, 14, 14])) else (if i.val < 99 then (51, [8, 14, 14]) else (42, [12, 14, 14]))) else (if i.val < 102 then (if i.val < 101 then (39, [14, 14, 14]) else (40, [15, 14, 14])) else (if i.val < 103 then (80, [0, 15, 14]) else (if i.val < 104 then (53, [8, 15, 14]) else (44, [12, 15, 14]))))) else (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then (41, [14, 15, 14]) else (40, [15, 15, 14])) else (if i.val < 108 then (80, [0, 0, 15]) else (if i.val < 109 then (80, [0, 8, 15]) else (80, [0, 12, 15])))) else (if i.val < 112 then (if i.val < 111 then (53, [8, 12, 15]) else (80, [0, 14, 15])) else (if i.val < 113 then (53, [8, 14, 15]) else (if i.val < 114 then (44, [12, 14, 15]) else (41, [14, 14, 15]))))))) else (if i.val < 134 then (if i.val < 124 then (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then (80, [0, 15, 15]) else (53, [8, 15, 15])) else (if i.val < 118 then (44, [12, 15, 15]) else (41, [14, 15, 15]))) else (if i.val < 121 then (if i.val < 120 then (40, [15, 15, 15]) else (54, [0, 0, 0])) else (if i.val < 122 then (72, [0, 0, 0]) else (if i.val < 123 then (72, [0, 0, 8]) else (72, [0, 8, 8]))))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 125 then (45, [8, 8, 8]) else (78, [0, 0, 0])) else (if i.val < 127 then (78, [0, 0, 8]) else (if i.val < 128 then (78, [0, 0, 12]) else (78, [0, 8, 12])))) else (if i.val < 131 then (if i.val < 130 then (51, [8, 8, 12]) else (78, [0, 12, 12])) else (if i.val < 132 then (51, [8, 12, 12]) else (if i.val < 133 then (42, [12, 12, 12]) else (80, [0, 0, 0])))))) else (if i.val < 144 then (if i.val < 139 then (if i.val < 136 then (if i.val < 135 then (80, [0, 0, 8]) else (80, [0, 0, 12])) else (if i.val < 137 then (80, [0, 8, 12]) else (if i.val < 138 then (80, [0, 0, 14]) else (80, [0, 8, 14])))) else (if i.val < 141 then (if i.val < 140 then (80, [0, 12, 14]) else (53, [8, 12, 14])) else (if i.val < 142 then (44, [12, 12, 14]) else (if i.val < 143 then (80, [0, 14, 14]) else (53, [8, 14, 14]))))) else (if i.val < 149 then (if i.val < 146 then (if i.val < 145 then (44, [12, 14, 14]) else (41, [14, 14, 14])) else (if i.val < 147 then (78, [0, 8, 8]) else (if i.val < 148 then (51, [8, 8, 8]) else (53, [8, 8, 12])))) else (if i.val < 151 then (if i.val < 150 then (80, [0, 12, 12]) else (53, [8, 12, 12])) else (if i.val < 152 then (44, [12, 12, 12]) else (if i.val < 153 then (80, [0, 8, 8]) else (53, [8, 8, 8])))))))))
def state (i : Fin 154) : State :=
  ⟨(fun j => ⟨(codes i).1 / 3 ^ j.val % 3, Nat.mod_lt _ (by decide)⟩),
    (codes i).2.map (fun c => decode ⟨c % 16, Nat.mod_lt _ (by decide)⟩)⟩
def succ (i : Fin 154) : List (Fin 154) :=
  (if i.val < 77 then (if i.val < 38 then (if i.val < 19 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [1, 2, 3, 4, 5] else [6, 7, 8, 9, 10]) else (if i.val < 3 then [11, 12, 13, 14, 15] else [16, 17, 18, 19, 20])) else (if i.val < 6 then (if i.val < 5 then [21, 22, 23, 24, 25] else [26, 27, 28, 29, 30]) else (if i.val < 7 then [31, 32, 33, 34, 35] else (if i.val < 8 then [36, 37, 38, 39, 40] else [41, 42, 43, 44, 45])))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then [46, 47, 48, 49, 50] else [51, 52, 53, 54, 55]) else (if i.val < 12 then [56] else (if i.val < 13 then [57, 58, 59] else [60, 61, 62, 63, 64]))) else (if i.val < 16 then (if i.val < 15 then [65, 66, 67, 68, 69] else [70, 71, 72, 73, 74]) else (if i.val < 17 then [75] else (if i.val < 18 then [76, 77] else [78, 79, 80, 81]))))) else (if i.val < 28 then (if i.val < 23 then (if i.val < 21 then (if i.val < 20 then [82, 83, 84, 85, 86] else [87, 88, 89, 90, 91]) else (if i.val < 22 then [92] else [93])) else (if i.val < 25 then (if i.val < 24 then [94, 95, 96] else [97, 98, 99, 100, 101]) else (if i.val < 26 then [102, 103, 104, 105, 106] else (if i.val < 27 then [107] else [108])))) else (if i.val < 33 then (if i.val < 30 then (if i.val < 29 then [109, 110] else [111, 112, 113, 114]) else (if i.val < 31 then [115, 116, 117, 118, 119] else (if i.val < 32 then [31, 32, 33, 34, 35] else [36, 37, 38, 39, 40]))) else (if i.val < 35 then (if i.val < 34 then [41, 42, 43, 44, 45] else [46, 47, 48, 49, 50]) else (if i.val < 36 then [51, 52, 53, 54, 55] else (if i.val < 37 then [56] else [57, 58, 59])))))) else (if i.val < 57 then (if i.val < 47 then (if i.val < 42 then (if i.val < 40 then (if i.val < 39 then [60, 61, 62, 63, 64] else [65, 66, 67, 68, 69]) else (if i.val < 41 then [70, 71, 72, 73, 74] else [75])) else (if i.val < 44 then (if i.val < 43 then [76, 77] else [78, 79, 80, 81]) else (if i.val < 45 then [82, 83, 84, 85, 86] else (if i.val < 46 then [87, 88, 89, 90, 91] else [92])))) else (if i.val < 52 then (if i.val < 49 then (if i.val < 48 then [93] else [94, 95, 96]) else (if i.val < 50 then [97, 98, 99, 100, 101] else (if i.val < 51 then [102, 103, 104, 105, 106] else [107]))) else (if i.val < 54 then (if i.val < 53 then [108] else [109, 110]) else (if i.val < 55 then [111, 112, 113, 114] else (if i.val < 56 then [115, 116, 117, 118, 119] else [120]))))) else (if i.val < 67 then (if i.val < 62 then (if i.val < 59 then (if i.val < 58 then [56] else [57, 58, 59]) else (if i.val < 60 then [60, 61, 62, 63] else (if i.val < 61 then [75] else [76, 77]))) else (if i.val < 64 then (if i.val < 63 then [78, 79, 80, 81] else [82, 83, 84, 85, 86]) else (if i.val < 65 then [87, 88, 89, 90, 91] else (if i.val < 66 then [92] else [93])))) else (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then [94, 95, 96] else [97, 98, 99, 100, 101]) else (if i.val < 70 then [102, 103, 104, 105, 106] else (if i.val < 71 then [107] else [108]))) else (if i.val < 74 then (if i.val < 73 then [109, 110] else [111, 112, 113, 114]) else (if i.val < 75 then [115, 116, 117, 118, 119] else (if i.val < 76 then [121] else [122]))))))) else (if i.val < 115 then (if i.val < 96 then (if i.val < 86 then (if i.val < 81 then (if i.val < 79 then (if i.val < 78 then [123, 124] else [75]) else (if i.val < 80 then [76, 77] else [78, 79, 80, 81])) else (if i.val < 83 then (if i.val < 82 then [82, 83, 84, 85, 86] else [92]) else (if i.val < 84 then [93] else (if i.val < 85 then [94, 95, 96] else [97, 98, 99, 100, 101])))) else (if i.val < 91 then (if i.val < 88 then (if i.val < 87 then [102, 103, 104, 105, 106] else [107]) else (if i.val < 89 then [108] else (if i.val < 90 then [109, 110] else [111, 112, 113, 114]))) else (if i.val < 93 then (if i.val < 92 then [115, 116, 117, 118, 119] else [125]) else (if i.val < 94 then [126] else (if i.val < 95 then [127] else [128, 129]))))) else (if i.val < 105 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [130, 131, 132] else [92]) else (if i.val < 99 then [93] else [94, 95, 96])) else (if i.val < 102 then (if i.val < 101 then [97, 98, 99, 100, 101] else [102, 103, 104, 105, 106]) else (if i.val < 103 then [107] else (if i.val < 104 then [108] else [109, 110])))) else (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then [111, 112, 113, 114] else [115, 116, 117, 118, 119]) else (if i.val < 108 then [133] else (if i.val < 109 then [134] else [135]))) else (if i.val < 112 then (if i.val < 111 then [136] else [137]) else (if i.val < 113 then [138] else (if i.val < 114 then [139, 140, 141] else [142, 143, 144, 145])))))) else (if i.val < 134 then (if i.val < 124 then (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then [107] else [108]) else (if i.val < 118 then [109, 110] else [111, 112, 113, 114])) else (if i.val < 121 then (if i.val < 120 then [115, 116, 117, 118, 119] else [120]) else (if i.val < 122 then [121] else (if i.val < 123 then [121] else [122])))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 125 then [123, 124] else [125]) else (if i.val < 127 then [125] else (if i.val < 128 then [125] else [126]))) else (if i.val < 131 then (if i.val < 130 then [146, 147] else [127]) else (if i.val < 132 then [128, 129] else (if i.val < 133 then [130, 131, 132] else [133]))))) else (if i.val < 144 then (if i.val < 139 then (if i.val < 136 then (if i.val < 135 then [133] else [133]) else (if i.val < 137 then [134] else (if i.val < 138 then [133] else [134]))) else (if i.val < 141 then (if i.val < 140 then [135] else [136, 148]) else (if i.val < 142 then [149, 150, 151] else (if i.val < 143 then [137] else [138])))) else (if i.val < 149 then (if i.val < 146 then (if i.val < 145 then [139, 140, 141] else [142, 143, 144, 145]) else (if i.val < 147 then [126] else (if i.val < 148 then [146, 147] else [152, 153]))) else (if i.val < 151 then (if i.val < 150 then [135] else [136, 148]) else (if i.val < 152 then [149, 150, 151] else (if i.val < 153 then [134] else [152, 153]))))))))
def vectors (i : Fin 154) : List ℕ :=
  (if i.val < 77 then (if i.val < 38 then (if i.val < 19 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [1, 5, 25, 89, 249, 596, 1286, 2578, 4886, 8851, 15439, 26072, 42800] else [1, 5, 25, 89, 249, 596, 1286, 2578, 4886, 8851, 15439, 26072, 42800]) else (if i.val < 3 then [1, 5, 19, 54, 128, 273, 544, 1028, 1858, 3232, 5438, 8886, 14148] else [1, 5, 17, 44, 98, 199, 377, 676, 1159, 1914, 3061, 4760, 7220])) else (if i.val < 6 then (if i.val < 5 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 7 then [1, 5, 25, 89, 249, 596, 1286, 2578, 4886, 8851, 15439, 26072, 42800] else (if i.val < 8 then [1, 5, 19, 54, 128, 273, 544, 1028, 1858, 3232, 5438, 8886, 14148] else [1, 5, 17, 44, 98, 199, 377, 676, 1159, 1914, 3061, 4760, 7220])))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 12 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 13 then [1, 3, 8, 21, 53, 126, 279, 577, 1124, 2081, 3690, 6305, 10431] else [1, 5, 17, 44, 98, 199, 377, 676, 1159, 1914, 3061, 4760, 7220]))) else (if i.val < 16 then (if i.val < 15 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 17 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 18 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 4, 12, 31, 72, 152, 297, 546, 956, 1608, 2614, 4125, 6340]))))) else (if i.val < 28 then (if i.val < 23 then (if i.val < 21 then (if i.val < 20 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 22 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 25 then (if i.val < 24 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162]) else (if i.val < 26 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 27 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 33 then (if i.val < 30 then (if i.val < 29 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389]) else (if i.val < 31 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 32 then [1, 5, 25, 89, 249, 596, 1286, 2578, 4886, 8851, 15439, 26072, 42800] else [1, 5, 19, 54, 128, 273, 544, 1028, 1858, 3232, 5438, 8886, 14148]))) else (if i.val < 35 then (if i.val < 34 then [1, 5, 17, 44, 98, 199, 377, 676, 1159, 1914, 3061, 4760, 7220] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162]) else (if i.val < 36 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 37 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 3, 8, 21, 53, 126, 279, 577, 1124, 2081, 3690, 6305, 10431])))))) else (if i.val < 57 then (if i.val < 47 then (if i.val < 42 then (if i.val < 40 then (if i.val < 39 then [1, 5, 17, 44, 98, 199, 377, 676, 1159, 1914, 3061, 4760, 7220] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162]) else (if i.val < 41 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 44 then (if i.val < 43 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 4, 12, 31, 72, 152, 297, 546, 956, 1608, 2614, 4125, 6340]) else (if i.val < 45 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else (if i.val < 46 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 52 then (if i.val < 49 then (if i.val < 48 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91]) else (if i.val < 50 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else (if i.val < 51 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 54 then (if i.val < 53 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 55 then [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389] else (if i.val < 56 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 67 then (if i.val < 62 then (if i.val < 59 then (if i.val < 58 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 3, 8, 21, 53, 126, 279, 577, 1124, 2081, 3690, 6305, 10431]) else (if i.val < 60 then [1, 4, 12, 31, 72, 152, 297, 546, 956, 1608, 2614, 4125, 6340] else (if i.val < 61 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]))) else (if i.val < 64 then (if i.val < 63 then [1, 4, 12, 31, 72, 152, 297, 546, 956, 1608, 2614, 4125, 6340] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162]) else (if i.val < 65 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 66 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162]) else (if i.val < 70 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 71 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 74 then (if i.val < 73 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389]) else (if i.val < 75 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else (if i.val < 76 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))))) else (if i.val < 115 then (if i.val < 96 then (if i.val < 86 then (if i.val < 81 then (if i.val < 79 then (if i.val < 78 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 80 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 4, 12, 31, 72, 152, 297, 546, 956, 1608, 2614, 4125, 6340])) else (if i.val < 83 then (if i.val < 82 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 84 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 85 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162])))) else (if i.val < 91 then (if i.val < 88 then (if i.val < 87 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 89 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 90 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389]))) else (if i.val < 93 then (if i.val < 92 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 94 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 95 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]))))) else (if i.val < 105 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 99 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91])) else (if i.val < 102 then (if i.val < 101 then [1, 5, 15, 36, 74, 138, 241, 401, 642, 995, 1499, 2202, 3162] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 103 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 104 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))) else (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389] else [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193]) else (if i.val < 108 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 109 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 112 then (if i.val < 111 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 113 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 114 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389])))))) else (if i.val < 134 then (if i.val < 124 then (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 118 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389])) else (if i.val < 121 then (if i.val < 120 then [1, 5, 13, 26, 47, 80, 130, 203, 306, 447, 635, 880, 1193] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 122 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 123 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 125 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 127 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 128 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 131 then (if i.val < 130 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 132 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else (if i.val < 133 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 144 then (if i.val < 139 then (if i.val < 136 then (if i.val < 135 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 137 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 138 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 141 then (if i.val < 140 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]) else (if i.val < 142 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else (if i.val < 143 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 149 then (if i.val < 146 then (if i.val < 145 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else [1, 4, 9, 17, 29, 46, 69, 99, 137, 184, 241, 309, 389]) else (if i.val < 147 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 148 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]))) else (if i.val < 151 then (if i.val < 150 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]) else (if i.val < 152 then [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91] else (if i.val < 153 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]))))))))
def v (k : Fin 13) (i : Fin 154) : ℕ := (vectors i)[k.val]!
def accepted (_ : Fin 154) : ℕ := 1
end A223840Table

namespace A223840Certificate
open A223840Proof A223840Table A223840Count

def tableIndex (n : ℕ) : Fin 154 := ⟨n % 154, Nat.mod_lt _ (by decide)⟩
def LocalCheck (i : Fin 154) : Prop :=
  allCols.filterMap (step (state i)) = (succ i).map state
def NumericCheck (s : Fin 154) : Prop :=
  v 0 s = 1 ∧ (∀ k : Fin 12, ((succ s).map (v k.castSucc)).sum = v k.succ s) ∧
  v 12 s + 36 * v 10 s + 126 * v 8 s + 84 * v 6 s + 9 * v 4 s = 9 * v 11 s + 84 * v 9 s + 126 * v 7 s + 36 * v 5 s + v 3 s
instance (i : Fin 154) : Decidable (LocalCheck i) := inferInstanceAs
  (Decidable (allCols.filterMap (step (state i)) = (succ i).map state))
instance (i : Fin 154) : Decidable (NumericCheck i) := by unfold NumericCheck; infer_instance

def LocalBlock (b : ℕ) : Prop := ∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))
def NumericBlock (b : ℕ) : Prop := ∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))
instance (b : ℕ) : Decidable (LocalBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))))
instance (b : ℕ) : Decidable (NumericBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem numeric_blocks : ∀ b : Fin 20, NumericBlock b.val := by
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
  intro b
  fin_cases b <;> assumption

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem local_blocks : ∀ b : Fin 20, LocalBlock b.val := by
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
  intro b
  fin_cases b <;> assumption

theorem covered (P : Fin 154 → Prop)
    (h : ∀ b : Fin 20, ∀ j : Fin 8, P (tableIndex (8 * b.val + j.val))) :
    ∀ i, P i := by
  intro i
  let b : Fin 20 := ⟨i.val / 8, by omega⟩
  let j : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : tableIndex (8 * b.val + j.val) = i := by
    apply Fin.ext
    simp only [tableIndex, b, j]
    omega
  simpa only [he] using h b j

theorem local_table (i : Fin 154) :
    allCols.filterMap (step (state i)) = (succ i).map state :=
  covered LocalCheck local_blocks i

theorem numeric_table (i : Fin 154) : NumericCheck i :=
  covered NumericCheck numeric_blocks i

theorem state_zero : state 0 = start := by decide +kernel

theorem paths_vectors (k : Fin 13) (i : Fin 154) :
    paths succ accepted k.val i = v k i :=
  paths_eq_vectors succ accepted v (fun s => (numeric_table s).1)
    (fun k s => (numeric_table s).2.1 k) k i

theorem recurrence_base (s : Fin 154) :
    paths succ accepted 12 s + 36 * paths succ accepted 10 s +
      126 * paths succ accepted 8 s + 84 * paths succ accepted 6 s + 9 * paths succ accepted 4 s =
    9 * paths succ accepted 11 s + 84 * paths succ accepted 9 s +
      126 * paths succ accepted 7 s + 36 * paths succ accepted 5 s + paths succ accepted 3 s := by
  have hv (n : Fin 13) := paths_vectors n s
  change paths succ accepted (12 : Fin 13).val s + 36 * paths succ accepted (10 : Fin 13).val s +
      126 * paths succ accepted (8 : Fin 13).val s + 84 * paths succ accepted (6 : Fin 13).val s +
      9 * paths succ accepted (4 : Fin 13).val s =
    9 * paths succ accepted (11 : Fin 13).val s + 84 * paths succ accepted (9 : Fin 13).val s +
      126 * paths succ accepted (7 : Fin 13).val s + 36 * paths succ accepted (5 : Fin 13).val s +
      paths succ accepted (3 : Fin 13).val s
  simp only [hv]
  exact (numeric_table s).2.2
end A223840Certificate

namespace A223840Table
open A223840Count A223840Certificate

def indexedCount (n : ℕ) : ℕ := paths succ accepted n 0

theorem indexed_vector (k : Fin 13) : indexedCount k.val = v k 0 :=
  paths_vectors k 0

theorem initial_1 : indexedCount 1 = 5 := by
  have h := indexed_vector (1 : Fin 13)
  have hv : v 1 0 = 5 := by decide +kernel
  exact h.trans hv

theorem initial_2 : indexedCount 2 = 25 := by
  have h := indexed_vector (2 : Fin 13)
  have hv : v 2 0 = 25 := by decide +kernel
  exact h.trans hv

theorem initial_3 : indexedCount 3 = 89 := by
  have h := indexed_vector (3 : Fin 13)
  have hv : v 3 0 = 89 := by decide +kernel
  exact h.trans hv

theorem initial_4 : indexedCount 4 = 249 := by
  have h := indexed_vector (4 : Fin 13)
  have hv : v 4 0 = 249 := by decide +kernel
  exact h.trans hv

theorem initial_5 : indexedCount 5 = 596 := by
  have h := indexed_vector (5 : Fin 13)
  have hv : v 5 0 = 596 := by decide +kernel
  exact h.trans hv

theorem initial_6 : indexedCount 6 = 1286 := by
  have h := indexed_vector (6 : Fin 13)
  have hv : v 6 0 = 1286 := by decide +kernel
  exact h.trans hv

theorem initial_7 : indexedCount 7 = 2578 := by
  have h := indexed_vector (7 : Fin 13)
  have hv : v 7 0 = 2578 := by decide +kernel
  exact h.trans hv

theorem initial_8 : indexedCount 8 = 4886 := by
  have h := indexed_vector (8 : Fin 13)
  have hv : v 8 0 = 4886 := by decide +kernel
  exact h.trans hv

theorem initial_9 : indexedCount 9 = 8851 := by
  have h := indexed_vector (9 : Fin 13)
  have hv : v 9 0 = 8851 := by decide +kernel
  exact h.trans hv

theorem initial_10 : indexedCount 10 = 15439 := by
  have h := indexed_vector (10 : Fin 13)
  have hv : v 10 0 = 15439 := by decide +kernel
  exact h.trans hv

theorem initial_11 : indexedCount 11 = 26072 := by
  have h := indexed_vector (11 : Fin 13)
  have hv : v 11 0 = 26072 := by decide +kernel
  exact h.trans hv

theorem initial_12 : indexedCount 12 = 42800 := by
  have h := indexed_vector (12 : Fin 13)
  have hv : v 12 0 = 42800 := by decide +kernel
  exact h.trans hv

theorem indexed_recurrence (n : ℕ) :
    indexedCount (n + 12) + 36 * indexedCount (n + 10) +
      126 * indexedCount (n + 8) + 84 * indexedCount (n + 6) + 9 * indexedCount (n + 4) =
    9 * indexedCount (n + 11) + 84 * indexedCount (n + 9) +
      126 * indexedCount (n + 7) + 36 * indexedCount (n + 5) + indexedCount (n + 3) :=
  paths_recurrence succ accepted recurrence_base n 0
end A223840Table

namespace A223840Formula
open PowerSeries
theorem integer_recurrence (a : ℕ → ℕ)
    (hs : ∀ n : ℕ,
  a (n + 12) + 36 * a (n + 10) + 126 * a (n + 8) +
    84 * a (n + 6) + 9 * a (n + 4) =
  9 * a (n + 11) + 84 * a (n + 9) + 126 * a (n + 7) +
    36 * a (n + 5) + a (n + 3)) (n : ℕ) (hn : 11 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) +
      36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  have h := hs (n - 12)
  have heq (k : ℕ) (hk : k ≤ 12) : n - 12 + k = n - (12 - k) := by omega
  rw [heq 12 (by decide), heq 10 (by decide), heq 8 (by decide),
    heq 6 (by decide), heq 4 (by decide), heq 11 (by decide),
    heq 9 (by decide), heq 7 (by decide), heq 5 (by decide),
    heq 3 (by decide)] at h
  norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at h
  have hz : (a n : ℤ) + 36 * a (n - 2) + 126 * a (n - 4) +
      84 * a (n - 6) + 9 * a (n - 8) =
    9 * a (n - 1) + 84 * a (n - 3) + 126 * a (n - 5) +
      36 * a (n - 7) + a (n - 9) := by exact_mod_cast h
  linarith

theorem generating_function (a : ℕ → ℕ)
(h1 : a 1 = 5) (h2 : a 2 = 25) (h3 : a 3 = 89)
(h4 : a 4 = 249) (h5 : a 5 = 596) (h6 : a 6 = 1286)
(h7 : a 7 = 2578) (h8 : a 8 = 4886) (h9 : a 9 = 8851)
(h10 : a 10 = 15439) (h11 : a 11 = 26072)
(hs : ∀ n : ℕ,
  a (n + 12) + 36 * a (n + 10) + 126 * a (n + 8) +
    84 * a (n + 6) + 9 * a (n + 4) =
  9 * a (n + 11) + 84 * a (n + 9) + 126 * a (n + 7) +
    36 * a (n + 5) + a (n + 3)) :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 +
        28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10 := by
  let g : PowerSeries ℚ := PowerSeries.mk fun n => (a (n + 1) : ℚ)
  change g * (1 - X) ^ 9 = _
  have hl : g * (1 - X) ^ 9 =
      g * X ^ 0 - 9 • (g * X ^ 1) + 36 • (g * X ^ 2) - 84 • (g * X ^ 3) +
      126 • (g * X ^ 4) - 126 • (g * X ^ 5) + 84 • (g * X ^ 6) -
      36 • (g * X ^ 7) + 9 • (g * X ^ 8) - g * X ^ 9 := by
    simp only [nsmul_eq_mul]
    ring
  have hr : (5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 +
      28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : PowerSeries ℚ) =
      5 • X ^ 0 - 20 • X ^ 1 + 44 • X ^ 2 - 72 • X ^ 3 + 89 • X ^ 4 -
        70 • X ^ 5 + 28 • X ^ 6 - 4 • X ^ 7 + 4 • X ^ 8 - 4 • X ^ 9 + X ^ 10 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_nsmul]
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · have hc (k : ℕ) (hk : k ≤ n) : coeff n (g * X ^ k) = (a (n - k + 1) : ℚ) := by
      rw [coeff_mul_X_pow', if_pos hk]
      simp only [g, coeff_mk]
    have hx (k : ℕ) (hk : k < n) : coeff n (X ^ k : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    simp (disch := omega) only [hc, hx, nsmul_eq_mul, mul_zero, add_zero,
      sub_zero, Nat.sub_zero]
    norm_num only [Nat.cast_ofNat]
    have hrec := hs (n - 11)
    have heq (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 12) : n - 11 + k = n - (12 - k) + 1 := by omega
    rw [heq 12 (by omega), heq 10 (by omega), heq 8 (by omega),
      heq 6 (by omega), heq 4 (by omega), heq 11 (by omega),
      heq 9 (by omega), heq 7 (by omega), heq 5 (by omega),
      heq 3 (by omega)] at hrec
    norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at hrec
    have hq : (a (n + 1) : ℚ) + 36 * a (n - 2 + 1) + 126 * a (n - 4 + 1) +
        84 * a (n - 6 + 1) + 9 * a (n - 8 + 1) =
      9 * a (n - 1 + 1) + 84 * a (n - 3 + 1) + 126 * a (n - 5 + 1) +
        36 * a (n - 7 + 1) + a (n - 9 + 1) := by exact_mod_cast hrec
    linarith

theorem of_recurrence (a : ℕ → ℕ)
(h1 : a 1 = 5) (h2 : a 2 = 25) (h3 : a 3 = 89)
(h4 : a 4 = 249) (h5 : a 5 = 596) (h6 : a 6 = 1286)
(h7 : a 7 = 2578) (h8 : a 8 = 4886) (h9 : a 9 = 8851)
(h10 : a 10 = 15439) (h11 : a 11 = 26072)
(hs : ∀ n : ℕ,
  a (n + 12) + 36 * a (n + 10) + 126 * a (n + 8) +
    84 * a (n + 6) + 9 * a (n + 4) =
  9 * a (n + 11) + 84 * a (n + 9) + 126 * a (n + 7) +
    36 * a (n + 5) + a (n + 3)) :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 +
        28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) +
      36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  exact ⟨generating_function a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hs,
    integer_recurrence a hs⟩
end A223840Formula

namespace A223840Proof
open OMA.S_oeis_a223840 A223840Table A223840Certificate PowerSeries

theorem a_eq_indexed (n : ℕ) : a n = indexedCount n :=
  a_eq_paths run_correct state succ accepted 0 local_table (fun _ => rfl) state_zero n

theorem result :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 +
        28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) +
      36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  have ha : a = indexedCount := funext a_eq_indexed
  rw [ha]
  exact A223840Formula.of_recurrence indexedCount initial_1 initial_2 initial_3
    initial_4 initial_5 initial_6 initial_7 initial_8 initial_9 initial_10 initial_11
    indexed_recurrence

end A223840Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a223840.main := by
  exact A223840Proof.result
