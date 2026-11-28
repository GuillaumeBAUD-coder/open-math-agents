import OMAStatements.S_oeis_a224041
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
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
A224041: exact enumeration of five-row binary arrays with nondecreasing
rows and diagonals and unimodal antidiagonals.

A four-column history checks every new antidiagonal valley. An exact
matrix-to-column-list equivalence and a reversal bijection identify the
canonical finite-set cardinality with paths in a closed 963-state table.
Kernel checks certify all transitions and eleven count vectors. The sixth
finite difference vanishes from suffix length four, and linear induction
propagates it to all lengths. This proves the polynomial, generating
function, and recurrence in the existing statement without changing it.

Source: https://oeis.org/A224041
Array definition: R. H. Hardin (2013).
Generating-function and recurrence conjectures: Colin Barker (2018).
Canonical matrix statement: PR35503.
Generic counting infrastructure is adapted from our independent proofs
of A223840 (PR40005) and A224040 (PR40465).
-/

namespace A224041Proof
open OMA.S_oeis_a224041
abbrev Col := Fin 5 → Fin 2

def adjacent (u v : Col) : Prop :=
  (∀ i : Fin 5, u i ≤ v i) ∧ (∀ i : Fin 4, u i.castSucc ≤ v i.succ)
instance (u v : Col) : Decidable (adjacent u v) := inferInstanceAs
  (Decidable ((∀ i : Fin 5, u i ≤ v i) ∧ (∀ i : Fin 4, u i.castSucc ≤ v i.succ)))

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

def zeroCol : Col := fun _ => 0

def valleyOK (l : List Col) : Prop :=
  ∀ i1 i2 i3 : Fin 5, i1 < i2 → i2 < i3 → i3.val - i1.val < l.length →
    ¬ ((l.getD (i3.val - i2.val) zeroCol) i2 <
          (l.getD (i3.val - i1.val) zeroCol) i1 ∧
       (l.getD (i3.val - i2.val) zeroCol) i2 < (l.getD 0 zeroCol) i3)

def triples : List (Fin 5 × Fin 5 × Fin 5) :=
  [(0,1,2),(0,1,3),(0,1,4),(0,2,3),(0,2,4),
   (0,3,4),(1,2,3),(1,2,4),(1,3,4),(2,3,4)]

theorem mem_triples (i1 i2 i3 : Fin 5) :
    (i1,i2,i3) ∈ triples ↔ i1 < i2 ∧ i2 < i3 := by
  have h : ∀ i1 i2 i3 : Fin 5, (i1,i2,i3) ∈ triples ↔ i1 < i2 ∧ i2 < i3 := by
    decide +kernel
  exact h i1 i2 i3

def tripleOK (l : List Col) (t : Fin 5 × Fin 5 × Fin 5) : Prop :=
  t.2.2.val - t.1.val < l.length →
    ¬ ((l.getD (t.2.2.val - t.2.1.val) zeroCol) t.2.1 <
          (l.getD (t.2.2.val - t.1.val) zeroCol) t.1 ∧
       (l.getD (t.2.2.val - t.2.1.val) zeroCol) t.2.1 <
          (l.getD 0 zeroCol) t.2.2)
instance (l : List Col) (t : Fin 5 × Fin 5 × Fin 5) : Decidable (tripleOK l t) := by
  unfold tripleOK; infer_instance

def valleyCheck (l : List Col) : Bool := triples.all fun t => decide (tripleOK l t)

theorem valleyCheck_iff (l : List Col) : valleyCheck l = true ↔ valleyOK l := by
  simp only [valleyCheck, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i1 i2 i3 h12 h23 hlen
    exact h (i1,i2,i3) ((mem_triples i1 i2 i3).mpr ⟨h12,h23⟩) hlen
  · intro h t ht
    rcases t with ⟨i1,i2,i3⟩
    have hh := (mem_triples i1 i2 i3).mp ht
    exact h i1 i2 i3 hh.1 hh.2

def localOK (s : State) (c : Col) : Prop :=
  headOK s c ∧ valleyCheck (c :: s.history) = true
instance (s : State) (c : Col) : Decidable (localOK s c) := inferInstanceAs
  (Decidable (headOK s c ∧ valleyCheck (c :: s.history) = true))

def nextState (s : State) (c : Col) : State := ⟨(c :: s.history).take 4⟩
def step (s : State) (c : Col) : Option State :=
  if localOK s c then some (nextState s c) else none

def decode (c : Fin 32) (i : Fin 5) : Fin 2 :=
  ⟨c.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩
def allCols : List Col := List.ofFn decode
theorem decode_injective : Function.Injective decode := by decide +kernel
noncomputable def colEquiv : Fin 32 ≃ Col :=
  Equiv.ofBijective decode
    ((Fintype.bijective_iff_injective_and_card decode).mpr
      ⟨decode_injective, by simp⟩)
theorem sum_allCols (f : Col → ℕ) :
    (allCols.map f).sum = ∑ c : Col, f c := by
  rw [allCols, List.map_ofFn, List.sum_ofFn]
  exact colEquiv.sum_comp f

def successors (s : State) : List State := allCols.filterMap (step s)
end A224041Proof

namespace A224041Proof
open OMA.S_oeis_a224041

def arrayOf (l : List Col) : Fin 5 → Fin l.length → Fin 2 := fun i j => l.get j i

def GoodList (l : List Col) : Prop := Good (arrayOf l)

def Spec (l : List Col) : Prop :=
  l.IsChain adjacent ∧
  ∀ i₁ i₂ i₃ : Fin 5, ∀ j₁ j₂ j₃ : ℕ,
    j₁ < l.length → j₂ < l.length → j₃ < l.length →
    i₁ < i₂ → i₂ < i₃ →
    i₁.val + j₁ = i₂.val + j₂ → i₂.val + j₂ = i₃.val + j₃ →
    ¬ ((l.getD j₂ zeroCol) i₂ < (l.getD j₁ zeroCol) i₁ ∧
      (l.getD j₂ zeroCol) i₂ < (l.getD j₃ zeroCol) i₃)

end A224041Proof

namespace A224041Proof
open OMA.S_oeis_a224041

theorem goodList_iff_spec (l : List Col) : GoodList l ↔ Spec l := by
  constructor
  · intro h
    rcases h with ⟨hr, hd, hv⟩
    refine ⟨List.isChain_iff_getElem.mpr ?_, ?_⟩
    · intro j hj
      constructor
      · intro i
        exact hr i ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
      · intro i
        exact hd i.castSucc i.succ ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl rfl
    · intro i₁ i₂ i₃ j₁ j₂ j₃ hj₁ hj₂ hj₃ hi₁ hi₂ he₁ he₂
      rw [List.getD_eq_getElem l zeroCol hj₁,
        List.getD_eq_getElem l zeroCol hj₂, List.getD_eq_getElem l zeroCol hj₃]
      exact hv i₁ i₂ i₃ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ ⟨j₃, hj₃⟩ hi₁ hi₂ he₁ he₂
  · rintro ⟨hc, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j j' he
      rcases j with ⟨j, hj⟩
      rcases j' with ⟨j', hj'⟩
      change j' = j + 1 at he
      subst j'
      exact ((List.isChain_iff_getElem.mp hc) j hj').1 i
    · intro i i' j j' hi hj
      rcases i with ⟨i, hi₀⟩
      rcases i' with ⟨i', hi'⟩
      rcases j with ⟨j, hj₀⟩
      rcases j' with ⟨j', hj'⟩
      change i' = i + 1 at hi
      change j' = j + 1 at hj
      subst i'
      subst j'
      exact ((List.isChain_iff_getElem.mp hc) j hj').2 ⟨i, by omega⟩
    · intro i₁ i₂ i₃ j₁ j₂ j₃ hi₁ hi₂ he₁ he₂
      have h := hv i₁ i₂ i₃ j₁.val j₂.val j₃.val j₁.isLt j₂.isLt j₃.isLt
        hi₁ hi₂ he₁ he₂
      rw [List.getD_eq_getElem l zeroCol j₁.isLt,
        List.getD_eq_getElem l zeroCol j₂.isLt, List.getD_eq_getElem l zeroCol j₃.isLt] at h
      exact h

theorem goodList_ofFn {n : ℕ} (w : Fin n → Col) :
    GoodList (List.ofFn w) ↔ Good (fun i j => w j i) := by
  constructor
  · rintro ⟨hr, hd, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j j' h
      simpa [arrayOf, List.get_eq_getElem] using
        hr i ⟨j.val, by rw [List.length_ofFn]; exact j.isLt⟩ ⟨j'.val, by rw [List.length_ofFn]; exact j'.isLt⟩ h
    · intro i i' j j' hi hj
      simpa [arrayOf, List.get_eq_getElem] using
        hd i i' ⟨j.val, by rw [List.length_ofFn]; exact j.isLt⟩ ⟨j'.val, by rw [List.length_ofFn]; exact j'.isLt⟩ hi hj
    · intro i₁ i₂ i₃ j₁ j₂ j₃ hi₁ hi₂ he₁ he₂
      simpa [arrayOf, List.get_eq_getElem] using
        hv i₁ i₂ i₃ ⟨j₁.val, by rw [List.length_ofFn]; exact j₁.isLt⟩
          ⟨j₂.val, by rw [List.length_ofFn]; exact j₂.isLt⟩ ⟨j₃.val, by rw [List.length_ofFn]; exact j₃.isLt⟩ hi₁ hi₂ he₁ he₂
  · rintro ⟨hr, hd, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j j' h
      simpa [arrayOf, List.get_eq_getElem] using
        hr i ⟨j.val, by simpa using j.isLt⟩ ⟨j'.val, by simpa using j'.isLt⟩ h
    · intro i i' j j' hi hj
      simpa [arrayOf, List.get_eq_getElem] using
        hd i i' ⟨j.val, by simpa using j.isLt⟩ ⟨j'.val, by simpa using j'.isLt⟩ hi hj
    · intro i₁ i₂ i₃ j₁ j₂ j₃ hi₁ hi₂ he₁ he₂
      simpa [arrayOf, List.get_eq_getElem] using
        hv i₁ i₂ i₃ ⟨j₁.val, by simpa using j₁.isLt⟩
          ⟨j₂.val, by simpa using j₂.isLt⟩ ⟨j₃.val, by simpa using j₃.isLt⟩ hi₁ hi₂ he₁ he₂

theorem a_eq_card_words (n : ℕ) :
    a n = Nat.card {w : Fin n → Col // GoodList (List.ofFn w)} := by
  classical
  let e : (Fin 5 → Fin n → Fin 2) ≃ (Fin n → Col) := {
    toFun := fun x j i => x i j
    invFun := fun w i j => w j i
    left_inv := by intro x; rfl
    right_inv := by intro w; rfl }
  calc
    a n = Nat.card {x : Fin 5 → Fin n → Fin 2 // Good x} := by
      simp [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := Nat.card_congr (e.subtypeEquiv (by
      intro x
      exact (goodList_ofFn (e x)).symm))

end A224041Proof

namespace A224041Proof
open OMA.S_oeis_a224041

theorem spec_nil : Spec [] := by
  simp [Spec]

theorem spec_tail {c : Col} {l : List Col} (h : Spec (c :: l)) : Spec l := by
  refine ⟨h.1.tail, ?_⟩
  intro i₁ i₂ i₃ j₁ j₂ j₃ h₁ h₂ h₃ hi₁ hi₂ he₁ he₂
  have hh := h.2 i₁ i₂ i₃ (j₁ + 1) (j₂ + 1) (j₃ + 1)
    (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
    hi₁ hi₂ (by omega) (by omega)
  simpa only [List.getD_cons_succ] using hh

theorem spec_cons_iff (c : Col) (l : List Col) :
    Spec (c :: l) ↔
      (∀ d ∈ l.head?, adjacent c d) ∧ valleyOK (c :: l) ∧ Spec l := by
  constructor
  · intro h
    refine ⟨(List.isChain_cons.mp h.1).1, ?_, spec_tail h⟩
    intro i₁ i₂ i₃ hi₁ hi₂ hj
    exact h.2 i₁ i₂ i₃ (i₃.val - i₁.val) (i₃.val - i₂.val) 0
      hj (by omega) (by simp) hi₁ hi₂ (by omega) (by omega)
  · rintro ⟨hc, hv, hl⟩
    refine ⟨List.isChain_cons.mpr ⟨hc, hl.1⟩, ?_⟩
    intro i₁ i₂ i₃ j₁ j₂ j₃ h₁ h₂ h₃ hi₁ hi₂ he₁ he₂
    cases j₃ with
    | zero =>
        have hj₁ : j₁ = i₃.val - i₁.val := by omega
        have hj₂ : j₂ = i₃.val - i₂.val := by omega
        subst j₁
        subst j₂
        exact hv i₁ i₂ i₃ hi₁ hi₂ h₁
    | succ j₃ =>
        cases j₂ with
        | zero => omega
        | succ j₂ =>
            cases j₁ with
            | zero => omega
            | succ j₁ =>
                have hh := hl.2 i₁ i₂ i₃ j₁ j₂ j₃
                  (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
                  hi₁ hi₂ (by omega) (by omega)
                simpa only [List.getD_cons_succ] using hh

theorem getD_take_of_lt {A : Type*} (l : List A) (k j : ℕ) (a : A)
    (hj : j < k) : (l.take k).getD j a = l.getD j a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

theorem valleyOK_take (l : List Col) : valleyOK (l.take 5) ↔ valleyOK l := by
  constructor
  · intro h i₁ i₂ i₃ hi₁ hi₂ hj
    have hb : i₃.val - i₁.val < 5 := by omega
    have hm : i₃.val - i₂.val < 5 := by omega
    have hh := h i₁ i₂ i₃ hi₁ hi₂ (by simpa only [List.length_take, Nat.lt_min] using And.intro hb hj)
    simpa only [getD_take_of_lt l 5 _ zeroCol hb,
      getD_take_of_lt l 5 _ zeroCol hm, getD_take_of_lt l 5 0 zeroCol (by decide)] using hh
  · intro h i₁ i₂ i₃ hi₁ hi₂ hj
    have hb : i₃.val - i₁.val < 5 := by omega
    have hm : i₃.val - i₂.val < 5 := by omega
    have hj' : i₃.val - i₁.val < l.length := by
      simp only [List.length_take, Nat.lt_min] at hj
      exact hj.2
    have hh := h i₁ i₂ i₃ hi₁ hi₂ hj'
    simpa only [getD_take_of_lt l 5 _ zeroCol hb,
      getD_take_of_lt l 5 _ zeroCol hm, getD_take_of_lt l 5 0 zeroCol (by decide)] using hh

theorem valleyOK_cons_take (c : Col) (l : List Col) :
    valleyOK (c :: l.take 4) ↔ valleyOK (c :: l) := by
  simpa only [List.take_succ_cons] using valleyOK_take (c :: l)

end A224041Proof

namespace A224041Proof

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

end A224041Proof

namespace A224041Proof

theorem run_tracks {l : List Col} {s : State} (h : run l = some s) :
    s.history = l.take 4 := by
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
    (ht : s.history = l.take 4) (c : Col) :
    localOK s c ↔ (∀ d ∈ l.head?, adjacent c d) ∧ valleyOK (c :: l) := by
  simp only [localOK, ht, valleyCheck_iff, valleyOK_cons_take]
  apply and_congr_left
  intro _
  cases l <;> simp [headOK, ht]

theorem run_correct_spec (l : List Col) : (run l).isSome = true ↔ Spec l := by
  induction l with
  | nil => simp [run, spec_nil]
  | cons c l ih =>
      cases ht : run l with
      | none =>
          constructor
          · simp [run, ht]
          · intro h
            have := ih.mpr (spec_tail h)
            simp [ht] at this
      | some s =>
          have hl : Spec l := ih.mp (by simp [ht])
          calc
            (run (c :: l)).isSome = true ↔ localOK s c := by
              simp only [run, ht, Option.bind_some]
              by_cases hok : localOK s c <;> simp [step, hok]
            _ ↔ _ := localOK_iff_tracks (run_tracks ht) c
            _ ↔ Spec (c :: l) := by
              rw [spec_cons_iff]
              simp [hl]

end A224041Proof

namespace A224041Count
variable {S : Type*}
def paths (succ : S → List S) (accepted : S → ℕ) : ℕ → S → ℕ
  | 0, s => accepted s
  | n + 1, s => ((succ s).map (paths succ accepted n)).sum

lemma sum_balance (L : List S) (f : Fin 11 → S → ℕ)
    (h : ∀ s, f 10 s + 15 * f 8 s + 15 * f 6 s + f 4 s =
      6 * f 9 s + 20 * f 7 s + 6 * f 5 s) :
    (L.map (f 10)).sum + 15 * (L.map (f 8)).sum + 15 * (L.map (f 6)).sum + (L.map (f 4)).sum =
      6 * (L.map (f 9)).sum + 20 * (L.map (f 7)).sum + 6 * (L.map (f 5)).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs := h s
    omega

theorem paths_recurrence (succ : S → List S) (accepted : S → ℕ)
    (hbase : ∀ s, paths succ accepted 10 s + 15 * paths succ accepted 8 s + 15 * paths succ accepted 6 s + paths succ accepted 4 s =
      6 * paths succ accepted 9 s + 20 * paths succ accepted 7 s + 6 * paths succ accepted 5 s) :
    ∀ n s, paths succ accepted (n + 10) s + 15 * paths succ accepted (n + 8) s + 15 * paths succ accepted (n + 6) s + paths succ accepted (n + 4) s =
      6 * paths succ accepted (n + 9) s + 20 * paths succ accepted (n + 7) s + 6 * paths succ accepted (n + 5) s := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accepted (n + 10))).sum + 15 * ((succ s).map (paths succ accepted (n + 8))).sum + 15 * ((succ s).map (paths succ accepted (n + 6))).sum + ((succ s).map (paths succ accepted (n + 4))).sum =
      6 * ((succ s).map (paths succ accepted (n + 9))).sum + 20 * ((succ s).map (paths succ accepted (n + 7))).sum + 6 * ((succ s).map (paths succ accepted (n + 5))).sum
    exact sum_balance (succ s) (fun k => paths succ accepted (n + k.val)) ih

theorem paths_eq_vectors (succ : S → List S) (accepted : S → ℕ)
    (v : Fin 11 → S → ℕ) (hzero : ∀ s, v 0 s = accepted s)
    (hnext : ∀ k : Fin 10, ∀ s,
      ((succ s).map (v k.castSucc)).sum = v k.succ s) :
    ∀ k : Fin 11, ∀ s, paths succ accepted k.val s = v k s := by
  intro k
  induction k using Fin.induction with
  | zero => intro s; exact (hzero s).symm
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accepted k.val)).sum = v k.succ s
    rw [show paths succ accepted k.val = v k.castSucc from funext ih]
    exact hnext k s
end A224041Count

namespace A224041Proof
open OMA.S_oeis_a224041

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
    ∀ n i, suffixCount (state i) n = A224041Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_allCols, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A224041Count.paths succ accepted n from funext ih]
    rfl

theorem run_correct (l : List Col) : (run l).isSome = true ↔ GoodList l :=
  (run_correct_spec l).trans (goodList_iff_spec l).symm

theorem a_eq_suffix
    (hcorrect : ∀ l, (run l).isSome = true ↔ GoodList l) (n : ℕ) :
    a n = suffixCount start n := by
  let e : {l : List Col // l.length = n ∧ GoodList l} ≃
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
    a n = Nat.card {l : List Col // l.length = n ∧ GoodList l} := by
      rw [card_lists]
      exact a_eq_card_words n
    _ = Nat.card {l : List Col // l.length = n ∧
        (runFrom start l).isSome = true} := Nat.card_congr e
    _ = suffixCount start n := by rw [card_lists]; rfl

theorem a_eq_paths
    (hcorrect : ∀ l, (run l).isSome = true ↔ GoodList l)
    (state : I → State) (succ : I → List I) (accepted : I → ℕ) (initial : I)
    (hstep : ∀ i, allCols.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, 1 = accepted i) (hstart : state initial = start) (n : ℕ) :
    a n = A224041Count.paths succ accepted n initial := by
  rw [a_eq_suffix hcorrect, ← hstart]
  exact suffixCount_eq_paths state succ accepted hstep haccept n initial

end A224041Proof

namespace A224041Table
open A224041Proof
def codes (i : Fin 963) : List ℕ :=
  (if i.val < 481 then (if i.val < 240 then (if i.val < 120 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [0] else [1])) else (if i.val < 5 then (if i.val < 4 then [2] else [3]) else (if i.val < 6 then [4] else [5]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then [6] else [7]) else (if i.val < 10 then [8] else [9])) else (if i.val < 13 then (if i.val < 12 then [10] else [11]) else (if i.val < 14 then [12] else [13])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then [14] else (if i.val < 17 then [15] else [16])) else (if i.val < 20 then (if i.val < 19 then [17] else [18]) else (if i.val < 21 then [19] else [20]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then [21] else [22]) else (if i.val < 25 then [23] else [24])) else (if i.val < 28 then (if i.val < 27 then [25] else [26]) else (if i.val < 29 then [27] else [28]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then [29] else (if i.val < 32 then [30] else [31])) else (if i.val < 35 then (if i.val < 34 then [0, 0] else [0, 1]) else (if i.val < 36 then [0, 2] else [0, 3]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then [1, 3] else [0, 4]) else (if i.val < 40 then [0, 5] else [0, 6])) else (if i.val < 43 then (if i.val < 42 then [2, 6] else [0, 7]) else (if i.val < 44 then [1, 7] else [2, 7])))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then [3, 7] else (if i.val < 47 then [0, 8] else [0, 9])) else (if i.val < 50 then (if i.val < 49 then [0, 10] else [0, 11]) else (if i.val < 51 then [1, 11] else [0, 12]))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then [4, 12] else [0, 13]) else (if i.val < 55 then [4, 13] else [0, 14])) else (if i.val < 58 then (if i.val < 57 then [2, 14] else [4, 14]) else (if i.val < 59 then [6, 14] else [0, 15])))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then [1, 15] else (if i.val < 62 then [2, 15] else [3, 15])) else (if i.val < 65 then (if i.val < 64 then [4, 15] else [5, 15]) else (if i.val < 66 then [6, 15] else [7, 15]))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then [0, 16] else [16, 16]) else (if i.val < 70 then [0, 17] else [16, 17])) else (if i.val < 73 then (if i.val < 72 then [0, 18] else [16, 18]) else (if i.val < 74 then [0, 19] else [1, 19])))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then [16, 19] else (if i.val < 77 then [17, 19] else [0, 20])) else (if i.val < 80 then (if i.val < 79 then [16, 20] else [0, 21]) else (if i.val < 81 then [16, 21] else [0, 22]))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then [2, 22] else [16, 22]) else (if i.val < 85 then [18, 22] else [0, 23])) else (if i.val < 88 then (if i.val < 87 then [1, 23] else [2, 23]) else (if i.val < 89 then [3, 23] else [16, 23]))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then [17, 23] else (if i.val < 92 then [18, 23] else [19, 23])) else (if i.val < 95 then (if i.val < 94 then [0, 24] else [8, 24]) else (if i.val < 96 then [16, 24] else [24, 24]))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then [0, 25] else [8, 25]) else (if i.val < 100 then [16, 25] else [24, 25])) else (if i.val < 103 then (if i.val < 102 then [0, 26] else [8, 26]) else (if i.val < 104 then [16, 26] else [24, 26])))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then [0, 27] else (if i.val < 107 then [1, 27] else [8, 27])) else (if i.val < 110 then (if i.val < 109 then [9, 27] else [16, 27]) else (if i.val < 111 then [17, 27] else [24, 27]))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [25, 27] else [0, 28]) else (if i.val < 115 then [4, 28] else [8, 28])) else (if i.val < 118 then (if i.val < 117 then [12, 28] else [16, 28]) else (if i.val < 119 then [20, 28] else [24, 28]))))))) else (if i.val < 180 then (if i.val < 150 then (if i.val < 135 then (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then [28, 28] else (if i.val < 122 then [0, 29] else [4, 29])) else (if i.val < 125 then (if i.val < 124 then [8, 29] else [12, 29]) else (if i.val < 126 then [16, 29] else [20, 29]))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then [24, 29] else [28, 29]) else (if i.val < 130 then [0, 30] else [2, 30])) else (if i.val < 133 then (if i.val < 132 then [4, 30] else [6, 30]) else (if i.val < 134 then [8, 30] else [10, 30])))) else (if i.val < 142 then (if i.val < 138 then (if i.val < 136 then [12, 30] else (if i.val < 137 then [14, 30] else [16, 30])) else (if i.val < 140 then (if i.val < 139 then [18, 30] else [20, 30]) else (if i.val < 141 then [22, 30] else [24, 30]))) else (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then [26, 30] else [28, 30]) else (if i.val < 145 then [30, 30] else [0, 31])) else (if i.val < 148 then (if i.val < 147 then [1, 31] else [2, 31]) else (if i.val < 149 then [3, 31] else [4, 31]))))) else (if i.val < 165 then (if i.val < 157 then (if i.val < 153 then (if i.val < 151 then [5, 31] else (if i.val < 152 then [6, 31] else [7, 31])) else (if i.val < 155 then (if i.val < 154 then [8, 31] else [9, 31]) else (if i.val < 156 then [10, 31] else [11, 31]))) else (if i.val < 161 then (if i.val < 159 then (if i.val < 158 then [12, 31] else [13, 31]) else (if i.val < 160 then [14, 31] else [15, 31])) else (if i.val < 163 then (if i.val < 162 then [16, 31] else [17, 31]) else (if i.val < 164 then [18, 31] else [19, 31])))) else (if i.val < 172 then (if i.val < 168 then (if i.val < 166 then [20, 31] else (if i.val < 167 then [21, 31] else [22, 31])) else (if i.val < 170 then (if i.val < 169 then [23, 31] else [24, 31]) else (if i.val < 171 then [25, 31] else [26, 31]))) else (if i.val < 176 then (if i.val < 174 then (if i.val < 173 then [27, 31] else [28, 31]) else (if i.val < 175 then [29, 31] else [30, 31])) else (if i.val < 178 then (if i.val < 177 then [31, 31] else [0, 0, 0]) else (if i.val < 179 then [0, 0, 1] else [0, 0, 2])))))) else (if i.val < 210 then (if i.val < 195 then (if i.val < 187 then (if i.val < 183 then (if i.val < 181 then [0, 0, 3] else (if i.val < 182 then [0, 1, 3] else [0, 0, 4])) else (if i.val < 185 then (if i.val < 184 then [0, 0, 5] else [0, 0, 6]) else (if i.val < 186 then [0, 2, 6] else [0, 0, 7]))) else (if i.val < 191 then (if i.val < 189 then (if i.val < 188 then [0, 1, 7] else [0, 2, 7]) else (if i.val < 190 then [0, 3, 7] else [1, 3, 7])) else (if i.val < 193 then (if i.val < 192 then [0, 0, 8] else [0, 0, 9]) else (if i.val < 194 then [0, 0, 10] else [0, 0, 11])))) else (if i.val < 202 then (if i.val < 198 then (if i.val < 196 then [0, 1, 11] else (if i.val < 197 then [0, 0, 12] else [0, 4, 12])) else (if i.val < 200 then (if i.val < 199 then [0, 0, 13] else [0, 4, 13]) else (if i.val < 201 then [0, 0, 14] else [0, 2, 14]))) else (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then [0, 4, 14] else [0, 6, 14]) else (if i.val < 205 then [2, 6, 14] else [0, 0, 15])) else (if i.val < 208 then (if i.val < 207 then [0, 1, 15] else [0, 2, 15]) else (if i.val < 209 then [0, 3, 15] else [1, 3, 15]))))) else (if i.val < 225 then (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then [0, 4, 15] else (if i.val < 212 then [0, 5, 15] else [0, 6, 15])) else (if i.val < 215 then (if i.val < 214 then [2, 6, 15] else [0, 7, 15]) else (if i.val < 216 then [1, 7, 15] else [2, 7, 15]))) else (if i.val < 221 then (if i.val < 219 then (if i.val < 218 then [3, 7, 15] else [0, 0, 16]) else (if i.val < 220 then [0, 16, 16] else [16, 16, 16])) else (if i.val < 223 then (if i.val < 222 then [0, 0, 17] else [0, 16, 17]) else (if i.val < 224 then [16, 16, 17] else [0, 0, 18])))) else (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then [0, 16, 18] else (if i.val < 227 then [16, 16, 18] else [0, 0, 19])) else (if i.val < 230 then (if i.val < 229 then [0, 1, 19] else [0, 16, 19]) else (if i.val < 231 then [16, 16, 19] else [0, 17, 19]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [16, 17, 19] else [0, 0, 20]) else (if i.val < 235 then [0, 16, 20] else [0, 0, 21])) else (if i.val < 238 then (if i.val < 237 then [0, 16, 21] else [0, 0, 22]) else (if i.val < 239 then [0, 2, 22] else [0, 16, 22])))))))) else (if i.val < 360 then (if i.val < 300 then (if i.val < 270 then (if i.val < 255 then (if i.val < 247 then (if i.val < 243 then (if i.val < 241 then [0, 18, 22] else (if i.val < 242 then [0, 0, 23] else [0, 1, 23])) else (if i.val < 245 then (if i.val < 244 then [0, 2, 23] else [0, 3, 23]) else (if i.val < 246 then [1, 3, 23] else [0, 16, 23]))) else (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then [0, 17, 23] else [0, 18, 23]) else (if i.val < 250 then [0, 19, 23] else [1, 19, 23])) else (if i.val < 253 then (if i.val < 252 then [0, 0, 24] else [0, 8, 24]) else (if i.val < 254 then [0, 16, 24] else [16, 16, 24])))) else (if i.val < 262 then (if i.val < 258 then (if i.val < 256 then [0, 24, 24] else (if i.val < 257 then [8, 24, 24] else [16, 24, 24])) else (if i.val < 260 then (if i.val < 259 then [24, 24, 24] else [0, 0, 25]) else (if i.val < 261 then [0, 8, 25] else [0, 16, 25]))) else (if i.val < 266 then (if i.val < 264 then (if i.val < 263 then [16, 16, 25] else [0, 24, 25]) else (if i.val < 265 then [8, 24, 25] else [16, 24, 25])) else (if i.val < 268 then (if i.val < 267 then [24, 24, 25] else [0, 0, 26]) else (if i.val < 269 then [0, 8, 26] else [0, 16, 26]))))) else (if i.val < 285 then (if i.val < 277 then (if i.val < 273 then (if i.val < 271 then [16, 16, 26] else (if i.val < 272 then [0, 24, 26] else [16, 24, 26])) else (if i.val < 275 then (if i.val < 274 then [0, 0, 27] else [0, 1, 27]) else (if i.val < 276 then [0, 8, 27] else [0, 9, 27]))) else (if i.val < 281 then (if i.val < 279 then (if i.val < 278 then [0, 16, 27] else [16, 16, 27]) else (if i.val < 280 then [0, 17, 27] else [16, 17, 27])) else (if i.val < 283 then (if i.val < 282 then [0, 24, 27] else [16, 24, 27]) else (if i.val < 284 then [0, 25, 27] else [16, 25, 27])))) else (if i.val < 292 then (if i.val < 288 then (if i.val < 286 then [0, 0, 28] else (if i.val < 287 then [0, 4, 28] else [0, 8, 28])) else (if i.val < 290 then (if i.val < 289 then [0, 12, 28] else [4, 12, 28]) else (if i.val < 291 then [0, 16, 28] else [0, 20, 28]))) else (if i.val < 296 then (if i.val < 294 then (if i.val < 293 then [0, 24, 28] else [8, 24, 28]) else (if i.val < 295 then [16, 24, 28] else [24, 24, 28])) else (if i.val < 298 then (if i.val < 297 then [0, 28, 28] else [4, 28, 28]) else (if i.val < 299 then [8, 28, 28] else [12, 28, 28])))))) else (if i.val < 330 then (if i.val < 315 then (if i.val < 307 then (if i.val < 303 then (if i.val < 301 then [16, 28, 28] else (if i.val < 302 then [20, 28, 28] else [24, 28, 28])) else (if i.val < 305 then (if i.val < 304 then [28, 28, 28] else [0, 0, 29]) else (if i.val < 306 then [0, 4, 29] else [0, 8, 29]))) else (if i.val < 311 then (if i.val < 309 then (if i.val < 308 then [0, 12, 29] else [0, 16, 29]) else (if i.val < 310 then [0, 20, 29] else [0, 24, 29])) else (if i.val < 313 then (if i.val < 312 then [8, 24, 29] else [16, 24, 29]) else (if i.val < 314 then [24, 24, 29] else [0, 28, 29])))) else (if i.val < 322 then (if i.val < 318 then (if i.val < 316 then [8, 28, 29] else (if i.val < 317 then [16, 28, 29] else [24, 28, 29])) else (if i.val < 320 then (if i.val < 319 then [0, 0, 30] else [0, 2, 30]) else (if i.val < 321 then [0, 4, 30] else [0, 6, 30]))) else (if i.val < 326 then (if i.val < 324 then (if i.val < 323 then [2, 6, 30] else [0, 8, 30]) else (if i.val < 325 then [0, 10, 30] else [0, 12, 30])) else (if i.val < 328 then (if i.val < 327 then [4, 12, 30] else [0, 14, 30]) else (if i.val < 329 then [2, 14, 30] else [4, 14, 30]))))) else (if i.val < 345 then (if i.val < 337 then (if i.val < 333 then (if i.val < 331 then [6, 14, 30] else (if i.val < 332 then [0, 16, 30] else [0, 18, 30])) else (if i.val < 335 then (if i.val < 334 then [0, 20, 30] else [0, 22, 30]) else (if i.val < 336 then [2, 22, 30] else [0, 24, 30]))) else (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then [16, 24, 30] else [0, 26, 30]) else (if i.val < 340 then [16, 26, 30] else [0, 28, 30])) else (if i.val < 343 then (if i.val < 342 then [4, 28, 30] else [8, 28, 30]) else (if i.val < 344 then [12, 28, 30] else [16, 28, 30])))) else (if i.val < 352 then (if i.val < 348 then (if i.val < 346 then [20, 28, 30] else (if i.val < 347 then [24, 28, 30] else [28, 28, 30])) else (if i.val < 350 then (if i.val < 349 then [0, 30, 30] else [2, 30, 30]) else (if i.val < 351 then [4, 30, 30] else [6, 30, 30]))) else (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then [8, 30, 30] else [10, 30, 30]) else (if i.val < 355 then [12, 30, 30] else [14, 30, 30])) else (if i.val < 358 then (if i.val < 357 then [16, 30, 30] else [18, 30, 30]) else (if i.val < 359 then [20, 30, 30] else [22, 30, 30]))))))) else (if i.val < 420 then (if i.val < 390 then (if i.val < 375 then (if i.val < 367 then (if i.val < 363 then (if i.val < 361 then [24, 30, 30] else (if i.val < 362 then [26, 30, 30] else [28, 30, 30])) else (if i.val < 365 then (if i.val < 364 then [30, 30, 30] else [0, 0, 31]) else (if i.val < 366 then [0, 1, 31] else [0, 2, 31]))) else (if i.val < 371 then (if i.val < 369 then (if i.val < 368 then [0, 3, 31] else [1, 3, 31]) else (if i.val < 370 then [0, 4, 31] else [0, 5, 31])) else (if i.val < 373 then (if i.val < 372 then [0, 6, 31] else [2, 6, 31]) else (if i.val < 374 then [0, 7, 31] else [1, 7, 31])))) else (if i.val < 382 then (if i.val < 378 then (if i.val < 376 then [2, 7, 31] else (if i.val < 377 then [3, 7, 31] else [0, 8, 31])) else (if i.val < 380 then (if i.val < 379 then [0, 9, 31] else [0, 10, 31]) else (if i.val < 381 then [0, 11, 31] else [1, 11, 31]))) else (if i.val < 386 then (if i.val < 384 then (if i.val < 383 then [0, 12, 31] else [0, 13, 31]) else (if i.val < 385 then [0, 14, 31] else [2, 14, 31])) else (if i.val < 388 then (if i.val < 387 then [4, 14, 31] else [6, 14, 31]) else (if i.val < 389 then [0, 15, 31] else [1, 15, 31]))))) else (if i.val < 405 then (if i.val < 397 then (if i.val < 393 then (if i.val < 391 then [2, 15, 31] else (if i.val < 392 then [3, 15, 31] else [4, 15, 31])) else (if i.val < 395 then (if i.val < 394 then [5, 15, 31] else [6, 15, 31]) else (if i.val < 396 then [7, 15, 31] else [0, 16, 31]))) else (if i.val < 401 then (if i.val < 399 then (if i.val < 398 then [0, 17, 31] else [0, 18, 31]) else (if i.val < 400 then [0, 19, 31] else [1, 19, 31])) else (if i.val < 403 then (if i.val < 402 then [0, 20, 31] else [0, 21, 31]) else (if i.val < 404 then [0, 22, 31] else [2, 22, 31])))) else (if i.val < 412 then (if i.val < 408 then (if i.val < 406 then [0, 23, 31] else (if i.val < 407 then [1, 23, 31] else [2, 23, 31])) else (if i.val < 410 then (if i.val < 409 then [3, 23, 31] else [0, 24, 31]) else (if i.val < 411 then [16, 24, 31] else [0, 25, 31]))) else (if i.val < 416 then (if i.val < 414 then (if i.val < 413 then [16, 25, 31] else [0, 26, 31]) else (if i.val < 415 then [16, 26, 31] else [0, 27, 31])) else (if i.val < 418 then (if i.val < 417 then [1, 27, 31] else [16, 27, 31]) else (if i.val < 419 then [17, 27, 31] else [0, 28, 31])))))) else (if i.val < 450 then (if i.val < 435 then (if i.val < 427 then (if i.val < 423 then (if i.val < 421 then [8, 28, 31] else (if i.val < 422 then [16, 28, 31] else [24, 28, 31])) else (if i.val < 425 then (if i.val < 424 then [0, 29, 31] else [8, 29, 31]) else (if i.val < 426 then [16, 29, 31] else [24, 29, 31]))) else (if i.val < 431 then (if i.val < 429 then (if i.val < 428 then [0, 30, 31] else [2, 30, 31]) else (if i.val < 430 then [4, 30, 31] else [6, 30, 31])) else (if i.val < 433 then (if i.val < 432 then [8, 30, 31] else [10, 30, 31]) else (if i.val < 434 then [12, 30, 31] else [14, 30, 31])))) else (if i.val < 442 then (if i.val < 438 then (if i.val < 436 then [16, 30, 31] else (if i.val < 437 then [18, 30, 31] else [20, 30, 31])) else (if i.val < 440 then (if i.val < 439 then [22, 30, 31] else [24, 30, 31]) else (if i.val < 441 then [26, 30, 31] else [28, 30, 31]))) else (if i.val < 446 then (if i.val < 444 then (if i.val < 443 then [30, 30, 31] else [0, 31, 31]) else (if i.val < 445 then [1, 31, 31] else [2, 31, 31])) else (if i.val < 448 then (if i.val < 447 then [3, 31, 31] else [4, 31, 31]) else (if i.val < 449 then [5, 31, 31] else [6, 31, 31]))))) else (if i.val < 465 then (if i.val < 457 then (if i.val < 453 then (if i.val < 451 then [7, 31, 31] else (if i.val < 452 then [8, 31, 31] else [9, 31, 31])) else (if i.val < 455 then (if i.val < 454 then [10, 31, 31] else [11, 31, 31]) else (if i.val < 456 then [12, 31, 31] else [13, 31, 31]))) else (if i.val < 461 then (if i.val < 459 then (if i.val < 458 then [14, 31, 31] else [15, 31, 31]) else (if i.val < 460 then [16, 31, 31] else [17, 31, 31])) else (if i.val < 463 then (if i.val < 462 then [18, 31, 31] else [19, 31, 31]) else (if i.val < 464 then [20, 31, 31] else [21, 31, 31])))) else (if i.val < 473 then (if i.val < 469 then (if i.val < 467 then (if i.val < 466 then [22, 31, 31] else [23, 31, 31]) else (if i.val < 468 then [24, 31, 31] else [25, 31, 31])) else (if i.val < 471 then (if i.val < 470 then [26, 31, 31] else [27, 31, 31]) else (if i.val < 472 then [28, 31, 31] else [29, 31, 31]))) else (if i.val < 477 then (if i.val < 475 then (if i.val < 474 then [30, 31, 31] else [31, 31, 31]) else (if i.val < 476 then [0, 0, 0, 0] else [0, 0, 0, 1])) else (if i.val < 479 then (if i.val < 478 then [0, 0, 0, 2] else [0, 0, 0, 3]) else (if i.val < 480 then [0, 0, 1, 3] else [0, 0, 0, 4]))))))))) else (if i.val < 722 then (if i.val < 601 then (if i.val < 541 then (if i.val < 511 then (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then [0, 0, 0, 5] else (if i.val < 483 then [0, 0, 0, 6] else [0, 0, 2, 6])) else (if i.val < 486 then (if i.val < 485 then [0, 0, 0, 7] else [0, 0, 1, 7]) else (if i.val < 487 then [0, 0, 2, 7] else [0, 0, 3, 7]))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then [0, 1, 3, 7] else [0, 0, 0, 8]) else (if i.val < 491 then [0, 0, 0, 9] else [0, 0, 0, 10])) else (if i.val < 494 then (if i.val < 493 then [0, 0, 0, 11] else [0, 0, 1, 11]) else (if i.val < 495 then [0, 0, 0, 12] else [0, 0, 4, 12])))) else (if i.val < 503 then (if i.val < 499 then (if i.val < 497 then [0, 0, 0, 13] else (if i.val < 498 then [0, 0, 4, 13] else [0, 0, 0, 14])) else (if i.val < 501 then (if i.val < 500 then [0, 0, 2, 14] else [0, 0, 4, 14]) else (if i.val < 502 then [0, 0, 6, 14] else [0, 2, 6, 14]))) else (if i.val < 507 then (if i.val < 505 then (if i.val < 504 then [0, 0, 0, 15] else [0, 0, 1, 15]) else (if i.val < 506 then [0, 0, 2, 15] else [0, 0, 3, 15])) else (if i.val < 509 then (if i.val < 508 then [0, 1, 3, 15] else [0, 0, 4, 15]) else (if i.val < 510 then [0, 0, 5, 15] else [0, 0, 6, 15]))))) else (if i.val < 526 then (if i.val < 518 then (if i.val < 514 then (if i.val < 512 then [0, 2, 6, 15] else (if i.val < 513 then [0, 0, 7, 15] else [0, 1, 7, 15])) else (if i.val < 516 then (if i.val < 515 then [0, 2, 7, 15] else [0, 3, 7, 15]) else (if i.val < 517 then [1, 3, 7, 15] else [0, 0, 0, 16]))) else (if i.val < 522 then (if i.val < 520 then (if i.val < 519 then [0, 0, 16, 16] else [0, 16, 16, 16]) else (if i.val < 521 then [16, 16, 16, 16] else [0, 0, 0, 17])) else (if i.val < 524 then (if i.val < 523 then [0, 0, 16, 17] else [0, 16, 16, 17]) else (if i.val < 525 then [16, 16, 16, 17] else [0, 0, 0, 18])))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then [0, 0, 16, 18] else (if i.val < 528 then [0, 16, 16, 18] else [0, 0, 0, 19])) else (if i.val < 531 then (if i.val < 530 then [0, 0, 1, 19] else [0, 0, 16, 19]) else (if i.val < 532 then [0, 16, 16, 19] else [0, 0, 17, 19]))) else (if i.val < 537 then (if i.val < 535 then (if i.val < 534 then [0, 16, 17, 19] else [0, 0, 0, 20]) else (if i.val < 536 then [0, 0, 16, 20] else [0, 0, 0, 21])) else (if i.val < 539 then (if i.val < 538 then [0, 0, 16, 21] else [0, 0, 0, 22]) else (if i.val < 540 then [0, 0, 2, 22] else [0, 0, 16, 22])))))) else (if i.val < 571 then (if i.val < 556 then (if i.val < 548 then (if i.val < 544 then (if i.val < 542 then [0, 0, 18, 22] else (if i.val < 543 then [0, 0, 0, 23] else [0, 0, 1, 23])) else (if i.val < 546 then (if i.val < 545 then [0, 0, 2, 23] else [0, 0, 3, 23]) else (if i.val < 547 then [0, 1, 3, 23] else [0, 0, 16, 23]))) else (if i.val < 552 then (if i.val < 550 then (if i.val < 549 then [0, 0, 17, 23] else [0, 0, 18, 23]) else (if i.val < 551 then [0, 0, 19, 23] else [0, 1, 19, 23])) else (if i.val < 554 then (if i.val < 553 then [0, 0, 0, 24] else [0, 0, 8, 24]) else (if i.val < 555 then [0, 0, 16, 24] else [0, 16, 16, 24])))) else (if i.val < 563 then (if i.val < 559 then (if i.val < 557 then [16, 16, 16, 24] else (if i.val < 558 then [0, 0, 24, 24] else [0, 8, 24, 24])) else (if i.val < 561 then (if i.val < 560 then [0, 16, 24, 24] else [16, 16, 24, 24]) else (if i.val < 562 then [0, 24, 24, 24] else [8, 24, 24, 24]))) else (if i.val < 567 then (if i.val < 565 then (if i.val < 564 then [16, 24, 24, 24] else [24, 24, 24, 24]) else (if i.val < 566 then [0, 0, 0, 25] else [0, 0, 8, 25])) else (if i.val < 569 then (if i.val < 568 then [0, 0, 16, 25] else [0, 16, 16, 25]) else (if i.val < 570 then [16, 16, 16, 25] else [0, 0, 24, 25]))))) else (if i.val < 586 then (if i.val < 578 then (if i.val < 574 then (if i.val < 572 then [0, 8, 24, 25] else (if i.val < 573 then [0, 16, 24, 25] else [16, 16, 24, 25])) else (if i.val < 576 then (if i.val < 575 then [0, 24, 24, 25] else [16, 24, 24, 25]) else (if i.val < 577 then [0, 0, 0, 26] else [0, 0, 8, 26]))) else (if i.val < 582 then (if i.val < 580 then (if i.val < 579 then [0, 0, 16, 26] else [0, 16, 16, 26]) else (if i.val < 581 then [0, 0, 24, 26] else [0, 16, 24, 26])) else (if i.val < 584 then (if i.val < 583 then [0, 0, 0, 27] else [0, 0, 1, 27]) else (if i.val < 585 then [0, 0, 8, 27] else [0, 0, 9, 27])))) else (if i.val < 593 then (if i.val < 589 then (if i.val < 587 then [0, 0, 16, 27] else (if i.val < 588 then [0, 16, 16, 27] else [0, 0, 17, 27])) else (if i.val < 591 then (if i.val < 590 then [0, 16, 17, 27] else [0, 0, 24, 27]) else (if i.val < 592 then [0, 16, 24, 27] else [0, 0, 25, 27]))) else (if i.val < 597 then (if i.val < 595 then (if i.val < 594 then [0, 16, 25, 27] else [0, 0, 0, 28]) else (if i.val < 596 then [0, 0, 4, 28] else [0, 0, 8, 28])) else (if i.val < 599 then (if i.val < 598 then [0, 0, 12, 28] else [0, 4, 12, 28]) else (if i.val < 600 then [0, 0, 16, 28] else [0, 0, 20, 28]))))))) else (if i.val < 661 then (if i.val < 631 then (if i.val < 616 then (if i.val < 608 then (if i.val < 604 then (if i.val < 602 then [0, 0, 24, 28] else (if i.val < 603 then [0, 8, 24, 28] else [0, 16, 24, 28])) else (if i.val < 606 then (if i.val < 605 then [16, 16, 24, 28] else [0, 24, 24, 28]) else (if i.val < 607 then [8, 24, 24, 28] else [16, 24, 24, 28]))) else (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then [24, 24, 24, 28] else [0, 0, 28, 28]) else (if i.val < 611 then [0, 4, 28, 28] else [0, 8, 28, 28])) else (if i.val < 614 then (if i.val < 613 then [0, 12, 28, 28] else [4, 12, 28, 28]) else (if i.val < 615 then [0, 16, 28, 28] else [0, 20, 28, 28])))) else (if i.val < 623 then (if i.val < 619 then (if i.val < 617 then [0, 24, 28, 28] else (if i.val < 618 then [8, 24, 28, 28] else [16, 24, 28, 28])) else (if i.val < 621 then (if i.val < 620 then [24, 24, 28, 28] else [0, 28, 28, 28]) else (if i.val < 622 then [4, 28, 28, 28] else [8, 28, 28, 28]))) else (if i.val < 627 then (if i.val < 625 then (if i.val < 624 then [12, 28, 28, 28] else [16, 28, 28, 28]) else (if i.val < 626 then [20, 28, 28, 28] else [24, 28, 28, 28])) else (if i.val < 629 then (if i.val < 628 then [28, 28, 28, 28] else [0, 0, 0, 29]) else (if i.val < 630 then [0, 0, 4, 29] else [0, 0, 8, 29]))))) else (if i.val < 646 then (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then [0, 0, 12, 29] else (if i.val < 633 then [0, 0, 16, 29] else [0, 0, 20, 29])) else (if i.val < 636 then (if i.val < 635 then [0, 0, 24, 29] else [0, 8, 24, 29]) else (if i.val < 637 then [0, 16, 24, 29] else [16, 16, 24, 29]))) else (if i.val < 642 then (if i.val < 640 then (if i.val < 639 then [0, 24, 24, 29] else [16, 24, 24, 29]) else (if i.val < 641 then [0, 0, 28, 29] else [0, 8, 28, 29])) else (if i.val < 644 then (if i.val < 643 then [0, 16, 28, 29] else [0, 24, 28, 29]) else (if i.val < 645 then [16, 24, 28, 29] else [0, 0, 0, 30])))) else (if i.val < 653 then (if i.val < 649 then (if i.val < 647 then [0, 0, 2, 30] else (if i.val < 648 then [0, 0, 4, 30] else [0, 0, 6, 30])) else (if i.val < 651 then (if i.val < 650 then [0, 2, 6, 30] else [0, 0, 8, 30]) else (if i.val < 652 then [0, 0, 10, 30] else [0, 0, 12, 30]))) else (if i.val < 657 then (if i.val < 655 then (if i.val < 654 then [0, 4, 12, 30] else [0, 0, 14, 30]) else (if i.val < 656 then [0, 2, 14, 30] else [0, 4, 14, 30])) else (if i.val < 659 then (if i.val < 658 then [0, 6, 14, 30] else [2, 6, 14, 30]) else (if i.val < 660 then [0, 0, 16, 30] else [0, 0, 18, 30])))))) else (if i.val < 691 then (if i.val < 676 then (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then [0, 0, 20, 30] else (if i.val < 663 then [0, 0, 22, 30] else [0, 2, 22, 30])) else (if i.val < 666 then (if i.val < 665 then [0, 0, 24, 30] else [0, 16, 24, 30]) else (if i.val < 667 then [0, 0, 26, 30] else [0, 16, 26, 30]))) else (if i.val < 672 then (if i.val < 670 then (if i.val < 669 then [0, 0, 28, 30] else [0, 4, 28, 30]) else (if i.val < 671 then [0, 8, 28, 30] else [0, 12, 28, 30])) else (if i.val < 674 then (if i.val < 673 then [4, 12, 28, 30] else [0, 16, 28, 30]) else (if i.val < 675 then [0, 20, 28, 30] else [0, 24, 28, 30])))) else (if i.val < 683 then (if i.val < 679 then (if i.val < 677 then [8, 24, 28, 30] else (if i.val < 678 then [16, 24, 28, 30] else [24, 24, 28, 30])) else (if i.val < 681 then (if i.val < 680 then [0, 28, 28, 30] else [4, 28, 28, 30]) else (if i.val < 682 then [8, 28, 28, 30] else [12, 28, 28, 30]))) else (if i.val < 687 then (if i.val < 685 then (if i.val < 684 then [16, 28, 28, 30] else [20, 28, 28, 30]) else (if i.val < 686 then [24, 28, 28, 30] else [28, 28, 28, 30])) else (if i.val < 689 then (if i.val < 688 then [0, 0, 30, 30] else [0, 2, 30, 30]) else (if i.val < 690 then [0, 4, 30, 30] else [0, 6, 30, 30]))))) else (if i.val < 706 then (if i.val < 698 then (if i.val < 694 then (if i.val < 692 then [2, 6, 30, 30] else (if i.val < 693 then [0, 8, 30, 30] else [0, 10, 30, 30])) else (if i.val < 696 then (if i.val < 695 then [0, 12, 30, 30] else [4, 12, 30, 30]) else (if i.val < 697 then [0, 14, 30, 30] else [2, 14, 30, 30]))) else (if i.val < 702 then (if i.val < 700 then (if i.val < 699 then [4, 14, 30, 30] else [6, 14, 30, 30]) else (if i.val < 701 then [0, 16, 30, 30] else [0, 18, 30, 30])) else (if i.val < 704 then (if i.val < 703 then [0, 20, 30, 30] else [0, 22, 30, 30]) else (if i.val < 705 then [2, 22, 30, 30] else [0, 24, 30, 30])))) else (if i.val < 714 then (if i.val < 710 then (if i.val < 708 then (if i.val < 707 then [16, 24, 30, 30] else [0, 26, 30, 30]) else (if i.val < 709 then [16, 26, 30, 30] else [0, 28, 30, 30])) else (if i.val < 712 then (if i.val < 711 then [4, 28, 30, 30] else [8, 28, 30, 30]) else (if i.val < 713 then [12, 28, 30, 30] else [16, 28, 30, 30]))) else (if i.val < 718 then (if i.val < 716 then (if i.val < 715 then [20, 28, 30, 30] else [24, 28, 30, 30]) else (if i.val < 717 then [28, 28, 30, 30] else [0, 30, 30, 30])) else (if i.val < 720 then (if i.val < 719 then [2, 30, 30, 30] else [4, 30, 30, 30]) else (if i.val < 721 then [6, 30, 30, 30] else [8, 30, 30, 30])))))))) else (if i.val < 842 then (if i.val < 782 then (if i.val < 752 then (if i.val < 737 then (if i.val < 729 then (if i.val < 725 then (if i.val < 723 then [10, 30, 30, 30] else (if i.val < 724 then [12, 30, 30, 30] else [14, 30, 30, 30])) else (if i.val < 727 then (if i.val < 726 then [16, 30, 30, 30] else [18, 30, 30, 30]) else (if i.val < 728 then [20, 30, 30, 30] else [22, 30, 30, 30]))) else (if i.val < 733 then (if i.val < 731 then (if i.val < 730 then [24, 30, 30, 30] else [26, 30, 30, 30]) else (if i.val < 732 then [28, 30, 30, 30] else [30, 30, 30, 30])) else (if i.val < 735 then (if i.val < 734 then [0, 0, 0, 31] else [0, 0, 1, 31]) else (if i.val < 736 then [0, 0, 2, 31] else [0, 0, 3, 31])))) else (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then [0, 1, 3, 31] else (if i.val < 739 then [0, 0, 4, 31] else [0, 0, 5, 31])) else (if i.val < 742 then (if i.val < 741 then [0, 0, 6, 31] else [0, 2, 6, 31]) else (if i.val < 743 then [0, 0, 7, 31] else [0, 1, 7, 31]))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then [0, 2, 7, 31] else [0, 3, 7, 31]) else (if i.val < 747 then [1, 3, 7, 31] else [0, 0, 8, 31])) else (if i.val < 750 then (if i.val < 749 then [0, 0, 9, 31] else [0, 0, 10, 31]) else (if i.val < 751 then [0, 0, 11, 31] else [0, 1, 11, 31]))))) else (if i.val < 767 then (if i.val < 759 then (if i.val < 755 then (if i.val < 753 then [0, 0, 12, 31] else (if i.val < 754 then [0, 0, 13, 31] else [0, 0, 14, 31])) else (if i.val < 757 then (if i.val < 756 then [0, 2, 14, 31] else [0, 4, 14, 31]) else (if i.val < 758 then [0, 6, 14, 31] else [2, 6, 14, 31]))) else (if i.val < 763 then (if i.val < 761 then (if i.val < 760 then [0, 0, 15, 31] else [0, 1, 15, 31]) else (if i.val < 762 then [0, 2, 15, 31] else [0, 3, 15, 31])) else (if i.val < 765 then (if i.val < 764 then [1, 3, 15, 31] else [0, 4, 15, 31]) else (if i.val < 766 then [0, 5, 15, 31] else [0, 6, 15, 31])))) else (if i.val < 774 then (if i.val < 770 then (if i.val < 768 then [2, 6, 15, 31] else (if i.val < 769 then [0, 7, 15, 31] else [1, 7, 15, 31])) else (if i.val < 772 then (if i.val < 771 then [2, 7, 15, 31] else [3, 7, 15, 31]) else (if i.val < 773 then [0, 0, 16, 31] else [0, 0, 17, 31]))) else (if i.val < 778 then (if i.val < 776 then (if i.val < 775 then [0, 0, 18, 31] else [0, 0, 19, 31]) else (if i.val < 777 then [0, 1, 19, 31] else [0, 0, 20, 31])) else (if i.val < 780 then (if i.val < 779 then [0, 0, 21, 31] else [0, 0, 22, 31]) else (if i.val < 781 then [0, 2, 22, 31] else [0, 0, 23, 31])))))) else (if i.val < 812 then (if i.val < 797 then (if i.val < 789 then (if i.val < 785 then (if i.val < 783 then [0, 1, 23, 31] else (if i.val < 784 then [0, 2, 23, 31] else [0, 3, 23, 31])) else (if i.val < 787 then (if i.val < 786 then [1, 3, 23, 31] else [0, 0, 24, 31]) else (if i.val < 788 then [0, 16, 24, 31] else [0, 0, 25, 31]))) else (if i.val < 793 then (if i.val < 791 then (if i.val < 790 then [0, 16, 25, 31] else [0, 0, 26, 31]) else (if i.val < 792 then [0, 16, 26, 31] else [0, 0, 27, 31])) else (if i.val < 795 then (if i.val < 794 then [0, 1, 27, 31] else [0, 16, 27, 31]) else (if i.val < 796 then [0, 17, 27, 31] else [0, 0, 28, 31])))) else (if i.val < 804 then (if i.val < 800 then (if i.val < 798 then [0, 8, 28, 31] else (if i.val < 799 then [0, 16, 28, 31] else [0, 24, 28, 31])) else (if i.val < 802 then (if i.val < 801 then [16, 24, 28, 31] else [0, 0, 29, 31]) else (if i.val < 803 then [0, 8, 29, 31] else [0, 16, 29, 31]))) else (if i.val < 808 then (if i.val < 806 then (if i.val < 805 then [0, 24, 29, 31] else [16, 24, 29, 31]) else (if i.val < 807 then [0, 0, 30, 31] else [0, 2, 30, 31])) else (if i.val < 810 then (if i.val < 809 then [0, 4, 30, 31] else [0, 6, 30, 31]) else (if i.val < 811 then [2, 6, 30, 31] else [0, 8, 30, 31]))))) else (if i.val < 827 then (if i.val < 819 then (if i.val < 815 then (if i.val < 813 then [0, 10, 30, 31] else (if i.val < 814 then [0, 12, 30, 31] else [4, 12, 30, 31])) else (if i.val < 817 then (if i.val < 816 then [0, 14, 30, 31] else [2, 14, 30, 31]) else (if i.val < 818 then [4, 14, 30, 31] else [6, 14, 30, 31]))) else (if i.val < 823 then (if i.val < 821 then (if i.val < 820 then [0, 16, 30, 31] else [0, 18, 30, 31]) else (if i.val < 822 then [0, 20, 30, 31] else [0, 22, 30, 31])) else (if i.val < 825 then (if i.val < 824 then [2, 22, 30, 31] else [0, 24, 30, 31]) else (if i.val < 826 then [16, 24, 30, 31] else [0, 26, 30, 31])))) else (if i.val < 834 then (if i.val < 830 then (if i.val < 828 then [16, 26, 30, 31] else (if i.val < 829 then [0, 28, 30, 31] else [4, 28, 30, 31])) else (if i.val < 832 then (if i.val < 831 then [8, 28, 30, 31] else [12, 28, 30, 31]) else (if i.val < 833 then [16, 28, 30, 31] else [20, 28, 30, 31]))) else (if i.val < 838 then (if i.val < 836 then (if i.val < 835 then [24, 28, 30, 31] else [28, 28, 30, 31]) else (if i.val < 837 then [0, 30, 30, 31] else [2, 30, 30, 31])) else (if i.val < 840 then (if i.val < 839 then [4, 30, 30, 31] else [6, 30, 30, 31]) else (if i.val < 841 then [8, 30, 30, 31] else [10, 30, 30, 31]))))))) else (if i.val < 902 then (if i.val < 872 then (if i.val < 857 then (if i.val < 849 then (if i.val < 845 then (if i.val < 843 then [12, 30, 30, 31] else (if i.val < 844 then [14, 30, 30, 31] else [16, 30, 30, 31])) else (if i.val < 847 then (if i.val < 846 then [18, 30, 30, 31] else [20, 30, 30, 31]) else (if i.val < 848 then [22, 30, 30, 31] else [24, 30, 30, 31]))) else (if i.val < 853 then (if i.val < 851 then (if i.val < 850 then [26, 30, 30, 31] else [28, 30, 30, 31]) else (if i.val < 852 then [30, 30, 30, 31] else [0, 0, 31, 31])) else (if i.val < 855 then (if i.val < 854 then [0, 1, 31, 31] else [0, 2, 31, 31]) else (if i.val < 856 then [0, 3, 31, 31] else [1, 3, 31, 31])))) else (if i.val < 864 then (if i.val < 860 then (if i.val < 858 then [0, 4, 31, 31] else (if i.val < 859 then [0, 5, 31, 31] else [0, 6, 31, 31])) else (if i.val < 862 then (if i.val < 861 then [2, 6, 31, 31] else [0, 7, 31, 31]) else (if i.val < 863 then [1, 7, 31, 31] else [2, 7, 31, 31]))) else (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then [3, 7, 31, 31] else [0, 8, 31, 31]) else (if i.val < 867 then [0, 9, 31, 31] else [0, 10, 31, 31])) else (if i.val < 870 then (if i.val < 869 then [0, 11, 31, 31] else [1, 11, 31, 31]) else (if i.val < 871 then [0, 12, 31, 31] else [0, 13, 31, 31]))))) else (if i.val < 887 then (if i.val < 879 then (if i.val < 875 then (if i.val < 873 then [0, 14, 31, 31] else (if i.val < 874 then [2, 14, 31, 31] else [4, 14, 31, 31])) else (if i.val < 877 then (if i.val < 876 then [6, 14, 31, 31] else [0, 15, 31, 31]) else (if i.val < 878 then [1, 15, 31, 31] else [2, 15, 31, 31]))) else (if i.val < 883 then (if i.val < 881 then (if i.val < 880 then [3, 15, 31, 31] else [4, 15, 31, 31]) else (if i.val < 882 then [5, 15, 31, 31] else [6, 15, 31, 31])) else (if i.val < 885 then (if i.val < 884 then [7, 15, 31, 31] else [0, 16, 31, 31]) else (if i.val < 886 then [0, 17, 31, 31] else [0, 18, 31, 31])))) else (if i.val < 894 then (if i.val < 890 then (if i.val < 888 then [0, 19, 31, 31] else (if i.val < 889 then [1, 19, 31, 31] else [0, 20, 31, 31])) else (if i.val < 892 then (if i.val < 891 then [0, 21, 31, 31] else [0, 22, 31, 31]) else (if i.val < 893 then [2, 22, 31, 31] else [0, 23, 31, 31]))) else (if i.val < 898 then (if i.val < 896 then (if i.val < 895 then [1, 23, 31, 31] else [2, 23, 31, 31]) else (if i.val < 897 then [3, 23, 31, 31] else [0, 24, 31, 31])) else (if i.val < 900 then (if i.val < 899 then [16, 24, 31, 31] else [0, 25, 31, 31]) else (if i.val < 901 then [16, 25, 31, 31] else [0, 26, 31, 31])))))) else (if i.val < 932 then (if i.val < 917 then (if i.val < 909 then (if i.val < 905 then (if i.val < 903 then [16, 26, 31, 31] else (if i.val < 904 then [0, 27, 31, 31] else [1, 27, 31, 31])) else (if i.val < 907 then (if i.val < 906 then [16, 27, 31, 31] else [17, 27, 31, 31]) else (if i.val < 908 then [0, 28, 31, 31] else [8, 28, 31, 31]))) else (if i.val < 913 then (if i.val < 911 then (if i.val < 910 then [16, 28, 31, 31] else [24, 28, 31, 31]) else (if i.val < 912 then [0, 29, 31, 31] else [8, 29, 31, 31])) else (if i.val < 915 then (if i.val < 914 then [16, 29, 31, 31] else [24, 29, 31, 31]) else (if i.val < 916 then [0, 30, 31, 31] else [2, 30, 31, 31])))) else (if i.val < 924 then (if i.val < 920 then (if i.val < 918 then [4, 30, 31, 31] else (if i.val < 919 then [6, 30, 31, 31] else [8, 30, 31, 31])) else (if i.val < 922 then (if i.val < 921 then [10, 30, 31, 31] else [12, 30, 31, 31]) else (if i.val < 923 then [14, 30, 31, 31] else [16, 30, 31, 31]))) else (if i.val < 928 then (if i.val < 926 then (if i.val < 925 then [18, 30, 31, 31] else [20, 30, 31, 31]) else (if i.val < 927 then [22, 30, 31, 31] else [24, 30, 31, 31])) else (if i.val < 930 then (if i.val < 929 then [26, 30, 31, 31] else [28, 30, 31, 31]) else (if i.val < 931 then [30, 30, 31, 31] else [0, 31, 31, 31]))))) else (if i.val < 947 then (if i.val < 939 then (if i.val < 935 then (if i.val < 933 then [1, 31, 31, 31] else (if i.val < 934 then [2, 31, 31, 31] else [3, 31, 31, 31])) else (if i.val < 937 then (if i.val < 936 then [4, 31, 31, 31] else [5, 31, 31, 31]) else (if i.val < 938 then [6, 31, 31, 31] else [7, 31, 31, 31]))) else (if i.val < 943 then (if i.val < 941 then (if i.val < 940 then [8, 31, 31, 31] else [9, 31, 31, 31]) else (if i.val < 942 then [10, 31, 31, 31] else [11, 31, 31, 31])) else (if i.val < 945 then (if i.val < 944 then [12, 31, 31, 31] else [13, 31, 31, 31]) else (if i.val < 946 then [14, 31, 31, 31] else [15, 31, 31, 31])))) else (if i.val < 955 then (if i.val < 951 then (if i.val < 949 then (if i.val < 948 then [16, 31, 31, 31] else [17, 31, 31, 31]) else (if i.val < 950 then [18, 31, 31, 31] else [19, 31, 31, 31])) else (if i.val < 953 then (if i.val < 952 then [20, 31, 31, 31] else [21, 31, 31, 31]) else (if i.val < 954 then [22, 31, 31, 31] else [23, 31, 31, 31]))) else (if i.val < 959 then (if i.val < 957 then (if i.val < 956 then [24, 31, 31, 31] else [25, 31, 31, 31]) else (if i.val < 958 then [26, 31, 31, 31] else [27, 31, 31, 31])) else (if i.val < 961 then (if i.val < 960 then [28, 31, 31, 31] else [29, 31, 31, 31]) else (if i.val < 962 then [30, 31, 31, 31] else [31, 31, 31, 31]))))))))))
def state (i : Fin 963) : State :=
  ⟨(codes i).map (fun c => decode ⟨c % 32, Nat.mod_lt _ (by decide)⟩)⟩
def succ (i : Fin 963) : List (Fin 963) :=
  (if i.val < 481 then (if i.val < 240 then (if i.val < 120 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] else (if i.val < 2 then [33] else [34])) else (if i.val < 5 then (if i.val < 4 then [35] else [36, 37]) else (if i.val < 6 then [38] else [39]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then [40, 41] else [42, 43, 44, 45]) else (if i.val < 10 then [46] else [47])) else (if i.val < 13 then (if i.val < 12 then [48] else [49, 50]) else (if i.val < 14 then [51, 52] else [53, 54])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then [55, 56, 57, 58] else (if i.val < 17 then [59, 60, 61, 62, 63, 64, 65, 66] else [67, 68])) else (if i.val < 20 then (if i.val < 19 then [69, 70] else [71, 72]) else (if i.val < 21 then [73, 74, 75, 76] else [77, 78]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then [79, 80] else [81, 82, 83, 84]) else (if i.val < 25 then [85, 86, 87, 88, 89, 90, 91, 92] else [93, 94, 95, 96])) else (if i.val < 28 then (if i.val < 27 then [97, 98, 99, 100] else [101, 102, 103, 104]) else (if i.val < 29 then [105, 106, 107, 108, 109, 110, 111, 112] else [113, 114, 115, 116, 117, 118, 119, 120]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then [121, 122, 123, 124, 125, 126, 127, 128] else (if i.val < 32 then [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144] else [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])) else (if i.val < 35 then (if i.val < 34 then [177] else [178]) else (if i.val < 36 then [179] else [180]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then [181] else [182]) else (if i.val < 40 then [183] else [184])) else (if i.val < 43 then (if i.val < 42 then [185] else [186]) else (if i.val < 44 then [187] else [188])))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then [189, 190] else (if i.val < 47 then [191] else [192])) else (if i.val < 50 then (if i.val < 49 then [193] else [194]) else (if i.val < 51 then [195] else [196]))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then [197] else [198]) else (if i.val < 55 then [199] else [200])) else (if i.val < 58 then (if i.val < 57 then [201] else [202]) else (if i.val < 59 then [203, 204] else [205])))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then [206] else (if i.val < 62 then [207] else [208, 209])) else (if i.val < 65 then (if i.val < 64 then [210] else [211]) else (if i.val < 66 then [212, 213] else [214, 215, 216, 217]))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then [218] else [219, 220]) else (if i.val < 70 then [221] else [222, 223])) else (if i.val < 73 then (if i.val < 72 then [224] else [225, 226]) else (if i.val < 74 then [227] else [228])))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then [229, 230] else (if i.val < 77 then [231, 232] else [233])) else (if i.val < 80 then (if i.val < 79 then [234] else [235]) else (if i.val < 81 then [236] else [237]))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then [238] else [239]) else (if i.val < 85 then [240] else [241])) else (if i.val < 88 then (if i.val < 87 then [242] else [243]) else (if i.val < 89 then [244, 245] else [246]))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then [247] else (if i.val < 92 then [248] else [249, 250])) else (if i.val < 95 then (if i.val < 94 then [251] else [252]) else (if i.val < 96 then [253, 254] else [255, 256, 257, 258]))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then [259] else [260]) else (if i.val < 100 then [261, 262] else [263, 264, 265, 266])) else (if i.val < 103 then (if i.val < 102 then [267] else [268]) else (if i.val < 104 then [269, 270] else [271, 272])))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then [273] else (if i.val < 107 then [274] else [275])) else (if i.val < 110 then (if i.val < 109 then [276] else [277, 278]) else (if i.val < 111 then [279, 280] else [281, 282]))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [283, 284] else [285]) else (if i.val < 115 then [286] else [287])) else (if i.val < 118 then (if i.val < 117 then [288, 289] else [290]) else (if i.val < 119 then [291] else [292, 293, 294, 295]))))))) else (if i.val < 180 then (if i.val < 150 then (if i.val < 135 then (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then [296, 297, 298, 299, 300, 301, 302, 303] else (if i.val < 122 then [304] else [305])) else (if i.val < 125 then (if i.val < 124 then [306] else [307]) else (if i.val < 126 then [308] else [309]))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then [310, 311, 312, 313] else [314, 315, 316, 317]) else (if i.val < 130 then [318] else [319])) else (if i.val < 133 then (if i.val < 132 then [320] else [321, 322]) else (if i.val < 134 then [323] else [324])))) else (if i.val < 142 then (if i.val < 138 then (if i.val < 136 then [325, 326] else (if i.val < 137 then [327, 328, 329, 330] else [331])) else (if i.val < 140 then (if i.val < 139 then [332] else [333]) else (if i.val < 141 then [334, 335] else [336, 337]))) else (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then [338, 339] else [340, 341, 342, 343, 344, 345, 346, 347]) else (if i.val < 145 then [348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363] else [364])) else (if i.val < 148 then (if i.val < 147 then [365] else [366]) else (if i.val < 149 then [367, 368] else [369]))))) else (if i.val < 165 then (if i.val < 157 then (if i.val < 153 then (if i.val < 151 then [370] else (if i.val < 152 then [371, 372] else [373, 374, 375, 376])) else (if i.val < 155 then (if i.val < 154 then [377] else [378]) else (if i.val < 156 then [379] else [380, 381]))) else (if i.val < 161 then (if i.val < 159 then (if i.val < 158 then [382] else [383]) else (if i.val < 160 then [384, 385, 386, 387] else [388, 389, 390, 391, 392, 393, 394, 395])) else (if i.val < 163 then (if i.val < 162 then [396] else [397]) else (if i.val < 164 then [398] else [399, 400])))) else (if i.val < 172 then (if i.val < 168 then (if i.val < 166 then [401] else (if i.val < 167 then [402] else [403, 404])) else (if i.val < 170 then (if i.val < 169 then [405, 406, 407, 408] else [409, 410]) else (if i.val < 171 then [411, 412] else [413, 414]))) else (if i.val < 176 then (if i.val < 174 then (if i.val < 173 then [415, 416, 417, 418] else [419, 420, 421, 422]) else (if i.val < 175 then [423, 424, 425, 426] else [427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442])) else (if i.val < 178 then (if i.val < 177 then [443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474] else [475]) else (if i.val < 179 then [476] else [477])))))) else (if i.val < 210 then (if i.val < 195 then (if i.val < 187 then (if i.val < 183 then (if i.val < 181 then [478] else (if i.val < 182 then [479] else [480])) else (if i.val < 185 then (if i.val < 184 then [481] else [482]) else (if i.val < 186 then [483] else [484]))) else (if i.val < 191 then (if i.val < 189 then (if i.val < 188 then [485] else [486]) else (if i.val < 190 then [487] else [488])) else (if i.val < 193 then (if i.val < 192 then [489] else [490]) else (if i.val < 194 then [491] else [492])))) else (if i.val < 202 then (if i.val < 198 then (if i.val < 196 then [493] else (if i.val < 197 then [494] else [495])) else (if i.val < 200 then (if i.val < 199 then [496] else [497]) else (if i.val < 201 then [498] else [499]))) else (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then [500] else [501]) else (if i.val < 205 then [502] else [503])) else (if i.val < 208 then (if i.val < 207 then [504] else [505]) else (if i.val < 209 then [506] else [507]))))) else (if i.val < 225 then (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then [508] else (if i.val < 212 then [509] else [510])) else (if i.val < 215 then (if i.val < 214 then [511] else [512]) else (if i.val < 216 then [513] else [514]))) else (if i.val < 221 then (if i.val < 219 then (if i.val < 218 then [515, 516] else [517]) else (if i.val < 220 then [518] else [519, 520])) else (if i.val < 223 then (if i.val < 222 then [521] else [522]) else (if i.val < 224 then [523, 524] else [525])))) else (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then [526] else (if i.val < 227 then [527] else [528])) else (if i.val < 230 then (if i.val < 229 then [529] else [530]) else (if i.val < 231 then [531] else [532]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [533] else [534]) else (if i.val < 235 then [535] else [536])) else (if i.val < 238 then (if i.val < 237 then [537] else [538]) else (if i.val < 239 then [539] else [540])))))))) else (if i.val < 360 then (if i.val < 300 then (if i.val < 270 then (if i.val < 255 then (if i.val < 247 then (if i.val < 243 then (if i.val < 241 then [541] else (if i.val < 242 then [542] else [543])) else (if i.val < 245 then (if i.val < 244 then [544] else [545]) else (if i.val < 246 then [546] else [547]))) else (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then [548] else [549]) else (if i.val < 250 then [550] else [551])) else (if i.val < 253 then (if i.val < 252 then [552] else [553]) else (if i.val < 254 then [554] else [555, 556])))) else (if i.val < 262 then (if i.val < 258 then (if i.val < 256 then [557] else (if i.val < 257 then [558] else [559, 560])) else (if i.val < 260 then (if i.val < 259 then [561, 562, 563, 564] else [565]) else (if i.val < 261 then [566] else [567]))) else (if i.val < 266 then (if i.val < 264 then (if i.val < 263 then [568, 569] else [570]) else (if i.val < 265 then [571] else [572, 573])) else (if i.val < 268 then (if i.val < 267 then [574, 575] else [576]) else (if i.val < 269 then [577] else [578]))))) else (if i.val < 285 then (if i.val < 277 then (if i.val < 273 then (if i.val < 271 then [579] else (if i.val < 272 then [580] else [581])) else (if i.val < 275 then (if i.val < 274 then [582] else [583]) else (if i.val < 276 then [584] else [585]))) else (if i.val < 281 then (if i.val < 279 then (if i.val < 278 then [586] else [587]) else (if i.val < 280 then [588] else [589])) else (if i.val < 283 then (if i.val < 282 then [590] else [591]) else (if i.val < 284 then [592] else [593])))) else (if i.val < 292 then (if i.val < 288 then (if i.val < 286 then [594] else (if i.val < 287 then [595] else [596])) else (if i.val < 290 then (if i.val < 289 then [597] else [598]) else (if i.val < 291 then [599] else [600]))) else (if i.val < 296 then (if i.val < 294 then (if i.val < 293 then [601] else [602]) else (if i.val < 295 then [603, 604] else [605, 606, 607, 608])) else (if i.val < 298 then (if i.val < 297 then [609] else [610]) else (if i.val < 299 then [611] else [612, 613])))))) else (if i.val < 330 then (if i.val < 315 then (if i.val < 307 then (if i.val < 303 then (if i.val < 301 then [614] else (if i.val < 302 then [615] else [616, 617, 618, 619])) else (if i.val < 305 then (if i.val < 304 then [620, 621, 622, 623, 624, 625, 626, 627] else [628]) else (if i.val < 306 then [629] else [630]))) else (if i.val < 311 then (if i.val < 309 then (if i.val < 308 then [631] else [632]) else (if i.val < 310 then [633] else [634])) else (if i.val < 313 then (if i.val < 312 then [635] else [636, 637]) else (if i.val < 314 then [638, 639] else [640])))) else (if i.val < 322 then (if i.val < 318 then (if i.val < 316 then [641] else (if i.val < 317 then [642] else [643, 644])) else (if i.val < 320 then (if i.val < 319 then [645] else [646]) else (if i.val < 321 then [647] else [648]))) else (if i.val < 326 then (if i.val < 324 then (if i.val < 323 then [649] else [650]) else (if i.val < 325 then [651] else [652])) else (if i.val < 328 then (if i.val < 327 then [653] else [654]) else (if i.val < 329 then [655] else [656]))))) else (if i.val < 345 then (if i.val < 337 then (if i.val < 333 then (if i.val < 331 then [657, 658] else (if i.val < 332 then [659] else [660])) else (if i.val < 335 then (if i.val < 334 then [661] else [662]) else (if i.val < 336 then [663] else [664]))) else (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then [665] else [666]) else (if i.val < 340 then [667] else [668])) else (if i.val < 343 then (if i.val < 342 then [669] else [670]) else (if i.val < 344 then [671, 672] else [673])))) else (if i.val < 352 then (if i.val < 348 then (if i.val < 346 then [674] else (if i.val < 347 then [675, 676, 677, 678] else [679, 680, 681, 682, 683, 684, 685, 686])) else (if i.val < 350 then (if i.val < 349 then [687] else [688]) else (if i.val < 351 then [689] else [690, 691]))) else (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then [692] else [693]) else (if i.val < 355 then [694, 695] else [696, 697, 698, 699])) else (if i.val < 358 then (if i.val < 357 then [700] else [701]) else (if i.val < 359 then [702] else [703, 704]))))))) else (if i.val < 420 then (if i.val < 390 then (if i.val < 375 then (if i.val < 367 then (if i.val < 363 then (if i.val < 361 then [705, 706] else (if i.val < 362 then [707, 708] else [709, 710, 711, 712, 713, 714, 715, 716])) else (if i.val < 365 then (if i.val < 364 then [717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732] else [733]) else (if i.val < 366 then [734] else [735]))) else (if i.val < 371 then (if i.val < 369 then (if i.val < 368 then [736] else [737]) else (if i.val < 370 then [738] else [739])) else (if i.val < 373 then (if i.val < 372 then [740] else [741]) else (if i.val < 374 then [742] else [743])))) else (if i.val < 382 then (if i.val < 378 then (if i.val < 376 then [744] else (if i.val < 377 then [745, 746] else [747])) else (if i.val < 380 then (if i.val < 379 then [748] else [749]) else (if i.val < 381 then [750] else [751]))) else (if i.val < 386 then (if i.val < 384 then (if i.val < 383 then [752] else [753]) else (if i.val < 385 then [754] else [755])) else (if i.val < 388 then (if i.val < 387 then [756] else [757, 758]) else (if i.val < 389 then [759] else [760]))))) else (if i.val < 405 then (if i.val < 397 then (if i.val < 393 then (if i.val < 391 then [761] else (if i.val < 392 then [762, 763] else [764])) else (if i.val < 395 then (if i.val < 394 then [765] else [766, 767]) else (if i.val < 396 then [768, 769, 770, 771] else [772]))) else (if i.val < 401 then (if i.val < 399 then (if i.val < 398 then [773] else [774]) else (if i.val < 400 then [775] else [776])) else (if i.val < 403 then (if i.val < 402 then [777] else [778]) else (if i.val < 404 then [779] else [780])))) else (if i.val < 412 then (if i.val < 408 then (if i.val < 406 then [781] else (if i.val < 407 then [782] else [783])) else (if i.val < 410 then (if i.val < 409 then [784, 785] else [786]) else (if i.val < 411 then [787] else [788]))) else (if i.val < 416 then (if i.val < 414 then (if i.val < 413 then [789] else [790]) else (if i.val < 415 then [791] else [792])) else (if i.val < 418 then (if i.val < 417 then [793] else [794]) else (if i.val < 419 then [795] else [796])))))) else (if i.val < 450 then (if i.val < 435 then (if i.val < 427 then (if i.val < 423 then (if i.val < 421 then [797] else (if i.val < 422 then [798] else [799, 800])) else (if i.val < 425 then (if i.val < 424 then [801] else [802]) else (if i.val < 426 then [803] else [804, 805]))) else (if i.val < 431 then (if i.val < 429 then (if i.val < 428 then [806] else [807]) else (if i.val < 430 then [808] else [809, 810])) else (if i.val < 433 then (if i.val < 432 then [811] else [812]) else (if i.val < 434 then [813, 814] else [815, 816, 817, 818])))) else (if i.val < 442 then (if i.val < 438 then (if i.val < 436 then [819] else (if i.val < 437 then [820] else [821])) else (if i.val < 440 then (if i.val < 439 then [822, 823] else [824, 825]) else (if i.val < 441 then [826, 827] else [828, 829, 830, 831, 832, 833, 834, 835]))) else (if i.val < 446 then (if i.val < 444 then (if i.val < 443 then [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851] else [852]) else (if i.val < 445 then [853] else [854])) else (if i.val < 448 then (if i.val < 447 then [855, 856] else [857]) else (if i.val < 449 then [858] else [859, 860]))))) else (if i.val < 465 then (if i.val < 457 then (if i.val < 453 then (if i.val < 451 then [861, 862, 863, 864] else (if i.val < 452 then [865] else [866])) else (if i.val < 455 then (if i.val < 454 then [867] else [868, 869]) else (if i.val < 456 then [870] else [871]))) else (if i.val < 461 then (if i.val < 459 then (if i.val < 458 then [872, 873, 874, 875] else [876, 877, 878, 879, 880, 881, 882, 883]) else (if i.val < 460 then [884] else [885])) else (if i.val < 463 then (if i.val < 462 then [886] else [887, 888]) else (if i.val < 464 then [889] else [890])))) else (if i.val < 473 then (if i.val < 469 then (if i.val < 467 then (if i.val < 466 then [891, 892] else [893, 894, 895, 896]) else (if i.val < 468 then [897, 898] else [899, 900])) else (if i.val < 471 then (if i.val < 470 then [901, 902] else [903, 904, 905, 906]) else (if i.val < 472 then [907, 908, 909, 910] else [911, 912, 913, 914]))) else (if i.val < 477 then (if i.val < 475 then (if i.val < 474 then [915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930] else [931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962]) else (if i.val < 476 then [475] else [475])) else (if i.val < 479 then (if i.val < 478 then [475] else [475]) else (if i.val < 480 then [476] else [475]))))))))) else (if i.val < 722 then (if i.val < 601 then (if i.val < 541 then (if i.val < 511 then (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then [475] else (if i.val < 483 then [475] else [477])) else (if i.val < 486 then (if i.val < 485 then [475] else [476]) else (if i.val < 487 then [477] else [478]))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then [479] else [475]) else (if i.val < 491 then [475] else [475])) else (if i.val < 494 then (if i.val < 493 then [475] else [476]) else (if i.val < 495 then [475] else [480])))) else (if i.val < 503 then (if i.val < 499 then (if i.val < 497 then [475] else (if i.val < 498 then [480] else [475])) else (if i.val < 501 then (if i.val < 500 then [477] else [480]) else (if i.val < 502 then [482] else [483]))) else (if i.val < 507 then (if i.val < 505 then (if i.val < 504 then [475] else [476]) else (if i.val < 506 then [477] else [478])) else (if i.val < 509 then (if i.val < 508 then [479] else [480]) else (if i.val < 510 then [481] else [482]))))) else (if i.val < 526 then (if i.val < 518 then (if i.val < 514 then (if i.val < 512 then [483] else (if i.val < 513 then [484] else [485])) else (if i.val < 516 then (if i.val < 515 then [486] else [487]) else (if i.val < 517 then [488] else [475]))) else (if i.val < 522 then (if i.val < 520 then (if i.val < 519 then [517] else [518]) else (if i.val < 521 then [519, 520] else [475])) else (if i.val < 524 then (if i.val < 523 then [517] else [518]) else (if i.val < 525 then [519] else [475])))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then [517] else (if i.val < 528 then [518] else [475])) else (if i.val < 531 then (if i.val < 530 then [476] else [517]) else (if i.val < 532 then [518] else [521]))) else (if i.val < 537 then (if i.val < 535 then (if i.val < 534 then [522] else [475]) else (if i.val < 536 then [517] else [475])) else (if i.val < 539 then (if i.val < 538 then [517] else [475]) else (if i.val < 540 then [477] else [517])))))) else (if i.val < 571 then (if i.val < 556 then (if i.val < 548 then (if i.val < 544 then (if i.val < 542 then [525] else (if i.val < 543 then [475] else [476])) else (if i.val < 546 then (if i.val < 545 then [477] else [478]) else (if i.val < 547 then [479] else [517]))) else (if i.val < 552 then (if i.val < 550 then (if i.val < 549 then [521] else [525]) else (if i.val < 551 then [528] else [529])) else (if i.val < 554 then (if i.val < 553 then [475] else [489]) else (if i.val < 555 then [517] else [518])))) else (if i.val < 563 then (if i.val < 559 then (if i.val < 557 then [519, 520] else (if i.val < 558 then [552] else [553])) else (if i.val < 561 then (if i.val < 560 then [554] else [555, 556]) else (if i.val < 562 then [557] else [558]))) else (if i.val < 567 then (if i.val < 565 then (if i.val < 564 then [559, 560] else [561, 562, 563, 564]) else (if i.val < 566 then [475] else [489])) else (if i.val < 569 then (if i.val < 568 then [517] else [518]) else (if i.val < 570 then [519] else [552]))))) else (if i.val < 586 then (if i.val < 578 then (if i.val < 574 then (if i.val < 572 then [553] else (if i.val < 573 then [554] else [555])) else (if i.val < 576 then (if i.val < 575 then [557] else [559]) else (if i.val < 577 then [475] else [489]))) else (if i.val < 582 then (if i.val < 580 then (if i.val < 579 then [517] else [518]) else (if i.val < 581 then [552] else [554])) else (if i.val < 584 then (if i.val < 583 then [475] else [476]) else (if i.val < 585 then [489] else [490])))) else (if i.val < 593 then (if i.val < 589 then (if i.val < 587 then [517] else (if i.val < 588 then [518] else [521])) else (if i.val < 591 then (if i.val < 590 then [522] else [552]) else (if i.val < 592 then [554] else [565]))) else (if i.val < 597 then (if i.val < 595 then (if i.val < 594 then [567] else [475]) else (if i.val < 596 then [480] else [489])) else (if i.val < 599 then (if i.val < 598 then [494] else [495]) else (if i.val < 600 then [517] else [534]))))))) else (if i.val < 661 then (if i.val < 631 then (if i.val < 616 then (if i.val < 608 then (if i.val < 604 then (if i.val < 602 then [552] else (if i.val < 603 then [553] else [554])) else (if i.val < 606 then (if i.val < 605 then [555, 556] else [557]) else (if i.val < 607 then [558] else [559, 560]))) else (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then [561, 562, 563, 564] else [594]) else (if i.val < 611 then [595] else [596])) else (if i.val < 614 then (if i.val < 613 then [597] else [598]) else (if i.val < 615 then [599] else [600])))) else (if i.val < 623 then (if i.val < 619 then (if i.val < 617 then [601] else (if i.val < 618 then [602] else [603, 604])) else (if i.val < 621 then (if i.val < 620 then [605, 606, 607, 608] else [609]) else (if i.val < 622 then [610] else [611]))) else (if i.val < 627 then (if i.val < 625 then (if i.val < 624 then [612, 613] else [614]) else (if i.val < 626 then [615] else [616, 617, 618, 619])) else (if i.val < 629 then (if i.val < 628 then [620, 621, 622, 623, 624, 625, 626, 627] else [475]) else (if i.val < 630 then [480] else [489]))))) else (if i.val < 646 then (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then [494] else (if i.val < 633 then [517] else [534])) else (if i.val < 636 then (if i.val < 635 then [552] else [553]) else (if i.val < 637 then [554] else [555]))) else (if i.val < 642 then (if i.val < 640 then (if i.val < 639 then [557] else [559]) else (if i.val < 641 then [594] else [596])) else (if i.val < 644 then (if i.val < 643 then [599] else [601]) else (if i.val < 645 then [603] else [475])))) else (if i.val < 653 then (if i.val < 649 then (if i.val < 647 then [477] else (if i.val < 648 then [480] else [482])) else (if i.val < 651 then (if i.val < 650 then [483] else [489]) else (if i.val < 652 then [491] else [494]))) else (if i.val < 657 then (if i.val < 655 then (if i.val < 654 then [495] else [498]) else (if i.val < 656 then [499] else [500])) else (if i.val < 659 then (if i.val < 658 then [501] else [502]) else (if i.val < 660 then [517] else [525])))))) else (if i.val < 691 then (if i.val < 676 then (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then [534] else (if i.val < 663 then [538] else [539])) else (if i.val < 666 then (if i.val < 665 then [552] else [554]) else (if i.val < 667 then [576] else [578]))) else (if i.val < 672 then (if i.val < 670 then (if i.val < 669 then [594] else [595]) else (if i.val < 671 then [596] else [597])) else (if i.val < 674 then (if i.val < 673 then [598] else [599]) else (if i.val < 675 then [600] else [601])))) else (if i.val < 683 then (if i.val < 679 then (if i.val < 677 then [602] else (if i.val < 678 then [603, 604] else [605, 606, 607, 608])) else (if i.val < 681 then (if i.val < 680 then [609] else [610]) else (if i.val < 682 then [611] else [612, 613]))) else (if i.val < 687 then (if i.val < 685 then (if i.val < 684 then [614] else [615]) else (if i.val < 686 then [616, 617, 618, 619] else [620, 621, 622, 623, 624, 625, 626, 627])) else (if i.val < 689 then (if i.val < 688 then [645] else [646]) else (if i.val < 690 then [647] else [648]))))) else (if i.val < 706 then (if i.val < 698 then (if i.val < 694 then (if i.val < 692 then [649] else (if i.val < 693 then [650] else [651])) else (if i.val < 696 then (if i.val < 695 then [652] else [653]) else (if i.val < 697 then [654] else [655]))) else (if i.val < 702 then (if i.val < 700 then (if i.val < 699 then [656] else [657, 658]) else (if i.val < 701 then [659] else [660])) else (if i.val < 704 then (if i.val < 703 then [661] else [662]) else (if i.val < 705 then [663] else [664])))) else (if i.val < 714 then (if i.val < 710 then (if i.val < 708 then (if i.val < 707 then [665] else [666]) else (if i.val < 709 then [667] else [668])) else (if i.val < 712 then (if i.val < 711 then [669] else [670]) else (if i.val < 713 then [671, 672] else [673]))) else (if i.val < 718 then (if i.val < 716 then (if i.val < 715 then [674] else [675, 676, 677, 678]) else (if i.val < 717 then [679, 680, 681, 682, 683, 684, 685, 686] else [687])) else (if i.val < 720 then (if i.val < 719 then [688] else [689]) else (if i.val < 721 then [690, 691] else [692])))))))) else (if i.val < 842 then (if i.val < 782 then (if i.val < 752 then (if i.val < 737 then (if i.val < 729 then (if i.val < 725 then (if i.val < 723 then [693] else (if i.val < 724 then [694, 695] else [696, 697, 698, 699])) else (if i.val < 727 then (if i.val < 726 then [700] else [701]) else (if i.val < 728 then [702] else [703, 704]))) else (if i.val < 733 then (if i.val < 731 then (if i.val < 730 then [705, 706] else [707, 708]) else (if i.val < 732 then [709, 710, 711, 712, 713, 714, 715, 716] else [717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732])) else (if i.val < 735 then (if i.val < 734 then [475] else [476]) else (if i.val < 736 then [477] else [478])))) else (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then [479] else (if i.val < 739 then [480] else [481])) else (if i.val < 742 then (if i.val < 741 then [482] else [483]) else (if i.val < 743 then [484] else [485]))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then [486] else [487]) else (if i.val < 747 then [488] else [489])) else (if i.val < 750 then (if i.val < 749 then [490] else [491]) else (if i.val < 751 then [492] else [493]))))) else (if i.val < 767 then (if i.val < 759 then (if i.val < 755 then (if i.val < 753 then [494] else (if i.val < 754 then [496] else [498])) else (if i.val < 757 then (if i.val < 756 then [499] else [500]) else (if i.val < 758 then [501] else [502]))) else (if i.val < 763 then (if i.val < 761 then (if i.val < 760 then [503] else [504]) else (if i.val < 762 then [505] else [506])) else (if i.val < 765 then (if i.val < 764 then [507] else [508]) else (if i.val < 766 then [509] else [510])))) else (if i.val < 774 then (if i.val < 770 then (if i.val < 768 then [511] else (if i.val < 769 then [512] else [513])) else (if i.val < 772 then (if i.val < 771 then [514] else [515, 516]) else (if i.val < 773 then [517] else [521]))) else (if i.val < 778 then (if i.val < 776 then (if i.val < 775 then [525] else [528]) else (if i.val < 777 then [529] else [534])) else (if i.val < 780 then (if i.val < 779 then [536] else [538]) else (if i.val < 781 then [539] else [542])))))) else (if i.val < 812 then (if i.val < 797 then (if i.val < 789 then (if i.val < 785 then (if i.val < 783 then [543] else (if i.val < 784 then [544] else [545])) else (if i.val < 787 then (if i.val < 786 then [546] else [552]) else (if i.val < 788 then [554] else [565]))) else (if i.val < 793 then (if i.val < 791 then (if i.val < 790 then [567] else [576]) else (if i.val < 792 then [578] else [582])) else (if i.val < 795 then (if i.val < 794 then [583] else [586]) else (if i.val < 796 then [588] else [594])))) else (if i.val < 804 then (if i.val < 800 then (if i.val < 798 then [596] else (if i.val < 799 then [599] else [601])) else (if i.val < 802 then (if i.val < 801 then [603] else [628]) else (if i.val < 803 then [630] else [632]))) else (if i.val < 808 then (if i.val < 806 then (if i.val < 805 then [634] else [636]) else (if i.val < 807 then [645] else [646])) else (if i.val < 810 then (if i.val < 809 then [647] else [648]) else (if i.val < 811 then [649] else [650]))))) else (if i.val < 827 then (if i.val < 819 then (if i.val < 815 then (if i.val < 813 then [651] else (if i.val < 814 then [652] else [653])) else (if i.val < 817 then (if i.val < 816 then [654] else [655]) else (if i.val < 818 then [656] else [657, 658]))) else (if i.val < 823 then (if i.val < 821 then (if i.val < 820 then [659] else [660]) else (if i.val < 822 then [661] else [662])) else (if i.val < 825 then (if i.val < 824 then [663] else [664]) else (if i.val < 826 then [665] else [666])))) else (if i.val < 834 then (if i.val < 830 then (if i.val < 828 then [667] else (if i.val < 829 then [668] else [669])) else (if i.val < 832 then (if i.val < 831 then [670] else [671, 672]) else (if i.val < 833 then [673] else [674]))) else (if i.val < 838 then (if i.val < 836 then (if i.val < 835 then [675, 676, 677, 678] else [679, 680, 681, 682, 683, 684, 685, 686]) else (if i.val < 837 then [687] else [688])) else (if i.val < 840 then (if i.val < 839 then [689] else [690, 691]) else (if i.val < 841 then [692] else [693]))))))) else (if i.val < 902 then (if i.val < 872 then (if i.val < 857 then (if i.val < 849 then (if i.val < 845 then (if i.val < 843 then [694, 695] else (if i.val < 844 then [696, 697, 698, 699] else [700])) else (if i.val < 847 then (if i.val < 846 then [701] else [702]) else (if i.val < 848 then [703, 704] else [705, 706]))) else (if i.val < 853 then (if i.val < 851 then (if i.val < 850 then [707, 708] else [709, 710, 711, 712, 713, 714, 715, 716]) else (if i.val < 852 then [717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732] else [733])) else (if i.val < 855 then (if i.val < 854 then [734] else [735]) else (if i.val < 856 then [736] else [737])))) else (if i.val < 864 then (if i.val < 860 then (if i.val < 858 then [738] else (if i.val < 859 then [739] else [740])) else (if i.val < 862 then (if i.val < 861 then [741] else [742]) else (if i.val < 863 then [743] else [744]))) else (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then [745, 746] else [747]) else (if i.val < 867 then [748] else [749])) else (if i.val < 870 then (if i.val < 869 then [750] else [751]) else (if i.val < 871 then [752] else [753]))))) else (if i.val < 887 then (if i.val < 879 then (if i.val < 875 then (if i.val < 873 then [754] else (if i.val < 874 then [755] else [756])) else (if i.val < 877 then (if i.val < 876 then [757, 758] else [759]) else (if i.val < 878 then [760] else [761]))) else (if i.val < 883 then (if i.val < 881 then (if i.val < 880 then [762, 763] else [764]) else (if i.val < 882 then [765] else [766, 767])) else (if i.val < 885 then (if i.val < 884 then [768, 769, 770, 771] else [772]) else (if i.val < 886 then [773] else [774])))) else (if i.val < 894 then (if i.val < 890 then (if i.val < 888 then [775] else (if i.val < 889 then [776] else [777])) else (if i.val < 892 then (if i.val < 891 then [778] else [779]) else (if i.val < 893 then [780] else [781]))) else (if i.val < 898 then (if i.val < 896 then (if i.val < 895 then [782] else [783]) else (if i.val < 897 then [784, 785] else [786])) else (if i.val < 900 then (if i.val < 899 then [787] else [788]) else (if i.val < 901 then [789] else [790])))))) else (if i.val < 932 then (if i.val < 917 then (if i.val < 909 then (if i.val < 905 then (if i.val < 903 then [791] else (if i.val < 904 then [792] else [793])) else (if i.val < 907 then (if i.val < 906 then [794] else [795]) else (if i.val < 908 then [796] else [797]))) else (if i.val < 913 then (if i.val < 911 then (if i.val < 910 then [798] else [799, 800]) else (if i.val < 912 then [801] else [802])) else (if i.val < 915 then (if i.val < 914 then [803] else [804, 805]) else (if i.val < 916 then [806] else [807])))) else (if i.val < 924 then (if i.val < 920 then (if i.val < 918 then [808] else (if i.val < 919 then [809, 810] else [811])) else (if i.val < 922 then (if i.val < 921 then [812] else [813, 814]) else (if i.val < 923 then [815, 816, 817, 818] else [819]))) else (if i.val < 928 then (if i.val < 926 then (if i.val < 925 then [820] else [821]) else (if i.val < 927 then [822, 823] else [824, 825])) else (if i.val < 930 then (if i.val < 929 then [826, 827] else [828, 829, 830, 831, 832, 833, 834, 835]) else (if i.val < 931 then [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851] else [852]))))) else (if i.val < 947 then (if i.val < 939 then (if i.val < 935 then (if i.val < 933 then [853] else (if i.val < 934 then [854] else [855, 856])) else (if i.val < 937 then (if i.val < 936 then [857] else [858]) else (if i.val < 938 then [859, 860] else [861, 862, 863, 864]))) else (if i.val < 943 then (if i.val < 941 then (if i.val < 940 then [865] else [866]) else (if i.val < 942 then [867] else [868, 869])) else (if i.val < 945 then (if i.val < 944 then [870] else [871]) else (if i.val < 946 then [872, 873, 874, 875] else [876, 877, 878, 879, 880, 881, 882, 883])))) else (if i.val < 955 then (if i.val < 951 then (if i.val < 949 then (if i.val < 948 then [884] else [885]) else (if i.val < 950 then [886] else [887, 888])) else (if i.val < 953 then (if i.val < 952 then [889] else [890]) else (if i.val < 954 then [891, 892] else [893, 894, 895, 896]))) else (if i.val < 959 then (if i.val < 957 then (if i.val < 956 then [897, 898] else [899, 900]) else (if i.val < 958 then [901, 902] else [903, 904, 905, 906])) else (if i.val < 961 then (if i.val < 960 then [907, 908, 909, 910] else [911, 912, 913, 914]) else (if i.val < 962 then [915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930] else [931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962]))))))))))
def vectors (i : Fin 963) : List ℕ :=
  (if i.val < 481 then (if i.val < 240 then (if i.val < 120 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [1, 32, 144, 298, 488, 734, 1064, 1505, 2091, 2864, 3875] else (if i.val < 2 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 5 then (if i.val < 4 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 6 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]) else (if i.val < 10 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 13 then (if i.val < 12 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 14 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else (if i.val < 17 then [1, 8, 13, 14, 14, 14, 14, 14, 14, 14, 14] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])) else (if i.val < 20 then (if i.val < 19 then [1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4] else [1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3]) else (if i.val < 21 then [1, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]) else (if i.val < 25 then [1, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76])) else (if i.val < 28 then (if i.val < 27 then [1, 4, 8, 11, 11, 11, 11, 11, 11, 11, 11] else [1, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6]) else (if i.val < 29 then [1, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then [1, 8, 14, 17, 17, 17, 17, 17, 17, 17, 17] else (if i.val < 32 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 32, 111, 230, 392, 611, 907, 1306, 1841, 2553, 3492])) else (if i.val < 35 then (if i.val < 34 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 36 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 40 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 43 then (if i.val < 42 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 44 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 47 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 50 then (if i.val < 49 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 51 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 55 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 58 then (if i.val < 57 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 59 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 62 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 65 then (if i.val < 64 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 66 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) else (if i.val < 70 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3])) else (if i.val < 73 then (if i.val < 72 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 74 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 77 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 80 then (if i.val < 79 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 81 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 85 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 88 then (if i.val < 87 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 89 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 92 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 95 then (if i.val < 94 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 96 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76]))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 100 then [1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] else [1, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6])) else (if i.val < 103 then (if i.val < 102 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 104 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 107 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 110 then (if i.val < 109 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 111 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 115 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 118 then (if i.val < 117 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 119 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76]))))))) else (if i.val < 180 then (if i.val < 150 then (if i.val < 135 then (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335] else (if i.val < 122 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 125 then (if i.val < 124 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 126 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then [1, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]) else (if i.val < 130 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 133 then (if i.val < 132 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 134 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 142 then (if i.val < 138 then (if i.val < 136 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 137 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 140 then (if i.val < 139 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 141 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]) else (if i.val < 145 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 148 then (if i.val < 147 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 149 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 165 then (if i.val < 157 then (if i.val < 153 then (if i.val < 151 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 152 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5])) else (if i.val < 155 then (if i.val < 154 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 156 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 161 then (if i.val < 159 then (if i.val < 158 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 160 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 8, 13, 14, 14, 14, 14, 14, 14, 14, 14])) else (if i.val < 163 then (if i.val < 162 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 164 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))) else (if i.val < 172 then (if i.val < 168 then (if i.val < 166 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 167 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 170 then (if i.val < 169 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 171 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 176 then (if i.val < 174 then (if i.val < 173 then [1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]) else (if i.val < 175 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152])) else (if i.val < 178 then (if i.val < 177 then [1, 32, 111, 230, 392, 611, 907, 1306, 1841, 2553, 3492] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 179 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 210 then (if i.val < 195 then (if i.val < 187 then (if i.val < 183 then (if i.val < 181 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 182 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 185 then (if i.val < 184 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 186 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 191 then (if i.val < 189 then (if i.val < 188 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 190 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 193 then (if i.val < 192 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 194 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 202 then (if i.val < 198 then (if i.val < 196 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 197 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 200 then (if i.val < 199 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 201 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 205 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 208 then (if i.val < 207 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 209 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 225 then (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 212 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 215 then (if i.val < 214 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 216 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 221 then (if i.val < 219 then (if i.val < 218 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 220 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])) else (if i.val < 223 then (if i.val < 222 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 224 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 227 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 230 then (if i.val < 229 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 231 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 235 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 238 then (if i.val < 237 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 239 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))))) else (if i.val < 360 then (if i.val < 300 then (if i.val < 270 then (if i.val < 255 then (if i.val < 247 then (if i.val < 243 then (if i.val < 241 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 242 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 245 then (if i.val < 244 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 246 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 250 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 253 then (if i.val < 252 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 254 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])))) else (if i.val < 262 then (if i.val < 258 then (if i.val < 256 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 257 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])) else (if i.val < 260 then (if i.val < 259 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 261 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 266 then (if i.val < 264 then (if i.val < 263 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 265 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 268 then (if i.val < 267 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 269 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 285 then (if i.val < 277 then (if i.val < 273 then (if i.val < 271 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 272 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 275 then (if i.val < 274 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 276 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 281 then (if i.val < 279 then (if i.val < 278 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 280 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 283 then (if i.val < 282 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 284 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 292 then (if i.val < 288 then (if i.val < 286 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 287 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 290 then (if i.val < 289 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 291 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 296 then (if i.val < 294 then (if i.val < 293 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 295 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76])) else (if i.val < 298 then (if i.val < 297 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 299 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])))))) else (if i.val < 330 then (if i.val < 315 then (if i.val < 307 then (if i.val < 303 then (if i.val < 301 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 302 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76])) else (if i.val < 305 then (if i.val < 304 then [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 306 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 311 then (if i.val < 309 then (if i.val < 308 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 310 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 313 then (if i.val < 312 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 314 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 322 then (if i.val < 318 then (if i.val < 316 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 317 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 320 then (if i.val < 319 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 321 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 326 then (if i.val < 324 then (if i.val < 323 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 325 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 328 then (if i.val < 327 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 329 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 345 then (if i.val < 337 then (if i.val < 333 then (if i.val < 331 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 332 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 335 then (if i.val < 334 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 336 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 340 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 343 then (if i.val < 342 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 344 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 352 then (if i.val < 348 then (if i.val < 346 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 347 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335])) else (if i.val < 350 then (if i.val < 349 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 351 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 355 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5])) else (if i.val < 358 then (if i.val < 357 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 359 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))))))) else (if i.val < 420 then (if i.val < 390 then (if i.val < 375 then (if i.val < 367 then (if i.val < 363 then (if i.val < 361 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 362 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335])) else (if i.val < 365 then (if i.val < 364 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 366 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 371 then (if i.val < 369 then (if i.val < 368 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 370 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 373 then (if i.val < 372 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 374 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 382 then (if i.val < 378 then (if i.val < 376 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 377 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 380 then (if i.val < 379 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 381 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 386 then (if i.val < 384 then (if i.val < 383 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 385 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 388 then (if i.val < 387 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 389 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 405 then (if i.val < 397 then (if i.val < 393 then (if i.val < 391 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 392 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 395 then (if i.val < 394 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 396 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 401 then (if i.val < 399 then (if i.val < 398 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 400 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 403 then (if i.val < 402 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 404 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 412 then (if i.val < 408 then (if i.val < 406 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 407 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 410 then (if i.val < 409 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 411 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 416 then (if i.val < 414 then (if i.val < 413 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 415 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 418 then (if i.val < 417 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 419 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 450 then (if i.val < 435 then (if i.val < 427 then (if i.val < 423 then (if i.val < 421 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 422 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 425 then (if i.val < 424 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 426 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 431 then (if i.val < 429 then (if i.val < 428 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 430 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 433 then (if i.val < 432 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 434 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5])))) else (if i.val < 442 then (if i.val < 438 then (if i.val < 436 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 437 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 440 then (if i.val < 439 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 441 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]))) else (if i.val < 446 then (if i.val < 444 then (if i.val < 443 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 445 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 448 then (if i.val < 447 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 449 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))))) else (if i.val < 465 then (if i.val < 457 then (if i.val < 453 then (if i.val < 451 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else (if i.val < 452 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 455 then (if i.val < 454 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 456 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 461 then (if i.val < 459 then (if i.val < 458 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 8, 13, 14, 14, 14, 14, 14, 14, 14, 14]) else (if i.val < 460 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 463 then (if i.val < 462 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 464 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 473 then (if i.val < 469 then (if i.val < 467 then (if i.val < 466 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]) else (if i.val < 468 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 471 then (if i.val < 470 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]) else (if i.val < 472 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]))) else (if i.val < 477 then (if i.val < 475 then (if i.val < 474 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 32, 111, 230, 392, 611, 907, 1306, 1841, 2553, 3492]) else (if i.val < 476 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 479 then (if i.val < 478 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 480 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))))))) else (if i.val < 722 then (if i.val < 601 then (if i.val < 541 then (if i.val < 511 then (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 483 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 486 then (if i.val < 485 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 487 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 491 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 494 then (if i.val < 493 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 495 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 503 then (if i.val < 499 then (if i.val < 497 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 498 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 501 then (if i.val < 500 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 502 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 507 then (if i.val < 505 then (if i.val < 504 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 506 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 509 then (if i.val < 508 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 510 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 526 then (if i.val < 518 then (if i.val < 514 then (if i.val < 512 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 513 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 516 then (if i.val < 515 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 517 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 522 then (if i.val < 520 then (if i.val < 519 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 521 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 524 then (if i.val < 523 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 525 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 528 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 531 then (if i.val < 530 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 532 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 537 then (if i.val < 535 then (if i.val < 534 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 536 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 539 then (if i.val < 538 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 540 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 571 then (if i.val < 556 then (if i.val < 548 then (if i.val < 544 then (if i.val < 542 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 543 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 546 then (if i.val < 545 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 547 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 552 then (if i.val < 550 then (if i.val < 549 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 551 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 554 then (if i.val < 553 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 555 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 563 then (if i.val < 559 then (if i.val < 557 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else (if i.val < 558 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 561 then (if i.val < 560 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) else (if i.val < 562 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 567 then (if i.val < 565 then (if i.val < 564 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76]) else (if i.val < 566 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 569 then (if i.val < 568 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 570 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 586 then (if i.val < 578 then (if i.val < 574 then (if i.val < 572 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 573 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 576 then (if i.val < 575 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 577 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 582 then (if i.val < 580 then (if i.val < 579 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 581 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 584 then (if i.val < 583 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 585 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 593 then (if i.val < 589 then (if i.val < 587 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 588 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 591 then (if i.val < 590 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 592 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 597 then (if i.val < 595 then (if i.val < 594 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 596 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 599 then (if i.val < 598 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 600 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))))) else (if i.val < 661 then (if i.val < 631 then (if i.val < 616 then (if i.val < 608 then (if i.val < 604 then (if i.val < 602 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 603 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 606 then (if i.val < 605 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 607 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]))) else (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 611 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 614 then (if i.val < 613 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 615 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 623 then (if i.val < 619 then (if i.val < 617 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 618 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])) else (if i.val < 621 then (if i.val < 620 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 622 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 627 then (if i.val < 625 then (if i.val < 624 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 626 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76])) else (if i.val < 629 then (if i.val < 628 then [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 630 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 646 then (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 633 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 636 then (if i.val < 635 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 637 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 642 then (if i.val < 640 then (if i.val < 639 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 641 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 644 then (if i.val < 643 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 645 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 653 then (if i.val < 649 then (if i.val < 647 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 648 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 651 then (if i.val < 650 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 652 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 657 then (if i.val < 655 then (if i.val < 654 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 656 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 659 then (if i.val < 658 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 660 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 691 then (if i.val < 676 then (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 663 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 666 then (if i.val < 665 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 667 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 672 then (if i.val < 670 then (if i.val < 669 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 671 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 674 then (if i.val < 673 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 675 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 683 then (if i.val < 679 then (if i.val < 677 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 678 then [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76])) else (if i.val < 681 then (if i.val < 680 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 682 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 687 then (if i.val < 685 then (if i.val < 684 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 686 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335])) else (if i.val < 689 then (if i.val < 688 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 690 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 706 then (if i.val < 698 then (if i.val < 694 then (if i.val < 692 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 693 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 696 then (if i.val < 695 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 697 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 702 then (if i.val < 700 then (if i.val < 699 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 701 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 704 then (if i.val < 703 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 705 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 714 then (if i.val < 710 then (if i.val < 708 then (if i.val < 707 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 709 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 712 then (if i.val < 711 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 713 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 718 then (if i.val < 716 then (if i.val < 715 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76]) else (if i.val < 717 then [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 720 then (if i.val < 719 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 721 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))))) else (if i.val < 842 then (if i.val < 782 then (if i.val < 752 then (if i.val < 737 then (if i.val < 729 then (if i.val < 725 then (if i.val < 723 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 724 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5])) else (if i.val < 727 then (if i.val < 726 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 728 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 733 then (if i.val < 731 then (if i.val < 730 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 732 then [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335] else [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152])) else (if i.val < 735 then (if i.val < 734 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 736 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 739 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 742 then (if i.val < 741 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 743 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 747 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 750 then (if i.val < 749 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 751 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 767 then (if i.val < 759 then (if i.val < 755 then (if i.val < 753 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 754 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 757 then (if i.val < 756 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 758 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 763 then (if i.val < 761 then (if i.val < 760 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 762 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 765 then (if i.val < 764 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 766 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 774 then (if i.val < 770 then (if i.val < 768 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 769 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 772 then (if i.val < 771 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 773 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 778 then (if i.val < 776 then (if i.val < 775 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 777 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 780 then (if i.val < 779 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 781 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 812 then (if i.val < 797 then (if i.val < 789 then (if i.val < 785 then (if i.val < 783 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 784 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 787 then (if i.val < 786 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 788 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 793 then (if i.val < 791 then (if i.val < 790 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 792 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 795 then (if i.val < 794 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 796 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 804 then (if i.val < 800 then (if i.val < 798 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 799 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 802 then (if i.val < 801 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 803 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 808 then (if i.val < 806 then (if i.val < 805 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 807 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 810 then (if i.val < 809 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 811 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 827 then (if i.val < 819 then (if i.val < 815 then (if i.val < 813 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 814 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 817 then (if i.val < 816 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 818 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 823 then (if i.val < 821 then (if i.val < 820 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 822 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 825 then (if i.val < 824 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 826 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 834 then (if i.val < 830 then (if i.val < 828 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 829 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 832 then (if i.val < 831 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 833 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 838 then (if i.val < 836 then (if i.val < 835 then [1, 4, 8, 13, 19, 26, 34, 43, 53, 64, 76] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]) else (if i.val < 837 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 840 then (if i.val < 839 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 841 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))))) else (if i.val < 902 then (if i.val < 872 then (if i.val < 857 then (if i.val < 849 then (if i.val < 845 then (if i.val < 843 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else (if i.val < 844 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 847 then (if i.val < 846 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 848 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))) else (if i.val < 853 then (if i.val < 851 then (if i.val < 850 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]) else (if i.val < 852 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 855 then (if i.val < 854 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 856 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 864 then (if i.val < 860 then (if i.val < 858 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 859 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 862 then (if i.val < 861 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 863 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 867 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 870 then (if i.val < 869 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 871 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 887 then (if i.val < 879 then (if i.val < 875 then (if i.val < 873 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 874 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 877 then (if i.val < 876 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 878 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 883 then (if i.val < 881 then (if i.val < 880 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 882 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 885 then (if i.val < 884 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 886 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 894 then (if i.val < 890 then (if i.val < 888 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 889 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 892 then (if i.val < 891 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 893 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 898 then (if i.val < 896 then (if i.val < 895 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 897 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 900 then (if i.val < 899 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 901 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))))) else (if i.val < 932 then (if i.val < 917 then (if i.val < 909 then (if i.val < 905 then (if i.val < 903 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 904 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 907 then (if i.val < 906 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 908 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 913 then (if i.val < 911 then (if i.val < 910 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 912 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 915 then (if i.val < 914 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 916 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) else (if i.val < 924 then (if i.val < 920 then (if i.val < 918 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 919 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) else (if i.val < 922 then (if i.val < 921 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 923 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) else (if i.val < 928 then (if i.val < 926 then (if i.val < 925 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 927 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 930 then (if i.val < 929 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 8, 19, 34, 54, 80, 113, 154, 204, 264, 335]) else (if i.val < 931 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))))) else (if i.val < 947 then (if i.val < 939 then (if i.val < 935 then (if i.val < 933 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else (if i.val < 934 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 937 then (if i.val < 936 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 938 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]))) else (if i.val < 943 then (if i.val < 941 then (if i.val < 940 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 942 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 945 then (if i.val < 944 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 946 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 8, 13, 14, 14, 14, 14, 14, 14, 14, 14])))) else (if i.val < 955 then (if i.val < 951 then (if i.val < 949 then (if i.val < 948 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 950 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])) else (if i.val < 953 then (if i.val < 952 then [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] else [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) else (if i.val < 954 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]))) else (if i.val < 959 then (if i.val < 957 then (if i.val < 956 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) else (if i.val < 958 then [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] else [1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4])) else (if i.val < 961 then (if i.val < 960 then [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5] else [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5]) else (if i.val < 962 then [1, 16, 46, 88, 145, 222, 325, 461, 638, 865, 1152] else [1, 32, 111, 230, 392, 611, 907, 1306, 1841, 2553, 3492]))))))))))
def v (k : Fin 11) (i : Fin 963) : ℕ := (vectors i)[k.val]!
def accepted (_ : Fin 963) : ℕ := 1
end A224041Table

namespace A224041Certificate
open A224041Proof A224041Table A224041Count

def tableIndex (n : ℕ) : Fin 963 := ⟨n % 963, Nat.mod_lt _ (by decide)⟩
def LocalCheck (i : Fin 963) : Prop :=
  allCols.filterMap (step (state i)) = (succ i).map state
def NumericCheck (s : Fin 963) : Prop :=
  v 0 s = 1 ∧ (∀ k : Fin 10, ((succ s).map (v k.castSucc)).sum = v k.succ s) ∧
  v 10 s + 15 * v 8 s + 15 * v 6 s + v 4 s = 6 * v 9 s + 20 * v 7 s + 6 * v 5 s
instance (i : Fin 963) : Decidable (LocalCheck i) := inferInstanceAs
  (Decidable (allCols.filterMap (step (state i)) = (succ i).map state))
instance (i : Fin 963) : Decidable (NumericCheck i) := by unfold NumericCheck; infer_instance

def LocalBlock (b : ℕ) : Prop := ∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))
def NumericBlock (b : ℕ) : Prop := ∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))
instance (b : ℕ) : Decidable (LocalBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, LocalCheck (tableIndex (8 * b + j.val))))
instance (b : ℕ) : Decidable (NumericBlock b) := inferInstanceAs
  (Decidable (∀ j : Fin 8, NumericCheck (tableIndex (8 * b + j.val))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_0 : PLift (NumericBlock 0) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_1 : PLift (NumericBlock 1) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_2 : PLift (NumericBlock 2) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_3 : PLift (NumericBlock 3) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_4 : PLift (NumericBlock 4) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_5 : PLift (NumericBlock 5) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_6 : PLift (NumericBlock 6) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_7 : PLift (NumericBlock 7) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_8 : PLift (NumericBlock 8) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_9 : PLift (NumericBlock 9) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_10 : PLift (NumericBlock 10) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_11 : PLift (NumericBlock 11) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_12 : PLift (NumericBlock 12) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_13 : PLift (NumericBlock 13) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_14 : PLift (NumericBlock 14) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_15 : PLift (NumericBlock 15) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_16 : PLift (NumericBlock 16) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_17 : PLift (NumericBlock 17) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_18 : PLift (NumericBlock 18) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_19 : PLift (NumericBlock 19) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_20 : PLift (NumericBlock 20) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_21 : PLift (NumericBlock 21) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_22 : PLift (NumericBlock 22) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_23 : PLift (NumericBlock 23) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_24 : PLift (NumericBlock 24) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_25 : PLift (NumericBlock 25) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_26 : PLift (NumericBlock 26) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_27 : PLift (NumericBlock 27) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_28 : PLift (NumericBlock 28) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_29 : PLift (NumericBlock 29) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_30 : PLift (NumericBlock 30) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_31 : PLift (NumericBlock 31) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_32 : PLift (NumericBlock 32) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_33 : PLift (NumericBlock 33) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_34 : PLift (NumericBlock 34) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_35 : PLift (NumericBlock 35) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_36 : PLift (NumericBlock 36) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_37 : PLift (NumericBlock 37) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_38 : PLift (NumericBlock 38) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_39 : PLift (NumericBlock 39) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_40 : PLift (NumericBlock 40) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_41 : PLift (NumericBlock 41) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_42 : PLift (NumericBlock 42) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_43 : PLift (NumericBlock 43) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_44 : PLift (NumericBlock 44) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_45 : PLift (NumericBlock 45) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_46 : PLift (NumericBlock 46) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_47 : PLift (NumericBlock 47) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_48 : PLift (NumericBlock 48) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_49 : PLift (NumericBlock 49) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_50 : PLift (NumericBlock 50) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_51 : PLift (NumericBlock 51) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_52 : PLift (NumericBlock 52) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_53 : PLift (NumericBlock 53) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_54 : PLift (NumericBlock 54) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_55 : PLift (NumericBlock 55) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_56 : PLift (NumericBlock 56) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_57 : PLift (NumericBlock 57) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_58 : PLift (NumericBlock 58) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_59 : PLift (NumericBlock 59) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_60 : PLift (NumericBlock 60) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_61 : PLift (NumericBlock 61) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_62 : PLift (NumericBlock 62) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_63 : PLift (NumericBlock 63) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_64 : PLift (NumericBlock 64) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_65 : PLift (NumericBlock 65) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_66 : PLift (NumericBlock 66) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_67 : PLift (NumericBlock 67) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_68 : PLift (NumericBlock 68) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_69 : PLift (NumericBlock 69) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_70 : PLift (NumericBlock 70) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_71 : PLift (NumericBlock 71) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_72 : PLift (NumericBlock 72) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_73 : PLift (NumericBlock 73) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_74 : PLift (NumericBlock 74) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_75 : PLift (NumericBlock 75) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_76 : PLift (NumericBlock 76) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_77 : PLift (NumericBlock 77) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_78 : PLift (NumericBlock 78) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_79 : PLift (NumericBlock 79) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_80 : PLift (NumericBlock 80) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_81 : PLift (NumericBlock 81) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_82 : PLift (NumericBlock 82) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_83 : PLift (NumericBlock 83) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_84 : PLift (NumericBlock 84) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_85 : PLift (NumericBlock 85) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_86 : PLift (NumericBlock 86) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_87 : PLift (NumericBlock 87) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_88 : PLift (NumericBlock 88) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_89 : PLift (NumericBlock 89) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_90 : PLift (NumericBlock 90) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_91 : PLift (NumericBlock 91) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_92 : PLift (NumericBlock 92) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_93 : PLift (NumericBlock 93) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_94 : PLift (NumericBlock 94) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_95 : PLift (NumericBlock 95) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_96 : PLift (NumericBlock 96) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_97 : PLift (NumericBlock 97) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_98 : PLift (NumericBlock 98) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_99 : PLift (NumericBlock 99) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_100 : PLift (NumericBlock 100) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_101 : PLift (NumericBlock 101) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_102 : PLift (NumericBlock 102) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_103 : PLift (NumericBlock 103) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_104 : PLift (NumericBlock 104) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_105 : PLift (NumericBlock 105) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_106 : PLift (NumericBlock 106) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_107 : PLift (NumericBlock 107) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_108 : PLift (NumericBlock 108) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_109 : PLift (NumericBlock 109) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_110 : PLift (NumericBlock 110) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_111 : PLift (NumericBlock 111) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_112 : PLift (NumericBlock 112) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_113 : PLift (NumericBlock 113) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_114 : PLift (NumericBlock 114) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_115 : PLift (NumericBlock 115) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_116 : PLift (NumericBlock 116) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_117 : PLift (NumericBlock 117) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_118 : PLift (NumericBlock 118) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_119 : PLift (NumericBlock 119) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def numeric_blocks_120 : PLift (NumericBlock 120) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
theorem numeric_blocks : ∀ b : Fin 121, NumericBlock b.val := by
  intro b
  fin_cases b

  · exact numeric_blocks_0.down

  · exact numeric_blocks_1.down

  · exact numeric_blocks_2.down

  · exact numeric_blocks_3.down

  · exact numeric_blocks_4.down

  · exact numeric_blocks_5.down

  · exact numeric_blocks_6.down

  · exact numeric_blocks_7.down

  · exact numeric_blocks_8.down

  · exact numeric_blocks_9.down

  · exact numeric_blocks_10.down

  · exact numeric_blocks_11.down

  · exact numeric_blocks_12.down

  · exact numeric_blocks_13.down

  · exact numeric_blocks_14.down

  · exact numeric_blocks_15.down

  · exact numeric_blocks_16.down

  · exact numeric_blocks_17.down

  · exact numeric_blocks_18.down

  · exact numeric_blocks_19.down

  · exact numeric_blocks_20.down

  · exact numeric_blocks_21.down

  · exact numeric_blocks_22.down

  · exact numeric_blocks_23.down

  · exact numeric_blocks_24.down

  · exact numeric_blocks_25.down

  · exact numeric_blocks_26.down

  · exact numeric_blocks_27.down

  · exact numeric_blocks_28.down

  · exact numeric_blocks_29.down

  · exact numeric_blocks_30.down

  · exact numeric_blocks_31.down

  · exact numeric_blocks_32.down

  · exact numeric_blocks_33.down

  · exact numeric_blocks_34.down

  · exact numeric_blocks_35.down

  · exact numeric_blocks_36.down

  · exact numeric_blocks_37.down

  · exact numeric_blocks_38.down

  · exact numeric_blocks_39.down

  · exact numeric_blocks_40.down

  · exact numeric_blocks_41.down

  · exact numeric_blocks_42.down

  · exact numeric_blocks_43.down

  · exact numeric_blocks_44.down

  · exact numeric_blocks_45.down

  · exact numeric_blocks_46.down

  · exact numeric_blocks_47.down

  · exact numeric_blocks_48.down

  · exact numeric_blocks_49.down

  · exact numeric_blocks_50.down

  · exact numeric_blocks_51.down

  · exact numeric_blocks_52.down

  · exact numeric_blocks_53.down

  · exact numeric_blocks_54.down

  · exact numeric_blocks_55.down

  · exact numeric_blocks_56.down

  · exact numeric_blocks_57.down

  · exact numeric_blocks_58.down

  · exact numeric_blocks_59.down

  · exact numeric_blocks_60.down

  · exact numeric_blocks_61.down

  · exact numeric_blocks_62.down

  · exact numeric_blocks_63.down

  · exact numeric_blocks_64.down

  · exact numeric_blocks_65.down

  · exact numeric_blocks_66.down

  · exact numeric_blocks_67.down

  · exact numeric_blocks_68.down

  · exact numeric_blocks_69.down

  · exact numeric_blocks_70.down

  · exact numeric_blocks_71.down

  · exact numeric_blocks_72.down

  · exact numeric_blocks_73.down

  · exact numeric_blocks_74.down

  · exact numeric_blocks_75.down

  · exact numeric_blocks_76.down

  · exact numeric_blocks_77.down

  · exact numeric_blocks_78.down

  · exact numeric_blocks_79.down

  · exact numeric_blocks_80.down

  · exact numeric_blocks_81.down

  · exact numeric_blocks_82.down

  · exact numeric_blocks_83.down

  · exact numeric_blocks_84.down

  · exact numeric_blocks_85.down

  · exact numeric_blocks_86.down

  · exact numeric_blocks_87.down

  · exact numeric_blocks_88.down

  · exact numeric_blocks_89.down

  · exact numeric_blocks_90.down

  · exact numeric_blocks_91.down

  · exact numeric_blocks_92.down

  · exact numeric_blocks_93.down

  · exact numeric_blocks_94.down

  · exact numeric_blocks_95.down

  · exact numeric_blocks_96.down

  · exact numeric_blocks_97.down

  · exact numeric_blocks_98.down

  · exact numeric_blocks_99.down

  · exact numeric_blocks_100.down

  · exact numeric_blocks_101.down

  · exact numeric_blocks_102.down

  · exact numeric_blocks_103.down

  · exact numeric_blocks_104.down

  · exact numeric_blocks_105.down

  · exact numeric_blocks_106.down

  · exact numeric_blocks_107.down

  · exact numeric_blocks_108.down

  · exact numeric_blocks_109.down

  · exact numeric_blocks_110.down

  · exact numeric_blocks_111.down

  · exact numeric_blocks_112.down

  · exact numeric_blocks_113.down

  · exact numeric_blocks_114.down

  · exact numeric_blocks_115.down

  · exact numeric_blocks_116.down

  · exact numeric_blocks_117.down

  · exact numeric_blocks_118.down

  · exact numeric_blocks_119.down

  · exact numeric_blocks_120.down


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_0 : PLift (LocalBlock 0) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_1 : PLift (LocalBlock 1) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_2 : PLift (LocalBlock 2) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_3 : PLift (LocalBlock 3) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_4 : PLift (LocalBlock 4) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_5 : PLift (LocalBlock 5) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_6 : PLift (LocalBlock 6) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_7 : PLift (LocalBlock 7) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_8 : PLift (LocalBlock 8) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_9 : PLift (LocalBlock 9) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_10 : PLift (LocalBlock 10) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_11 : PLift (LocalBlock 11) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_12 : PLift (LocalBlock 12) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_13 : PLift (LocalBlock 13) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_14 : PLift (LocalBlock 14) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_15 : PLift (LocalBlock 15) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_16 : PLift (LocalBlock 16) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_17 : PLift (LocalBlock 17) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_18 : PLift (LocalBlock 18) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_19 : PLift (LocalBlock 19) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_20 : PLift (LocalBlock 20) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_21 : PLift (LocalBlock 21) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_22 : PLift (LocalBlock 22) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_23 : PLift (LocalBlock 23) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_24 : PLift (LocalBlock 24) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_25 : PLift (LocalBlock 25) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_26 : PLift (LocalBlock 26) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_27 : PLift (LocalBlock 27) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_28 : PLift (LocalBlock 28) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_29 : PLift (LocalBlock 29) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_30 : PLift (LocalBlock 30) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_31 : PLift (LocalBlock 31) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_32 : PLift (LocalBlock 32) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_33 : PLift (LocalBlock 33) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_34 : PLift (LocalBlock 34) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_35 : PLift (LocalBlock 35) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_36 : PLift (LocalBlock 36) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_37 : PLift (LocalBlock 37) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_38 : PLift (LocalBlock 38) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_39 : PLift (LocalBlock 39) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_40 : PLift (LocalBlock 40) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_41 : PLift (LocalBlock 41) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_42 : PLift (LocalBlock 42) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_43 : PLift (LocalBlock 43) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_44 : PLift (LocalBlock 44) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_45 : PLift (LocalBlock 45) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_46 : PLift (LocalBlock 46) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_47 : PLift (LocalBlock 47) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_48 : PLift (LocalBlock 48) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_49 : PLift (LocalBlock 49) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_50 : PLift (LocalBlock 50) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_51 : PLift (LocalBlock 51) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_52 : PLift (LocalBlock 52) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_53 : PLift (LocalBlock 53) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_54 : PLift (LocalBlock 54) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_55 : PLift (LocalBlock 55) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_56 : PLift (LocalBlock 56) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_57 : PLift (LocalBlock 57) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_58 : PLift (LocalBlock 58) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_59 : PLift (LocalBlock 59) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_60 : PLift (LocalBlock 60) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_61 : PLift (LocalBlock 61) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_62 : PLift (LocalBlock 62) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_63 : PLift (LocalBlock 63) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_64 : PLift (LocalBlock 64) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_65 : PLift (LocalBlock 65) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_66 : PLift (LocalBlock 66) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_67 : PLift (LocalBlock 67) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_68 : PLift (LocalBlock 68) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_69 : PLift (LocalBlock 69) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_70 : PLift (LocalBlock 70) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_71 : PLift (LocalBlock 71) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_72 : PLift (LocalBlock 72) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_73 : PLift (LocalBlock 73) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_74 : PLift (LocalBlock 74) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_75 : PLift (LocalBlock 75) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_76 : PLift (LocalBlock 76) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_77 : PLift (LocalBlock 77) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_78 : PLift (LocalBlock 78) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_79 : PLift (LocalBlock 79) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_80 : PLift (LocalBlock 80) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_81 : PLift (LocalBlock 81) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_82 : PLift (LocalBlock 82) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_83 : PLift (LocalBlock 83) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_84 : PLift (LocalBlock 84) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_85 : PLift (LocalBlock 85) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_86 : PLift (LocalBlock 86) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_87 : PLift (LocalBlock 87) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_88 : PLift (LocalBlock 88) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_89 : PLift (LocalBlock 89) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_90 : PLift (LocalBlock 90) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_91 : PLift (LocalBlock 91) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_92 : PLift (LocalBlock 92) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_93 : PLift (LocalBlock 93) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_94 : PLift (LocalBlock 94) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_95 : PLift (LocalBlock 95) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_96 : PLift (LocalBlock 96) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_97 : PLift (LocalBlock 97) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_98 : PLift (LocalBlock 98) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_99 : PLift (LocalBlock 99) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_100 : PLift (LocalBlock 100) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_101 : PLift (LocalBlock 101) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_102 : PLift (LocalBlock 102) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_103 : PLift (LocalBlock 103) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_104 : PLift (LocalBlock 104) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_105 : PLift (LocalBlock 105) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_106 : PLift (LocalBlock 106) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_107 : PLift (LocalBlock 107) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_108 : PLift (LocalBlock 108) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_109 : PLift (LocalBlock 109) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_110 : PLift (LocalBlock 110) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_111 : PLift (LocalBlock 111) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_112 : PLift (LocalBlock 112) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_113 : PLift (LocalBlock 113) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_114 : PLift (LocalBlock 114) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_115 : PLift (LocalBlock 115) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_116 : PLift (LocalBlock 116) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_117 : PLift (LocalBlock 117) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_118 : PLift (LocalBlock 118) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_119 : PLift (LocalBlock 119) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def local_blocks_120 : PLift (LocalBlock 120) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
theorem local_blocks : ∀ b : Fin 121, LocalBlock b.val := by
  intro b
  fin_cases b

  · exact local_blocks_0.down

  · exact local_blocks_1.down

  · exact local_blocks_2.down

  · exact local_blocks_3.down

  · exact local_blocks_4.down

  · exact local_blocks_5.down

  · exact local_blocks_6.down

  · exact local_blocks_7.down

  · exact local_blocks_8.down

  · exact local_blocks_9.down

  · exact local_blocks_10.down

  · exact local_blocks_11.down

  · exact local_blocks_12.down

  · exact local_blocks_13.down

  · exact local_blocks_14.down

  · exact local_blocks_15.down

  · exact local_blocks_16.down

  · exact local_blocks_17.down

  · exact local_blocks_18.down

  · exact local_blocks_19.down

  · exact local_blocks_20.down

  · exact local_blocks_21.down

  · exact local_blocks_22.down

  · exact local_blocks_23.down

  · exact local_blocks_24.down

  · exact local_blocks_25.down

  · exact local_blocks_26.down

  · exact local_blocks_27.down

  · exact local_blocks_28.down

  · exact local_blocks_29.down

  · exact local_blocks_30.down

  · exact local_blocks_31.down

  · exact local_blocks_32.down

  · exact local_blocks_33.down

  · exact local_blocks_34.down

  · exact local_blocks_35.down

  · exact local_blocks_36.down

  · exact local_blocks_37.down

  · exact local_blocks_38.down

  · exact local_blocks_39.down

  · exact local_blocks_40.down

  · exact local_blocks_41.down

  · exact local_blocks_42.down

  · exact local_blocks_43.down

  · exact local_blocks_44.down

  · exact local_blocks_45.down

  · exact local_blocks_46.down

  · exact local_blocks_47.down

  · exact local_blocks_48.down

  · exact local_blocks_49.down

  · exact local_blocks_50.down

  · exact local_blocks_51.down

  · exact local_blocks_52.down

  · exact local_blocks_53.down

  · exact local_blocks_54.down

  · exact local_blocks_55.down

  · exact local_blocks_56.down

  · exact local_blocks_57.down

  · exact local_blocks_58.down

  · exact local_blocks_59.down

  · exact local_blocks_60.down

  · exact local_blocks_61.down

  · exact local_blocks_62.down

  · exact local_blocks_63.down

  · exact local_blocks_64.down

  · exact local_blocks_65.down

  · exact local_blocks_66.down

  · exact local_blocks_67.down

  · exact local_blocks_68.down

  · exact local_blocks_69.down

  · exact local_blocks_70.down

  · exact local_blocks_71.down

  · exact local_blocks_72.down

  · exact local_blocks_73.down

  · exact local_blocks_74.down

  · exact local_blocks_75.down

  · exact local_blocks_76.down

  · exact local_blocks_77.down

  · exact local_blocks_78.down

  · exact local_blocks_79.down

  · exact local_blocks_80.down

  · exact local_blocks_81.down

  · exact local_blocks_82.down

  · exact local_blocks_83.down

  · exact local_blocks_84.down

  · exact local_blocks_85.down

  · exact local_blocks_86.down

  · exact local_blocks_87.down

  · exact local_blocks_88.down

  · exact local_blocks_89.down

  · exact local_blocks_90.down

  · exact local_blocks_91.down

  · exact local_blocks_92.down

  · exact local_blocks_93.down

  · exact local_blocks_94.down

  · exact local_blocks_95.down

  · exact local_blocks_96.down

  · exact local_blocks_97.down

  · exact local_blocks_98.down

  · exact local_blocks_99.down

  · exact local_blocks_100.down

  · exact local_blocks_101.down

  · exact local_blocks_102.down

  · exact local_blocks_103.down

  · exact local_blocks_104.down

  · exact local_blocks_105.down

  · exact local_blocks_106.down

  · exact local_blocks_107.down

  · exact local_blocks_108.down

  · exact local_blocks_109.down

  · exact local_blocks_110.down

  · exact local_blocks_111.down

  · exact local_blocks_112.down

  · exact local_blocks_113.down

  · exact local_blocks_114.down

  · exact local_blocks_115.down

  · exact local_blocks_116.down

  · exact local_blocks_117.down

  · exact local_blocks_118.down

  · exact local_blocks_119.down

  · exact local_blocks_120.down


theorem covered (P : Fin 963 → Prop)
    (h : ∀ b : Fin 121, ∀ j : Fin 8, P (tableIndex (8 * b.val + j.val))) :
    ∀ i, P i := by
  intro i
  let b : Fin 121 := ⟨i.val / 8, by omega⟩
  let j : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : tableIndex (8 * b.val + j.val) = i := by
    apply Fin.ext
    simp only [tableIndex, b, j]
    omega
  simpa only [he] using h b j

theorem local_table (i : Fin 963) :
    allCols.filterMap (step (state i)) = (succ i).map state :=
  covered LocalCheck local_blocks i

theorem numeric_table (i : Fin 963) : NumericCheck i :=
  covered NumericCheck numeric_blocks i

theorem state_zero : state 0 = start := by decide +kernel

theorem paths_vectors (k : Fin 11) (i : Fin 963) :
    paths succ accepted k.val i = v k i :=
  paths_eq_vectors succ accepted v (fun s => (numeric_table s).1)
    (fun k s => (numeric_table s).2.1 k) k i

theorem recurrence_base (s : Fin 963) :
    paths succ accepted 10 s + 15 * paths succ accepted 8 s + 15 * paths succ accepted 6 s +
      paths succ accepted 4 s =
      6 * paths succ accepted 9 s + 20 * paths succ accepted 7 s + 6 * paths succ accepted 5 s := by
  have hv (n : Fin 11) := paths_vectors n s
  change paths succ accepted (10 : Fin 11).val s + 15 * paths succ accepted (8 : Fin 11).val s +
      15 * paths succ accepted (6 : Fin 11).val s + paths succ accepted (4 : Fin 11).val s =
      6 * paths succ accepted (9 : Fin 11).val s + 20 * paths succ accepted (7 : Fin 11).val s +
      6 * paths succ accepted (5 : Fin 11).val s
  simp only [hv]
  exact (numeric_table s).2.2
end A224041Certificate

namespace A224041Table
open A224041Count A224041Certificate

def indexedCount (n : ℕ) : ℕ := paths succ accepted n 0

theorem indexed_vector (k : Fin 11) : indexedCount k.val = v k 0 := paths_vectors k 0

theorem initial_1 : indexedCount 1 = 32 := by
  have h := indexed_vector (1 : Fin 11)
  have hv : v 1 0 = 32 := by decide +kernel
  exact h.trans hv

theorem initial_2 : indexedCount 2 = 144 := by
  have h := indexed_vector (2 : Fin 11)
  have hv : v 2 0 = 144 := by decide +kernel
  exact h.trans hv

theorem initial_3 : indexedCount 3 = 298 := by
  have h := indexed_vector (3 : Fin 11)
  have hv : v 3 0 = 298 := by decide +kernel
  exact h.trans hv

theorem initial_4 : indexedCount 4 = 488 := by
  have h := indexed_vector (4 : Fin 11)
  have hv : v 4 0 = 488 := by decide +kernel
  exact h.trans hv

theorem initial_5 : indexedCount 5 = 734 := by
  have h := indexed_vector (5 : Fin 11)
  have hv : v 5 0 = 734 := by decide +kernel
  exact h.trans hv

theorem initial_6 : indexedCount 6 = 1064 := by
  have h := indexed_vector (6 : Fin 11)
  have hv : v 6 0 = 1064 := by decide +kernel
  exact h.trans hv

theorem initial_7 : indexedCount 7 = 1505 := by
  have h := indexed_vector (7 : Fin 11)
  have hv : v 7 0 = 1505 := by decide +kernel
  exact h.trans hv

theorem initial_8 : indexedCount 8 = 2091 := by
  have h := indexed_vector (8 : Fin 11)
  have hv : v 8 0 = 2091 := by decide +kernel
  exact h.trans hv

theorem initial_9 : indexedCount 9 = 2864 := by
  have h := indexed_vector (9 : Fin 11)
  have hv : v 9 0 = 2864 := by decide +kernel
  exact h.trans hv

theorem initial_10 : indexedCount 10 = 3875 := by
  have h := indexed_vector (10 : Fin 11)
  have hv : v 10 0 = 3875 := by decide +kernel
  exact h.trans hv

theorem indexed_recurrence (n : ℕ) :
    indexedCount (n + 10) + 15 * indexedCount (n + 8) + 15 * indexedCount (n + 6) + indexedCount (n + 4) =
      6 * indexedCount (n + 9) + 20 * indexedCount (n + 7) + 6 * indexedCount (n + 5) :=
  paths_recurrence succ accepted recurrence_base n 0
end A224041Table

namespace A224041Formula
open PowerSeries

noncomputable def closed (n : ℕ) : ℚ :=
  1 / 120 * n ^ 5 + 1 / 24 * n ^ 4 + 25 / 24 * n ^ 3 +
    227 / 24 * n ^ 2 + 1289 / 20 * n - 7

private theorem closed_recurrence (n : ℕ) :
    closed (n + 10) + 15 * closed (n + 8) + 15 * closed (n + 6) + closed (n + 4) =
      6 * closed (n + 9) + 20 * closed (n + 7) + 6 * closed (n + 5) := by
  simp only [closed, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem closed_formula (a : ℕ → ℕ)
    (h4 : a 4 = 488) (h5 : a 5 = 734) (h6 : a 6 = 1064)
    (h7 : a 7 = 1505) (h8 : a 8 = 2091) (h9 : a 9 = 2864)
    (hs : ∀ n, a (n + 10) + 15 * a (n + 8) + 15 * a (n + 6) + a (n + 4) =
      6 * a (n + 9) + 20 * a (n + 7) + 6 * a (n + 5))
    (n : ℕ) (hn : 3 < n) : (a n : ℚ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn9 : n ≤ 9
    · have hn4 : 4 ≤ n := by omega
      interval_cases n <;> norm_num [h4, h5, h6, h7, h8, h9, closed]
    · let m := n - 10
      have heq : n = m + 10 := by dsimp [m]; omega
      have hi (k : ℕ) (hk4 : 4 ≤ k) (hk : k < 10) :
          (a (m + k) : ℚ) = closed (m + k) :=
        ih (m + k) (by dsimp [m]; omega) (by omega)
      have hq : (a (m + 10) : ℚ) + 15 * a (m + 8) + 15 * a (m + 6) + a (m + 4) =
          6 * a (m + 9) + 20 * a (m + 7) + 6 * a (m + 5) := by exact_mod_cast hs m
      rw [hi 8 (by decide) (by decide), hi 6 (by decide) (by decide),
        hi 4 (by decide) (by decide), hi 9 (by decide) (by decide),
        hi 7 (by decide) (by decide), hi 5 (by decide) (by decide)] at hq
      rw [heq]
      linarith [closed_recurrence m]

theorem integer_recurrence (a : ℕ → ℕ)
    (hs : ∀ n, a (n + 10) + 15 * a (n + 8) + 15 * a (n + 6) + a (n + 4) =
      6 * a (n + 9) + 20 * a (n + 7) + 6 * a (n + 5))
    (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  have h := hs (n - 10)
  have heq (k : ℕ) (hk : k ≤ 10) : n - 10 + k = n - (10 - k) := by omega
  rw [heq 10 (by decide), heq 8 (by decide), heq 6 (by decide),
    heq 4 (by decide), heq 9 (by decide), heq 7 (by decide), heq 5 (by decide)] at h
  norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at h
  have hz : (a n : ℤ) + 15 * a (n - 2) + 15 * a (n - 4) + a (n - 6) =
      6 * a (n - 1) + 20 * a (n - 3) + 6 * a (n - 5) := by exact_mod_cast h
  linarith

theorem generating_function (a : ℕ → ℕ)
    (h1 : a 1 = 32) (h2 : a 2 = 144) (h3 : a 3 = 298)
    (h4 : a 4 = 488) (h5 : a 5 = 734) (h6 : a 6 = 1064)
    (h7 : a 7 = 1505) (h8 : a 8 = 2091) (h9 : a 9 = 2864)
    (hs : ∀ n, a (n + 10) + 15 * a (n + 8) + 15 * a (n + 6) + a (n + 4) =
      6 * a (n + 9) + 20 * a (n + 7) + 6 * a (n + 5)) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 - 124 * X ^ 4 -
        12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8) := by
  let g : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)
  change g * (1 - X) ^ 6 = _
  have hl : g * (1 - X) ^ 6 =
      g * X ^ 0 - 6 • (g * X ^ 1) + 15 • (g * X ^ 2) -
      20 • (g * X ^ 3) + 15 • (g * X ^ 4) - 6 • (g * X ^ 5) + g * X ^ 6 := by
    simp only [nsmul_eq_mul]
    ring
  have hr : ((X : PowerSeries ℚ) * (32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 -
      124 * X ^ 4 - 12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8)) =
      32 • X ^ 1 - 48 • X ^ 2 - 86 • X ^ 3 + 220 • X ^ 4 -
        124 • X ^ 5 - 12 • X ^ 6 + 9 • X ^ 7 + 17 • X ^ 8 - 7 • X ^ 9 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_nsmul]
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk,
        h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · have hc (k : ℕ) (hk : k < n) : coeff n (g * X ^ k) = (a (n - k) : ℚ) := by
      rw [coeff_mul_X_pow', if_pos (by omega)]
      simp only [g, coeff_mk, if_neg (by omega : n - k ≠ 0)]
    have hx (k : ℕ) (hk : k < n) : coeff n (X ^ k : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    simp (disch := omega) only [hc, hx, nsmul_eq_mul, mul_zero, add_zero,
      sub_zero, Nat.sub_zero]
    norm_num only [Nat.cast_ofNat]
    have hrec := hs (n - 10)
    have heq (k : ℕ) (hk : k ≤ 10) : n - 10 + k = n - (10 - k) := by omega
    rw [heq 10 (by omega), heq 8 (by omega), heq 6 (by omega),
      heq 4 (by omega), heq 9 (by omega), heq 7 (by omega), heq 5 (by omega)] at hrec
    norm_num only [Nat.sub_self, Nat.sub_zero, Nat.reduceSub] at hrec
    have hq : (a n : ℚ) + 15 * a (n - 2) + 15 * a (n - 4) + a (n - 6) =
      6 * a (n - 1) + 20 * a (n - 3) + 6 * a (n - 5) := by exact_mod_cast hrec
    linarith

theorem of_recurrence (a : ℕ → ℕ)
    (h1 : a 1 = 32) (h2 : a 2 = 144) (h3 : a 3 = 298)
    (h4 : a 4 = 488) (h5 : a 5 = 734) (h6 : a 6 = 1064)
    (h7 : a 7 = 1505) (h8 : a 8 = 2091) (h9 : a 9 = 2864)
    (hs : ∀ n, a (n + 10) + 15 * a (n + 8) + 15 * a (n + 6) + a (n + 4) =
      6 * a (n + 9) + 20 * a (n + 7) + 6 * a (n + 5)) :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = 1 / 120 * n ^ 5 + 1 / 24 * n ^ 4 +
      25 / 24 * n ^ 3 + 227 / 24 * n ^ 2 + 1289 / 20 * n - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 - 124 * X ^ 4 -
        12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) +
      20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  exact ⟨closed_formula a h4 h5 h6 h7 h8 h9 hs,
    generating_function a h1 h2 h3 h4 h5 h6 h7 h8 h9 hs, integer_recurrence a hs⟩

end A224041Formula

namespace A224041Proof
open OMA.S_oeis_a224041 A224041Table A224041Certificate PowerSeries

theorem a_eq_indexed (n : ℕ) : a n = indexedCount n :=
  a_eq_paths run_correct state succ accepted 0 local_table (fun _ => rfl) state_zero n

theorem result :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = 1 / 120 * n ^ 5 + 1 / 24 * n ^ 4 +
      25 / 24 * n ^ 3 + 227 / 24 * n ^ 2 + 1289 / 20 * n - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 - 124 * X ^ 4 -
        12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) +
      20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  have ha : a = indexedCount := funext a_eq_indexed
  rw [ha]
  exact A224041Formula.of_recurrence indexedCount initial_1 initial_2 initial_3
    initial_4 initial_5 initial_6 initial_7 initial_8 initial_9 indexed_recurrence

end A224041Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a224041.main := by
  exact A224041Proof.result
