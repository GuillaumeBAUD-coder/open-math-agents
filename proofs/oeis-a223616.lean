import OMAStatements.S_oeis_a223616
import Mathlib

/-!
# oeis-a223616: counting the n X 4 arrays with unimodal rows and columns

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns. The number g(c, n) of ways to append n rows from column states c then
satisfies a linear recursion over the next row, and its explicit polynomial closed forms are checked
by induction over the 81 state vectors. The value at the initial state is a polynomial of degree
8, and the generating function and the recurrence follow from it.

Source: OEIS A223616, https://oeis.org/A223616.
-/
namespace OMA.P_oeis_a223616

open OMA.S_oeis_a223616

/-! ### Unimodal 0..1 sequences -/

def Z (l : List ℕ) : Prop := ∀ y ∈ l, y = 0
def D (l : List ℕ) : Prop := l.Pairwise (· ≥ ·)

lemma pw_const {l : List ℕ} {c : ℕ} (R : ℕ → ℕ → Prop) (hR : R c c) (h : ∀ y ∈ l, y = c) :
    l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩
    rw [h x (List.mem_cons_self), h y (List.mem_cons_of_mem _ hy)]; exact hR

lemma Z_D {l : List ℕ} (h : Z l) : D l := pw_const _ (le_refl 0) h

lemma U_nil : Unimodal [] := ⟨0, by simp, by simp⟩

lemma U_cons0 (l : List ℕ) : Unimodal (0 :: l) ↔ Unimodal l := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero] at h2
      exact ⟨0, by simp, by simpa only [List.drop_zero] using (List.pairwise_cons.mp h2).2⟩
    | succ m =>
      simp only [List.take_succ_cons, List.drop_succ_cons] at h1 h2
      exact ⟨m, (List.pairwise_cons.mp h1).2, h2⟩
  · rintro ⟨m, h1, h2⟩
    refine ⟨m + 1, ?_, by simpa only [List.drop_succ_cons] using h2⟩
    simp only [List.take_succ_cons]
    exact List.pairwise_cons.mpr ⟨fun y _ => Nat.zero_le y, h1⟩

lemma U_cons1 (l : List ℕ) (hl : ∀ y ∈ l, y ≤ 1) : Unimodal (1 :: l) ↔ D l := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero] at h2
      exact (List.pairwise_cons.mp h2).2
    | succ m =>
      simp only [List.take_succ_cons, List.drop_succ_cons] at h1 h2
      have hA : ∀ y ∈ l.take m, y = 1 := fun y hy =>
        le_antisymm (hl y (List.mem_of_mem_take hy)) ((List.pairwise_cons.mp h1).1 y hy)
      unfold D
      rw [← List.take_append_drop m l, List.pairwise_append]
      refine ⟨pw_const _ (le_refl 1) hA, h2, fun x hx y hy => ?_⟩
      rw [hA x hx]; exact hl y (List.mem_of_mem_drop hy)
  · intro h
    refine ⟨1, by simp, ?_⟩
    simp only [List.drop_succ_cons, List.drop_zero]
    exact h

lemma D_cons1 (l : List ℕ) (hl : ∀ y ∈ l, y ≤ 1) : D (1 :: l) ↔ D l := by
  unfold D; rw [List.pairwise_cons]
  exact ⟨fun h => h.2, fun h => ⟨fun y hy => hl y hy, h⟩⟩

lemma D_cons0 (l : List ℕ) : D (0 :: l) ↔ Z l := by
  unfold D; rw [List.pairwise_cons]
  exact ⟨fun h y hy => Nat.le_zero.mp (h.1 y hy), fun h => ⟨fun y hy => (h y hy).le, Z_D h⟩⟩

lemma Z_cons0 (l : List ℕ) : Z (0 :: l) ↔ Z l := by simp [Z]

lemma Z_cons1 (l : List ℕ) : ¬ Z (1 :: l) := by simp [Z]

/-- The automaton: state, transition and acceptance. -/
def St (s : Fin 3) (l : List ℕ) : Prop := if s = 0 then Unimodal l else if s = 1 then D l else Z l

def dl : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![2, 1], ![2, 2]]

def okb : Fin 3 → Fin 2 → Bool := ![![true, true], ![true, true], ![true, false]]

lemma dl00 : dl 0 0 = 0 := rfl
lemma dl01 : dl 0 1 = 1 := rfl
lemma dl10 : dl 1 0 = 2 := rfl
lemma dl11 : dl 1 1 = 1 := rfl
lemma dl20 : dl 2 0 = 2 := rfl
lemma dl21 : dl 2 1 = 2 := rfl

def Acc : Fin 3 → List (Fin 2) → Bool
  | _, [] => true
  | s, b :: L => okb s b && Acc (dl s b) L

lemma bin (L : List (Fin 2)) : ∀ y ∈ L.map (fun x : Fin 2 => (x : ℕ)), y ≤ 1 := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact Nat.lt_succ_iff.mp x.isLt

lemma accSt (s : Fin 3) (L : List (Fin 2)) : St s (L.map (fun x : Fin 2 => (x : ℕ))) ↔ Acc s L = true := by
  induction L generalizing s with
  | nil => fin_cases s <;> simp [St, Acc, U_nil, D, Z]
  | cons b L ih =>
    rw [List.map_cons, Acc, Bool.and_eq_true, ← ih]
    have hl := bin L
    fin_cases s <;> fin_cases b <;>
      simp [St, dl, okb, U_cons0, U_cons1 _ hl, D_cons0, D_cons1 _ hl, Z_cons0, Z_cons1]

lemma uniAcc (L : List (Fin 2)) : Unimodal (L.map (fun x : Fin 2 => (x : ℕ))) ↔ Acc 0 L = true := by
  rw [← accSt]; simp [St]

/-! ### Arrays as lists of rows -/

abbrev R := Fin 4 → Fin 2

lemma sumk (g : R → ℚ) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, g ![y0, y1, y2, y3] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2], fun f => (f 0, f 1, f 2, f 3), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The condition on the first row from column states `c`. -/
def okT (c : Fin 4 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ ∀ j, okb (c j) (r j) = true

instance (c : Fin 4 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 4 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ ∀ j, Acc (c j) (l.map (· j)) = true

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 4) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q
  simp only [rowUni, colUni]

lemma Q_nil (c : Fin 4 → Fin 3) : Q c [] := by simp [Q, Acc]

lemma Q_cons (c : Fin 4 → Fin 3) (r : R) (l : List R) :
    Q c (r :: l) ↔ okT c r ∧ Q (fun j => dl (c j) (r j)) l := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Acc, Bool.and_eq_true, forall_and]
  tauto

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih =>
    cases l with
    | nil => simp [LL]
    | cons x m => simp [LL, ih]

lemma card_cons (n : ℕ) (P : List R → Prop) [DecidablePred P] :
    ((LL (n + 1)).filter P).card = ∑ s : R, ((LL n).filter (fun m => P (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h; simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2)]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

noncomputable def g (c : Fin 4 → Fin 3) (n : ℕ) : ℕ := ((LL n).filter (Q c)).card

lemma a_eq (n : ℕ) : a n = g (fun _ => 0) n := by
  have e : {l : List R // l.length = n ∧ IsSolution l} ≃ {l // l ∈ (LL n).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

lemma g_zero (c : Fin 4 → Fin 3) : g c 0 = 1 := by
  unfold g; simp only [LL]; rw [Finset.filter_singleton, if_pos (Q_nil c)]; rfl

lemma g_succ (c : Fin 4 → Fin 3) (n : ℕ) :
    g c (n + 1) = ∑ r : R, if okT c r then g ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3)] n else 0 := by
  unfold g
  rw [card_cons]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hv : (fun j => dl (c j) (r j)) = ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3)] := by ext j; fin_cases j <;> rfl
  simp only [Q_cons, ← hv]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def G : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ → ℚ :=
  ![![![![(fun n : ℕ => ((1 : ℚ) / 112) * (n : ℚ) ^ 8 + ((79 : ℚ) / 1260) * (n : ℚ) ^ 7 + ((59 : ℚ) / 180) * (n : ℚ) ^ 6 + ((299 : ℚ) / 360) * (n : ℚ) ^ 5 + ((259 : ℚ) / 144) * (n : ℚ) ^ 4 + ((821 : ℚ) / 360) * (n : ℚ) ^ 3 + ((7219 : ℚ) / 2520) * (n : ℚ) ^ 2 + ((767 : ℚ) / 420) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 60) * (n : ℚ) ^ 7 + ((2 : ℚ) / 15) * (n : ℚ) ^ 6 + ((37 : ℚ) / 60) * (n : ℚ) ^ 5 + ((37 : ℚ) / 24) * (n : ℚ) ^ 4 + ((53 : ℚ) / 20) * (n : ℚ) ^ 3 + ((113 : ℚ) / 40) * (n : ℚ) ^ 2 + ((133 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((23 : ℚ) / 360) * (n : ℚ) ^ 6 + ((31 : ℚ) / 120) * (n : ℚ) ^ 5 + ((8 : ℚ) / 9) * (n : ℚ) ^ 4 + ((31 : ℚ) / 24) * (n : ℚ) ^ 3 + ((737 : ℚ) / 360) * (n : ℚ) ^ 2 + ((29 : ℚ) / 20) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((2 : ℚ) / 105) * (n : ℚ) ^ 7 + ((23 : ℚ) / 180) * (n : ℚ) ^ 6 + ((3 : ℚ) / 5) * (n : ℚ) ^ 5 + ((13 : ℚ) / 9) * (n : ℚ) ^ 4 + ((13 : ℚ) / 5) * (n : ℚ) ^ 3 + ((527 : ℚ) / 180) * (n : ℚ) ^ 2 + ((479 : ℚ) / 210) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((19 : ℚ) / 360) * (n : ℚ) ^ 6 + ((43 : ℚ) / 120) * (n : ℚ) ^ 5 + ((95 : ℚ) / 72) * (n : ℚ) ^ 4 + ((61 : ℚ) / 24) * (n : ℚ) ^ 3 + ((563 : ℚ) / 180) * (n : ℚ) ^ 2 + ((13 : ℚ) / 5) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((113 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((7 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 120) * (n : ℚ) ^ 5 + ((29 : ℚ) / 72) * (n : ℚ) ^ 4 + ((17 : ℚ) / 24) * (n : ℚ) ^ 3 + ((71 : ℚ) / 45) * (n : ℚ) ^ 2 + ((37 : ℚ) / 30) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 20) * (n : ℚ) ^ 5 + ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((5 : ℚ) / 4) * (n : ℚ) ^ 2 + ((17 : ℚ) / 10) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 4) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((2 : ℚ) / 105) * (n : ℚ) ^ 7 + ((23 : ℚ) / 180) * (n : ℚ) ^ 6 + ((3 : ℚ) / 5) * (n : ℚ) ^ 5 + ((13 : ℚ) / 9) * (n : ℚ) ^ 4 + ((13 : ℚ) / 5) * (n : ℚ) ^ 3 + ((527 : ℚ) / 180) * (n : ℚ) ^ 2 + ((479 : ℚ) / 210) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + (3 : ℚ) * (n : ℚ) ^ 3 + (3 : ℚ) * (n : ℚ) ^ 2 + ((8 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + ((1 : ℚ) / 2) * (n : ℚ) ^ 4 + ((17 : ℚ) / 12) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((29 : ℚ) / 15) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((11 : ℚ) / 180) * (n : ℚ) ^ 6 + ((1 : ℚ) / 3) * (n : ℚ) ^ 5 + ((43 : ℚ) / 36) * (n : ℚ) ^ 4 + ((5 : ℚ) / 2) * (n : ℚ) ^ 3 + ((146 : ℚ) / 45) * (n : ℚ) ^ 2 + ((8 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + ((7 : ℚ) / 8) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((29 : ℚ) / 8) * (n : ℚ) ^ 2 + ((181 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 6) * (n : ℚ) ^ 3 + ((13 : ℚ) / 6) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 30) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((11 : ℚ) / 8) * (n : ℚ) ^ 2 + ((103 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((7 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 120) * (n : ℚ) ^ 5 + ((29 : ℚ) / 72) * (n : ℚ) ^ 4 + ((17 : ℚ) / 24) * (n : ℚ) ^ 3 + ((71 : ℚ) / 45) * (n : ℚ) ^ 2 + ((37 : ℚ) / 30) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 30) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((11 : ℚ) / 8) * (n : ℚ) ^ 2 + ((103 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((11 : ℚ) / 12) * (n : ℚ) ^ 2 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 30) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((11 : ℚ) / 8) * (n : ℚ) ^ 2 + ((103 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((11 : ℚ) / 12) * (n : ℚ) ^ 2 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]]], ![![![(fun n : ℕ => ((1 : ℚ) / 60) * (n : ℚ) ^ 7 + ((2 : ℚ) / 15) * (n : ℚ) ^ 6 + ((37 : ℚ) / 60) * (n : ℚ) ^ 5 + ((37 : ℚ) / 24) * (n : ℚ) ^ 4 + ((53 : ℚ) / 20) * (n : ℚ) ^ 3 + ((113 : ℚ) / 40) * (n : ℚ) ^ 2 + ((133 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((7 : ℚ) / 30) * (n : ℚ) ^ 5 + ((7 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((17 : ℚ) / 6) * (n : ℚ) ^ 2 + ((13 : ℚ) / 5) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((113 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + (3 : ℚ) * (n : ℚ) ^ 3 + (3 : ℚ) * (n : ℚ) ^ 2 + ((8 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 4 + (3 : ℚ) * (n : ℚ) ^ 3 + ((10 : ℚ) / 3) * (n : ℚ) ^ 2 + (3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((5 : ℚ) / 3) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 30) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((11 : ℚ) / 8) * (n : ℚ) ^ 2 + ((103 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((19 : ℚ) / 360) * (n : ℚ) ^ 6 + ((43 : ℚ) / 120) * (n : ℚ) ^ 5 + ((95 : ℚ) / 72) * (n : ℚ) ^ 4 + ((61 : ℚ) / 24) * (n : ℚ) ^ 3 + ((563 : ℚ) / 180) * (n : ℚ) ^ 2 + ((13 : ℚ) / 5) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 4 + (3 : ℚ) * (n : ℚ) ^ 3 + ((10 : ℚ) / 3) * (n : ℚ) ^ 2 + (3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 6) * (n : ℚ) ^ 3 + ((13 : ℚ) / 6) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + ((7 : ℚ) / 8) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((29 : ℚ) / 8) * (n : ℚ) ^ 2 + ((181 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((25 : ℚ) / 6) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 2 + (3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((1 : ℚ) / 20) * (n : ℚ) ^ 5 + ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((5 : ℚ) / 4) * (n : ℚ) ^ 2 + ((17 : ℚ) / 10) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 2 + (3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]]], ![![![(fun n : ℕ => ((23 : ℚ) / 360) * (n : ℚ) ^ 6 + ((31 : ℚ) / 120) * (n : ℚ) ^ 5 + ((8 : ℚ) / 9) * (n : ℚ) ^ 4 + ((31 : ℚ) / 24) * (n : ℚ) ^ 3 + ((737 : ℚ) / 360) * (n : ℚ) ^ 2 + ((29 : ℚ) / 20) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((113 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 4) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + ((1 : ℚ) / 2) * (n : ℚ) ^ 4 + ((17 : ℚ) / 12) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((29 : ℚ) / 15) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 6) * (n : ℚ) ^ 3 + ((13 : ℚ) / 6) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((11 : ℚ) / 12) * (n : ℚ) ^ 2 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((113 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((5 : ℚ) / 3) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 6) * (n : ℚ) ^ 3 + ((13 : ℚ) / 6) * (n : ℚ) ^ 2 + ((7 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)]], ![![(fun n : ℕ => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 4) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0)], ![(fun n : ℕ => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0), (fun n : ℕ => (1 : ℚ) * (n : ℚ) ^ 0)]]]]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem g_closed (n : ℕ) : ∀ (c0 c1 c2 c3 : Fin 3), (g ![c0, c1, c2, c3] n : ℚ) = G c0 c1 c2 c3 n := by
  induction n with
  | zero =>
    intro c0 c1 c2 c3; rw [g_zero]
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> simp [G]
  | succ n ih =>
    intro c0 c1 c2 c3; rw [g_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;>
      simp +decide only [okT, if_true, if_false, add_zero, zero_add] <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
        Fin.isValue, dl00, dl01, dl10, dl11, dl20, dl21, ih] <;>
      simp [G, dl] <;> ring

lemma av (n : ℕ) : (a n : ℚ) = ((1 : ℚ) / 112) * (n : ℚ) ^ 8 + ((79 : ℚ) / 1260) * (n : ℚ) ^ 7 + ((59 : ℚ) / 180) * (n : ℚ) ^ 6 + ((299 : ℚ) / 360) * (n : ℚ) ^ 5 + ((259 : ℚ) / 144) * (n : ℚ) ^ 4 + ((821 : ℚ) / 360) * (n : ℚ) ^ 3 + ((7219 : ℚ) / 2520) * (n : ℚ) ^ 2 + ((767 : ℚ) / 420) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0 := by
  rw [a_eq]
  have h := g_closed n 0 0 0 0
  rw [show (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] by ext j; fin_cases j <;> rfl, h]
  simp [G]

open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 + 22 * X ^ 1 + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 - 8 * X ^ 7 + X ^ 8) ∧
    (∀ n > 9, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) + C (9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 8) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 9) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (11 + 22 * X ^ 1 + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 - 8 * X ^ 7 + X ^ 8 : PowerSeries ℚ) =
        C (11 : ℚ) * X ^ 0 + C (22 : ℚ) * X ^ 1 + C (183 : ℚ) * X ^ 2 + C (14 : ℚ) * X ^ 3 + C (158 : ℚ) * X ^ 4 + C (-56 : ℚ) * X ^ 5 + C (35 : ℚ) * X ^ 6 + C (-8 : ℚ) * X ^ 7 + C (1 : ℚ) * X ^ 8 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge c 9 with h | h
    · interval_cases c <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 9 := ⟨c - 9, by omega⟩
      simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m + 0 by omega, show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega, show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega, show 8 ≤ m + 9 by omega, show 9 ≤ m + 9 by omega, if_true, show m + 9 ≠ 0 by omega, show m + 9 ≠ 1 by omega, show m + 9 ≠ 2 by omega, show m + 9 ≠ 3 by omega, show m + 9 ≠ 4 by omega, show m + 9 ≠ 5 by omega, show m + 9 ≠ 6 by omega, show m + 9 ≠ 7 by omega, show m + 9 ≠ 8 by omega, if_false]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, false_and, ↓reduceIte, add_zero]
      simp only [av]; push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega]
    qify
    simp only [av]; push_cast; ring

end OMA.P_oeis_a223616

theorem OMA.solution : type_of% @OMA.S_oeis_a223616.main := OMA.P_oeis_a223616.full
