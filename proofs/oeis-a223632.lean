import OMAStatements.S_oeis_a223632
import Mathlib

/-!
# oeis-a223632: counting the n X 3 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 3 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 1 it is an explicit polynomial, checked by induction over the
124 states (c, r) whose top row is allowed, from exact values at n = 1..1. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223632, https://oeis.org/A223632.
-/
namespace OMA.P_oeis_a223632

open OMA.S_oeis_a223632

def adj (r s : Fin 3 → Fin 2) : Prop := True

instance (r s : Fin 3 → Fin 2) : Decidable (adj r s) := by unfold adj; infer_instance

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

abbrev R := Fin 3 → Fin 2

lemma sumk {M : Type*} [AddCommMonoid M] (g : R → M) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, g ![y0, y1, y2] := by
  let e : Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2], fun f => (f 0, f 1, f 2), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def adiagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 3 then r ⟨j, h⟩ :: (if j = 0 then [] else adiagF l (j - 1)) else []

lemma adiag_map (l : List R) (j : ℕ) :
    adiagFrom l j = (adiagF l j).map (fun x : Fin 2 => (x : ℕ)) := by
  induction l generalizing j with
  | nil => simp [adiagFrom, adiagF]
  | cons r l ih => unfold adiagFrom adiagF; split_ifs <;> simp [ih]

lemma adiagF_nil (j : ℕ) : adiagF [] j = [] := rfl

lemma ad_cons0 (r : R) (l : List R) : adiagF (r :: l) 0 = [r 0] := by
  simp [adiagF]

lemma ad_cons1 (r : R) (l : List R) : adiagF (r :: l) 1 = r 1 :: adiagF l 0 := by
  simp [adiagF]

lemma ad_cons2 (r : R) (l : List R) : adiagF (r :: l) 2 = r 2 :: adiagF l 1 := by
  simp [adiagF]

lemma forall_drop (P : List R → Prop) (l : List R) :
    (∀ i, P (l.drop i)) ↔ P l ∧ ∀ i, P (l.drop (i + 1)) := by
  constructor
  · intro h; exact ⟨h 0, fun i => h (i + 1)⟩
  · rintro ⟨h0, h⟩ i; cases i with
    | zero => exact h0
    | succ i => exact h i

lemma fdrop (l : List R) : (∀ i, Acc 0 (adiagF (l.drop i) 2) = true) ↔
    Acc 0 (adiagF l 2) = true ∧ ∀ i, Acc 0 (adiagF (l.drop (i + 1)) 2) = true :=
  forall_drop (fun L => Acc 0 (adiagF L 2) = true) l

lemma ltK (P : ℕ → Prop) : (∀ j < 3, P j) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h0, h1, h2⟩ j hj
    interval_cases j <;> assumption

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 3) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 6 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 0) = true ∧ okb (c 4) (r 1) = true ∧ okb (c 5) (r 2) = true

instance (c : Fin 6 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 6 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ Acc (c 0) (l.map (· 0)) = true ∧ Acc (c 1) (l.map (· 1)) = true ∧ Acc (c 2) (l.map (· 2)) = true ∧ Acc (c 3) (adiagF l 0) = true ∧ Acc (c 4) (adiagF l 1) = true ∧ Acc (c 5) (adiagF l 2) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 2) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 2)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 2) = true by simp only [adiag_map, uniAcc], fdrop]
  simp only [rowUni, colUni, adiag_map, uniAcc, ltK, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, IsEmpty.forall_iff, and_true,
    chain_true]
  tauto

lemma Q_single (c : Fin 6 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF]

lemma Q_cons (c : Fin 6 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 4) (r 1), dl (c 5) (r 2), 0] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, List.drop_succ_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l)]
  simp only [ad_cons2, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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

noncomputable def f (c : Fin 6 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 6 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 6 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 4) (r 1), dl (c 5) (r 2), 0] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 6 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 c4 c5 : Fin 3) (r0 r1 r2 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5] (n + 1) ![r0, r1, r2] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5] ![r0, r1, r2] ∧ adj ![r0, r1, r2] s then
        (f ![dl (c0) (r0), dl (c1) (r1), dl (c2) (r2), dl (c4) (r1), dl (c5) (r2), 0] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 c4 c5 : Fin 3) (r0 r1 r2 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5] (n + 1) ![r0, r1, r2] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5] ![r0, r1, r2] ∧ adj ![r0, r1, r2] s then
        (f ![dl (c0) (r0), dl (c1) (r1), dl (c2) (r2), dl (c4) (r1), dl (c5) (r2), 0] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2916 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1458 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4374 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_729 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2187 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5103 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_90 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3006 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1548 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4464 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_819 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2277 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5193 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_144 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3060 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1602 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4518 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_18 : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1476 : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_747 : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2205 : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_72 : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1530 : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_30 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2946 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1488 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4404 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_759 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2217 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5133 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_120 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3036 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1578 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4494 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_849 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2307 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5223 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_48 : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1506 : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_777 : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2235 : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6 : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2922 : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_735 : (f ![0, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_96 : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3012 : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_825 : (f ![0, 2, 1, 0, 1, 0] 1 ![1, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_150 : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3066 : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_24 : (f ![0, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_753 : (f ![0, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78 : (f ![0, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2917 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1459 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4375 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_730 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2188 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5104 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_19 : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1477 : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_748 : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2206 : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_73 : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1531 : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_31 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2947 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1489 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4405 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_760 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2218 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5134 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_121 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3037 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1579 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4495 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_850 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2308 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5224 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_49 : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1507 : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_778 : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2236 : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7 : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2923 : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_736 : (f ![1, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_25 : (f ![1, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_754 : (f ![1, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_79 : (f ![1, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2918 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1460 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4376 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_92 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3008 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1550 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4466 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_146 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3062 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1604 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4520 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_20 : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1478 : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_74 : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1532 : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_32 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2948 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1490 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4406 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_122 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3038 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1580 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4496 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_50 : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1508 : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8 : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2924 : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_98 : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3014 : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_152 : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3068 : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_26 : (f ![2, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80 : (f ![2, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 124 → Fin 6 → Fin 3 := ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![2, 0, 2, 0, 0, 0], ![0, 2, 2, 0, 0, 0], ![1, 2, 2, 0, 0, 0], ![2, 2, 2, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![2, 1, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 0], ![1, 1, 2, 1, 0, 0], ![2, 1, 2, 1, 0, 0], ![0, 0, 2, 2, 0, 0], ![1, 0, 2, 2, 0, 0], ![2, 0, 2, 2, 0, 0], ![0, 2, 2, 2, 0, 0], ![1, 2, 2, 2, 0, 0], ![2, 2, 2, 2, 0, 0], ![0, 0, 1, 0, 1, 0], ![2, 0, 1, 0, 1, 0], ![0, 2, 1, 0, 1, 0], ![2, 2, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![2, 1, 1, 1, 1, 0], ![0, 0, 1, 2, 1, 0], ![2, 0, 1, 2, 1, 0], ![0, 2, 1, 2, 1, 0], ![2, 2, 1, 2, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![0, 2, 2, 0, 0, 0], ![1, 2, 2, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 0], ![1, 1, 2, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![0, 2, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![2, 0, 2, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![2, 1, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 0], ![1, 1, 2, 1, 0, 0], ![2, 1, 2, 1, 0, 0], ![0, 0, 2, 2, 0, 0], ![1, 0, 2, 2, 0, 0], ![2, 0, 2, 2, 0, 0], ![0, 0, 1, 0, 1, 0], ![2, 0, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![2, 1, 1, 1, 1, 0], ![0, 0, 1, 2, 1, 0], ![2, 0, 1, 2, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 0], ![1, 1, 2, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![2, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![2, 0, 1, 0, 1, 0], ![0, 2, 1, 0, 1, 0], ![2, 2, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![2, 1, 1, 1, 1, 0], ![0, 0, 1, 2, 1, 0], ![2, 0, 1, 2, 1, 0], ![0, 2, 1, 2, 1, 0], ![2, 2, 1, 2, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![2, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![2, 0, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![2, 1, 1, 1, 1, 0], ![0, 0, 1, 2, 1, 0], ![2, 0, 1, 2, 1, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0]]

set_option maxRecDepth 100000 in
def rs : Fin 124 → R := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 124 → ℕ → ℚ := ![fun n => ((23 : ℚ) / 360) * (n : ℚ) ^ 6 + ((19 : ℚ) / 40) * (n : ℚ) ^ 5 + ((193 : ℚ) / 72) * (n : ℚ) ^ 4 + ((69 : ℚ) / 8) * (n : ℚ) ^ 3 + ((1373 : ℚ) / 90) * (n : ℚ) ^ 2 + ((149 : ℚ) / 10) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 3) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 3) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (1 : ℚ) * (n : ℚ) ^ 3 + ((9 : ℚ) / 4) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (1 : ℚ) * (n : ℚ) ^ 3 + ((9 : ℚ) / 4) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 4) * (n : ℚ) ^ 3 + ((131 : ℚ) / 12) * (n : ℚ) ^ 2 + ((197 : ℚ) / 15) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 4) * (n : ℚ) ^ 3 + ((131 : ℚ) / 12) * (n : ℚ) ^ 2 + ((197 : ℚ) / 15) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + ((17 : ℚ) / 4) * (n : ℚ) ^ 3 + (11 : ℚ) * (n : ℚ) ^ 2 + ((68 : ℚ) / 5) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + ((17 : ℚ) / 4) * (n : ℚ) ^ 3 + (11 : ℚ) * (n : ℚ) ^ 2 + ((68 : ℚ) / 5) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((11 : ℚ) / 4) * (n : ℚ) ^ 3 + ((95 : ℚ) / 12) * (n : ℚ) ^ 2 + ((349 : ℚ) / 30) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((25 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((29 : ℚ) / 5) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((25 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((29 : ℚ) / 5) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((23 : ℚ) / 360) * (n : ℚ) ^ 6 + ((19 : ℚ) / 40) * (n : ℚ) ^ 5 + ((193 : ℚ) / 72) * (n : ℚ) ^ 4 + ((69 : ℚ) / 8) * (n : ℚ) ^ 3 + ((1373 : ℚ) / 90) * (n : ℚ) ^ 2 + ((149 : ℚ) / 10) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 3) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((17 : ℚ) / 12) * (n : ℚ) ^ 2 + ((13 : ℚ) / 3) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((3 : ℚ) / 2) * (n : ℚ) ^ 3 + ((17 : ℚ) / 4) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (1 : ℚ) * (n : ℚ) ^ 3 + ((9 : ℚ) / 4) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (1 : ℚ) * (n : ℚ) ^ 3 + ((9 : ℚ) / 4) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 4) * (n : ℚ) ^ 3 + ((131 : ℚ) / 12) * (n : ℚ) ^ 2 + ((197 : ℚ) / 15) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((13 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 4) * (n : ℚ) ^ 3 + ((131 : ℚ) / 12) * (n : ℚ) ^ 2 + ((197 : ℚ) / 15) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((3 : ℚ) / 2) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + ((17 : ℚ) / 4) * (n : ℚ) ^ 3 + (11 : ℚ) * (n : ℚ) ^ 2 + ((68 : ℚ) / 5) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = ((3 : ℚ) / 20) * (n : ℚ) ^ 5 + (1 : ℚ) * (n : ℚ) ^ 4 + ((17 : ℚ) / 4) * (n : ℚ) ^ 3 + (11 : ℚ) * (n : ℚ) ^ 2 + ((68 : ℚ) / 5) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_66 (n : ℕ) : PP 66 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_67 (n : ℕ) : PP 67 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_68 (n : ℕ) : PP 68 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_69 (n : ℕ) : PP 69 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_70 (n : ℕ) : PP 70 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_71 (n : ℕ) : PP 71 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_72 (n : ℕ) : PP 72 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_73 (n : ℕ) : PP 73 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_74 (n : ℕ) : PP 74 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_75 (n : ℕ) : PP 75 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_76 (n : ℕ) : PP 76 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_77 (n : ℕ) : PP 77 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_78 (n : ℕ) : PP 78 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((7 : ℚ) / 3) * (n : ℚ) ^ 3 + ((23 : ℚ) / 3) * (n : ℚ) ^ 2 + ((35 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_79 (n : ℕ) : PP 79 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_80 (n : ℕ) : PP 80 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_81 (n : ℕ) : PP 81 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_82 (n : ℕ) : PP 82 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_83 (n : ℕ) : PP 83 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_84 (n : ℕ) : PP 84 n = ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((11 : ℚ) / 4) * (n : ℚ) ^ 3 + ((95 : ℚ) / 12) * (n : ℚ) ^ 2 + ((349 : ℚ) / 30) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_85 (n : ℕ) : PP 85 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_86 (n : ℕ) : PP 86 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_87 (n : ℕ) : PP 87 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_88 (n : ℕ) : PP 88 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_89 (n : ℕ) : PP 89 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_90 (n : ℕ) : PP 90 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_91 (n : ℕ) : PP 91 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_92 (n : ℕ) : PP 92 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_93 (n : ℕ) : PP 93 n = ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((25 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((29 : ℚ) / 5) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_94 (n : ℕ) : PP 94 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_95 (n : ℕ) : PP 95 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_96 (n : ℕ) : PP 96 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_97 (n : ℕ) : PP 97 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_98 (n : ℕ) : PP 98 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_99 (n : ℕ) : PP 99 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_100 (n : ℕ) : PP 100 n = ((7 : ℚ) / 60) * (n : ℚ) ^ 5 + ((7 : ℚ) / 12) * (n : ℚ) ^ 4 + ((25 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((29 : ℚ) / 5) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_101 (n : ℕ) : PP 101 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (5 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_102 (n : ℕ) : PP 102 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_103 (n : ℕ) : PP 103 n = (1 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_104 (n : ℕ) : PP 104 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_105 (n : ℕ) : PP 105 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_106 (n : ℕ) : PP 106 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_107 (n : ℕ) : PP 107 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_108 (n : ℕ) : PP 108 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_109 (n : ℕ) : PP 109 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_110 (n : ℕ) : PP 110 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_111 (n : ℕ) : PP 111 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_112 (n : ℕ) : PP 112 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_113 (n : ℕ) : PP 113 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_114 (n : ℕ) : PP 114 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_115 (n : ℕ) : PP 115 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (2 : ℚ) * (n : ℚ) ^ 3 + ((37 : ℚ) / 6) * (n : ℚ) ^ 2 + ((21 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_116 (n : ℕ) : PP 116 n = (1 : ℚ) * (n : ℚ) ^ 2 + (4 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_117 (n : ℕ) : PP 117 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_118 (n : ℕ) : PP 118 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_119 (n : ℕ) : PP 119 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_120 (n : ℕ) : PP 120 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_121 (n : ℕ) : PP 121 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_122 (n : ℕ) : PP 122 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_123 (n : ℕ) : PP 123 n = ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((28 : ℚ) / 3) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h84 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 84 n := ih 84
  have h51 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 51 n := ih 51
  have h104 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 104 n := ih 104
  have h35 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 35 n := ih 35
  have h73 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 73 n := ih 73
  have h117 : (f ![0, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h84, h51, h104, h35, h73, h117, f_dead, pp_0, pp_0, pp_84, pp_51, pp_104, pp_35, pp_73, pp_117]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 7 := by exact_mod_cast fv1_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h2 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h86 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 86 n := ih 86
  have h53 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 53 n := ih 53
  have h106 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 106 n := ih 106
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h2, h86, h53, h106, f_dead, pp_1, pp_2, pp_86, pp_53, pp_106]
  try (push_cast; ring)

lemma b_1 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_1
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h2 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h86 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 86 n := ih 86
  have h53 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 53 n := ih 53
  have h106 : (f ![2, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 106 n := ih 106
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h2, h86, h53, h106, f_dead, pp_2, pp_2, pp_86, pp_53, pp_106]
  try (push_cast; ring)

lemma b_2 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_2
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h3 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h87 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 87 n := ih 87
  have h37 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 37 n := ih 37
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h3, h87, h37, f_dead, pp_3, pp_3, pp_87, pp_37]
  try (push_cast; ring)

lemma b_3 : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_6
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h5 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h89 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h5, h89, f_dead, pp_4, pp_5, pp_89]
  try (push_cast; ring)

lemma b_4 : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_7
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h5 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h89 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h5, h89, f_dead, pp_5, pp_5, pp_89]
  try (push_cast; ring)

lemma b_5 : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_8
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h6 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 6 n := ih 6
  have h54 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 54 n := ih 54
  have h39 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 39 n := ih 39
  have h75 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h6, h54, h39, h75, f_dead, pp_6, pp_6, pp_54, pp_39, pp_75]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_18
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h8 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 8 n := ih 8
  have h56 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h8, h56, f_dead, pp_7, pp_8, pp_56]
  try (push_cast; ring)

lemma b_7 : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_19
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h8 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 8 n := ih 8
  have h56 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h8, h56, f_dead, pp_8, pp_8, pp_56]
  try (push_cast; ring)

lemma b_8 : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_20
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h9 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h41 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h9, h41, f_dead, pp_9, pp_9, pp_41]
  try (push_cast; ring)

lemma b_9 : (f ![0, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_24
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h11, f_dead, pp_10, pp_11]
  try (push_cast; ring)

lemma b_10 : (f ![1, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_25
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 0, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h11, f_dead, pp_11, pp_11]
  try (push_cast; ring)

lemma b_11 : (f ![2, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![2, 2, 2, 0, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_26
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h3 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h87 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 87 n := ih 87
  have h37 : (f ![0, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 37 n := ih 37
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h3, h87, h37, f_dead, pp_12, pp_3, pp_87, pp_37]
  try (push_cast; ring)

lemma b_12 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_30
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h5 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h89 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h5, h89, f_dead, pp_13, pp_5, pp_89]
  try (push_cast; ring)

lemma b_13 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_31
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h5 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h89 : (f ![2, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h5, h89, f_dead, pp_14, pp_5, pp_89]
  try (push_cast; ring)

lemma b_14 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_32
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h9 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h41 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h9, h41, f_dead, pp_15, pp_9, pp_41]
  try (push_cast; ring)

lemma b_15 : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_48
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 16 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h11, f_dead, pp_16, pp_11]
  try (push_cast; ring)

lemma b_16 : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 16 0 := by
  have h : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_49
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 17 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h11, f_dead, pp_17, pp_11]
  try (push_cast; ring)

lemma b_17 : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 17 0 := by
  have h : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_50
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 18 (n + 1) := by
  have h6 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 6 n := ih 6
  have h54 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 54 n := ih 54
  have h39 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 39 n := ih 39
  have h75 : (f ![0, 0, 2, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h6, h54, h39, h75, f_dead, pp_18, pp_6, pp_54, pp_39, pp_75]
  try (push_cast; ring)

lemma b_18 : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 18 0 := by
  have h : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_72
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 19 (n + 1) := by
  have h8 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 8 n := ih 8
  have h56 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h8, h56, f_dead, pp_19, pp_8, pp_56]
  try (push_cast; ring)

lemma b_19 : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 19 0 := by
  have h : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_73
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 20 (n + 1) := by
  have h8 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 8 n := ih 8
  have h56 : (f ![2, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h8, h56, f_dead, pp_20, pp_8, pp_56]
  try (push_cast; ring)

lemma b_20 : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 20 0 := by
  have h : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_74
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 21 (n + 1) := by
  have h9 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h41 : (f ![0, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h9, h41, f_dead, pp_21, pp_9, pp_41]
  try (push_cast; ring)

lemma b_21 : (f ![0, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 21 0 := by
  have h : (f ![0, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_78
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 22 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h11, f_dead, pp_22, pp_11]
  try (push_cast; ring)

lemma b_22 : (f ![1, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 22 0 := by
  have h : (f ![1, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_79
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 0, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 23 (n + 1) := by
  have h11 : (f ![2, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h11, f_dead, pp_23, pp_11]
  try (push_cast; ring)

lemma b_23 : (f ![2, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = PP 23 0 := by
  have h : (f ![2, 2, 2, 2, 0, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_80
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 24 (n + 1) := by
  have h18 : (f ![0, 0, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h63 : (f ![0, 0, 2, 2, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h18, h63, f_dead, pp_24, pp_18, pp_63]
  try (push_cast; ring)

lemma b_24 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 24 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_90
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 25 (n + 1) := by
  have h20 : (f ![2, 0, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 20 n := ih 20
  have h65 : (f ![2, 0, 2, 2, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h20, h65, f_dead, pp_25, pp_20, pp_65]
  try (push_cast; ring)

lemma b_25 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 25 0 := by
  have h : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_92
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 26 (n + 1) := by
  have h21 : (f ![0, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 21 n := ih 21
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h21, f_dead, pp_26, pp_21]
  try (push_cast; ring)

lemma b_26 : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 26 0 := by
  have h : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_96
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 27 (n + 1) := by
  have h23 : (f ![2, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 23 n := ih 23
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h23, f_dead, pp_27, pp_23]
  try (push_cast; ring)

lemma b_27 : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 27 0 := by
  have h : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_98
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 28 (n + 1) := by
  have h21 : (f ![0, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 21 n := ih 21
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h21, f_dead, pp_28, pp_21]
  try (push_cast; ring)

lemma b_28 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 28 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_120
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 29 (n + 1) := by
  have h23 : (f ![2, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 23 n := ih 23
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h23, f_dead, pp_29, pp_23]
  try (push_cast; ring)

lemma b_29 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 29 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_121
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 30 (n + 1) := by
  have h23 : (f ![2, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 23 n := ih 23
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h23, f_dead, pp_30, pp_23]
  try (push_cast; ring)

lemma b_30 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 30 0 := by
  have h : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_122
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 31 (n + 1) := by
  have h18 : (f ![0, 0, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h63 : (f ![0, 0, 2, 2, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h18, h63, f_dead, pp_31, pp_18, pp_63]
  try (push_cast; ring)

lemma b_31 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 31 0 := by
  have h : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_144
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 32 (n + 1) := by
  have h20 : (f ![2, 0, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 20 n := ih 20
  have h65 : (f ![2, 0, 2, 2, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h20, h65, f_dead, pp_32, pp_20, pp_65]
  try (push_cast; ring)

lemma b_32 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 32 0 := by
  have h : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_146
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 33 (n + 1) := by
  have h21 : (f ![0, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 21 n := ih 21
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h21, f_dead, pp_33, pp_21]
  try (push_cast; ring)

lemma b_33 : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 33 0 := by
  have h : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_150
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 0] : ℚ) = PP 34 (n + 1) := by
  have h23 : (f ![2, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 23 n := ih 23
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h23, f_dead, pp_34, pp_23]
  try (push_cast; ring)

lemma b_34 : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = PP 34 0 := by
  have h : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_152
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 35 (n + 1) := by
  have h1 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h85 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 85 n := ih 85
  have h52 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 52 n := ih 52
  have h105 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 105 n := ih 105
  have h36 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 36 n := ih 36
  have h74 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 74 n := ih 74
  have h118 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 118 n := ih 118
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h1, h85, h52, h105, h36, h74, h118, f_dead, pp_35, pp_1, pp_85, pp_52, pp_105, pp_36, pp_74, pp_118]
  try (push_cast; ring)

lemma b_35 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 35 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv1_729
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 36 (n + 1) := by
  have h1 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h85 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 85 n := ih 85
  have h52 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 52 n := ih 52
  have h105 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 105 n := ih 105
  have h36 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 36 n := ih 36
  have h74 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 74 n := ih 74
  have h118 : (f ![1, 0, 0, 0, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 118 n := ih 118
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h1, h85, h52, h105, h36, h74, h118, f_dead, pp_36, pp_1, pp_85, pp_52, pp_105, pp_36, pp_74, pp_118]
  try (push_cast; ring)

lemma b_36 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 36 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv1_730
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 0, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 37 (n + 1) := by
  have h4 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h88 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 88 n := ih 88
  have h38 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h4, h88, h38, f_dead, pp_37, pp_4, pp_88, pp_38]
  try (push_cast; ring)

lemma b_37 : (f ![0, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 37 0 := by
  have h : (f ![0, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_735
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 38 (n + 1) := by
  have h4 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h88 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 88 n := ih 88
  have h38 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h4, h88, h38, f_dead, pp_38, pp_4, pp_88, pp_38]
  try (push_cast; ring)

lemma b_38 : (f ![1, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 38 0 := by
  have h : (f ![1, 2, 0, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_736
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 39 (n + 1) := by
  have h7 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h55 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 55 n := ih 55
  have h40 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 40 n := ih 40
  have h76 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 76 n := ih 76
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h7, h55, h40, h76, f_dead, pp_39, pp_7, pp_55, pp_40, pp_76]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_747
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 40 (n + 1) := by
  have h7 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h55 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 55 n := ih 55
  have h40 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 40 n := ih 40
  have h76 : (f ![1, 0, 2, 0, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 76 n := ih 76
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h7, h55, h40, h76, f_dead, pp_40, pp_7, pp_55, pp_40, pp_76]
  try (push_cast; ring)

lemma b_40 : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 40 0 := by
  have h : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv1_748
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 41 (n + 1) := by
  have h10 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h42 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h10, h42, f_dead, pp_41, pp_10, pp_42]
  try (push_cast; ring)

lemma b_41 : (f ![0, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 41 0 := by
  have h : (f ![0, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_753
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 0, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 42 (n + 1) := by
  have h10 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h42 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h10, h42, f_dead, pp_42, pp_10, pp_42]
  try (push_cast; ring)

lemma b_42 : (f ![1, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 42 0 := by
  have h : (f ![1, 2, 2, 0, 0, 0] 1 ![1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_754
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 43 (n + 1) := by
  have h4 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h88 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 88 n := ih 88
  have h38 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h4, h88, h38, f_dead, pp_43, pp_4, pp_88, pp_38]
  try (push_cast; ring)

lemma b_43 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 43 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_759
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 44 (n + 1) := by
  have h4 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h88 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 88 n := ih 88
  have h38 : (f ![1, 2, 0, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h4, h88, h38, f_dead, pp_44, pp_4, pp_88, pp_38]
  try (push_cast; ring)

lemma b_44 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 44 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv1_760
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 1, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 45 (n + 1) := by
  have h10 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h42 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h10, h42, f_dead, pp_45, pp_10, pp_42]
  try (push_cast; ring)

lemma b_45 : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 45 0 := by
  have h : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_777
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 1, 0, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 46 (n + 1) := by
  have h10 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h42 : (f ![1, 2, 2, 0, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, dl20, h10, h42, f_dead, pp_46, pp_10, pp_42]
  try (push_cast; ring)

lemma b_46 : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = PP 46 0 := by
  have h : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_778
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 47 (n + 1) := by
  have h19 : (f ![1, 0, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h64 : (f ![1, 0, 2, 2, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h19, h64, f_dead, pp_47, pp_19, pp_64]
  try (push_cast; ring)

lemma b_47 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 0, 0] : ℚ) = PP 47 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv1_819
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 1, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 48 (n + 1) := by
  have h22 : (f ![1, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 22 n := ih 22
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h22, f_dead, pp_48, pp_22]
  try (push_cast; ring)

lemma b_48 : (f ![0, 2, 1, 0, 1, 0] 1 ![1, 0, 0] : ℚ) = PP 48 0 := by
  have h : (f ![0, 2, 1, 0, 1, 0] 1 ![1, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_825
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 49 (n + 1) := by
  have h22 : (f ![1, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 22 n := ih 22
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h22, f_dead, pp_49, pp_22]
  try (push_cast; ring)

lemma b_49 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℚ) = PP 49 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_849
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 0, 0] : ℚ) = PP 50 (n + 1) := by
  have h22 : (f ![1, 2, 2, 2, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 22 n := ih 22
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h22, f_dead, pp_50, pp_22]
  try (push_cast; ring)

lemma b_50 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℚ) = PP 50 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 0, 0] : ℚ) = 1 := by exact_mod_cast fv1_850
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 51 (n + 1) := by
  have h12 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h90 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 90 n := ih 90
  have h57 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 57 n := ih 57
  have h107 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 107 n := ih 107
  have h43 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 43 n := ih 43
  have h77 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h119 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h90, h57, h107, h43, h77, h119, f_dead, pp_51, pp_12, pp_90, pp_57, pp_107, pp_43, pp_77, pp_119]
  try (push_cast; ring)

lemma b_51 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 51 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_1458
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 52 (n + 1) := by
  have h14 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h92 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 92 n := ih 92
  have h59 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 59 n := ih 59
  have h109 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 109 n := ih 109
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h14, h92, h59, h109, f_dead, pp_52, pp_14, pp_92, pp_59, pp_109]
  try (push_cast; ring)

lemma b_52 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 52 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1459
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 53 (n + 1) := by
  have h14 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h92 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 92 n := ih 92
  have h59 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 59 n := ih 59
  have h109 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 109 n := ih 109
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h14, h92, h59, h109, f_dead, pp_53, pp_14, pp_92, pp_59, pp_109]
  try (push_cast; ring)

lemma b_53 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 53 0 := by
  have h : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1460
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 54 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h15, h60, h45, h79, f_dead, pp_54, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_54 : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 54 0 := by
  have h : (f ![0, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1476
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 55 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h17, h62, f_dead, pp_55, pp_17, pp_62]
  try (push_cast; ring)

lemma b_55 : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 55 0 := by
  have h : (f ![1, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1477
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 2, 0, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 56 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h17, h62, f_dead, pp_56, pp_17, pp_62]
  try (push_cast; ring)

lemma b_56 : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 56 0 := by
  have h : (f ![2, 0, 2, 0, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1478
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 57 (n + 1) := by
  have h12 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h90 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 90 n := ih 90
  have h57 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 57 n := ih 57
  have h107 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 107 n := ih 107
  have h43 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 43 n := ih 43
  have h77 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h119 : (f ![0, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h90, h57, h107, h43, h77, h119, f_dead, pp_57, pp_12, pp_90, pp_57, pp_107, pp_43, pp_77, pp_119]
  try (push_cast; ring)

lemma b_57 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 57 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_1488
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 58 (n + 1) := by
  have h14 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h92 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 92 n := ih 92
  have h59 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 59 n := ih 59
  have h109 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 109 n := ih 109
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h14, h92, h59, h109, f_dead, pp_58, pp_14, pp_92, pp_59, pp_109]
  try (push_cast; ring)

lemma b_58 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 58 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1489
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 59 (n + 1) := by
  have h14 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h92 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 92 n := ih 92
  have h59 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 59 n := ih 59
  have h109 : (f ![2, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 109 n := ih 109
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h14, h92, h59, h109, f_dead, pp_59, pp_14, pp_92, pp_59, pp_109]
  try (push_cast; ring)

lemma b_59 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 59 0 := by
  have h : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1490
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 60 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h15, h60, h45, h79, f_dead, pp_60, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_60 : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 60 0 := by
  have h : (f ![0, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1506
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 61 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h17, h62, f_dead, pp_61, pp_17, pp_62]
  try (push_cast; ring)

lemma b_61 : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 61 0 := by
  have h : (f ![1, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1507
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 2, 1, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 62 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h17, h62, f_dead, pp_62, pp_17, pp_62]
  try (push_cast; ring)

lemma b_62 : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 62 0 := by
  have h : (f ![2, 1, 2, 1, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1508
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 63 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h15, h60, h45, h79, f_dead, pp_63, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_63 : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 63 0 := by
  have h : (f ![0, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1530
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 64 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h17, h62, f_dead, pp_64, pp_17, pp_62]
  try (push_cast; ring)

lemma b_64 : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 64 0 := by
  have h : (f ![1, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1531
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 2, 2, 0, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 65 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h17, h62, f_dead, pp_65, pp_17, pp_62]
  try (push_cast; ring)

lemma b_65 : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = PP 65 0 := by
  have h : (f ![2, 0, 2, 2, 0, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1532
  rw [h, pp_65]; try norm_num

set_option maxRecDepth 100000 in
lemma st_66 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 66 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h15, h60, h45, h79, f_dead, pp_66, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_66 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 66 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1548
  rw [h, pp_66]; try norm_num

set_option maxRecDepth 100000 in
lemma st_67 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 67 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h17, h62, f_dead, pp_67, pp_17, pp_62]
  try (push_cast; ring)

lemma b_67 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 67 0 := by
  have h : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1550
  rw [h, pp_67]; try norm_num

set_option maxRecDepth 100000 in
lemma st_68 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 68 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h15, h60, h45, h79, f_dead, pp_68, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_68 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 68 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1578
  rw [h, pp_68]; try norm_num

set_option maxRecDepth 100000 in
lemma st_69 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 69 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h17, h62, f_dead, pp_69, pp_17, pp_62]
  try (push_cast; ring)

lemma b_69 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 69 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1579
  rw [h, pp_69]; try norm_num

set_option maxRecDepth 100000 in
lemma st_70 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 70 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, dl20, h17, h62, f_dead, pp_70, pp_17, pp_62]
  try (push_cast; ring)

lemma b_70 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 70 0 := by
  have h : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1580
  rw [h, pp_70]; try norm_num

set_option maxRecDepth 100000 in
lemma st_71 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 71 (n + 1) := by
  have h15 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h60 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 60 n := ih 60
  have h45 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 45 n := ih 45
  have h79 : (f ![0, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h15, h60, h45, h79, f_dead, pp_71, pp_15, pp_60, pp_45, pp_79]
  try (push_cast; ring)

lemma b_71 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 71 0 := by
  have h : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_1602
  rw [h, pp_71]; try norm_num

set_option maxRecDepth 100000 in
lemma st_72 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 1, 0] : ℚ) = PP 72 (n + 1) := by
  have h17 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h62 : (f ![2, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h17, h62, f_dead, pp_72, pp_17, pp_62]
  try (push_cast; ring)

lemma b_72 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℚ) = PP 72 0 := by
  have h : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 0] : ℚ) = 2 := by exact_mod_cast fv1_1604
  rw [h, pp_72]; try norm_num

set_option maxRecDepth 100000 in
lemma st_73 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 73 (n + 1) := by
  have h13 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h91 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 91 n := ih 91
  have h58 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 58 n := ih 58
  have h108 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 108 n := ih 108
  have h44 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 44 n := ih 44
  have h78 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 78 n := ih 78
  have h120 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 120 n := ih 120
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h13, h91, h58, h108, h44, h78, h120, f_dead, pp_73, pp_13, pp_91, pp_58, pp_108, pp_44, pp_78, pp_120]
  try (push_cast; ring)

lemma b_73 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 73 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_2187
  rw [h, pp_73]; try norm_num

set_option maxRecDepth 100000 in
lemma st_74 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 74 (n + 1) := by
  have h13 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h91 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 91 n := ih 91
  have h58 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 58 n := ih 58
  have h108 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 108 n := ih 108
  have h44 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 44 n := ih 44
  have h78 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 78 n := ih 78
  have h120 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 120 n := ih 120
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h13, h91, h58, h108, h44, h78, h120, f_dead, pp_74, pp_13, pp_91, pp_58, pp_108, pp_44, pp_78, pp_120]
  try (push_cast; ring)

lemma b_74 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 74 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_2188
  rw [h, pp_74]; try norm_num

set_option maxRecDepth 100000 in
lemma st_75 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 0, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 75 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h16, h61, h46, h80, f_dead, pp_75, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_75 : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 75 0 := by
  have h : (f ![0, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2205
  rw [h, pp_75]; try norm_num

set_option maxRecDepth 100000 in
lemma st_76 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 2, 0, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 76 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h16, h61, h46, h80, f_dead, pp_76, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_76 : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 76 0 := by
  have h : (f ![1, 0, 2, 0, 0, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2206
  rw [h, pp_76]; try norm_num

set_option maxRecDepth 100000 in
lemma st_77 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 77 (n + 1) := by
  have h13 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h91 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 91 n := ih 91
  have h58 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 58 n := ih 58
  have h108 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 108 n := ih 108
  have h44 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 44 n := ih 44
  have h78 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 78 n := ih 78
  have h120 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 120 n := ih 120
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h13, h91, h58, h108, h44, h78, h120, f_dead, pp_77, pp_13, pp_91, pp_58, pp_108, pp_44, pp_78, pp_120]
  try (push_cast; ring)

lemma b_77 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 77 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_2217
  rw [h, pp_77]; try norm_num

set_option maxRecDepth 100000 in
lemma st_78 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 78 (n + 1) := by
  have h13 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h91 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 91 n := ih 91
  have h58 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 58 n := ih 58
  have h108 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 108 n := ih 108
  have h44 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 44 n := ih 44
  have h78 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 78 n := ih 78
  have h120 : (f ![1, 1, 0, 1, 0, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 120 n := ih 120
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h13, h91, h58, h108, h44, h78, h120, f_dead, pp_78, pp_13, pp_91, pp_58, pp_108, pp_44, pp_78, pp_120]
  try (push_cast; ring)

lemma b_78 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 78 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = 7 := by exact_mod_cast fv1_2218
  rw [h, pp_78]; try norm_num

set_option maxRecDepth 100000 in
lemma st_79 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 1, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 79 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h16, h61, h46, h80, f_dead, pp_79, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_79 : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 79 0 := by
  have h : (f ![0, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2235
  rw [h, pp_79]; try norm_num

set_option maxRecDepth 100000 in
lemma st_80 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 1, 0, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 80 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h16, h61, h46, h80, f_dead, pp_80, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_80 : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = PP 80 0 := by
  have h : (f ![1, 1, 2, 1, 0, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2236
  rw [h, pp_80]; try norm_num

set_option maxRecDepth 100000 in
lemma st_81 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 81 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h16, h61, h46, h80, f_dead, pp_81, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_81 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 0] : ℚ) = PP 81 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2277
  rw [h, pp_81]; try norm_num

set_option maxRecDepth 100000 in
lemma st_82 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 82 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h16, h61, h46, h80, f_dead, pp_82, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_82 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℚ) = PP 82 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2307
  rw [h, pp_82]; try norm_num

set_option maxRecDepth 100000 in
lemma st_83 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 1, 0] : ℚ) = PP 83 (n + 1) := by
  have h16 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h61 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 61 n := ih 61
  have h46 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 46 n := ih 46
  have h80 : (f ![1, 1, 2, 1, 0, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h16, h61, h46, h80, f_dead, pp_83, pp_16, pp_61, pp_46, pp_80]
  try (push_cast; ring)

lemma b_83 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℚ) = PP 83 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv1_2308
  rw [h, pp_83]; try norm_num

set_option maxRecDepth 100000 in
lemma st_84 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 84 (n + 1) := by
  have h24 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h93 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 93 n := ih 93
  have h66 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 66 n := ih 66
  have h110 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 110 n := ih 110
  have h47 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 47 n := ih 47
  have h81 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 81 n := ih 81
  have h121 : (f ![0, 0, 1, 0, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 121 n := ih 121
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h24, h93, h66, h110, h47, h81, h121, f_dead, pp_84, pp_24, pp_93, pp_66, pp_110, pp_47, pp_81, pp_121]
  try (push_cast; ring)

lemma b_84 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 84 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 7 := by exact_mod_cast fv1_2916
  rw [h, pp_84]; try norm_num

set_option maxRecDepth 100000 in
lemma st_85 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 85 (n + 1) := by
  have h25 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 25 n := ih 25
  have h94 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 94 n := ih 94
  have h67 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 67 n := ih 67
  have h111 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 111 n := ih 111
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h25, h94, h67, h111, f_dead, pp_85, pp_25, pp_94, pp_67, pp_111]
  try (push_cast; ring)

lemma b_85 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 85 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_2917
  rw [h, pp_85]; try norm_num

set_option maxRecDepth 100000 in
lemma st_86 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 86 (n + 1) := by
  have h25 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 25 n := ih 25
  have h94 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 94 n := ih 94
  have h67 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 67 n := ih 67
  have h111 : (f ![2, 0, 1, 0, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 111 n := ih 111
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h25, h94, h67, h111, f_dead, pp_86, pp_25, pp_94, pp_67, pp_111]
  try (push_cast; ring)

lemma b_86 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 86 0 := by
  have h : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_2918
  rw [h, pp_86]; try norm_num

set_option maxRecDepth 100000 in
lemma st_87 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 87 (n + 1) := by
  have h26 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h95 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 95 n := ih 95
  have h48 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h26, h95, h48, f_dead, pp_87, pp_26, pp_95, pp_48]
  try (push_cast; ring)

lemma b_87 : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 87 0 := by
  have h : (f ![0, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 3 := by exact_mod_cast fv1_2922
  rw [h, pp_87]; try norm_num

set_option maxRecDepth 100000 in
lemma st_88 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 88 (n + 1) := by
  have h27 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 27 n := ih 27
  have h96 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h27, h96, f_dead, pp_88, pp_27, pp_96]
  try (push_cast; ring)

lemma b_88 : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 88 0 := by
  have h : (f ![1, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_2923
  rw [h, pp_88]; try norm_num

set_option maxRecDepth 100000 in
lemma st_89 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 89 (n + 1) := by
  have h27 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 27 n := ih 27
  have h96 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h27, h96, f_dead, pp_89, pp_27, pp_96]
  try (push_cast; ring)

lemma b_89 : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 89 0 := by
  have h : (f ![2, 2, 0, 0, 0, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_2924
  rw [h, pp_89]; try norm_num

set_option maxRecDepth 100000 in
lemma st_90 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 90 (n + 1) := by
  have h26 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h95 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 95 n := ih 95
  have h48 : (f ![0, 2, 1, 0, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h26, h95, h48, f_dead, pp_90, pp_26, pp_95, pp_48]
  try (push_cast; ring)

lemma b_90 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 90 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = 3 := by exact_mod_cast fv1_2946
  rw [h, pp_90]; try norm_num

set_option maxRecDepth 100000 in
lemma st_91 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 91 (n + 1) := by
  have h27 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 27 n := ih 27
  have h96 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h27, h96, f_dead, pp_91, pp_27, pp_96]
  try (push_cast; ring)

lemma b_91 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 91 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_2947
  rw [h, pp_91]; try norm_num

set_option maxRecDepth 100000 in
lemma st_92 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 92 (n + 1) := by
  have h27 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 27 n := ih 27
  have h96 : (f ![2, 2, 1, 0, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h27, h96, f_dead, pp_92, pp_27, pp_96]
  try (push_cast; ring)

lemma b_92 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = PP 92 0 := by
  have h : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_2948
  rw [h, pp_92]; try norm_num

set_option maxRecDepth 100000 in
lemma st_93 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 93 (n + 1) := by
  have h31 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 31 n := ih 31
  have h100 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 100 n := ih 100
  have h71 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 71 n := ih 71
  have h115 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 115 n := ih 115
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h31, h100, h71, h115, f_dead, pp_93, pp_31, pp_100, pp_71, pp_115]
  try (push_cast; ring)

lemma b_93 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 93 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_3006
  rw [h, pp_93]; try norm_num

set_option maxRecDepth 100000 in
lemma st_94 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 94 (n + 1) := by
  have h32 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 32 n := ih 32
  have h101 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 101 n := ih 101
  have h72 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 72 n := ih 72
  have h116 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 116 n := ih 116
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h32, h101, h72, h116, f_dead, pp_94, pp_32, pp_101, pp_72, pp_116]
  try (push_cast; ring)

lemma b_94 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 94 0 := by
  have h : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_3008
  rw [h, pp_94]; try norm_num

set_option maxRecDepth 100000 in
lemma st_95 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 95 (n + 1) := by
  have h33 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 33 n := ih 33
  have h102 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 102 n := ih 102
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h33, h102, f_dead, pp_95, pp_33, pp_102]
  try (push_cast; ring)

lemma b_95 : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 95 0 := by
  have h : (f ![0, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3012
  rw [h, pp_95]; try norm_num

set_option maxRecDepth 100000 in
lemma st_96 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 96 (n + 1) := by
  have h34 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 34 n := ih 34
  have h103 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h34, h103, f_dead, pp_96, pp_34, pp_103]
  try (push_cast; ring)

lemma b_96 : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 96 0 := by
  have h : (f ![2, 2, 1, 0, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3014
  rw [h, pp_96]; try norm_num

set_option maxRecDepth 100000 in
lemma st_97 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 97 (n + 1) := by
  have h33 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 33 n := ih 33
  have h102 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 102 n := ih 102
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h33, h102, f_dead, pp_97, pp_33, pp_102]
  try (push_cast; ring)

lemma b_97 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 97 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3036
  rw [h, pp_97]; try norm_num

set_option maxRecDepth 100000 in
lemma st_98 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 98 (n + 1) := by
  have h34 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 34 n := ih 34
  have h103 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h34, h103, f_dead, pp_98, pp_34, pp_103]
  try (push_cast; ring)

lemma b_98 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 98 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3037
  rw [h, pp_98]; try norm_num

set_option maxRecDepth 100000 in
lemma st_99 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 99 (n + 1) := by
  have h34 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 34 n := ih 34
  have h103 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h34, h103, f_dead, pp_99, pp_34, pp_103]
  try (push_cast; ring)

lemma b_99 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 99 0 := by
  have h : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3038
  rw [h, pp_99]; try norm_num

set_option maxRecDepth 100000 in
lemma st_100 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 100 (n + 1) := by
  have h31 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 31 n := ih 31
  have h100 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 100 n := ih 100
  have h71 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 71 n := ih 71
  have h115 : (f ![0, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 115 n := ih 115
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h31, h100, h71, h115, f_dead, pp_100, pp_31, pp_100, pp_71, pp_115]
  try (push_cast; ring)

lemma b_100 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 100 0 := by
  have h : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_3060
  rw [h, pp_100]; try norm_num

set_option maxRecDepth 100000 in
lemma st_101 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 101 (n + 1) := by
  have h32 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 32 n := ih 32
  have h101 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 101 n := ih 101
  have h72 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 72 n := ih 72
  have h116 : (f ![2, 0, 1, 2, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 116 n := ih 116
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h32, h101, h72, h116, f_dead, pp_101, pp_32, pp_101, pp_72, pp_116]
  try (push_cast; ring)

lemma b_101 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 101 0 := by
  have h : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv1_3062
  rw [h, pp_101]; try norm_num

set_option maxRecDepth 100000 in
lemma st_102 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 102 (n + 1) := by
  have h33 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 33 n := ih 33
  have h102 : (f ![0, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 102 n := ih 102
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h33, h102, f_dead, pp_102, pp_33, pp_102]
  try (push_cast; ring)

lemma b_102 : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 102 0 := by
  have h : (f ![0, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3066
  rw [h, pp_102]; try norm_num

set_option maxRecDepth 100000 in
lemma st_103 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 2, 1, 0] (n + 1 + 1) ![0, 0, 1] : ℚ) = PP 103 (n + 1) := by
  have h34 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 34 n := ih 34
  have h103 : (f ![2, 2, 1, 2, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h34, h103, f_dead, pp_103, pp_34, pp_103]
  try (push_cast; ring)

lemma b_103 : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = PP 103 0 := by
  have h : (f ![2, 2, 1, 2, 1, 0] 1 ![0, 0, 1] : ℚ) = 2 := by exact_mod_cast fv1_3068
  rw [h, pp_103]; try norm_num

set_option maxRecDepth 100000 in
lemma st_104 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 104 (n + 1) := by
  have h28 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 28 n := ih 28
  have h97 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 97 n := ih 97
  have h68 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 68 n := ih 68
  have h112 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 112 n := ih 112
  have h49 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 49 n := ih 49
  have h82 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 82 n := ih 82
  have h122 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h28, h97, h68, h112, h49, h82, h122, f_dead, pp_104, pp_28, pp_97, pp_68, pp_112, pp_49, pp_82, pp_122]
  try (push_cast; ring)

lemma b_104 : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 104 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_4374
  rw [h, pp_104]; try norm_num

set_option maxRecDepth 100000 in
lemma st_105 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 105 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h30, h99, h70, h114, f_dead, pp_105, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_105 : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 105 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4375
  rw [h, pp_105]; try norm_num

set_option maxRecDepth 100000 in
lemma st_106 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 106 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, h30, h99, h70, h114, f_dead, pp_106, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_106 : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 106 0 := by
  have h : (f ![2, 0, 0, 0, 0, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4376
  rw [h, pp_106]; try norm_num

set_option maxRecDepth 100000 in
lemma st_107 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 107 (n + 1) := by
  have h28 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 28 n := ih 28
  have h97 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 97 n := ih 97
  have h68 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 68 n := ih 68
  have h112 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 112 n := ih 112
  have h49 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 49 n := ih 49
  have h82 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 82 n := ih 82
  have h122 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h28, h97, h68, h112, h49, h82, h122, f_dead, pp_107, pp_28, pp_97, pp_68, pp_112, pp_49, pp_82, pp_122]
  try (push_cast; ring)

lemma b_107 : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 107 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_4404
  rw [h, pp_107]; try norm_num

set_option maxRecDepth 100000 in
lemma st_108 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 108 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h30, h99, h70, h114, f_dead, pp_108, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_108 : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 108 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4405
  rw [h, pp_108]; try norm_num

set_option maxRecDepth 100000 in
lemma st_109 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 1, 0, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 109 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h30, h99, h70, h114, f_dead, pp_109, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_109 : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = PP 109 0 := by
  have h : (f ![2, 1, 0, 1, 0, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4406
  rw [h, pp_109]; try norm_num

set_option maxRecDepth 100000 in
lemma st_110 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 110 (n + 1) := by
  have h28 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 28 n := ih 28
  have h97 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 97 n := ih 97
  have h68 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 68 n := ih 68
  have h112 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 112 n := ih 112
  have h49 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 49 n := ih 49
  have h82 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 82 n := ih 82
  have h122 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h28, h97, h68, h112, h49, h82, h122, f_dead, pp_110, pp_28, pp_97, pp_68, pp_112, pp_49, pp_82, pp_122]
  try (push_cast; ring)

lemma b_110 : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 110 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_4464
  rw [h, pp_110]; try norm_num

set_option maxRecDepth 100000 in
lemma st_111 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 111 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h30, h99, h70, h114, f_dead, pp_111, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_111 : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 111 0 := by
  have h : (f ![2, 0, 1, 0, 1, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4466
  rw [h, pp_111]; try norm_num

set_option maxRecDepth 100000 in
lemma st_112 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 112 (n + 1) := by
  have h28 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 28 n := ih 28
  have h97 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 97 n := ih 97
  have h68 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 68 n := ih 68
  have h112 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 112 n := ih 112
  have h49 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 49 n := ih 49
  have h82 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 82 n := ih 82
  have h122 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h28, h97, h68, h112, h49, h82, h122, f_dead, pp_112, pp_28, pp_97, pp_68, pp_112, pp_49, pp_82, pp_122]
  try (push_cast; ring)

lemma b_112 : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 112 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_4494
  rw [h, pp_112]; try norm_num

set_option maxRecDepth 100000 in
lemma st_113 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 113 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h30, h99, h70, h114, f_dead, pp_113, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_113 : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 113 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4495
  rw [h, pp_113]; try norm_num

set_option maxRecDepth 100000 in
lemma st_114 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 114 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h30, h99, h70, h114, f_dead, pp_114, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_114 : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 114 0 := by
  have h : (f ![2, 1, 1, 1, 1, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4496
  rw [h, pp_114]; try norm_num

set_option maxRecDepth 100000 in
lemma st_115 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 115 (n + 1) := by
  have h28 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 28 n := ih 28
  have h97 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 97 n := ih 97
  have h68 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 68 n := ih 68
  have h112 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 112 n := ih 112
  have h49 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 49 n := ih 49
  have h82 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 82 n := ih 82
  have h122 : (f ![0, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h28, h97, h68, h112, h49, h82, h122, f_dead, pp_115, pp_28, pp_97, pp_68, pp_112, pp_49, pp_82, pp_122]
  try (push_cast; ring)

lemma b_115 : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 115 0 := by
  have h : (f ![0, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_4518
  rw [h, pp_115]; try norm_num

set_option maxRecDepth 100000 in
lemma st_116 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2, 1, 0] (n + 1 + 1) ![0, 1, 1] : ℚ) = PP 116 (n + 1) := by
  have h30 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 30 n := ih 30
  have h99 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 99 n := ih 99
  have h70 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 70 n := ih 70
  have h114 : (f ![2, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 114 n := ih 114
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h30, h99, h70, h114, f_dead, pp_116, pp_30, pp_99, pp_70, pp_114]
  try (push_cast; ring)

lemma b_116 : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℚ) = PP 116 0 := by
  have h : (f ![2, 0, 1, 2, 1, 0] 1 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv1_4520
  rw [h, pp_116]; try norm_num

set_option maxRecDepth 100000 in
lemma st_117 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 117 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_117, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_117 : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℚ) = PP 117 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5103
  rw [h, pp_117]; try norm_num

set_option maxRecDepth 100000 in
lemma st_118 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 118 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_118, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_118 : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℚ) = PP 118 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5104
  rw [h, pp_118]; try norm_num

set_option maxRecDepth 100000 in
lemma st_119 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 119 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_119, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_119 : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℚ) = PP 119 0 := by
  have h : (f ![0, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5133
  rw [h, pp_119]; try norm_num

set_option maxRecDepth 100000 in
lemma st_120 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 1, 0, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 120 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_120, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_120 : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℚ) = PP 120 0 := by
  have h : (f ![1, 1, 0, 1, 0, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5134
  rw [h, pp_120]; try norm_num

set_option maxRecDepth 100000 in
lemma st_121 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 1, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 121 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_121, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_121 : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 1] : ℚ) = PP 121 0 := by
  have h : (f ![0, 0, 1, 0, 1, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5193
  rw [h, pp_121]; try norm_num

set_option maxRecDepth 100000 in
lemma st_122 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 122 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_122, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_122 : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℚ) = PP 122 0 := by
  have h : (f ![0, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5223
  rw [h, pp_122]; try norm_num

set_option maxRecDepth 100000 in
lemma st_123 (n : ℕ) (ih : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 0] (n + 1 + 1) ![1, 1, 1] : ℚ) = PP 123 (n + 1) := by
  have h29 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 0] : ℚ) = PP 29 n := ih 29
  have h98 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 0, 1] : ℚ) = PP 98 n := ih 98
  have h69 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 0] : ℚ) = PP 69 n := ih 69
  have h113 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![0, 1, 1] : ℚ) = PP 113 n := ih 113
  have h50 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 0, 0] : ℚ) = PP 50 n := ih 50
  have h83 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 0] : ℚ) = PP 83 n := ih 83
  have h123 : (f ![1, 1, 1, 1, 1, 0] (n + 1) ![1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h29, h98, h69, h113, h50, h83, h123, f_dead, pp_123, pp_29, pp_98, pp_69, pp_113, pp_50, pp_83, pp_123]
  try (push_cast; ring)

lemma b_123 : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℚ) = PP 123 0 := by
  have h : (f ![1, 1, 1, 1, 1, 0] 1 ![1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv1_5224
  rw [h, pp_123]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 124, (f (cs k) (n + 1) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65, b_66, b_67, b_68, b_69, b_70, b_71, b_72, b_73, b_74, b_75, b_76, b_77, b_78, b_79, b_80, b_81, b_82, b_83, b_84, b_85, b_86, b_87, b_88, b_89, b_90, b_91, b_92, b_93, b_94, b_95, b_96, b_97, b_98, b_99, b_100, b_101, b_102, b_103, b_104, b_105, b_106, b_107, b_108, b_109, b_110, b_111, b_112, b_113, b_114, b_115, b_116, b_117, b_118, b_119, b_120, b_121, b_122, b_123]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih, st_66 n ih, st_67 n ih, st_68 n ih, st_69 n ih, st_70 n ih, st_71 n ih, st_72 n ih, st_73 n ih, st_74 n ih, st_75 n ih, st_76 n ih, st_77 n ih, st_78 n ih, st_79 n ih, st_80 n ih, st_81 n ih, st_82 n ih, st_83 n ih, st_84 n ih, st_85 n ih, st_86 n ih, st_87 n ih, st_88 n ih, st_89 n ih, st_90 n ih, st_91 n ih, st_92 n ih, st_93 n ih, st_94 n ih, st_95 n ih, st_96 n ih, st_97 n ih, st_98 n ih, st_99 n ih, st_100 n ih, st_101 n ih, st_102 n ih, st_103 n ih, st_104 n ih, st_105 n ih, st_106 n ih, st_107 n ih, st_108 n ih, st_109 n ih, st_110 n ih, st_111 n ih, st_112 n ih, st_113 n ih, st_114 n ih, st_115 n ih, st_116 n ih, st_117 n ih, st_118 n ih, st_119 n ih, st_120 n ih, st_121 n ih, st_122 n ih, st_123 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 2) : ℚ) = ((23 : ℚ) / 360) * (m : ℚ) ^ 6 + ((103 : ℚ) / 120) * (m : ℚ) ^ 5 + ((433 : ℚ) / 72) * (m : ℚ) ^ 4 + ((203 : ℚ) / 8) * (m : ℚ) ^ 3 + ((5663 : ℚ) / 90) * (m : ℚ) ^ 2 + ((2543 : ℚ) / 30) * (m : ℚ) ^ 1 + (49 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g84 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![0, 0, 1] : ℚ) = PP 84 m := f_closed m 84
  have g51 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![0, 1, 0] : ℚ) = PP 51 m := f_closed m 51
  have g104 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![0, 1, 1] : ℚ) = PP 104 m := f_closed m 104
  have g35 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![1, 0, 0] : ℚ) = PP 35 m := f_closed m 35
  have g73 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![1, 1, 0] : ℚ) = PP 73 m := f_closed m 73
  have g117 : (f ![0, 0, 0, 0, 0, 0] (m + 1) ![1, 1, 1] : ℚ) = PP 117 m := f_closed m 117
  rw [show m + 2 = (m + 1) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 6 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g84, g51, g104, g35, g73, g117, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_84, pp_51, pp_104, pp_35, pp_73, pp_117]
  ring

lemma aS1 : (a 1 : ℚ) = 7 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 6 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma av (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((23 : ℚ) / 360) * (n : ℚ) ^ 6 + ((11 : ℚ) / 120) * (n : ℚ) ^ 5 + ((91 : ℚ) / 72) * (n : ℚ) ^ 4 + ((11 : ℚ) / 8) * (n : ℚ) ^ 3 + ((301 : ℚ) / 180) * (n : ℚ) ^ 2 + ((23 : ℚ) / 15) * (n : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp only [aS1] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 + 33 * X ^ 2 - 18 * X ^ 3 + 29 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (7 + 33 * X ^ 2 - 18 * X ^ 3 + 29 * X ^ 4 - 6 * X ^ 5 + X ^ 6 : PowerSeries ℚ) =
        C (7 : ℚ) * X ^ 0 + C (33 : ℚ) * X ^ 2 + C (-18 : ℚ) * X ^ 3 + C (29 : ℚ) * X ^ 4 + C (-6 : ℚ) * X ^ 5 + C (1 : ℚ) * X ^ 6 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 7 := aS1
    have e2 : (a 2 : ℚ) = 49 := by rw [av 2 (by norm_num)]; norm_num
    have e3 : (a 3 : ℚ) = 229 := by rw [av 3 (by norm_num)]; norm_num
    have e4 : (a 4 : ℚ) = 801 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 2297 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 5699 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 12657 := by rw [av 7 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 7 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6, e7] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 7 := ⟨c - 7, by omega⟩
      simp only [show m + 7 - 0 = m + 7 by omega, show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m + 0 by omega, show 0 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show 7 ≤ m + 7 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 7 + 1) (by omega), av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega), av (m + 1 + 1) (by omega), av (m + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega]
    qify
    rw [av (m + 8) (by omega), av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega), av (m + 2) (by omega), av (m + 1) (by omega)]
    push_cast; ring

end OMA.P_oeis_a223632

theorem OMA.solution : type_of% @OMA.S_oeis_a223632.main := OMA.P_oeis_a223632.full
