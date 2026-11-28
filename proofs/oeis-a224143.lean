import OMAStatements.S_oeis_a224143
import Mathlib

/-!
# oeis-a224143: counting the n X 5 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 5 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 3 it is an explicit polynomial, checked by induction over the
101 states (c, r) whose top row is allowed, from exact values at n = 1..3. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A224143, https://oeis.org/A224143.
-/
namespace OMA.P_oeis_a224143

open OMA.S_oeis_a224143

def adj (r s : Fin 5 → Fin 2) : Prop := ∀ j : Fin 5, r j ≤ s j

instance (r s : Fin 5 → Fin 2) : Decidable (adj r s) := by unfold adj; infer_instance

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

abbrev R := Fin 5 → Fin 2

lemma sumk {M : Type*} [AddCommMonoid M] (g : R → M) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, ∑ y4 : Fin 2, g ![y0, y1, y2, y3, y4] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2], fun f => (f 0, f 1, f 2, f 3, f 4), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def adiagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 5 then r ⟨j, h⟩ :: (if j = 0 then [] else adiagF l (j - 1)) else []

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

lemma ad_cons3 (r : R) (l : List R) : adiagF (r :: l) 3 = r 3 :: adiagF l 2 := by
  simp [adiagF]

lemma ad_cons4 (r : R) (l : List R) : adiagF (r :: l) 4 = r 4 :: adiagF l 3 := by
  simp [adiagF]

lemma forall_drop (P : List R → Prop) (l : List R) :
    (∀ i, P (l.drop i)) ↔ P l ∧ ∀ i, P (l.drop (i + 1)) := by
  constructor
  · intro h; exact ⟨h 0, fun i => h (i + 1)⟩
  · rintro ⟨h0, h⟩ i; cases i with
    | zero => exact h0
    | succ i => exact h i

lemma fdrop (l : List R) : (∀ i, Acc 0 (adiagF (l.drop i) 4) = true) ↔
    Acc 0 (adiagF l 4) = true ∧ ∀ i, Acc 0 (adiagF (l.drop (i + 1)) 4) = true :=
  forall_drop (fun L => Acc 0 (adiagF L 4) = true) l

lemma ltK (P : ℕ → Prop) : (∀ j < 5, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ j hj
    interval_cases j <;> assumption

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 5) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 5 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true ∧ okb (c 4) (r 4) = true

instance (c : Fin 5 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 5 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ Acc (c 0) (adiagF l 0) = true ∧ Acc (c 1) (adiagF l 1) = true ∧ Acc (c 2) (adiagF l 2) = true ∧ Acc (c 3) (adiagF l 3) = true ∧ Acc (c 4) (adiagF l 4) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 4) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 4)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 4) = true by simp only [adiag_map, uniAcc], fdrop]
  simp only [rowUni, adiag_map, uniAcc, ltK, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    ]
  tauto

lemma Q_single (c : Fin 5 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF]

lemma Q_cons (c : Fin 5 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 4) (r 4), 0] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, ad_cons3, ad_cons4, List.drop_succ_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l)]
  simp only [ad_cons4, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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

noncomputable def f (c : Fin 5 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 5 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 5 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 4) (r 4), 0] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 5 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 c4 : Fin 3) (r0 r1 r2 r3 r4 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4] (n + 1) ![r0, r1, r2, r3, r4] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4] ![r0, r1, r2, r3, r4] ∧ adj ![r0, r1, r2, r3, r4] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c4) (r4), 0] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 c4 : Fin 3) (r0 r1 r2 r3 r4 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4] (n + 1) ![r0, r1, r2, r3, r4] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4] ![r0, r1, r2, r3, r4] ∧ adj ![r0, r1, r2, r3, r4] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c4) (r4), 0] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3888 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1944 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5832 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_972 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 1, 0, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2916 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6804 : (f ![0, 0, 0, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_486 : (f ![0, 0, 0, 0, 0] 1 ![0, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1458 : (f ![0, 0, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3402 : (f ![0, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7290 : (f ![0, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_243 : (f ![0, 0, 0, 0, 0] 1 ![1, 0, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_729 : (f ![0, 0, 0, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1701 : (f ![0, 0, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3645 : (f ![0, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7533 : (f ![0, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3915 : (f ![0, 0, 0, 1, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5859 : (f ![0, 0, 0, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6831 : (f ![0, 0, 0, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7317 : (f ![0, 0, 0, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7560 : (f ![0, 0, 0, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1953 : (f ![0, 0, 1, 0, 0] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5841 : (f ![0, 0, 1, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2925 : (f ![0, 0, 1, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6813 : (f ![0, 0, 1, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3411 : (f ![0, 0, 1, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7299 : (f ![0, 0, 1, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3654 : (f ![0, 0, 1, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7542 : (f ![0, 0, 1, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5868 : (f ![0, 0, 1, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6840 : (f ![0, 0, 1, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7326 : (f ![0, 0, 1, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7569 : (f ![0, 0, 1, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3933 : (f ![0, 0, 2, 1, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5877 : (f ![0, 0, 2, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_975 : (f ![0, 1, 0, 0, 0] 1 ![0, 0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2919 : (f ![0, 1, 0, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6807 : (f ![0, 1, 0, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1461 : (f ![0, 1, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3405 : (f ![0, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7293 : (f ![0, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1704 : (f ![0, 1, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3648 : (f ![0, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7536 : (f ![0, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2928 : (f ![0, 1, 1, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6816 : (f ![0, 1, 1, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3414 : (f ![0, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7302 : (f ![0, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3657 : (f ![0, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7545 : (f ![0, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6843 : (f ![0, 1, 1, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7329 : (f ![0, 1, 1, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7572 : (f ![0, 1, 1, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1959 : (f ![0, 2, 1, 0, 0] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5847 : (f ![0, 2, 1, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2931 : (f ![0, 2, 1, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6819 : (f ![0, 2, 1, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5874 : (f ![0, 2, 1, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6846 : (f ![0, 2, 1, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3939 : (f ![0, 2, 2, 1, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5883 : (f ![0, 2, 2, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_487 : (f ![1, 0, 0, 0, 0] 1 ![0, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1459 : (f ![1, 0, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3403 : (f ![1, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7291 : (f ![1, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_730 : (f ![1, 0, 0, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1702 : (f ![1, 0, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3646 : (f ![1, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7534 : (f ![1, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1462 : (f ![1, 1, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3406 : (f ![1, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7294 : (f ![1, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1705 : (f ![1, 1, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3649 : (f ![1, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7537 : (f ![1, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3415 : (f ![1, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7303 : (f ![1, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3658 : (f ![1, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7546 : (f ![1, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7330 : (f ![1, 1, 1, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7573 : (f ![1, 1, 1, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_977 : (f ![2, 1, 0, 0, 0] 1 ![0, 0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2921 : (f ![2, 1, 0, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6809 : (f ![2, 1, 0, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1463 : (f ![2, 1, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3407 : (f ![2, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7295 : (f ![2, 1, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2930 : (f ![2, 1, 1, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6818 : (f ![2, 1, 1, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3416 : (f ![2, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7304 : (f ![2, 1, 1, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6845 : (f ![2, 1, 1, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7331 : (f ![2, 1, 1, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1961 : (f ![2, 2, 1, 0, 0] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5849 : (f ![2, 2, 1, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2933 : (f ![2, 2, 1, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6821 : (f ![2, 2, 1, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5876 : (f ![2, 2, 1, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6848 : (f ![2, 2, 1, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_3941 : (f ![2, 2, 2, 1, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_5885 : (f ![2, 2, 2, 1, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 0] : ℤ) = 86 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_3888, fv1_1944, fv1_5832, fv1_972, fv1_2916, fv1_6804, fv1_486, fv1_1458, fv1_3402, fv1_7290, fv1_243, fv1_729, fv1_1701, fv1_3645, fv1_7533, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3888 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_3915, fv1_5859, fv1_6831, fv1_7317, fv1_7560, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1944 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 0] : ℤ) = 24 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1953, fv1_5841, fv1_2925, fv1_6813, fv1_3411, fv1_7299, fv1_3654, fv1_7542, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5832 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_5868, fv1_6840, fv1_7326, fv1_7569, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_972 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 1, 0, 0] : ℤ) = 30 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_975, fv1_2919, fv1_6807, fv1_1461, fv1_3405, fv1_7293, fv1_1704, fv1_3648, fv1_7536, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2916 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_2928, fv1_6816, fv1_3414, fv1_7302, fv1_3657, fv1_7545, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6804 : (f ![0, 0, 0, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_6843, fv1_7329, fv1_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_486 : (f ![0, 0, 0, 0, 0] 2 ![0, 1, 0, 0, 0] : ℤ) = 30 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_487, fv1_1459, fv1_3403, fv1_7291, fv1_730, fv1_1702, fv1_3646, fv1_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1458 : (f ![0, 0, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1462, fv1_3406, fv1_7294, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3402 : (f ![0, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7290 : (f ![0, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_243 : (f ![0, 0, 0, 0, 0] 2 ![1, 0, 0, 0, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_243, fv1_729, fv1_1701, fv1_3645, fv1_7533, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_729 : (f ![0, 0, 0, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_730, fv1_1702, fv1_3646, fv1_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1701 : (f ![0, 0, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3645 : (f ![0, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7533 : (f ![0, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3915 : (f ![0, 0, 0, 1, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_3933, fv1_5877, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5859 : (f ![0, 0, 0, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_5868, fv1_6840, fv1_7326, fv1_7569, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6831 : (f ![0, 0, 0, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_6843, fv1_7329, fv1_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7317 : (f ![0, 0, 0, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7560 : (f ![0, 0, 0, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1953 : (f ![0, 0, 1, 0, 0] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_1959, fv1_5847, fv1_2931, fv1_6819, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5841 : (f ![0, 0, 1, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_5874, fv1_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2925 : (f ![0, 0, 1, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_2928, fv1_6816, fv1_3414, fv1_7302, fv1_3657, fv1_7545, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6813 : (f ![0, 0, 1, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_6843, fv1_7329, fv1_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3411 : (f ![0, 0, 1, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7299 : (f ![0, 0, 1, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3654 : (f ![0, 0, 1, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7542 : (f ![0, 0, 1, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5868 : (f ![0, 0, 1, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_5874, fv1_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6840 : (f ![0, 0, 1, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_6843, fv1_7329, fv1_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7326 : (f ![0, 0, 1, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7569 : (f ![0, 0, 1, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3933 : (f ![0, 0, 2, 1, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_3939, fv1_5883, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5877 : (f ![0, 0, 2, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_5874, fv1_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_975 : (f ![0, 1, 0, 0, 0] 2 ![0, 0, 1, 0, 0] : ℤ) = 24 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_977, fv1_2921, fv1_6809, fv1_1463, fv1_3407, fv1_7295, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2919 : (f ![0, 1, 0, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6807 : (f ![0, 1, 0, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1461 : (f ![0, 1, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1462, fv1_3406, fv1_7294, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3405 : (f ![0, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7293 : (f ![0, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1704 : (f ![0, 1, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3648 : (f ![0, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7536 : (f ![0, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2928 : (f ![0, 1, 1, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6816 : (f ![0, 1, 1, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3414 : (f ![0, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7302 : (f ![0, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3657 : (f ![0, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7545 : (f ![0, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6843 : (f ![0, 1, 1, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7329 : (f ![0, 1, 1, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7572 : (f ![0, 1, 1, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1959 : (f ![0, 2, 1, 0, 0] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_1961, fv1_5849, fv1_2933, fv1_6821, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5847 : (f ![0, 2, 1, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2931 : (f ![0, 2, 1, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6819 : (f ![0, 2, 1, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5874 : (f ![0, 2, 1, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6846 : (f ![0, 2, 1, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3939 : (f ![0, 2, 2, 1, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_3941, fv1_5885, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5883 : (f ![0, 2, 2, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_487 : (f ![1, 0, 0, 0, 0] 2 ![0, 1, 0, 0, 0] : ℤ) = 30 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_487, fv1_1459, fv1_3403, fv1_7291, fv1_730, fv1_1702, fv1_3646, fv1_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1459 : (f ![1, 0, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1462, fv1_3406, fv1_7294, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3403 : (f ![1, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7291 : (f ![1, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_730 : (f ![1, 0, 0, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_730, fv1_1702, fv1_3646, fv1_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1702 : (f ![1, 0, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3646 : (f ![1, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7534 : (f ![1, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1462 : (f ![1, 1, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1462, fv1_3406, fv1_7294, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3406 : (f ![1, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7294 : (f ![1, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1705 : (f ![1, 1, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3649 : (f ![1, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7537 : (f ![1, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3415 : (f ![1, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7303 : (f ![1, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3658 : (f ![1, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7546 : (f ![1, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7330 : (f ![1, 1, 1, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7573 : (f ![1, 1, 1, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_977 : (f ![2, 1, 0, 0, 0] 2 ![0, 0, 1, 0, 0] : ℤ) = 24 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_977, fv1_2921, fv1_6809, fv1_1463, fv1_3407, fv1_7295, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2921 : (f ![2, 1, 0, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6809 : (f ![2, 1, 0, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1463 : (f ![2, 1, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1462, fv1_3406, fv1_7294, fv1_1705, fv1_3649, fv1_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3407 : (f ![2, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7295 : (f ![2, 1, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2930 : (f ![2, 1, 1, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6818 : (f ![2, 1, 1, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3416 : (f ![2, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_3415, fv1_7303, fv1_3658, fv1_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7304 : (f ![2, 1, 1, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6845 : (f ![2, 1, 1, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7331 : (f ![2, 1, 1, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_7330, fv1_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1961 : (f ![2, 2, 1, 0, 0] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_1961, fv1_5849, fv1_2933, fv1_6821, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5849 : (f ![2, 2, 1, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2933 : (f ![2, 2, 1, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_2930, fv1_6818, fv1_3416, fv1_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6821 : (f ![2, 2, 1, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5876 : (f ![2, 2, 1, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6848 : (f ![2, 2, 1, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_6845, fv1_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_3941 : (f ![2, 2, 2, 1, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_3941, fv1_5885, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_5885 : (f ![2, 2, 2, 1, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_5876, fv1_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_0 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℤ) = 275 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_0, fv2_3888, fv2_1944, fv2_5832, fv2_972, fv2_2916, fv2_6804, fv2_486, fv2_1458, fv2_3402, fv2_7290, fv2_243, fv2_729, fv2_1701, fv2_3645, fv2_7533, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3888 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_3915, fv2_5859, fv2_6831, fv2_7317, fv2_7560, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1944 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℤ) = 52 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1953, fv2_5841, fv2_2925, fv2_6813, fv2_3411, fv2_7299, fv2_3654, fv2_7542, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5832 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_5868, fv2_6840, fv2_7326, fv2_7569, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_972 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℤ) = 80 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_975, fv2_2919, fv2_6807, fv2_1461, fv2_3405, fv2_7293, fv2_1704, fv2_3648, fv2_7536, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2916 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_2928, fv2_6816, fv2_3414, fv2_7302, fv2_3657, fv2_7545, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6804 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_6843, fv2_7329, fv2_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_486 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℤ) = 80 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_487, fv2_1459, fv2_3403, fv2_7291, fv2_730, fv2_1702, fv2_3646, fv2_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1458 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 40 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1462, fv2_3406, fv2_7294, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3402 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7290 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_243 : (f ![0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℤ) = 35 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_243, fv2_729, fv2_1701, fv2_3645, fv2_7533, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_729 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 20 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_730, fv2_1702, fv2_3646, fv2_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1701 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3645 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7533 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3915 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_3933, fv2_5877, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5859 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_5868, fv2_6840, fv2_7326, fv2_7569, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6831 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_6843, fv2_7329, fv2_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7317 : (f ![0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7560 : (f ![0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1953 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_1959, fv2_5847, fv2_2931, fv2_6819, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5841 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_5874, fv2_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2925 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_2928, fv2_6816, fv2_3414, fv2_7302, fv2_3657, fv2_7545, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6813 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_6843, fv2_7329, fv2_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3411 : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7299 : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3654 : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7542 : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5868 : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_5874, fv2_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6840 : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_6843, fv2_7329, fv2_7572, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7326 : (f ![0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7569 : (f ![0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3933 : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_3939, fv2_5883, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5877 : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_5874, fv2_6846, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_975 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℤ) = 70 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_977, fv2_2921, fv2_6809, fv2_1463, fv2_3407, fv2_7295, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2919 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6807 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1461 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 40 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1462, fv2_3406, fv2_7294, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3405 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7293 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1704 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3648 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7536 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2928 : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6816 : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3414 : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7302 : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3657 : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7545 : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6843 : (f ![0, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7329 : (f ![0, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7572 : (f ![0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1959 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_1961, fv2_5849, fv2_2933, fv2_6821, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5847 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2931 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6819 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5874 : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6846 : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3939 : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_3941, fv2_5885, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5883 : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_487 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℤ) = 80 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_487, fv2_1459, fv2_3403, fv2_7291, fv2_730, fv2_1702, fv2_3646, fv2_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1459 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 40 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1462, fv2_3406, fv2_7294, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3403 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7291 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_730 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 20 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_730, fv2_1702, fv2_3646, fv2_7534, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1702 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3646 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7534 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1462 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 40 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1462, fv2_3406, fv2_7294, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3406 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7294 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1705 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3649 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7537 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3415 : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7303 : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3658 : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7546 : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7330 : (f ![1, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7573 : (f ![1, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_977 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℤ) = 70 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_977, fv2_2921, fv2_6809, fv2_1463, fv2_3407, fv2_7295, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2921 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6809 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1463 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 40 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1462, fv2_3406, fv2_7294, fv2_1705, fv2_3649, fv2_7537, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3407 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7295 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2930 : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6818 : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3416 : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_3415, fv2_7303, fv2_3658, fv2_7546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7304 : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6845 : (f ![2, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7331 : (f ![2, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_7330, fv2_7573, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1961 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_1961, fv2_5849, fv2_2933, fv2_6821, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5849 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2933 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_2930, fv2_6818, fv2_3416, fv2_7304, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6821 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5876 : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6848 : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_6845, fv2_7331, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_3941 : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_3941, fv2_5885, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_5885 : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_5876, fv2_6848, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 101 → Fin 5 → Fin 3 := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 2, 1, 0, 0], ![2, 2, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![2, 1, 1, 0, 0], ![0, 2, 1, 0, 0], ![2, 2, 1, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![2, 1, 1, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 2, 1, 0], ![0, 2, 2, 1, 0], ![2, 2, 2, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 2, 1, 0, 0], ![2, 2, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 2, 1, 1, 0], ![2, 2, 1, 1, 0], ![0, 0, 2, 1, 0], ![0, 2, 2, 1, 0], ![2, 2, 2, 1, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![2, 1, 1, 0, 0], ![0, 2, 1, 0, 0], ![2, 2, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 1, 1, 1, 0], ![2, 1, 1, 1, 0], ![0, 2, 1, 1, 0], ![2, 2, 1, 1, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![2, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![2, 1, 1, 1, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 1, 1, 1, 0], ![1, 1, 1, 1, 0]]

set_option maxRecDepth 100000 in
def rs : Fin 101 → R := ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 101 → ℕ → ℚ := ![fun n => ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((8 : ℚ) / 3) * (n : ℚ) ^ 4 + ((70 : ℚ) / 3) * (n : ℚ) ^ 3 + ((331 : ℚ) / 3) * (n : ℚ) ^ 2 + ((4193 : ℚ) / 15) * (n : ℚ) ^ 1 + (275 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((11 : ℚ) / 12) * (n : ℚ) ^ 3 + ((179 : ℚ) / 24) * (n : ℚ) ^ 2 + ((319 : ℚ) / 12) * (n : ℚ) ^ 1 + (35 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((67 : ℚ) / 3) * (n : ℚ) ^ 2 + ((208 : ℚ) / 3) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((67 : ℚ) / 3) * (n : ℚ) ^ 2 + ((208 : ℚ) / 3) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((37 : ℚ) / 3) * (n : ℚ) ^ 1 + (20 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((37 : ℚ) / 3) * (n : ℚ) ^ 1 + (20 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((99 : ℚ) / 4) * (n : ℚ) ^ 2 + (71 : ℚ) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((97 : ℚ) / 4) * (n : ℚ) ^ 2 + ((133 : ℚ) / 2) * (n : ℚ) ^ 1 + (70 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((97 : ℚ) / 4) * (n : ℚ) ^ 2 + ((133 : ℚ) / 2) * (n : ℚ) ^ 1 + (70 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((8 : ℚ) / 3) * (n : ℚ) ^ 4 + ((70 : ℚ) / 3) * (n : ℚ) ^ 3 + ((331 : ℚ) / 3) * (n : ℚ) ^ 2 + ((4193 : ℚ) / 15) * (n : ℚ) ^ 1 + (275 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((11 : ℚ) / 12) * (n : ℚ) ^ 3 + ((179 : ℚ) / 24) * (n : ℚ) ^ 2 + ((319 : ℚ) / 12) * (n : ℚ) ^ 1 + (35 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((67 : ℚ) / 3) * (n : ℚ) ^ 2 + ((208 : ℚ) / 3) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((67 : ℚ) / 3) * (n : ℚ) ^ 2 + ((208 : ℚ) / 3) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((37 : ℚ) / 3) * (n : ℚ) ^ 1 + (20 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + ((37 : ℚ) / 3) * (n : ℚ) ^ 1 + (20 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((99 : ℚ) / 4) * (n : ℚ) ^ 2 + (71 : ℚ) * (n : ℚ) ^ 1 + (80 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((97 : ℚ) / 4) * (n : ℚ) ^ 2 + ((133 : ℚ) / 2) * (n : ℚ) ^ 1 + (70 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((97 : ℚ) / 4) * (n : ℚ) ^ 2 + ((133 : ℚ) / 2) * (n : ℚ) ^ 1 + (70 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((13 : ℚ) / 2) * (n : ℚ) ^ 2 + (28 : ℚ) * (n : ℚ) ^ 1 + (40 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_66 (n : ℕ) : PP 66 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_67 (n : ℕ) : PP 67 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_68 (n : ℕ) : PP 68 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_69 (n : ℕ) : PP 69 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_70 (n : ℕ) : PP 70 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_71 (n : ℕ) : PP 71 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_72 (n : ℕ) : PP 72 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_73 (n : ℕ) : PP 73 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_74 (n : ℕ) : PP 74 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_75 (n : ℕ) : PP 75 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_76 (n : ℕ) : PP 76 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_77 (n : ℕ) : PP 77 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_78 (n : ℕ) : PP 78 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_79 (n : ℕ) : PP 79 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_80 (n : ℕ) : PP 80 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_81 (n : ℕ) : PP 81 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_82 (n : ℕ) : PP 82 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_83 (n : ℕ) : PP 83 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_84 (n : ℕ) : PP 84 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_85 (n : ℕ) : PP 85 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_86 (n : ℕ) : PP 86 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_87 (n : ℕ) : PP 87 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_88 (n : ℕ) : PP 88 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_89 (n : ℕ) : PP 89 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_90 (n : ℕ) : PP 90 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_91 (n : ℕ) : PP 91 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_92 (n : ℕ) : PP 92 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_93 (n : ℕ) : PP 93 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_94 (n : ℕ) : PP 94 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_95 (n : ℕ) : PP 95 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_96 (n : ℕ) : PP 96 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_97 (n : ℕ) : PP 97 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_98 (n : ℕ) : PP 98 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_99 (n : ℕ) : PP 99 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_100 (n : ℕ) : PP 100 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h46 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h18 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 18 n := ih 18
  have h51 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 51 n := ih 51
  have h6 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 6 n := ih 6
  have h22 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 22 n := ih 22
  have h62 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  have h2 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h9 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 9 n := ih 9
  have h30 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h76 : (f ![0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 76 n := ih 76
  have h1 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h4 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h14 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h39 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 39 n := ih 39
  have h90 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 90 n := ih 90
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h46, h18, h51, h6, h22, h62, h2, h9, h30, h76, h1, h4, h14, h39, h90, f_dead, pp_0, pp_0, pp_46, pp_18, pp_51, pp_6, pp_22, pp_62, pp_2, pp_9, pp_30, pp_76, pp_1, pp_4, pp_14, pp_39, pp_90]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℚ) = 275 := by exact_mod_cast fv3_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h1 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h4 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h14 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h39 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 39 n := ih 39
  have h90 : (f ![0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 90 n := ih 90
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h1, h4, h14, h39, h90, f_dead, pp_1, pp_1, pp_4, pp_14, pp_39, pp_90]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = 35 := by exact_mod_cast fv3_243
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h3 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h10 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h31 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h77 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 77 n := ih 77
  have h5 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 40 n := ih 40
  have h91 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h3, h10, h31, h77, h5, h15, h40, h91, f_dead, pp_2, pp_3, pp_10, pp_31, pp_77, pp_5, pp_15, pp_40, pp_91]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = 80 := by exact_mod_cast fv3_486
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h3 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h10 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h31 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h77 : (f ![1, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 77 n := ih 77
  have h5 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 40 n := ih 40
  have h91 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h3, h10, h31, h77, h5, h15, h40, h91, f_dead, pp_3, pp_3, pp_10, pp_31, pp_77, pp_5, pp_15, pp_40, pp_91]
  try (push_cast; ring)

lemma b_3 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = 80 := by exact_mod_cast fv3_487
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h5 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 40 n := ih 40
  have h91 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h5, h15, h40, h91, f_dead, pp_4, pp_5, pp_15, pp_40, pp_91]
  try (push_cast; ring)

lemma b_4 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 20 := by exact_mod_cast fv3_729
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h5 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 40 n := ih 40
  have h91 : (f ![1, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h5, h15, h40, h91, f_dead, pp_5, pp_5, pp_15, pp_40, pp_91]
  try (push_cast; ring)

lemma b_5 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 20 := by exact_mod_cast fv3_730
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h7 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 7 n := ih 7
  have h23 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h63 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  have h11 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 11 n := ih 11
  have h32 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 32 n := ih 32
  have h78 : (f ![0, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 78 n := ih 78
  have h16 : (f ![0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 16 n := ih 16
  have h41 : (f ![0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 41 n := ih 41
  have h92 : (f ![0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 92 n := ih 92
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h7, h23, h63, h11, h32, h78, h16, h41, h92, f_dead, pp_6, pp_7, pp_23, pp_63, pp_11, pp_32, pp_78, pp_16, pp_41, pp_92]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = 80 := by exact_mod_cast fv3_972
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h8 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 8 n := ih 8
  have h24 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 24 n := ih 24
  have h64 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  have h13 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h34 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 34 n := ih 34
  have h80 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h8, h24, h64, h13, h34, h80, f_dead, pp_7, pp_8, pp_24, pp_64, pp_13, pp_34, pp_80]
  try (push_cast; ring)

lemma b_7 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = 70 := by exact_mod_cast fv3_975
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h8 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 8 n := ih 8
  have h24 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 24 n := ih 24
  have h64 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  have h13 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h34 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 34 n := ih 34
  have h80 : (f ![2, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h8, h24, h64, h13, h34, h80, f_dead, pp_8, pp_8, pp_24, pp_64, pp_13, pp_34, pp_80]
  try (push_cast; ring)

lemma b_8 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = 70 := by exact_mod_cast fv3_977
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  have h79 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 79 n := ih 79
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h33, h79, h17, h42, h93, f_dead, pp_9, pp_12, pp_33, pp_79, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_9 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 40 := by exact_mod_cast fv3_1458
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  have h79 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 79 n := ih 79
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h33, h79, h17, h42, h93, f_dead, pp_10, pp_12, pp_33, pp_79, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_10 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 40 := by exact_mod_cast fv3_1459
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  have h79 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 79 n := ih 79
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h79, h17, h42, h93, f_dead, pp_11, pp_12, pp_33, pp_79, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_11 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 40 := by exact_mod_cast fv3_1461
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  have h79 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 79 n := ih 79
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h79, h17, h42, h93, f_dead, pp_12, pp_12, pp_33, pp_79, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_12 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 40 := by exact_mod_cast fv3_1462
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  have h79 : (f ![1, 1, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 79 n := ih 79
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h79, h17, h42, h93, f_dead, pp_13, pp_12, pp_33, pp_79, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_13 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 40 := by exact_mod_cast fv3_1463
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h17, h42, h93, f_dead, pp_14, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_14 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_1701
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h17, h42, h93, f_dead, pp_15, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_15 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_1702
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 16 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h17, h42, h93, f_dead, pp_16, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_16 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 16 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_1704
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 17 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 42 n := ih 42
  have h93 : (f ![1, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h17, h42, h93, f_dead, pp_17, pp_17, pp_42, pp_93]
  try (push_cast; ring)

lemma b_17 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 17 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_1705
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 18 (n + 1) := by
  have h19 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 19 n := ih 19
  have h52 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 52 n := ih 52
  have h25 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 25 n := ih 25
  have h65 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h35 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 35 n := ih 35
  have h81 : (f ![0, 0, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 81 n := ih 81
  have h43 : (f ![0, 0, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 43 n := ih 43
  have h94 : (f ![0, 0, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 94 n := ih 94
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h19, h52, h25, h65, h35, h81, h43, h94, f_dead, pp_18, pp_19, pp_52, pp_25, pp_65, pp_35, pp_81, pp_43, pp_94]
  try (push_cast; ring)

lemma b_18 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 18 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = 52 := by exact_mod_cast fv3_1944
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 19 (n + 1) := by
  have h20 : (f ![0, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 20 n := ih 20
  have h53 : (f ![0, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 53 n := ih 53
  have h28 : (f ![0, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 28 n := ih 28
  have h68 : (f ![0, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 68 n := ih 68
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h20, h53, h28, h68, f_dead, pp_19, pp_20, pp_53, pp_28, pp_68]
  try (push_cast; ring)

lemma b_19 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 19 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_1953
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 20 (n + 1) := by
  have h21 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 21 n := ih 21
  have h54 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 54 n := ih 54
  have h29 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 29 n := ih 29
  have h69 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 69 n := ih 69
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h21, h54, h29, h69, f_dead, pp_20, pp_21, pp_54, pp_29, pp_69]
  try (push_cast; ring)

lemma b_20 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 20 0 := by
  have h : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_1959
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 21 (n + 1) := by
  have h21 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 21 n := ih 21
  have h54 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 54 n := ih 54
  have h29 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 29 n := ih 29
  have h69 : (f ![2, 2, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 69 n := ih 69
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h21, h54, h29, h69, f_dead, pp_21, pp_21, pp_54, pp_29, pp_69]
  try (push_cast; ring)

lemma b_21 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 21 0 := by
  have h : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_1961
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 22 (n + 1) := by
  have h26 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h66 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 66 n := ih 66
  have h36 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 36 n := ih 36
  have h82 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 82 n := ih 82
  have h44 : (f ![0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 44 n := ih 44
  have h95 : (f ![0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 95 n := ih 95
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h26, h66, h36, h82, h44, h95, f_dead, pp_22, pp_26, pp_66, pp_36, pp_82, pp_44, pp_95]
  try (push_cast; ring)

lemma b_22 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 22 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_2916
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 23 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h27, h67, h38, h84, f_dead, pp_23, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_23 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 23 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2919
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 24 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h27, h67, h38, h84, f_dead, pp_24, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_24 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 24 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2921
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 25 (n + 1) := by
  have h26 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h66 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 66 n := ih 66
  have h36 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 36 n := ih 36
  have h82 : (f ![0, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 82 n := ih 82
  have h44 : (f ![0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 44 n := ih 44
  have h95 : (f ![0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 95 n := ih 95
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h26, h66, h36, h82, h44, h95, f_dead, pp_25, pp_26, pp_66, pp_36, pp_82, pp_44, pp_95]
  try (push_cast; ring)

lemma b_25 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 25 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_2925
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 26 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h27, h67, h38, h84, f_dead, pp_26, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_26 : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 26 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2928
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 27 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h27, h67, h38, h84, f_dead, pp_27, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_27 : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 27 0 := by
  have h : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2930
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 28 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h27, h67, h38, h84, f_dead, pp_28, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_28 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 28 0 := by
  have h : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2931
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 29 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h67 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h38 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 38 n := ih 38
  have h84 : (f ![2, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 84 n := ih 84
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h27, h67, h38, h84, f_dead, pp_29, pp_27, pp_67, pp_38, pp_84]
  try (push_cast; ring)

lemma b_29 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 29 0 := by
  have h : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_2933
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 30 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h37, h83, h45, h96, f_dead, pp_30, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_30 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 30 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3402
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 31 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h37, h83, h45, h96, f_dead, pp_31, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_31 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 31 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3403
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 32 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_32, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_32 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 32 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3405
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 33 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_33, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_33 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 33 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3406
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 34 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_34, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_34 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 34 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3407
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 35 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_35, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_35 : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 35 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3411
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 36 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_36, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_36 : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 36 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3414
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 37 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_37, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_37 : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 37 0 := by
  have h : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3415
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 38 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 37 n := ih 37
  have h83 : (f ![1, 1, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 83 n := ih 83
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h37, h83, h45, h96, f_dead, pp_38, pp_37, pp_83, pp_45, pp_96]
  try (push_cast; ring)

lemma b_38 : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 38 0 := by
  have h : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_3416
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 39 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h45, h96, f_dead, pp_39, pp_45, pp_96]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3645
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 40 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h45, h96, f_dead, pp_40, pp_45, pp_96]
  try (push_cast; ring)

lemma b_40 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 40 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3646
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 41 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h45, h96, f_dead, pp_41, pp_45, pp_96]
  try (push_cast; ring)

lemma b_41 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 41 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3648
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 42 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h45, h96, f_dead, pp_42, pp_45, pp_96]
  try (push_cast; ring)

lemma b_42 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 42 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3649
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 43 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h45, h96, f_dead, pp_43, pp_45, pp_96]
  try (push_cast; ring)

lemma b_43 : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 43 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3654
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 44 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h45, h96, f_dead, pp_44, pp_45, pp_96]
  try (push_cast; ring)

lemma b_44 : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 44 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3657
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 45 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 45 n := ih 45
  have h96 : (f ![1, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h45, h96, f_dead, pp_45, pp_45, pp_96]
  try (push_cast; ring)

lemma b_45 : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 45 0 := by
  have h : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_3658
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 46 (n + 1) := by
  have h47 : (f ![0, 0, 0, 1, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 47 n := ih 47
  have h55 : (f ![0, 0, 0, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 55 n := ih 55
  have h70 : (f ![0, 0, 0, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 70 n := ih 70
  have h85 : (f ![0, 0, 0, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 85 n := ih 85
  have h97 : (f ![0, 0, 0, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 97 n := ih 97
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h47, h55, h70, h85, h97, f_dead, pp_46, pp_47, pp_55, pp_70, pp_85, pp_97]
  try (push_cast; ring)

lemma b_46 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 46 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 21 := by exact_mod_cast fv3_3888
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 47 (n + 1) := by
  have h48 : (f ![0, 0, 2, 1, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h59 : (f ![0, 0, 2, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 59 n := ih 59
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h48, h59, f_dead, pp_47, pp_48, pp_59]
  try (push_cast; ring)

lemma b_47 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 47 0 := by
  have h : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_3915
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 48 (n + 1) := by
  have h49 : (f ![0, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 49 n := ih 49
  have h60 : (f ![0, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h49, h60, f_dead, pp_48, pp_49, pp_60]
  try (push_cast; ring)

lemma b_48 : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 48 0 := by
  have h : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_3933
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 49 (n + 1) := by
  have h50 : (f ![2, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 50 n := ih 50
  have h61 : (f ![2, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 61 n := ih 61
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h50, h61, f_dead, pp_49, pp_50, pp_61]
  try (push_cast; ring)

lemma b_49 : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 49 0 := by
  have h : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_3939
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 50 (n + 1) := by
  have h50 : (f ![2, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 50 n := ih 50
  have h61 : (f ![2, 2, 2, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 61 n := ih 61
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h50, h61, f_dead, pp_50, pp_50, pp_61]
  try (push_cast; ring)

lemma b_50 : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 50 0 := by
  have h : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_3941
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 51 (n + 1) := by
  have h56 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 56 n := ih 56
  have h71 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  have h86 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 86 n := ih 86
  have h98 : (f ![0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 98 n := ih 98
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h56, h71, h86, h98, f_dead, pp_51, pp_56, pp_71, pp_86, pp_98]
  try (push_cast; ring)

lemma b_51 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 51 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 13 := by exact_mod_cast fv3_5832
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 52 (n + 1) := by
  have h57 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 57 n := ih 57
  have h74 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 74 n := ih 74
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h57, h74, f_dead, pp_52, pp_57, pp_74]
  try (push_cast; ring)

lemma b_52 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 52 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5841
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 53 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h58, h75, f_dead, pp_53, pp_58, pp_75]
  try (push_cast; ring)

lemma b_53 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 53 0 := by
  have h : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5847
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 54 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h58, h75, f_dead, pp_54, pp_58, pp_75]
  try (push_cast; ring)

lemma b_54 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 54 0 := by
  have h : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5849
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 55 (n + 1) := by
  have h56 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 56 n := ih 56
  have h71 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  have h86 : (f ![0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 86 n := ih 86
  have h98 : (f ![0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 98 n := ih 98
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h56, h71, h86, h98, f_dead, pp_55, pp_56, pp_71, pp_86, pp_98]
  try (push_cast; ring)

lemma b_55 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 55 0 := by
  have h : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 13 := by exact_mod_cast fv3_5859
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 56 (n + 1) := by
  have h57 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 57 n := ih 57
  have h74 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 74 n := ih 74
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h57, h74, f_dead, pp_56, pp_57, pp_74]
  try (push_cast; ring)

lemma b_56 : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 56 0 := by
  have h : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5868
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 57 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h58, h75, f_dead, pp_57, pp_58, pp_75]
  try (push_cast; ring)

lemma b_57 : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 57 0 := by
  have h : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5874
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 58 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h58, h75, f_dead, pp_58, pp_58, pp_75]
  try (push_cast; ring)

lemma b_58 : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 58 0 := by
  have h : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5876
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 59 (n + 1) := by
  have h57 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 57 n := ih 57
  have h74 : (f ![0, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 74 n := ih 74
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h57, h74, f_dead, pp_59, pp_57, pp_74]
  try (push_cast; ring)

lemma b_59 : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 59 0 := by
  have h : (f ![0, 0, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5877
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 60 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h58, h75, f_dead, pp_60, pp_58, pp_75]
  try (push_cast; ring)

lemma b_60 : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 60 0 := by
  have h : (f ![0, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5883
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 61 (n + 1) := by
  have h58 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h75 : (f ![2, 2, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 75 n := ih 75
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h58, h75, f_dead, pp_61, pp_58, pp_75]
  try (push_cast; ring)

lemma b_61 : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 61 0 := by
  have h : (f ![2, 2, 2, 1, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_5885
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 62 (n + 1) := by
  have h72 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  have h87 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 87 n := ih 87
  have h99 : (f ![0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h72, h87, h99, f_dead, pp_62, pp_72, pp_87, pp_99]
  try (push_cast; ring)

lemma b_62 : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 62 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_6804
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 63 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h73, h89, f_dead, pp_63, pp_73, pp_89]
  try (push_cast; ring)

lemma b_63 : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 63 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6807
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 64 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h73, h89, f_dead, pp_64, pp_73, pp_89]
  try (push_cast; ring)

lemma b_64 : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 64 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6809
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 65 (n + 1) := by
  have h72 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  have h87 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 87 n := ih 87
  have h99 : (f ![0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h72, h87, h99, f_dead, pp_65, pp_72, pp_87, pp_99]
  try (push_cast; ring)

lemma b_65 : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 65 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_6813
  rw [h, pp_65]; try norm_num

set_option maxRecDepth 100000 in
lemma st_66 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 66 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h73, h89, f_dead, pp_66, pp_73, pp_89]
  try (push_cast; ring)

lemma b_66 : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 66 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6816
  rw [h, pp_66]; try norm_num

set_option maxRecDepth 100000 in
lemma st_67 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 67 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h73, h89, f_dead, pp_67, pp_73, pp_89]
  try (push_cast; ring)

lemma b_67 : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 67 0 := by
  have h : (f ![2, 1, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6818
  rw [h, pp_67]; try norm_num

set_option maxRecDepth 100000 in
lemma st_68 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 68 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h73, h89, f_dead, pp_68, pp_73, pp_89]
  try (push_cast; ring)

lemma b_68 : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 68 0 := by
  have h : (f ![0, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6819
  rw [h, pp_68]; try norm_num

set_option maxRecDepth 100000 in
lemma st_69 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 69 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h73, h89, f_dead, pp_69, pp_73, pp_89]
  try (push_cast; ring)

lemma b_69 : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 69 0 := by
  have h : (f ![2, 2, 1, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6821
  rw [h, pp_69]; try norm_num

set_option maxRecDepth 100000 in
lemma st_70 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 70 (n + 1) := by
  have h72 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  have h87 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 87 n := ih 87
  have h99 : (f ![0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h72, h87, h99, f_dead, pp_70, pp_72, pp_87, pp_99]
  try (push_cast; ring)

lemma b_70 : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 70 0 := by
  have h : (f ![0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_6831
  rw [h, pp_70]; try norm_num

set_option maxRecDepth 100000 in
lemma st_71 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 71 (n + 1) := by
  have h72 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  have h87 : (f ![0, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 87 n := ih 87
  have h99 : (f ![0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h72, h87, h99, f_dead, pp_71, pp_72, pp_87, pp_99]
  try (push_cast; ring)

lemma b_71 : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 71 0 := by
  have h : (f ![0, 0, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_6840
  rw [h, pp_71]; try norm_num

set_option maxRecDepth 100000 in
lemma st_72 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 72 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h73, h89, f_dead, pp_72, pp_73, pp_89]
  try (push_cast; ring)

lemma b_72 : (f ![0, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 72 0 := by
  have h : (f ![0, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6843
  rw [h, pp_72]; try norm_num

set_option maxRecDepth 100000 in
lemma st_73 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 73 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h73, h89, f_dead, pp_73, pp_73, pp_89]
  try (push_cast; ring)

lemma b_73 : (f ![2, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 73 0 := by
  have h : (f ![2, 1, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6845
  rw [h, pp_73]; try norm_num

set_option maxRecDepth 100000 in
lemma st_74 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 74 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h73, h89, f_dead, pp_74, pp_73, pp_89]
  try (push_cast; ring)

lemma b_74 : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 74 0 := by
  have h : (f ![0, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6846
  rw [h, pp_74]; try norm_num

set_option maxRecDepth 100000 in
lemma st_75 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 75 (n + 1) := by
  have h73 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 73 n := ih 73
  have h89 : (f ![2, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h73, h89, f_dead, pp_75, pp_73, pp_89]
  try (push_cast; ring)

lemma b_75 : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 75 0 := by
  have h : (f ![2, 2, 1, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_6848
  rw [h, pp_75]; try norm_num

set_option maxRecDepth 100000 in
lemma st_76 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 76 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h88, h100, f_dead, pp_76, pp_88, pp_100]
  try (push_cast; ring)

lemma b_76 : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 76 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7290
  rw [h, pp_76]; try norm_num

set_option maxRecDepth 100000 in
lemma st_77 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 77 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h88, h100, f_dead, pp_77, pp_88, pp_100]
  try (push_cast; ring)

lemma b_77 : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 77 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7291
  rw [h, pp_77]; try norm_num

set_option maxRecDepth 100000 in
lemma st_78 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 78 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_78, pp_88, pp_100]
  try (push_cast; ring)

lemma b_78 : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 78 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7293
  rw [h, pp_78]; try norm_num

set_option maxRecDepth 100000 in
lemma st_79 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 79 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_79, pp_88, pp_100]
  try (push_cast; ring)

lemma b_79 : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 79 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7294
  rw [h, pp_79]; try norm_num

set_option maxRecDepth 100000 in
lemma st_80 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 80 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_80, pp_88, pp_100]
  try (push_cast; ring)

lemma b_80 : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 80 0 := by
  have h : (f ![2, 1, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7295
  rw [h, pp_80]; try norm_num

set_option maxRecDepth 100000 in
lemma st_81 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 81 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_81, pp_88, pp_100]
  try (push_cast; ring)

lemma b_81 : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 81 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7299
  rw [h, pp_81]; try norm_num

set_option maxRecDepth 100000 in
lemma st_82 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 82 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_82, pp_88, pp_100]
  try (push_cast; ring)

lemma b_82 : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 82 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7302
  rw [h, pp_82]; try norm_num

set_option maxRecDepth 100000 in
lemma st_83 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 83 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_83, pp_88, pp_100]
  try (push_cast; ring)

lemma b_83 : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 83 0 := by
  have h : (f ![1, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7303
  rw [h, pp_83]; try norm_num

set_option maxRecDepth 100000 in
lemma st_84 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 84 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_84, pp_88, pp_100]
  try (push_cast; ring)

lemma b_84 : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 84 0 := by
  have h : (f ![2, 1, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7304
  rw [h, pp_84]; try norm_num

set_option maxRecDepth 100000 in
lemma st_85 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 85 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_85, pp_88, pp_100]
  try (push_cast; ring)

lemma b_85 : (f ![0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 85 0 := by
  have h : (f ![0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7317
  rw [h, pp_85]; try norm_num

set_option maxRecDepth 100000 in
lemma st_86 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 86 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_86, pp_88, pp_100]
  try (push_cast; ring)

lemma b_86 : (f ![0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 86 0 := by
  have h : (f ![0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7326
  rw [h, pp_86]; try norm_num

set_option maxRecDepth 100000 in
lemma st_87 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 87 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_87, pp_88, pp_100]
  try (push_cast; ring)

lemma b_87 : (f ![0, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 87 0 := by
  have h : (f ![0, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7329
  rw [h, pp_87]; try norm_num

set_option maxRecDepth 100000 in
lemma st_88 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 88 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_88, pp_88, pp_100]
  try (push_cast; ring)

lemma b_88 : (f ![1, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 88 0 := by
  have h : (f ![1, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7330
  rw [h, pp_88]; try norm_num

set_option maxRecDepth 100000 in
lemma st_89 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 89 (n + 1) := by
  have h88 : (f ![1, 1, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 88 n := ih 88
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h88, h100, f_dead, pp_89, pp_88, pp_100]
  try (push_cast; ring)

lemma b_89 : (f ![2, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 89 0 := by
  have h : (f ![2, 1, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_7331
  rw [h, pp_89]; try norm_num

set_option maxRecDepth 100000 in
lemma st_90 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 90 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h100, f_dead, pp_90, pp_100]
  try (push_cast; ring)

lemma b_90 : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 90 0 := by
  have h : (f ![0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7533
  rw [h, pp_90]; try norm_num

set_option maxRecDepth 100000 in
lemma st_91 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 91 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h100, f_dead, pp_91, pp_100]
  try (push_cast; ring)

lemma b_91 : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 91 0 := by
  have h : (f ![1, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7534
  rw [h, pp_91]; try norm_num

set_option maxRecDepth 100000 in
lemma st_92 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 92 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_92, pp_100]
  try (push_cast; ring)

lemma b_92 : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 92 0 := by
  have h : (f ![0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7536
  rw [h, pp_92]; try norm_num

set_option maxRecDepth 100000 in
lemma st_93 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 93 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_93, pp_100]
  try (push_cast; ring)

lemma b_93 : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 93 0 := by
  have h : (f ![1, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7537
  rw [h, pp_93]; try norm_num

set_option maxRecDepth 100000 in
lemma st_94 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 94 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_94, pp_100]
  try (push_cast; ring)

lemma b_94 : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 94 0 := by
  have h : (f ![0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7542
  rw [h, pp_94]; try norm_num

set_option maxRecDepth 100000 in
lemma st_95 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 95 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_95, pp_100]
  try (push_cast; ring)

lemma b_95 : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 95 0 := by
  have h : (f ![0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7545
  rw [h, pp_95]; try norm_num

set_option maxRecDepth 100000 in
lemma st_96 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 96 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_96, pp_100]
  try (push_cast; ring)

lemma b_96 : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 96 0 := by
  have h : (f ![1, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7546
  rw [h, pp_96]; try norm_num

set_option maxRecDepth 100000 in
lemma st_97 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 97 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_97, pp_100]
  try (push_cast; ring)

lemma b_97 : (f ![0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 97 0 := by
  have h : (f ![0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7560
  rw [h, pp_97]; try norm_num

set_option maxRecDepth 100000 in
lemma st_98 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 98 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_98, pp_100]
  try (push_cast; ring)

lemma b_98 : (f ![0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 98 0 := by
  have h : (f ![0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7569
  rw [h, pp_98]; try norm_num

set_option maxRecDepth 100000 in
lemma st_99 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 99 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_99, pp_100]
  try (push_cast; ring)

lemma b_99 : (f ![0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 99 0 := by
  have h : (f ![0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7572
  rw [h, pp_99]; try norm_num

set_option maxRecDepth 100000 in
lemma st_100 (n : ℕ) (ih : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 100 (n + 1) := by
  have h100 : (f ![1, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h100, f_dead, pp_100, pp_100]
  try (push_cast; ring)

lemma b_100 : (f ![1, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 100 0 := by
  have h : (f ![1, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_7573
  rw [h, pp_100]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 101, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65, b_66, b_67, b_68, b_69, b_70, b_71, b_72, b_73, b_74, b_75, b_76, b_77, b_78, b_79, b_80, b_81, b_82, b_83, b_84, b_85, b_86, b_87, b_88, b_89, b_90, b_91, b_92, b_93, b_94, b_95, b_96, b_97, b_98, b_99, b_100]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih, st_66 n ih, st_67 n ih, st_68 n ih, st_69 n ih, st_70 n ih, st_71 n ih, st_72 n ih, st_73 n ih, st_74 n ih, st_75 n ih, st_76 n ih, st_77 n ih, st_78 n ih, st_79 n ih, st_80 n ih, st_81 n ih, st_82 n ih, st_83 n ih, st_84 n ih, st_85 n ih, st_86 n ih, st_87 n ih, st_88 n ih, st_89 n ih, st_90 n ih, st_91 n ih, st_92 n ih, st_93 n ih, st_94 n ih, st_95 n ih, st_96 n ih, st_97 n ih, st_98 n ih, st_99 n ih, st_100 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 4) : ℚ) = ((2 : ℚ) / 15) * (m : ℚ) ^ 5 + ((10 : ℚ) / 3) * (m : ℚ) ^ 4 + ((106 : ℚ) / 3) * (m : ℚ) ^ 3 + ((593 : ℚ) / 3) * (m : ℚ) ^ 2 + ((8723 : ℚ) / 15) * (m : ℚ) ^ 1 + (691 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g46 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 46 m := f_closed m 46
  have g18 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 18 m := f_closed m 18
  have g51 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 51 m := f_closed m 51
  have g6 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 6 m := f_closed m 6
  have g22 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 22 m := f_closed m 22
  have g62 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 62 m := f_closed m 62
  have g2 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 2 m := f_closed m 2
  have g9 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 9 m := f_closed m 9
  have g30 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 30 m := f_closed m 30
  have g76 : (f ![0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 76 m := f_closed m 76
  have g1 : (f ![0, 0, 0, 0, 0] (m + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 1 m := f_closed m 1
  have g4 : (f ![0, 0, 0, 0, 0] (m + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 4 m := f_closed m 4
  have g14 : (f ![0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 14 m := f_closed m 14
  have g39 : (f ![0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 39 m := f_closed m 39
  have g90 : (f ![0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 90 m := f_closed m 90
  rw [show m + 4 = (m + 3) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 5 => (0 : Fin 3)) = ![0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g46, g18, g51, g6, g22, g62, g2, g9, g30, g76, g1, g4, g14, g39, g90, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_46, pp_18, pp_51, pp_6, pp_22, pp_62, pp_2, pp_9, pp_30, pp_76, pp_1, pp_4, pp_14, pp_39, pp_90]
  ring

lemma aS1 : (a 1 : ℚ) = 16 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 5 => (0 : Fin 3)) = ![0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 86 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 5 => (0 : Fin 3)) = ![0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 5 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_3888, fv1_1944, fv1_5832, fv1_972, fv1_2916, fv1_6804, fv1_486, fv1_1458, fv1_3402, fv1_7290, fv1_243, fv1_729, fv1_1701, fv1_3645, fv1_7533]
  norm_num

lemma aS3 : (a 3 : ℚ) = 275 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 5 => (0 : Fin 3)) = ![0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 5 → Fin 3) (r : R), (f c 2 r : ℚ) = ((f c 2 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv2_0, fv2_3888, fv2_1944, fv2_5832, fv2_972, fv2_2916, fv2_6804, fv2_486, fv2_1458, fv2_3402, fv2_7290, fv2_243, fv2_729, fv2_1701, fv2_3645, fv2_7533]
  norm_num

lemma av (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((2 : ℚ) / 3) * (n : ℚ) ^ 4 + ((10 : ℚ) / 3) * (n : ℚ) ^ 3 + ((25 : ℚ) / 3) * (n : ℚ) ^ 2 + ((203 : ℚ) / 15) * (n : ℚ) ^ 1 + (-17 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [aS3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
      16 - 10 * X - X ^ 2 + 11 * X ^ 3 + 8 * X ^ 4 - 10 * X ^ 5 + X ^ 6 + X ^ 7) ∧
    (∀ n > 8, (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - 1 * a (n - 6)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-6 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (15 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-20 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (15 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-6 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (16 - 10 * X - X ^ 2 + 11 * X ^ 3 + 8 * X ^ 4 - 10 * X ^ 5 + X ^ 6 + X ^ 7 : PowerSeries ℚ) =
        C (16 : ℚ) * X ^ 0 + C (-10 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (11 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-10 : ℚ) * X ^ 5 + C (1 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 16 := aS1
    have e2 : (a 2 : ℚ) = 86 := aS2
    have e3 : (a 3 : ℚ) = 275 := aS3
    have e4 : (a 4 : ℚ) = 691 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 1509 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 2985 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 5471 := by rw [av 7 (by norm_num)]; norm_num
    have e8 : (a 8 : ℚ) = 9431 := by rw [av 8 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 8 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6, e7, e8] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 8 := ⟨c - 8, by omega⟩
      simp only [show m + 8 - 0 = m + 8 by omega, show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show 0 ≤ m + 8 by omega, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega, show 4 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 8 + 1) (by omega), av (m + 7 + 1) (by omega), av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega]
    qify
    rw [av (m + 9) (by omega), av (m + 8) (by omega), av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega)]
    push_cast; ring

end OMA.P_oeis_a224143

theorem OMA.solution : type_of% @OMA.S_oeis_a224143.main := OMA.P_oeis_a224143.full
