import OMAStatements.S_oeis_a224040
import Mathlib

/-!
# oeis-a224040: counting the n X 4 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 3 it is an explicit polynomial, checked by induction over the
50 states (c, r) whose top row is allowed, from exact values at n = 1..3. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A224040, https://oeis.org/A224040.
-/
namespace OMA.P_oeis_a224040

open OMA.S_oeis_a224040

def adj (r s : Fin 4 → Fin 2) : Prop := (∀ j : Fin 4, r j ≤ s j) ∧ (∀ i : Fin 3, r i.castSucc ≤ s i.succ)

instance (r s : Fin 4 → Fin 2) : Decidable (adj r s) := by unfold adj; infer_instance

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

lemma sumk {M : Type*} [AddCommMonoid M] (g : R → M) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, g ![y0, y1, y2, y3] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2], fun f => (f 0, f 1, f 2, f 3), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def adiagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 4 then r ⟨j, h⟩ :: (if j = 0 then [] else adiagF l (j - 1)) else []

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

lemma forall_drop (P : List R → Prop) (l : List R) :
    (∀ i, P (l.drop i)) ↔ P l ∧ ∀ i, P (l.drop (i + 1)) := by
  constructor
  · intro h; exact ⟨h 0, fun i => h (i + 1)⟩
  · rintro ⟨h0, h⟩ i; cases i with
    | zero => exact h0
    | succ i => exact h i

lemma fdrop (l : List R) : (∀ i, Acc 0 (adiagF (l.drop i) 3) = true) ↔
    Acc 0 (adiagF l 3) = true ∧ ∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true :=
  forall_drop (fun L => Acc 0 (adiagF L 3) = true) l

lemma ltK (P : ℕ → Prop) : (∀ j < 4, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3⟩ j hj
    interval_cases j <;> assumption

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 4) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 4 → Fin 3) (r : R) : Prop := okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true

instance (c : Fin 4 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 4 → Fin 3) (l : List R) : Prop :=
  Acc (c 0) (adiagF l 0) = true ∧ Acc (c 1) (adiagF l 1) = true ∧ Acc (c 2) (adiagF l 2) = true ∧ Acc (c 3) (adiagF l 3) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 3)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 3) = true by simp only [adiag_map, uniAcc], fdrop]
  simp only [adiag_map, uniAcc, ltK, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    ]
  tauto

lemma Q_single (c : Fin 4 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF]

lemma Q_cons (c : Fin 4 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0] (s :: l) := by
  unfold Q okT
  simp only [Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, ad_cons3, List.drop_succ_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l)]
  simp only [ad_cons3, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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

noncomputable def f (c : Fin 4 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 4 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 4 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 4 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3] (n + 1) ![r0, r1, r2, r3] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3] (n + 1) ![r0, r1, r2, r3] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_648 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_324 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_972 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_162 : (f ![0, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_810 : (f ![0, 0, 0, 0] 1 ![0, 1, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_486 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1134 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_81 : (f ![0, 0, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_729 : (f ![0, 0, 0, 0] 1 ![1, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_405 : (f ![0, 0, 0, 0] 1 ![1, 0, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1053 : (f ![0, 0, 0, 0] 1 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_243 : (f ![0, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_891 : (f ![0, 0, 0, 0] 1 ![1, 1, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_567 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1215 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_657 : (f ![0, 0, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_981 : (f ![0, 0, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_819 : (f ![0, 0, 1, 0] 1 ![0, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1143 : (f ![0, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_738 : (f ![0, 0, 1, 0] 1 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1062 : (f ![0, 0, 1, 0] 1 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_900 : (f ![0, 0, 1, 0] 1 ![1, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1224 : (f ![0, 0, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_975 : (f ![0, 1, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1137 : (f ![0, 1, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1056 : (f ![0, 1, 0, 0] 1 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1218 : (f ![0, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_984 : (f ![0, 1, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1146 : (f ![0, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1065 : (f ![0, 1, 1, 0] 1 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1227 : (f ![0, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_663 : (f ![0, 2, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_987 : (f ![0, 2, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_744 : (f ![0, 2, 1, 0] 1 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1068 : (f ![0, 2, 1, 0] 1 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_487 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1135 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_568 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1216 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1144 : (f ![1, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1225 : (f ![1, 0, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1138 : (f ![1, 1, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1219 : (f ![1, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1147 : (f ![1, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1228 : (f ![1, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_986 : (f ![2, 1, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1148 : (f ![2, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_665 : (f ![2, 2, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_989 : (f ![2, 2, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 55 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_810, fv1_486, fv1_1134, fv1_81, fv1_729, fv1_405, fv1_1053, fv1_243, fv1_891, fv1_567, fv1_1215]
  simp +decide only []
  try norm_num

lemma fv2_648 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_657, fv1_981, fv1_819, fv1_1143, fv1_738, fv1_1062, fv1_900, fv1_1224]
  simp +decide only []
  try norm_num

lemma fv2_324 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_975, fv1_1137, fv1_1056, fv1_1218]
  simp +decide only []
  try norm_num

lemma fv2_972 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_984, fv1_1146, fv1_1065, fv1_1227]
  simp +decide only []
  try norm_num

lemma fv2_162 : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_487, fv1_1135, fv1_568, fv1_1216]
  simp +decide only []
  try norm_num

lemma fv2_810 : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1144, fv1_1225]
  simp +decide only []
  try norm_num

lemma fv2_486 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1138, fv1_1219]
  simp +decide only []
  try norm_num

lemma fv2_1134 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_81 : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_243, fv1_891, fv1_567, fv1_1215]
  simp +decide only []
  try norm_num

lemma fv2_729 : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_900, fv1_1224]
  simp +decide only []
  try norm_num

lemma fv2_405 : (f ![0, 0, 0, 0] 2 ![1, 0, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1218]
  simp +decide only []
  try norm_num

lemma fv2_1053 : (f ![0, 0, 0, 0] 2 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1227]
  simp +decide only []
  try norm_num

lemma fv2_243 : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_568, fv1_1216]
  simp +decide only []
  try norm_num

lemma fv2_891 : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1225]
  simp +decide only []
  try norm_num

lemma fv2_567 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1219]
  simp +decide only []
  try norm_num

lemma fv2_1215 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_657 : (f ![0, 0, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_663, fv1_987, fv1_744, fv1_1068, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_981 : (f ![0, 0, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_984, fv1_1146, fv1_1065, fv1_1227]
  simp +decide only []
  try norm_num

lemma fv2_819 : (f ![0, 0, 1, 0] 2 ![0, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1143 : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_738 : (f ![0, 0, 1, 0] 2 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1062 : (f ![0, 0, 1, 0] 2 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1227]
  simp +decide only []
  try norm_num

lemma fv2_900 : (f ![0, 0, 1, 0] 2 ![1, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1224 : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_975 : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1137 : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1056 : (f ![0, 1, 0, 0] 2 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1218 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_984 : (f ![0, 1, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1146 : (f ![0, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1065 : (f ![0, 1, 1, 0] 2 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1227 : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_663 : (f ![0, 2, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_665, fv1_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_987 : (f ![0, 2, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_744 : (f ![0, 2, 1, 0] 2 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1068 : (f ![0, 2, 1, 0] 2 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_487 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1138, fv1_1219]
  simp +decide only []
  try norm_num

lemma fv2_1135 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_568 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1219]
  simp +decide only []
  try norm_num

lemma fv2_1216 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1144 : (f ![1, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1225 : (f ![1, 0, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1138 : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1219 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1147 : (f ![1, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_1228 : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_986 : (f ![2, 1, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1148 : (f ![2, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228]
  simp +decide only []
  try norm_num

lemma fv2_665 : (f ![2, 2, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_665, fv1_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_989 : (f ![2, 2, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_0 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 105 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_0, fv2_648, fv2_324, fv2_972, fv2_162, fv2_810, fv2_486, fv2_1134, fv2_81, fv2_729, fv2_405, fv2_1053, fv2_243, fv2_891, fv2_567, fv2_1215]
  simp +decide only []
  try norm_num

lemma fv3_648 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_657, fv2_981, fv2_819, fv2_1143, fv2_738, fv2_1062, fv2_900, fv2_1224]
  simp +decide only []
  try norm_num

lemma fv3_324 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_975, fv2_1137, fv2_1056, fv2_1218]
  simp +decide only []
  try norm_num

lemma fv3_972 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_984, fv2_1146, fv2_1065, fv2_1227]
  simp +decide only []
  try norm_num

lemma fv3_162 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_487, fv2_1135, fv2_568, fv2_1216]
  simp +decide only []
  try norm_num

lemma fv3_810 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1144, fv2_1225]
  simp +decide only []
  try norm_num

lemma fv3_486 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1138, fv2_1219]
  simp +decide only []
  try norm_num

lemma fv3_1134 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_81 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_243, fv2_891, fv2_567, fv2_1215]
  simp +decide only []
  try norm_num

lemma fv3_729 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_900, fv2_1224]
  simp +decide only []
  try norm_num

lemma fv3_405 : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1218]
  simp +decide only []
  try norm_num

lemma fv3_1053 : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1227]
  simp +decide only []
  try norm_num

lemma fv3_243 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_568, fv2_1216]
  simp +decide only []
  try norm_num

lemma fv3_891 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1225]
  simp +decide only []
  try norm_num

lemma fv3_567 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1219]
  simp +decide only []
  try norm_num

lemma fv3_1215 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_657 : (f ![0, 0, 1, 0] 3 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_663, fv2_987, fv2_744, fv2_1068, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_981 : (f ![0, 0, 1, 0] 3 ![0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_984, fv2_1146, fv2_1065, fv2_1227]
  simp +decide only []
  try norm_num

lemma fv3_819 : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1143 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_738 : (f ![0, 0, 1, 0] 3 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1062 : (f ![0, 0, 1, 0] 3 ![1, 0, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1227]
  simp +decide only []
  try norm_num

lemma fv3_900 : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1224 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_975 : (f ![0, 1, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv2_986, fv2_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1137 : (f ![0, 1, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1056 : (f ![0, 1, 0, 0] 3 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1218 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_984 : (f ![0, 1, 1, 0] 3 ![0, 0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_986, fv2_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1146 : (f ![0, 1, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1065 : (f ![0, 1, 1, 0] 3 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1227 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_663 : (f ![0, 2, 1, 0] 3 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_665, fv2_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_987 : (f ![0, 2, 1, 0] 3 ![0, 0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_986, fv2_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_744 : (f ![0, 2, 1, 0] 3 ![1, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1068 : (f ![0, 2, 1, 0] 3 ![1, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_487 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1138, fv2_1219]
  simp +decide only []
  try norm_num

lemma fv3_1135 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_568 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1219]
  simp +decide only []
  try norm_num

lemma fv3_1216 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1144 : (f ![1, 0, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1225 : (f ![1, 0, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1138 : (f ![1, 1, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1219 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1147 : (f ![1, 1, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_1228 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_986 : (f ![2, 1, 1, 0] 3 ![0, 0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_986, fv2_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1148 : (f ![2, 1, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1147, fv2_1228]
  simp +decide only []
  try norm_num

lemma fv3_665 : (f ![2, 2, 1, 0] 3 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_665, fv2_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_989 : (f ![2, 2, 1, 0] 3 ![0, 0, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_986, fv2_1148, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 50 → Fin 4 → Fin 3 := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 2, 1, 0], ![2, 2, 1, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 2, 1, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![2, 1, 1, 0], ![0, 2, 1, 0], ![2, 2, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 2, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![2, 1, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0]]

set_option maxRecDepth 100000 in
def rs : Fin 50 → R := ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![1, 0, 0, 1], ![1, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1], ![1, 1, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![1, 0, 1, 1], ![1, 0, 1, 1], ![1, 0, 1, 1], ![1, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 50 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((191 : ℚ) / 24) * (n : ℚ) ^ 2 + ((217 : ℚ) / 4) * (n : ℚ) ^ 1 + (105 : ℚ) * (n : ℚ) ^ 0, fun n => (5 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (14 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((3 : ℚ) / 4) * (n : ℚ) ^ 3 + ((191 : ℚ) / 24) * (n : ℚ) ^ 2 + ((217 : ℚ) / 4) * (n : ℚ) ^ 1 + (105 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = (2 : ℚ) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (14 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h10 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 10 n := ih 10
  have h4 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 4 n := ih 4
  have h21 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 21 n := ih 21
  have h2 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 2 n := ih 2
  have h17 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 0, 1] : ℚ) = PP 17 n := ih 17
  have h6 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 6 n := ih 6
  have h33 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h1 : (f ![0, 0, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h14 : (f ![0, 0, 0, 0] (n + 3) ![1, 0, 0, 1] : ℚ) = PP 14 n := ih 14
  have h5 : (f ![0, 0, 0, 0] (n + 3) ![1, 0, 1, 0] : ℚ) = PP 5 n := ih 5
  have h28 : (f ![0, 0, 0, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 28 n := ih 28
  have h3 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 3 n := ih 3
  have h19 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 0, 1] : ℚ) = PP 19 n := ih 19
  have h8 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 8 n := ih 8
  have h42 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h10, h4, h21, h2, h17, h6, h33, h1, h14, h5, h28, h3, h19, h8, h42, pp_0, pp_0, pp_10, pp_4, pp_21, pp_2, pp_17, pp_6, pp_33, pp_1, pp_14, pp_5, pp_28, pp_3, pp_19, pp_8, pp_42]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 105 := by exact_mod_cast fv3_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h3 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 3 n := ih 3
  have h19 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 0, 1] : ℚ) = PP 19 n := ih 19
  have h8 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 8 n := ih 8
  have h42 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h3, h19, h8, h42, pp_1, pp_3, pp_19, pp_8, pp_42]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 5 := by exact_mod_cast fv3_81
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h7 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 7 n := ih 7
  have h34 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 34 n := ih 34
  have h9 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 9 n := ih 9
  have h43 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h7, h34, h9, h43, pp_2, pp_7, pp_34, pp_9, pp_43]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_162
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h9 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 9 n := ih 9
  have h43 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h9, h43, pp_3, pp_9, pp_43]
  try (push_cast; ring)

lemma b_3 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = 2 := by exact_mod_cast fv3_243
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 4 (n + 1) := by
  have h22 : (f ![0, 1, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 22 n := ih 22
  have h35 : (f ![0, 1, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 35 n := ih 35
  have h29 : (f ![0, 1, 0, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 29 n := ih 29
  have h44 : (f ![0, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h22, h35, h29, h44, pp_4, pp_22, pp_35, pp_29, pp_44]
  try (push_cast; ring)

lemma b_4 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 4 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_324
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 0, 1, 0] : ℚ) = PP 5 (n + 1) := by
  have h44 : (f ![0, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h44, pp_5, pp_44]
  try (push_cast; ring)

lemma b_5 : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 0] : ℚ) = PP 5 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 0] : ℚ) = 1 := by exact_mod_cast fv3_405
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 6 (n + 1) := by
  have h36 : (f ![1, 1, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 36 n := ih 36
  have h45 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h36, h45, pp_6, pp_36, pp_45]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_486
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 7 (n + 1) := by
  have h36 : (f ![1, 1, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 36 n := ih 36
  have h45 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h36, h45, pp_7, pp_36, pp_45]
  try (push_cast; ring)

lemma b_7 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 7 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_487
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 8 (n + 1) := by
  have h45 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h45, pp_8, pp_45]
  try (push_cast; ring)

lemma b_8 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 8 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 1 := by exact_mod_cast fv3_567
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 9 (n + 1) := by
  have h45 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h45, pp_9, pp_45]
  try (push_cast; ring)

lemma b_9 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 9 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 1 := by exact_mod_cast fv3_568
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 10 (n + 1) := by
  have h11 : (f ![0, 0, 1, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 11 n := ih 11
  have h23 : (f ![0, 0, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 23 n := ih 23
  have h18 : (f ![0, 0, 1, 0] (n + 3) ![0, 1, 0, 1] : ℚ) = PP 18 n := ih 18
  have h37 : (f ![0, 0, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h15 : (f ![0, 0, 1, 0] (n + 3) ![1, 0, 0, 1] : ℚ) = PP 15 n := ih 15
  have h30 : (f ![0, 0, 1, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 30 n := ih 30
  have h20 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 0, 1] : ℚ) = PP 20 n := ih 20
  have h46 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 46 n := ih 46
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h11, h23, h18, h37, h15, h30, h20, h46, pp_10, pp_11, pp_23, pp_18, pp_37, pp_15, pp_30, pp_20, pp_46]
  try (push_cast; ring)

lemma b_10 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 10 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 14 := by exact_mod_cast fv3_648
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 11 (n + 1) := by
  have h12 : (f ![0, 2, 1, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 12 n := ih 12
  have h26 : (f ![0, 2, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 26 n := ih 26
  have h16 : (f ![0, 2, 1, 0] (n + 3) ![1, 0, 0, 1] : ℚ) = PP 16 n := ih 16
  have h32 : (f ![0, 2, 1, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 32 n := ih 32
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h12, h26, h16, h32, f_dead, pp_11, pp_12, pp_26, pp_16, pp_32]
  try (push_cast; ring)

lemma b_11 : (f ![0, 0, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 11 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_657
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 12 (n + 1) := by
  have h13 : (f ![2, 2, 1, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 13 n := ih 13
  have h27 : (f ![2, 2, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h13, h27, f_dead, pp_12, pp_13, pp_27]
  try (push_cast; ring)

lemma b_12 : (f ![0, 2, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 12 0 := by
  have h : (f ![0, 2, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_663
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 13 (n + 1) := by
  have h13 : (f ![2, 2, 1, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 13 n := ih 13
  have h27 : (f ![2, 2, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h13, h27, f_dead, pp_13, pp_13, pp_27]
  try (push_cast; ring)

lemma b_13 : (f ![2, 2, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 13 0 := by
  have h : (f ![2, 2, 1, 0] 3 ![0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_665
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 1] : ℚ) = PP 14 (n + 1) := by
  have h20 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 0, 1] : ℚ) = PP 20 n := ih 20
  have h46 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 46 n := ih 46
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h20, h46, pp_14, pp_20, pp_46]
  try (push_cast; ring)

lemma b_14 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 1] : ℚ) = PP 14 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_729
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 0, 0, 1] : ℚ) = PP 15 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, f_dead, pp_15]
  try (push_cast; ring)

lemma b_15 : (f ![0, 0, 1, 0] 3 ![1, 0, 0, 1] : ℚ) = PP 15 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_738
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 3 + 1) ![1, 0, 0, 1] : ℚ) = PP 16 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_16]
  try (push_cast; ring)

lemma b_16 : (f ![0, 2, 1, 0] 3 ![1, 0, 0, 1] : ℚ) = PP 16 0 := by
  have h : (f ![0, 2, 1, 0] 3 ![1, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_744
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 1] : ℚ) = PP 17 (n + 1) := by
  have h38 : (f ![1, 0, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  have h47 : (f ![1, 0, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 47 n := ih 47
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h38, h47, pp_17, pp_38, pp_47]
  try (push_cast; ring)

lemma b_17 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 1] : ℚ) = PP 17 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_810
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 1, 0, 1] : ℚ) = PP 18 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, f_dead, pp_18]
  try (push_cast; ring)

lemma b_18 : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 1] : ℚ) = PP 18 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_819
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 1] : ℚ) = PP 19 (n + 1) := by
  have h47 : (f ![1, 0, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 47 n := ih 47
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h47, pp_19, pp_47]
  try (push_cast; ring)

lemma b_19 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 1] : ℚ) = PP 19 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_891
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 1, 0, 1] : ℚ) = PP 20 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, f_dead, pp_20]
  try (push_cast; ring)

lemma b_20 : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 1] : ℚ) = PP 20 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_900
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 21 (n + 1) := by
  have h24 : (f ![0, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 24 n := ih 24
  have h39 : (f ![0, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 39 n := ih 39
  have h31 : (f ![0, 1, 1, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 31 n := ih 31
  have h48 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h24, h39, h31, h48, pp_21, pp_24, pp_39, pp_31, pp_48]
  try (push_cast; ring)

lemma b_21 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 21 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_972
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 22 (n + 1) := by
  have h25 : (f ![2, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h41 : (f ![2, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h25, h41, f_dead, pp_22, pp_25, pp_41]
  try (push_cast; ring)

lemma b_22 : (f ![0, 1, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 22 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_975
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 23 (n + 1) := by
  have h24 : (f ![0, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 24 n := ih 24
  have h39 : (f ![0, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 39 n := ih 39
  have h31 : (f ![0, 1, 1, 0] (n + 3) ![1, 0, 1, 1] : ℚ) = PP 31 n := ih 31
  have h48 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h24, h39, h31, h48, pp_23, pp_24, pp_39, pp_31, pp_48]
  try (push_cast; ring)

lemma b_23 : (f ![0, 0, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 23 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_981
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 24 (n + 1) := by
  have h25 : (f ![2, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h41 : (f ![2, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h25, h41, f_dead, pp_24, pp_25, pp_41]
  try (push_cast; ring)

lemma b_24 : (f ![0, 1, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 24 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_984
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 25 (n + 1) := by
  have h25 : (f ![2, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h41 : (f ![2, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h25, h41, f_dead, pp_25, pp_25, pp_41]
  try (push_cast; ring)

lemma b_25 : (f ![2, 1, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 25 0 := by
  have h : (f ![2, 1, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_986
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 26 (n + 1) := by
  have h25 : (f ![2, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h41 : (f ![2, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h25, h41, f_dead, pp_26, pp_25, pp_41]
  try (push_cast; ring)

lemma b_26 : (f ![0, 2, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 26 0 := by
  have h : (f ![0, 2, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_987
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 27 (n + 1) := by
  have h25 : (f ![2, 1, 1, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h41 : (f ![2, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h25, h41, f_dead, pp_27, pp_25, pp_41]
  try (push_cast; ring)

lemma b_27 : (f ![2, 2, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 27 0 := by
  have h : (f ![2, 2, 1, 0] 3 ![0, 0, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_989
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 0, 1, 1] : ℚ) = PP 28 (n + 1) := by
  have h48 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h48, pp_28, pp_48]
  try (push_cast; ring)

lemma b_28 : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 1] : ℚ) = PP 28 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 0, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1053
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 0, 1, 1] : ℚ) = PP 29 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, f_dead, pp_29]
  try (push_cast; ring)

lemma b_29 : (f ![0, 1, 0, 0] 3 ![1, 0, 1, 1] : ℚ) = PP 29 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1056
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 0, 1, 1] : ℚ) = PP 30 (n + 1) := by
  have h48 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 48 n := ih 48
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h48, pp_30, pp_48]
  try (push_cast; ring)

lemma b_30 : (f ![0, 0, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = PP 30 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1062
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![1, 0, 1, 1] : ℚ) = PP 31 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, f_dead, pp_31]
  try (push_cast; ring)

lemma b_31 : (f ![0, 1, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = PP 31 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1065
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 3 + 1) ![1, 0, 1, 1] : ℚ) = PP 32 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_32]
  try (push_cast; ring)

lemma b_32 : (f ![0, 2, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = PP 32 0 := by
  have h : (f ![0, 2, 1, 0] 3 ![1, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1068
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 33 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h40, h49, pp_33, pp_40, pp_49]
  try (push_cast; ring)

lemma b_33 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 33 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1134
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 34 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h40, h49, pp_34, pp_40, pp_49]
  try (push_cast; ring)

lemma b_34 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 34 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1135
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 35 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_35, pp_40, pp_49]
  try (push_cast; ring)

lemma b_35 : (f ![0, 1, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 35 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1137
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 36 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_36, pp_40, pp_49]
  try (push_cast; ring)

lemma b_36 : (f ![1, 1, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 36 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1138
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 37 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_37, pp_40, pp_49]
  try (push_cast; ring)

lemma b_37 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 37 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1143
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 38 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_38, pp_40, pp_49]
  try (push_cast; ring)

lemma b_38 : (f ![1, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 38 0 := by
  have h : (f ![1, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1144
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 39 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_39, pp_40, pp_49]
  try (push_cast; ring)

lemma b_39 : (f ![0, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 39 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1146
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 40 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_40, pp_40, pp_49]
  try (push_cast; ring)

lemma b_40 : (f ![1, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 40 0 := by
  have h : (f ![1, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1147
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 41 (n + 1) := by
  have h40 : (f ![1, 1, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h40, h49, pp_41, pp_40, pp_49]
  try (push_cast; ring)

lemma b_41 : (f ![2, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 41 0 := by
  have h : (f ![2, 1, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1148
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 42 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h49, pp_42, pp_49]
  try (push_cast; ring)

lemma b_42 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 42 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1215
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 43 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h49, pp_43, pp_49]
  try (push_cast; ring)

lemma b_43 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 43 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1216
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 44 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_44, pp_49]
  try (push_cast; ring)

lemma b_44 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 44 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1218
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 45 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_45, pp_49]
  try (push_cast; ring)

lemma b_45 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 45 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1219
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 46 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_46, pp_49]
  try (push_cast; ring)

lemma b_46 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 46 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1224
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 47 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_47, pp_49]
  try (push_cast; ring)

lemma b_47 : (f ![1, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 47 0 := by
  have h : (f ![1, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1225
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 48 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_48, pp_49]
  try (push_cast; ring)

lemma b_48 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 48 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1227
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 49 (n + 1) := by
  have h49 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h49, pp_49, pp_49]
  try (push_cast; ring)

lemma b_49 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 49 0 := by
  have h : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1228
  rw [h, pp_49]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 50, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 4) : ℚ) = ((1 : ℚ) / 24) * (m : ℚ) ^ 4 + ((11 : ℚ) / 12) * (m : ℚ) ^ 3 + ((251 : ℚ) / 24) * (m : ℚ) ^ 2 + ((871 : ℚ) / 12) * (m : ℚ) ^ 1 + (168 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g10 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 0, 1] : ℚ) = PP 10 m := f_closed m 10
  have g4 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 1, 0] : ℚ) = PP 4 m := f_closed m 4
  have g21 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 1, 1] : ℚ) = PP 21 m := f_closed m 21
  have g2 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 0, 0] : ℚ) = PP 2 m := f_closed m 2
  have g17 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 0, 1] : ℚ) = PP 17 m := f_closed m 17
  have g6 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 1, 0] : ℚ) = PP 6 m := f_closed m 6
  have g33 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 1, 1] : ℚ) = PP 33 m := f_closed m 33
  have g1 : (f ![0, 0, 0, 0] (m + 3) ![1, 0, 0, 0] : ℚ) = PP 1 m := f_closed m 1
  have g14 : (f ![0, 0, 0, 0] (m + 3) ![1, 0, 0, 1] : ℚ) = PP 14 m := f_closed m 14
  have g5 : (f ![0, 0, 0, 0] (m + 3) ![1, 0, 1, 0] : ℚ) = PP 5 m := f_closed m 5
  have g28 : (f ![0, 0, 0, 0] (m + 3) ![1, 0, 1, 1] : ℚ) = PP 28 m := f_closed m 28
  have g3 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 0, 0] : ℚ) = PP 3 m := f_closed m 3
  have g19 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 0, 1] : ℚ) = PP 19 m := f_closed m 19
  have g8 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 1, 0] : ℚ) = PP 8 m := f_closed m 8
  have g42 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 1, 1] : ℚ) = PP 42 m := f_closed m 42
  rw [show m + 4 = (m + 3) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g10, g4, g21, g2, g17, g6, g33, g1, g14, g5, g28, g3, g19, g8, g42]
  simp only [pp_0, pp_10, pp_4, pp_21, pp_2, pp_17, pp_6, pp_33, pp_1, pp_14, pp_5, pp_28, pp_3, pp_19, pp_8, pp_42]
  ring

lemma aS1 : (a 1 : ℚ) = 16 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, if_true]
  norm_num

lemma aS2 : (a 2 : ℚ) = 55 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 4 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_810, fv1_486, fv1_1134, fv1_81, fv1_729, fv1_405, fv1_1053, fv1_243, fv1_891, fv1_567, fv1_1215]
  norm_num

lemma aS3 : (a 3 : ℚ) = 105 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 4 → Fin 3) (r : R), (f c 2 r : ℚ) = ((f c 2 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, fv2_0, fv2_648, fv2_324, fv2_972, fv2_162, fv2_810, fv2_486, fv2_1134, fv2_81, fv2_729, fv2_405, fv2_1053, fv2_243, fv2_891, fv2_567, fv2_1215]
  norm_num

lemma av (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((83 : ℚ) / 24) * (n : ℚ) ^ 2 + ((89 : ℚ) / 4) * (n : ℚ) ^ 1 + (-3 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [aS3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 + 3 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (16 - 25 * X - 10 * X ^ 2 + 33 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 + 3 * X ^ 6 : PowerSeries ℚ) =
        C (16 : ℚ) * X ^ 0 + C (-25 : ℚ) * X ^ 1 + C (-10 : ℚ) * X ^ 2 + C (33 : ℚ) * X ^ 3 + C (-8 : ℚ) * X ^ 4 + C (-8 : ℚ) * X ^ 5 + C (3 : ℚ) * X ^ 6 by
      simp only [map_neg, map_ofNat, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 16 := aS1
    have e2 : (a 2 : ℚ) = 55 := aS2
    have e3 : (a 3 : ℚ) = 105 := aS3
    have e4 : (a 4 : ℚ) = 168 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 252 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 363 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 508 := by rw [av 7 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 7 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6, e7] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 7 := ⟨c - 7, by omega⟩
      simp only [show m + 7 - 0 = m + 7 by omega, show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show 0 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 7 + 1) (by omega), av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega]
    qify
    rw [av (m + 8) (by omega), av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega)]
    push_cast; ring

end OMA.P_oeis_a224040

theorem OMA.solution : type_of% @OMA.S_oeis_a224040.main := OMA.P_oeis_a224040.full
