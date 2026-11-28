import OMAStatements.S_oeis_a223834
import Mathlib

/-!
# oeis-a223834: counting the n X 4 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 2 it is an explicit polynomial, checked by induction over the
66 states (c, r) whose top row is allowed, from exact values at n = 1..2. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223834, https://oeis.org/A223834.
-/
namespace OMA.P_oeis_a223834

open OMA.S_oeis_a223834

def adj (r s : Fin 4 → Fin 2) : Prop := ∀ j : Fin 4, r j ≤ s j

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

def diagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 4 then r ⟨j, h⟩ :: diagF l (j + 1) else []

lemma diag_map (l : List R) (j : ℕ) :
    diagFrom l j = (diagF l j).map (fun x : Fin 2 => (x : ℕ)) := by
  induction l generalizing j with
  | nil => simp [diagFrom, diagF]
  | cons r l ih => unfold diagFrom diagF; split_ifs <;> simp [ih]

lemma dg_cons0 (r : R) (l : List R) : diagF (r :: l) 0 = r 0 :: diagF l 1 := by
  simp [diagF]

lemma dg_cons1 (r : R) (l : List R) : diagF (r :: l) 1 = r 1 :: diagF l 2 := by
  simp [diagF]

lemma dg_cons2 (r : R) (l : List R) : diagF (r :: l) 2 = r 2 :: diagF l 3 := by
  simp [diagF]

lemma dg_cons3 (r : R) (l : List R) : diagF (r :: l) 3 = [r 3] := by
  cases l <;> simp [diagF]

lemma gdrop (l : List R) : (∀ i, Acc 0 (diagF (l.drop i) 0) = true) ↔
    Acc 0 (diagF l 0) = true ∧ ∀ i, Acc 0 (diagF (l.drop (i + 1)) 0) = true :=
  forall_drop (fun L => Acc 0 (diagF L 0) = true) l

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 4) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 8 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true ∧ okb (c 4) (r 0) = true ∧ okb (c 5) (r 1) = true ∧ okb (c 6) (r 2) = true ∧ okb (c 7) (r 3) = true

instance (c : Fin 8 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 8 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ Acc (c 0) (adiagF l 0) = true ∧ Acc (c 1) (adiagF l 1) = true ∧ Acc (c 2) (adiagF l 2) = true ∧ Acc (c 3) (adiagF l 3) = true ∧ Acc (c 4) (diagF l 0) = true ∧ Acc (c 5) (diagF l 1) = true ∧ Acc (c 6) (diagF l 2) = true ∧ Acc (c 7) (diagF l 3) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true) ∧ (∀ i, Acc 0 (diagF (l.drop (i + 1)) 0) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 3)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 3) = true by simp only [adiag_map, uniAcc], fdrop]
  rw [show (∀ i, Unimodal (diagFrom (l.drop i) 0)) ↔ ∀ i, Acc 0 (diagF (l.drop i) 0) = true by simp only [diag_map, uniAcc], gdrop]
  simp only [rowUni, adiag_map, uniAcc, ltK, diag_map, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    ]
  tauto

lemma Q_single (c : Fin 8 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF, diagF]

lemma Q_cons (c : Fin 8 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0, 0, dl (c 4) (r 0), dl (c 5) (r 1), dl (c 6) (r 2)] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, ad_cons3, List.drop_succ_cons, dg_cons0, dg_cons1, dg_cons2, dg_cons3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l), gdrop (s :: l)]
  simp only [ad_cons3, dg_cons0, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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

noncomputable def f (c : Fin 8 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 8 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 8 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0, 0, dl (c 4) (r 0), dl (c 5) (r 1), dl (c 6) (r 2)] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 8 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 c4 c5 c6 c7 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7] (n + 1) ![r0, r1, r2, r3] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0, 0, dl (c4) (r0), dl (c5) (r1), dl (c6) (r2)] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 c4 c5 c6 c7 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7] (n + 1) ![r0, r1, r2, r3] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0, 0, dl (c4) (r0), dl (c5) (r1), dl (c6) (r2)] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_52488 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_26244 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78732 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_13122 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_39366 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_91854 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6561 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_19683 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_45927 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_98415 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6804 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_19926 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_46170 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_98658 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8262 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_21384 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_12636 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_25758 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_52497 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78741 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_91863 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_98424 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_28434 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80922 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_41556 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94044 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_48117 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_100605 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80931 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94053 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_100614 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_52503 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78747 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_13852 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_40096 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_92584 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_20413 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_46657 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_99145 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_18226 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_44470 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_24787 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_51031 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_20656 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_46900 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_99388 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_25030 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_51274 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_42286 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94774 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_48847 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_101335 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_49090 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_101578 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94783 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_101344 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_101587 : (f ![1, 1, 1, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_28436 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80924 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_41558 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94046 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80933 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94055 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_52505 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78749 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 46 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_52488, fv1_26244, fv1_78732, fv1_13122, fv1_39366, fv1_91854, fv1_6561, fv1_19683, fv1_45927, fv1_98415, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_52488 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_52497, fv1_78741, fv1_91863, fv1_98424, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_26244 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_28434, fv1_80922, fv1_41556, fv1_94044, fv1_48117, fv1_100605, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_78732 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_80931, fv1_94053, fv1_100614, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_13122 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_13852, fv1_40096, fv1_92584, fv1_20413, fv1_46657, fv1_99145, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_39366 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_91854 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6561 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_6804, fv1_19926, fv1_46170, fv1_98658, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_19683 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_20656, fv1_46900, fv1_99388, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_45927 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_98415 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6804 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_8262, fv1_21384, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_19926 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_20656, fv1_46900, fv1_99388, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_46170 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_98658 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8262 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_12636, fv1_25758, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_21384 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_12636 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_12636, fv1_25758, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_25758 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_52497 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_52503, fv1_78747, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_78741 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_80931, fv1_94053, fv1_100614, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_91863 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_98424 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_28434 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_28436, fv1_80924, fv1_41558, fv1_94046, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80922 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_41556 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94044 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_48117 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_100605 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80931 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94053 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_100614 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_52503 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_52505, fv1_78749, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_78747 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_13852 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_18226, fv1_44470, fv1_24787, fv1_51031, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_40096 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_92584 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_20413 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_46657 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_99145 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_18226 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_18226, fv1_44470, fv1_24787, fv1_51031, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_44470 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_24787 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_51031 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_20656 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_46900 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_99388 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_25030 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_25030, fv1_51274, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_51274 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_42286 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94774 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_48847 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_101335 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_49090 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_49090, fv1_101578, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_101578 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94783 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_101344 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_101587 : (f ![1, 1, 1, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_101587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_28436 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_28436, fv1_80924, fv1_41558, fv1_94046, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80924 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_41558 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_42286, fv1_94774, fv1_48847, fv1_101335, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94046 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80933 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94055 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_94783, fv1_101344, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_52505 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_52505, fv1_78749, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_78749 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_80933, fv1_94055, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 66 → Fin 8 → Fin 3 := ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 2, 0], ![0, 0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 2, 0], ![1, 0, 0, 0, 0, 0, 1, 2], ![1, 0, 0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![2, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![2, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0, 1, 1], ![1, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 0, 0, 0, 1, 1, 1], ![1, 0, 0, 0, 0, 0, 1, 2], ![1, 0, 0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0], ![2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0], ![2, 2, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![2, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 1], ![2, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![2, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 1], ![2, 1, 1, 0, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 1, 1, 1]]

set_option maxRecDepth 100000 in
def rs : Fin 66 → R := ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 66 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((10 : ℚ) / 3) * (n : ℚ) ^ 3 + ((103 : ℚ) / 6) * (n : ℚ) ^ 2 + ((307 : ℚ) / 6) * (n : ℚ) ^ 1 + (46 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((10 : ℚ) / 3) * (n : ℚ) ^ 3 + ((103 : ℚ) / 6) * (n : ℚ) ^ 2 + ((307 : ℚ) / 6) * (n : ℚ) ^ 1 + (46 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h34 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 34 n := ih 34
  have h16 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 16 n := ih 16
  have h38 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 38 n := ih 38
  have h5 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 5 n := ih 5
  have h19 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 19 n := ih 19
  have h46 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 46 n := ih 46
  have h1 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h8 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 8 n := ih 8
  have h25 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 25 n := ih 25
  have h55 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 55 n := ih 55
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h34, h16, h38, h5, h19, h46, h1, h8, h25, h55, f_dead, pp_0, pp_0, pp_34, pp_16, pp_38, pp_5, pp_19, pp_46, pp_1, pp_8, pp_25, pp_55]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℚ) = 46 := by exact_mod_cast fv2_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![1, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h2 : (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h9 : (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 9 n := ih 9
  have h26 : (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h57 : (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 57 n := ih 57
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h2, h9, h26, h57, f_dead, pp_1, pp_2, pp_9, pp_26, pp_57]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv2_6561
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2 + 1) ![1, 0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h3 : (f ![0, 0, 0, 0, 0, 1, 2, 0] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h12 : (f ![0, 0, 0, 0, 0, 1, 2, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 12 n := ih 12
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h3, h12, f_dead, pp_2, pp_3, pp_12]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_6804
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 2, 0] (n + 2 + 1) ![1, 0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h4 : (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h15 : (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h4, h15, f_dead, pp_3, pp_4, pp_15]
  try (push_cast; ring)

lemma b_3 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_8262
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2 + 1) ![1, 0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h4 : (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h15 : (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 15 n := ih 15
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h4, h15, f_dead, pp_4, pp_4, pp_15]
  try (push_cast; ring)

lemma b_4 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_12636
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 1, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h6 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 6 n := ih 6
  have h20 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 20 n := ih 20
  have h48 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 48 n := ih 48
  have h10 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h27 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 27 n := ih 27
  have h58 : (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 58 n := ih 58
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h6, h20, h48, h10, h27, h58, f_dead, pp_5, pp_6, pp_20, pp_48, pp_10, pp_27, pp_58]
  try (push_cast; ring)

lemma b_5 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = 15 := by exact_mod_cast fv2_13122
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![0, 1, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h7 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 7 n := ih 7
  have h24 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 24 n := ih 24
  have h13 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h32 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 32 n := ih 32
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h7, h24, h13, h32, f_dead, pp_6, pp_7, pp_24, pp_13, pp_32]
  try (push_cast; ring)

lemma b_6 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 0, 0] : ℚ) = 12 := by exact_mod_cast fv2_13852
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2 + 1) ![0, 1, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h7 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 7 n := ih 7
  have h24 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 24 n := ih 24
  have h13 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h32 : (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 32 n := ih 32
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h7, h24, h13, h32, f_dead, pp_7, pp_7, pp_24, pp_13, pp_32]
  try (push_cast; ring)

lemma b_7 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 0, 0] : ℚ) = 12 := by exact_mod_cast fv2_18226
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h11 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 11 n := ih 11
  have h28 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 28 n := ih 28
  have h59 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 59 n := ih 59
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h11, h28, h59, f_dead, pp_8, pp_11, pp_28, pp_59]
  try (push_cast; ring)

lemma b_8 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = 5 := by exact_mod_cast fv2_19683
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h11 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 11 n := ih 11
  have h28 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 28 n := ih 28
  have h59 : (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 59 n := ih 59
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h11, h28, h59, f_dead, pp_9, pp_11, pp_28, pp_59]
  try (push_cast; ring)

lemma b_9 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = 5 := by exact_mod_cast fv2_19926
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h14, h33, f_dead, pp_10, pp_14, pp_33]
  try (push_cast; ring)

lemma b_10 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_20413
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h14, h33, f_dead, pp_11, pp_14, pp_33]
  try (push_cast; ring)

lemma b_11 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_20656
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 2, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h14, h33, f_dead, pp_12, pp_14, pp_33]
  try (push_cast; ring)

lemma b_12 : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_21384
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h14, h33, f_dead, pp_13, pp_14, pp_33]
  try (push_cast; ring)

lemma b_13 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_24787
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h14, h33, f_dead, pp_14, pp_14, pp_33]
  try (push_cast; ring)

lemma b_14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_25030
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 2, 2] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h14 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 14 n := ih 14
  have h33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h14, h33, f_dead, pp_15, pp_14, pp_33]
  try (push_cast; ring)

lemma b_15 : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 1, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 1, 0, 0] : ℚ) = 4 := by exact_mod_cast fv2_25758
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 16 (n + 1) := by
  have h17 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 42 n := ih 42
  have h21 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 21 n := ih 21
  have h49 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 49 n := ih 49
  have h29 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 29 n := ih 29
  have h60 : (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 60 n := ih 60
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h17, h42, h21, h49, h29, h60, f_dead, pp_16, pp_17, pp_42, pp_21, pp_49, pp_29, pp_60]
  try (push_cast; ring)

lemma b_16 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = PP 16 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = 15 := by exact_mod_cast fv2_26244
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 17 (n + 1) := by
  have h18 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 18 n := ih 18
  have h43 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 43 n := ih 43
  have h22 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 22 n := ih 22
  have h50 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 50 n := ih 50
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h18, h43, h22, h50, f_dead, pp_17, pp_18, pp_43, pp_22, pp_50]
  try (push_cast; ring)

lemma b_17 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℚ) = PP 17 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℚ) = 12 := by exact_mod_cast fv2_28434
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 18 (n + 1) := by
  have h18 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 18 n := ih 18
  have h43 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 43 n := ih 43
  have h22 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 22 n := ih 22
  have h50 : (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 50 n := ih 50
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h18, h43, h22, h50, f_dead, pp_18, pp_18, pp_43, pp_22, pp_50]
  try (push_cast; ring)

lemma b_18 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℚ) = PP 18 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℚ) = 12 := by exact_mod_cast fv2_28436
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 19 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h23, h53, h30, h62, f_dead, pp_19, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_19 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 19 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_39366
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 20 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h23, h53, h30, h62, f_dead, pp_20, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_20 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 20 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_40096
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 21 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h23, h53, h30, h62, f_dead, pp_21, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_21 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℚ) = PP 21 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_41556
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 22 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h23, h53, h30, h62, f_dead, pp_22, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_22 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℚ) = PP 22 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_41558
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 23 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h23, h53, h30, h62, f_dead, pp_23, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 0] : ℚ) = PP 23 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_42286
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 24 (n + 1) := by
  have h23 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 53 n := ih 53
  have h30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 30 n := ih 30
  have h62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h23, h53, h30, h62, f_dead, pp_24, pp_23, pp_53, pp_30, pp_62]
  try (push_cast; ring)

lemma b_24 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 1, 0] : ℚ) = PP 24 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_44470
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 25 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h31, h64, f_dead, pp_25, pp_31, pp_64]
  try (push_cast; ring)

lemma b_25 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 25 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_45927
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 26 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_26, pp_31, pp_64]
  try (push_cast; ring)

lemma b_26 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 26 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_46170
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 27 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_27, pp_31, pp_64]
  try (push_cast; ring)

lemma b_27 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 27 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_46657
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 28 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_28, pp_31, pp_64]
  try (push_cast; ring)

lemma b_28 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 28 0 := by
  have h : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_46900
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 29 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_29, pp_31, pp_64]
  try (push_cast; ring)

lemma b_29 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 0] : ℚ) = PP 29 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_48117
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 30 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_30, pp_31, pp_64]
  try (push_cast; ring)

lemma b_30 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 0] : ℚ) = PP 30 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_48847
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 31 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_31, pp_31, pp_64]
  try (push_cast; ring)

lemma b_31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 0] : ℚ) = PP 31 0 := by
  have h : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_49090
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 2] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 32 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_32, pp_31, pp_64]
  try (push_cast; ring)

lemma b_32 : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 1, 0] : ℚ) = PP 32 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 2] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_51031
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 1, 1, 2] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 33 (n + 1) := by
  have h31 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h31, h64, f_dead, pp_33, pp_31, pp_64]
  try (push_cast; ring)

lemma b_33 : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 1, 0] : ℚ) = PP 33 0 := by
  have h : (f ![1, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_51274
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 34 (n + 1) := by
  have h35 : (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 35 n := ih 35
  have h39 : (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 39 n := ih 39
  have h47 : (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 47 n := ih 47
  have h56 : (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h35, h39, h47, h56, f_dead, pp_34, pp_35, pp_39, pp_47, pp_56]
  try (push_cast; ring)

lemma b_34 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 34 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv2_52488
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 35 (n + 1) := by
  have h36 : (f ![0, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 36 n := ih 36
  have h40 : (f ![0, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h36, h40, f_dead, pp_35, pp_36, pp_40]
  try (push_cast; ring)

lemma b_35 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 35 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_52497
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 36 (n + 1) := by
  have h37 : (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 37 n := ih 37
  have h41 : (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h37, h41, f_dead, pp_36, pp_37, pp_41]
  try (push_cast; ring)

lemma b_36 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 36 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_52503
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 37 (n + 1) := by
  have h37 : (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 37 n := ih 37
  have h41 : (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h37, h41, f_dead, pp_37, pp_37, pp_41]
  try (push_cast; ring)

lemma b_37 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 37 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_52505
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 38 (n + 1) := by
  have h44 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 44 n := ih 44
  have h51 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 51 n := ih 51
  have h61 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 61 n := ih 61
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h44, h51, h61, f_dead, pp_38, pp_44, pp_51, pp_61]
  try (push_cast; ring)

lemma b_38 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 38 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 5 := by exact_mod_cast fv2_78732
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 39 (n + 1) := by
  have h44 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 44 n := ih 44
  have h51 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 51 n := ih 51
  have h61 : (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 61 n := ih 61
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h44, h51, h61, f_dead, pp_39, pp_44, pp_51, pp_61]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 5 := by exact_mod_cast fv2_78741
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 40 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h45, h52, f_dead, pp_40, pp_45, pp_52]
  try (push_cast; ring)

lemma b_40 : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 40 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_78747
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 41 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h45, h52, f_dead, pp_41, pp_45, pp_52]
  try (push_cast; ring)

lemma b_41 : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 41 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_78749
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 42 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h45, h52, f_dead, pp_42, pp_45, pp_52]
  try (push_cast; ring)

lemma b_42 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = PP 42 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_80922
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 43 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h45, h52, f_dead, pp_43, pp_45, pp_52]
  try (push_cast; ring)

lemma b_43 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = PP 43 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_80924
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 44 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h45, h52, f_dead, pp_44, pp_45, pp_52]
  try (push_cast; ring)

lemma b_44 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = PP 44 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_80931
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 45 (n + 1) := by
  have h45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 45 n := ih 45
  have h52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h45, h52, f_dead, pp_45, pp_45, pp_52]
  try (push_cast; ring)

lemma b_45 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = PP 45 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_80933
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 46 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h54, h63, f_dead, pp_46, pp_54, pp_63]
  try (push_cast; ring)

lemma b_46 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 46 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_91854
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 47 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_47, pp_54, pp_63]
  try (push_cast; ring)

lemma b_47 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 47 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_91863
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 48 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_48, pp_54, pp_63]
  try (push_cast; ring)

lemma b_48 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 48 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_92584
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 49 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_49, pp_54, pp_63]
  try (push_cast; ring)

lemma b_49 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 49 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94044
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 50 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_50, pp_54, pp_63]
  try (push_cast; ring)

lemma b_50 : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 50 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94046
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 51 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_51, pp_54, pp_63]
  try (push_cast; ring)

lemma b_51 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 51 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94053
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 52 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_52, pp_54, pp_63]
  try (push_cast; ring)

lemma b_52 : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 52 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94055
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 53 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_53, pp_54, pp_63]
  try (push_cast; ring)

lemma b_53 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 53 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94774
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 54 (n + 1) := by
  have h54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h63, f_dead, pp_54, pp_54, pp_63]
  try (push_cast; ring)

lemma b_54 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℚ) = PP 54 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_94783
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 55 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h65, f_dead, pp_55, pp_65]
  try (push_cast; ring)

lemma b_55 : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 55 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_98415
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 56 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_56, pp_65]
  try (push_cast; ring)

lemma b_56 : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 56 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_98424
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 57 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_57, pp_65]
  try (push_cast; ring)

lemma b_57 : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 57 0 := by
  have h : (f ![0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_98658
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 58 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_58, pp_65]
  try (push_cast; ring)

lemma b_58 : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 58 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_99145
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 1, 1, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 59 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_59, pp_65]
  try (push_cast; ring)

lemma b_59 : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 59 0 := by
  have h : (f ![1, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_99388
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 60 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_60, pp_65]
  try (push_cast; ring)

lemma b_60 : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 60 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_100605
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 61 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_61, pp_65]
  try (push_cast; ring)

lemma b_61 : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 61 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_100614
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 62 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_62, pp_65]
  try (push_cast; ring)

lemma b_62 : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 62 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_101335
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 1, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 63 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_63, pp_65]
  try (push_cast; ring)

lemma b_63 : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 63 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_101344
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 1, 1, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 64 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_64, pp_65]
  try (push_cast; ring)

lemma b_64 : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 64 0 := by
  have h : (f ![1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_101578
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 65 (n + 1) := by
  have h65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h65, f_dead, pp_65, pp_65]
  try (push_cast; ring)

lemma b_65 : (f ![1, 1, 1, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = PP 65 0 := by
  have h : (f ![1, 1, 1, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_101587
  rw [h, pp_65]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 66, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih]

lemma aBig (m : ℕ) : (a (m + 3) : ℚ) = ((1 : ℚ) / 3) * (m : ℚ) ^ 4 + ((14 : ℚ) / 3) * (m : ℚ) ^ 3 + ((175 : ℚ) / 6) * (m : ℚ) ^ 2 + ((581 : ℚ) / 6) * (m : ℚ) ^ 1 + (118 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g34 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 0, 0, 1] : ℚ) = PP 34 m := f_closed m 34
  have g16 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 0, 1, 0] : ℚ) = PP 16 m := f_closed m 16
  have g38 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 0, 1, 1] : ℚ) = PP 38 m := f_closed m 38
  have g5 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 1, 0, 0] : ℚ) = PP 5 m := f_closed m 5
  have g19 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 1, 1, 0] : ℚ) = PP 19 m := f_closed m 19
  have g46 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![0, 1, 1, 1] : ℚ) = PP 46 m := f_closed m 46
  have g1 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![1, 0, 0, 0] : ℚ) = PP 1 m := f_closed m 1
  have g8 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![1, 1, 0, 0] : ℚ) = PP 8 m := f_closed m 8
  have g25 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![1, 1, 1, 0] : ℚ) = PP 25 m := f_closed m 25
  have g55 : (f ![0, 0, 0, 0, 0, 0, 0, 0] (m + 2) ![1, 1, 1, 1] : ℚ) = PP 55 m := f_closed m 55
  rw [show m + 3 = (m + 2) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 8 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g34, g16, g38, g5, g19, g46, g1, g8, g25, g55, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_34, pp_16, pp_38, pp_5, pp_19, pp_46, pp_1, pp_8, pp_25, pp_55]
  ring

lemma aS1 : (a 1 : ℚ) = 11 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 8 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 46 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 8 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 8 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_52488, fv1_26244, fv1_78732, fv1_13122, fv1_39366, fv1_91854, fv1_6561, fv1_19683, fv1_45927, fv1_98415]
  norm_num

lemma av (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((2 : ℚ) / 3) * (n : ℚ) ^ 3 + ((31 : ℚ) / 6) * (n : ℚ) ^ 2 + ((71 : ℚ) / 6) * (n : ℚ) ^ 1 + (-9 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp only [aS2] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      11 - 9 * X - 2 * X ^ 2 + 9 * X ^ 3 + X ^ 4 - 2 * X ^ 5) ∧
    (∀ n > 6, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (11 - 9 * X - 2 * X ^ 2 + 9 * X ^ 3 + X ^ 4 - 2 * X ^ 5 : PowerSeries ℚ) =
        C (11 : ℚ) * X ^ 0 + C (-9 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (9 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (-2 : ℚ) * X ^ 5 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 11 := aS1
    have e2 : (a 2 : ℚ) = 46 := aS2
    have e3 : (a 3 : ℚ) = 118 := by rw [av 3 (by norm_num)]; norm_num
    have e4 : (a 4 : ℚ) = 249 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 471 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 824 := by rw [av 6 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 6 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 6 := ⟨c - 6, by omega⟩
      simp only [show m + 6 - 0 = m + 6 by omega, show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show 0 ≤ m + 6 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega), av (m + 1 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega]
    qify
    rw [av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega), av (m + 2) (by omega)]
    push_cast; ring

end OMA.P_oeis_a223834

theorem OMA.solution : type_of% @OMA.S_oeis_a223834.main := OMA.P_oeis_a223834.full
