import OMAStatements.S_oeis_a223840
import Mathlib

/-!
# oeis-a223840: counting the n X 4 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 3 it is an explicit polynomial, checked by induction over the
73 states (c, r) whose top row is allowed, from exact values at n = 1..3. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223840, https://oeis.org/A223840.
-/
namespace OMA.P_oeis_a223840

open OMA.S_oeis_a223840

def adj (r s : Fin 4 → Fin 2) : Prop := True

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
def okT (c : Fin 12 → Fin 3) (r : R) : Prop := (∀ i : Fin 3, r i.castSucc ≤ r i.succ) ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true ∧ okb (c 4) (r 0) = true ∧ okb (c 5) (r 1) = true ∧ okb (c 6) (r 2) = true ∧ okb (c 7) (r 3) = true ∧ okb (c 8) (r 0) = true ∧ okb (c 9) (r 1) = true ∧ okb (c 10) (r 2) = true ∧ okb (c 11) (r 3) = true

instance (c : Fin 12 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 12 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, ∀ i : Fin 3, r i.castSucc ≤ r i.succ) ∧ Acc (c 0) (l.map (· 0)) = true ∧ Acc (c 1) (l.map (· 1)) = true ∧ Acc (c 2) (l.map (· 2)) = true ∧ Acc (c 3) (l.map (· 3)) = true ∧ Acc (c 4) (adiagF l 0) = true ∧ Acc (c 5) (adiagF l 1) = true ∧ Acc (c 6) (adiagF l 2) = true ∧ Acc (c 7) (adiagF l 3) = true ∧ Acc (c 8) (diagF l 0) = true ∧ Acc (c 9) (diagF l 1) = true ∧ Acc (c 10) (diagF l 2) = true ∧ Acc (c 11) (diagF l 3) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true) ∧ (∀ i, Acc 0 (diagF (l.drop (i + 1)) 0) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 3)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 3) = true by simp only [adiag_map, uniAcc], fdrop]
  rw [show (∀ i, Unimodal (diagFrom (l.drop i) 0)) ↔ ∀ i, Acc 0 (diagF (l.drop i) 0) = true by simp only [diag_map, uniAcc], gdrop]
  simp only [colUni, adiag_map, uniAcc, ltK, diag_map, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    chain_true]
  tauto

lemma Q_single (c : Fin 12 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF, diagF]

lemma Q_cons (c : Fin 12 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 5) (r 1), dl (c 6) (r 2), dl (c 7) (r 3), 0, 0, dl (c 8) (r 0), dl (c 9) (r 1), dl (c 10) (r 2)] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Acc, Bool.and_eq_true,
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

noncomputable def f (c : Fin 12 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 12 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 12 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 5) (r 1), dl (c 6) (r 2), dl (c 7) (r 3), 0, 0, dl (c 8) (r 0), dl (c 9) (r 1), dl (c 10) (r 2)] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 12 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] (n + 1) ![r0, r1, r2, r3] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c0) (r0), dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c5) (r1), dl (c6) (r2), dl (c7) (r3), 0, 0, dl (c8) (r0), dl (c9) (r1), dl (c10) (r2)] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] (n + 1) ![r0, r1, r2, r3] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c0) (r0), dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c5) (r1), dl (c6) (r2), dl (c7) (r3), 0, 0, dl (c8) (r0), dl (c9) (r1), dl (c10) (r2)] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4251528 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6377292 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7440174 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7971615 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_756 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252284 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6378048 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7440930 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7972371 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1242 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252770 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6378534 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1404 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252932 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6378696 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_54 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_540 : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_216 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_702 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_178155 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4429683 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6555447 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7618329 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8149770 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_178317 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4429845 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6555609 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7618491 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1422 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252950 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_72 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_234 : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_720 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_237288 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4488816 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6614580 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7677462 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8208903 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_178323 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4429851 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6555615 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1428 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252956 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_355722 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_78 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_240 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_726 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_355020 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_256972 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4508500 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 1 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6634264 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7697146 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8228587 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_237290 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4488818 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6614582 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7677464 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_178325 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4429853 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_6555617 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_296423 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4547951 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 1 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1430 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_4252958 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_355724 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_473822 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_242 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_354536 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_728 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_355022 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_473120 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 25 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_4251528, fv1_6377292, fv1_7440174, fv1_7971615, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4251528 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 19 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_756, fv1_4252284, fv1_6378048, fv1_7440930, fv1_7972371, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6377292 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_178155, fv1_4429683, fv1_6555447, fv1_7618329, fv1_8149770, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7440174 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_237288, fv1_4488816, fv1_6614580, fv1_7677462, fv1_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7971615 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_256972, fv1_4508500, fv1_6634264, fv1_7697146, fv1_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_756 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_540, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252284 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1242, fv1_4252770, fv1_6378534, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6378048 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_178155, fv1_4429683, fv1_6555447, fv1_7618329, fv1_8149770, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7440930 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_237288, fv1_4488816, fv1_6614580, fv1_7677462, fv1_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7972371 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_256972, fv1_4508500, fv1_6634264, fv1_7697146, fv1_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1242 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_702, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252770 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1404, fv1_4252932, fv1_6378696, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6378534 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_178317, fv1_4429845, fv1_6555609, fv1_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1404 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_702, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252932 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1404, fv1_4252932, fv1_6378696, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6378696 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_178317, fv1_4429845, fv1_6555609, fv1_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_54 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_54, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_540 : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_216 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_54, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_702 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_178155 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4429683 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1422, fv1_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6555447 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_178317, fv1_4429845, fv1_6555609, fv1_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7618329 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_237288, fv1_4488816, fv1_6614580, fv1_7677462, fv1_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8149770 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_256972, fv1_4508500, fv1_6634264, fv1_7697146, fv1_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_178317 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4429845 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1422, fv1_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6555609 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_178317, fv1_4429845, fv1_6555609, fv1_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7618491 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_237288, fv1_4488816, fv1_6614580, fv1_7677462, fv1_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1422 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252950 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1422, fv1_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_72 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_72, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_234 : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_72, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_720 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_234, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_237288 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_355020, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4488816 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_355722, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6614580 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_178323, fv1_4429851, fv1_6555615, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7677462 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_237288, fv1_4488816, fv1_6614580, fv1_7677462, fv1_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8208903 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_256972, fv1_4508500, fv1_6634264, fv1_7697146, fv1_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_178323 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4429851 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1428, fv1_4252956, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6555615 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_178323, fv1_4429851, fv1_6555615, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1428 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252956 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1428, fv1_4252956, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_355722 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_78 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_78, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_240 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_78, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_726 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_240, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_355020 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_240, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_256972 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_473120, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4508500 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 2 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_473822, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6634264 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 2 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_296423, fv1_4547951, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7697146 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_237290, fv1_4488818, fv1_6614582, fv1_7677464, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8228587 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_256972, fv1_4508500, fv1_6634264, fv1_7697146, fv1_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_237290 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4488818 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_355724, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6614582 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_178325, fv1_4429853, fv1_6555617, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7677464 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_237290, fv1_4488818, fv1_6614582, fv1_7677464, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_178325 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4429853 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1430, fv1_4252958, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_6555617 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_178325, fv1_4429853, fv1_6555617, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_296423 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4547951 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 2 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_355724, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1430 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_4252958 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1430, fv1_4252958, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_355724 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_473822 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_242 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_354536 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_728 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_242, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_355022 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_242, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_473120 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_354536, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 89 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_0, fv2_4251528, fv2_6377292, fv2_7440174, fv2_7971615, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4251528 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 54 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_756, fv2_4252284, fv2_6378048, fv2_7440930, fv2_7972371, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6377292 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 44 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_178155, fv2_4429683, fv2_6555447, fv2_7618329, fv2_8149770, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7440174 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_237288, fv2_4488816, fv2_6614580, fv2_7677462, fv2_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7971615 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 26 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_256972, fv2_4508500, fv2_6634264, fv2_7697146, fv2_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_756 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_540, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252284 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1242, fv2_4252770, fv2_6378534, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6378048 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 44 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_178155, fv2_4429683, fv2_6555447, fv2_7618329, fv2_8149770, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7440930 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_237288, fv2_4488816, fv2_6614580, fv2_7677462, fv2_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7972371 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 26 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_256972, fv2_4508500, fv2_6634264, fv2_7697146, fv2_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1242 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_702, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252770 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1404, fv2_4252932, fv2_6378696, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6378534 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 31 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_178317, fv2_4429845, fv2_6555609, fv2_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1404 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_702, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252932 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1404, fv2_4252932, fv2_6378696, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6378696 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 31 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_178317, fv2_4429845, fv2_6555609, fv2_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_54 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_54, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_540 : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_216, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_216 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_54, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_702 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_216, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_178155 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4429683 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1422, fv2_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6555447 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 31 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_178317, fv2_4429845, fv2_6555609, fv2_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7618329 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_237288, fv2_4488816, fv2_6614580, fv2_7677462, fv2_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_8149770 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℤ) = 26 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_256972, fv2_4508500, fv2_6634264, fv2_7697146, fv2_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_178317 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4429845 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1422, fv2_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6555609 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 31 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_178317, fv2_4429845, fv2_6555609, fv2_7618491, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7618491 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_237288, fv2_4488816, fv2_6614580, fv2_7677462, fv2_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1422 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_720, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252950 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1422, fv2_4252950, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_72 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_72, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_234 : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_72, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_720 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_234, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_237288 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_355020, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4488816 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_355722, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6614580 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_178323, fv2_4429851, fv2_6555615, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7677462 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_237288, fv2_4488816, fv2_6614580, fv2_7677462, fv2_8208903, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_8208903 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℤ) = 26 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_256972, fv2_4508500, fv2_6634264, fv2_7697146, fv2_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_178323 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4429851 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1428, fv2_4252956, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6555615 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_178323, fv2_4429851, fv2_6555615, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1428 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252956 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1428, fv2_4252956, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_355722 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_726, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_78 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_78, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_240 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_78, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_726 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_240, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_355020 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_240, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_256972 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_473120, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4508500 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_473822, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6634264 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_296423, fv2_4547951, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7697146 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_237290, fv2_4488818, fv2_6614582, fv2_7677464, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_8228587 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℤ) = 26 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_256972, fv2_4508500, fv2_6634264, fv2_7697146, fv2_8228587, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_237290 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4488818 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_355724, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6614582 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_178325, fv2_4429853, fv2_6555617, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7677464 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_237290, fv2_4488818, fv2_6614582, fv2_7677464, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_178325 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4429853 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1430, fv2_4252958, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_6555617 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_178325, fv2_4429853, fv2_6555617, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_296423 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4547951 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_355724, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1430 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_4252958 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1430, fv2_4252958, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_355724 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_473822 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_355022, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_80 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_242 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_354536 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_728 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_242, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_355022 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_242, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_473120 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_354536, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 73 → Fin 12 → Fin 3 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0], ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1], ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2], ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2], ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2], ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2], ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2], ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2], ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]]

set_option maxRecDepth 100000 in
def rs : Fin 73 → R := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 73 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((1 : ℚ) / 2016) * (n : ℚ) ^ 7 + ((31 : ℚ) / 2880) * (n : ℚ) ^ 6 + ((127 : ℚ) / 720) * (n : ℚ) ^ 5 + ((9287 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((3103 : ℚ) / 288) * (n : ℚ) ^ 3 + ((472519 : ℚ) / 10080) * (n : ℚ) ^ 2 + ((84461 : ℚ) / 840) * (n : ℚ) ^ 1 + (89 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((17 : ℚ) / 360) * (n : ℚ) ^ 5 + ((11 : ℚ) / 18) * (n : ℚ) ^ 4 + ((2887 : ℚ) / 720) * (n : ℚ) ^ 3 + ((6619 : ℚ) / 360) * (n : ℚ) ^ 2 + ((1783 : ℚ) / 35) * (n : ℚ) ^ 1 + (54 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((41 : ℚ) / 144) * (n : ℚ) ^ 4 + ((127 : ℚ) / 48) * (n : ℚ) ^ 3 + ((4757 : ℚ) / 360) * (n : ℚ) ^ 2 + ((227 : ℚ) / 6) * (n : ℚ) ^ 1 + (44 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((41 : ℚ) / 144) * (n : ℚ) ^ 4 + ((127 : ℚ) / 48) * (n : ℚ) ^ 3 + ((4757 : ℚ) / 360) * (n : ℚ) ^ 2 + ((227 : ℚ) / 6) * (n : ℚ) ^ 1 + (44 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((59 : ℚ) / 6) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((59 : ℚ) / 6) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((1 : ℚ) / 2016) * (n : ℚ) ^ 7 + ((31 : ℚ) / 2880) * (n : ℚ) ^ 6 + ((127 : ℚ) / 720) * (n : ℚ) ^ 5 + ((9287 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((3103 : ℚ) / 288) * (n : ℚ) ^ 3 + ((472519 : ℚ) / 10080) * (n : ℚ) ^ 2 + ((84461 : ℚ) / 840) * (n : ℚ) ^ 1 + (89 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((17 : ℚ) / 360) * (n : ℚ) ^ 5 + ((11 : ℚ) / 18) * (n : ℚ) ^ 4 + ((2887 : ℚ) / 720) * (n : ℚ) ^ 3 + ((6619 : ℚ) / 360) * (n : ℚ) ^ 2 + ((1783 : ℚ) / 35) * (n : ℚ) ^ 1 + (54 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((4 : ℚ) / 9) * (n : ℚ) ^ 4 + ((1837 : ℚ) / 720) * (n : ℚ) ^ 3 + ((3259 : ℚ) / 360) * (n : ℚ) ^ 2 + ((4181 : ℚ) / 210) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

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
lemma pp_46 (n : ℕ) : PP 46 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((41 : ℚ) / 144) * (n : ℚ) ^ 4 + ((127 : ℚ) / 48) * (n : ℚ) ^ 3 + ((4757 : ℚ) / 360) * (n : ℚ) ^ 2 + ((227 : ℚ) / 6) * (n : ℚ) ^ 1 + (44 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((41 : ℚ) / 144) * (n : ℚ) ^ 4 + ((127 : ℚ) / 48) * (n : ℚ) ^ 3 + ((4757 : ℚ) / 360) * (n : ℚ) ^ 2 + ((227 : ℚ) / 6) * (n : ℚ) ^ 1 + (44 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((107 : ℚ) / 48) * (n : ℚ) ^ 3 + ((484 : ℚ) / 45) * (n : ℚ) ^ 2 + ((111 : ℚ) / 4) * (n : ℚ) ^ 1 + (31 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((9 : ℚ) / 2) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 8) * (n : ℚ) ^ 4 + ((29 : ℚ) / 24) * (n : ℚ) ^ 3 + ((67 : ℚ) / 8) * (n : ℚ) ^ 2 + ((1697 : ℚ) / 60) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_66 (n : ℕ) : PP 66 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((59 : ℚ) / 6) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_67 (n : ℕ) : PP 67 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((59 : ℚ) / 6) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_68 (n : ℕ) : PP 68 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_69 (n : ℕ) : PP 69 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_70 (n : ℕ) : PP 70 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_71 (n : ℕ) : PP 71 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_72 (n : ℕ) : PP 72 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((7 : ℚ) / 12) * (n : ℚ) ^ 3 + ((95 : ℚ) / 24) * (n : ℚ) ^ 2 + ((197 : ℚ) / 12) * (n : ℚ) ^ 1 + (26 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h35 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 35 n := ih 35
  have h50 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 50 n := ih 50
  have h61 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 61 n := ih 61
  have h68 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 68 n := ih 68
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h35, h50, h61, h68, f_dead, pp_0, pp_0, pp_35, pp_50, pp_61, pp_68]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 89 := by exact_mod_cast fv3_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h1 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h1, f_dead, pp_1, pp_1]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_54
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h2 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h2, f_dead, pp_2, pp_2]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_72
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h3 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h3, f_dead, pp_3, pp_3]
  try (push_cast; ring)

lemma b_3 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_78
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h4 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h4, f_dead, pp_4, pp_4]
  try (push_cast; ring)

lemma b_4 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_80
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h1 : (f ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h1, f_dead, pp_5, pp_1]
  try (push_cast; ring)

lemma b_5 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_216
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h2 : (f ![0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h2, f_dead, pp_6, pp_2]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_234
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h3 : (f ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h3, f_dead, pp_7, pp_3]
  try (push_cast; ring)

lemma b_7 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_240
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h4 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h4, f_dead, pp_8, pp_4]
  try (push_cast; ring)

lemma b_8 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_242
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h5 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h5, f_dead, pp_9, pp_5]
  try (push_cast; ring)

lemma b_9 : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_540
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h5 : (f ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h5, f_dead, pp_10, pp_5]
  try (push_cast; ring)

lemma b_10 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_702
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h6 : (f ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 6 n := ih 6
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h6, f_dead, pp_11, pp_6]
  try (push_cast; ring)

lemma b_11 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_720
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h7 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h7, f_dead, pp_12, pp_7]
  try (push_cast; ring)

lemma b_12 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_726
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h8 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 8 n := ih 8
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h8, f_dead, pp_13, pp_8]
  try (push_cast; ring)

lemma b_13 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_728
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h9 : (f ![0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 9 n := ih 9
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h9, f_dead, pp_14, pp_9]
  try (push_cast; ring)

lemma b_14 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_756
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h10 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 10 n := ih 10
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h10, f_dead, pp_15, pp_10]
  try (push_cast; ring)

lemma b_15 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_1242
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 16 (n + 1) := by
  have h10 : (f ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 10 n := ih 10
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h10, f_dead, pp_16, pp_10]
  try (push_cast; ring)

lemma b_16 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 16 0 := by
  have h : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_1404
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 17 (n + 1) := by
  have h11 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h11, f_dead, pp_17, pp_11]
  try (push_cast; ring)

lemma b_17 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 17 0 := by
  have h : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_1422
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 18 (n + 1) := by
  have h12 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h12, f_dead, pp_18, pp_12]
  try (push_cast; ring)

lemma b_18 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 18 0 := by
  have h : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_1428
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 19 (n + 1) := by
  have h13 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h13, f_dead, pp_19, pp_13]
  try (push_cast; ring)

lemma b_19 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 19 0 := by
  have h : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_1430
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 20 (n + 1) := by
  have h11 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h11, f_dead, pp_20, pp_11]
  try (push_cast; ring)

lemma b_20 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 20 0 := by
  have h : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_178155
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 21 (n + 1) := by
  have h11 : (f ![0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h11, f_dead, pp_21, pp_11]
  try (push_cast; ring)

lemma b_21 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 21 0 := by
  have h : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_178317
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 22 (n + 1) := by
  have h12 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h12, f_dead, pp_22, pp_12]
  try (push_cast; ring)

lemma b_22 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 22 0 := by
  have h : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_178323
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 23 (n + 1) := by
  have h13 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h13, f_dead, pp_23, pp_13]
  try (push_cast; ring)

lemma b_23 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 23 0 := by
  have h : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_178325
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 24 (n + 1) := by
  have h29 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 29 n := ih 29
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h29, f_dead, pp_24, pp_29]
  try (push_cast; ring)

lemma b_24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 24 0 := by
  have h : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_237288
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 25 (n + 1) := by
  have h30 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 30 n := ih 30
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h30, f_dead, pp_25, pp_30]
  try (push_cast; ring)

lemma b_25 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 25 0 := by
  have h : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_237290
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 26 (n + 1) := by
  have h33 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h33, f_dead, pp_26, pp_33]
  try (push_cast; ring)

lemma b_26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 26 0 := by
  have h : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_256972
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 27 (n + 1) := by
  have h30 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 30 n := ih 30
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h30, f_dead, pp_27, pp_30]
  try (push_cast; ring)

lemma b_27 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 0] : ℚ) = PP 27 0 := by
  have h : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_296423
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 28 (n + 1) := by
  have h4 : (f ![2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h4, f_dead, pp_28, pp_4]
  try (push_cast; ring)

lemma b_28 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 28 0 := by
  have h : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_354536
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 29 (n + 1) := by
  have h7 : (f ![0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h7, f_dead, pp_29, pp_7]
  try (push_cast; ring)

lemma b_29 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 29 0 := by
  have h : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_355020
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 30 (n + 1) := by
  have h8 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 8 n := ih 8
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h8, f_dead, pp_30, pp_8]
  try (push_cast; ring)

lemma b_30 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 30 0 := by
  have h : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_355022
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 31 (n + 1) := by
  have h12 : (f ![0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h12, f_dead, pp_31, pp_12]
  try (push_cast; ring)

lemma b_31 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 31 0 := by
  have h : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_355722
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 32 (n + 1) := by
  have h13 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h13, f_dead, pp_32, pp_13]
  try (push_cast; ring)

lemma b_32 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 32 0 := by
  have h : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_355724
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 33 (n + 1) := by
  have h28 : (f ![2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h28, f_dead, pp_33, pp_28]
  try (push_cast; ring)

lemma b_33 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 33 0 := by
  have h : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_473120
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 34 (n + 1) := by
  have h30 : (f ![2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 30 n := ih 30
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h30, f_dead, pp_34, pp_30]
  try (push_cast; ring)

lemma b_34 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 34 0 := by
  have h : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_473822
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 35 (n + 1) := by
  have h14 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h36 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 36 n := ih 36
  have h51 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 51 n := ih 51
  have h62 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 62 n := ih 62
  have h69 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 69 n := ih 69
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h14, h36, h51, h62, h69, f_dead, pp_35, pp_14, pp_36, pp_51, pp_62, pp_69]
  try (push_cast; ring)

lemma b_35 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 35 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 54 := by exact_mod_cast fv3_4251528
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 36 (n + 1) := by
  have h15 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h37 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 37 n := ih 37
  have h52 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 52 n := ih 52
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h15, h37, h52, f_dead, pp_36, pp_15, pp_37, pp_52]
  try (push_cast; ring)

lemma b_36 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 36 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 21 := by exact_mod_cast fv3_4252284
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 37 (n + 1) := by
  have h16 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h38 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 38 n := ih 38
  have h53 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 53 n := ih 53
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h16, h38, h53, f_dead, pp_37, pp_16, pp_38, pp_53]
  try (push_cast; ring)

lemma b_37 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 37 0 := by
  have h : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 21 := by exact_mod_cast fv3_4252770
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 38 (n + 1) := by
  have h16 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h38 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 38 n := ih 38
  have h53 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 53 n := ih 53
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h16, h38, h53, f_dead, pp_38, pp_16, pp_38, pp_53]
  try (push_cast; ring)

lemma b_38 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 38 0 := by
  have h : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 21 := by exact_mod_cast fv3_4252932
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 39 (n + 1) := by
  have h17 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h39 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h17, h39, f_dead, pp_39, pp_17, pp_39]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4252950
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 40 (n + 1) := by
  have h18 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h18, h40, f_dead, pp_40, pp_18, pp_40]
  try (push_cast; ring)

lemma b_40 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 40 0 := by
  have h : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4252956
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 41 (n + 1) := by
  have h19 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h41 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h19, h41, f_dead, pp_41, pp_19, pp_41]
  try (push_cast; ring)

lemma b_41 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 41 0 := by
  have h : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4252958
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 42 (n + 1) := by
  have h17 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h39 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h17, h39, f_dead, pp_42, pp_17, pp_39]
  try (push_cast; ring)

lemma b_42 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 42 0 := by
  have h : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4429683
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 43 (n + 1) := by
  have h17 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h39 : (f ![0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h17, h39, f_dead, pp_43, pp_17, pp_39]
  try (push_cast; ring)

lemma b_43 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 43 0 := by
  have h : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4429845
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 44 (n + 1) := by
  have h18 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h18, h40, f_dead, pp_44, pp_18, pp_40]
  try (push_cast; ring)

lemma b_44 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 44 0 := by
  have h : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4429851
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 45 (n + 1) := by
  have h19 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h41 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h19, h41, f_dead, pp_45, pp_19, pp_41]
  try (push_cast; ring)

lemma b_45 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 45 0 := by
  have h : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv3_4429853
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 46 (n + 1) := by
  have h31 : (f ![0, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 31 n := ih 31
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h31, f_dead, pp_46, pp_31]
  try (push_cast; ring)

lemma b_46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 46 0 := by
  have h : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_4488816
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 47 (n + 1) := by
  have h32 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 32 n := ih 32
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h32, f_dead, pp_47, pp_32]
  try (push_cast; ring)

lemma b_47 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 47 0 := by
  have h : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_4488818
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 48 (n + 1) := by
  have h34 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 34 n := ih 34
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h34, f_dead, pp_48, pp_34]
  try (push_cast; ring)

lemma b_48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 48 0 := by
  have h : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_4508500
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 49 (n + 1) := by
  have h32 : (f ![2, 2, 2, 1, 2, 2, 1, 0, 0, 0, 0, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 32 n := ih 32
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h32, f_dead, pp_49, pp_32]
  try (push_cast; ring)

lemma b_49 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 1] : ℚ) = PP 49 0 := by
  have h : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] 3 ![0, 0, 0, 1] : ℚ) = 1 := by exact_mod_cast fv3_4547951
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 50 (n + 1) := by
  have h20 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 20 n := ih 20
  have h42 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 42 n := ih 42
  have h54 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  have h70 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 70 n := ih 70
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h20, h42, h54, h63, h70, f_dead, pp_50, pp_20, pp_42, pp_54, pp_63, pp_70]
  try (push_cast; ring)

lemma b_50 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 50 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 44 := by exact_mod_cast fv3_6377292
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 51 (n + 1) := by
  have h20 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 20 n := ih 20
  have h42 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 42 n := ih 42
  have h54 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 54 n := ih 54
  have h63 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 63 n := ih 63
  have h70 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 70 n := ih 70
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h20, h42, h54, h63, h70, f_dead, pp_51, pp_20, pp_42, pp_54, pp_63, pp_70]
  try (push_cast; ring)

lemma b_51 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 51 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 44 := by exact_mod_cast fv3_6378048
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 52 (n + 1) := by
  have h21 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 21 n := ih 21
  have h43 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 43 n := ih 43
  have h55 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 55 n := ih 55
  have h64 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h21, h43, h55, h64, f_dead, pp_52, pp_21, pp_43, pp_55, pp_64]
  try (push_cast; ring)

lemma b_52 : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 52 0 := by
  have h : (f ![0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 31 := by exact_mod_cast fv3_6378534
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 53 (n + 1) := by
  have h21 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 21 n := ih 21
  have h43 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 43 n := ih 43
  have h55 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 55 n := ih 55
  have h64 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h21, h43, h55, h64, f_dead, pp_53, pp_21, pp_43, pp_55, pp_64]
  try (push_cast; ring)

lemma b_53 : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 53 0 := by
  have h : (f ![0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 31 := by exact_mod_cast fv3_6378696
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 54 (n + 1) := by
  have h21 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 21 n := ih 21
  have h43 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 43 n := ih 43
  have h55 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 55 n := ih 55
  have h64 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h21, h43, h55, h64, f_dead, pp_54, pp_21, pp_43, pp_55, pp_64]
  try (push_cast; ring)

lemma b_54 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 54 0 := by
  have h : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 31 := by exact_mod_cast fv3_6555447
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 55 (n + 1) := by
  have h21 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 21 n := ih 21
  have h43 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 43 n := ih 43
  have h55 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 55 n := ih 55
  have h64 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 64 n := ih 64
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h21, h43, h55, h64, f_dead, pp_55, pp_21, pp_43, pp_55, pp_64]
  try (push_cast; ring)

lemma b_55 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 55 0 := by
  have h : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 31 := by exact_mod_cast fv3_6555609
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 56 (n + 1) := by
  have h22 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 22 n := ih 22
  have h44 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 44 n := ih 44
  have h56 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h22, h44, h56, f_dead, pp_56, pp_22, pp_44, pp_56]
  try (push_cast; ring)

lemma b_56 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 56 0 := by
  have h : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 10 := by exact_mod_cast fv3_6555615
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 57 (n + 1) := by
  have h23 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 23 n := ih 23
  have h45 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 45 n := ih 45
  have h57 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 57 n := ih 57
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h23, h45, h57, f_dead, pp_57, pp_23, pp_45, pp_57]
  try (push_cast; ring)

lemma b_57 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 57 0 := by
  have h : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 10 := by exact_mod_cast fv3_6555617
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 58 (n + 1) := by
  have h22 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 22 n := ih 22
  have h44 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 44 n := ih 44
  have h56 : (f ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 56 n := ih 56
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h22, h44, h56, f_dead, pp_58, pp_22, pp_44, pp_56]
  try (push_cast; ring)

lemma b_58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 58 0 := by
  have h : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = 10 := by exact_mod_cast fv3_6614580
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 59 (n + 1) := by
  have h23 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 23 n := ih 23
  have h45 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 45 n := ih 45
  have h57 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 57 n := ih 57
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h23, h45, h57, f_dead, pp_59, pp_23, pp_45, pp_57]
  try (push_cast; ring)

lemma b_59 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 59 0 := by
  have h : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = 10 := by exact_mod_cast fv3_6614582
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 60 (n + 1) := by
  have h27 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 27 n := ih 27
  have h49 : (f ![2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 2, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 49 n := ih 49
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h27, h49, f_dead, pp_60, pp_27, pp_49]
  try (push_cast; ring)

lemma b_60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 60 0 := by
  have h : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 0, 1, 1] : ℚ) = 2 := by exact_mod_cast fv3_6634264
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 61 (n + 1) := by
  have h24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h24, h46, h58, h65, h71, f_dead, pp_61, pp_24, pp_46, pp_58, pp_65, pp_71]
  try (push_cast; ring)

lemma b_61 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 61 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 36 := by exact_mod_cast fv3_7440174
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 62 (n + 1) := by
  have h24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h24, h46, h58, h65, h71, f_dead, pp_62, pp_24, pp_46, pp_58, pp_65, pp_71]
  try (push_cast; ring)

lemma b_62 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 62 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 36 := by exact_mod_cast fv3_7440930
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 63 (n + 1) := by
  have h24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h24, h46, h58, h65, h71, f_dead, pp_63, pp_24, pp_46, pp_58, pp_65, pp_71]
  try (push_cast; ring)

lemma b_63 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 63 0 := by
  have h : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = 36 := by exact_mod_cast fv3_7618329
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 64 (n + 1) := by
  have h24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h24, h46, h58, h65, h71, f_dead, pp_64, pp_24, pp_46, pp_58, pp_65, pp_71]
  try (push_cast; ring)

lemma b_64 : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 64 0 := by
  have h : (f ![0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = 36 := by exact_mod_cast fv3_7618491
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 65 (n + 1) := by
  have h24 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 24 n := ih 24
  have h46 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 46 n := ih 46
  have h58 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 58 n := ih 58
  have h65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 65 n := ih 65
  have h71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h24, h46, h58, h65, h71, f_dead, pp_65, pp_24, pp_46, pp_58, pp_65, pp_71]
  try (push_cast; ring)

lemma b_65 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 65 0 := by
  have h : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = 36 := by exact_mod_cast fv3_7677462
  rw [h, pp_65]; try norm_num

set_option maxRecDepth 100000 in
lemma st_66 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 66 (n + 1) := by
  have h25 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 25 n := ih 25
  have h47 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 47 n := ih 47
  have h59 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 59 n := ih 59
  have h66 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 66 n := ih 66
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h25, h47, h59, h66, f_dead, pp_66, pp_25, pp_47, pp_59, pp_66]
  try (push_cast; ring)

lemma b_66 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 66 0 := by
  have h : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = 17 := by exact_mod_cast fv3_7677464
  rw [h, pp_66]; try norm_num

set_option maxRecDepth 100000 in
lemma st_67 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 67 (n + 1) := by
  have h25 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 25 n := ih 25
  have h47 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 47 n := ih 47
  have h59 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 59 n := ih 59
  have h66 : (f ![2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 66 n := ih 66
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h25, h47, h59, h66, f_dead, pp_67, pp_25, pp_47, pp_59, pp_66]
  try (push_cast; ring)

lemma b_67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 67 0 := by
  have h : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = 17 := by exact_mod_cast fv3_7697146
  rw [h, pp_67]; try norm_num

set_option maxRecDepth 100000 in
lemma st_68 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 68 (n + 1) := by
  have h26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  have h67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h26, h48, h60, h67, h72, f_dead, pp_68, pp_26, pp_48, pp_60, pp_67, pp_72]
  try (push_cast; ring)

lemma b_68 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 68 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 26 := by exact_mod_cast fv3_7971615
  rw [h, pp_68]; try norm_num

set_option maxRecDepth 100000 in
lemma st_69 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 69 (n + 1) := by
  have h26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  have h67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h48, h60, h67, h72, f_dead, pp_69, pp_26, pp_48, pp_60, pp_67, pp_72]
  try (push_cast; ring)

lemma b_69 : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 69 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 26 := by exact_mod_cast fv3_7972371
  rw [h, pp_69]; try norm_num

set_option maxRecDepth 100000 in
lemma st_70 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 70 (n + 1) := by
  have h26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  have h67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h48, h60, h67, h72, f_dead, pp_70, pp_26, pp_48, pp_60, pp_67, pp_72]
  try (push_cast; ring)

lemma b_70 : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 70 0 := by
  have h : (f ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℚ) = 26 := by exact_mod_cast fv3_8149770
  rw [h, pp_70]; try norm_num

set_option maxRecDepth 100000 in
lemma st_71 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 71 (n + 1) := by
  have h26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  have h67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h48, h60, h67, h72, f_dead, pp_71, pp_26, pp_48, pp_60, pp_67, pp_72]
  try (push_cast; ring)

lemma b_71 : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 71 0 := by
  have h : (f ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = 26 := by exact_mod_cast fv3_8208903
  rw [h, pp_71]; try norm_num

set_option maxRecDepth 100000 in
lemma st_72 (n : ℕ) (ih : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 72 (n + 1) := by
  have h26 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 26 n := ih 26
  have h48 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 48 n := ih 48
  have h60 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 60 n := ih 60
  have h67 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 67 n := ih 67
  have h72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h48, h60, h67, h72, f_dead, pp_72, pp_26, pp_48, pp_60, pp_67, pp_72]
  try (push_cast; ring)

lemma b_72 : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 72 0 := by
  have h : (f ![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = 26 := by exact_mod_cast fv3_8228587
  rw [h, pp_72]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 73, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65, b_66, b_67, b_68, b_69, b_70, b_71, b_72]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih, st_66 n ih, st_67 n ih, st_68 n ih, st_69 n ih, st_70 n ih, st_71 n ih, st_72 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 4) : ℚ) = ((1 : ℚ) / 40320) * (m : ℚ) ^ 8 + ((1 : ℚ) / 1440) * (m : ℚ) ^ 7 + ((43 : ℚ) / 2880) * (m : ℚ) ^ 6 + ((91 : ℚ) / 360) * (m : ℚ) ^ 5 + ((15407 : ℚ) / 5760) * (m : ℚ) ^ 4 + ((27679 : ℚ) / 1440) * (m : ℚ) ^ 3 + ((915367 : ℚ) / 10080) * (m : ℚ) ^ 2 + ((9361 : ℚ) / 40) * (m : ℚ) ^ 1 + (249 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g35 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 1] : ℚ) = PP 35 m := f_closed m 35
  have g50 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 1] : ℚ) = PP 50 m := f_closed m 50
  have g61 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 1] : ℚ) = PP 61 m := f_closed m 61
  have g68 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 1] : ℚ) = PP 68 m := f_closed m 68
  rw [show m + 4 = (m + 3) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 12 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g35, g50, g61, g68, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_35, pp_50, pp_61, pp_68]
  ring

lemma aS1 : (a 1 : ℚ) = 5 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 12 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 25 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 12 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 12 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_4251528, fv1_6377292, fv1_7440174, fv1_7971615]
  norm_num

lemma aS3 : (a 3 : ℚ) = 89 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 12 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 12 → Fin 3) (r : R), (f c 2 r : ℚ) = ((f c 2 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv2_0, fv2_4251528, fv2_6377292, fv2_7440174, fv2_7971615]
  norm_num

lemma av (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((-1 : ℚ) / 10080) * (n : ℚ) ^ 7 + ((19 : ℚ) / 2880) * (n : ℚ) ^ 6 + ((7 : ℚ) / 180) * (n : ℚ) ^ 5 + ((527 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((3683 : ℚ) / 1440) * (n : ℚ) ^ 3 + ((4051 : ℚ) / 10080) * (n : ℚ) ^ 2 + ((-1707 : ℚ) / 280) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [aS3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 + 28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) + C (9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 8) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 9) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 + 28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : PowerSeries ℚ) =
        C (5 : ℚ) * X ^ 0 + C (-20 : ℚ) * X ^ 1 + C (44 : ℚ) * X ^ 2 + C (-72 : ℚ) * X ^ 3 + C (89 : ℚ) * X ^ 4 + C (-70 : ℚ) * X ^ 5 + C (28 : ℚ) * X ^ 6 + C (-4 : ℚ) * X ^ 7 + C (4 : ℚ) * X ^ 8 + C (-4 : ℚ) * X ^ 9 + C (1 : ℚ) * X ^ 10 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 5 := aS1
    have e2 : (a 2 : ℚ) = 25 := aS2
    have e3 : (a 3 : ℚ) = 89 := aS3
    have e4 : (a 4 : ℚ) = 249 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 596 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 1286 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 2578 := by rw [av 7 (by norm_num)]; norm_num
    have e8 : (a 8 : ℚ) = 4886 := by rw [av 8 (by norm_num)]; norm_num
    have e9 : (a 9 : ℚ) = 8851 := by rw [av 9 (by norm_num)]; norm_num
    have e10 : (a 10 : ℚ) = 15439 := by rw [av 10 (by norm_num)]; norm_num
    have e11 : (a 11 : ℚ) = 26072 := by rw [av 11 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 11 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 11 := ⟨c - 11, by omega⟩
      simp only [show m + 11 - 0 = m + 11 by omega, show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega, show 0 ≤ m + 11 by omega, show 1 ≤ m + 11 by omega, show 2 ≤ m + 11 by omega, show 3 ≤ m + 11 by omega, show 4 ≤ m + 11 by omega, show 5 ≤ m + 11 by omega, show 6 ≤ m + 11 by omega, show 7 ≤ m + 11 by omega, show 8 ≤ m + 11 by omega, show 9 ≤ m + 11 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 11 + 1) (by omega), av (m + 10 + 1) (by omega), av (m + 9 + 1) (by omega), av (m + 8 + 1) (by omega), av (m + 7 + 1) (by omega), av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega, show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega, show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega, show m + 12 - 9 = m + 3 by omega]
    qify
    rw [av (m + 12) (by omega), av (m + 11) (by omega), av (m + 10) (by omega), av (m + 9) (by omega), av (m + 8) (by omega), av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega)]
    push_cast; ring

end OMA.P_oeis_a223840

theorem OMA.solution : type_of% @OMA.S_oeis_a223840.main := OMA.P_oeis_a223840.full
