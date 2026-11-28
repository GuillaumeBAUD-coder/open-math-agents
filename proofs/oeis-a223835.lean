import OMAStatements.S_oeis_a223835
import Mathlib

/-!
# oeis-a223835: counting the n X 5 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 5 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 3 it is an explicit polynomial, checked by induction over the
138 states (c, r) whose top row is allowed, from exact values at n = 1..3. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223835, https://oeis.org/A223835.
-/
namespace OMA.P_oeis_a223835

open OMA.S_oeis_a223835

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

def diagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 5 then r ⟨j, h⟩ :: diagF l (j + 1) else []

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

lemma dg_cons3 (r : R) (l : List R) : diagF (r :: l) 3 = r 3 :: diagF l 4 := by
  simp [diagF]

lemma dg_cons4 (r : R) (l : List R) : diagF (r :: l) 4 = [r 4] := by
  cases l <;> simp [diagF]

lemma gdrop (l : List R) : (∀ i, Acc 0 (diagF (l.drop i) 0) = true) ↔
    Acc 0 (diagF l 0) = true ∧ ∀ i, Acc 0 (diagF (l.drop (i + 1)) 0) = true :=
  forall_drop (fun L => Acc 0 (diagF L 0) = true) l

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 5) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 10 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true ∧ okb (c 4) (r 4) = true ∧ okb (c 5) (r 0) = true ∧ okb (c 6) (r 1) = true ∧ okb (c 7) (r 2) = true ∧ okb (c 8) (r 3) = true ∧ okb (c 9) (r 4) = true

instance (c : Fin 10 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 10 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ Acc (c 0) (adiagF l 0) = true ∧ Acc (c 1) (adiagF l 1) = true ∧ Acc (c 2) (adiagF l 2) = true ∧ Acc (c 3) (adiagF l 3) = true ∧ Acc (c 4) (adiagF l 4) = true ∧ Acc (c 5) (diagF l 0) = true ∧ Acc (c 6) (diagF l 1) = true ∧ Acc (c 7) (diagF l 2) = true ∧ Acc (c 8) (diagF l 3) = true ∧ Acc (c 9) (diagF l 4) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 4) = true) ∧ (∀ i, Acc 0 (diagF (l.drop (i + 1)) 0) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 4)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 4) = true by simp only [adiag_map, uniAcc], fdrop]
  rw [show (∀ i, Unimodal (diagFrom (l.drop i) 0)) ↔ ∀ i, Acc 0 (diagF (l.drop i) 0) = true by simp only [diag_map, uniAcc], gdrop]
  simp only [rowUni, adiag_map, uniAcc, ltK, diag_map, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    ]
  tauto

lemma Q_single (c : Fin 10 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF, diagF]

lemma Q_cons (c : Fin 10 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 4) (r 4), 0, 0, dl (c 5) (r 0), dl (c 6) (r 1), dl (c 7) (r 2), dl (c 8) (r 3)] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, ad_cons3, ad_cons4, List.drop_succ_cons, dg_cons0, dg_cons1, dg_cons2, dg_cons3, dg_cons4, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l), gdrop (s :: l)]
  simp only [ad_cons4, dg_cons0, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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

noncomputable def f (c : Fin 10 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 10 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 10 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), dl (c 4) (r 4), 0, 0, dl (c 5) (r 0), dl (c 6) (r 1), dl (c 7) (r 2), dl (c 8) (r 3)] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 10 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Fin 3) (r0 r1 r2 r3 r4 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] (n + 1) ![r0, r1, r2, r3, r4] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] ![r0, r1, r2, r3, r4] ∧ adj ![r0, r1, r2, r3, r4] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c4) (r4), 0, 0, dl (c5) (r0), dl (c6) (r1), dl (c7) (r2), dl (c8) (r3)] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Fin 3) (r0 r1 r2 r3 r4 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] (n + 1) ![r0, r1, r2, r3, r4] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] ![r0, r1, r2, r3, r4] ∧ adj ![r0, r1, r2, r3, r4] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), dl (c4) (r4), 0, 0, dl (c5) (r0), dl (c6) (r1), dl (c7) (r2), dl (c8) (r3)] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_944784 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_472392 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1417176 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_236196 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 0, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_708588 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1653372 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_118098 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_354294 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_826686 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1771470 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_59049 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 0, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_177147 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_413343 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_885735 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1830519 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_59778 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 1 ![1, 0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_177876 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_414072 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_886464 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1831248 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_64152 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 1 ![1, 0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_182250 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_77274 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 1 ![1, 0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_195372 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_116640 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 1 ![1, 0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_234738 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_944811 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1417203 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1653399 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1771497 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1830546 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_492084 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436868 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_728280 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673064 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_846378 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1791162 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_905427 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1850211 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436895 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673091 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1791189 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1850238 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_944829 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1417221 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_242760 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_715152 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1659936 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_360858 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_833250 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1778034 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_419907 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_892299 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1837083 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_734844 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1679628 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_852942 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1797726 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_911991 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1856775 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1679655 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1797753 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1856802 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_492090 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436874 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_728286 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673070 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436901 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673097 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_944835 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1417227 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_120286 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![0, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_356482 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_828874 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1773658 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_179335 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_415531 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_887923 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1832707 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_133408 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 1 ![0, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_369604 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_192457 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_428653 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_172774 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 1 ![0, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_408970 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_231823 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_468019 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_180064 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_416260 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_888652 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1833436 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_193186 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_429382 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_232552 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 1 ![1, 1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_468748 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_363046 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_835438 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1780222 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_422095 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_894487 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1839271 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_402412 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_874804 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_461461 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_933853 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_422824 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_895216 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1840000 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_462190 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 1 ![1, 1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_934582 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_855130 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1799914 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_914179 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1858963 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_914908 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 1 ![1, 1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1859692 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1799941 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1858990 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1859719 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] 1 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_282128 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_754520 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_400226 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_872618 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_734846 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1679630 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_852944 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1797728 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1679657 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1797755 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 1 ![0, 1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_492092 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436876 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_728288 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673072 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1436903 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1673099 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 1 ![0, 0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_944837 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1417229 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 1 ![0, 0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 0] : ℤ) = 86 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_944784, fv1_472392, fv1_1417176, fv1_236196, fv1_708588, fv1_1653372, fv1_118098, fv1_354294, fv1_826686, fv1_1771470, fv1_59049, fv1_177147, fv1_413343, fv1_885735, fv1_1830519, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_944784 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_944811, fv1_1417203, fv1_1653399, fv1_1771497, fv1_1830546, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_472392 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 0] : ℤ) = 24 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_492084, fv1_1436868, fv1_728280, fv1_1673064, fv1_846378, fv1_1791162, fv1_905427, fv1_1850211, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1417176 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1436895, fv1_1673091, fv1_1791189, fv1_1850238, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_236196 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 0, 0] : ℤ) = 25 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_242760, fv1_715152, fv1_1659936, fv1_360858, fv1_833250, fv1_1778034, fv1_419907, fv1_892299, fv1_1837083, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_708588 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_734844, fv1_1679628, fv1_852942, fv1_1797726, fv1_911991, fv1_1856775, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1653372 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1679655, fv1_1797753, fv1_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_118098 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 0, 0, 0] : ℤ) = 24 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_120286, fv1_356482, fv1_828874, fv1_1773658, fv1_179335, fv1_415531, fv1_887923, fv1_1832707, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_354294 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_363046, fv1_835438, fv1_1780222, fv1_422095, fv1_894487, fv1_1839271, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_826686 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1771470 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_59049 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 0, 0, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_59778, fv1_177876, fv1_414072, fv1_886464, fv1_1831248, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_177147 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_180064, fv1_416260, fv1_888652, fv1_1833436, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_413343 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_422824, fv1_895216, fv1_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_885735 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1830519 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_59778 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 2 ![1, 0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_64152, fv1_182250, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_177876 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_180064, fv1_416260, fv1_888652, fv1_1833436, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_414072 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_422824, fv1_895216, fv1_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_886464 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1831248 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_64152 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 2 ![1, 0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_77274, fv1_195372, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_182250 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_193186, fv1_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_77274 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 2 ![1, 0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_116640, fv1_234738, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_195372 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_116640 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 2 ![1, 0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_116640, fv1_234738, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_234738 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_944811 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_944829, fv1_1417221, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1417203 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1436895, fv1_1673091, fv1_1791189, fv1_1850238, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1653399 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1679655, fv1_1797753, fv1_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1771497 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1830546 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_492084 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_492090, fv1_1436874, fv1_728286, fv1_1673070, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436868 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_1436901, fv1_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_728280 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_734844, fv1_1679628, fv1_852942, fv1_1797726, fv1_911991, fv1_1856775, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673064 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1679655, fv1_1797753, fv1_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_846378 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1791162 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_905427 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1850211 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436895 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1436901, fv1_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673091 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1679655, fv1_1797753, fv1_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1791189 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1850238 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_944829 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_944835, fv1_1417227, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1417221 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1436901, fv1_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_242760 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 0, 1, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_282128, fv1_754520, fv1_400226, fv1_872618, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_715152 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1659936 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_360858 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_833250 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1778034 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_419907 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_892299 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1837083 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_734844 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1679628 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_852942 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1797726 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_911991 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1856775 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1679655 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1797753 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1856802 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_492090 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_492092, fv1_1436876, fv1_728288, fv1_1673072, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436874 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_728286 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673070 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436901 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673097 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_944835 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_944837, fv1_1417229, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1417227 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_120286 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![0, 1, 0, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_133408, fv1_369604, fv1_192457, fv1_428653, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_356482 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_363046, fv1_835438, fv1_1780222, fv1_422095, fv1_894487, fv1_1839271, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_828874 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1773658 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_179335 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_193186, fv1_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_415531 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_422824, fv1_895216, fv1_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_887923 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1832707 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_133408 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 2 ![0, 1, 0, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_172774, fv1_408970, fv1_231823, fv1_468019, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_369604 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_192457 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_428653 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_172774 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 2 ![0, 1, 0, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_172774, fv1_408970, fv1_231823, fv1_468019, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_408970 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_231823 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_468019 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_180064 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_193186, fv1_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_416260 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_422824, fv1_895216, fv1_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_888652 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1833436 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_193186 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_429382 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_232552 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 2 ![1, 1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_232552, fv1_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_468748 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_363046 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_835438 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1780222 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_422095 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_894487 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1839271 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_402412 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_874804 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_461461 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_933853 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_422824 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_895216 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1840000 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_462190 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 2 ![1, 1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_462190, fv1_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_934582 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_855130 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1799914 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_914179 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1858963 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_914908 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 2 ![1, 1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_914908, fv1_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1859692 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1799941 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1858990 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1859719 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] 2 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_282128 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 0, 1, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_282128, fv1_754520, fv1_400226, fv1_872618, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_754520 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_400226 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 1, 0, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_402412, fv1_874804, fv1_461461, fv1_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_872618 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_734846 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1679630 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_852944 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_855130, fv1_1799914, fv1_914179, fv1_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1797728 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1679657 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1797755 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 2 ![0, 1, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_1799941, fv1_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_492092 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_492092, fv1_1436876, fv1_728288, fv1_1673072, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436876 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_728288 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_734846, fv1_1679630, fv1_852944, fv1_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673072 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1436903 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1673099 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 2 ![0, 0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1679657, fv1_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_944837 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_944837, fv1_1417229, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1417229 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 2 ![0, 0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_1436903, fv1_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℤ) = 255 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_0, fv2_944784, fv2_472392, fv2_1417176, fv2_236196, fv2_708588, fv2_1653372, fv2_118098, fv2_354294, fv2_826686, fv2_1771470, fv2_59049, fv2_177147, fv2_413343, fv2_885735, fv2_1830519, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_944784 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_944811, fv2_1417203, fv2_1653399, fv2_1771497, fv2_1830546, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_472392 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℤ) = 52 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_492084, fv2_1436868, fv2_728280, fv2_1673064, fv2_846378, fv2_1791162, fv2_905427, fv2_1850211, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1417176 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1436895, fv2_1673091, fv2_1791189, fv2_1850238, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_236196 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℤ) = 64 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_242760, fv2_715152, fv2_1659936, fv2_360858, fv2_833250, fv2_1778034, fv2_419907, fv2_892299, fv2_1837083, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_708588 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_734844, fv2_1679628, fv2_852942, fv2_1797726, fv2_911991, fv2_1856775, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1653372 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1679655, fv2_1797753, fv2_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_118098 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℤ) = 52 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_120286, fv2_356482, fv2_828874, fv2_1773658, fv2_179335, fv2_415531, fv2_887923, fv2_1832707, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_354294 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_363046, fv2_835438, fv2_1780222, fv2_422095, fv2_894487, fv2_1839271, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_826686 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1771470 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_59049 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℤ) = 21 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_59778, fv2_177876, fv2_414072, fv2_886464, fv2_1831248, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_177147 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_180064, fv2_416260, fv2_888652, fv2_1833436, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_413343 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_422824, fv2_895216, fv2_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_885735 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1830519 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_59778 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_64152, fv2_182250, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_177876 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_180064, fv2_416260, fv2_888652, fv2_1833436, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_414072 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_422824, fv2_895216, fv2_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_886464 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1831248 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_64152 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 0, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_77274, fv2_195372, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_182250 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_193186, fv2_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_77274 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 0, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_116640, fv2_234738, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_195372 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_116640 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 0, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_116640, fv2_234738, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_234738 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_944811 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_944829, fv2_1417221, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1417203 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 13 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1436895, fv2_1673091, fv2_1791189, fv2_1850238, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1653399 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1679655, fv2_1797753, fv2_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1771497 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1830546 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_492084 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_492090, fv2_1436874, fv2_728286, fv2_1673070, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436868 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_1436901, fv2_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_728280 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_734844, fv2_1679628, fv2_852942, fv2_1797726, fv2_911991, fv2_1856775, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673064 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1679655, fv2_1797753, fv2_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_846378 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1791162 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_905427 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1850211 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436895 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1436901, fv2_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673091 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1679655, fv2_1797753, fv2_1856802, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1791189 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1850238 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_944829 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_944835, fv2_1417227, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1417221 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1436901, fv2_1673097, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_242760 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 0, 0] : ℤ) = 49 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_282128, fv2_754520, fv2_400226, fv2_872618, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_715152 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1659936 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_360858 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_833250 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1778034 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_419907 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_892299 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1837083 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_734844 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1679628 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_852942 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1797726 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_911991 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1856775 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1679655 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1797753 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1856802 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_492090 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_492092, fv2_1436876, fv2_728288, fv2_1673072, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436874 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_728286 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673070 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436901 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673097 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_944835 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_944837, fv2_1417229, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1417227 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_120286 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 0, 0, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_133408, fv2_369604, fv2_192457, fv2_428653, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_356482 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_363046, fv2_835438, fv2_1780222, fv2_422095, fv2_894487, fv2_1839271, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_828874 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1773658 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_179335 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_193186, fv2_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_415531 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_422824, fv2_895216, fv2_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_887923 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1832707 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_133408 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 0, 0, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_172774, fv2_408970, fv2_231823, fv2_468019, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_369604 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_192457 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_428653 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_172774 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 0, 0, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_172774, fv2_408970, fv2_231823, fv2_468019, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_408970 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_231823 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_468019 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_180064 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_193186, fv2_429382, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_416260 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_422824, fv2_895216, fv2_1840000, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_888652 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1833436 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_193186 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_429382 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_232552 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_232552, fv2_468748, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_468748 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_363046 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_835438 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1780222 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_422095 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_894487 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1839271 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_402412 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_874804 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_461461 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_933853 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_422824 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_895216 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1840000 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_462190 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_462190, fv2_934582, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_934582 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_855130 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1799914 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_914179 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1858963 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_914908 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_914908, fv2_1859692, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1859692 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1799941 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1858990 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1859719 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_1859719, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_282128 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 0, 0] : ℤ) = 49 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_282128, fv2_754520, fv2_400226, fv2_872618, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_754520 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_400226 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_402412, fv2_874804, fv2_461461, fv2_933853, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_872618 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_734846 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1679630 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_852944 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_855130, fv2_1799914, fv2_914179, fv2_1858963, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1797728 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1679657 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1797755 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_1799941, fv2_1858990, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_492092 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_492092, fv2_1436876, fv2_728288, fv2_1673072, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436876 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_728288 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_734846, fv2_1679630, fv2_852944, fv2_1797728, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673072 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1436903 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1673099 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1679657, fv2_1797755, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_944837 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_944837, fv2_1417229, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1417229 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_1436903, fv2_1673099, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 138 → Fin 10 → Fin 3 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0], ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2], ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2], ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2], ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1], ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1], ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1], ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1], ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1], ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1]]

set_option maxRecDepth 100000 in
def rs : Fin 138 → R := ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 138 → ℕ → ℚ := ![fun n => ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((13 : ℚ) / 6) * (n : ℚ) ^ 4 + ((103 : ℚ) / 6) * (n : ℚ) ^ 3 + ((497 : ℚ) / 6) * (n : ℚ) ^ 2 + ((2387 : ℚ) / 10) * (n : ℚ) ^ 1 + (255 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((81 : ℚ) / 4) * (n : ℚ) ^ 2 + (56 : ℚ) * (n : ℚ) ^ 1 + (64 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((77 : ℚ) / 4) * (n : ℚ) ^ 2 + (49 : ℚ) * (n : ℚ) ^ 1 + (49 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((77 : ℚ) / 4) * (n : ℚ) ^ 2 + (49 : ℚ) * (n : ℚ) ^ 1 + (49 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((13 : ℚ) / 6) * (n : ℚ) ^ 4 + ((103 : ℚ) / 6) * (n : ℚ) ^ 3 + ((497 : ℚ) / 6) * (n : ℚ) ^ 2 + ((2387 : ℚ) / 10) * (n : ℚ) ^ 1 + (255 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((81 : ℚ) / 4) * (n : ℚ) ^ 2 + (56 : ℚ) * (n : ℚ) ^ 1 + (64 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((77 : ℚ) / 4) * (n : ℚ) ^ 2 + (49 : ℚ) * (n : ℚ) ^ 1 + (49 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = ((1 : ℚ) / 4) * (n : ℚ) ^ 4 + ((7 : ℚ) / 2) * (n : ℚ) ^ 3 + ((77 : ℚ) / 4) * (n : ℚ) ^ 2 + (49 : ℚ) * (n : ℚ) ^ 1 + (49 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

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
lemma pp_30 (n : ℕ) : PP 30 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((37 : ℚ) / 3) * (n : ℚ) ^ 2 + ((115 : ℚ) / 3) * (n : ℚ) ^ 1 + (52 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((13 : ℚ) / 6) * (n : ℚ) ^ 3 + ((34 : ℚ) / 3) * (n : ℚ) ^ 2 + ((88 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (22 : ℚ) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + ((11 : ℚ) / 2) * (n : ℚ) ^ 2 + (21 : ℚ) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_66 (n : ℕ) : PP 66 n = (1 : ℚ) * (n : ℚ) ^ 2 + (8 : ℚ) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_67 (n : ℕ) : PP 67 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_68 (n : ℕ) : PP 68 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_69 (n : ℕ) : PP 69 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_70 (n : ℕ) : PP 70 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_71 (n : ℕ) : PP 71 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_72 (n : ℕ) : PP 72 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_73 (n : ℕ) : PP 73 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_74 (n : ℕ) : PP 74 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_75 (n : ℕ) : PP 75 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_76 (n : ℕ) : PP 76 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_77 (n : ℕ) : PP 77 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_78 (n : ℕ) : PP 78 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_79 (n : ℕ) : PP 79 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_80 (n : ℕ) : PP 80 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((59 : ℚ) / 24) * (n : ℚ) ^ 2 + ((121 : ℚ) / 12) * (n : ℚ) ^ 1 + (21 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_81 (n : ℕ) : PP 81 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_82 (n : ℕ) : PP 82 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_83 (n : ℕ) : PP 83 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_84 (n : ℕ) : PP 84 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_85 (n : ℕ) : PP 85 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_86 (n : ℕ) : PP 86 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((19 : ℚ) / 3) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_87 (n : ℕ) : PP 87 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_88 (n : ℕ) : PP 88 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_89 (n : ℕ) : PP 89 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_90 (n : ℕ) : PP 90 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_91 (n : ℕ) : PP 91 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_92 (n : ℕ) : PP 92 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_93 (n : ℕ) : PP 93 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_94 (n : ℕ) : PP 94 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_95 (n : ℕ) : PP 95 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_96 (n : ℕ) : PP 96 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_97 (n : ℕ) : PP 97 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_98 (n : ℕ) : PP 98 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_99 (n : ℕ) : PP 99 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_100 (n : ℕ) : PP 100 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_101 (n : ℕ) : PP 101 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_102 (n : ℕ) : PP 102 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_103 (n : ℕ) : PP 103 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_104 (n : ℕ) : PP 104 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_105 (n : ℕ) : PP 105 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_106 (n : ℕ) : PP 106 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_107 (n : ℕ) : PP 107 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_108 (n : ℕ) : PP 108 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_109 (n : ℕ) : PP 109 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_110 (n : ℕ) : PP 110 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_111 (n : ℕ) : PP 111 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_112 (n : ℕ) : PP 112 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_113 (n : ℕ) : PP 113 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_114 (n : ℕ) : PP 114 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_115 (n : ℕ) : PP 115 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_116 (n : ℕ) : PP 116 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_117 (n : ℕ) : PP 117 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_118 (n : ℕ) : PP 118 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_119 (n : ℕ) : PP 119 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_120 (n : ℕ) : PP 120 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_121 (n : ℕ) : PP 121 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_122 (n : ℕ) : PP 122 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_123 (n : ℕ) : PP 123 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_124 (n : ℕ) : PP 124 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_125 (n : ℕ) : PP 125 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_126 (n : ℕ) : PP 126 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_127 (n : ℕ) : PP 127 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_128 (n : ℕ) : PP 128 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_129 (n : ℕ) : PP 129 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_130 (n : ℕ) : PP 130 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_131 (n : ℕ) : PP 131 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_132 (n : ℕ) : PP 132 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_133 (n : ℕ) : PP 133 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_134 (n : ℕ) : PP 134 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_135 (n : ℕ) : PP 135 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_136 (n : ℕ) : PP 136 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_137 (n : ℕ) : PP 137 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h80 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 80 n := ih 80
  have h45 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 45 n := ih 45
  have h85 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 85 n := ih 85
  have h21 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 21 n := ih 21
  have h49 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 49 n := ih 49
  have h96 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  have h6 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 6 n := ih 6
  have h24 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 24 n := ih 24
  have h57 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 57 n := ih 57
  have h109 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 109 n := ih 109
  have h1 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h10 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h32 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 32 n := ih 32
  have h67 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 67 n := ih 67
  have h122 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 122 n := ih 122
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h80, h45, h85, h21, h49, h96, h6, h24, h57, h109, h1, h10, h32, h67, h122, f_dead, pp_0, pp_0, pp_80, pp_45, pp_85, pp_21, pp_49, pp_96, pp_6, pp_24, pp_57, pp_109, pp_1, pp_10, pp_32, pp_67, pp_122]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 0] : ℚ) = 255 := by exact_mod_cast fv3_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h2 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h11 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 11 n := ih 11
  have h33 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h68 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 68 n := ih 68
  have h124 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 124 n := ih 124
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h2, h11, h33, h68, h124, f_dead, pp_1, pp_2, pp_11, pp_33, pp_68, pp_124]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = 21 := by exact_mod_cast fv3_59049
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h3 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h14 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 14 n := ih 14
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h3, h14, f_dead, pp_2, pp_3, pp_14]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_59778
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h4 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h17 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 17 n := ih 17
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h4, h17, f_dead, pp_3, pp_4, pp_17]
  try (push_cast; ring)

lemma b_3 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_64152
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h5 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h20 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 20 n := ih 20
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h5, h20, f_dead, pp_4, pp_5, pp_20]
  try (push_cast; ring)

lemma b_4 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 0, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_77274
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3 + 1) ![1, 0, 0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h5 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h20 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 20 n := ih 20
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h5, h20, f_dead, pp_5, pp_5, pp_20]
  try (push_cast; ring)

lemma b_5 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 0, 0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 0, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_116640
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h7 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h25 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 25 n := ih 25
  have h58 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 58 n := ih 58
  have h111 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 111 n := ih 111
  have h12 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h34 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 34 n := ih 34
  have h69 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 69 n := ih 69
  have h125 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 125 n := ih 125
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h7, h25, h58, h111, h12, h34, h69, h125, f_dead, pp_6, pp_7, pp_25, pp_58, pp_111, pp_12, pp_34, pp_69, pp_125]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = 52 := by exact_mod_cast fv3_118098
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h8 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 8 n := ih 8
  have h28 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 28 n := ih 28
  have h15 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h39 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h8, h28, h15, h39, f_dead, pp_7, pp_8, pp_28, pp_15, pp_39]
  try (push_cast; ring)

lemma b_7 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = 32 := by exact_mod_cast fv3_120286
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h9 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h31 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 31 n := ih 31
  have h18 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h43 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h9, h31, h18, h43, f_dead, pp_8, pp_9, pp_31, pp_18, pp_43]
  try (push_cast; ring)

lemma b_8 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 0, 0, 0] : ℚ) = 32 := by exact_mod_cast fv3_133408
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3 + 1) ![0, 1, 0, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h9 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h31 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 31 n := ih 31
  have h18 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h43 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h9, h31, h18, h43, f_dead, pp_9, pp_9, pp_31, pp_18, pp_43]
  try (push_cast; ring)

lemma b_9 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 0, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 0, 0, 0] : ℚ) = 32 := by exact_mod_cast fv3_172774
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h13 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h35 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  have h70 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h126 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 126 n := ih 126
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h13, h35, h70, h126, f_dead, pp_10, pp_13, pp_35, pp_70, pp_126]
  try (push_cast; ring)

lemma b_10 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 13 := by exact_mod_cast fv3_177147
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h13 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  have h35 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  have h70 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h126 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 126 n := ih 126
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h13, h35, h70, h126, f_dead, pp_11, pp_13, pp_35, pp_70, pp_126]
  try (push_cast; ring)

lemma b_11 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 13 := by exact_mod_cast fv3_177876
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h16 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h40 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h16, h40, f_dead, pp_12, pp_16, pp_40]
  try (push_cast; ring)

lemma b_12 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_179335
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h16 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h40 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h16, h40, f_dead, pp_13, pp_16, pp_40]
  try (push_cast; ring)

lemma b_13 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_180064
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h16 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  have h40 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h16, h40, f_dead, pp_14, pp_16, pp_40]
  try (push_cast; ring)

lemma b_14 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_182250
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h19, h44, f_dead, pp_15, pp_19, pp_44]
  try (push_cast; ring)

lemma b_15 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_192457
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 16 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h19, h44, f_dead, pp_16, pp_19, pp_44]
  try (push_cast; ring)

lemma b_16 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 16 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_193186
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 17 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h19, h44, f_dead, pp_17, pp_19, pp_44]
  try (push_cast; ring)

lemma b_17 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 17 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 0] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_195372
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 18 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h19, h44, f_dead, pp_18, pp_19, pp_44]
  try (push_cast; ring)

lemma b_18 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 18 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_231823
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 19 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h19, h44, f_dead, pp_19, pp_19, pp_44]
  try (push_cast; ring)

lemma b_19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 19 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_232552
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] (n + 3 + 1) ![1, 1, 0, 0, 0] : ℚ) = PP 20 (n + 1) := by
  have h19 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  have h44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h19, h44, f_dead, pp_20, pp_19, pp_44]
  try (push_cast; ring)

lemma b_20 : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = PP 20 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 2, 2, 2] 3 ![1, 1, 0, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_234738
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 21 (n + 1) := by
  have h22 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 22 n := ih 22
  have h50 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 50 n := ih 50
  have h98 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 98 n := ih 98
  have h26 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 26 n := ih 26
  have h59 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 59 n := ih 59
  have h112 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 112 n := ih 112
  have h36 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 36 n := ih 36
  have h71 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 71 n := ih 71
  have h127 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 127 n := ih 127
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h22, h50, h98, h26, h59, h112, h36, h71, h127, f_dead, pp_21, pp_22, pp_50, pp_98, pp_26, pp_59, pp_112, pp_36, pp_71, pp_127]
  try (push_cast; ring)

lemma b_21 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 21 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = 64 := by exact_mod_cast fv3_236196
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 22 (n + 1) := by
  have h23 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 23 n := ih 23
  have h56 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 56 n := ih 56
  have h29 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 29 n := ih 29
  have h65 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h23, h56, h29, h65, f_dead, pp_22, pp_23, pp_56, pp_29, pp_65]
  try (push_cast; ring)

lemma b_22 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 22 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 0, 0] : ℚ) = 49 := by exact_mod_cast fv3_242760
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3 + 1) ![0, 0, 1, 0, 0] : ℚ) = PP 23 (n + 1) := by
  have h23 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 23 n := ih 23
  have h56 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 56 n := ih 56
  have h29 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 29 n := ih 29
  have h65 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 65 n := ih 65
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h23, h56, h29, h65, f_dead, pp_23, pp_23, pp_56, pp_29, pp_65]
  try (push_cast; ring)

lemma b_23 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 0, 0] : ℚ) = PP 23 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 0, 0] : ℚ) = 49 := by exact_mod_cast fv3_282128
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 24 (n + 1) := by
  have h27 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 27 n := ih 27
  have h60 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 60 n := ih 60
  have h113 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 113 n := ih 113
  have h37 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 37 n := ih 37
  have h72 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 72 n := ih 72
  have h128 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 128 n := ih 128
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h27, h60, h113, h37, h72, h128, f_dead, pp_24, pp_27, pp_60, pp_113, pp_37, pp_72, pp_128]
  try (push_cast; ring)

lemma b_24 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 24 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 32 := by exact_mod_cast fv3_354294
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 25 (n + 1) := by
  have h27 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 27 n := ih 27
  have h60 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 60 n := ih 60
  have h113 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 113 n := ih 113
  have h37 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 37 n := ih 37
  have h72 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 72 n := ih 72
  have h128 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 128 n := ih 128
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h27, h60, h113, h37, h72, h128, f_dead, pp_25, pp_27, pp_60, pp_113, pp_37, pp_72, pp_128]
  try (push_cast; ring)

lemma b_25 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 25 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 32 := by exact_mod_cast fv3_356482
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 26 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h30, h66, h41, h78, f_dead, pp_26, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_26 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 26 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_360858
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 27 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h30, h66, h41, h78, f_dead, pp_27, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_27 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 27 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_363046
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 28 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h30, h66, h41, h78, f_dead, pp_28, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_28 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 28 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_369604
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 29 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h30, h66, h41, h78, f_dead, pp_29, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_29 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 29 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_400226
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 30 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h30, h66, h41, h78, f_dead, pp_30, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 30 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_402412
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3 + 1) ![0, 1, 1, 0, 0] : ℚ) = PP 31 (n + 1) := by
  have h30 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 41 n := ih 41
  have h78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 78 n := ih 78
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h30, h66, h41, h78, f_dead, pp_31, pp_30, pp_66, pp_41, pp_78]
  try (push_cast; ring)

lemma b_31 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = PP 31 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![0, 1, 1, 0, 0] : ℚ) = 28 := by exact_mod_cast fv3_408970
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 32 (n + 1) := by
  have h38 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  have h129 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 129 n := ih 129
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h38, h73, h129, f_dead, pp_32, pp_38, pp_73, pp_129]
  try (push_cast; ring)

lemma b_32 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 32 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_413343
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 33 (n + 1) := by
  have h38 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  have h129 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 129 n := ih 129
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h38, h73, h129, f_dead, pp_33, pp_38, pp_73, pp_129]
  try (push_cast; ring)

lemma b_33 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 33 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_414072
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 34 (n + 1) := by
  have h38 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  have h129 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 129 n := ih 129
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h38, h73, h129, f_dead, pp_34, pp_38, pp_73, pp_129]
  try (push_cast; ring)

lemma b_34 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 34 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_415531
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 35 (n + 1) := by
  have h38 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  have h129 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 129 n := ih 129
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h38, h73, h129, f_dead, pp_35, pp_38, pp_73, pp_129]
  try (push_cast; ring)

lemma b_35 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 35 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 8 := by exact_mod_cast fv3_416260
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 36 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h42, h79, f_dead, pp_36, pp_42, pp_79]
  try (push_cast; ring)

lemma b_36 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 36 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_419907
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 37 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h42, h79, f_dead, pp_37, pp_42, pp_79]
  try (push_cast; ring)

lemma b_37 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 37 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_422095
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 38 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h42, h79, f_dead, pp_38, pp_42, pp_79]
  try (push_cast; ring)

lemma b_38 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 38 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_422824
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 39 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h42, h79, f_dead, pp_39, pp_42, pp_79]
  try (push_cast; ring)

lemma b_39 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 39 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_428653
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 40 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h42, h79, f_dead, pp_40, pp_42, pp_79]
  try (push_cast; ring)

lemma b_40 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 40 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 0] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_429382
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 41 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h42, h79, f_dead, pp_41, pp_42, pp_79]
  try (push_cast; ring)

lemma b_41 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 41 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_461461
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 42 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h42, h79, f_dead, pp_42, pp_42, pp_79]
  try (push_cast; ring)

lemma b_42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 42 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_462190
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 43 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h42, h79, f_dead, pp_43, pp_42, pp_79]
  try (push_cast; ring)

lemma b_43 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 43 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_468019
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] (n + 3 + 1) ![1, 1, 1, 0, 0] : ℚ) = PP 44 (n + 1) := by
  have h42 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 42 n := ih 42
  have h79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 79 n := ih 79
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h42, h79, f_dead, pp_44, pp_42, pp_79]
  try (push_cast; ring)

lemma b_44 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = PP 44 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 2, 2] 3 ![1, 1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_468748
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 45 (n + 1) := by
  have h46 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 46 n := ih 46
  have h90 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 90 n := ih 90
  have h51 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 51 n := ih 51
  have h99 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  have h61 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 61 n := ih 61
  have h114 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 114 n := ih 114
  have h74 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 74 n := ih 74
  have h130 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 130 n := ih 130
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h46, h90, h51, h99, h61, h114, h74, h130, f_dead, pp_45, pp_46, pp_90, pp_51, pp_99, pp_61, pp_114, pp_74, pp_130]
  try (push_cast; ring)

lemma b_45 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 45 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 0] : ℚ) = 52 := by exact_mod_cast fv3_472392
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 46 (n + 1) := by
  have h47 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 47 n := ih 47
  have h91 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 91 n := ih 91
  have h52 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 52 n := ih 52
  have h100 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h47, h91, h52, h100, f_dead, pp_46, pp_47, pp_91, pp_52, pp_100]
  try (push_cast; ring)

lemma b_46 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 46 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_492084
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 47 (n + 1) := by
  have h48 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 48 n := ih 48
  have h92 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 92 n := ih 92
  have h53 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 53 n := ih 53
  have h101 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h48, h92, h53, h101, f_dead, pp_47, pp_48, pp_92, pp_53, pp_101]
  try (push_cast; ring)

lemma b_47 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 47 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_492090
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 0] : ℚ) = PP 48 (n + 1) := by
  have h48 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 48 n := ih 48
  have h92 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 92 n := ih 92
  have h53 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 53 n := ih 53
  have h101 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h48, h92, h53, h101, f_dead, pp_48, pp_48, pp_92, pp_53, pp_101]
  try (push_cast; ring)

lemma b_48 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = PP 48 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_492092
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 49 (n + 1) := by
  have h54 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 54 n := ih 54
  have h105 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 105 n := ih 105
  have h62 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 62 n := ih 62
  have h116 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 116 n := ih 116
  have h75 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 75 n := ih 75
  have h132 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 132 n := ih 132
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h54, h105, h62, h116, h75, h132, f_dead, pp_49, pp_54, pp_105, pp_62, pp_116, pp_75, pp_132]
  try (push_cast; ring)

lemma b_49 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 49 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_708588
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 50 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h55, h106, h63, h117, f_dead, pp_50, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_50 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 50 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_715152
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 51 (n + 1) := by
  have h54 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 54 n := ih 54
  have h105 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 105 n := ih 105
  have h62 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 62 n := ih 62
  have h116 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 116 n := ih 116
  have h75 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 75 n := ih 75
  have h132 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 132 n := ih 132
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h54, h105, h62, h116, h75, h132, f_dead, pp_51, pp_54, pp_105, pp_62, pp_116, pp_75, pp_132]
  try (push_cast; ring)

lemma b_51 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 51 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_728280
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 52 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h55, h106, h63, h117, f_dead, pp_52, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_52 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 52 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_728286
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 53 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h55, h106, h63, h117, f_dead, pp_53, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_53 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 53 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_728288
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 54 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h55, h106, h63, h117, f_dead, pp_54, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_54 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 54 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_734844
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 55 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h55, h106, h63, h117, f_dead, pp_55, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 55 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_734846
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3 + 1) ![0, 0, 1, 1, 0] : ℚ) = PP 56 (n + 1) := by
  have h55 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  have h63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 117 n := ih 117
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h55, h106, h63, h117, f_dead, pp_56, pp_55, pp_106, pp_63, pp_117]
  try (push_cast; ring)

lemma b_56 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 1, 0] : ℚ) = PP 56 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 0, 1, 1, 0] : ℚ) = 28 := by exact_mod_cast fv3_754520
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 57 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h64, h120, h76, h134, f_dead, pp_57, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_57 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 57 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_826686
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 58 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_58, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_58 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 58 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_828874
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 59 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_59, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_59 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 59 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_833250
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 60 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_60, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_60 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 60 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_835438
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 61 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_61, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_61 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 61 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_846378
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 62 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_62, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_62 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 62 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_852942
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 63 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_63, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_63 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 63 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_852944
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 64 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_64, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 64 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_855130
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 65 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_65, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_65 : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 65 0 := by
  have h : (f ![2, 1, 0, 0, 0, 0, 0, 0, 1, 2] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_872618
  rw [h, pp_65]; try norm_num

set_option maxRecDepth 100000 in
lemma st_66 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3 + 1) ![0, 1, 1, 1, 0] : ℚ) = PP 66 (n + 1) := by
  have h64 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 120 n := ih 120
  have h76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 76 n := ih 76
  have h134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 134 n := ih 134
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h64, h120, h76, h134, f_dead, pp_66, pp_64, pp_120, pp_76, pp_134]
  try (push_cast; ring)

lemma b_66 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 1, 0] : ℚ) = PP 66 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![0, 1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_874804
  rw [h, pp_66]; try norm_num

set_option maxRecDepth 100000 in
lemma st_67 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 67 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h77, h136, f_dead, pp_67, pp_77, pp_136]
  try (push_cast; ring)

lemma b_67 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 67 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_885735
  rw [h, pp_67]; try norm_num

set_option maxRecDepth 100000 in
lemma st_68 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 68 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_68, pp_77, pp_136]
  try (push_cast; ring)

lemma b_68 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 68 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_886464
  rw [h, pp_68]; try norm_num

set_option maxRecDepth 100000 in
lemma st_69 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 69 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_69, pp_77, pp_136]
  try (push_cast; ring)

lemma b_69 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 69 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_887923
  rw [h, pp_69]; try norm_num

set_option maxRecDepth 100000 in
lemma st_70 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 70 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_70, pp_77, pp_136]
  try (push_cast; ring)

lemma b_70 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 70 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_888652
  rw [h, pp_70]; try norm_num

set_option maxRecDepth 100000 in
lemma st_71 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 71 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_71, pp_77, pp_136]
  try (push_cast; ring)

lemma b_71 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 71 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_892299
  rw [h, pp_71]; try norm_num

set_option maxRecDepth 100000 in
lemma st_72 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 72 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_72, pp_77, pp_136]
  try (push_cast; ring)

lemma b_72 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 72 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_894487
  rw [h, pp_72]; try norm_num

set_option maxRecDepth 100000 in
lemma st_73 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 73 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_73, pp_77, pp_136]
  try (push_cast; ring)

lemma b_73 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 73 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_895216
  rw [h, pp_73]; try norm_num

set_option maxRecDepth 100000 in
lemma st_74 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 74 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_74, pp_77, pp_136]
  try (push_cast; ring)

lemma b_74 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 74 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_905427
  rw [h, pp_74]; try norm_num

set_option maxRecDepth 100000 in
lemma st_75 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 75 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_75, pp_77, pp_136]
  try (push_cast; ring)

lemma b_75 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 75 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_911991
  rw [h, pp_75]; try norm_num

set_option maxRecDepth 100000 in
lemma st_76 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 76 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_76, pp_77, pp_136]
  try (push_cast; ring)

lemma b_76 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 76 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_914179
  rw [h, pp_76]; try norm_num

set_option maxRecDepth 100000 in
lemma st_77 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 77 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_77, pp_77, pp_136]
  try (push_cast; ring)

lemma b_77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 77 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_914908
  rw [h, pp_77]; try norm_num

set_option maxRecDepth 100000 in
lemma st_78 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 78 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_78, pp_77, pp_136]
  try (push_cast; ring)

lemma b_78 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 78 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_933853
  rw [h, pp_78]; try norm_num

set_option maxRecDepth 100000 in
lemma st_79 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 1, 0] : ℚ) = PP 79 (n + 1) := by
  have h77 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 77 n := ih 77
  have h136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 136 n := ih 136
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h77, h136, f_dead, pp_79, pp_77, pp_136]
  try (push_cast; ring)

lemma b_79 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℚ) = PP 79 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 2] 3 ![1, 1, 1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv3_934582
  rw [h, pp_79]; try norm_num

set_option maxRecDepth 100000 in
lemma st_80 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 80 (n + 1) := by
  have h81 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 81 n := ih 81
  have h86 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 86 n := ih 86
  have h97 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 97 n := ih 97
  have h110 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 110 n := ih 110
  have h123 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 123 n := ih 123
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h81, h86, h97, h110, h123, f_dead, pp_80, pp_81, pp_86, pp_97, pp_110, pp_123]
  try (push_cast; ring)

lemma b_80 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 80 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 21 := by exact_mod_cast fv3_944784
  rw [h, pp_80]; try norm_num

set_option maxRecDepth 100000 in
lemma st_81 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 81 (n + 1) := by
  have h82 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 82 n := ih 82
  have h87 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 87 n := ih 87
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h82, h87, f_dead, pp_81, pp_82, pp_87]
  try (push_cast; ring)

lemma b_81 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 81 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_944811
  rw [h, pp_81]; try norm_num

set_option maxRecDepth 100000 in
lemma st_82 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 82 (n + 1) := by
  have h83 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 83 n := ih 83
  have h88 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 88 n := ih 88
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h83, h88, f_dead, pp_82, pp_83, pp_88]
  try (push_cast; ring)

lemma b_82 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 82 0 := by
  have h : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_944829
  rw [h, pp_82]; try norm_num

set_option maxRecDepth 100000 in
lemma st_83 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 83 (n + 1) := by
  have h84 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 84 n := ih 84
  have h89 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h84, h89, f_dead, pp_83, pp_84, pp_89]
  try (push_cast; ring)

lemma b_83 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 83 0 := by
  have h : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_944835
  rw [h, pp_83]; try norm_num

set_option maxRecDepth 100000 in
lemma st_84 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0, 1] : ℚ) = PP 84 (n + 1) := by
  have h84 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 84 n := ih 84
  have h89 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 89 n := ih 89
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h84, h89, f_dead, pp_84, pp_84, pp_89]
  try (push_cast; ring)

lemma b_84 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = PP 84 0 := by
  have h : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv3_944837
  rw [h, pp_84]; try norm_num

set_option maxRecDepth 100000 in
lemma st_85 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 85 (n + 1) := by
  have h93 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 93 n := ih 93
  have h102 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 102 n := ih 102
  have h115 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 115 n := ih 115
  have h131 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 131 n := ih 131
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h93, h102, h115, h131, f_dead, pp_85, pp_93, pp_102, pp_115, pp_131]
  try (push_cast; ring)

lemma b_85 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 85 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 13 := by exact_mod_cast fv3_1417176
  rw [h, pp_85]; try norm_num

set_option maxRecDepth 100000 in
lemma st_86 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 86 (n + 1) := by
  have h93 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 93 n := ih 93
  have h102 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 102 n := ih 102
  have h115 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 115 n := ih 115
  have h131 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 131 n := ih 131
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h93, h102, h115, h131, f_dead, pp_86, pp_93, pp_102, pp_115, pp_131]
  try (push_cast; ring)

lemma b_86 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 86 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 13 := by exact_mod_cast fv3_1417203
  rw [h, pp_86]; try norm_num

set_option maxRecDepth 100000 in
lemma st_87 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 87 (n + 1) := by
  have h94 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 94 n := ih 94
  have h103 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h94, h103, f_dead, pp_87, pp_94, pp_103]
  try (push_cast; ring)

lemma b_87 : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 87 0 := by
  have h : (f ![0, 0, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1417221
  rw [h, pp_87]; try norm_num

set_option maxRecDepth 100000 in
lemma st_88 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 88 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h95, h104, f_dead, pp_88, pp_95, pp_104]
  try (push_cast; ring)

lemma b_88 : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 88 0 := by
  have h : (f ![0, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1417227
  rw [h, pp_88]; try norm_num

set_option maxRecDepth 100000 in
lemma st_89 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 89 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h95, h104, f_dead, pp_89, pp_95, pp_104]
  try (push_cast; ring)

lemma b_89 : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 89 0 := by
  have h : (f ![2, 2, 2, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1417229
  rw [h, pp_89]; try norm_num

set_option maxRecDepth 100000 in
lemma st_90 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 90 (n + 1) := by
  have h94 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 94 n := ih 94
  have h103 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h94, h103, f_dead, pp_90, pp_94, pp_103]
  try (push_cast; ring)

lemma b_90 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 90 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436868
  rw [h, pp_90]; try norm_num

set_option maxRecDepth 100000 in
lemma st_91 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 91 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h95, h104, f_dead, pp_91, pp_95, pp_104]
  try (push_cast; ring)

lemma b_91 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 91 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436874
  rw [h, pp_91]; try norm_num

set_option maxRecDepth 100000 in
lemma st_92 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 92 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h95, h104, f_dead, pp_92, pp_95, pp_104]
  try (push_cast; ring)

lemma b_92 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 92 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436876
  rw [h, pp_92]; try norm_num

set_option maxRecDepth 100000 in
lemma st_93 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 93 (n + 1) := by
  have h94 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 94 n := ih 94
  have h103 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h94, h103, f_dead, pp_93, pp_94, pp_103]
  try (push_cast; ring)

lemma b_93 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 93 0 := by
  have h : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436895
  rw [h, pp_93]; try norm_num

set_option maxRecDepth 100000 in
lemma st_94 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 94 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h95, h104, f_dead, pp_94, pp_95, pp_104]
  try (push_cast; ring)

lemma b_94 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 94 0 := by
  have h : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436901
  rw [h, pp_94]; try norm_num

set_option maxRecDepth 100000 in
lemma st_95 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 0, 1, 1] : ℚ) = PP 95 (n + 1) := by
  have h95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 95 n := ih 95
  have h104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, dl20, h95, h104, f_dead, pp_95, pp_95, pp_104]
  try (push_cast; ring)

lemma b_95 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = PP 95 0 := by
  have h : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 0, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1436903
  rw [h, pp_95]; try norm_num

set_option maxRecDepth 100000 in
lemma st_96 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 96 (n + 1) := by
  have h107 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  have h118 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 118 n := ih 118
  have h133 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 133 n := ih 133
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h107, h118, h133, f_dead, pp_96, pp_107, pp_118, pp_133]
  try (push_cast; ring)

lemma b_96 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 96 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1653372
  rw [h, pp_96]; try norm_num

set_option maxRecDepth 100000 in
lemma st_97 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 97 (n + 1) := by
  have h107 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  have h118 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 118 n := ih 118
  have h133 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 133 n := ih 133
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h107, h118, h133, f_dead, pp_97, pp_107, pp_118, pp_133]
  try (push_cast; ring)

lemma b_97 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 97 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1653399
  rw [h, pp_97]; try norm_num

set_option maxRecDepth 100000 in
lemma st_98 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 98 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h108, h119, f_dead, pp_98, pp_108, pp_119]
  try (push_cast; ring)

lemma b_98 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 98 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1659936
  rw [h, pp_98]; try norm_num

set_option maxRecDepth 100000 in
lemma st_99 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 99 (n + 1) := by
  have h107 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  have h118 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 118 n := ih 118
  have h133 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 133 n := ih 133
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h107, h118, h133, f_dead, pp_99, pp_107, pp_118, pp_133]
  try (push_cast; ring)

lemma b_99 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 99 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1673064
  rw [h, pp_99]; try norm_num

set_option maxRecDepth 100000 in
lemma st_100 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 100 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h108, h119, f_dead, pp_100, pp_108, pp_119]
  try (push_cast; ring)

lemma b_100 : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 100 0 := by
  have h : (f ![0, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1673070
  rw [h, pp_100]; try norm_num

set_option maxRecDepth 100000 in
lemma st_101 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 101 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h108, h119, f_dead, pp_101, pp_108, pp_119]
  try (push_cast; ring)

lemma b_101 : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 101 0 := by
  have h : (f ![2, 2, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1673072
  rw [h, pp_101]; try norm_num

set_option maxRecDepth 100000 in
lemma st_102 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 102 (n + 1) := by
  have h107 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  have h118 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 118 n := ih 118
  have h133 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 133 n := ih 133
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h107, h118, h133, f_dead, pp_102, pp_107, pp_118, pp_133]
  try (push_cast; ring)

lemma b_102 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 102 0 := by
  have h : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1673091
  rw [h, pp_102]; try norm_num

set_option maxRecDepth 100000 in
lemma st_103 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 103 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h108, h119, f_dead, pp_103, pp_108, pp_119]
  try (push_cast; ring)

lemma b_103 : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 103 0 := by
  have h : (f ![0, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1673097
  rw [h, pp_103]; try norm_num

set_option maxRecDepth 100000 in
lemma st_104 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 104 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h108, h119, f_dead, pp_104, pp_108, pp_119]
  try (push_cast; ring)

lemma b_104 : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 104 0 := by
  have h : (f ![2, 2, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1673099
  rw [h, pp_104]; try norm_num

set_option maxRecDepth 100000 in
lemma st_105 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 105 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h108, h119, f_dead, pp_105, pp_108, pp_119]
  try (push_cast; ring)

lemma b_105 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 105 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1679628
  rw [h, pp_105]; try norm_num

set_option maxRecDepth 100000 in
lemma st_106 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 106 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h108, h119, f_dead, pp_106, pp_108, pp_119]
  try (push_cast; ring)

lemma b_106 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 106 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1679630
  rw [h, pp_106]; try norm_num

set_option maxRecDepth 100000 in
lemma st_107 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 107 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h108, h119, f_dead, pp_107, pp_108, pp_119]
  try (push_cast; ring)

lemma b_107 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 107 0 := by
  have h : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1679655
  rw [h, pp_107]; try norm_num

set_option maxRecDepth 100000 in
lemma st_108 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 0, 1, 1, 1] : ℚ) = PP 108 (n + 1) := by
  have h108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  have h119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 119 n := ih 119
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h108, h119, f_dead, pp_108, pp_108, pp_119]
  try (push_cast; ring)

lemma b_108 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = PP 108 0 := by
  have h : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 0, 1, 1, 1] : ℚ) = 7 := by exact_mod_cast fv3_1679657
  rw [h, pp_108]; try norm_num

set_option maxRecDepth 100000 in
lemma st_109 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 109 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h121, h135, f_dead, pp_109, pp_121, pp_135]
  try (push_cast; ring)

lemma b_109 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 109 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1771470
  rw [h, pp_109]; try norm_num

set_option maxRecDepth 100000 in
lemma st_110 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 110 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_110, pp_121, pp_135]
  try (push_cast; ring)

lemma b_110 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 110 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1771497
  rw [h, pp_110]; try norm_num

set_option maxRecDepth 100000 in
lemma st_111 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 111 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_111, pp_121, pp_135]
  try (push_cast; ring)

lemma b_111 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 111 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1773658
  rw [h, pp_111]; try norm_num

set_option maxRecDepth 100000 in
lemma st_112 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 112 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_112, pp_121, pp_135]
  try (push_cast; ring)

lemma b_112 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 112 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1778034
  rw [h, pp_112]; try norm_num

set_option maxRecDepth 100000 in
lemma st_113 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 113 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_113, pp_121, pp_135]
  try (push_cast; ring)

lemma b_113 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 113 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1780222
  rw [h, pp_113]; try norm_num

set_option maxRecDepth 100000 in
lemma st_114 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 114 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_114, pp_121, pp_135]
  try (push_cast; ring)

lemma b_114 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 114 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1791162
  rw [h, pp_114]; try norm_num

set_option maxRecDepth 100000 in
lemma st_115 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 115 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_115, pp_121, pp_135]
  try (push_cast; ring)

lemma b_115 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 115 0 := by
  have h : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1791189
  rw [h, pp_115]; try norm_num

set_option maxRecDepth 100000 in
lemma st_116 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 116 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_116, pp_121, pp_135]
  try (push_cast; ring)

lemma b_116 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 116 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1797726
  rw [h, pp_116]; try norm_num

set_option maxRecDepth 100000 in
lemma st_117 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 117 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_117, pp_121, pp_135]
  try (push_cast; ring)

lemma b_117 : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 117 0 := by
  have h : (f ![2, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1797728
  rw [h, pp_117]; try norm_num

set_option maxRecDepth 100000 in
lemma st_118 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 118 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_118, pp_121, pp_135]
  try (push_cast; ring)

lemma b_118 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 118 0 := by
  have h : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1797753
  rw [h, pp_118]; try norm_num

set_option maxRecDepth 100000 in
lemma st_119 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 119 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_119, pp_121, pp_135]
  try (push_cast; ring)

lemma b_119 : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 119 0 := by
  have h : (f ![2, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1797755
  rw [h, pp_119]; try norm_num

set_option maxRecDepth 100000 in
lemma st_120 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 120 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_120, pp_121, pp_135]
  try (push_cast; ring)

lemma b_120 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 120 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1799914
  rw [h, pp_120]; try norm_num

set_option maxRecDepth 100000 in
lemma st_121 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![0, 1, 1, 1, 1] : ℚ) = PP 121 (n + 1) := by
  have h121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 121 n := ih 121
  have h135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 135 n := ih 135
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h121, h135, f_dead, pp_121, pp_121, pp_135]
  try (push_cast; ring)

lemma b_121 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = PP 121 0 := by
  have h : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![0, 1, 1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv3_1799941
  rw [h, pp_121]; try norm_num

set_option maxRecDepth 100000 in
lemma st_122 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 122 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h137, f_dead, pp_122, pp_137]
  try (push_cast; ring)

lemma b_122 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 122 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1830519
  rw [h, pp_122]; try norm_num

set_option maxRecDepth 100000 in
lemma st_123 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 123 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_123, pp_137]
  try (push_cast; ring)

lemma b_123 : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 123 0 := by
  have h : (f ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1830546
  rw [h, pp_123]; try norm_num

set_option maxRecDepth 100000 in
lemma st_124 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 124 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_124, pp_137]
  try (push_cast; ring)

lemma b_124 : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 124 0 := by
  have h : (f ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1831248
  rw [h, pp_124]; try norm_num

set_option maxRecDepth 100000 in
lemma st_125 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 125 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_125, pp_137]
  try (push_cast; ring)

lemma b_125 : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 125 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1832707
  rw [h, pp_125]; try norm_num

set_option maxRecDepth 100000 in
lemma st_126 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 126 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_126, pp_137]
  try (push_cast; ring)

lemma b_126 : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 126 0 := by
  have h : (f ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1833436
  rw [h, pp_126]; try norm_num

set_option maxRecDepth 100000 in
lemma st_127 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 127 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_127, pp_137]
  try (push_cast; ring)

lemma b_127 : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 127 0 := by
  have h : (f ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1837083
  rw [h, pp_127]; try norm_num

set_option maxRecDepth 100000 in
lemma st_128 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 128 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_128, pp_137]
  try (push_cast; ring)

lemma b_128 : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 128 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 0, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1839271
  rw [h, pp_128]; try norm_num

set_option maxRecDepth 100000 in
lemma st_129 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 129 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_129, pp_137]
  try (push_cast; ring)

lemma b_129 : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 129 0 := by
  have h : (f ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1840000
  rw [h, pp_129]; try norm_num

set_option maxRecDepth 100000 in
lemma st_130 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 130 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_130, pp_137]
  try (push_cast; ring)

lemma b_130 : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 130 0 := by
  have h : (f ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1850211
  rw [h, pp_130]; try norm_num

set_option maxRecDepth 100000 in
lemma st_131 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 131 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_131, pp_137]
  try (push_cast; ring)

lemma b_131 : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 131 0 := by
  have h : (f ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1850238
  rw [h, pp_131]; try norm_num

set_option maxRecDepth 100000 in
lemma st_132 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 132 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_132, pp_137]
  try (push_cast; ring)

lemma b_132 : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 132 0 := by
  have h : (f ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1856775
  rw [h, pp_132]; try norm_num

set_option maxRecDepth 100000 in
lemma st_133 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 133 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_133, pp_137]
  try (push_cast; ring)

lemma b_133 : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 133 0 := by
  have h : (f ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1856802
  rw [h, pp_133]; try norm_num

set_option maxRecDepth 100000 in
lemma st_134 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 134 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_134, pp_137]
  try (push_cast; ring)

lemma b_134 : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 134 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1858963
  rw [h, pp_134]; try norm_num

set_option maxRecDepth 100000 in
lemma st_135 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 135 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_135, pp_137]
  try (push_cast; ring)

lemma b_135 : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 135 0 := by
  have h : (f ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1858990
  rw [h, pp_135]; try norm_num

set_option maxRecDepth 100000 in
lemma st_136 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 136 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_136, pp_137]
  try (push_cast; ring)

lemma b_136 : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 136 0 := by
  have h : (f ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1859692
  rw [h, pp_136]; try norm_num

set_option maxRecDepth 100000 in
lemma st_137 (n : ℕ) (ih : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1, 1] : ℚ) = PP 137 (n + 1) := by
  have h137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] (n + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 137 n := ih 137
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h137, f_dead, pp_137, pp_137]
  try (push_cast; ring)

lemma b_137 : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = PP 137 0 := by
  have h : (f ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1] 3 ![1, 1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv3_1859719
  rw [h, pp_137]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 138, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65, b_66, b_67, b_68, b_69, b_70, b_71, b_72, b_73, b_74, b_75, b_76, b_77, b_78, b_79, b_80, b_81, b_82, b_83, b_84, b_85, b_86, b_87, b_88, b_89, b_90, b_91, b_92, b_93, b_94, b_95, b_96, b_97, b_98, b_99, b_100, b_101, b_102, b_103, b_104, b_105, b_106, b_107, b_108, b_109, b_110, b_111, b_112, b_113, b_114, b_115, b_116, b_117, b_118, b_119, b_120, b_121, b_122, b_123, b_124, b_125, b_126, b_127, b_128, b_129, b_130, b_131, b_132, b_133, b_134, b_135, b_136, b_137]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih, st_66 n ih, st_67 n ih, st_68 n ih, st_69 n ih, st_70 n ih, st_71 n ih, st_72 n ih, st_73 n ih, st_74 n ih, st_75 n ih, st_76 n ih, st_77 n ih, st_78 n ih, st_79 n ih, st_80 n ih, st_81 n ih, st_82 n ih, st_83 n ih, st_84 n ih, st_85 n ih, st_86 n ih, st_87 n ih, st_88 n ih, st_89 n ih, st_90 n ih, st_91 n ih, st_92 n ih, st_93 n ih, st_94 n ih, st_95 n ih, st_96 n ih, st_97 n ih, st_98 n ih, st_99 n ih, st_100 n ih, st_101 n ih, st_102 n ih, st_103 n ih, st_104 n ih, st_105 n ih, st_106 n ih, st_107 n ih, st_108 n ih, st_109 n ih, st_110 n ih, st_111 n ih, st_112 n ih, st_113 n ih, st_114 n ih, st_115 n ih, st_116 n ih, st_117 n ih, st_118 n ih, st_119 n ih, st_120 n ih, st_121 n ih, st_122 n ih, st_123 n ih, st_124 n ih, st_125 n ih, st_126 n ih, st_127 n ih, st_128 n ih, st_129 n ih, st_130 n ih, st_131 n ih, st_132 n ih, st_133 n ih, st_134 n ih, st_135 n ih, st_136 n ih, st_137 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 4) : ℚ) = ((2 : ℚ) / 15) * (m : ℚ) ^ 5 + ((17 : ℚ) / 6) * (m : ℚ) ^ 4 + ((163 : ℚ) / 6) * (m : ℚ) ^ 3 + ((446 : ℚ) / 3) * (m : ℚ) ^ 2 + ((2326 : ℚ) / 5) * (m : ℚ) ^ 1 + (596 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g80 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 0, 1] : ℚ) = PP 80 m := f_closed m 80
  have g45 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 1, 0] : ℚ) = PP 45 m := f_closed m 45
  have g85 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 0, 1, 1] : ℚ) = PP 85 m := f_closed m 85
  have g21 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 0, 0] : ℚ) = PP 21 m := f_closed m 21
  have g49 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 1, 0] : ℚ) = PP 49 m := f_closed m 49
  have g96 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 0, 1, 1, 1] : ℚ) = PP 96 m := f_closed m 96
  have g6 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 1, 0, 0, 0] : ℚ) = PP 6 m := f_closed m 6
  have g24 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 0, 0] : ℚ) = PP 24 m := f_closed m 24
  have g57 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 1, 0] : ℚ) = PP 57 m := f_closed m 57
  have g109 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![0, 1, 1, 1, 1] : ℚ) = PP 109 m := f_closed m 109
  have g1 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 0, 0, 0, 0] : ℚ) = PP 1 m := f_closed m 1
  have g10 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 1, 0, 0, 0] : ℚ) = PP 10 m := f_closed m 10
  have g32 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 0, 0] : ℚ) = PP 32 m := f_closed m 32
  have g67 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 1, 0] : ℚ) = PP 67 m := f_closed m 67
  have g122 : (f ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 3) ![1, 1, 1, 1, 1] : ℚ) = PP 122 m := f_closed m 122
  rw [show m + 4 = (m + 3) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 10 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g80, g45, g85, g21, g49, g96, g6, g24, g57, g109, g1, g10, g32, g67, g122, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_80, pp_45, pp_85, pp_21, pp_49, pp_96, pp_6, pp_24, pp_57, pp_109, pp_1, pp_10, pp_32, pp_67, pp_122]
  ring

lemma aS1 : (a 1 : ℚ) = 16 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 10 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 86 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 10 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 10 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_944784, fv1_472392, fv1_1417176, fv1_236196, fv1_708588, fv1_1653372, fv1_118098, fv1_354294, fv1_826686, fv1_1771470, fv1_59049, fv1_177147, fv1_413343, fv1_885735, fv1_1830519]
  norm_num

lemma aS3 : (a 3 : ℚ) = 255 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 10 => (0 : Fin 3)) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 10 → Fin 3) (r : R), (f c 2 r : ℚ) = ((f c 2 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv2_0, fv2_944784, fv2_472392, fv2_1417176, fv2_236196, fv2_708588, fv2_1653372, fv2_118098, fv2_354294, fv2_826686, fv2_1771470, fv2_59049, fv2_177147, fv2_413343, fv2_885735, fv2_1830519]
  norm_num

lemma av (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((2 : ℚ) / 15) * (n : ℚ) ^ 5 + ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 6) * (n : ℚ) ^ 3 + ((28 : ℚ) / 3) * (n : ℚ) ^ 2 + ((126 : ℚ) / 5) * (n : ℚ) ^ 1 + (-36 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [aS3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
      16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7) ∧
    (∀ n > 8, (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - 1 * a (n - 6)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-6 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (15 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-20 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (15 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-6 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) =
        C (16 : ℚ) * X ^ 0 + C (-10 : ℚ) * X ^ 1 + C (-21 : ℚ) * X ^ 2 + C (36 : ℚ) * X ^ 3 + C (9 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (2 : ℚ) * X ^ 6 + C (2 : ℚ) * X ^ 7 by
      simp only [map_neg, map_ofNat, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 16 := aS1
    have e2 : (a 2 : ℚ) = 86 := aS2
    have e3 : (a 3 : ℚ) = 255 := aS3
    have e4 : (a 4 : ℚ) = 596 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 1240 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 2388 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 4325 := by rw [av 7 (by norm_num)]; norm_num
    have e8 : (a 8 : ℚ) = 7436 := by rw [av 8 (by norm_num)]; norm_num
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

end OMA.P_oeis_a223835

theorem OMA.solution : type_of% @OMA.S_oeis_a223835.main := OMA.P_oeis_a223835.full
