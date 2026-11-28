import OMAStatements.S_oeis_a223772
import Mathlib

/-!
# oeis-a223772: counting the n X 3 arrays with unimodal rows and columns and nondecreasing antidiagonals

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 3 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 2 it is an explicit polynomial, checked by induction over the
46 states (c, r) whose top row is allowed, from exact values at n = 1..2. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223772, https://oeis.org/A223772.
-/
namespace OMA.P_oeis_a223772

open OMA.S_oeis_a223772

def adj (r s : Fin 3 → Fin 2) : Prop := ∀ j : Fin 2, r j.succ ≤ s j.castSucc

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

/-- The condition on the first row from column states `c`. -/
def okT (c : Fin 3 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ ∀ j, okb (c j) (r j) = true

instance (c : Fin 3 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 3 → Fin 3) (l : List R) : Prop :=
  ((∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ ∀ j, Acc (c j) (l.map (· j)) = true) ∧ l.IsChain adj

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 3) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  simp only [rowUni, colUni, and_assoc]

lemma Q_single (c : Fin 3 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc]

lemma Q_cons (c : Fin 3 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q (fun j => dl (c j) (r j)) (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Acc, Bool.and_eq_true, forall_and,
    List.isChain_cons_cons]
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

noncomputable def f (c : Fin 3 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 3 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 3 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2)] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hv : (fun j => dl (c j) (r j)) = ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2)] := by ext j; fin_cases j <;> rfl
  simp only [Q_cons, ← hv]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 3 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 : Fin 3) (r0 r1 r2 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2] (n + 1) ![r0, r1, r2] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2] ![r0, r1, r2] ∧ adj ![r0, r1, r2] s then
        (f ![dl c0 r0, dl c1 r1, dl c2 r2] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 : Fin 3) (r0 r1 r2 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2] (n + 1) ![r0, r1, r2] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2] ![r0, r1, r2] ∧ adj ![r0, r1, r2] s then
        (f ![dl c0 r0, dl c1 r1, dl c2 r2] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0] 1 ![0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_108 : (f ![0, 0, 0] 1 ![0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_54 : (f ![0, 0, 0] 1 ![0, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_162 : (f ![0, 0, 0] 1 ![0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_27 : (f ![0, 0, 0] 1 ![1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_81 : (f ![0, 0, 0] 1 ![1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_189 : (f ![0, 0, 0] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_63 : (f ![0, 0, 1] 1 ![0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_171 : (f ![0, 0, 1] 1 ![0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_90 : (f ![0, 0, 1] 1 ![1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_198 : (f ![0, 0, 1] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_30 : (f ![0, 1, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_84 : (f ![0, 1, 0] 1 ![1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_192 : (f ![0, 1, 0] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_93 : (f ![0, 1, 1] 1 ![1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_201 : (f ![0, 1, 1] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_48 : (f ![0, 1, 2] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_102 : (f ![0, 1, 2] 1 ![1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1 : (f ![1, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_109 : (f ![1, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_55 : (f ![1, 0, 0] 1 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_163 : (f ![1, 0, 0] 1 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_28 : (f ![1, 0, 0] 1 ![1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_82 : (f ![1, 0, 0] 1 ![1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_190 : (f ![1, 0, 0] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_31 : (f ![1, 1, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_85 : (f ![1, 1, 0] 1 ![1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_193 : (f ![1, 1, 0] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_94 : (f ![1, 1, 1] 1 ![1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_202 : (f ![1, 1, 1] 1 ![1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_49 : (f ![1, 1, 2] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_103 : (f ![1, 1, 2] 1 ![1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7 : (f ![1, 2, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_115 : (f ![1, 2, 0] 1 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_34 : (f ![1, 2, 0] 1 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_25 : (f ![1, 2, 2] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_52 : (f ![1, 2, 2] 1 ![1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2 : (f ![2, 0, 0] 1 ![0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_110 : (f ![2, 0, 0] 1 ![0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_56 : (f ![2, 0, 0] 1 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_164 : (f ![2, 0, 0] 1 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_65 : (f ![2, 0, 1] 1 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_173 : (f ![2, 0, 1] 1 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8 : (f ![2, 2, 0] 1 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_116 : (f ![2, 2, 0] 1 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_26 : (f ![2, 2, 2] 1 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0] 2 ![0, 0, 0] : ℤ) = 28 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_108, fv1_54, fv1_162, fv1_27, fv1_81, fv1_189, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_108 : (f ![0, 0, 0] 2 ![0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_63, fv1_171, fv1_90, fv1_198, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_54 : (f ![0, 0, 0] 2 ![0, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_30, fv1_84, fv1_192, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_162 : (f ![0, 0, 0] 2 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_93, fv1_201, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_27 : (f ![0, 0, 0] 2 ![1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1, fv1_109, fv1_55, fv1_163, fv1_28, fv1_82, fv1_190, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_81 : (f ![0, 0, 0] 2 ![1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_31, fv1_85, fv1_193, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_189 : (f ![0, 0, 0] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_63 : (f ![0, 0, 1] 2 ![0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_48, fv1_102, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_171 : (f ![0, 0, 1] 2 ![0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_93, fv1_201, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_90 : (f ![0, 0, 1] 2 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_49, fv1_103, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_198 : (f ![0, 0, 1] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_30 : (f ![0, 1, 0] 2 ![1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_7, fv1_115, fv1_34, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_84 : (f ![0, 1, 0] 2 ![1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_31, fv1_85, fv1_193, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_192 : (f ![0, 1, 0] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_93 : (f ![0, 1, 1] 2 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_49, fv1_103, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_201 : (f ![0, 1, 1] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_48 : (f ![0, 1, 2] 2 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_25, fv1_52, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_102 : (f ![0, 1, 2] 2 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_49, fv1_103, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1 : (f ![1, 0, 0] 2 ![0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_2, fv1_110, fv1_56, fv1_164, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_109 : (f ![1, 0, 0] 2 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_65, fv1_173, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_55 : (f ![1, 0, 0] 2 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_163 : (f ![1, 0, 0] 2 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_28 : (f ![1, 0, 0] 2 ![1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv1_1, fv1_109, fv1_55, fv1_163, fv1_28, fv1_82, fv1_190, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_82 : (f ![1, 0, 0] 2 ![1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_31, fv1_85, fv1_193, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_190 : (f ![1, 0, 0] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_31 : (f ![1, 1, 0] 2 ![1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, fv1_7, fv1_115, fv1_34, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_85 : (f ![1, 1, 0] 2 ![1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv1_31, fv1_85, fv1_193, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_193 : (f ![1, 1, 0] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_94 : (f ![1, 1, 1] 2 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, fv1_49, fv1_103, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_202 : (f ![1, 1, 1] 2 ![1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, fv1_94, fv1_202, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_49 : (f ![1, 1, 2] 2 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, fv1_25, fv1_52, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_103 : (f ![1, 1, 2] 2 ![1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv1_49, fv1_103, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7 : (f ![1, 2, 0] 2 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_8, fv1_116, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_115 : (f ![1, 2, 0] 2 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_34 : (f ![1, 2, 0] 2 ![1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv1_7, fv1_115, fv1_34, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_25 : (f ![1, 2, 2] 2 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl20, fv1_26, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_52 : (f ![1, 2, 2] 2 ![1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv1_25, fv1_52, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2 : (f ![2, 0, 0] 2 ![0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_2, fv1_110, fv1_56, fv1_164, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_110 : (f ![2, 0, 0] 2 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv1_65, fv1_173, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_56 : (f ![2, 0, 0] 2 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_164 : (f ![2, 0, 0] 2 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_65 : (f ![2, 0, 1] 2 ![0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_173 : (f ![2, 0, 1] 2 ![0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8 : (f ![2, 2, 0] 2 ![0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_8, fv1_116, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_116 : (f ![2, 2, 0] 2 ![0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_26 : (f ![2, 2, 2] 2 ![0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl20, fv1_26, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 46 → Fin 3 → Fin 3 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![1, 2, 0], ![2, 2, 0], ![1, 2, 2], ![2, 2, 2], ![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 2, 0], ![0, 1, 2], ![1, 1, 2], ![1, 2, 2], ![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![0, 0, 1], ![2, 0, 1], ![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 1], ![0, 1, 2], ![1, 1, 2], ![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![1, 2, 0], ![2, 2, 0], ![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![0, 0, 1], ![2, 0, 1], ![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 1]]

set_option maxRecDepth 100000 in
def rs : Fin 46 → R := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![0, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![0, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 46 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((7 : ℚ) / 240) * (n : ℚ) ^ 5 + ((59 : ℚ) / 144) * (n : ℚ) ^ 4 + ((137 : ℚ) / 48) * (n : ℚ) ^ 3 + ((634 : ℚ) / 45) * (n : ℚ) ^ 2 + ((1957 : ℚ) / 60) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((41 : ℚ) / 12) * (n : ℚ) ^ 2 + ((137 : ℚ) / 10) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((41 : ℚ) / 12) * (n : ℚ) ^ 2 + ((137 : ℚ) / 10) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((7 : ℚ) / 240) * (n : ℚ) ^ 5 + ((59 : ℚ) / 144) * (n : ℚ) ^ 4 + ((137 : ℚ) / 48) * (n : ℚ) ^ 3 + ((634 : ℚ) / 45) * (n : ℚ) ^ 2 + ((1957 : ℚ) / 60) * (n : ℚ) ^ 1 + (28 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((41 : ℚ) / 12) * (n : ℚ) ^ 2 + ((137 : ℚ) / 10) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((41 : ℚ) / 12) * (n : ℚ) ^ 2 + ((137 : ℚ) / 10) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = (2 : ℚ) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((1 : ℚ) / 4) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((27 : ℚ) / 4) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

lemma st_0 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h29 : (f ![0, 0, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 29 n := ih 29
  have h15 : (f ![0, 0, 0] (n + 2) ![0, 1, 0] : ℚ) = PP 15 n := ih 15
  have h34 : (f ![0, 0, 0] (n + 2) ![0, 1, 1] : ℚ) = PP 34 n := ih 34
  have h7 : (f ![0, 0, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 7 n := ih 7
  have h20 : (f ![0, 0, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 20 n := ih 20
  have h39 : (f ![0, 0, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h29, h15, h34, h7, h20, h39, f_dead, pp_0, pp_0, pp_29, pp_15, pp_34, pp_7, pp_20, pp_39]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0] 2 ![0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0] 2 ![0, 0, 0] : ℚ) = 28 := by exact_mod_cast fv2_0
  rw [h, pp_0]; try norm_num

lemma st_1 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h2 : (f ![2, 0, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h31 : (f ![2, 0, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 31 n := ih 31
  have h17 : (f ![2, 0, 0] (n + 2) ![0, 1, 0] : ℚ) = PP 17 n := ih 17
  have h36 : (f ![2, 0, 0] (n + 2) ![0, 1, 1] : ℚ) = PP 36 n := ih 36
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h2, h31, h17, h36, f_dead, pp_1, pp_2, pp_31, pp_17, pp_36]
  try (push_cast; ring)

lemma b_1 : (f ![1, 0, 0] 2 ![0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![1, 0, 0] 2 ![0, 0, 0] : ℚ) = 6 := by exact_mod_cast fv2_1
  rw [h, pp_1]; try norm_num

lemma st_2 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h2 : (f ![2, 0, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h31 : (f ![2, 0, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 31 n := ih 31
  have h17 : (f ![2, 0, 0] (n + 2) ![0, 1, 0] : ℚ) = PP 17 n := ih 17
  have h36 : (f ![2, 0, 0] (n + 2) ![0, 1, 1] : ℚ) = PP 36 n := ih 36
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h2, h31, h17, h36, f_dead, pp_2, pp_2, pp_31, pp_17, pp_36]
  try (push_cast; ring)

lemma b_2 : (f ![2, 0, 0] 2 ![0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![2, 0, 0] 2 ![0, 0, 0] : ℚ) = 6 := by exact_mod_cast fv2_2
  rw [h, pp_2]; try norm_num

lemma st_3 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h4 : (f ![2, 2, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h33 : (f ![2, 2, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h4, h33, f_dead, pp_3, pp_4, pp_33]
  try (push_cast; ring)

lemma b_3 : (f ![1, 2, 0] 2 ![0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![1, 2, 0] 2 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv2_7
  rw [h, pp_3]; try norm_num

lemma st_4 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h4 : (f ![2, 2, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h33 : (f ![2, 2, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 33 n := ih 33
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h4, h33, f_dead, pp_4, pp_4, pp_33]
  try (push_cast; ring)

lemma b_4 : (f ![2, 2, 0] 2 ![0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![2, 2, 0] 2 ![0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv2_8
  rw [h, pp_4]; try norm_num

lemma st_5 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h6 : (f ![2, 2, 2] (n + 2) ![0, 0, 0] : ℚ) = PP 6 n := ih 6
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl20, h6, f_dead, pp_5, pp_6]
  try (push_cast; ring)

lemma b_5 : (f ![1, 2, 2] 2 ![0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![1, 2, 2] 2 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv2_25
  rw [h, pp_5]; try norm_num

lemma st_6 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2] (n + 2 + 1) ![0, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h6 : (f ![2, 2, 2] (n + 2) ![0, 0, 0] : ℚ) = PP 6 n := ih 6
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl20, h6, f_dead, pp_6, pp_6]
  try (push_cast; ring)

lemma b_6 : (f ![2, 2, 2] 2 ![0, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![2, 2, 2] 2 ![0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv2_26
  rw [h, pp_6]; try norm_num

lemma st_7 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h1 : (f ![1, 0, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h30 : (f ![1, 0, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 30 n := ih 30
  have h16 : (f ![1, 0, 0] (n + 2) ![0, 1, 0] : ℚ) = PP 16 n := ih 16
  have h35 : (f ![1, 0, 0] (n + 2) ![0, 1, 1] : ℚ) = PP 35 n := ih 35
  have h8 : (f ![1, 0, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 8 n := ih 8
  have h21 : (f ![1, 0, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 21 n := ih 21
  have h40 : (f ![1, 0, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h1, h30, h16, h35, h8, h21, h40, f_dead, pp_7, pp_1, pp_30, pp_16, pp_35, pp_8, pp_21, pp_40]
  try (push_cast; ring)

lemma b_7 : (f ![0, 0, 0] 2 ![1, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![0, 0, 0] 2 ![1, 0, 0] : ℚ) = 18 := by exact_mod_cast fv2_27
  rw [h, pp_7]; try norm_num

lemma st_8 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h1 : (f ![1, 0, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h30 : (f ![1, 0, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 30 n := ih 30
  have h16 : (f ![1, 0, 0] (n + 2) ![0, 1, 0] : ℚ) = PP 16 n := ih 16
  have h35 : (f ![1, 0, 0] (n + 2) ![0, 1, 1] : ℚ) = PP 35 n := ih 35
  have h8 : (f ![1, 0, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 8 n := ih 8
  have h21 : (f ![1, 0, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 21 n := ih 21
  have h40 : (f ![1, 0, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h1, h30, h16, h35, h8, h21, h40, f_dead, pp_8, pp_1, pp_30, pp_16, pp_35, pp_8, pp_21, pp_40]
  try (push_cast; ring)

lemma b_8 : (f ![1, 0, 0] 2 ![1, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![1, 0, 0] 2 ![1, 0, 0] : ℚ) = 18 := by exact_mod_cast fv2_28
  rw [h, pp_8]; try norm_num

lemma st_9 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h3 : (f ![1, 2, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h32 : (f ![1, 2, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 32 n := ih 32
  have h11 : (f ![1, 2, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h3, h32, h11, f_dead, pp_9, pp_3, pp_32, pp_11]
  try (push_cast; ring)

lemma b_9 : (f ![0, 1, 0] 2 ![1, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 1, 0] 2 ![1, 0, 0] : ℚ) = 5 := by exact_mod_cast fv2_30
  rw [h, pp_9]; try norm_num

lemma st_10 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h3 : (f ![1, 2, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h32 : (f ![1, 2, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 32 n := ih 32
  have h11 : (f ![1, 2, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h3, h32, h11, f_dead, pp_10, pp_3, pp_32, pp_11]
  try (push_cast; ring)

lemma b_10 : (f ![1, 1, 0] 2 ![1, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 1, 0] 2 ![1, 0, 0] : ℚ) = 5 := by exact_mod_cast fv2_31
  rw [h, pp_10]; try norm_num

lemma st_11 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h3 : (f ![1, 2, 0] (n + 2) ![0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h32 : (f ![1, 2, 0] (n + 2) ![0, 0, 1] : ℚ) = PP 32 n := ih 32
  have h11 : (f ![1, 2, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 11 n := ih 11
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h3, h32, h11, f_dead, pp_11, pp_3, pp_32, pp_11]
  try (push_cast; ring)

lemma b_11 : (f ![1, 2, 0] 2 ![1, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![1, 2, 0] 2 ![1, 0, 0] : ℚ) = 5 := by exact_mod_cast fv2_34
  rw [h, pp_11]; try norm_num

lemma st_12 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h5 : (f ![1, 2, 2] (n + 2) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h14 : (f ![1, 2, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 14 n := ih 14
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h5, h14, f_dead, pp_12, pp_5, pp_14]
  try (push_cast; ring)

lemma b_12 : (f ![0, 1, 2] 2 ![1, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![0, 1, 2] 2 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv2_48
  rw [h, pp_12]; try norm_num

lemma st_13 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h5 : (f ![1, 2, 2] (n + 2) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h14 : (f ![1, 2, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 14 n := ih 14
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl11, dl20, h5, h14, f_dead, pp_13, pp_5, pp_14]
  try (push_cast; ring)

lemma b_13 : (f ![1, 1, 2] 2 ![1, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![1, 1, 2] 2 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv2_49
  rw [h, pp_13]; try norm_num

lemma st_14 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2] (n + 2 + 1) ![1, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h5 : (f ![1, 2, 2] (n + 2) ![0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h14 : (f ![1, 2, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 14 n := ih 14
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, dl20, h5, h14, f_dead, pp_14, pp_5, pp_14]
  try (push_cast; ring)

lemma b_14 : (f ![1, 2, 2] 2 ![1, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![1, 2, 2] 2 ![1, 0, 0] : ℚ) = 3 := by exact_mod_cast fv2_52
  rw [h, pp_14]; try norm_num

lemma st_15 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![0, 1, 0] : ℚ) = PP 15 (n + 1) := by
  have h9 : (f ![0, 1, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 9 n := ih 9
  have h22 : (f ![0, 1, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 22 n := ih 22
  have h41 : (f ![0, 1, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h9, h22, h41, f_dead, pp_15, pp_9, pp_22, pp_41]
  try (push_cast; ring)

lemma b_15 : (f ![0, 0, 0] 2 ![0, 1, 0] : ℚ) = PP 15 0 := by
  have h : (f ![0, 0, 0] 2 ![0, 1, 0] : ℚ) = 8 := by exact_mod_cast fv2_54
  rw [h, pp_15]; try norm_num

lemma st_16 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![0, 1, 0] : ℚ) = PP 16 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, f_dead, pp_16]
  try (push_cast; ring)

lemma b_16 : (f ![1, 0, 0] 2 ![0, 1, 0] : ℚ) = PP 16 0 := by
  have h : (f ![1, 0, 0] 2 ![0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv2_55
  rw [h, pp_16]; try norm_num

lemma st_17 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0] (n + 2 + 1) ![0, 1, 0] : ℚ) = PP 17 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, f_dead, pp_17]
  try (push_cast; ring)

lemma b_17 : (f ![2, 0, 0] 2 ![0, 1, 0] : ℚ) = PP 17 0 := by
  have h : (f ![2, 0, 0] 2 ![0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv2_56
  rw [h, pp_17]; try norm_num

lemma st_18 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1] (n + 2 + 1) ![0, 1, 0] : ℚ) = PP 18 (n + 1) := by
  have h12 : (f ![0, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 12 n := ih 12
  have h27 : (f ![0, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 27 n := ih 27
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h12, h27, f_dead, pp_18, pp_12, pp_27]
  try (push_cast; ring)

lemma b_18 : (f ![0, 0, 1] 2 ![0, 1, 0] : ℚ) = PP 18 0 := by
  have h : (f ![0, 0, 1] 2 ![0, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_63
  rw [h, pp_18]; try norm_num

lemma st_19 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1] (n + 2 + 1) ![0, 1, 0] : ℚ) = PP 19 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_19]
  try (push_cast; ring)

lemma b_19 : (f ![2, 0, 1] 2 ![0, 1, 0] : ℚ) = PP 19 0 := by
  have h : (f ![2, 0, 1] 2 ![0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv2_65
  rw [h, pp_19]; try norm_num

lemma st_20 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 20 (n + 1) := by
  have h10 : (f ![1, 1, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h23 : (f ![1, 1, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h42 : (f ![1, 1, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h10, h23, h42, f_dead, pp_20, pp_10, pp_23, pp_42]
  try (push_cast; ring)

lemma b_20 : (f ![0, 0, 0] 2 ![1, 1, 0] : ℚ) = PP 20 0 := by
  have h : (f ![0, 0, 0] 2 ![1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv2_81
  rw [h, pp_20]; try norm_num

lemma st_21 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 21 (n + 1) := by
  have h10 : (f ![1, 1, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h23 : (f ![1, 1, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h42 : (f ![1, 1, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h10, h23, h42, f_dead, pp_21, pp_10, pp_23, pp_42]
  try (push_cast; ring)

lemma b_21 : (f ![1, 0, 0] 2 ![1, 1, 0] : ℚ) = PP 21 0 := by
  have h : (f ![1, 0, 0] 2 ![1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv2_82
  rw [h, pp_21]; try norm_num

lemma st_22 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 22 (n + 1) := by
  have h10 : (f ![1, 1, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h23 : (f ![1, 1, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h42 : (f ![1, 1, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h10, h23, h42, f_dead, pp_22, pp_10, pp_23, pp_42]
  try (push_cast; ring)

lemma b_22 : (f ![0, 1, 0] 2 ![1, 1, 0] : ℚ) = PP 22 0 := by
  have h : (f ![0, 1, 0] 2 ![1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv2_84
  rw [h, pp_22]; try norm_num

lemma st_23 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 23 (n + 1) := by
  have h10 : (f ![1, 1, 0] (n + 2) ![1, 0, 0] : ℚ) = PP 10 n := ih 10
  have h23 : (f ![1, 1, 0] (n + 2) ![1, 1, 0] : ℚ) = PP 23 n := ih 23
  have h42 : (f ![1, 1, 0] (n + 2) ![1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h10, h23, h42, f_dead, pp_23, pp_10, pp_23, pp_42]
  try (push_cast; ring)

lemma b_23 : (f ![1, 1, 0] 2 ![1, 1, 0] : ℚ) = PP 23 0 := by
  have h : (f ![1, 1, 0] 2 ![1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv2_85
  rw [h, pp_23]; try norm_num

lemma st_24 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 24 (n + 1) := by
  have h13 : (f ![1, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h28 : (f ![1, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h13, h28, f_dead, pp_24, pp_13, pp_28]
  try (push_cast; ring)

lemma b_24 : (f ![0, 0, 1] 2 ![1, 1, 0] : ℚ) = PP 24 0 := by
  have h : (f ![0, 0, 1] 2 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_90
  rw [h, pp_24]; try norm_num

lemma st_25 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 25 (n + 1) := by
  have h13 : (f ![1, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h28 : (f ![1, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h13, h28, f_dead, pp_25, pp_13, pp_28]
  try (push_cast; ring)

lemma b_25 : (f ![0, 1, 1] 2 ![1, 1, 0] : ℚ) = PP 25 0 := by
  have h : (f ![0, 1, 1] 2 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_93
  rw [h, pp_25]; try norm_num

lemma st_26 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 26 (n + 1) := by
  have h13 : (f ![1, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h28 : (f ![1, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl11, h13, h28, f_dead, pp_26, pp_13, pp_28]
  try (push_cast; ring)

lemma b_26 : (f ![1, 1, 1] 2 ![1, 1, 0] : ℚ) = PP 26 0 := by
  have h : (f ![1, 1, 1] 2 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_94
  rw [h, pp_26]; try norm_num

lemma st_27 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 27 (n + 1) := by
  have h13 : (f ![1, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h28 : (f ![1, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h13, h28, f_dead, pp_27, pp_13, pp_28]
  try (push_cast; ring)

lemma b_27 : (f ![0, 1, 2] 2 ![1, 1, 0] : ℚ) = PP 27 0 := by
  have h : (f ![0, 1, 2] 2 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_102
  rw [h, pp_27]; try norm_num

lemma st_28 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2] (n + 2 + 1) ![1, 1, 0] : ℚ) = PP 28 (n + 1) := by
  have h13 : (f ![1, 1, 2] (n + 2) ![1, 0, 0] : ℚ) = PP 13 n := ih 13
  have h28 : (f ![1, 1, 2] (n + 2) ![1, 1, 0] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, dl20, h13, h28, f_dead, pp_28, pp_13, pp_28]
  try (push_cast; ring)

lemma b_28 : (f ![1, 1, 2] 2 ![1, 1, 0] : ℚ) = PP 28 0 := by
  have h : (f ![1, 1, 2] 2 ![1, 1, 0] : ℚ) = 4 := by exact_mod_cast fv2_103
  rw [h, pp_28]; try norm_num

lemma st_29 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![0, 0, 1] : ℚ) = PP 29 (n + 1) := by
  have h18 : (f ![0, 0, 1] (n + 2) ![0, 1, 0] : ℚ) = PP 18 n := ih 18
  have h37 : (f ![0, 0, 1] (n + 2) ![0, 1, 1] : ℚ) = PP 37 n := ih 37
  have h24 : (f ![0, 0, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 24 n := ih 24
  have h43 : (f ![0, 0, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h18, h37, h24, h43, f_dead, pp_29, pp_18, pp_37, pp_24, pp_43]
  try (push_cast; ring)

lemma b_29 : (f ![0, 0, 0] 2 ![0, 0, 1] : ℚ) = PP 29 0 := by
  have h : (f ![0, 0, 0] 2 ![0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv2_108
  rw [h, pp_29]; try norm_num

lemma st_30 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![0, 0, 1] : ℚ) = PP 30 (n + 1) := by
  have h19 : (f ![2, 0, 1] (n + 2) ![0, 1, 0] : ℚ) = PP 19 n := ih 19
  have h38 : (f ![2, 0, 1] (n + 2) ![0, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h19, h38, f_dead, pp_30, pp_19, pp_38]
  try (push_cast; ring)

lemma b_30 : (f ![1, 0, 0] 2 ![0, 0, 1] : ℚ) = PP 30 0 := by
  have h : (f ![1, 0, 0] 2 ![0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv2_109
  rw [h, pp_30]; try norm_num

lemma st_31 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0] (n + 2 + 1) ![0, 0, 1] : ℚ) = PP 31 (n + 1) := by
  have h19 : (f ![2, 0, 1] (n + 2) ![0, 1, 0] : ℚ) = PP 19 n := ih 19
  have h38 : (f ![2, 0, 1] (n + 2) ![0, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h19, h38, f_dead, pp_31, pp_19, pp_38]
  try (push_cast; ring)

lemma b_31 : (f ![2, 0, 0] 2 ![0, 0, 1] : ℚ) = PP 31 0 := by
  have h : (f ![2, 0, 0] 2 ![0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv2_110
  rw [h, pp_31]; try norm_num

lemma st_32 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0] (n + 2 + 1) ![0, 0, 1] : ℚ) = PP 32 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_32]
  try (push_cast; ring)

lemma b_32 : (f ![1, 2, 0] 2 ![0, 0, 1] : ℚ) = PP 32 0 := by
  have h : (f ![1, 2, 0] 2 ![0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv2_115
  rw [h, pp_32]; try norm_num

lemma st_33 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0] (n + 2 + 1) ![0, 0, 1] : ℚ) = PP 33 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, f_dead, pp_33]
  try (push_cast; ring)

lemma b_33 : (f ![2, 2, 0] 2 ![0, 0, 1] : ℚ) = PP 33 0 := by
  have h : (f ![2, 2, 0] 2 ![0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv2_116
  rw [h, pp_33]; try norm_num

lemma st_34 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![0, 1, 1] : ℚ) = PP 34 (n + 1) := by
  have h25 : (f ![0, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 25 n := ih 25
  have h44 : (f ![0, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h25, h44, f_dead, pp_34, pp_25, pp_44]
  try (push_cast; ring)

lemma b_34 : (f ![0, 0, 0] 2 ![0, 1, 1] : ℚ) = PP 34 0 := by
  have h : (f ![0, 0, 0] 2 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_162
  rw [h, pp_34]; try norm_num

lemma st_35 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![0, 1, 1] : ℚ) = PP 35 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, f_dead, pp_35]
  try (push_cast; ring)

lemma b_35 : (f ![1, 0, 0] 2 ![0, 1, 1] : ℚ) = PP 35 0 := by
  have h : (f ![1, 0, 0] 2 ![0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv2_163
  rw [h, pp_35]; try norm_num

lemma st_36 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0] (n + 2 + 1) ![0, 1, 1] : ℚ) = PP 36 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, f_dead, pp_36]
  try (push_cast; ring)

lemma b_36 : (f ![2, 0, 0] 2 ![0, 1, 1] : ℚ) = PP 36 0 := by
  have h : (f ![2, 0, 0] 2 ![0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv2_164
  rw [h, pp_36]; try norm_num

lemma st_37 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1] (n + 2 + 1) ![0, 1, 1] : ℚ) = PP 37 (n + 1) := by
  have h25 : (f ![0, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 25 n := ih 25
  have h44 : (f ![0, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h25, h44, f_dead, pp_37, pp_25, pp_44]
  try (push_cast; ring)

lemma b_37 : (f ![0, 0, 1] 2 ![0, 1, 1] : ℚ) = PP 37 0 := by
  have h : (f ![0, 0, 1] 2 ![0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_171
  rw [h, pp_37]; try norm_num

lemma st_38 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1] (n + 2 + 1) ![0, 1, 1] : ℚ) = PP 38 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_38]
  try (push_cast; ring)

lemma b_38 : (f ![2, 0, 1] 2 ![0, 1, 1] : ℚ) = PP 38 0 := by
  have h : (f ![2, 0, 1] 2 ![0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv2_173
  rw [h, pp_38]; try norm_num

lemma st_39 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 39 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h26, h45, f_dead, pp_39, pp_26, pp_45]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 0] 2 ![1, 1, 1] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 0] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_189
  rw [h, pp_39]; try norm_num

lemma st_40 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 40 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h45, f_dead, pp_40, pp_26, pp_45]
  try (push_cast; ring)

lemma b_40 : (f ![1, 0, 0] 2 ![1, 1, 1] : ℚ) = PP 40 0 := by
  have h : (f ![1, 0, 0] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_190
  rw [h, pp_40]; try norm_num

lemma st_41 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 41 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h45, f_dead, pp_41, pp_26, pp_45]
  try (push_cast; ring)

lemma b_41 : (f ![0, 1, 0] 2 ![1, 1, 1] : ℚ) = PP 41 0 := by
  have h : (f ![0, 1, 0] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_192
  rw [h, pp_41]; try norm_num

lemma st_42 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 42 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h45, f_dead, pp_42, pp_26, pp_45]
  try (push_cast; ring)

lemma b_42 : (f ![1, 1, 0] 2 ![1, 1, 1] : ℚ) = PP 42 0 := by
  have h : (f ![1, 1, 0] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_193
  rw [h, pp_42]; try norm_num

lemma st_43 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 43 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h45, f_dead, pp_43, pp_26, pp_45]
  try (push_cast; ring)

lemma b_43 : (f ![0, 0, 1] 2 ![1, 1, 1] : ℚ) = PP 43 0 := by
  have h : (f ![0, 0, 1] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_198
  rw [h, pp_43]; try norm_num

lemma st_44 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 44 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h26, h45, f_dead, pp_44, pp_26, pp_45]
  try (push_cast; ring)

lemma b_44 : (f ![0, 1, 1] 2 ![1, 1, 1] : ℚ) = PP 44 0 := by
  have h : (f ![0, 1, 1] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_201
  rw [h, pp_44]; try norm_num

lemma st_45 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1] (n + 2 + 1) ![1, 1, 1] : ℚ) = PP 45 (n + 1) := by
  have h26 : (f ![1, 1, 1] (n + 2) ![1, 1, 0] : ℚ) = PP 26 n := ih 26
  have h45 : (f ![1, 1, 1] (n + 2) ![1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, h26, h45, f_dead, pp_45, pp_26, pp_45]
  try (push_cast; ring)

lemma b_45 : (f ![1, 1, 1] 2 ![1, 1, 1] : ℚ) = PP 45 0 := by
  have h : (f ![1, 1, 1] 2 ![1, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_202
  rw [h, pp_45]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih]

lemma aBig (m : ℕ) : (a (m + 3) : ℚ) = ((1 : ℚ) / 720) * (m : ℚ) ^ 6 + ((3 : ℚ) / 80) * (m : ℚ) ^ 5 + ((83 : ℚ) / 144) * (m : ℚ) ^ 4 + ((77 : ℚ) / 16) * (m : ℚ) ^ 3 + ((1144 : ℚ) / 45) * (m : ℚ) ^ 2 + ((1423 : ℚ) / 20) * (m : ℚ) ^ 1 + (78 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0] (m + 2) ![0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g29 : (f ![0, 0, 0] (m + 2) ![0, 0, 1] : ℚ) = PP 29 m := f_closed m 29
  have g15 : (f ![0, 0, 0] (m + 2) ![0, 1, 0] : ℚ) = PP 15 m := f_closed m 15
  have g34 : (f ![0, 0, 0] (m + 2) ![0, 1, 1] : ℚ) = PP 34 m := f_closed m 34
  have g7 : (f ![0, 0, 0] (m + 2) ![1, 0, 0] : ℚ) = PP 7 m := f_closed m 7
  have g20 : (f ![0, 0, 0] (m + 2) ![1, 1, 0] : ℚ) = PP 20 m := f_closed m 20
  have g39 : (f ![0, 0, 0] (m + 2) ![1, 1, 1] : ℚ) = PP 39 m := f_closed m 39
  rw [show m + 3 = (m + 2) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 3 => (0 : Fin 3)) = ![0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g29, g15, g34, g7, g20, g39, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_29, pp_15, pp_34, pp_7, pp_20, pp_39]
  ring

lemma aS1 : (a 1 : ℚ) = 7 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 3 => (0 : Fin 3)) = ![0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 28 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 3 => (0 : Fin 3)) = ![0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 3 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_108, fv1_54, fv1_162, fv1_27, fv1_81, fv1_189]
  norm_num

lemma av (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 80) * (n : ℚ) ^ 5 + ((29 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 48) * (n : ℚ) ^ 3 + ((1727 : ℚ) / 360) * (n : ℚ) ^ 2 + ((-8 : ℚ) / 15) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp only [aS1, aS2] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 - 21 * X ^ 1 + 29 * X ^ 2 - 23 * X ^ 3 + 14 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (7 - 21 * X ^ 1 + 29 * X ^ 2 - 23 * X ^ 3 + 14 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : PowerSeries ℚ) =
        C (7 : ℚ) * X ^ 0 + C (-21 : ℚ) * X ^ 1 + C (29 : ℚ) * X ^ 2 + C (-23 : ℚ) * X ^ 3 + C (14 : ℚ) * X ^ 4 + C (-7 : ℚ) * X ^ 5 + C (2 : ℚ) * X ^ 6 by
      simp only [map_neg, map_ofNat, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 7 := aS1
    have e2 : (a 2 : ℚ) = 28 := aS2
    have e3 : (a 3 : ℚ) = 78 := by rw [av 3 (by norm_num)]; norm_num
    have e4 : (a 4 : ℚ) = 180 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 371 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 707 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 1269 := by rw [av 7 (by norm_num)]; norm_num
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

end OMA.P_oeis_a223772

theorem OMA.solution : type_of% @OMA.S_oeis_a223772.main := OMA.P_oeis_a223772.full
