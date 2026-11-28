import OMAStatements.S_oeis_a200887
import Mathlib

/-! Proof for OEIS A200887: arrays are built from the front. Let `A_m(t)` count valid arrays of length `m + 1` starting with `t`, and `B_m(t)` those whose second entry is `≥ t`. Prepending `t` to an array starting with `y` is valid iff `y ≤ t`, or the array's second entry is `≥ y`; this gives `A_(m+1)(t) = Σ_(y ≤ t) A_m(y) + Σ_(t < y ≤ n) B_m(y)` and `B_(m+1)(t) = A_m(t) + Σ_(t < y ≤ n) B_m(y)`, `A_0 = B_0 = 1`. Both are explicit polynomials in `(t, n)` (Faulhaber sums), so `a(n) = Σ_(t ≤ n) A_3(t)` is an explicit polynomial and the g.f. follows coefficientwise.
Credit: Sudharsan Rajendiran -/

namespace OMA.Old200887

/-- `ok l`: no interior entry of `l` is greater than both of its neighbours. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (c < b)) && ok (b :: c :: t)
  | _ => true

/-- A200887(n): the number of arrays `x(0..3)` of 4 elements in `0..n` without any interior element
greater than both neighbours. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

end OMA.Old200887

namespace OMA.P200887
open OMA.Old200887 Finset

/-- the second entry, if any, is at least the first. -/
def geS : List ℕ → Bool
  | a :: b :: _ => decide (a ≤ b)
  | _ => true

def okg (l : List ℕ) : Bool := ok l && geS l

lemma ok_cons (x y : ℕ) (t : List ℕ) :
    ok (x :: y :: t) = (ok (y :: t) && (decide (y ≤ x) || geS (y :: t))) := by
  cases t with
  | nil => simp [ok, geS]
  | cons c t =>
    simp only [ok, geS]
    by_cases h1 : x < y <;> by_cases h2 : c < y <;>
      simp [h1, h2, Nat.not_lt.mp, Bool.and_comm] <;> omega

abbrev arr (n L : ℕ) : Finset (Fin L → ℕ) := Fintype.piFinset fun _ : Fin L => range (n + 1)

lemma ofFn_eq {L : ℕ} (v : Fin (L + 1) → ℕ) : List.ofFn v = v 0 :: List.ofFn (Fin.tail v) := by
  rw [List.ofFn_succ]; rfl

/-- arrays of length `m + 1` starting with `t` satisfying `P`. -/
def S (n m t : ℕ) (P : List ℕ → Bool) : ℕ :=
  ((arr n (m + 1)).filter (fun w => w 0 = t ∧ P (List.ofFn w) = true)).card

lemma S_succ (n m t : ℕ) (P : List ℕ → Bool) (ht : t ≤ n) :
    S n (m + 1) t P = ((arr n (m + 1)).filter (fun w => P (t :: List.ofFn w) = true)).card := by
  unfold S
  apply card_nbij' (fun v => Fin.tail v) (fun w => Fin.cons t w)
  · intro v hv
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hv ⊢
    refine ⟨fun i => hv.1 _, ?_⟩
    have := hv.2.2; rw [ofFn_eq, hv.2.1] at this; exact this
  · intro w hw
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hw ⊢
    refine ⟨fun i => ?_, by simp, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp; omega
      · simpa using hw.1 j
    · rw [ofFn_eq]; simpa using hw.2
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv
    rw [← hv.2.1]; exact Fin.cons_self_tail v
  · intro w _; exact Fin.tail_cons _ _

lemma fiber (n m : ℕ) (R : List ℕ → Bool) :
    ((arr n (m + 1)).filter (fun w => R (List.ofFn w) = true)).card = ∑ y ∈ range (n + 1), S n m y R := by
  rw [card_eq_sum_card_fiberwise (f := fun w => w 0) (t := range (n + 1))]
  · apply sum_congr rfl; intro y _
    unfold S; rw [filter_filter]; congr 1; apply filter_congr; intro w _; exact and_comm
  · intro w hw
    simp only [coe_filter, mem_filter, Fintype.mem_piFinset, mem_range] at hw
    simpa using hw.1 0

lemma S_congr (n m y : ℕ) (P Q : List ℕ → Bool) (h : ∀ l, P (y :: l) = Q (y :: l)) :
    S n m y P = S n m y Q := by
  unfold S; congr 1; apply filter_congr; intro w _
  rw [ofFn_eq]
  constructor
  · rintro ⟨h0, hp⟩; exact ⟨h0, by rw [h0] at hp ⊢; rw [← h]; exact hp⟩
  · rintro ⟨h0, hp⟩; exact ⟨h0, by rw [h0] at hp ⊢; rw [h]; exact hp⟩

lemma S_false (n m y : ℕ) (P : List ℕ → Bool) (h : ∀ l, P (y :: l) = false) : S n m y P = 0 := by
  unfold S; rw [card_eq_zero, filter_eq_empty_iff]
  rintro w - ⟨h0, hp⟩
  rw [ofFn_eq, h0, h] at hp; exact absurd hp (by simp)

lemma S_zero (n t : ℕ) (P : List ℕ → Bool) (ht : t ≤ n) (hP : P [t] = true) : S n 0 t P = 1 := by
  unfold S; rw [card_eq_one]
  refine ⟨fun _ => t, ?_⟩
  ext w; simp only [mem_filter, Fintype.mem_piFinset, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, h0, -⟩; funext i; fin_cases i; exact h0
  · rintro rfl; exact ⟨fun _ => Nat.lt_succ_of_le ht, rfl, by simpa [List.ofFn_succ] using hP⟩

lemma recA (n m t : ℕ) (ht : t ≤ n) :
    S n (m + 1) t ok = ∑ y ∈ range (n + 1), (if y ≤ t then S n m y ok else S n m y okg) := by
  rw [S_succ n m t ok ht, fiber n m (fun l => ok (t :: l))]
  apply sum_congr rfl; intro y _
  split_ifs with h
  · apply S_congr; intro l; rw [ok_cons]; simp [h]
  · apply S_congr; intro l; rw [ok_cons]; simp [h, okg]

lemma recB (n m t : ℕ) (ht : t ≤ n) :
    S n (m + 1) t okg = ∑ y ∈ range (n + 1), (if y = t then S n m y ok else if t < y then S n m y okg else 0) := by
  rw [S_succ n m t okg ht, fiber n m (fun l => okg (t :: l))]
  apply sum_congr rfl; intro y _
  split_ifs with h1 h2
  · subst h1; apply S_congr; intro l; simp [okg, ok_cons, geS]
  · apply S_congr; intro l; simp [okg, ok_cons, geS, Nat.not_le.mpr h2, h2.le]
  · apply S_false; intro l
    have : ¬ t ≤ y := by omega
    simp [okg, ok_cons, geS, this]

lemma a_eq (n : ℕ) : a n = ∑ y ∈ range (n + 1), S n 3 y ok := by
  rw [← fiber]; rfl

lemma split_range (t n : ℕ) (ht : t ≤ n) (g : ℕ → ℚ) :
    ∑ y ∈ range (n + 1), g y = ∑ y ∈ range (t + 1), g y + ∑ y ∈ Ico (t + 1) (n + 1), g y := by
  rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive _ (by omega) (by omega)]

lemma split1 (t n : ℕ) (ht : t ≤ n) (f g : ℕ → ℚ) :
    ∑ y ∈ range (n + 1), (if y ≤ t then f y else g y) =
      ∑ y ∈ range (t + 1), f y + (∑ y ∈ range (n + 1), g y - ∑ y ∈ range (t + 1), g y) := by
  rw [split_range t n ht, split_range t n ht g]
  rw [sum_congr rfl (fun y hy => if_pos (by simp at hy; omega) : ∀ y ∈ range (t + 1), (if y ≤ t then f y else g y) = f y),
    sum_congr rfl (fun y hy => if_neg (by simp at hy; omega) : ∀ y ∈ Ico (t + 1) (n + 1), (if y ≤ t then f y else g y) = g y)]
  ring

lemma split2 (t n : ℕ) (ht : t ≤ n) (f g : ℕ → ℚ) :
    ∑ y ∈ range (n + 1), (if y = t then f y else if t < y then g y else 0) =
      f t + (∑ y ∈ range (n + 1), g y - ∑ y ∈ range (t + 1), g y) := by
  rw [split_range t n ht, split_range t n ht g, sum_range_succ]
  rw [sum_congr rfl (fun y hy => by rw [if_neg (by simp at hy; omega), if_neg (by simp at hy; omega)] :
      ∀ y ∈ range t, (if y = t then f y else if t < y then g y else 0) = 0),
    if_pos rfl,
    sum_congr rfl (fun y hy => by rw [if_neg (by simp at hy; omega), if_pos (by simp at hy; omega)] :
      ∀ y ∈ Ico (t + 1) (n + 1), (if y = t then f y else if t < y then g y else 0) = g y)]
  simp

def pa0 (n t : ℕ) : ℚ := (1 : ℚ)
def pb0 (n t : ℕ) : ℚ := (1 : ℚ)

def pa1 (n t : ℕ) : ℚ := (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)
def pb1 (n t : ℕ) : ℚ := (-1 : ℚ) * (t : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)

def pa2 (n t : ℕ) : ℚ := (1/2 : ℚ) * (t : ℚ) ^ 2 + (1/2 : ℚ) * (t : ℚ) ^ 1 + (1/2 : ℚ) * (n : ℚ) ^ 2 + (3/2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)
def pb2 (n t : ℕ) : ℚ := (1/2 : ℚ) * (t : ℚ) ^ 2 + (-1 : ℚ) * (t : ℚ) ^ 1 * (n : ℚ) ^ 1 + (-1/2 : ℚ) * (t : ℚ) ^ 1 + (1/2 : ℚ) * (n : ℚ) ^ 2 + (3/2 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)

def pa3 (n t : ℕ) : ℚ := (1/2 : ℚ) * (t : ℚ) ^ 2 * (n : ℚ) ^ 1 + (1/2 : ℚ) * (t : ℚ) ^ 2 + (1/2 : ℚ) * (t : ℚ) ^ 1 * (n : ℚ) ^ 1 + (1/2 : ℚ) * (t : ℚ) ^ 1 + (1/6 : ℚ) * (n : ℚ) ^ 3 + (3/2 : ℚ) * (n : ℚ) ^ 2 + (7/3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)
def pb3 (n t : ℕ) : ℚ := (-1/6 : ℚ) * (t : ℚ) ^ 3 + (1/2 : ℚ) * (t : ℚ) ^ 2 * (n : ℚ) ^ 1 + (1/2 : ℚ) * (t : ℚ) ^ 2 + (-1/2 : ℚ) * (t : ℚ) ^ 1 * (n : ℚ) ^ 2 + (-1 : ℚ) * (t : ℚ) ^ 1 * (n : ℚ) ^ 1 + (-1/3 : ℚ) * (t : ℚ) ^ 1 + (1/6 : ℚ) * (n : ℚ) ^ 3 + (3/2 : ℚ) * (n : ℚ) ^ 2 + (7/3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ)

lemma sum_pa0 (n s : ℕ) : ∑ y ∈ range (s + 1), pa0 n y = (1 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pa0]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pa0]; push_cast; ring

lemma sum_pb0 (n s : ℕ) : ∑ y ∈ range (s + 1), pb0 n y = (1 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pb0]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pb0]; push_cast; ring

lemma sum_pa1 (n s : ℕ) : ∑ y ∈ range (s + 1), pa1 n y = (1 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pa1]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pa1]; push_cast; ring

lemma sum_pb1 (n s : ℕ) : ∑ y ∈ range (s + 1), pb1 n y = (1 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (1 : ℚ) * (n : ℚ) ^ 1 + (-1/2 : ℚ) * (s : ℚ) ^ 2 + (1/2 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pb1]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pb1]; push_cast; ring

lemma sum_pa2 (n s : ℕ) : ∑ y ∈ range (s + 1), pa2 n y = (1/2 : ℚ) * (n : ℚ) ^ 2 * (s : ℚ) ^ 1 + (1/2 : ℚ) * (n : ℚ) ^ 2 + (3/2 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (3/2 : ℚ) * (n : ℚ) ^ 1 + (1/6 : ℚ) * (s : ℚ) ^ 3 + (1/2 : ℚ) * (s : ℚ) ^ 2 + (4/3 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pa2]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pa2]; push_cast; ring

lemma sum_pb2 (n s : ℕ) : ∑ y ∈ range (s + 1), pb2 n y = (1/2 : ℚ) * (n : ℚ) ^ 2 * (s : ℚ) ^ 1 + (1/2 : ℚ) * (n : ℚ) ^ 2 + (-1/2 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (3/2 : ℚ) * (n : ℚ) ^ 1 + (1/6 : ℚ) * (s : ℚ) ^ 3 + (5/6 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pb2]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pb2]; push_cast; ring

lemma sum_pa3 (n s : ℕ) : ∑ y ∈ range (s + 1), pa3 n y = (1/6 : ℚ) * (n : ℚ) ^ 3 * (s : ℚ) ^ 1 + (1/6 : ℚ) * (n : ℚ) ^ 3 + (3/2 : ℚ) * (n : ℚ) ^ 2 * (s : ℚ) ^ 1 + (3/2 : ℚ) * (n : ℚ) ^ 2 + (1/6 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 3 + (1/2 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 2 + (8/3 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (7/3 : ℚ) * (n : ℚ) ^ 1 + (1/6 : ℚ) * (s : ℚ) ^ 3 + (1/2 : ℚ) * (s : ℚ) ^ 2 + (4/3 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pa3]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pa3]; push_cast; ring

lemma sum_pb3 (n s : ℕ) : ∑ y ∈ range (s + 1), pb3 n y = (1/6 : ℚ) * (n : ℚ) ^ 3 * (s : ℚ) ^ 1 + (1/6 : ℚ) * (n : ℚ) ^ 3 + (-1/4 : ℚ) * (n : ℚ) ^ 2 * (s : ℚ) ^ 2 + (5/4 : ℚ) * (n : ℚ) ^ 2 * (s : ℚ) ^ 1 + (3/2 : ℚ) * (n : ℚ) ^ 2 + (1/6 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 3 + (-1/4 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 2 + (23/12 : ℚ) * (n : ℚ) ^ 1 * (s : ℚ) ^ 1 + (7/3 : ℚ) * (n : ℚ) ^ 1 + (-1/24 : ℚ) * (s : ℚ) ^ 4 + (1/12 : ℚ) * (s : ℚ) ^ 3 + (1/24 : ℚ) * (s : ℚ) ^ 2 + (11/12 : ℚ) * (s : ℚ) ^ 1 + (1 : ℚ) := by
  induction s with
  | zero => simp [pb3]
  | succ s ih => rw [sum_range_succ, ih]; simp only [pb3]; push_cast; ring

lemma cl0 (n t : ℕ) (ht : t ≤ n) : (S n 0 t ok : ℚ) = pa0 n t ∧ (S n 0 t okg : ℚ) = pb0 n t := by
  rw [S_zero n t ok ht (by simp [ok]), S_zero n t okg ht (by simp [okg, ok, geS])]; simp [pa0, pb0]

lemma cl1 (n t : ℕ) (ht : t ≤ n) : (S n 1 t ok : ℚ) = pa1 n t ∧ (S n 1 t okg : ℚ) = pb1 n t := by
  have IH : ∀ y ≤ n, (S n 0 y ok : ℚ) = pa0 n y ∧ (S n 0 y okg : ℚ) = pb0 n y := fun y hy => cl0 n y hy
  constructor
  · rw [recA n 0 t ht]; push_cast
    rw [split1 t n ht]
    rw [sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).1),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pa0, sum_pb0, sum_pb0]
    simp only [pa1]; ring
  · rw [recB n 0 t ht]; push_cast
    rw [split2 t n ht]
    rw [(IH t ht).1,
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pb0, sum_pb0]
    simp only [pb1, pa0]; ring

lemma cl2 (n t : ℕ) (ht : t ≤ n) : (S n 2 t ok : ℚ) = pa2 n t ∧ (S n 2 t okg : ℚ) = pb2 n t := by
  have IH : ∀ y ≤ n, (S n 1 y ok : ℚ) = pa1 n y ∧ (S n 1 y okg : ℚ) = pb1 n y := fun y hy => cl1 n y hy
  constructor
  · rw [recA n 1 t ht]; push_cast
    rw [split1 t n ht]
    rw [sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).1),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pa1, sum_pb1, sum_pb1]
    simp only [pa2]; ring
  · rw [recB n 1 t ht]; push_cast
    rw [split2 t n ht]
    rw [(IH t ht).1,
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pb1, sum_pb1]
    simp only [pb2, pa1]; ring

lemma cl3 (n t : ℕ) (ht : t ≤ n) : (S n 3 t ok : ℚ) = pa3 n t ∧ (S n 3 t okg : ℚ) = pb3 n t := by
  have IH : ∀ y ≤ n, (S n 2 y ok : ℚ) = pa2 n y ∧ (S n 2 y okg : ℚ) = pb2 n y := fun y hy => cl2 n y hy
  constructor
  · rw [recA n 2 t ht]; push_cast
    rw [split1 t n ht]
    rw [sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).1),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pa2, sum_pb2, sum_pb2]
    simp only [pa3]; ring
  · rw [recB n 2 t ht]; push_cast
    rw [split2 t n ht]
    rw [(IH t ht).1,
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2),
      sum_congr rfl (fun y hy => (IH y (by simp at hy; omega)).2)]
    rw [sum_pb2, sum_pb2]
    simp only [pb3, pa2]; ring

lemma closed (n : ℕ) : (a n : ℚ) = (1/3 : ℚ) * (n : ℚ) ^ 4 + (7/3 : ℚ) * (n : ℚ) ^ 3 + (14/3 : ℚ) * (n : ℚ) ^ 2 + (11/3 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) := by
  rw [a_eq n]; push_cast
  rw [sum_congr rfl (fun y hy => (cl3 n y (by simp at hy; omega)).1), sum_pa3]
  ring

open PowerSeries in
lemma gf_old :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (12 - 9 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  ext m
  have hX : ((1 - X) ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-5 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 + C (5 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_one, map_ofNat, map_natCast]; ring
  rw [hX]
  have hN : (X * (12 - 9 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : PowerSeries ℚ) = X ^ 1 * C (12 : ℚ) + X ^ 2 * C (-9 : ℚ) + X ^ 3 * C (9 : ℚ) + X ^ 4 * C (-5 : ℚ) + X ^ 5 * C (1 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hN]
  simp only [mul_add, map_add, coeff_mk, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mul_C, coeff_X,
    Nat.zero_le, if_true, Nat.sub_zero]
  have t1 : (OMA.Old200887.a 1 : ℚ) = 12 := by rw [OMA.P200887.closed]; norm_num
  have t2 : (OMA.Old200887.a 2 : ℚ) = 51 := by rw [OMA.P200887.closed]; norm_num
  have t3 : (OMA.Old200887.a 3 : ℚ) = 144 := by rw [OMA.P200887.closed]; norm_num
  have t4 : (OMA.Old200887.a 4 : ℚ) = 325 := by rw [OMA.P200887.closed]; norm_num
  have t5 : (OMA.Old200887.a 5 : ℚ) = 636 := by rw [OMA.P200887.closed]; norm_num
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num [t1, t2, t3, t4, t5, ]
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 6 := ⟨m - 6, by omega⟩
    simp only [if_pos (show 1 ≤ p + 6 by omega), if_pos (show 2 ≤ p + 6 by omega), if_pos (show 3 ≤ p + 6 by omega), if_pos (show 4 ≤ p + 6 by omega), if_pos (show 5 ≤ p + 6 by omega)]
    try simp only [if_neg (show ¬ (p + 6 = 0) by omega), if_neg (show ¬ (p + 6 = 1) by omega), if_neg (show ¬ (p + 6 = 2) by omega), if_neg (show ¬ (p + 6 = 3) by omega), if_neg (show ¬ (p + 6 = 4) by omega), if_neg (show ¬ (p + 6 = 5) by omega)]
    try simp only [if_neg (show ¬ (p + 6 - 0 = 0) by omega), if_neg (show ¬ (p + 6 - 1 = 0) by omega), if_neg (show ¬ (p + 6 - 2 = 0) by omega), if_neg (show ¬ (p + 6 - 3 = 0) by omega), if_neg (show ¬ (p + 6 - 4 = 0) by omega), if_neg (show ¬ (p + 6 - 5 = 0) by omega)]
    rw [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega, show p + 6 - 3 = p + 3 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 5 = p + 1 by omega]
    rw [OMA.P200887.closed (p + 6), OMA.P200887.closed (p + 5), OMA.P200887.closed (p + 4), OMA.P200887.closed (p + 3), OMA.P200887.closed (p + 2), OMA.P200887.closed (p + 1)]
    push_cast
    ring

lemma ofFn4 (v : Fin 4 → ℕ) : List.ofFn v = [v 0, v 1, v 2, v 3] := by
  simp [List.ofFn_succ]
lemma bridge (n : ℕ) : OMA.S_oeis_a200887.a n = OMA.Old200887.a n := by
  unfold OMA.S_oeis_a200887.a OMA.Old200887.a
  apply Finset.card_nbij' (fun (x : Fin 4 → Fin (n + 1)) i => (x i : ℕ))
    (fun v i => (⟨min (v i) n, by omega⟩ : Fin (n + 1)))
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fintype.mem_piFinset,
      Finset.mem_range] at hx ⊢
    refine ⟨fun i => (x i).isLt, ?_⟩
    rw [ofFn4]; unfold OMA.S_oeis_a200887.NoPeak at hx; simp only [Fin.lt_iff_val_lt_val] at hx
    simp [OMA.Old200887.ok, decide_eq_false_iff_not]; omega
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fintype.mem_piFinset,
      Finset.mem_range] at hv ⊢
    obtain ⟨hr, hv⟩ := hv
    have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
    rw [ofFn4] at hv; simp [OMA.Old200887.ok, decide_eq_false_iff_not] at hv
    unfold OMA.S_oeis_a200887.NoPeak; simp only [Fin.lt_iff_val_lt_val]
    omega
  · intro x _; funext i; apply Fin.ext; simp; exact Nat.le_of_lt_succ (x i).isLt
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, Finset.mem_range] at hv
    funext i; have := hv.1 i; simp; omega

lemma rec_new (n : ℕ) (hn : 5 < n) : (OMA.S_oeis_a200887.a n : ℤ) = 5 * OMA.S_oeis_a200887.a (n - 1) - 10 * OMA.S_oeis_a200887.a (n - 2) + 10 * OMA.S_oeis_a200887.a (n - 3) - 5 * OMA.S_oeis_a200887.a (n - 4) + OMA.S_oeis_a200887.a (n - 5) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  simp only [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega, show p + 6 - 3 = p + 3 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 5 = p + 1 by omega]
  simp only [bridge]
  rw [← @Int.cast_inj ℚ]
  push_cast
  simp only [closed]
  push_cast
  ring

end OMA.P200887

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a200887.main := by
  refine ⟨?_, ?_, OMA.P200887.rec_new⟩
  · have hf : (fun n => if n < 1 then (0 : ℚ) else (OMA.S_oeis_a200887.a n : ℚ)) =
        (fun n => if n = 0 then (0 : ℚ) else (OMA.Old200887.a n : ℚ)) := by
      funext n; rw [OMA.P200887.bridge]
      by_cases h : n = 0
      · simp [h]
      · simp [h, show ¬ n < 1 by omega]
    rw [hf]; exact OMA.P200887.gf_old
  · intro n _; rw [OMA.P200887.bridge, OMA.P200887.closed]; ring
