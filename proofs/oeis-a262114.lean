import OMAStatements.S_oeis_a262114
import Mathlib

-- Problem: oeis-a262114 (Barker's recurrence and g.f. for the digits of 1/5 in base b)
-- Credit: @Aijy0264561
-- For 5 not dividing b = 5t + r, digit k of 1/5 is t * (r^k mod 5) + r (r^k mod 5) / 5, affine in t.
-- The bases 5t+2, ..., 5t+6 contribute exactly 12 entries (row lengths 4, 4, 2, 1, 1), so
-- a(12t + p + 1) is affine in t for each p < 12; both formulas follow.

namespace OMA.A262114proof

open OMA.S_oeis_a262114 PowerSeries

lemma digit_eq (t r k : ℕ) (hr : 1 ≤ r) (hr5 : r < 5) :
    digit (5 * t + r) k = t * (r ^ k % 5) + r * (r ^ k % 5) / 5 := by
  unfold digit
  have hb : (5 * t + r) ^ k % 5 = r ^ k % 5 := by
    rw [Nat.pow_mod, show (5 * t + r) % 5 = r by omega]
  have hd := Nat.div_add_mod ((5 * t + r) ^ k) 5
  set Q := (5 * t + r) ^ k / 5
  set e := r ^ k % 5 with he
  have he5 : e < 5 := Nat.mod_lt _ (by norm_num)
  rw [hb] at hd
  have hpow : (5 * t + r) ^ (k + 1) = 5 * ((5 * t + r) * Q + t * e) + r * e := by
    rw [pow_succ, ← hd]; ring
  rw [hpow, Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [show r * e / 5 + ((5 * t + r) * Q + t * e) = (5 * t + r) * Q + (t * e + r * e / 5) by ring,
    Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  interval_cases r <;> interval_cases e <;> omega

lemma cast5 (b : ℕ) : ((b : ℕ) : ZMod 5) = ((b % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod b 5).symm

lemma ord2 : orderOf (2 : ZMod 5) = 4 := by rw [orderOf_eq_iff (by norm_num)]; decide
lemma ord3 : orderOf (3 : ZMod 5) = 4 := by rw [orderOf_eq_iff (by norm_num)]; decide
lemma ord4 : orderOf (4 : ZMod 5) = 2 := by rw [orderOf_eq_iff (by norm_num)]; decide

lemma row2 (t : ℕ) : row (5 * t + 2) = [t, 2 * t, 4 * t + 1, 3 * t + 1] := by
  unfold row
  rw [if_neg (by omega), cast5, show (5 * t + 2) % 5 = 2 by omega]
  simp only [Nat.cast_ofNat, ord2]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, digit_eq t 2 _ (by norm_num) (by norm_num)]
  norm_num
  try ring_nf
  try simp

lemma row3 (t : ℕ) : row (5 * t + 3) = [t, 3 * t + 1, 4 * t + 2, 2 * t + 1] := by
  unfold row
  rw [if_neg (by omega), cast5, show (5 * t + 3) % 5 = 3 by omega]
  simp only [Nat.cast_ofNat, ord3]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, digit_eq t 3 _ (by norm_num) (by norm_num)]
  norm_num
  try ring_nf
  try simp

lemma row4 (t : ℕ) : row (5 * t + 4) = [t, 4 * t + 3] := by
  unfold row
  rw [if_neg (by omega), cast5, show (5 * t + 4) % 5 = 4 by omega]
  simp only [Nat.cast_ofNat, ord4]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, digit_eq t 4 _ (by norm_num) (by norm_num)]
  norm_num
  try ring_nf
  try simp

lemma row5 (t : ℕ) : row (5 * t + 5) = [t + 1] := by
  unfold row
  rw [if_pos (by omega)]
  simp only [digit, zero_add, pow_one]
  rw [show (5 * t + 5) / 5 = t + 1 by omega, Nat.mod_eq_of_lt (by omega)]

lemma row6 (t : ℕ) : row (5 * t + 6) = [t + 1] := by
  unfold row
  rw [if_neg (by omega), cast5, show (5 * t + 6) % 5 = 1 by omega]
  simp only [Nat.cast_one, orderOf_one]
  have := digit_eq (t + 1) 1 0 (by norm_num) (by norm_num)
  rw [show 5 * (t + 1) + 1 = 5 * t + 6 by ring] at this
  simp [this]

/-- The twelve entries contributed by the bases `5t+2, …, 5t+6`. -/
def block (t : ℕ) : List ℕ :=
  [t, 2 * t, 4 * t + 1, 3 * t + 1, t, 3 * t + 1, 4 * t + 2, 2 * t + 1, t, 4 * t + 3, t + 1, t + 1]

noncomputable def Fl (N : ℕ) : List ℕ := (List.range N).flatMap (fun k => row (k + 2))

lemma Fl_add (m k : ℕ) :
    Fl (m + k) = Fl m ++ (List.range k).flatMap (fun j => row (m + j + 2)) := by
  unfold Fl
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

lemma Fl_block (t : ℕ) : Fl (5 * (t + 1)) = Fl (5 * t) ++ block t := by
  rw [show 5 * (t + 1) = 5 * t + 5 by ring, Fl_add]
  congr 1
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show 5 * t + 0 + 2 = 5 * t + 2 by ring, show 5 * t + 1 + 2 = 5 * t + 3 by ring,
    show 5 * t + 2 + 2 = 5 * t + 4 by ring, show 5 * t + 3 + 2 = 5 * t + 5 by ring,
    show 5 * t + 4 + 2 = 5 * t + 6 by ring, row2, row3, row4, row5, row6]
  rfl

lemma length_Fl5 (t : ℕ) : (Fl (5 * t)).length = 12 * t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Fl_block, List.length_append, ih]; simp [block]; ring

lemma row_ne (b : ℕ) : 1 ≤ (row b).length := by
  unfold row
  split_ifs with h
  · simp
  · rw [cast5]
    have h5 : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have h0 : b % 5 ≠ 0 := fun h' => h (Nat.dvd_of_mod_eq_zero h')
    simp only [List.length_map, List.length_range]
    interval_cases hb : b % 5
    · omega
    · simp
    · simp [ord2]
    · simp [ord3]
    · simp [ord4]

lemma length_Fl (n : ℕ) : n ≤ (Fl n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fl_add n 1]
    simp only [List.length_append, List.range_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, add_zero]
    have := row_ne (n + 2)
    omega

lemma a_val (t p : ℕ) (hp : p < 12) : a (12 * t + p + 1) = (block t).getD p 0 := by
  have e : a (12 * t + p + 1) = (Fl (12 * t + p + 1)).getD (12 * t + p) 0 := rfl
  rw [e]
  have h1 := length_Fl (12 * t + p + 1)
  have hA := Fl_add (12 * t + p + 1) (5 * (t + 1))
  have hB := Fl_add (5 * (t + 1)) (12 * t + p + 1)
  rw [Nat.add_comm (5 * (t + 1))] at hB
  have hlen : (Fl (5 * (t + 1))).length = 12 * t + 12 := by
    rw [Fl_block, List.length_append, length_Fl5]; simp [block]
  rw [← List.getD_append _ _ 0 _ (show 12 * t + p < (Fl (12 * t + p + 1)).length by omega), ← hA,
    hB, List.getD_append _ _ 0 _ (by omega), Fl_block,
    List.getD_append_right _ _ 0 _ (by rw [length_Fl5]; omega), length_Fl5]
  congr 1; omega

lemma a_lit (n : ℕ) (hn : 1 ≤ n) : a n = (block ((n - 1) / 12)).getD ((n - 1) % 12) 0 := by
  have := a_val ((n - 1) / 12) ((n - 1) % 12) (Nat.mod_lt _ (by norm_num))
  rw [show 12 * ((n - 1) / 12) + (n - 1) % 12 + 1 = n by omega] at this
  exact this

lemma a_zero : a 0 = 0 := rfl

lemma rec0 (n : ℕ) (hn : 24 < n) :
    (a n : ℤ) - 2 * a (n - 12) + a (n - 24) = 0 := by
  obtain ⟨s, p, hp, rfl⟩ : ∃ s p, p < 12 ∧ n = 12 * (s + 2) + p + 1 :=
    ⟨(n - 25) / 12, (n - 25) % 12, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show 12 * (s + 2) + p + 1 - 12 = 12 * (s + 1) + p + 1 by omega,
    show 12 * (s + 2) + p + 1 - 24 = 12 * s + p + 1 by omega, a_val _ _ hp, a_val _ _ hp,
    a_val _ _ hp]
  interval_cases p <;> simp [block] <;> push_cast <;> ring

lemma numer_eq : (X ^ 3 * (X ^ 19 + X ^ 18 + X ^ 17 + 2 * X ^ 16 + 2 * X ^ 15 + X ^ 14 +
      2 * X ^ 13 + 3 * X ^ 12 + 2 * X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + 3 * X ^ 7 + X ^ 5 +
      2 * X ^ 4 + X ^ 3 + X + 1) : PowerSeries ℤ) =
    X ^ 22 + X ^ 21 + X ^ 20 + C 2 * X ^ 19 + C 2 * X ^ 18 + X ^ 17 + C 2 * X ^ 16 +
      C 3 * X ^ 15 + C 2 * X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + C 3 * X ^ 10 + X ^ 8 +
      C 2 * X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 := by
  simp only [map_ofNat]; ring

lemma denom_eq : (X ^ 24 - 2 * X ^ 12 + 1 : PowerSeries ℤ) = 1 - C 2 * X ^ 12 + X ^ 24 := by
  simp only [map_ofNat]; ring

theorem a262114 :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 2 * a (n - 12) - a (n - 24)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (X ^ 24 - 2 * X ^ 12 + 1) =
      X ^ 3 * (X ^ 19 + X ^ 18 + X ^ 17 + 2 * X ^ 16 + 2 * X ^ 15 + X ^ 14 + 2 * X ^ 13 +
        3 * X ^ 12 + 2 * X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + 3 * X ^ 7 + X ^ 5 + 2 * X ^ 4 +
        X ^ 3 + X + 1) := by
  refine ⟨fun n hn => by linarith [rec0 n hn], ?_⟩
  rw [denom_eq, numer_eq]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 25 with h | h
  · interval_cases n <;> simp [a_zero, a_lit, block]
  · have := rec0 n h
    simp only [show 12 ≤ n by omega, show 24 ≤ n by omega, if_true,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      show n ≠ 8 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega,
      show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega, show n ≠ 16 by omega,
      show n ≠ 17 by omega, show n ≠ 18 by omega, show n ≠ 19 by omega, show n ≠ 20 by omega,
      show n ≠ 21 by omega, show n ≠ 22 by omega, if_false, Nat.sub_eq_zero_iff_le,
      show ¬ n ≤ 7 by omega, show ¬ n ≤ 10 by omega, show ¬ n ≤ 14 by omega,
      show ¬ n ≤ 15 by omega, show ¬ n ≤ 16 by omega, show ¬ n ≤ 18 by omega,
      show ¬ n ≤ 19 by omega, ite_self]
    linarith

end OMA.A262114proof

theorem OMA.solution : type_of% @OMA.S_oeis_a262114.main := OMA.A262114proof.a262114
