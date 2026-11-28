import OMAStatements.S_oeis_a059894
import Mathlib

-- Problem: A059894, complement and reverse all but the top bit; recurrence and binary weight.
-- Credit: @jagong-cmu
-- Proof: with D the bits of n without the top bit, a(n) has bits reverse(1-D) ++ [1]. For
-- 2n and 2n+1, D gets a new low bit 0 or 1, which becomes a new high bit 1 or 0 of a.
-- A054429(n) has bits (1-D) ++ [1], and the weight of 1-D is the number of 0s in D.
namespace OMAa059894

open OMA.S_oeis_a059894

/-- The binary digits of `n` without the most significant bit. -/
def D (n : ℕ) : List ℕ := (Nat.digits 2 n).dropLast

/-- Bitwise complement of a list of bits. -/
def C (l : List ℕ) : List ℕ := l.map (fun b => 1 - b)

theorem a_eq (n : ℕ) : a n = Nat.ofDigits 2 ((C (D n)).reverse ++ [1]) := rfl

theorem digits_two_mul (m : ℕ) (hm : 1 ≤ m) : Nat.digits 2 (2 * m) = 0 :: Nat.digits 2 m := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [h1, h2]

theorem digits_two_mul_add_one (m : ℕ) :
    Nat.digits 2 (2 * m + 1) = 1 :: Nat.digits 2 m := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2]

theorem ne_nil (m : ℕ) (hm : 1 ≤ m) : Nat.digits 2 m ≠ [] :=
  Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)

theorem D_two_mul (m : ℕ) (hm : 1 ≤ m) : D (2 * m) = 0 :: D m := by
  rw [D, digits_two_mul m hm, List.dropLast_cons_of_ne_nil (ne_nil m hm)]
  rfl

theorem D_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) : D (2 * m + 1) = 1 :: D m := by
  rw [D, digits_two_mul_add_one m, List.dropLast_cons_of_ne_nil (ne_nil m hm)]
  rfl

theorem len_D (m : ℕ) (hm : 1 ≤ m) : (D m).length = Nat.log 2 m := by
  rw [D, List.length_dropLast, Nat.length_digits 2 m (by norm_num) (by omega)]
  omega

theorem len_C (l : List ℕ) : (C l).length = l.length := by
  simp [C]

theorem rec_even (m : ℕ) (hm : 1 ≤ m) : a (2 * m) = a m + 2 ^ (Nat.log 2 m + 1) := by
  rw [a_eq, a_eq, D_two_mul m hm]
  simp only [C, List.map_cons, List.reverse_cons, List.append_assoc, Nat.ofDigits_append]
  have hl : ((List.map (fun b => 1 - b) (D m)).reverse).length = Nat.log 2 m := by
    rw [List.length_reverse, List.length_map, len_D m hm]
  rw [hl]
  norm_num [Nat.ofDigits, pow_succ]
  ring

theorem rec_odd (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = a m + 2 ^ Nat.log 2 m := by
  rw [a_eq, a_eq, D_two_mul_add_one m hm]
  simp only [C, List.map_cons, List.reverse_cons, List.append_assoc, Nat.ofDigits_append]
  have hl : ((List.map (fun b => 1 - b) (D m)).reverse).length = Nat.log 2 m := by
    rw [List.length_reverse, List.length_map, len_D m hm]
  rw [hl]
  norm_num [Nat.ofDigits, pow_succ]
  ring

theorem bin_D (n : ℕ) : ∀ x ∈ D n, x < 2 := by
  intro x hx
  exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_dropLast hx)

theorem bin_C (l : List ℕ) : ∀ x ∈ C l, x < 2 := by
  intro x hx
  simp only [C, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  omega

theorem split (n : ℕ) (hn : 1 ≤ n) : Nat.digits 2 n = D n ++ [1] := by
  have hne := ne_nil n hn
  have hlast := Nat.getLast_digit_ne_zero 2 (show n ≠ 0 by omega)
  have hlt : (Nat.digits 2 n).getLast hne < 2 :=
    Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
  have h1 : (Nat.digits 2 n).getLast hne = 1 := by omega
  rw [D]
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [h1]

theorem digits_of (l : List ℕ) (hl : ∀ x ∈ l, x < 2) :
    Nat.digits 2 (Nat.ofDigits 2 (l ++ [1])) = l ++ [1] := by
  apply Nat.digits_ofDigits 2 (by norm_num)
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hl x hx
    · simp at hx
      omega
  · intro _
    simp

theorem comp_add (l : List ℕ) (hl : ∀ x ∈ l, x < 2) :
    Nat.ofDigits 2 (C l) + Nat.ofDigits 2 l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [C]
  | cons x l ih =>
    have hx : x < 2 := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    simp only [C, List.map_cons] at ih' ⊢
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

theorem sum_C (l : List ℕ) (hl : ∀ x ∈ l, x < 2) : (C l).sum = l.count 0 := by
  induction l with
  | nil => simp [C]
  | cons x l ih =>
    have hx : x < 2 := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    simp only [C, List.map_cons, List.sum_cons, List.count_cons] at ih' ⊢
    rw [ih']
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
    · simp
      omega
    · simp

theorem rev_eq (n : ℕ) (hn : 1 ≤ n) : rev n = Nat.ofDigits 2 (C (D n) ++ [1]) := by
  have hc := comp_add (D n) (bin_D n)
  have hd : n = Nat.ofDigits 2 (D n ++ [1]) := by
    conv_lhs => rw [← Nat.ofDigits_digits 2 n, split n hn]
  rw [Nat.ofDigits_append, len_D n hn] at hd
  rw [Nat.ofDigits_append, len_C, len_D n hn, rev, pow_succ]
  rw [len_D n hn] at hc
  norm_num [Nat.ofDigits] at hd ⊢
  omega

theorem wt_a (n : ℕ) : wt (a n) = (C (D n)).sum + 1 := by
  rw [wt, a_eq, digits_of _ (by
    intro x hx
    exact bin_C (D n) x (List.mem_reverse.mp hx))]
  simp

theorem wt_rev (n : ℕ) (hn : 1 ≤ n) : wt (rev n) = (C (D n)).sum + 1 := by
  rw [wt, rev_eq n hn, digits_of _ (bin_C (D n))]
  simp

theorem zeros_eq (n : ℕ) (hn : 1 ≤ n) : zeros n = (D n).count 0 := by
  rw [zeros, split n hn, List.count_append]
  simp

theorem sol :
    a 1 = 1 ∧
      (∀ n : ℕ, 1 ≤ n →
        a (2 * n) = a n + 2 ^ (Nat.log 2 n + 1) ∧ a (2 * n + 1) = a n + 2 ^ Nat.log 2 n) ∧
      (∀ n : ℕ, 1 ≤ n → wt (a n) = wt (rev n) ∧ wt (rev n) = zeros n + 1) := by
  refine ⟨?_, fun n hn => ⟨rec_even n hn, rec_odd n hn⟩, fun n hn => ⟨?_, ?_⟩⟩
  · norm_num [a, Nat.ofDigits]
  · rw [wt_a, wt_rev n hn]
  · rw [wt_rev n hn, zeros_eq n hn, sum_C (D n) (bin_D n)]

end OMAa059894

theorem OMA.solution : type_of% @OMA.S_oeis_a059894.main :=
  OMAa059894.sol
