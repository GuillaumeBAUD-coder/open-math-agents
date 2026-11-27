import OMAStatements.S_oeis_a001045
import Mathlib

namespace OMA.P_oeis_a001045

open Finset OMA.S_oeis_a001045

theorem a_succ (n : ℕ) : a (n + 1) = 2 * a n + (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a]
    | 1, _ => simp [a]
    | (m + 2), ih =>
      have h1 := ih (m + 1) (by omega)
      show a (m + 2) + 2 * a (m + 1) = _
      rw [h1]
      ring

theorem a_closed (n : ℕ) : 3 * a n = ((2 ^ n : ℕ) : ℤ) - (-1) ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [a_succ]
    push_cast at ih ⊢
    rw [pow_succ, pow_succ]
    linarith

theorem pow_entry (n : ℕ) (i j : Fin 3) :
    (A ^ n) i j = a n + if i = j then (-1) ^ n else 0 := by
  induction n generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, a]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, ih, ih, ih, a_succ]
    fin_cases i <;> fin_cases j <;> simp [A] <;> ring

theorem cnt_Ioc (x y : ℕ) (h : x ≤ y) : #{m ∈ Ioc x y | 3 ∣ m} = y / 3 - x / 3 := by
  have hu := Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) h
  have hd : Disjoint (Ioc 0 x) (Ioc x y) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [mem_Ioc] at hm hm'
    omega
  have e := Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (p := fun m => 3 ∣ m)
    (q := fun m => 3 ∣ m) hd)
  rw [← Finset.filter_union, hu, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at e
  omega

theorem count (n : ℕ) :
    ((((Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card : ℕ) : ℤ) = a n := by
  have hpos : 0 < 2 ^ n := by positivity
  have e : (Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)
      = (Finset.Ioc (2 ^ n) (2 ^ n * 2 - 1)).filter (fun m => 3 ∣ m) := by
    ext m
    simp only [mem_filter, mem_Ioo, mem_Ioc, pow_succ]
    omega
  rw [e, cnt_Ioc _ _ (by omega)]
  have hc := a_closed n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hm : 2 ^ n % 3 = 1 := by
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [Even.neg_one_pow ⟨k, hk⟩] at hc
    omega
  · have hm : 2 ^ n % 3 = 2 := by
      rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [Odd.neg_one_pow ⟨k, hk⟩] at hc
    omega

end OMA.P_oeis_a001045

theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main := by
  refine ⟨OMA.P_oeis_a001045.count, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.trace, Fin.sum_univ_three]
    simp only [Matrix.diag, OMA.P_oeis_a001045.pow_entry, if_true,
      OMA.P_oeis_a001045.a_succ, Nat.add_sub_cancel]
    ring
  · intro i j hij
    rw [OMA.P_oeis_a001045.pow_entry, if_neg hij, add_zero]
  · intro i
    rw [OMA.P_oeis_a001045.pow_entry, if_pos rfl]
    split_ifs with he
    · rw [Even.neg_one_pow he]
    · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)]
      ring
