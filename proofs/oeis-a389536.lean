import OMAStatements.S_oeis_a389536
import Mathlib

namespace CoefficientResidues

open OMA.S_oeis_a389536

private theorem coefficientStep (n : ℕ) (hn : 0 < n) :
    (b n : ZMod 4) = (term b n (n / 2) : ℕ) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [b.eq_2]
    simp only [dite_eq_ite, List.range_succ, List.map_append, List.sum_append, Nat.cast_add]
    have hz : (↑((List.range ((n + 1) / 2)).map
        (term (fun k => if k < n + 1 then b k else 0) (n + 1))).sum : ZMod 4) = 0 := by
      rw [Nat.cast_list_sum, List.map_map]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hlt := List.mem_range.mp hk
      have he : n + 1 - 2 * k = 2 + (n + 1 - 2 * k - 2) := by omega
      simp only [Function.comp_apply, term, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [he, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, zero_mul, mul_zero]
    have hlast : (n + 1) / 2 < n + 1 := by omega
    rw [hz, zero_add]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, term, if_pos hlast]

private theorem power_double (m : ℕ) (hm : 0 < m) :
    (∃ k : ℕ, 2 * m = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ j =>
      rw [pow_succ] at hk
      exact ⟨j, by omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by rw [pow_succ, Nat.mul_comm]⟩

private theorem power_odd (m : ℕ) (hm : 0 < m) : ¬ ∃ k : ℕ, 2 * m + 1 = 2 ^ k := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk; omega
  | succ j => rw [pow_succ] at hk; omega

open scoped Classical in
private theorem residues (n : ℕ) (hn : 0 < n) :
    (b n : ZMod 4) = if ∃ k : ℕ, n = 2 ^ k then 2 else 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      rw [if_pos (show ∃ k : ℕ, (1 : ℕ) = 2 ^ k from ⟨0, rfl⟩)]
      decide +kernel
    let m := n / 2
    have hm : 0 < m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hd : n = 2 * m ∨ n = 2 * m + 1 := by dsimp [m]; omega
    rw [coefficientStep n hn]
    change (↑(term b n m) : ZMod 4) = _
    rcases hd with he | ho
    · have hzero : n - 2 * m = 0 := by omega
      simp only [term, hzero, Nat.choose_zero_right, pow_zero, mul_one]
      rw [ih m hmn hm]
      have hp : (∃ k : ℕ, n = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
        rw [he]
        exact power_double m hm
      simp only [hp]
    · have hone : n - 2 * m = 1 := by omega
      have hp : ¬ ∃ k : ℕ, n = 2 ^ k := by
        rw [ho]
        exact power_odd m hm
      rw [if_neg hp]
      simp only [term, hone, Nat.choose_one_right, pow_one, Nat.cast_mul, Nat.cast_ofNat]
      rw [ih m hmn hm]
      split_ifs
      · calc
          (2 : ZMod 4) * (↑(m + 1) : ZMod 4) * 2 =
              (2 * 2) * (↑(m + 1) : ZMod 4) := by ring
          _ = 0 := by rw [show (2 : ZMod 4) * 2 = 0 by decide, zero_mul]
      · simp

end CoefficientResidues

theorem OMA.solution : type_of% @OMA.S_oeis_a389536.main := by
  classical
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have hm : 0 < m := by omega
    have hb := CoefficientResidues.residues m hm
    simp only [OMA.S_oeis_a389536.a, Nat.add_left_inj]
    by_cases hp : ∃ k : ℕ, m = 2 ^ k
    · refine Or.inl ⟨hp, ?_⟩
      rw [if_pos hp] at hb
      simpa [ZMod.val_natCast, show (2 : ZMod 4).val = 2 by decide] using congrArg ZMod.val hb
    · refine Or.inr ⟨hp, ?_⟩
      rw [if_neg hp] at hb
      simpa [ZMod.val_natCast] using congrArg ZMod.val hb