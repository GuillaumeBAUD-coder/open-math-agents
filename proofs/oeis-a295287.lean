import OMAStatements.S_oeis_a295287
import Mathlib

namespace OMA.A295287Proof

open OMA.S_oeis_a295287

def T (n m : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 m, i * (n - i) * ((i + 1) % 2)

theorem a_eq (n : ℕ) : a n = T n (n / 2) := rfl

theorem T_odd (n p : ℕ) : T n (2 * p + 1) = T n (2 * p) := by
  unfold T
  rw [Finset.sum_Icc_succ_top (by omega)]
  have : (2 * p + 1 + 1) % 2 = 0 := by omega
  rw [this, mul_zero, add_zero]

theorem T_even (n p : ℕ) (h : 2 * p ≤ n) :
    3 * (T n (2 * p) : ℤ) = 3 * n * p * (p + 1) - 2 * p * (p + 1) * (2 * p + 1) := by
  induction p with
  | zero => simp [T]
  | succ p ih =>
    have h' : 2 * p ≤ n := by omega
    have e : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
    rw [e]
    unfold T
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hT := T_odd n p
    unfold T at hT ih
    rw [hT]
    have hm : (2 * p + 1 + 1 + 1) % 2 = 1 := by omega
    rw [hm, mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]
    generalize (∑ i ∈ Finset.Icc 1 (2 * p), i * (n - i) * ((i + 1) % 2)) = S at ih ⊢
    push_cast
    linear_combination ih h'

theorem closed (N : ℕ) :
    3 * (a N : ℤ) = 3 * N * ((N / 4 : ℕ) : ℤ) * (((N / 4 : ℕ) : ℤ) + 1) -
      2 * ((N / 4 : ℕ) : ℤ) * (((N / 4 : ℕ) : ℤ) + 1) * (2 * ((N / 4 : ℕ) : ℤ) + 1) := by
  rw [a_eq]
  rcases (show N / 2 = 2 * (N / 4) ∨ N / 2 = 2 * (N / 4) + 1 by omega) with h | h
  · rw [h, T_even N (N / 4) (by omega)]
  · rw [h, T_odd, T_even N (N / 4) (by omega)]

end OMA.A295287Proof

open OMA.S_oeis_a295287 in
theorem OMA.solution : type_of% @OMA.S_oeis_a295287.main := by
  intro n hn
  obtain ⟨s, r, hr, rfl⟩ : ∃ s r, r < 4 ∧ n = 4 * s + r + 13 :=
    ⟨(n - 13) / 4, (n - 13) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show 4 * s + r + 13 - 1 = 4 * s + r + 12 by omega,
    show 4 * s + r + 13 - 4 = 4 * s + r + 9 by omega,
    show 4 * s + r + 13 - 5 = 4 * s + r + 8 by omega,
    show 4 * s + r + 13 - 8 = 4 * s + r + 5 by omega,
    show 4 * s + r + 13 - 9 = 4 * s + r + 4 by omega,
    show 4 * s + r + 13 - 12 = 4 * s + r + 1 by omega,
    show 4 * s + r + 13 - 13 = 4 * s + r + 0 by omega]
  have hdiv : ∀ c, (4 * s + r + c) / 4 = s + (r + c) / 4 := fun c => by omega
  have e13 := OMA.A295287Proof.closed (4 * s + r + 13)
  have e12 := OMA.A295287Proof.closed (4 * s + r + 12)
  have e9 := OMA.A295287Proof.closed (4 * s + r + 9)
  have e8 := OMA.A295287Proof.closed (4 * s + r + 8)
  have e5 := OMA.A295287Proof.closed (4 * s + r + 5)
  have e4 := OMA.A295287Proof.closed (4 * s + r + 4)
  have e1 := OMA.A295287Proof.closed (4 * s + r + 1)
  have e0 := OMA.A295287Proof.closed (4 * s + r + 0)
  rw [hdiv] at e13 e12 e9 e8 e5 e4 e1 e0
  have key : 3 * ((a (4 * s + r + 13) : ℤ) - (a (4 * s + r + 12) + 3 * a (4 * s + r + 9) -
      3 * a (4 * s + r + 8) - 3 * a (4 * s + r + 5) + 3 * a (4 * s + r + 4) +
      a (4 * s + r + 1) - a (4 * s + r + 0))) = 0 := by
    interval_cases r <;> norm_num at e13 e12 e9 e8 e5 e4 e1 e0 <;> push_cast at e13 e12 e9 e8 e5 e4 e1 e0 ⊢ <;>
      linear_combination e13 - e12 - 3 * e9 + 3 * e8 + 3 * e5 - 3 * e4 - e1 + e0
  omega
