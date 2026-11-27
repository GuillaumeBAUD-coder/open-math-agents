import OMAStatements.S_oeis_a234307
import Mathlib

namespace OMA.P_a234307

open Finset

/-- `A m = ∑_{k=1}^{m} gcd(k, 2m)`. -/
def A (m : ℕ) : ℕ := ∑ j ∈ range m, Nat.gcd (j + 1) (2 * m)

/-- `O m = ∑_{k odd, k ≤ 2m} gcd(k, m)`. -/
def O (m : ℕ) : ℕ := ∑ j ∈ range m, Nat.gcd (2 * j + 1) m

lemma sum_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range (2 * m), f k = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    abel

lemma sum_Icc_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Icc 1 N, f k = ∑ j ∈ range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma gcd_odd (j m : ℕ) : Nat.gcd (2 * j + 1) (2 * m) = Nat.gcd (2 * j + 1) m := by
  apply Nat.Coprime.gcd_mul_left_cancel_right
  rw [Nat.coprime_two_left]
  exact odd_two_mul_add_one j

lemma A_two (m : ℕ) : A (2 * m) = 2 * A m + O m := by
  unfold A O
  rw [sum_two_mul (fun k => Nat.gcd (k + 1) (2 * (2 * m))), mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.gcd_mul_left,
    show 2 * (2 * m) = 2 * (2 * m) by rfl, gcd_odd, gcd_odd]
  ring

lemma O_two (n : ℕ) : O (2 * n) = 2 * O n := by
  unfold O
  rw [two_mul n, sum_range_add, two_mul (∑ j ∈ range n, _)]
  congr 1
  · apply sum_congr rfl; intro j _; rw [← two_mul, gcd_odd]
  · apply sum_congr rfl; intro j _
    rw [← two_mul, gcd_odd, show 2 * (n + j) + 1 = 2 * j + 1 + n * 2 by ring,
      Nat.gcd_add_mul_left_left]

end OMA.P_a234307

open OMA.P_a234307 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a234307.main := by
  intro n hn
  have hL : OMA.S_oeis_a234307.a n = A n := by
    unfold OMA.S_oeis_a234307.a A
    rw [sum_Icc_one]
    apply sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ 2 * n := by simp at hj; omega
    rw [Nat.gcd_comm, ← Nat.gcd_sub_self_right hj']
  have hR : ∑ k ∈ Icc 1 (4 * n), (-1 : ℚ) ^ k * (Nat.gcd k (8 * n) : ℚ)
      = 2 * (A (2 * n) : ℚ) - (O (2 * n) : ℚ) := by
    rw [sum_Icc_one, show 4 * n = 2 * (2 * n) by ring, sum_two_mul]
    unfold A O
    push_cast
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 8 * n = 2 * (2 * (2 * n)) by ring,
      Nat.gcd_mul_left, gcd_odd, gcd_odd]
    rw [pow_succ, pow_mul, pow_succ, pow_mul]
    push_cast
    ring
  rw [hL, hR, A_two, O_two]
  push_cast
  ring
