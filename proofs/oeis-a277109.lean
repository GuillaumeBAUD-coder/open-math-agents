import OMAStatements.S_oeis_a277109
import Mathlib

namespace A277109Proof

open OMA.S_oeis_a277109

theorem collatz_double (x : ℕ) : collatz (2 * x) = x := by
  unfold collatz
  rw [if_pos (by omega)]
  omega

theorem iter_double (i x : ℕ) : collatz^[i + 1] (2 * x) = collatz^[i] x := by
  rw [Function.iterate_succ_apply, collatz_double]

theorem steps_double (x : ℕ) (hx : 1 ≤ x) : steps (2 * x) = steps x + 1 := by
  unfold steps
  by_cases h : ∃ i : ℕ, collatz^[i] x = 1
  · have h2 : ∃ i : ℕ, collatz^[i] (2 * x) = 1 := by
      obtain ⟨i, hi⟩ := h
      exact ⟨i + 1, by rw [iter_double]; exact hi⟩
    rw [dif_pos h, dif_pos h2]
    have key : Nat.find h2 = Nat.find h + 1 := by
      rw [Nat.find_eq_iff]
      refine ⟨by rw [iter_double]; exact Nat.find_spec h, ?_⟩
      intro m hm
      cases m with
      | zero =>
        rw [Function.iterate_zero, id]
        omega
      | succ m =>
        rw [iter_double]
        exact Nat.find_min h (by omega)
    rw [key]
    push_cast
    rfl
  · have h2 : ¬ ∃ i : ℕ, collatz^[i] (2 * x) = 1 := by
      rintro ⟨i, hi⟩
      cases i with
      | zero =>
        rw [Function.iterate_zero, id] at hi
        omega
      | succ i =>
        rw [iter_double] at hi
        exact h ⟨i, hi⟩
    rw [dif_neg h, dif_neg h2]
    rfl

theorem succ_cancel (a b : ℕ∞) (h : a + 1 = b + 1) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe b =>
      exfalso
      have : ((b + 1 : ℕ) : ℕ∞) = ⊤ := by
        push_cast
        rw [← h]
        rfl
      exact ENat.coe_ne_top _ this
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((a + 1 : ℕ) : ℕ∞) = ⊤ := by
        push_cast
        rw [h]
        rfl
      exact ENat.coe_ne_top _ this
    | coe b =>
      have : ((a + 1 : ℕ) : ℕ∞) = ((b + 1 : ℕ) : ℕ∞) := by
        push_cast
        exact h
      have h3 : a + 1 = b + 1 := by exact_mod_cast this
      have h4 : a = b := by omega
      rw [h4]

theorem half (m i : ℕ) : steps (2 ^ (m + 1) + 2 * i) = steps (2 ^ m + i) + 1 := by
  have h1 : 2 ^ (m + 1) + 2 * i = 2 * (2 ^ m + i) := by ring
  rw [h1]
  exact steps_double _ (by have := Nat.one_le_two_pow (n := m); omega)

theorem main_proof : ∀ n k : ℕ, 1 ≤ n → 1 < k →
    RunLength n (2 ^ k - 1) → RunLength (n - 1) (2 ^ (k - 1) - 1) := by
  intro n k hn hk hrun
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  obtain ⟨-, hall, hend⟩ := hrun
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have h2j : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hbase : steps (2 ^ (m + 1) + 1) = steps (2 ^ m + 1) + 1 := by
    rw [← hall 2 (by omega) (by omega)]
    have := half m 1
    rw [Nat.mul_one] at this
    exact this
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi1 hi2
    apply succ_cancel
    rw [← half, ← hbase]
    exact hall (2 * i) (by omega) (by omega)
  · intro heq
    apply hend
    have e : 2 ^ (m + 1) + (2 ^ (j + 1) - 1) + 1 = 2 ^ (m + 1) + 2 * (2 ^ j) := by omega
    have e2 : 2 ^ m + (2 ^ j - 1) + 1 = 2 ^ m + 2 ^ j := by omega
    rw [e, half, hbase, ← heq, e2]

end A277109Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a277109.main := A277109Proof.main_proof
