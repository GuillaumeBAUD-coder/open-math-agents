import OMAStatements.S_oeis_a392003
import Mathlib

open OMA.S_oeis_a392003

namespace P392003

def F (t : ℕ) (i : ℤ) : Bool := decide ( i ≤ -(t : ℤ) ∨ (t : ℤ) + 1 ≤ i ∨ (-(t : ℤ) + 3 ≤ i ∧ (i + t) % 2 = 1))

lemma step (t : ℕ) (i : ℤ) : ca163 (t + 1) i = rule163 (ca163 t (i - 1)) (ca163 t i) (ca163 t (i + 1)) := rfl

lemma zero (j : ℤ) : ca163 0 j = decide (j = 0) := by
  simp only [ca163]
  by_cases h : j = 0
  · simp [h]
  · simp [h]

lemma one (i : ℤ) : ca163 1 i = F 1 i := by
  rw [step, zero, zero, zero]
  unfold F
  by_cases h1 : i - 1 = 0 <;> by_cases h2 : i = 0 <;> by_cases h3 : i + 1 = 0 <;>
    by_cases h4 : (i ≤ -((1 : ℕ) : ℤ) ∨ ((1 : ℕ) : ℤ) + 1 ≤ i ∨ (-((1 : ℕ) : ℤ) + 3 ≤ i ∧ (i + ((1 : ℕ) : ℤ)) % 2 = 1)) <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false] <;>
    first | rfl | omega

lemma form (t : ℕ) (ht : 1 ≤ t) : ∀ i, ca163 t i = F t i := by
  induction t with
  | zero => omega
  | succ t ih =>
    intro i
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; exact one i
    rw [step, ih h0, ih h0, ih h0]
    unfold F
    by_cases h1 : (i - 1 ≤ -(t : ℤ) ∨ (t : ℤ) + 1 ≤ i - 1 ∨ (-(t : ℤ) + 3 ≤ i - 1 ∧ (i - 1 + t) % 2 = 1)) <;>
    by_cases h2 : (i ≤ -(t : ℤ) ∨ (t : ℤ) + 1 ≤ i ∨ (-(t : ℤ) + 3 ≤ i ∧ (i + t) % 2 = 1)) <;>
    by_cases h3 : (i + 1 ≤ -(t : ℤ) ∨ (t : ℤ) + 1 ≤ i + 1 ∨ (-(t : ℤ) + 3 ≤ i + 1 ∧ (i + 1 + t) % 2 = 1)) <;>
    by_cases h4 : (i ≤ -((t + 1 : ℕ) : ℤ) ∨ ((t + 1 : ℕ) : ℤ) + 1 ≤ i ∨ (-((t + 1 : ℕ) : ℤ) + 3 ≤ i ∧ (i + ((t + 1 : ℕ) : ℤ)) % 2 = 1)) <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false] <;>
    first | rfl | (exfalso; omega)

def c (k : ℕ) : ℕ := if k = 0 ∨ (3 ≤ k ∧ k % 2 = 1) then 1 else 0

lemma hA (n : ℕ) (hn : 1 ≤ n) : A266753 n = ∑ k ∈ Finset.range (2 * n + 1), c k * 2 ^ (2 * n - k) := by
  unfold A266753
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [form n hn]
  have e : (F n ((k : ℤ) - n) = true) ↔ (k = 0 ∨ (3 ≤ k ∧ k % 2 = 1)) := by
    unfold F; rw [decide_eq_true_iff]; omega
  simp only [e, c]

def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), c k * 2 ^ (2 * n - k)

lemma S_succ (n : ℕ) (hn : 1 ≤ n) : S (n + 1) = 4 * S n + 2 := by
  unfold S
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.mul_sum]
  have e1 : c (2 * n + 1) = 1 := by unfold c; rw [if_pos (by omega)]
  have e2 : c (2 * n + 1 + 1) = 0 := by unfold c; rw [if_neg (by omega)]
  rw [e1, e2, show 2 * (n + 1) - (2 * n + 1) = 1 by omega]
  have : ∀ k ∈ Finset.range (2 * n + 1), c k * 2 ^ (2 * (n + 1) - k) = 4 * (c k * 2 ^ (2 * n - k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show 2 * (n + 1) - k = (2 * n - k) + 2 by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl this]
  ring

lemma S_one : S 1 = 4 := by decide

lemma S_form (m : ℕ) : 6 * (S (m + 1) : ℤ) = 7 * 4 ^ (m + 1) - 4 := by
  induction m with
  | zero => rw [S_one]; norm_num
  | succ m ih =>
    rw [S_succ (m + 1) (by omega)]
    push_cast
    rw [pow_succ]
    linarith

end P392003

open P392003 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392003.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hA (m + 1) hn]
  have h := S_form m
  unfold S at h
  unfold a
  have e : (7 * (2 : ℤ) ^ (2 * (m + 1)) - 9 + 5 * (-1 : ℤ) ^ (2 * (m + 1))) = 7 * 4 ^ (m + 1) - 4 := by
    rw [pow_mul, pow_mul]; norm_num; ring
  rw [e, ← h]
  push_cast
  omega
