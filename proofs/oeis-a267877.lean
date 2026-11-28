import OMAStatements.S_oeis_a267877
import Mathlib

open OMA.S_oeis_a267877

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (t = 1 ∧ (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 1)) ∨
    (t = 2 ∧ (i ≠ -1 ∧ i ≠ 1)) ∨
    (t = 3 ∧ (i ≠ 0)) ∨
    (4 ≤ t ∧ t % 2 = 0) ∨
    (4 ≤ t ∧ t % 2 = 1)

private lemma table (l c r : Bool) :
    eca 233 l c r = true ↔ (c = true ∧ r = true) ∨ (l = false ∧ c = false ∧ r = false) ∨ (l = true ∧ r = true) ∨ (l = true ∧ c = true) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 4 with h | h
    · simp only [live]
      interval_cases t <;> omega
    · simp only [live, eq_false (show ¬ t = 0 by omega), eq_false (show ¬ t = 1 by omega), eq_false (show ¬ t = 2 by omega), eq_false (show ¬ t = 3 by omega), eq_false (show ¬ t + 1 = 0 by omega), eq_false (show ¬ t + 1 = 1 by omega), eq_false (show ¬ t + 1 = 2 by omega), eq_false (show ¬ t + 1 = 3 by omega), eq_true (show 4 ≤ t by omega), eq_true (show 4 ≤ t + 1 by omega), false_and, false_or, or_false, true_and]
      omega

private lemma wsum (n : ℕ) (f : ℕ → ℤ) (c : ℤ) (w : ℕ → ℤ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range n) (h : ∀ k < n, k ∉ E → f k = c * w k) :
    ∑ k ∈ Finset.range n, f k = c * ∑ k ∈ Finset.range n, w k + ∑ k ∈ E, (f k - c * w k) := by
  rw [Finset.sum_subset hE (fun k hk hkE => by rw [h k (Finset.mem_range.mp hk) hkE]; ring),
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

private lemma geo (t : ℕ) : ((2 : ℤ) - 1) * ∑ k ∈ Finset.range (2 * t + 1), (2 : ℤ) ^ (2 * t - k) =
    (2 : ℤ) ^ (2 * t + 1) - 1 := by
  have := Finset.sum_range_reflect (fun j => (2 : ℤ) ^ j) (2 * t + 1)
  simp only [show 2 * t + 1 - 1 = 2 * t by omega] at this
  rw [this, mul_comm, geom_sum_mul]

private lemma aval (t : ℕ) : (a t : ℤ) =
    ∑ k ∈ Finset.range (2 * t + 1), (if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0) := by
  unfold a; push_cast; rfl

private lemma row0 (t : ℕ) (ht : 4 ≤ t) (hp : t % 2 = 0) :
    ((1 : ℤ) * (2 : ℤ) ^ 0) * (a t : ℤ) = ((2 : ℤ) ^ (2 * t + 1 + 0) - (2 : ℤ) ^ 0) := by
  have key := wsum (2 * t + 1)
    (fun k => if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0) (1 : ℤ)
    (fun k => (2 : ℤ) ^ (2 * t - k)) (∅ : Finset ℕ)
    (by simp)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = true := by
        rw [state_iff]; simp only [live]; simp at hkE; push_cast <;> omega
      simp [hs])

  have g := geo t
  rw [aval]
  linear_combination (1 : ℤ) * (2 : ℤ) ^ 0 * key + (1 : ℤ) * (2 : ℤ) ^ 0 * g

private lemma row1 (t : ℕ) (ht : 4 ≤ t) (hp : t % 2 = 1) :
    ((1 : ℤ) * (2 : ℤ) ^ 0) * (a t : ℤ) = ((2 : ℤ) ^ (2 * t + 1 + 0) - (2 : ℤ) ^ 0) := by
  have key := wsum (2 * t + 1)
    (fun k => if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0) (1 : ℤ)
    (fun k => (2 : ℤ) ^ (2 * t - k)) (∅ : Finset ℕ)
    (by simp)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = true := by
        rw [state_iff]; simp only [live]; simp at hkE; push_cast <;> omega
      simp [hs])

  have g := geo t
  rw [aval]
  linear_combination (1 : ℤ) * (2 : ℤ) ^ 0 * key + (1 : ℤ) * (2 : ℤ) ^ 0 * g

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma cc (t : ℕ) (ht : 4 ≤ t) :
    2 * ((1 : ℤ) * (2 : ℤ) ^ 0) * (a t : ℤ) = (1 + (-1) ^ t) * (((2 : ℤ) ^ (2 * t + 1 + 0) - (2 : ℤ) ^ 0)) + (1 - (-1) ^ t) * (((2 : ℤ) ^ (2 * t + 1 + 0) - (2 : ℤ) ^ 0)) := by
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · have h := row0 (2 * m) ht (by omega); rw [ev]; linear_combination 2 * h
  · have h := row1 (2 * m + 1) ht (by omega); rw [od]; linear_combination 2 * h

private lemma v0 : a 0 = 1 := by decide

private lemma v1 : a 1 = 0 := by decide

private lemma v2 : a 2 = 21 := by decide

private lemma v3 : a 3 = 119 := by decide

set_option maxRecDepth 100000 in
private lemma v4 : a 4 = 511 := by
  have h := cc 4 (by norm_num)
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v5 : a 5 = 2047 := by
  have h := cc 5 (by norm_num)
  norm_num at h
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267877.main) := by
  intro h
  have hr := h.1 5 (by norm_num)
  simp only [show (5 : ℕ) - 1 = 4 from rfl, show (5 : ℕ) - 2 = 3 from rfl, v5, v4, v3] at hr
  norm_num at hr
