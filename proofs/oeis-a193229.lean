import OMAStatements.S_oeis_a193229
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Local recurrence T(n+1,k+1) = T(n+1,k+2) + (k+1) T(n,k) and T(n+1,0)=T(n+1,1);
-- then induction on n with downward induction on k, closing by factorial arithmetic.

namespace OMA.A193229Proof
open OMA.S_oeis_a193229
lemma Lz (n k : ℕ) (h : n < k) : a193229 n k = 0 := by
  cases n with
  | zero => obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; rfl
  | succ n =>
    simp only [a193229]
    apply Finset.sum_eq_zero
    intro i hi
    simp at hi
    simp [show ¬ k ≤ i + 1 by omega]

lemma L1 (n k : ℕ) :
    a193229 (n+1) (k+1) = a193229 (n+1) (k+2) + (k+1) * a193229 n k := by
  simp only [a193229]
  have h : ∀ i ∈ Finset.range (n+1),
      (if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) =
      (if k + 2 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
      (if k = i then (k + 1) * a193229 n k else 0) := by
    intro i _
    by_cases h1 : k = i
    · subst h1; simp
    · by_cases h2 : k + 2 ≤ i + 1
      · simp [h1, h2, show k + 1 ≤ i + 1 by omega]
      · simp [h1, h2, show ¬ k + 1 ≤ i + 1 by omega]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq]
  by_cases hk : k < n + 1
  · simp [hk]
  · have h0 : ∀ i ∈ Finset.range (n+1),
        (if k + 2 ≤ i + 1 then (i + 1) * a193229 n i else 0) = 0 := by
      intro i hi
      simp at hi
      simp [show ¬ k + 2 ≤ i + 1 by omega]
    have h0' : ∀ i ∈ Finset.range (n+1),
        (if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) = 0 := by
      intro i hi
      simp at hi
      simp [show ¬ k + 1 ≤ i + 1 by omega]
    simp [hk, Lz n k (by omega)]

lemma L0 (n : ℕ) : a193229 (n+1) 0 = a193229 (n+1) 1 := by
  simp only [a193229]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem main' :
    ∀ n k : ℕ, k ≤ n →
      2 ^ (n - k) * (n - k).factorial * a193229 n k = (2 * n - k).factorial := by
  intro n
  induction n with
  | zero => intro k hk; obtain rfl : k = 0 := by omega
            simp [a193229]
  | succ n ih =>
    have key : ∀ m k, k + m = n + 1 →
        2 ^ (n + 1 - k) * (n + 1 - k).factorial * a193229 (n+1) k
          = (2 * (n+1) - k).factorial := by
      intro m
      induction m with
      | zero =>
        intro k hk
        obtain rfl : k = n + 1 := by omega
        have := ih n le_rfl
        rw [L1, show 2 * n - n = n by omega] at *
        simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, one_mul] at *
        have hz : a193229 (n+1) (n+2) = 0 := by
          simp only [a193229]
          apply Finset.sum_eq_zero
          intro i hi
          simp at hi
          simp [show ¬ n + 2 ≤ i + 1 by omega]
        rw [hz, show 2 * (n+1) - (n+1) = n + 1 by omega, Nat.factorial_succ, ← this]
        ring
      | succ m ihm =>
        intro k hk
        have hB := ihm (k+1) (by omega)
        rcases k with _ | k
        · rw [L0]
          obtain rfl : n = m := by omega
          rw [show 2 * (n + 1) - (0 + 1) = 2 * n + 1 by omega,
            show n + 1 - (0 + 1) = n by omega] at hB
          rw [show 2 * (n + 1) - 0 = (2 * n + 1) + 1 by omega,
            show n + 1 - 0 = n + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, ← hB,
            pow_succ]
          ring
        · have hA := ih k (by omega)
          rw [L1]
          obtain rfl : n = k + 1 + m := by omega
          rw [show 2 * (k + 1 + m + 1) - (k + 1 + 1) = k + 2 * m + 2 by omega,
            show k + 1 + m + 1 - (k + 1 + 1) = m by omega] at hB
          rw [show 2 * (k + 1 + m) - k = k + 2 * m + 2 by omega,
            show k + 1 + m - k = m + 1 by omega] at hA
          rw [show 2 * (k + 1 + m + 1) - (k + 1) = (k + 2 * m + 2) + 1 by omega,
            show k + 1 + m + 1 - (k + 1) = m + 1 by omega, Nat.factorial_succ]
          rw [Nat.factorial_succ, pow_succ] at hA ⊢
          have e : (k + 2 * m + 2 + 1) * (k + 2 * m + 2).factorial
              = 2 * (m+1) * (k + 2 * m + 2).factorial + (k+1) * (k + 2 * m + 2).factorial := by
            ring
          rw [e]
          nth_rewrite 1 [← hB]
          nth_rewrite 1 [← hA]
          ring
    intro k hk
    exact key (n + 1 - k) k (by omega)

end OMA.A193229Proof

open OMA.S_oeis_a193229 in
theorem OMA.solution : type_of% @OMA.S_oeis_a193229.main := by
  exact OMA.A193229Proof.main'
