import OMAStatements.S_oeis_a396722
import Mathlib

namespace OMA.A396722Proof

open OMA.S_oeis_a396722 Polynomial

/-- The value at 5/2 of the Lagrange basis polynomial attached to node 1. -/
noncomputable def q (n : ℕ) : ℚ :=
  (Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1) 0).eval (5 / 2)

theorem p_eq (n : ℕ) :
    p n = 1 - Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1) 0 := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℚ) + 1) (Finset.range (n + 1) : Set ℕ) := by
    intro x _ y _ h
    simpa using h
  have hs : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  have h1 := Lagrange.sum_basis hinj hs
  rw [p, Lagrange.interpolate_apply]
  have h2 : ∀ i ∈ Finset.range (n + 1),
      C (if i = 0 then (0 : ℚ) else 1) * Lagrange.basis (Finset.range (n + 1))
        (fun i : ℕ => (i : ℚ) + 1) i =
      Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1) i -
        if i = 0 then Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1) 0
        else 0 := by
    intro i _
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, h1, Finset.sum_ite_eq']
  simp

theorem a_eq (n : ℕ) : a n = 4 ^ n / 2 * (1 - q n) := by
  rw [a, p_eq, q, eval_sub, eval_one]

theorem q_zero : q 0 = 1 := by
  simp [q, Lagrange.basis]

theorem q_succ (n : ℕ) : q (n + 1) = q n * ((2 * (n : ℚ) - 1) / (2 * (n : ℚ) + 2)) := by
  have hr : (Finset.range (n + 1 + 1)).erase 0 = insert (n + 1) ((Finset.range (n + 1)).erase 0) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ (Finset.range (n + 1)).erase 0 := by simp
  rw [q, q, Lagrange.basis, Lagrange.basis, hr, Finset.prod_insert hnot, eval_mul]
  rw [mul_comm]
  congr 1
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  have h : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  have h' : (-1 - (n : ℚ)) ≠ 0 := by
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    intro h0
    linarith
  push_cast
  ring_nf
  field_simp
  ring

end OMA.A396722Proof

open OMA.S_oeis_a396722 OMA.A396722Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a396722.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, a_eq, a_eq, a_eq,
    show k + 2 = k + 1 + 1 by omega, q_succ (k + 1), q_succ k]
  have h1 : (2 * ((k + 1 : ℕ) : ℚ) + 2) ≠ 0 := by positivity
  have h2 : (2 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast at h1 ⊢
  field_simp
  ring
