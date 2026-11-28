import OMAStatements.S_oeis_a080239
import Mathlib

open OMA.S_oeis_a080239 in
theorem OMA.solution : type_of% @OMA.S_oeis_a080239.main := by
  have st (N : ℕ) : a (N+4) = a N + Nat.fib (N+4) := by
    unfold a
    rw [show (N+4)/4+1 = N/4+1+1 by omega, Finset.sum_range_succ']
    congr 1
    exact Finset.sum_congr rfl fun j _ => by congr 1; omega
  have K (m : ℕ) : a (4*m) = Nat.fib (2*m+2) * Nat.fib (2*m) ∧
      a (4*m+1) = Nat.fib (2*m+2) * Nat.fib (2*m+1) ∧ a (4*m+2) = Nat.fib (2*m+2) ^ 2 ∧
      a (4*m+3) + 1 = Nat.fib (2*m+4) * Nat.fib (2*m+1) := by
    induction m with
    | zero => decide
    | succ m ih =>
      have t0 : a (4*m+4) = a (4*m) +
          Nat.fib (2*m+1+1) * (2*Nat.fib (2*m+1) + Nat.fib (2*m+1+1)) := by
        rw [st, show 4*m+4 = 2*(2*m+1)+2 by ring, Nat.fib_two_mul_add_two]
      have t1 : a (4*m+1+4) = a (4*m+1) + (Nat.fib (2*m+2+1)^2 + Nat.fib (2*m+2)^2) := by
        rw [st, show 4*m+1+4 = 2*(2*m+2)+1 by ring, Nat.fib_two_mul_add_one]
      have t2 : a (4*m+2+4) = a (4*m+2) +
          Nat.fib (2*m+2+1) * (2*Nat.fib (2*m+2) + Nat.fib (2*m+2+1)) := by
        rw [st, show 4*m+2+4 = 2*(2*m+2)+2 by ring, Nat.fib_two_mul_add_two]
      have t3 : a (4*m+3+4) = a (4*m+3) + (Nat.fib (2*m+3+1)^2 + Nat.fib (2*m+3)^2) := by
        rw [st, show 4*m+3+4 = 2*(2*m+3)+1 by ring, Nat.fib_two_mul_add_one]
      simp only [mul_add, mul_one, add_assoc, Nat.reduceAdd, Nat.fib_add_two]
        at t0 t1 t2 t3 ih ⊢
      obtain ⟨h0, h1, h2, h3⟩ := ih
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have P (m r : ℕ) (h : r < 4) : p (4*m+r) = 2*m+2+2*(r/3) := by
    unfold p
    omega
  intro n _
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4*m+r := ⟨n/4, n%4, by omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := K m
  rw [P m r hr]
  interval_cases r <;> simp [q, pow_two, add_assoc, *] <;> omega
