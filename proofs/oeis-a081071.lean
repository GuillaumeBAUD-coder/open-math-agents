import OMAStatements.S_oeis_a081071
import Mathlib

namespace OMA.A081071Proof

open OMA.S_oeis_a081071

theorem lucas_succ (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lucas]
    | 1 => simp [lucas, Nat.fib_add_two]
    | m + 2 =>
      rw [show m + 2 + 1 = (m + 1) + 2 by ring, lucas, ih (m + 1) (by omega), ih m (by omega)]
      simp only [Nat.fib_add_two]
      ring

theorem sum_fib (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc 2 m, Nat.fib (2 * k)) + 2 = Nat.fib (2 * m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => simp [Nat.fib_add_two]
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Nat.fib_add_two,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    omega

end OMA.A081071Proof

open OMA.A081071Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  have h1 := sum_fib (2 * n) (by omega)
  have h2 := lucas_succ (4 * n + 1)
  unfold OMA.S_oeis_a081071.a
  rw [show 4 * n + 1 + 1 = 4 * n + 2 by ring] at h2
  rw [h2, show 4 * n + 1 + 2 = 4 * n + 3 by ring]
  rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at h1
  omega
