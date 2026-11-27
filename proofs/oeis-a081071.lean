import OMAStatements.S_oeis_a081071

-- Problem: oeis-a081071
-- Credit: @anmolspace
-- Proof: lucas (n+1) = fib n + fib (n+2) (paired induction) and
-- (∑_{k=2}^{m} fib (2k)) + 2 = fib (2m+1) for m ≥ 1 (induction); combine with omega.

namespace OMA.P081071
open OMA.S_oeis_a081071

lemma lucas_pair (n : ℕ) :
    lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) ∧
      lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := by
  induction n with
  | zero => simp [lucas, Nat.fib_add_two]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    have e : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    have f2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have f3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [e, ih.1, ih.2]
    omega

lemma sum_even2 (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc 2 m, Nat.fib (2 * k)) + 2 = Nat.fib (2 * m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have f : Nat.fib (2 * m + 1 + 2) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 1 + 1) :=
      Nat.fib_add_two
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    omega

end OMA.P081071

theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  have hL := (OMA.P081071.lucas_pair (4 * n + 1)).1
  rw [show 4 * n + 1 + 1 = 4 * n + 2 by ring, show 4 * n + 1 + 2 = 4 * n + 3 by ring] at hL
  have hS := OMA.P081071.sum_even2 (2 * n) (by omega)
  rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hS
  simp only [OMA.S_oeis_a081071.a]
  omega
