import FormalConjectures.ErdosProblems.«1052»

-- Reduction Erdos1052.erdos_1052.R3 of Erdős Problem 1052
-- Credit: @Salofe

/-!
# Erdős 1052: finiteness for bounded 2-adic valuation, and the bound

A number `n` is unitary perfect when the sum of its unitary divisors is `2 n`, that is
`∏ (1 + q) = 2 n` over the prime powers `q` exactly dividing `n`.

* `H1` (the theorem of Subbarao and Warren, 1966): for every `A` only finitely many unitary
  perfect numbers have 2-adic valuation at most `A`. Reason: if `n = 2 ^ a * m` with `m` odd,
  every odd prime power `q` exactly dividing `n` makes `1 + q` even, so `m` has at most `a + 1`
  prime factors; and an equation `∏ (1 + 1 / q_i) = 2` in a bounded number of unknowns has only
  finitely many solutions.
* `H2` (the open core): the 2-adic valuation of unitary perfect numbers is bounded.
-/

namespace OMA.R_Erdos1052_erdos_1052_R3

/-- Subbarao and Warren: finitely many unitary perfect numbers below any bound on the exponent
of 2. -/
def H1 : Prop :=
  ∀ A : ℕ, {n : ℕ | Erdos1052.IsUnitaryPerfect n ∧ padicValNat 2 n ≤ A}.Finite

/-- The open core: the exponent of 2 in a unitary perfect number is bounded. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → padicValNat 2 n ≤ A

theorem main : H1 → H2 → type_of% @Erdos1052.erdos_1052 := by
  intro h1 h2
  obtain ⟨A, hA⟩ := h2
  exact (h1 A).subset fun n hn => ⟨hn, hA n hn⟩

end OMA.R_Erdos1052_erdos_1052_R3
