import Mathlib

/-!
# A181901: least modulus separating 2(s_k)^2 for alternating prime sums (Sun's conjecture)

Source: https://oeis.org/A181901 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A181901 (offset 1): a(n) = least positive integer m such that 2(s_k)^2 for k=1,...,n are
pairwise distinct modulo m, where s_k = Sum_{j=1..k} (-1)^(k-j)*p_j and p_j is the j-th prime;
data 1, 4, 7, 9, 13, 17, 19, 23, 25, 31, ...

The entry records (Zhi-Wei Sun, Mar 28 2012):

  Zhi-Wei Sun conjectured that a(n) is the (n+1)-th prime p_{n+1} with the only exceptions
  being a(1)=1, a(2)=4, a(4)=9 and a(9)=25. He has shown that 2(s_k)^2 (k=1,...,n) are indeed
  pairwise distinct modulo p_{n+1} and hence a(n) does not exceed p_{n+1}.

Reading of the source:
* `p j` is the `j`-th prime with `p 1 = 2` (`Nat.nth Nat.Prime (j - 1)`), and
  `s k = ∑_{j=1}^{k} (-1)^(k-j) p_j` is an integer.
* "pairwise distinct modulo m": for `1 ≤ i < k ≤ n`, `2 s_i^2` and `2 s_k^2` are not congruent
  modulo `m`. `a n` is the least positive such `m` (it exists: any `m` larger than all the
  values works).
* The conjecture: for every `n ≥ 1`, `a n = p (n + 1)`, except `a 1 = 1`, `a 2 = 4`, `a 4 = 9`
  and `a 9 = 25`. (The listed exceptional values are part of the statement.)
-/

namespace OMA.S_oeis_a181901

/-- `p j`: the `j`-th prime, with `p 1 = 2`. -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

/-- `s_k = ∑_{j=1}^{k} (-1)^(k-j) p_j`. -/
noncomputable def s (k : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 k, (-1) ^ (k - j) * (p j : ℤ)

/-- `m` separates `2 s_1^2, ..., 2 s_n^2`: they are pairwise distinct modulo `m`. -/
def Separates (n m : ℕ) : Prop :=
  ∀ i k : ℕ, 1 ≤ i → i < k → k ≤ n → ¬ (2 * s i ^ 2 ≡ 2 * s k ^ 2 [ZMOD (m : ℤ)])

/-- A181901(n): the least positive `m` that separates `2 s_1^2, ..., 2 s_n^2`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ Separates n m}

/-- Sun's conjecture: `a(n) = p_(n+1)` except `a(1) = 1`, `a(2) = 4`, `a(4) = 9`, `a(9) = 25`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = if n = 1 then 1 else if n = 2 then 4 else if n = 4 then 9 else if n = 9 then 25
      else p (n + 1) := by
  sorry

end OMA.S_oeis_a181901
