import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.NormNum

/-!
# OEIS A395149: the alternating row sums of index 2n stated in the entry

Source: https://oeis.org/A395149, revision 20 (April 27, 2026), F. Chapoton.
Row d of the triangle lists, in increasing degree, the coefficients of the
characteristic polynomial of the d x d matrix with entries -C(i+j+2, j) for
0 <= i, j < d, rows numbered from 0 as in the entry's SageMath code. The entry
states as a conjecture: the alternating row sum of index 2n is
A266091(n)^4 / 3^(2*n) / (2*n+1), for example 1 - 76 + 275 - 76 + 1 =
15^4 / 3^4 / 5. Conventions: the alternating sum of row 2n, starting with a
plus sign, is the characteristic polynomial evaluated at -1 (the degree 2n is
even); A266091(n) = Product_{k=0..n} (3*k)!/(n+k)!; the claim is stated for
every n >= 0.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Sol and other OpenAI models, checked with Claude.
-/

open scoped BigOperators

namespace OMA.S_oeis_a395149

/-- A395149 has matrix dimension d in row d and zero-based entry indices. -/
def negativePascal (d : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j => -(Nat.choose (i.val + j.val + 2) j.val : ℚ)

/-- Evaluation at -1 is the alternating sum of the coefficients in increasing degree. -/
noncomputable def alternatingRowSum (n : ℕ) : ℚ :=
  (negativePascal (2 * n)).charpoly.eval (-1)

/-- The defining factorial product in OEIS A266091. -/
def a266091 (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range (n + 1), (Nat.factorial (3 * k) : ℚ) / Nat.factorial (n + k)

def conjecturedValue (n : ℕ) : ℚ :=
  a266091 n ^ 4 / (3 : ℚ) ^ (2 * n) / (2 * (n : ℚ) + 1)

theorem main : ∀ n : ℕ, alternatingRowSum n = conjecturedValue n := by
  sorry

end OMA.S_oeis_a395149
