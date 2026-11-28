import FormalConjectures.ErdosProblems.«556»

-- Reduction Erdos556.erdos_556.variants.kss_large_odd.R1 of Erdős Problem 556 — kss large odd
-- Credit: @rodriveiga01
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Splitting $R(C_n;3) = 4n-3$ (odd $n$) into its two inequalities

The theorem of Kohayakawa, Simonovits and Skokan for large odd $n$ is an equality of natural
numbers, and the two directions come from completely different arguments:

* `H1` is the construction side: a 3-colouring of the edges of `K_{4n-4}` with no monochromatic
  `C_n`, which gives the lower bound $4n-3 \le R(C_n;3)$. It needs the explicit colouring.
* `H2` is the Ramsey side: every 3-colouring of `K_{4n-3}` contains a monochromatic `C_n`. It
  needs the (much harder) embedding argument.

`main` assembles the equality from the two bounds by antisymmetry.
-/

namespace OMA.R_Erdos556_erdos_556_variants_kss_large_odd_R1

open Filter SimpleGraph Erdos556

/-- Lower bound: for all sufficiently large odd `n`, a 3-colouring of `K_{4n-4}` avoids
monochromatic cycles, so `4 * n - 3 ≤ R(C_n;3)`. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, Odd n → 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

/-- Upper bound: for all sufficiently large odd `n`, every 3-colouring of `K_{4n-3}` has a
monochromatic `C_n`, so `R(C_n;3) ≤ 4 * n - 3`. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, Odd n → multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.kss_large_odd := by
  intro lower upper
  filter_upwards [lower, upper] with n hlow hup hodd
  exact le_antisymm (hup hodd) (hlow hodd)

end OMA.R_Erdos556_erdos_556_variants_kss_large_odd_R1
