import Mathlib

/-!
# OEIS A273310: Blomberg's other rules and closed form and Barker's recurrence and g.f. for Rule 641

Source: https://oeis.org/A273310 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273310 (Robert Price, May 19 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 641, based on the 5-celled von
Neumann neighborhood.
Formula section:
Conjecture: Rules 649, 897 and 905 also generate this sequence. - Lars Blomberg, Jul 17 2016
Conjecture: a(n) = 4*4^n - 4*2^n - 8, n>1. - Lars Blomberg, Jul 17 2016
Conjectures from Colin Barker, Jul 17 2016:
a(n) = 7*a(n-1)-14*a(n-2)+8*a(n-3) for n>4.
G.f.: (1-3*x+26*x^2-16*x^3-32*x^4) / ((1-x)*(1-2*x)*(1-4*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 641
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Counting convention: a(n) is the number of ON cells of stage 2^n - 1 in the square [-(2^n - 1),
  2^n - 1]^2, as the entry's program counts it (it trims each stage s to the square [-s, s]^2 and
  takes the counts at the stages 2^n - 1).
* Other codes: ruleOf, stateOf and aOf are rule, state and a with the code r in place of 641, so
  rule unfolds to ruleOf 641 and a to aOf 641; a statement that Rule r also generates this sequence
  is stated as aOf r n = a n for every n.
* The statement is the conjunction of the 6 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..2 equal to
  the entry's first 3 terms, 1, 4, 40.
-/

namespace OMA.S_oeis_a273310

open PowerSeries

/-- Rule 641: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 641). -/
def rule (c : Bool) (k : ℕ) : Bool := (641 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A273310(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if state (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

/-- The outer totalistic rule with code `r`: bit `2k + c` of `r`, as `rule` is for this entry. -/
def ruleOf (r : ℕ) (c : Bool) (k : ℕ) : Bool := r.testBit (2 * k + cond c 1 0)

/-- The automaton with code `r` on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateOf (r : ℕ) : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleOf r (stateOf r t p) ((nbrs p).countP (fun q => stateOf r t q))

/-- The same count as `a` for the automaton with code `r`. -/
def aOf (r n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateOf r (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Blomberg's other rules and closed form and Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, aOf 649 n = a n) ∧
    (∀ n : ℕ, aOf 897 n = a n) ∧
    (∀ n : ℕ, aOf 905 n = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 4 * 4 ^ n - 4 * 2 ^ n - 8) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    A = (1 - 3 * X + 26 * X ^ 2 - 16 * X ^ 3 - 32 * X ^ 4) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a273310
