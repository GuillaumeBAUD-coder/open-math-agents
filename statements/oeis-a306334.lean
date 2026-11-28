import Mathlib

/-!
# A306334: a(n) is the number of different linear hydrocarbon molecules with n carbon atoms.

Source: https://oeis.org/A306334
Credit: @xor2k

Vaclav Kotesovec (Feb 12 2019), in the formula section of A306334:
  Conjectures:
  a(n) = 2*a(n-1) + 3*a(n-2) - 5*a(n-3) - a(n-4) - 2*a(n-6) + 3*a(n-7) + a(n-8) - a(n-9), for n >= 10.
  G.f.: (1 - x - 2*x^2 - x^4 + 2*x^5 + x^6 - x^7) / ((1 - 2*x - x^2 + x^3)*(1 - 2*x^2 - x^4 + x^6)) - 1.
(The catalogue row is the comment of Petros Hadjicostas, Nov 16 2019, which proves these two
conjectures by the Cayley-Hamilton theorem. Both conjectures are stated here, as one conjunction.)

Conventions:
* A linear hydrocarbon molecule with n carbon atoms is a chain C_1 - C_2 - ... - C_n of carbon
  atoms in which consecutive atoms C_i, C_(i+1) are joined by a single, double or triple bond; the
  remaining valences are filled with hydrogen atoms. Since carbon has valence 4, the molecule
  exists exactly if the two bonds at each inner carbon atom have orders summing to at most 4.
  So a molecule is given by its list of bond orders (b_1, ..., b_(n-1)), each b_i in {1, 2, 3},
  with b_i + b_(i+1) ≤ 4 for consecutive bonds (`Valid`), and a list and its reversal describe
  the same molecule (the chain read from the other end). Examples of the entry: n = 2 gives
  CH3CH3, CH2CH2, CHCH (lists [1], [2], [3]); n = 3 gives CH3CH2CH3, CH3CHCH2, CH2CCH2, CHCCH3
  (lists [1,1], [1,2] ~ [2,1], [2,2], [1,3] ~ [3,1]).
* `a n` is the number of classes of valid lists of length n - 1 under the relation
  `l ~ l'` iff `l' = l` or `l' = l.reverse` (which is an equivalence relation): the cardinality of
  the quotient `Quot`. Offset 1; the value `a 0` (natural subtraction: lists of length 0) is not
  used by the statement.
* The recurrence is stated in ℤ for every n ≥ 10.
* The g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1
  (offset 1), as an identity of formal power series over ℚ with the denominator multiplied out:
  (∑ a(n) X^n + 1) * denominator = numerator.

Numerical check: a Python copy of the definition (brute force over all lists, classes under
reversal) gives 1, 3, 4, 10, 18, 42, 84, 192, 409, 926, 2030, 4577, 10171, 22889, 51176, 115070,
257987, 579868, 1301664, 2925209 for n = 1..20; compared with DATA: identical for the first 20
terms.
-/

namespace OMA.S_oeis_a306334

/-- A list of bond orders of a linear hydrocarbon: every bond is single, double or triple, and
two consecutive bonds (meeting in a carbon atom of valence 4) have orders summing to at most 4. -/
def Valid (l : List ℕ) : Prop :=
  (∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3) ∧ l.IsChain (fun x y => x + y ≤ 4)

/-- The bond lists of the chains with n carbon atoms (n - 1 bonds). -/
def Chains (n : ℕ) : Type := {l : List ℕ // l.length = n - 1 ∧ Valid l}

/-- Two bond lists describe the same molecule iff they are equal or reverses of each other. -/
def Same (n : ℕ) (l l' : Chains n) : Prop := l'.1 = l.1 ∨ l'.1 = l.1.reverse

/-- A306334 (offset 1): the number of linear hydrocarbon molecules with n carbon atoms. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (Same n))

/-- Kotesovec's conjectures: the recurrence for n ≥ 10 and the rational g.f. -/
theorem main : (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 5 * a (n - 3)
      - a (n - 4) - 2 * a (n - 6) + 3 * a (n - 7) + a (n - 8) - a (n - 9)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) + 1) *
        ((1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
          (1 - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4 + PowerSeries.X ^ 6)) =
      1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5
        + PowerSeries.X ^ 6 - PowerSeries.X ^ 7 := by
  sorry

end OMA.S_oeis_a306334
