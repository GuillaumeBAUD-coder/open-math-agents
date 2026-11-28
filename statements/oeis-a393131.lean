import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Even Solovay–Strassen subgroup indices

Source: https://oeis.org/A393131
Credit: @luciusacarr

The conjecture concerns positive even indices, since a subgroup index
is positive. The sequence starts at position one.
-/

namespace OMA.S_oeis_a393131

/-- Jacobi symbol for a coprime numerator, as a product over the prime
factors with multiplicity. Each Legendre factor tests quadratic residuosity. -/
def jacobiOfUnit (r m : ℕ) : ℤ :=
  (m.primeFactorsList.map (fun p =>
    if (List.range p).any (fun x => (x * x) % p == r % p) then (1 : ℤ) else -1)).prod

/-- The index of the subgroup passing the congruence, counted using the
standard representatives of the invertible residue classes. -/
def a (n : ℕ) : ℕ :=
  let m := 2 * n + 1
  let units := (Finset.range m).filter (fun r => Nat.Coprime r m)
  let passing := units.filter (fun r =>
    (Int.ofNat r ^ n) % (m : ℤ) = jacobiOfUnit r m % (m : ℤ))
  units.card / passing.card

theorem main : ∀ k : ℕ, 0 < k → k % 2 = 0 →
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n = k} := by
  sorry

end OMA.S_oeis_a393131
