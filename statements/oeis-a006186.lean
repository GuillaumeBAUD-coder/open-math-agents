import Mathlib.Data.Finset.Card
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a006186

/-- An exact pair-covering (linear space) of `Fin v` with largest block size `4` is a family `B`
of subsets of `Fin v` such that every block has size `2 ≤ |b| ≤ 4`, at least one block has
size `4`, and every pair of distinct elements of `Fin v` is contained in a unique block of `B`. -/
def IsExactPairCoveringMax4 (v : ℕ) (B : Finset (Finset (Fin v))) : Prop :=
  (∀ b ∈ B, 2 ≤ b.card ∧ b.card ≤ 4) ∧
  (∃ b ∈ B, b.card = 4) ∧
  (∀ x y : Fin v, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b)

/-- OEIS A006186(v) (offset 4): the Stanton-Allston-Cowan covering number `g^(4)(v)`, i.e. the
minimum number of blocks in an exact pair-covering of `Fin v` with largest block size `4`
(`a(4)=1, a(5)=5, a(6)=8, a(7)=10, a(8)=11, a(9)=12, a(10)=12, a(11)=13, ...`). -/
noncomputable def a006186 (v : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ B : Finset (Finset (Fin v)), IsExactPairCoveringMax4 v B ∧ B.card = m }

/-- Conjecture (Simon Plouffe, 1992; OEIS A006186): The ordinary generating function of
`a006186(n + 4)` (`n ≥ 0`) equals `(1 + 5*z + 6*z^2 + z^3) / ((z - 1) * (z^2 - z - 1))`,
i.e. `((X - 1) * (X^2 - X - 1)) * (∑_{n ≥ 0} a006186(n + 4) * X^n) = 1 + 5*X + 6*X^2 + X^3`
in `ℤ⟦X⟧`. -/
theorem main :
    ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 - PowerSeries.X - 1)) *
      PowerSeries.mk (fun n => (a006186 (n + 4) : ℤ)) =
      (1 : PowerSeries ℤ) + 5 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
  sorry

end OMA.S_oeis_a006186
