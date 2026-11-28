import Mathlib

/-!
# OEIS A275527: classes of permutations under rotation and complement

Source: https://oeis.org/A275527
Credit: @SudharsanAnimations

A275527(n) is the number of classes of permutations of length `n`, two permutations being equivalent
if one is obtained from the other by a cyclic rotation (12345 -> 23451, ...), by the complement to
`n + 1` (31254 -> 35412), or by a combination of the two. The entry conjectured
`a(n) = (n - 1)!/2` for odd `n` and `a(n) = (n - 2)!! (1 + (n - 1)!!)/2` for even `n`, and Martin
Fuller recorded (Dec 2025) that the conjectured formula is correct for `n > 1`. We state this
proved result.

Conventions: a permutation is `σ : Equiv.Perm (Fin n)`, read as the word `σ 0, ..., σ (n-1)` with
values `0, ..., n-1` standing for `1, ..., n`; rotation by `k` is `i ↦ σ (i + k)` (indices mod `n`)
and the complement is `Fin.rev` on values. `a n` counts the distinct equivalence classes; `‼` is
the double factorial and `/` is natural-number division (exact here).
-/

namespace OMA.S_oeis_a275527

open Nat

/-- Two permutations of length `n` (written `σ 0, …, σ (n-1)`, values `0, …, n-1` standing for
`1, …, n`) are equivalent if one is obtained from the other by a cyclic rotation
(`τ i = σ (i + k)`, indices mod `n`), possibly combined with the complement to `n + 1`
(`v ↦ n + 1 - v`, i.e. `Fin.rev` on the values). -/
def Equivalent {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∃ k : Fin n, ∃ c : Bool, ∀ i : Fin n, τ i = (if c then Fin.rev (σ (i + k)) else σ (i + k))

open Classical in
/-- A275527(n): the number of equivalence classes. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).image
    (fun σ => Finset.univ.filter (fun τ => Equivalent σ τ))).card

theorem main : ∀ n : ℕ, 1 < n →
    (Odd n → a n = (n - 1)! / 2) ∧ (Even n → a n = (n - 2)‼ * (1 + (n - 1)‼) / 2) := by
  sorry

end OMA.S_oeis_a275527
