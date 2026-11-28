import Mathlib

/-!
# OEIS A264185: (n+1) x 4 arrays of permutations with index change ±(0,0), ±(1,-1), or ±(2,2)

Source: https://oeis.org/A264185
Credit: @ceejcake

Offset 1: for n ≥ 1, `a n` is the number of permutations of an `(n + 1) × 4` grid
in which every element moves by `(0, 0)`, `±(1, -1)`, or `±(2, 2)`.
For the ordinary generating function (offset 1), we set `a 0 = 0`.

Conjectures listed in OEIS (empirical recurrence by R. H. Hardin; g.f. and closed form
by Colin Barker, Jan 05 2019):
- `a(n) = 10 * a(n - 1)` for `n > 4`.
- `a(n) = 441 * 2^n * 5^(n - 4)` for `n > 3`.
- G.f.: `x * (8 + x - 90*x^2 - 144*x^3) / (1 - 10*x)`.
-/

namespace OMA.S_oeis_a264185

/-- Allowed displacement between a grid cell `p` and its image `q` in an `(n+1) × 4` array. -/
def validMove {n : ℕ} (p q : Fin (n + 1) × Fin 4) : Prop :=
  let dr : ℤ := (q.1.val : ℤ) - (p.1.val : ℤ)
  let dc : ℤ := (q.2.val : ℤ) - (p.2.val : ℤ)
  (dr = 0 ∧ dc = 0) ∨ (dr = 1 ∧ dc = -1) ∨ (dr = -1 ∧ dc = 1) ∨
    (dr = 2 ∧ dc = 2) ∨ (dr = -2 ∧ dc = -2)

instance {n : ℕ} (p q : Fin (n + 1) × Fin 4) : Decidable (validMove p q) := by
  unfold validMove; infer_instance

/-- OEIS A264185(n) for n ≥ 1, with `a 0 = 0` for the offset-1 generating function. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {σ : Equiv.Perm (Fin (n + 1) × Fin 4) // ∀ p, validMove p (σ p)}

theorem main :
    (∀ n : ℕ, 4 < n → a n = 10 * a (n - 1)) ∧
    (∀ n : ℕ, 3 < n → a n = 441 * 2 ^ n * 5 ^ (n - 4)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk (fun n => (a n : ℤ)) * (1 - 10 * X) =
       X * (8 + X - 90 * X ^ 2 - 144 * X ^ 3)) := by
  sorry

end OMA.S_oeis_a264185
