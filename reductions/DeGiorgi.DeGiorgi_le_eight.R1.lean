import FormalConjectures.Paper.DeGiorgi

/-!
# Reduction of De Giorgi's conjecture in the sharp range `n ≤ 8`

`DeGiorgi.DeGiorgi_le_eight` states that De Giorgi's conjecture holds in every dimension `n ≤ 8`.
The literature proves `n = 1` (trivial), `n = 2` (Ghoussoub–Gui), `n = 3` (Ambrosio–Cabré) and
`4 ≤ n ≤ 8` under an extra hypothesis (Savin); the cases `4 ≤ n ≤ 8` without that hypothesis are
open, so dimension `8` is the top open case.

What is proved here (not assumed) is the **downward induction** that turns one solution of the
conjecture in the top dimension into all the smaller ones. The mechanism is the *vertical
extension*: given `u : ℝⁿ → ℝ` put `ũ(x, t) := u x`. Then `ũ` is again a bounded classical
solution of `Δũ + ũ - ũ³ = 0` (it does not depend on the last coordinate, so `Δũ = Δu` along the
first `n` coordinates and the extra coordinate contributes nothing), `∂₁ũ = ∂₁u > 0`, and its
level sets are `u⁻¹{y} × ℝ`. Hence hyperplane level sets for `ũ` (an affine subspace of dimension
`(n+1) - 1 = n` in `ℝⁿ⁺¹`) imply hyperplane level sets for `u`: intersect with the hyperplane
`t = 0`, which is transverse to the direction of `u⁻¹{y} × ℝ` (that set is invariant under the
translation `t ↦ t + s`, so its direction contains the last coordinate axis), and a dimension
count `n = (n+1) - 1` in `ℝⁿ⁺¹` gives dimension `n - 1` for `u⁻¹{y}`. Consequently

  `DeGiorgi_conclusion (n+1) → DeGiorgi_conclusion n`   (the *descent step*, `H2` below).

That descent step is mathematically true; it is isolated as `H2` because its analytic core
(`Δ` of an extension by constancy, and the affine-subspace dimension count) is not yet formalized.
`H1` is De Giorgi's conjecture in dimension `8` — the honest open core, since a proof of `H1`
combined with the descent step settles every `n ≤ 8`, and `n = 8` is the largest open case.

So this file reduces `DeGiorgi_le_eight` to two ingredients: the conjecture in dimension `8`
(`H1`), and the extension/descent mechanism (`H2`).
-/

namespace OMA.R_DeGiorgi_DeGiorgi_le_eight_R1

/-- H1: De Giorgi's conjecture in the top open dimension `8`: every bounded classical solution of
`Δu + u - u³ = 0` on `ℝ⁸` with `∂₁u > 0` has hyperplane level sets. -/
def H1 : Prop := ∀ [NeZero 8], DeGiorgi.DeGiorgi_conclusion 8

/-- H2: the descent (vertical extension) step. If De Giorgi's conclusion holds in dimension
`k + 1`, it holds in dimension `k`: extend `u : ℝᵏ → ℝ` to `ũ : ℝᵏ⁺¹ → ℝ` by `ũ(x, t) = u x`,
which is again a bounded solution with positive first derivative and whose level sets are
`u⁻¹{y} × ℝ`, and read off the hyperplane structure of `u⁻¹{y}` by intersecting with `t = 0`. -/
def H2 : Prop :=
  ∀ k : ℕ, (∀ [NeZero (k + 1)], DeGiorgi.DeGiorgi_conclusion (k + 1)) →
    (∀ [NeZero k], DeGiorgi.DeGiorgi_conclusion k)

/-- Downward induction: from the conclusion in dimension `8` we get the conclusion in every
dimension `m ≤ 8` by applying the descent step `8 - m` times. -/
theorem desc (h2 : H2) {m : ℕ} (hm : m ≤ 8)
    (h8 : ∀ [NeZero 8], DeGiorgi.DeGiorgi_conclusion 8) :
    ∀ [NeZero m], DeGiorgi.DeGiorgi_conclusion m :=
  Nat.decreasingInduction' (P := fun k => ∀ [NeZero k], DeGiorgi.DeGiorgi_conclusion k)
    (fun k _ _ hk => h2 k hk) hm h8

/-- The descent step together with De Giorgi's conjecture in dimension `8` gives De Giorgi's
conjecture in every dimension `n ≤ 8`. -/
theorem main : H1 → H2 → type_of% @DeGiorgi.DeGiorgi_le_eight := by
  intro h1 h2 n _hn hn8
  exact desc h2 hn8 h1

end OMA.R_DeGiorgi_DeGiorgi_le_eight_R1
