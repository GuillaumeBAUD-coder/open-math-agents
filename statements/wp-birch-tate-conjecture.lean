import Mathlib

/-!
# Birch–Tate conjecture

Source: https://en.wikipedia.org/wiki/Birch–Tate_conjecture
Credit: @iancbaer

Let `F` be a totally real number field with ring of integers `O`, and let `K₂(O)` be the centre
of the Steinberg group `St(O)` (Milnor's `K₂`, here the tame kernel of `F`). Let `N` be the largest
natural number such that the extension of `F` by the `N`-th roots of unity has an elementary
abelian `2`-group as its Galois group. The conjecture states that

  `#K₂(O) = |N ζ_F(-1)|`,

where `ζ_F` is the Dedekind zeta function of `F`.

Formalization notes.
* `St(R)` is the stable Steinberg group: generators `x i j r` for natural numbers `i ≠ j` and
  `r : R`, with relations `x i j r * x i j s = x i j (r + s)`; `[x i j r, x k l s] = 1` when
  `j ≠ k` and `i ≠ l`; and `[x i j r, x j k s] = x i k (r * s)` for distinct `i, j, k`, where
  `[a, b] = a b a⁻¹ b⁻¹`. The generating set used below is all triples `(i, j, r)`, and the
  generators with `i = j` are set equal to `1`, which gives the same group.
* `K₂(O)` is the centre of `St(O)` (Milnor, Introduction to algebraic K-theory, Theorem 5.1).
* A group is an elementary abelian `2`-group exactly when every element squares to `1`. The set
  of admissible `N` is finite for a number field, so its supremum is its largest element.
* The value `ζ_F(-1)` needs the analytic continuation, which is not constructed here: `main`
  quantifies over every function `Z` holomorphic on `ℂ ∖ {1}` that agrees with the Dedekind zeta
  series `∑ N(I)^(-s)` (over the nonzero ideals `I` of `O`) for `Re s > 1`. Such a `Z` exists and
  is unique, so `Z (-1) = ζ_F(-1)`.
* `Nat.card` of an infinite group is `0`, while `ζ_F(-1) ≠ 0` for totally real `F`, so the
  equality also asserts that `K₂(O)` is finite.
-/

namespace OMA.S_wp_birch_tate_conjecture

open NumberField FreeGroup

/-- The defining relations of the stable Steinberg group of `R`. -/
def steinbergRels (R : Type) [Ring R] : Set (FreeGroup (ℕ × ℕ × R)) :=
  {g | (∃ (i : ℕ) (r : R), g = of (i, i, r)) ∨
    (∃ (i j : ℕ) (r s : R), i ≠ j ∧ g = of (i, j, r) * of (i, j, s) * (of (i, j, r + s))⁻¹) ∨
    (∃ (i j k l : ℕ) (r s : R), i ≠ j ∧ k ≠ l ∧ j ≠ k ∧ i ≠ l ∧
      g = of (i, j, r) * of (k, l, s) * (of (i, j, r))⁻¹ * (of (k, l, s))⁻¹) ∨
    (∃ (i j k : ℕ) (r s : R), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      g = of (i, j, r) * of (j, k, s) * (of (i, j, r))⁻¹ * (of (j, k, s))⁻¹ *
        (of (i, k, r * s))⁻¹)}

/-- The stable Steinberg group `St(R)`. -/
abbrev Steinberg (R : Type) [Ring R] : Type := PresentedGroup (steinbergRels R)

/-- The largest `N` such that `Gal(F(ζ_N)/F)` is an elementary abelian `2`-group. -/
noncomputable def w₂ (F : Type) [Field F] : ℕ :=
  sSup {N : ℕ | 0 < N ∧ ∀ (L : Type) [Field L] [Algebra F L] [IsCyclotomicExtension {N} F L]
    (σ : L ≃ₐ[F] L), σ * σ = 1}

/-- The Dedekind zeta series of `F`, for `Re s > 1`. -/
noncomputable def zetaSeries (F : Type) [Field F] [NumberField F] (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℂ) ^ (-s)

theorem main :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Z : ℂ → ℂ),
      DifferentiableOn ℂ Z {s : ℂ | s ≠ 1} →
      (∀ s : ℂ, 1 < s.re → Z s = zetaSeries F s) →
      (Nat.card (Subgroup.center (Steinberg (𝓞 F))) : ℝ) = (w₂ F : ℝ) * ‖Z (-1)‖ := by
  sorry

end OMA.S_wp_birch_tate_conjecture
