import Mathlib

/-!
# Inequality of a concave function

Source: https://mathoverflow.net/questions/253925
Credit: @zarnab222-dev

For a concave `G : ℝ → ℝ` put `G_ε(x) := max_{y ∈ [x-ε, x+ε]} G(y)`. The question asks whether there
is some `h : ℝ → ℝ` with `G_ε(x) + h(x)(y-x) - ε|h(x)| ≥ G(y)` for all real `x, y`. The affirmative
claim is stated, for every concave `G` and every admissible `ε`; `h` may depend on `G` and `ε`.

Translation choices:
* concave on the whole line: `ConcaveOn ℝ Set.univ G`;
* `G_ε(x)` is `Geps G ε x`, the supremum `sSup` of the image of `[x-ε, x+ε]` under `G`. A concave
  function on `ℝ` is continuous, so for a nonempty interval this supremum is attained and is the
  maximum of the source;
* the source leaves the range of `ε` implicit. The interval `[x-ε, x+ε]` is nonempty, so that the
  maximum exists, exactly when `0 ≤ ε`; that is the hypothesis used (it contains the case `ε > 0`).
-/

namespace OMA.S_mo_253925

/-- `Geps G ε x` is `G_ε(x) = max_{y ∈ [x-ε, x+ε]} G(y)`. -/
noncomputable def Geps (G : ℝ → ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  sSup (G '' Set.Icc (x - ε) (x + ε))

theorem main :
    ∀ (G : ℝ → ℝ) (ε : ℝ), ConcaveOn ℝ Set.univ G → 0 ≤ ε →
      ∃ h : ℝ → ℝ, ∀ x y : ℝ,
        Geps G ε x + h x * (y - x) - ε * |h x| ≥ G y := by
  sorry

end OMA.S_mo_253925
