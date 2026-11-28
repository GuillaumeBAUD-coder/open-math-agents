import Mathlib

/-!
# Verifying a combinatorial inequality

Source: https://mathoverflow.net/questions/140259 (CC BY-SA 4.0).

Let `n ≥ 2` and let `μ_1, …, μ_n, γ_1, …, γ_n` be distinct positive reals with `γ_1 < ⋯ < γ_n`. The
asker conjectures
`f(μ, γ) = ∑_{v ∈ {-1,1}^n} ∏_{i=2}^n ∏_{j=1}^{i-1} (v_i γ_i - v_j γ_j) · ∏_{i,j} (μ_i + v_j γ_j) · 2^(v·γ) > 0`
(proved for `n = 2` and when all `μ`'s exceed all `γ`'s).

We state the conjecture.

Formalization notes:
* Indices run over `Fin n`; a sign vector is `v : Fin n → Bool`, read as `±1` by `s`.
* "Distinct" for all `2n` numbers: `μ` is injective, `γ` is strictly increasing, and `μ i ≠ γ j`.
* `2^(v·γ)` is the real power `(2 : ℝ) ^ (∑ j, v_j γ_j)`.
* Checked exactly (rationals) on 400 random integer instances with `n = 2, 3, 4`: always positive.
-/

namespace OMA.S_mo_140259

/-- The alternating sum `f(μ, γ)` is positive. -/
theorem main :
    ∀ (n : ℕ) (hn : 2 ≤ n) (μ γ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) (hγ : ∀ i, 0 < γ i)
      (hγmono : StrictMono γ) (hμinj : Function.Injective μ) (hμγ : ∀ i j, μ i ≠ γ j),
    let s : Bool → ℝ := fun b => if b then 1 else -1
    0 < ∑ v : Fin n → Bool,
      (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => j < i), (s (v i) * γ i - s (v j) * γ j)) *
        (∏ i : Fin n, ∏ j : Fin n, (μ i + s (v j) * γ j)) *
        (2 : ℝ) ^ (∑ j : Fin n, s (v j) * γ j) := by
  sorry

end OMA.S_mo_140259
