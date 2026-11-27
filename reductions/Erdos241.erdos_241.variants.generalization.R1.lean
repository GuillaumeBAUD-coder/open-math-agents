import FormalConjectures.ErdosProblems.«241»

-- Reduction Erdos241.erdos_241.variants.generalization.R1 of Erdős Problem 241 — generalization
-- Credit: @Sathy-21
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Bose–Chowla conjecture: split into the lower and the upper bound

The target says `f N r ~ N^(1/r)` for every `r ≥ 2`. It is split into its two halves, stated in the
same `(1 + o(1))` form the upstream file uses for `r = 3` (`erdos_241.variants.lower_bound`):

* `H1`, the lower bound `(1 + o(1)) N^(1/r) ≤ f N r`. This is known for every `r`: it follows from
  the Bose–Chowla construction [BoCh62] (`B_r` sets of size `q` modulo `q^r - 1` for prime powers
  `q`) together with a prime-gap argument to pass from `q^r` to all `N`.
* `H2`, the upper bound `f N r ≤ (1 + o(1)) N^(1/r)`. This is the open direction: for `r = 3` the
  best known constant is about `1.5155` (White 2024), not `1`.

`main` is the squeeze: `ε₁ v ≤ f - v ≤ ε₂ v` gives `|f - v| ≤ max |εᵢ| · v = o(v)`.
-/

namespace OMA.R_Erdos241_erdos_241_variants_generalization_R1

open Filter Asymptotics

/-- Lower bound: for every `r ≥ 2`, `(1 + o(1)) N^(1/r) ≤ f N r`. -/
def H1 : Prop := ∀ r : ℕ, 2 ≤ r → ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ N in atTop, (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / r) ≤ (Erdos241.f N r : ℝ)

/-- Upper bound: for every `r ≥ 2`, `f N r ≤ (1 + o(1)) N^(1/r)`. -/
def H2 : Prop := ∀ r : ℕ, 2 ≤ r → ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ N in atTop, (Erdos241.f N r : ℝ) ≤ (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / r)

theorem main : H1 → H2 → type_of% @Erdos241.erdos_241.variants.generalization := by
  intro h1 h2 r hr
  obtain ⟨e₁, he₁, hlow⟩ := h1 r hr
  obtain ⟨e₂, he₂, hupp⟩ := h2 r hr
  unfold Erdos241.BoseChowlaConjecture IsEquivalent
  refine IsLittleO.of_bound (fun c hc => ?_)
  filter_upwards [he₁.bound hc, he₂.bound hc, hlow, hupp] with N b₁ b₂ l u
  simp only [norm_one, mul_one, Real.norm_eq_abs] at b₁ b₂
  have hv : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / r) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv, Pi.sub_apply, abs_sub_le_iff]
  obtain ⟨b₁l, b₁u⟩ := abs_le.mp b₁
  obtain ⟨b₂l, b₂u⟩ := abs_le.mp b₂
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right b₂u hv, mul_le_mul_of_nonneg_right b₁l hv]

end OMA.R_Erdos241_erdos_241_variants_generalization_R1
