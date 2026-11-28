import OMAReductions.R_Erdos865_erdos_865_variants_sos_R1

/-!
# Reduction of step Erdos865.erdos_865.variants.sos.R1.H2

The step is the Erdős–Sós upper bound for every `k ≥ 4`: for each `ε > 0` and all large `N`,
every `A ⊆ [1, N]` with `|A| ≥ (c_k + ε) N` contains `k` elements whose pairwise sums lie in `A`,
where `c_k = (1/2) (1 + ∑_{1 ≤ r ≤ k-2} 4^{-r})`.

This file splits it by induction on `k`:
* the first case `k = 4`, where `c_4 = 21/32`;
* the induction step: for every `k ≥ 4`, the bound for `k` implies the bound for `k + 1`.
-/

-- Reduction Erdos865.erdos_865.variants.sos.R1.H2.R1 of step Erdos865.erdos_865.variants.sos.R1.H2

namespace OMA.R_Erdos865_erdos_865_variants_sos_R1_H2_R1

open Filter Finset

/-- The first case, `k = 4`: the constant is `21/32`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
    ∀ A ⊆ Icc 1 N,
      ((1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (4 - 2), (1 / 4 : ℝ) ^ r) + ε) * N ≤ A.card →
      ∃ S ⊆ A, S.card = 4 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A

/-- The induction step from `k` to `k + 1`, for every `k ≥ 4`. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N,
        ((1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (k - 2), (1 / 4 : ℝ) ^ r) + ε) * N ≤ A.card →
        ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N,
        ((1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (k + 1 - 2), (1 / 4 : ℝ) ^ r) + ε) * N ≤ A.card →
        ∃ S ⊆ A, S.card = k + 1 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A)

theorem main : H1 → H2 → OMA.R_Erdos865_erdos_865_variants_sos_R1.H2 := by
  intro h1 h2 k hk
  induction k, hk using Nat.le_induction with
  | base => exact h1
  | succ n hn ih => exact h2 n hn ih

end OMA.R_Erdos865_erdos_865_variants_sos_R1_H2_R1
