import FormalConjectures.ErdosProblems.«1191»

-- Reduction Erdos1191.erdos_1191.parts.i.R2 of Erdős Problem 1191 — i
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A regular / irregular split of Erdős Problem 1191 (i)

Write `f(x) = |A ∩ [1,x]| ^ 2 * log x / x`. The target asks that `liminf f = 0`
(in rpow-free form: beyond every threshold some `x` has `f(x) ≤ ε ^ 2`).

* `H1` (regular regime): the claim for Sidon sets with `f` bounded on `x ≥ 2`,
  i.e. sets whose counting function is `O(sqrt (x / log x))` at every scale.
* `H2` (irregular regime): the claim for Sidon sets with `f` unbounded,
  i.e. sets that are exceptionally dense at arbitrarily large scales.

The two cases are complementary; `main` performs the case split and the
conversion from the rpow-free form to the `ENNReal` liminf of the target.
-/

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R2

open Filter

def H1 : Prop :=
  ∀ (A : Set ℕ), A.Infinite → IsSidon A → ∀ C : ℝ,
    (∀ x : ℕ, 2 ≤ x → ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ C * x) →
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x

def H2 : Prop :=
  ∀ (A : Set ℕ), A.Infinite → IsSidon A →
    (∀ C : ℝ, ∃ x : ℕ, 2 ≤ x ∧ C * x < ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x) →
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x

theorem liminf_ofReal_zero_of_frequently {u : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ x in atTop, u x ≤ ε) :
    liminf (fun x ↦ ENNReal.ofReal (u x)) atTop = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  apply Filter.liminf_le_of_frequently_le'
  refine (h ε (by exact_mod_cast hε)).mono fun x hx => ?_
  exact ENNReal.ofReal_le_of_le_toReal (by simpa using hx)

theorem normalised_le_of_sq_le {n x : ℕ} {ε : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    (h : (n : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x) :
    (n : ℝ) / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) ≤ ε := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_mul_eq_mul_div,
    div_le_iff₀ (Real.sqrt_pos.2 hx0)]
  have h1 : (n : ℝ) * Real.sqrt (Real.log x) = Real.sqrt ((n : ℝ) ^ 2 * Real.log x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
  have h2 : ε * Real.sqrt x = Real.sqrt (ε ^ 2 * x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
  rw [h1, h2]
  exact Real.sqrt_le_sqrt h

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.i := by
  intro hH1 hH2 A hinf hS
  have hcore : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x := by
    by_cases hb : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
        ((A ∩ Set.Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ C * x
    · obtain ⟨C, hC⟩ := hb
      exact hH1 A hinf hS C hC
    · refine hH2 A hinf hS fun C => ?_
      push Not at hb
      exact hb C
  apply liminf_ofReal_zero_of_frequently
  intro ε hε
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨x, hNx, hx1, hx⟩ := hcore ε hε N
  exact ⟨x, hNx, normalised_le_of_sq_le hε hx1 hx⟩

end OMA.R_Erdos1191_erdos_1191_parts_i_R2
