import Mathlib

namespace OMA.S_wp_selberg_s_orthogonality_conjecture

open scoped BigOperators Topology

noncomputable def dirichletTerm (a : ℕ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  a n / (n : ℂ) ^ s

/-- The continuation after removing a possible pole at one is entire of finite order. -/
def finiteOrderContinuation (F : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (G : ℂ → ℂ) (C ρ : ℝ),
    Differentiable ℂ G ∧ 0 < C ∧ 0 < ρ ∧
    (∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) ∧
    ∀ s, ‖G s‖ ≤ C * Real.exp (‖s‖ ^ ρ)

/-- The arguments of the gamma factors avoid their poles. -/
def gammaRegular {r : ℕ} (weights : Fin r → ℝ) (μ : Fin r → ℂ) (s : ℂ) : Prop :=
  ∀ (j : Fin r) (n : ℕ), (weights j : ℂ) * s + μ j ≠ -(n : ℂ)

noncomputable def completed {r : ℕ} (F : ℂ → ℂ) (Q : ℝ)
    (weights : Fin r → ℝ) (μ : Fin r → ℂ) (s : ℂ) : ℂ :=
  (Q : ℂ) ^ s * F s * ∏ j, Complex.Gamma ((weights j : ℂ) * s + μ j)

/-- The meromorphic reflection equation, evaluated at common regular points. -/
def functionalEquation (F : ℂ → ℂ) : Prop :=
  ∃ (r : ℕ) (Q : ℝ) (weights : Fin r → ℝ) (μ : Fin r → ℂ) (ω : ℂ),
    0 < Q ∧ (∀ j, 0 < weights j ∧ 0 ≤ (μ j).re) ∧ ‖ω‖ = 1 ∧
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      gammaRegular weights μ s → gammaRegular weights μ (1 - star s) →
      completed F Q weights μ s = ω * star (completed F Q weights μ (1 - star s))

/-- The logarithmic Euler product with coefficients supported on prime powers. -/
def eulerProduct (F : ℂ → ℂ) : Prop :=
  ∃ (b : ℕ → ℂ) (C θ : ℝ), 0 < C ∧ θ < 1 / 2 ∧
    (∀ n, 2 ≤ n → (¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k) → b n = 0) ∧
    (∀ n, 2 ≤ n → ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    ∀ s : ℂ, 1 < s.re →
      Summable (fun n : ℕ => ‖dirichletTerm b (n + 2) s‖) ∧
      F s = Complex.exp (∑' n : ℕ, dirichletTerm b (n + 2) s)

/-- A Dirichlet series satisfying the defining conditions of the Selberg class. -/
structure SelbergSeries where
  value : ℂ → ℂ
  coefficient : ℕ → ℂ
  normalized : coefficient 1 = 1
  series : ∀ s : ℂ, 1 < s.re →
    HasSum (fun n : ℕ => dirichletTerm coefficient (n + 1) s) (value s) ∧
    Summable (fun n : ℕ => ‖dirichletTerm coefficient (n + 1) s‖)
  continuation : finiteOrderContinuation value
  ramanujan : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ‖coefficient n‖ ≤ C * (n : ℝ) ^ ε
  reflection : functionalEquation value
  product : eulerProduct value

def sameSeries (F G : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 < s.re → F s = G s

/-- A nonidentity member with no factorization into two nonidentity members. -/
def Primitive (F : SelbergSeries) : Prop :=
  ¬ sameSeries F.value (fun _ => 1) ∧
    ∀ G H : SelbergSeries,
      sameSeries F.value (fun s => G.value s * H.value s) →
      sameSeries G.value (fun _ => 1) ∨ sameSeries H.value (fun _ => 1)

noncomputable def primeCorrelation (F G : SelbergSeries) (x : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
    F.coefficient p * star (G.coefficient p) / (p : ℂ)

/-- Selberg's normality and orthogonality conjectures with bounded remainders. -/
theorem main :
    (∀ F : SelbergSeries, ∃ (m : ℤ) (C : ℝ),
      (Primitive F → m = 1) ∧
      ∀ x : ℕ, 2 ≤ x →
        ‖primeCorrelation F F x - (m : ℂ) * (Real.log (Real.log x) : ℂ)‖ ≤ C) ∧
    (∀ F G : SelbergSeries, Primitive F → Primitive G → ¬ sameSeries F.value G.value →
      ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ‖primeCorrelation F G x‖ ≤ C) := by
  sorry

end OMA.S_wp_selberg_s_orthogonality_conjecture
