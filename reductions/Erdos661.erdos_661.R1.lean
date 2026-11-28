import FormalConjectures.ErdosProblems.«661»

open Filter Asymptotics
open Erdos661
open scoped EuclideanGeometry

/-!
Erdős 661 asks for `F(n) = o(n/sqrt(log n))`, where F is the minimal number of
cross distances between two n-point sets. The upstream file proves (with a full
Lean proof, category textbook) the transfer lemma `F(n) ≤ f(2n)` where f is the
minimal number of distinct distances of 2n points. We isolate that proved
transfer in H1. The only open content left in H2 is the classical distinct
distances upper bound. `main` is a one-line squeeze: since 0 ≤ F ≤ f and f is
little-o of the same denominator, F is little-o of it too.
-/

namespace OMA.R_Erdos661_erdos_661_R1

-- Proved upstream: erdos_661.variants.le_minimalDistinctDistances (textbook).
def H1 : Prop :=
  ∀ n : ℕ, minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

-- Open: the classical distinct-distances upper bound f(2n) = o(n / sqrt(log n)).
def H2 : Prop :=
  (fun n : ℕ => (minimalDistinctDistances ℝ² (2 * n) : ℝ)) =o[atTop]
    (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt)

theorem main : H1 → H2 → type_of% @Erdos661.erdos_661 := by
  intro hle hf
  change (fun n : ℕ => (minimalDistinctDistances ℝ² (2 * n) : ℝ)) =o[atTop]
    (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) at hf
  rw [Asymptotics.isLittleO_iff] at hf ⊢
  intro c hc
  filter_upwards [hf hc] with n hn
  have hnorm : ‖(minimalCrossDistances ℝ² n : ℝ)‖ ≤
      ‖(minimalDistinctDistances ℝ² (2 * n) : ℝ)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (minimalCrossDistances ℝ² n : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (minimalDistinctDistances ℝ² (2 * n) : ℝ))]
    exact_mod_cast hle n
  exact hnorm.trans hn

end OMA.R_Erdos661_erdos_661_R1
