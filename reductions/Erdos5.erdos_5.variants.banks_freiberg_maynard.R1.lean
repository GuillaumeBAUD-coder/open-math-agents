import FormalConjectures.ErdosProblems.«5»
import Mathlib

-- Reduction Erdos5.erdos_5.variants.banks_freiberg_maynard.R1 of the nine-shift theorem of
-- Banks, Freiberg and Maynard on limit points of normalised prime gaps (Erdős Problem 5).
-- Source: W. D. Banks, T. Freiberg, J. Maynard, On limit points of the sequence of normalized
-- prime gaps, Proc. Lond. Math. Soc. (3) 113 (2016), 515-539, Theorem 1.1.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Banks–Freiberg–Maynard nine-shift theorem, index normalisation, weakly increasing shifts

The upstream statement normalises the prime gaps by `log n` and allows repeated shifts
(`Monotone β`). The paper normalises by `log pₙ`, and its sieve argument produces a difference
of two *distinct* shifts.

* `H1` (deep input, [BFM16, Theorem 1.1] in the paper's own normalisation, for strictly
  increasing shifts): for nonnegative reals `β₁ < … < β₉` some difference `βⱼ - βᵢ`, `i < j`, is
  a limit of `(pₙ₊₁ - pₙ) / log pₙ` along a strictly increasing sequence of indices. Its proof
  combines the Maynard–Tao sieve with the Erdős–Rankin construction. This is word for word `H1`
  of `Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1`, so one proof closes both trees.
* `H2` (elementary given Chebyshev bounds): `log pₙ / log n → 1`. This is word for word `H2` of
  the `banks_freiberg_maynard_measure`, `merikoski_measure`, `merikoski_bounded_gaps` and `pintz`
  reductions of Erdős Problem 5.

`main` glues them as follows. `H1` and `H2` give the statement for strictly increasing shifts
(`strict_case`). Applying that to the shifts `0, ε, 2ε, …, 8ε` puts a point of the limit point
set in `(0, 8ε]` for every `ε > 0`; the limit point set is closed, so it contains `0`
(`zero_mem`). No separate appeal to Goldston–Pintz–Yıldırım is needed. Finally a weakly
increasing `β` is either strictly increasing, or has `βᵢ = βⱼ` for some `i < j`, and then the
difference is `0`.
-/

namespace OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R1

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

/-- Banks–Freiberg–Maynard, Theorem 1.1, in the prime normalisation `log pₙ`, for strictly
increasing nonnegative shifts. Deep input (Maynard–Tao sieve plus Erdős–Rankin). -/
def H1 : Prop := ∀ β : Fin 9 → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
    ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 (β j - β i))

/-- Passing from the prime normalisation to the index normalisation: `log pₙ / log n → 1`. -/
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

/-- The nine-shift theorem for strictly increasing shifts, in the index normalisation. -/
lemma strict_case (h1 : H1) (h2 : H2) (β : Fin 9 → ℝ) (hβ : ∀ i, 0 ≤ β i) (hs : StrictMono β) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  obtain ⟨i, j, hij, n, hn, hlim⟩ := h1 β hβ hs
  refine ⟨i, j, hij, (mem_limitPointSet_iff _).2 ⟨n, hn, ?_⟩⟩
  have h := hlim.mul (h2.comp hn.tendsto_atTop)
  rw [mul_one] at h
  refine h.congr fun k => ?_
  have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
  simp only [Function.comp_apply, normalizedGap]
  rw [div_mul_div_cancel₀ hp.ne']

/-- Zero is a limit point: the strict case puts limit points in `(0, 8ε]` for every `ε`. -/
lemma zero_mem (h1 : H1) (h2 : H2) : (0 : ℝ) ∈ limitPointSet := by
  rw [← isClosed_limitPointSet.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hε9 : 0 < ε / 9 := by positivity
  obtain ⟨i, j, hij, hmem⟩ := strict_case h1 h2 (fun i : Fin 9 => (i : ℝ) * (ε / 9))
    (fun i => by positivity)
    (fun a b hab => by
      have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      exact mul_lt_mul_of_pos_right this hε9)
  refine ⟨_, hmem, ?_⟩
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hj : ((j : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (by omega : (j : ℕ) ≤ 8)
  have hlt : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  rw [Real.dist_eq, zero_sub, abs_neg]
  have hpos : 0 ≤ (j : ℝ) * (ε / 9) - (i : ℝ) * (ε / 9) := by nlinarith
  rw [abs_of_nonneg hpos]
  nlinarith

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  intro h1 h2 β hβ hβmono
  by_cases hs : StrictMono β
  · exact strict_case h1 h2 β hβ hs
  · unfold StrictMono at hs
    push Not at hs
    obtain ⟨i, j, hij, hle⟩ := hs
    have heq : β j - β i = 0 := by linarith [hβmono hij.le]
    exact ⟨i, j, hij, heq ▸ zero_mem h1 h2⟩

end OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R1
