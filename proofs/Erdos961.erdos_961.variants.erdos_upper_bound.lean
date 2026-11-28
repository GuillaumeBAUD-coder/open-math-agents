import FormalConjectures.ErdosProblems.«961»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.PrimeCounting

-- Problem: Erdős Problem 961 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/961.lean:83
-- Credit: @sassmama27
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Nat Finset

namespace Erdos961

/-- Bound on the p-adic valuation of a binomial coefficient.
Uses Mathlib's Kummer theorem (`padicValNat_choose`). -/
lemma binomial_val_bound (u t p : ℕ) (hp : Nat.Prime p) (hpu : p ≤ u + t) (ht : 0 < t) :
    padicValNat p (Nat.choose (u + t) t) ≤ Nat.log p (u + t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkn : t ≤ u + t := Nat.le_add_left t u
  have hnb : Nat.log p (u + t) < Nat.log p (u + t) + 1 := Nat.lt_succ_self _
  rw [padicValNat_choose hkn hnb]
  apply Finset.card_le_card
  apply Finset.filter_subset
  exact Nat.le_of_lt_succ (Finset.card_Ico _ _)

/-- Product over primes ≤ k of maximal powers is ≤ (u+t)^{π(k)} -/
lemma product_smooth_bound (k u t : ℕ) (hk : 0 < k) (ht : 0 < t) (hu : 1 < u + t) :
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p (u + t))
      ≤ (u + t) ^ (Nat.primeCounting k) := by
  -- Each p^{log_p m} ≤ m
  have hterm (p : ℕ) (hp : p ∈ (Finset.range (k + 1)).filter Nat.Prime) :
      p ^ Nat.log p (u + t) ≤ u + t := by
    sorry -- use Nat.pow_log_le or similar
  -- Number of primes is π(k)
  have hcard : ((Finset.range (k + 1)).filter Nat.Prime).card = Nat.primeCounting k := by
    sorry -- Mathlib: Nat.primeCounting_eq_card_primes_le or equivalent
  -- Product of ≤ terms raised to the count
  sorry -- Finset.prod_le_prod + pow_le_pow

/-- Main contradiction for large constant (c > 6 works) -/
lemma erdos_1955_contradiction (k : ℕ) (hk : 100 < k)
    (h : ∃ u ≥ k ^ 2, ∀ i < ⌈(6 : ℝ) * k / Real.log k⌉₊,
      (u + i).PrimeFactors.sup id ≤ k) :
    False := by
  -- Obtain u and the long smooth run
  obtain ⟨u, hu, hrun⟩ := h
  -- Set t = ⌈6 k / log k⌉
  let t := ⌈(6 : ℝ) * k / Real.log k⌉₊
  -- Binomial is large: choose (u+t) t ≳ (u/t)^t or better lower bound
  -- On the other hand, from smoothness + binomial_val_bound + product_smooth_bound
  -- the binomial is ≤ (u+t)^{π(k)} which is too small for c=6
  sorry

end Erdos961

theorem OMA.solution : type_of% @Erdos961.erdos_961.variants.erdos_upper_bound := by
  -- Eventually for large k, f k < 3 * k / log k
  sorry
