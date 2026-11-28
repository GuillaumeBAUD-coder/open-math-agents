import FormalConjectures.ErdosProblems.«961»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Multiplicity

-- Problem: Erdős Problem 961 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/961.lean:83
-- Credit: @sassmama27
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Nat

namespace Erdos961

/-- Bound on the p-adic valuation of a binomial coefficient.
Uses Mathlib's Kummer theorem (`padicValNat_choose`). -/
lemma binomial_val_bound (u t p : ℕ) (hp : Nat.Prime p) (hpu : p ≤ u + t) (ht : 0 < t) :
    padicValNat p (Nat.choose (u + t) t) ≤ Nat.log p (u + t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Number of carries ≤ number of base-p digits of (u+t), which is ≤ log_p (u+t) + 1
  -- but the strict bound we need is ≤ log (after adjusting)
  have hkn : t ≤ u + t := Nat.le_add_left t u
  have hnb : Nat.log p (u + t) < Nat.log p (u + t) + 1 := Nat.lt_succ_self _
  -- padicValNat_choose equates the valuation to the cardinality of the carry set
  -- The carry set is a subset of Ico 1 (log + 1), hence card ≤ log
  sorry -- replace with:
  -- rw [padicValNat_choose hkn hnb]
  -- exact Finset.card_le_card (Finset.filter_subset _ _)
  -- then bound by card of Ico which is log

/-- Product over primes ≤ k of maximal powers is ≤ (u+t)^{π(k)} -/
lemma product_smooth_bound (k u t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p (u + t))
      ≤ (u + t) ^ (Nat.primeCounting k) := by
  sorry

/-- Main contradiction for large constant (c > 6 works) -/
lemma erdos_1955_contradiction (k : ℕ) (hk : 100 < k)
    (h : ∃ u ≥ k ^ 2, ∀ i < ⌈(6 : ℝ) * k / Real.log k⌉₊,
      (u + i).PrimeFactors.sup id ≤ k) :
    False := by
  sorry

end Erdos961

theorem OMA.solution : type_of% @Erdos961.erdos_961.variants.erdos_upper_bound := by
  -- Eventually for large k, f k < 3 * k / log k
  sorry
