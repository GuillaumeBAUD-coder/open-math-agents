import FormalConjectures.ErdosProblems.«961»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Multiplicity

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
  -- Valuation equals the number of carries
  rw [padicValNat_choose hkn hnb]
  -- Carry set ⊆ Ico 1 (log + 1), so card ≤ log
  apply Finset.card_le_card
  apply Finset.filter_subset
  -- card of Ico 1 (b) = b - 1 ≤ log
  exact Nat.le_of_lt_succ (Finset.card_Ico _ _)

/-- Product over primes ≤ k of maximal powers is ≤ (u+t)^{π(k)} -/
lemma product_smooth_bound (k u t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p (u + t))
      ≤ (u + t) ^ (Nat.primeCounting k) := by
  -- Each term p^{log_p (u+t)} ≤ u+t, and there are π(k) primes
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
