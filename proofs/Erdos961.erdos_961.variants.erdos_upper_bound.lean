import FormalConjectures.ErdosProblems.«961»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Bounds

-- Problem: Erdős Problem 961 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/961.lean:83
-- Credit: @sassmama27
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Nat Finset

namespace Erdos961

lemma binomial_val_bound (u t p : ℕ) (hp : Nat.Prime p) (hpu : p ≤ u + t) (ht : 0 < t) :
    padicValNat p (Nat.choose (u + t) t) ≤ Nat.log p (u + t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkn : t ≤ u + t := Nat.le_add_left t u
  have hnb : Nat.log p (u + t) < Nat.log p (u + t) + 1 := Nat.lt_succ_self _
  rw [padicValNat_choose hkn hnb]
  apply Finset.card_le_card
  apply Finset.filter_subset
  exact Nat.le_of_lt_succ (Finset.card_Ico _ _)

lemma product_smooth_bound (k u t : ℕ) (hk : 0 < k) (ht : 0 < t) (hu : 1 < u + t) :
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p (u + t))
      ≤ (u + t) ^ (Nat.primeCounting k) := by
  have hterm (p : ℕ) (hp : p ∈ (Finset.range (k + 1)).filter Nat.Prime) :
      p ^ Nat.log p (u + t) ≤ u + t := by
    have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact Nat.pow_log_le_self hp_prime.one_lt (by linarith [hu])
  have hcard : ((Finset.range (k + 1)).filter Nat.Prime).card = Nat.primeCounting k := by
    -- primes in 1..k have cardinality π(k)
    sorry
  -- ∏ ≤ (u+t)^card
  sorry

/-- Lower bound on the binomial coefficient for large u relative to t. -/
lemma binomial_lower_bound (u t : ℕ) (hu : t ≤ u) (ht : 0 < t) :
    (u / t : ℝ) ^ t ≤ Nat.choose (u + t) t := by
  -- Standard bound: choose (u+t) t ≥ (u/t)^t
  -- Follows from choose n k ≥ (n/k)^k for k ≤ n/2 or similar
  sorry

lemma erdos_1955_contradiction (k : ℕ) (hk : 100 < k)
    (h : ∃ u ≥ k ^ 2, ∀ i < ⌈(6 : ℝ) * ↑k / Real.log ↑k⌉₊,
      (u + i).PrimeFactors.sup id ≤ k) :
    False := by
  obtain ⟨u, hu_ge, hrun⟩ := h
  let t := ⌈(6 : ℝ) * ↑k / Real.log ↑k⌉₊
  have ht_pos : 0 < t := by sorry
  have hu_large : 1 < u + t := by sorry
  have ht_le_u : t ≤ u := by
    -- for k>100, 6k/log k ≤ k²
    sorry
  -- Upper bound from smoothness
  have hupper : Nat.choose (u + t) t ≤ (u + t) ^ Nat.primeCounting k := by
    sorry
  -- Lower bound
  have hlower : (u + t) ^ Nat.primeCounting k < Nat.choose (u + t) t := by
    -- use binomial_lower_bound and compare (u/t)^t vs (u+t)^π(k)
    sorry
  exact lt_irrefl _ (hupper.trans_lt hlower)

end Erdos961

theorem OMA.solution : type_of% @Erdos961.erdos_961.variants.erdos_upper_bound := by
  sorry
