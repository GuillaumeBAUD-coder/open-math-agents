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
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact congr_arg Finset.card (Nat.primesLE_eq_filter_range k)
  -- Each term ≤ u+t, so product ≤ (u+t)^card
  calc
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ Nat.log p (u + t)
        ≤ ∏ p in (Finset.range (k + 1)).filter Nat.Prime, (u + t) := by
          exact Finset.prod_le_prod (fun p hp => Nat.zero_le _) hterm
      _ = (u + t) ^ ((Finset.range (k + 1)).filter Nat.Prime).card := by
          rw [Finset.prod_const]
      _ = (u + t) ^ Nat.primeCounting k := by
          rw [hcard]

/-- Lower bound on the binomial coefficient for large u relative to t. -/
lemma binomial_lower_bound (u t : ℕ) (hu : t ≤ u) (ht : 0 < t) :
    (u / t : ℝ) ^ t ≤ Nat.choose (u + t) t := by
  -- Step 1: Mathlib lower bound (n + 1 - r)^r / r! ≤ choose n r
  -- with n = u + t, r = t gives (u + 1)^t / t! ≤ choose (u + t) t
  have h2 : (↑(u + 1) ^ t : ℝ) / ↑(t.factorial) ≤ ↑(Nat.choose (u + t) t) := by
    exact_mod_cast Nat.pow_le_choose t (u + t)
  -- Step 2: trivial comparison u ≤ u + 1
  have h1 : (↑u / ↑t) ^ t ≤ (↑(u + 1) / ↑t) ^ t := by
    gcongr
    exact Nat.cast_le.mpr (Nat.le_succ u)
  -- Step 3: middle inequality
  -- (u + 1)^t / t^t ≤ (u + 1)^t / t!
  -- which rearranges to t! ≤ t^t (true for t ≥ 1)
  have hmid : (↑(u + 1) / ↑t) ^ t ≤ (↑(u + 1) ^ t : ℝ) / ↑(t.factorial) := by
    -- After clearing denominators this is t! ≤ t^t
    -- which holds by induction or by t! = 1·2·…·t ≤ t·t·…·t
    sorry
  exact h1.trans (hmid.trans h2)

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
