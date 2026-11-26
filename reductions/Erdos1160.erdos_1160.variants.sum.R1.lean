import FormalConjectures.ErdosProblems.«1160»

/-!
Erdős problem 1160, sum variant. Reduction by @kamaleshanantha with Codex. This file proves the implication from H1 and H2.
The group enumeration estimates used to justify these hypotheses are due to
Yinan Li and Youming Qiao, arXiv:2610.14509v3, sections 15.5 and 15.7.
-/

open Filter
open scoped BigOperators

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1

open Erdos1160

-- Below order 2^m, groups of 2-power order eventually account for at least half
-- of the isomorphism classes. See Corollary 15.10 at the cutoff 2^m - 1.
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (∑ n ∈ Finset.Ico 1 (2 ^ m), g n) ≤ 2 * (∑ k ∈ Finset.range m, g (2 ^ k))

-- On doubling the order from 2^m, the number of isomorphism classes eventually
-- more than triples. See the adjacent-order logarithmic estimate in section 15.7.
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, 3 * g (2 ^ m) < g (2 ^ (m + 1))

lemma sum_le_of_eventual_growth (a : ℕ → ℕ)
    (h : ∀ᶠ m : ℕ in atTop, 3 * a m < a (m + 1)) :
    ∀ᶠ m : ℕ in atTop, 2 * (∑ k ∈ Finset.range m, a k) ≤ a m := by
  obtain ⟨N, hg⟩ := Filter.eventually_atTop.mp h
  let S (m : ℕ) : ℕ := ∑ k ∈ Finset.range m, a k
  have hs (m : ℕ) : S (m + 1) = S m + a m := Finset.sum_range_succ a m
  -- After N, each step recovers at least one unit of the initial cumulative deficit.
  have bound (t : ℕ) : 2 * S (N + t) + t ≤ a (N + t) + 2 * S N := by
    induction t with
    | zero =>
      simp only [Nat.add_zero]
      omega
    | succ t ih =>
      have inc := hg (N + t) (by omega)
      change 2 * S ((N + t) + 1) + (t + 1) ≤ a ((N + t) + 1) + 2 * S N
      rw [hs]
      omega
  refine Filter.eventually_atTop.mpr ⟨N + 2 * S N, ?_⟩
  intro m hm
  have ht : 2 * S N ≤ m - N := by omega
  have he : N + (m - N) = m := by omega
  have hb := bound (m - N)
  rw [he] at hb
  change 2 * S m ≤ a m
  omega

theorem main : H1 → H2 → type_of% @Erdos1160.erdos_1160.variants.sum := by
  intro h₁ h₂
  unfold H1 at h₁
  unfold H2 at h₂
  have hg := sum_le_of_eventual_growth (fun k => g (2 ^ k)) h₂
  filter_upwards [h₁, hg] with m hcount hsum using hcount.trans hsum

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1
