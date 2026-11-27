import FormalConjectures.ErdosProblems.«360»

-- Reduction Erdos360.erdos_360.variants.alon_erdos.R1 of Erdős Problem 360 — alon erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/360.lean:77
-- Credit: @tgg6956g2z-bot
-- Splits the two-sided Alon-Erdős (1996) asymptotic bound into independent explicit lower and upper bounds.

namespace OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1

/-- Explicit lower bound from Alon-Erdős (1996): f(n) >> n^(1/3) / (log n)^(4/3). -/
def H1 : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
    (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) ^ (4 / 3 : ℝ) ≤ C * (Erdos360.f n : ℝ)

/-- Explicit upper bound from Alon-Erdős (1996): f(n) << n^(1/3) * (log log n)^(1/3) / (log n)^(1/3). -/
def H2 : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
    (Erdos360.f n : ℝ) ≤
      C * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ))

theorem main : H1 → H2 → type_of% @Erdos360.erdos_360.variants.alon_erdos := by
  rintro ⟨C1, N1, h1⟩ ⟨C2, N2, h2⟩
  refine ⟨?_, ?_⟩
  · rw [Asymptotics.isBigO_iff]
    refine ⟨C1, Filter.eventually_atTop.mpr ⟨max N1 1, fun n hn ↦ ?_⟩⟩
    have hn1 : (1 : ℝ) ≤ (n : ℝ) :=
      Nat.one_le_cast.mpr (le_trans (le_max_right N1 1) hn)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hlhs : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) ^ (4 / 3 : ℝ) :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg hlog _)
    rw [Real.norm_eq_abs, abs_of_nonneg hlhs,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (Erdos360.f n))]
    exact h1 n (le_trans (le_max_left N1 1) hn)
  · rw [Asymptotics.isBigO_iff]
    refine ⟨C2, Filter.eventually_atTop.mpr ⟨max N2 (Nat.ceil (Real.exp 1)), fun n hn ↦ ?_⟩⟩
    have hexp : Real.exp 1 ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil (Real.exp 1))
        (Nat.cast_le.mpr (le_trans (le_max_right N2 (Nat.ceil (Real.exp 1))) hn))
    have hlog1 : 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hexp
    have hlog : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog1
    have hloglog : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hlog1
    have hrhs :
        0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) :=
      mul_nonneg
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg hlog _))
        (Real.rpow_nonneg hloglog _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (Erdos360.f n)),
      Real.norm_eq_abs, abs_of_nonneg hrhs]
    exact h2 n (le_trans (le_max_left N2 (Nat.ceil (Real.exp 1))) hn)

end OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1

/-!
# Elementary covering classes for the Alon–Erdős upper bound

These are the three types of classes used in Section 2 of Alon and Erdős,
*Sure monochromatic subset sums* (1996). Integer inequalities encode the
interval endpoints without rounding. A finite subset is represented by a
finset, so the summands are distinct.
-/

namespace Erdos360IntervalClasses

open Finset

/-- A finite nonempty subset with at most `k` elements strictly below `n / k`
has sum strictly below `n`. -/
theorem sum_lt_target_of_card_le {n k : ℕ} {T : Finset ℕ}
    (hT : T.Nonempty) (hcard : T.card ≤ k)
    (hupper : ∀ a ∈ T, k * a < n) : (∑ a ∈ T, a) < n := by
  have hsum : k * (∑ a ∈ T, a) < T.card * n := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using
      (Finset.sum_lt_sum_of_nonempty hT hupper)
  by_contra! h
  exact hsum.not_ge ((Nat.mul_le_mul_right n hcard).trans (Nat.mul_le_mul_left k h))

/-- No finite subset of the interval class sums to the target. -/
theorem interval_sum_ne {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {T : Finset ℕ} (hT : ∀ a ∈ T, (n ≤ (k + 1) * a ∧ k * a < n)) :
    (∑ a ∈ T, a) ≠ n := by
  intro hsum
  by_cases hcard : T.card ≤ k
  · have hne : T.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
      exact hn.ne' hsum.symm
    exact (sum_lt_target_of_card_le hne hcard fun a ha => (hT a ha).2).ne hsum
  · have hcard' : k + 1 ≤ T.card := Nat.succ_le_of_lt (lt_of_not_ge hcard)
    have htwo : 1 < T.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    have hstrict : ∃ x ∈ T, n < (k + 1) * x := by
      by_contra! h
      have haeq := le_antisymm (h a ha) (hT a ha).1
      have hbeq := le_antisymm (h b hb) (hT b hb).1
      exact hab (Nat.eq_of_mul_eq_mul_left (by omega) (haeq.trans hbeq.symm))
    have hscaled : T.card * n < (k + 1) * (∑ a ∈ T, a) := by
      rw [Finset.mul_sum]
      simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using
        (Finset.sum_lt_sum (fun a ha => (hT a ha).1) hstrict)
    rw [hsum] at hscaled
    exact hscaled.not_ge (Nat.mul_le_mul_right n hcard')

/-- Multiples of any number that does not divide the target form a valid class. -/
theorem multiples_sum_ne {n p : ℕ} (hn : ¬ p ∣ n) {T : Finset ℕ}
    (hT : ∀ a ∈ T, p ∣ a) : (∑ a ∈ T, a) ≠ n := by
  intro hsum
  exact hn (hsum ▸ Finset.dvd_sum hT)

/-- Elements below the target are either below all the intervals through `t`,
or lie in one of those intervals. -/
theorem below_or_mem_interval {n a : ℕ} (ha : a < n) (t : ℕ) :
    (t + 1) * a < n ∨ ∃ k, 1 ≤ k ∧ k ≤ t ∧ (n ≤ (k + 1) * a ∧ k * a < n) := by
  induction t with
  | zero => exact Or.inl (by simpa using ha)
  | succ t ih =>
    rcases ih with hbelow | ⟨k, hk, hkt, hmem⟩
    · by_cases h : (t + 1 + 1) * a < n
      · exact Or.inl h
      · exact Or.inr ⟨t + 1, by omega, le_rfl, le_of_not_gt h, hbelow⟩
    · exact Or.inr ⟨k, hk, hkt.trans (Nat.le_succ t), hmem⟩

/-- A block of at most `t + 1` remaining elements cannot sum to `n`. -/
theorem small_block_sum_ne {n t : ℕ} (hn : 0 < n) {T : Finset ℕ}
    (hcard : T.card ≤ t + 1) (hT : ∀ a ∈ T, (t + 1) * a < n) :
    (∑ a ∈ T, a) ≠ n := by
  by_cases hne : T.Nonempty
  · exact (sum_lt_target_of_card_le hne hcard hT).ne
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact hn.ne

/-- After using the intervals and the divisibility classes indexed by `P`,
an uncovered element lies in the short interval and is sifted by `P`. -/
theorem uncovered_iff {n a t : ℕ} (ha : a < n) (P : Finset ℕ) :
    (¬ (∃ k, 1 ≤ k ∧ k ≤ t ∧ (n ≤ (k + 1) * a ∧ k * a < n)) ∧
      ¬ (∃ p ∈ P, p ∣ a)) ↔
      ((t + 1) * a < n ∧ ∀ p ∈ P, ¬ p ∣ a) := by
  constructor
  · rintro ⟨hinterval, hmultiple⟩
    refine ⟨(below_or_mem_interval ha t).resolve_right hinterval, ?_⟩
    exact fun p hp hdvd => hmultiple ⟨p, hp, hdvd⟩
  · rintro ⟨hsmall, hrough⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨k, _, hkt, hmem⟩
      have hmul : (k + 1) * a ≤ (t + 1) * a :=
        Nat.mul_le_mul_right a (Nat.succ_le_succ hkt)
      exact (hmem.1.trans hmul).not_gt hsmall
    · rintro ⟨p, hp, hdvd⟩
      exact hrough p hp hdvd

/-- The interval class satisfies the subset-sum condition in `Erdos360.f`. -/
theorem interval_not_mem_subsetSums {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    n ∉ subsetSums {a | (n ≤ (k + 1) * a ∧ k * a < n)} := by
  rintro ⟨T, hT, hsum⟩
  exact interval_sum_ne hn hk (fun a ha => hT ha) hsum.symm

/-- The divisibility class satisfies the same condition when its index does not
divide `n`. -/
theorem multiples_not_mem_subsetSums {n p : ℕ} (hn : ¬ p ∣ n) :
    n ∉ subsetSums {a | p ∣ a} := by
  rintro ⟨T, hT, hsum⟩
  exact multiples_sum_ne hn (fun a ha => hT ha) hsum.symm

/-- A sufficiently short block of uncovered elements is also a valid class. -/
theorem small_block_not_mem_subsetSums {n t : ℕ} (hn : 0 < n) {B : Finset ℕ}
    (hcard : B.card ≤ t + 1) (hB : ∀ a ∈ B, (t + 1) * a < n) :
    n ∉ subsetSums (B : Set ℕ) := by
  rintro ⟨T, hT, hsum⟩
  exact small_block_sum_ne hn ((card_le_card hT).trans hcard)
    (fun a ha => hB a (hT ha)) hsum.symm

end Erdos360IntervalClasses
