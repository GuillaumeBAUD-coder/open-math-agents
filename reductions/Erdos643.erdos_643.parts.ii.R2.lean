import FormalConjectures.ErdosProblems.«643»

/-!
Assembly of the independently verified rank-three and higher-rank proofs.
-/

namespace Erdos643Star

/- Binomial estimates adapted from Yilin Liu, icekylinx/jsp-000523-proof,
commit 59d41a6a1f3b8f99f148fa21b21e834525eed3a5 (Apache-2.0).
The star and squeeze below use the pinned hypergraph definitions. -/

open Filter Erdos643

/-- Clearing denominators in Mathlib's binomial lower bound. -/
theorem pow_sub_le_factorial_mul_choose (n t : ℕ) :
    (n + 1 - t) ^ t ≤ t.factorial * n.choose t := by
  have hq := Nat.pow_le_choose (α := ℚ) t n
  have hf : (0 : ℚ) < (t.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos t
  rw [div_le_iff₀ hf] at hq
  have hNat : (n + 1 - t) ^ t ≤ n.choose t * t.factorial := by
    exact_mod_cast hq
  simpa [Nat.mul_comm] using hNat

/-- The elementary ratio between a star and its ambient shadow layer. -/
theorem shifted_choose_ratio (n k : ℕ) (hn : k + 1 ≤ n) :
    ((n - 1).choose k : ℝ) / (n.choose k : ℝ) = 1 - (k : ℝ) / n := by
  have hn1 : 1 ≤ n := by omega
  have hPos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNat := Nat.choose_mul_succ_eq (n - 1) k
  rw [Nat.sub_add_cancel hn1] at hNat
  have hEqNat : ((n - 1).choose k : ℝ) * n = (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast hNat
  rw [Nat.cast_sub (show k ≤ n by omega)] at hEqNat
  have hEq := hEqNat
  apply (div_eq_iff hPos.ne').2
  field_simp [hnPos.ne']
  nlinarith only [hEq]

/-- A fixed binomial coefficient of order at least two dominates a
quadratic term, with an explicit constant. -/
theorem quadratic_le_factorial_choose (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 4 ≤ n) :
    n ^ 2 ≤ 4 * k.factorial * n.choose k := by
  let b := n + 1 - k
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hnb : n ≤ 2 * b := by dsimp [b]; omega
  have hp : b ^ 2 ≤ b ^ k := Nat.pow_le_pow_right hb hk
  have hChoose := pow_sub_le_factorial_mul_choose n k
  have hSq := Nat.pow_le_pow_left hnb 2
  change b ^ k ≤ k.factorial * n.choose k at hChoose
  nlinarith only [hSq, hp, hChoose]

/-- Every nonnegative linear-size error is negligible relative to a
fixed binomial coefficient of order at least two. -/
theorem linear_error_choose_ratio_tendsto_zero
    (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ᶠ n in atTop, f n ≤ n + 1) :
    Tendsto (fun n => (f n : ℝ) / (n.choose k : ℝ)) atTop (nhds 0) := by
  have hUpper := tendsto_const_div_atTop_nhds_zero_nat (8 * (k.factorial : ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [hf, eventually_ge_atTop (2 * k + 4)] with n hfn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : (0 : ℝ) < n := by linarith
  have hChoosePos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hQuadratic : (n : ℝ) ^ 2 ≤ 4 * (k.factorial : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast quadratic_le_factorial_choose n k hk hn
  have hF : (f n : ℝ) ≤ 2 * n := by
    have h : (f n : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hfn
    linarith
  apply (div_le_div_iff₀ hChoosePos hnPos).2
  nlinarith only [mul_le_mul_of_nonneg_right hF hnPos.le, hQuadratic]

/-- Fixed-rank stars have coefficient one in the ambient binomial scale. -/
theorem shifted_choose_ratio_tendsto_one (k : ℕ) :
    Tendsto (fun n => ((n - 1).choose k : ℝ) / (n.choose k : ℝ)) atTop (nhds 1) := by
  have hLimit : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  apply hLimit.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  exact (shifted_choose_ratio n k hn).symm

theorem star_lower (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    (n-1).choose (r-1) ≤ forcingThreshold n r := by
  classical
  let c : Fin n := ⟨0, hn⟩
  let H := ((Finset.univ : Finset (Fin n)).powersetCard r).filter ({c} ⊆ ·)
  have hcard : H.card = (n-1).choose (r-1) := by
    simpa [H] using Finset.card_filter_powersetCard_subset ({c} : Finset (Fin n))
      Finset.univ r (by simp) (by simpa using hr)
  have hfree : ¬ H.HasRepeatedDisjointUnion := by
    rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, _⟩
    have ha : c ∈ A := (Finset.mem_filter.mp hA).2 (by simp)
    have hb : c ∈ B := (Finset.mem_filter.mp hB).2 (by simp)
    exact Finset.disjoint_left.mp hAB ha hb
  rw [← hcard, forcingThreshold]
  apply Nat.le_succ_of_le
  unfold Hypergraph.extremalNumber
  apply Finset.le_sup (b := H)
  have hmem : H ∈ ((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter
      (fun K ↦ ¬ K.HasRepeatedDisjointUnion) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hfree⟩
  simpa using hmem

end Erdos643Star

namespace OMA.R_Erdos643_erdos_643_parts_ii_R2

open Filter Asymptotics Erdos643 Erdos643Star

private theorem rank_three_limit
    (h3 : ∀ n : ℕ, Hypergraph.extremalNumber n 3 (fun H ↦ ¬ H.HasRepeatedDisjointUnion) ≤ n.choose 2) :
    (fun n ↦ (forcingThreshold n 3 : ℝ)) ~[atTop] (fun n ↦ (n.choose (3 - 1) : ℝ)) := by
  have hz := linear_error_choose_ratio_tendsto_zero 2 (by decide)
    (fun n => n+1) (Eventually.of_forall fun _ => le_rfl)
  have hu := (tendsto_const_nhds (x := (1 : ℝ))).add hz
  rw [add_zero] at hu
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (shifted_choose_ratio_tendsto_one 2) hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    change ((n-1).choose 2 : ℝ) ≤ (forcingThreshold n 3 : ℝ)
    exact_mod_cast star_lower 3 n (by decide) hn
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hp : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
    change (forcingThreshold n 3 : ℝ) / _ ≤ 1 + ((n+1 : ℕ) : ℝ) / _
    rw [← div_self hp.ne', ← add_div]
    apply div_le_div_of_nonneg_right _ hp.le
    have h := h3 n
    rw [forcingThreshold]
    exact_mod_cast (show _ ≤ n.choose 2 + (n+1) by omega)

def H1 : Prop :=
  ∀ n : ℕ, Hypergraph.extremalNumber n 3
    (fun H ↦ ¬ H.HasRepeatedDisjointUnion) ≤ n.choose 2

def H2 : Prop :=
  ∀ d : ℕ, (fun n : ℕ ↦ (forcingThreshold n (d+4) : ℝ)) ~[atTop]
    (fun n ↦ (n.choose (d+3) : ℝ))

-- Credit: @MrSeizy
theorem main : H1 → H2 → type_of% @Erdos643.erdos_643.parts.ii := by
  intro h3 h4 r hr
  by_cases he : r = 3
  · subst r
    exact rank_three_limit h3
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ r by omega)
  rw [add_comm 4 d]
  simpa [show d+4-1=d+3 by omega] using h4 d

end OMA.R_Erdos643_erdos_643_parts_ii_R2
