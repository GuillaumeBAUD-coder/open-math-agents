import FormalConjectures.ErdosProblems.«142»

/-!
# A two-hypothesis reduction of the logarithmic little-o bound

One quantitative input for every progression length at least three (a power saving
over the logarithm) plus the elementary length-two estimate imply that r_k(N) is
little-o of N / log N for every k > 1. The reduction keeps the two inputs separate:
the first is the deep Szemeredi-type estimate, the second is a one-line combinatorial
fact about two-term progressions.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R4

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- A quantitative power saving beyond one logarithm for every length at least three. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε)

/-- A two-term-progression-free subset of an interval has at most one element. -/
def H2 : Prop :=
  ∀ N : ℕ, r 2 N ≤ 1

lemma power_saving_to_littleO (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε)) :
    (fun N ↦ (r k N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  have hLog : Tendsto (fun N : ℕ ↦ log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSmall : Tendsto (fun N : ℕ ↦ log (N : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp hLog
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hbound, hLog.eventually (eventually_gt_atTop (0 : ℝ)),
    hSmall.eventually (gt_mem_nhds hc)] with N hN hLogN hfactor
  have hPos : 0 < log (N : ℝ) := hLogN
  have hNonneg : 0 ≤ (N : ℝ) / log (N : ℝ) := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hNonneg]
  calc
    (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε) := hN
    _ = log (N : ℝ) ^ (-ε) * ((N : ℝ) / log (N : ℝ)) := by
      rw [rpow_add hPos, rpow_one, rpow_neg hPos.le]
      field_simp
    _ ≤ c * ((N : ℝ) / log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor.le hNonneg

lemma constant_one_is_littleO :
    (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  have hlim : Tendsto (fun N : ℕ ↦ log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hp : 0 < (N : ℝ) / log (N : ℝ) := div_pos (by positivity) (log_pos hN1)
    exact fun h => (hp.ne' h).elim
  · simpa only [one_div, inv_div] using hlim

lemma length_two_is_littleO (hTwo : H2) :
    (fun N ↦ (r 2 N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  apply IsBigO.trans_isLittleO _ constant_one_is_littleO
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun N => by
    simpa using (show (r 2 N : ℝ) ≤ 1 by exact_mod_cast hTwo N)

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.lower := by
  intro hQuant hTwo k hk
  by_cases hk2 : k = 2
  · subst k
    exact length_two_is_littleO hTwo
  obtain ⟨ε, hε, hbound⟩ := hQuant k (by omega)
  exact power_saving_to_littleO k ε hε hbound

end OMA.R_Erdos142_erdos_142_variants_lower_R4
