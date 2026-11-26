import FormalConjectures.ErdosProblems.«142»

/-!
# Quantitative arithmetic-progression bounds implying the logarithmic little-o bound

The three-term case uses the quantitative Roth theorem of Kelley and Meka. The longer
progressions require a separate estimate. A positive power saving over the logarithm
suffices in each case.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- The logarithmic power saving for three-term progression-free sets. -/
def H1 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
    (r 3 N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε)

/-- A logarithmic power saving for each fixed progression length at least four. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε)

lemma card_bound_two (N : ℕ) : r 2 N ≤ 1 := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro A hA hAP
    have hEmpty : A = ∅ := Set.subset_empty_iff.mp (by simpa using hA)
    exact (Set.not_isAPOfLength_empty (by decide) (hEmpty ▸ hAP)).elim
  · rintro m ⟨A, _, hA, rfl⟩
    by_contra! hLarge
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hLarge
    have hf (x y : ℕ) (hx : x ∈ A) (hy : y ∈ A) (hxy : x < y) : False := by
      have hSub : ({x, y} : Set ℕ) ⊆ (A : Set ℕ) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hTwo := hA _ hSub (Nat.isAPOfLength_pair hxy)
      exact (by decide : ¬ ((2 : ℕ) : ℕ∞) ≤ 1) hTwo
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hf a b ha hb hlt
    · exact hf b a hb ha hgt

lemma of_power_saving (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᶠ N : ℕ in atTop, (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε)) :
    (fun N ↦ (r k N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  have hLog : Tendsto (fun N : ℕ ↦ log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPow : Tendsto (fun N : ℕ ↦ log (N : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp hLog
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hbound, hLog.eventually (eventually_gt_atTop (0 : ℝ)),
    hPow.eventually (gt_mem_nhds hc)] with N hN hLogN hSmall
  have hPos : 0 < log (N : ℝ) := hLogN
  have hNN : 0 ≤ (N : ℝ) / log (N : ℝ) := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hNN]
  calc
    (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ (1 + ε) := hN
    _ = log (N : ℝ) ^ (-ε) * ((N : ℝ) / log (N : ℝ)) := by
      rw [rpow_add hPos, rpow_one, rpow_neg hPos.le]
      field_simp
    _ ≤ c * ((N : ℝ) / log (N : ℝ)) := mul_le_mul_of_nonneg_right hSmall.le hNN

lemma two_littleO :
    (fun N ↦ (r 2 N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  have hT : Tendsto (fun N : ℕ ↦ log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hT.eventually (gt_mem_nhds hc), eventually_gt_atTop (1 : ℕ)] with N hN hLarge
  have hOne : 1 < (N : ℝ) := by exact_mod_cast hLarge
  have hPos : 0 < log (N : ℝ) := log_pos hOne
  have hNat : 0 < (N : ℝ) := zero_lt_one.trans hOne
  have hcard : (r 2 N : ℝ) ≤ 1 := by exact_mod_cast card_bound_two N
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  apply hcard.trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hPos).mpr
  simpa using ((div_lt_iff₀ hNat).mp hN).le

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.lower := by
  intro hThree hLong k hk
  by_cases hs : k = 2
  · subst k
    exact two_littleO
  by_cases hs' : k = 3
  · subst k
    obtain ⟨ε, hε, hbound⟩ := hThree
    exact of_power_saving 3 ε hε hbound
  · obtain ⟨ε, hε, hbound⟩ := hLong k (by omega)
    exact of_power_saving k ε hε hbound

end OMA.R_Erdos142_erdos_142_variants_lower_R1
