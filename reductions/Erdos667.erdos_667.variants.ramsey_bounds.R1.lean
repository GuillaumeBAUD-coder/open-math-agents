import FormalConjectures.ErdosProblems.«667»

/-!
# Finite graph estimates for the Ramsey bounds of Erdős Problem 667

Credit: @DarkWingMcQuack.
-/

namespace OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1

open Erdos667 Filter Real SimpleGraph

/-- Every sufficiently large locally dense graph contains a clique of the lower-bound size. -/
def H1 : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∀ a : ℝ, a < 1 / ((p : ℝ) - 1) →
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, m ≤ n ∧ (n : ℝ) ^ a ≤ (m : ℝ) ∧
      ∀ G : SimpleGraph (Fin n), LocallyDense p 1 G → ¬ G.CliqueFree m

/-- Arbitrarily large locally dense graphs exist with clique number at most the upper-bound
size. -/
def H2 : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∀ b : ℝ, 2 / ((p : ℝ) + 1) < b →
    ∃ᶠ n : ℕ in atTop, ∃ (m : ℕ) (G : SimpleGraph (Fin n)),
      (m : ℝ) ≤ (n : ℝ) ^ b ∧ LocallyDense p 1 G ∧ G.CliqueFree (m + 1)

lemma one_le_H (p : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ H p 1 n := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold H
  refine Nat.le_findGreatest hn ?_
  intro G _
  rw [cliqueFree_one]
  exact not_isEmpty_of_nonempty _

lemma H_le_of_cliqueFree {p n m : ℕ} {G : SimpleGraph (Fin n)}
    (hDense : LocallyDense p 1 G) (hFree : G.CliqueFree (m + 1)) : H p 1 n ≤ m := by
  classical
  have hSpec : ∀ G' : SimpleGraph (Fin n), LocallyDense p 1 G' →
      ¬ G'.CliqueFree (H p 1 n) := by
    unfold H
    apply Nat.findGreatest_spec (P := fun k ↦
      ∀ G' : SimpleGraph (Fin n), LocallyDense p 1 G' → ¬ G'.CliqueFree k)
      (m := 0) (Nat.zero_le n)
    simp
  by_contra! h
  exact hSpec G hDense (hFree.mono (by omega))

theorem main : H1 → H2 → type_of% @Erdos667.erdos_667.variants.ramsey_bounds := by
  classical
  intro hLower hUpper p hp
  let ratio (n : ℕ) := log (H p 1 n) / log n
  have hLarge : ∀ᶠ n : ℕ in atTop, 1 < n := eventually_gt_atTop 1
  have hNonneg : atTop.IsBoundedUnder (· ≥ ·) ratio := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ ratio n
    filter_upwards [hLarge] with n hn
    have hOne : 1 ≤ (H p 1 n : ℝ) := by exact_mod_cast one_le_H p hn.le
    have hLog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn.le)
    exact div_nonneg (log_nonneg hOne) hLog
  have hBounded : atTop.IsBoundedUnder (· ≤ ·) ratio := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n in atTop, ratio n ≤ 1
    filter_upwards [hLarge] with n hn
    have hLog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn)
    have hHpos : 0 < (H p 1 n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_H p hn.le))
    have hHle : (H p 1 n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.findGreatest_le (P := fun m ↦
        ∀ G : SimpleGraph (Fin n), LocallyDense p 1 G → ¬ G.CliqueFree m) n
    exact (div_le_one hLog).mpr (log_le_log hHpos hHle)
  change 1 / ((p : ℝ) - 1) ≤ liminf ratio atTop ∧
    liminf ratio atTop ≤ 2 / ((p : ℝ) + 1)
  refine ⟨(le_liminf_iff' hBounded.isCoboundedUnder_ge hNonneg).mpr ?_,
    (liminf_le_iff' hBounded.isCoboundedUnder_ge hNonneg).mpr ?_⟩
  · intro a ha
    filter_upwards [hLarge, hLower p hp a ha] with n hn hWitness
    obtain ⟨m, hmn, hPower, hGraph⟩ := hWitness
    have hml : (m : ℝ) ≤ (H p 1 n : ℝ) := by
      exact_mod_cast Nat.le_findGreatest hmn hGraph
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hn
    have hnPos : 0 < (n : ℝ) := zero_lt_one.trans hnReal
    apply (le_div_iff₀ (log_pos hnReal)).mpr
    rw [← log_rpow hnPos]
    exact log_le_log (rpow_pos_of_pos hnPos _) (hPower.trans hml)
  · intro b hb
    refine ((hUpper p hp b hb).and_eventually hLarge).mono ?_
    rintro n ⟨⟨m, G, hPower, hDense, hFree⟩, hn⟩
    have hHle : (H p 1 n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast H_le_of_cliqueFree hDense hFree
    have hHpos : 0 < (H p 1 n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_H p hn.le))
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hn
    have hnPos : 0 < (n : ℝ) := zero_lt_one.trans hnReal
    apply (div_le_iff₀ (log_pos hnReal)).mpr
    rw [← log_rpow hnPos]
    exact log_le_log hHpos (hHle.trans hPower)

end OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1
