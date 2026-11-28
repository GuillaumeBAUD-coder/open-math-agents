import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1
import Mathlib.Algebra.Order.Round
import Mathlib.Order.LiminfLimsup

-- Credit: @marcusbuffett. The proof is elementary: |x - round x| ≤ 1/2 and nonnegativity give the bound.

open Filter

theorem OMA.solution : OMA.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1.H1 := by
  intro α β hα
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _)) (distToNearestInt_nonneg _)
  have hfreq : ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) < ε := by
    intro ε hε
    refine (hα (2 * ε) (by linarith)).mono ?_
    intro n hn
    have hx : 0 ≤ (n : ℝ) * distToNearestInt (n * α) :=
      mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _)
    have hd : distToNearestInt ((n : ℝ) * β) ≤ 1 / 2 := abs_sub_round _
    have := mul_le_mul_of_nonneg_left hd hx
    linarith
  have hle : ∀ ε : ℝ, 0 < ε →
      atTop.liminf (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) ≤ ε :=
    fun ε hε => Filter.liminf_le_of_frequently_le
      ((hfreq ε hε).mono fun n hn => hn.le) (Filter.isBoundedUnder_of ⟨0, fun n => hnn n⟩)
  have hge : 0 ≤ atTop.liminf (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) := by
    apply Filter.le_liminf_of_le
    · refine ⟨0, fun a ha => ?_⟩
      by_contra hneg
      push Not at hneg
      obtain ⟨n, hn1, hn2⟩ :=
        ((hfreq a hneg).and_eventually (Filter.eventually_map.1 ha)).exists
      linarith
    · exact Filter.Eventually.of_forall fun n => hnn n
  have hle0 : atTop.liminf (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by
      have := hle ε hε
      linarith
  exact le_antisymm hle0 hge
