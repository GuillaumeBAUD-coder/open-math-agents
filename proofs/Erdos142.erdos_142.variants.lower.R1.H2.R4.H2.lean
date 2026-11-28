import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R4
import Mathlib

-- Pre-verified proof of PR #37114 H2 (Erdos142.erdos_142.variants.lower.R1.H2.R4.H2)
-- Credit: @DPS0340

theorem test_37114_H2 :
    ∀ (k : ℕ), 3 ≤ k → ∀ (B : ℕ → Finset ℕ), (∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) →
      (∀ j, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j) →
      ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, ∃ j b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b := by
  intro k hk B hB hfree
  rintro ⟨a, d, hd, hAP⟩
  have hblk : ∀ i < k, ∃ j, 4 * 4 ^ j < a + i * d ∧ a + i * d ≤ 5 * 4 ^ j := by
    intro i hi
    obtain ⟨j, b, hb, heq⟩ := hAP i hi
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp (hB j hb)
    exact ⟨j, by omega, by omega⟩
  choose j hj_lo hj_hi using hblk
  have hmono : ∀ i₁ i₂ (h₁ : i₁ < k) (h₂ : i₂ < k), i₁ < i₂ → j i₁ h₁ ≤ j i₂ h₂ := by
    intro i₁ i₂ h₁ h₂ hlt
    by_contra hgt
    push Not at hgt
    have hpow : 4 * 4 ^ j i₂ h₂ ≤ 4 ^ j i₁ h₁ := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) (show j i₂ h₂ + 1 ≤ j i₁ h₁ by omega)
      rw [Nat.pow_succ, Nat.mul_comm] at this
      exact this
    have h1 := hj_lo i₁ h₁
    have h2 := hj_hi i₂ h₂
    have hstep : a + i₁ * d < a + i₂ * d := by nlinarith
    omega
  have hsame : ∀ i (hi : i + 2 < k), j i (by omega) = j (i + 1) (by omega) ∧
      j (i + 1) (by omega) = j (i + 2) (by omega) := by
    intro i hi
    have h01 : j i (by omega) ≤ j (i + 1) (by omega) := hmono i (i + 1) _ _ (by omega)
    have h12 : j (i + 1) (by omega) ≤ j (i + 2) (by omega) := hmono (i + 1) (i + 2) _ _ (by omega)
    have heq12 : j (i + 1) (by omega) = j (i + 2) (by omega) := by
      by_contra hne
      have hpow : 4 * 4 ^ j (i + 1) (by omega) ≤ 4 ^ j (i + 2) (by omega) := by
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4)
          (show j (i + 1) (by omega) + 1 ≤ j (i + 2) (by omega) by omega)
        rw [Nat.pow_succ, Nat.mul_comm] at this
        exact this
      have hlo2 := hj_lo (i + 2) hi
      have hhi1 := hj_hi (i + 1) (by omega)
      have hlin : (a + (i + 2) * d) + (a + i * d) = 2 * (a + (i + 1) * d) := by ring
      omega
    have heq01 : j i (by omega) = j (i + 1) (by omega) := by
      by_contra hne
      have hpow : 4 * 4 ^ j i (by omega) ≤ 4 ^ j (i + 1) (by omega) := by
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4)
          (show j i (by omega) + 1 ≤ j (i + 1) (by omega) by omega)
        rw [Nat.pow_succ, Nat.mul_comm] at this
        exact this
      have hhi0 := hj_hi i (by omega)
      have hlo1 := hj_lo (i + 1) (by omega)
      have hhi2 := hj_hi (i + 2) hi
      rw [← heq12] at hhi2
      have hlin : (a + (i + 2) * d) + (a + i * d) = 2 * (a + (i + 1) * d) := by ring
      omega
    exact ⟨heq01, heq12⟩
  let j₀ := j 0 (by omega)
  have hall : ∀ i (hi : i < k), j i hi = j₀ := by
    intro i hi
    induction i with
    | zero => rfl
    | succ m ih =>
      rcases m with _ | m'
      · exact (hsame 0 (by omega)).1.symm
      · have hprev := ih (by omega)
        have hstep := (hsame m' (by omega)).2
        exact hstep.symm.trans hprev
  have hmemB : ∀ i (hi : i < k), a + i * d - 4 * 4 ^ j₀ ∈ B j₀ := by
    intro i hi
    obtain ⟨ji, bi, hbi, heq⟩ := hAP i hi
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp (hB ji hbi)
    have hji_eq : ji = j₀ := by
      have hj_i := hall i hi
      have hlo := hj_lo i hi
      have hhi := hj_hi i hi
      rw [hj_i] at hlo hhi
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 4 * 4 ^ ji ≤ 4 ^ j₀ := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) (show ji + 1 ≤ j₀ by omega)
          rw [Nat.pow_succ, Nat.mul_comm] at this
          exact this
        omega
      · have hpow : 4 * 4 ^ j₀ ≤ 4 ^ ji := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) (show j₀ + 1 ≤ ji by omega)
          rw [Nat.pow_succ, Nat.mul_comm] at this
          exact this
        omega
    subst hji_eq
    have : a + i * d - 4 * 4 ^ j₀ = bi := by omega
    rwa [this]
  apply hfree j₀
  refine ⟨a - 4 * 4 ^ j₀, d, hd, fun i hi => ?_⟩
  have hlo0 : 4 * 4 ^ j₀ < a := by
    have := hj_lo 0 (by omega)
    simpa [j₀] using this
  have heq : a - 4 * 4 ^ j₀ + i * d = a + i * d - 4 * 4 ^ j₀ := by omega
  rw [heq]
  exact hmemB i hi

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4.H2 := test_37114_H2
