import OMAStatements.S_oeis_a206912
import Mathlib

namespace OMA.S_oeis_a206912

lemma H_mono {j k : ℕ} (h : j ≤ k) : (harmonic j : ℝ) ≤ harmonic k := by
  have : harmonic j ≤ harmonic k := by
    induction k, h using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
      refine ih.trans ?_
      rw [harmonic_succ]
      have : (0:ℚ) ≤ ((k+1 : ℕ) : ℚ)⁻¹ := by positivity
      linarith
  exact_mod_cast this

lemma H_ge (n : ℕ) : Real.log ((n:ℝ) + 1) ≤ (harmonic n : ℝ) := by
  have := log_add_one_le_harmonic n
  simpa using this

lemma fin_S (n : ℕ) : {j : ℕ | 1 ≤ j ∧ (harmonic j : ℝ) < Real.log (n + 1)}.Finite := by
  refine (Set.finite_lt_nat n).subset ?_
  intro j hj
  simp only [Set.mem_setOf_eq] at hj ⊢
  by_contra hc
  push_neg at hc
  have := H_mono hc
  have := H_ge n
  linarith [hj.2]

lemma sub_single (n : ℕ) :
    {j : ℕ | 1 ≤ j ∧ Real.log ((n:ℝ) + 1) ≤ (harmonic j : ℝ) ∧ (harmonic j : ℝ) < Real.log ((n+1 : ℕ) + 1)}.Subsingleton := by
  have key : ∀ j k : ℕ, j < k → 1 ≤ j → Real.log ((n:ℝ) + 1) ≤ (harmonic j : ℝ) →
      (harmonic k : ℝ) < Real.log (((n+1 : ℕ) : ℝ) + 1) → False := by
    intro j k hjk hj1 h1 h2
    have hk : (harmonic (j+1) : ℝ) ≤ harmonic k := H_mono hjk
    have hs : (harmonic (j+1) : ℝ) = harmonic j + 1 / ((j:ℝ)+1) := by
      rw [harmonic_succ]; push_cast; ring
    have hlog : Real.log (((n+1 : ℕ) : ℝ) + 1) - Real.log ((n:ℝ) + 1) ≤ 1 / ((n:ℝ)+1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (x := (((n+1 : ℕ) : ℝ) + 1) / ((n:ℝ) + 1)) (by positivity)
      have e : (((n+1 : ℕ) : ℝ) + 1) / ((n:ℝ) + 1) - 1 = 1 / ((n:ℝ)+1) := by
        push_cast; field_simp; ring
      linarith
    have h3 : 1 / ((j:ℝ)+1) < 1 / ((n:ℝ)+1) := by linarith
    have h4 : (n:ℝ) + 1 < (j:ℝ) + 1 := by
      by_contra hc; push_neg at hc
      have := one_div_le_one_div_of_le (by positivity) hc
      linarith
    have h5 : n + 1 ≤ j := by
      have : (n:ℝ) < j := by linarith
      exact_mod_cast this
    have h6 := H_mono (le_trans h5 hjk.le)
    have h7 := H_ge (n+1)
    linarith
  intro j hj k hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key j k h hj.1 hj.2.1 hk.2.2
  · exact key k j h hk.1 hk.2.1 hj.2.2

theorem main_aux : type_of% @OMA.S_oeis_a206912.main := by
  intro n hn
  unfold a
  set S : ℕ → Set ℕ := fun m => {j : ℕ | 1 ≤ j ∧ (harmonic j : ℝ) < Real.log (m + 1)} with hS
  have hmono : S n ⊆ S (n+1) := by
    intro j hj
    simp only [hS, Set.mem_setOf_eq] at hj ⊢
    refine ⟨hj.1, lt_of_lt_of_le hj.2 (Real.log_le_log (by positivity) (by push_cast; linarith))⟩
  have h1 : (S n).ncard ≤ (S (n+1)).ncard := Set.ncard_le_ncard hmono (fin_S _)
  have hunion : S (n+1) ⊆ S n ∪ {j : ℕ | 1 ≤ j ∧ Real.log ((n:ℝ) + 1) ≤ (harmonic j : ℝ) ∧ (harmonic j : ℝ) < Real.log ((n+1 : ℕ) + 1)} := by
    intro j hj
    simp only [hS, Set.mem_setOf_eq, Set.mem_union] at hj ⊢
    by_cases h : (harmonic j : ℝ) < Real.log (n + 1)
    · exact Or.inl ⟨hj.1, h⟩
    · exact Or.inr ⟨hj.1, not_lt.mp h, by exact_mod_cast hj.2⟩
  have h2 : (S (n+1)).ncard ≤ (S n).ncard + 1 := by
    calc (S (n+1)).ncard ≤ (S n ∪ _).ncard := Set.ncard_le_ncard hunion ((fin_S n).union ((fin_S (n+1)).subset (by
            intro j hj; exact ⟨hj.1, hj.2.2⟩)))
      _ ≤ (S n).ncard + _ := Set.ncard_union_le _ _
      _ ≤ (S n).ncard + 1 := by
          have hf := (sub_single n).finite
          haveI : Finite _ := hf.to_subtype
          have := Set.ncard_le_one_iff_subsingleton.mpr (sub_single n)
          omega
  show n + 1 + (S (n+1)).ncard = n + (S n).ncard + 1 ∨ n + 1 + (S (n+1)).ncard = n + (S n).ncard + 2
  omega

end OMA.S_oeis_a206912

theorem OMA.solution : type_of% @OMA.S_oeis_a206912.main := OMA.S_oeis_a206912.main_aux
