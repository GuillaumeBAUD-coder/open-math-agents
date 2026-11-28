import OMAReductions.R_Erdos1056_erdos_1056_R1_H3_R1
import Mathlib

-- Step Erdos1056.erdos_1056.R1.H3.R1.H1: hypothesis H1 of reduction Erdos1056.erdos_1056.R1.H3.R1
-- Credit: @Raimo33

def pm (p a : ℕ) : ℕ → ℕ
  | 0 => 1 % p
  | len + 1 => (pm p a len * (a + len)) % p

lemma prod_mod_eq (p a : ℕ) : ∀ len, (∏ n ∈ Finset.Ico a (a + len), n) % p = pm p a len
  | 0 => by simp [pm]
  | len + 1 => by
    rw [show a + (len + 1) = (a + len) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
      Nat.mul_mod, prod_mod_eq p a len, pm, Nat.mul_mod (pm p a len) (a + len), Nat.mod_mul_mod]

lemma modeq_of_pm (p a c : ℕ) (hac : a ≤ c) (h : pm p a (c - a) = 1 % p) :
    (∏ n ∈ Finset.Ico a c, n) ≡ 1 [MOD p] := by
  have := prod_mod_eq p a (c - a)
  rw [Nat.add_sub_cancel' hac] at this
  unfold Nat.ModEq
  rw [this, h]

theorem OMA.solution : OMA.R_Erdos1056_erdos_1056_R1_H3_R1.H1 := by
  intro k hk4 hk12
  interval_cases k
  · refine ⟨17, by norm_num, ![1, 2, 6, 12, 16], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨23, by norm_num, ![1, 2, 5, 9, 12, 22], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨71, by norm_num, ![8, 10, 20, 52, 62, 64, 71], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨599, by norm_num, ![29, 51, 123, 184, 251, 290, 501, 540], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨599, by norm_num, ![29, 51, 123, 184, 251, 290, 501, 540, 556], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨3011, by norm_num, ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨3011, by norm_num, ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨52163, by norm_num, ![1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644,
      44736, 44872], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
  · refine ⟨52163, by norm_num, ![1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644,
      44736, 44872, 52162], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]; decide
    · intro i; fin_cases i <;> exact modeq_of_pm _ _ _ (by decide) (by decide +kernel)
