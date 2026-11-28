import FormalConjectures.ErdosProblems.«422»
import Mathlib

-- Credit: @Iraeeee

open Filter

namespace HofstadterGrowth

/-- Looking one step ahead bounds the current value by its index. -/
theorem le_index (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f) (n : ℕ+) : f n ≤ n := by
  by_cases hn : n = 1
  · simp [hn, hf.1]
  have h : (2 : ℕ+) < n + 1 := by
    change 2 < (n : ℕ) + 1
    have := n.pos
    have hn' : (n : ℕ) ≠ 1 := fun e => hn (PNat.eq e)
    omega
  have hprev := (hf.2.2 (n + 1) h).1
  rw [PNat.add_sub] at hprev
  change (f n : ℕ) < (n : ℕ) + 1 at hprev
  exact Nat.le_of_lt_succ hprev

end HofstadterGrowth

noncomputable def OMA.answer : ℕ+ → ℝ := fun n => n

theorem OMA.solution : Erdos422.erdos_422.variants.growth_rate.answer = OMA.answer → type_of% @Erdos422.erdos_422.variants.growth_rate := by
  intro h f hf
  rw [h]
  apply Asymptotics.IsBigO.of_bound 1
  exact Filter.Eventually.of_forall fun n => by
    have hl : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast HofstadterGrowth.le_index f hf n
    simpa [OMA.answer, Real.norm_eq_abs] using hl
