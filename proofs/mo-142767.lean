import OMAStatements.S_mo_142767
import Mathlib

/-! Moving point masses. This formalizes Davide Giraudo's counterexample
on MathOverflow, question 142767, shifting the index to start at zero. -/
open MeasureTheory Filter Set OMA.S_mo_142767
open scoped Topology ENNReal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_142767.main) := by
  intro H
  let u (n : ℕ) : Fin 1 → ℝ := fun _ => 1 / ((n:ℝ)+1)
  have cu : Tendsto u atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have nz (n:ℕ) : u n ≠ 0 := by
    intro h
    have eq := congrFun h (0 : Fin 1)
    change (1:ℝ)/((n:ℝ)+1)=0 at eq
    exact (ne_of_gt (by positivity)) eq
  let μ (n:ℕ) := Measure.dirac (u n)
  let ν := Measure.dirac (0 : Fin 1 → ℝ)
  have weak : IntegralsConverge μ ν := by
    intro f hf
    simpa only [μ,ν,integral_dirac,Function.comp_def] using (hf.continuous.tendsto (0 : Fin 1 → ℝ)).comp cu
  have bad := H 1 μ ν weak {0} (measurableSet_singleton _)
  have lhs (n:ℕ) : μ n {0}=0 := by simp [μ,nz n]
  have rhs : ν {0}=1 := Measure.dirac_apply_of_mem (Set.mem_singleton _)
  simp only [lhs,rhs] at bad
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds bad)
