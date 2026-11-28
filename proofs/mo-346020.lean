import OMAStatements.S_mo_346020
import Mathlib

-- Problem: Is $|f^{-1}f(p)|$ constant on a conull set?
-- Upstream: formal-conjectures statements/mo-346020.lean:0 (declaration OMA.S_mo_346020.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Set MeasureTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_346020.main) := by
  intro h
  let f : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x _ => x 0 ^ 3 - 3 * x 0
  have hf : AnalyticOnNhd ℝ f univ := by
    intro x _
    have h0 : AnalyticAt ℝ (fun y : Fin 1 → ℝ => y 0) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).analyticAt x
    rw [analyticAt_pi_iff]
    intro i
    exact (h0.pow 3).sub (analyticAt_const.mul h0)
  obtain ⟨U, hU, hcard⟩ := h 1 1 f hf
  have key : ∀ a b : ℝ, a < b → ∃ p ∈ U, a < p 0 ∧ p 0 < b := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have hsub : (Set.pi univ (fun _ : Fin 1 => Ioo a b)) ⊆ Uᶜ := by
      intro p hp hpU
      have hp0 : p 0 ∈ Ioo a b := hp 0 (mem_univ _)
      exact absurd hp0.2 (not_lt.mpr (hcon p hpU hp0.1))
    have hvol : volume (Set.pi univ (fun _ : Fin 1 => Ioo a b)) = ENNReal.ofReal (b - a) := by
      have h1 := Real.volume_pi_Ioo (a := fun _ : Fin 1 => a) (b := fun _ => b)
      simpa using h1
    have h2 := measure_mono (μ := volume) hsub
    rw [hU, hvol] at h2
    have h3 : ENNReal.ofReal (b - a) = 0 := le_antisymm h2 zero_le
    rw [ENNReal.ofReal_eq_zero] at h3
    linarith
  obtain ⟨p, hpU, hp1, hp2⟩ := key 0 1 one_pos
  obtain ⟨q, hqU, hq1, hq2⟩ := key 3 4 (by norm_num)
  have hc := hcard p hpU q hqU
  have hq : (OMA.S_mo_346020.AnalyticFibre f q).Subsingleton := by
    have hall : ∀ x ∈ OMA.S_mo_346020.AnalyticFibre f q, x = q := by
      intro x hx
      have hx0 : x 0 ^ 3 - 3 * x 0 = q 0 ^ 3 - 3 * q 0 := congrFun hx 0
      have hxq : x 0 = q 0 := by
        by_contra hne
        have hne' : x 0 - q 0 ≠ 0 := sub_ne_zero.mpr hne
        have hfac : (x 0 - q 0) * (x 0 ^ 2 + q 0 * x 0 + q 0 ^ 2 - 3) = 0 := by
          have e : (x 0 - q 0) * (x 0 ^ 2 + q 0 * x 0 + q 0 ^ 2 - 3)
              = (x 0 ^ 3 - 3 * x 0) - (q 0 ^ 3 - 3 * q 0) := by ring
          rw [e, hx0]
          ring
        rcases mul_eq_zero.mp hfac with h1 | h1
        · exact hne' h1
        · have hq9 : 9 < q 0 ^ 2 := by nlinarith
          nlinarith [sq_nonneg (x 0 + q 0 / 2)]
      funext i
      fin_cases i
      exact hxq
    intro x hx y hy
    rw [hall x hx, hall y hy]
  have hp : (OMA.S_mo_346020.AnalyticFibre f p).Nontrivial := by
    set s := Real.sqrt (12 - 3 * p 0 ^ 2) with hs
    have hpp : p 0 ^ 2 < 1 := by nlinarith
    have hs3 : 3 ≤ s := (Real.le_sqrt' (by norm_num)).mpr (by nlinarith)
    have hsq : s ^ 2 = 12 - 3 * p 0 ^ 2 := Real.sq_sqrt (by nlinarith)
    refine ⟨p, rfl, (fun _ => (-p 0 + s) / 2), ?_, ?_⟩
    · funext i
      show ((-p 0 + s) / 2) ^ 3 - 3 * ((-p 0 + s) / 2) = p 0 ^ 3 - 3 * p 0
      have e : ((-p 0 + s) / 2) ^ 3 - 3 * ((-p 0 + s) / 2) - (p 0 ^ 3 - 3 * p 0)
          = ((-p 0 + s) / 2 - p 0) * ((s ^ 2 + 3 * p 0 ^ 2 - 12) / 4) := by ring
      rw [hsq] at e
      have e2 : ((-p 0 + s) / 2 - p 0) * ((12 - 3 * p 0 ^ 2 + 3 * p 0 ^ 2 - 12) / 4) = 0 := by
        ring
      linarith
    · intro heq
      have h3 : p 0 = (-p 0 + s) / 2 := congrFun heq 0
      linarith
  have h1 : Cardinal.mk (OMA.S_mo_346020.AnalyticFibre f q) ≤ 1 :=
    Cardinal.mk_le_one_iff_set_subsingleton.mpr hq
  have h2 : 1 < Cardinal.mk (OMA.S_mo_346020.AnalyticFibre f p) := by
    rw [Cardinal.one_lt_iff_nontrivial]
    exact Set.nontrivial_coe_sort.mpr hp
  rw [hc] at h2
  exact absurd h1 (not_le.mpr h2)
