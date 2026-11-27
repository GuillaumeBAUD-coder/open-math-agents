import OMAStatements.S_mo_481044
import Mathlib

-- Problem: mo-481044, an explicit smooth, space-periodic, time-dependent, pressureless
-- solution of the incompressible Euler equations in dimension d >= 2.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- A travelling shear flow: u_0 = 1, u_1 = sin(2 pi (x_0 - t)), and all other components 0.
-- Then u_1 is transported by the constant velocity u_0 = 1, the divergence vanishes because
-- u_1 does not depend on x_1, and the time derivative of u_1 is not identically zero.

namespace MO481044

noncomputable def U {d : ℕ} (i0 i1 : Fin d) (t : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i = i0 then 1 else if i = i1 then Real.sin (2 * Real.pi * (x i0 - t)) else 0

lemma dt {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) (x : Fin d → ℝ) (t : ℝ) (i : Fin d) :
    deriv (fun s => U i0 i1 s x i) t
      = if i = i1 then -(2 * Real.pi) * Real.cos (2 * Real.pi * (x i0 - t)) else 0 := by
  by_cases hi0 : i = i0
  · have hi1 : i ≠ i1 := fun h => h01 (hi0.symm.trans h)
    have e : (fun s => U i0 i1 s x i) = fun _ => (1 : ℝ) := by
      funext s
      simp [U, hi0]
    rw [e, if_neg hi1, deriv_const]
  · by_cases hi1 : i = i1
    · have e : (fun s => U i0 i1 s x i) = fun s => Real.sin (2 * Real.pi * (x i0 - s)) := by
        funext s
        simp only [U]
        rw [if_neg hi0, if_pos hi1]
      rw [e, if_pos hi1]
      have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (x i0 - s)) (2 * Real.pi * (-1)) t :=
        ((hasDerivAt_id t).const_sub (x i0)).const_mul (2 * Real.pi)
      have h2 := h1.sin
      rw [h2.deriv]
      ring
    · have e : (fun s => U i0 i1 s x i) = fun _ => (0 : ℝ) := by
        funext s
        simp [U, hi0, hi1]
      rw [e, if_neg hi1, deriv_const]

lemma dx {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) (t : ℝ) (x : Fin d → ℝ) (i j : Fin d) :
    OMA.S_mo_481044.partialSpace (U i0 i1) t x i j
      = if i = i1 ∧ j = i0 then 2 * Real.pi * Real.cos (2 * Real.pi * (x i0 - t)) else 0 := by
  unfold OMA.S_mo_481044.partialSpace
  by_cases hi0 : i = i0
  · have hi1 : i ≠ i1 := fun h => h01 (hi0.symm.trans h)
    have e : (fun r => U i0 i1 t (Function.update x j r) i) = fun _ => (1 : ℝ) := by
      funext r
      simp [U, hi0]
    rw [e, deriv_const, if_neg (fun h => hi1 h.1)]
  · by_cases hi1 : i = i1
    · by_cases hj : j = i0
      · have e : (fun r => U i0 i1 t (Function.update x j r) i)
            = fun r => Real.sin (2 * Real.pi * (r - t)) := by
          funext r
          simp only [U]
          rw [if_neg hi0, if_pos hi1, hj, Function.update_self]
        rw [e, if_pos ⟨hi1, hj⟩, hj]
        have h1 : HasDerivAt (fun r : ℝ => 2 * Real.pi * (r - t)) (2 * Real.pi * 1) (x i0) :=
          ((hasDerivAt_id (x i0)).sub_const t).const_mul (2 * Real.pi)
        have h2 := h1.sin
        rw [h2.deriv]
        ring
      · have e : (fun r => U i0 i1 t (Function.update x j r) i)
            = fun _ => Real.sin (2 * Real.pi * (x i0 - t)) := by
          funext r
          simp only [U]
          rw [if_neg hi0, if_pos hi1, Function.update_of_ne (Ne.symm hj)]
        rw [e, deriv_const, if_neg (fun h => hj h.2)]
    · have e : (fun r => U i0 i1 t (Function.update x j r) i) = fun _ => (0 : ℝ) := by
        funext r
        simp [U, hi0, hi1]
      rw [e, deriv_const, if_neg (fun h => hi1 h.1)]

end MO481044

open MO481044 in
theorem OMA.solution : type_of% @OMA.S_mo_481044.main := by
  intro d hd
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin d, i0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin d, i1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := by
    intro h
    rw [h] at hi0
    omega
  refine ⟨U i0 i1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h0 : i = i0
    · have e : (fun p : ℝ × (Fin d → ℝ) => U i0 i1 p.1 p.2 i) = fun _ => (1 : ℝ) := by
        funext p
        simp [U, h0]
      rw [e]
      exact contDiff_const
    · by_cases h1 : i = i1
      · have e : (fun p : ℝ × (Fin d → ℝ) => U i0 i1 p.1 p.2 i)
            = fun p => Real.sin (2 * Real.pi * (p.2 i0 - p.1)) := by
          funext p
          simp only [U]
          rw [if_neg h0, if_pos h1]
        rw [e]
        have hlin : ContDiff ℝ ⊤ (fun p : ℝ × (Fin d → ℝ) => 2 * Real.pi * (p.2 i0 - p.1)) :=
          contDiff_const.mul (((contDiff_apply ℝ ℝ i0).comp contDiff_snd).sub contDiff_fst)
        exact Real.contDiff_sin.comp hlin
      · have e : (fun p : ℝ × (Fin d → ℝ) => U i0 i1 p.1 p.2 i) = fun _ => (0 : ℝ) := by
          funext p
          simp [U, h0, h1]
        rw [e]
        exact contDiff_const
  · intro t x k
    funext i
    simp only [U]
    have e : 2 * Real.pi * (x i0 + (k i0 : ℝ) - t)
        = 2 * Real.pi * (x i0 - t) + (k i0 : ℝ) * (2 * Real.pi) := by ring
    rw [e, Real.sin_add_int_mul_two_pi]
  · intro t x i
    rw [dt i0 i1 h01]
    simp only [dx i0 i1 h01]
    by_cases hi : i = i1
    · rw [if_pos hi, Finset.sum_eq_single i0]
      · rw [if_pos ⟨hi, rfl⟩]
        simp only [U, if_true]
        ring
      · intro j _ hj
        rw [if_neg (fun h => hj h.2), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    · rw [if_neg hi, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hi h.1), mul_zero]
  · intro t x
    apply Finset.sum_eq_zero
    intro i _
    rw [dx i0 i1 h01, if_neg]
    rintro ⟨h1, h2⟩
    exact h01 (h2.symm.trans h1)
  · refine ⟨0, fun _ => 0, i1, ?_⟩
    rw [dt i0 i1 h01, if_pos rfl]
    simp [Real.pi_ne_zero]
