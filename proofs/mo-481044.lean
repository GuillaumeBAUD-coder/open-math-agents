import OMAStatements.S_mo_481044
import Mathlib

/-! A travelling shear on the unit torus. The constant second component
transports the sinusoidal first component at exactly unit speed. -/
namespace Deldor14.TravellingShear
open Real Finset OMA.S_mo_481044
private noncomputable def field {d : ℕ} (a b : Fin d) (t : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i=a then sin (2*π*(x b-t)) else if i=b then 1 else 0

private theorem dt {d : ℕ} (a b : Fin d) (t : ℝ) (x : Fin d → ℝ) (i : Fin d) :
    deriv (fun s => field a b s x i) t =
      if i=a then -(2*π)*cos (2*π*(x b-t)) else 0 := by
  by_cases e : i=a
  · simp only [field,if_pos e]
    have h := (((hasDerivAt_id t).const_sub (x b)).const_mul (2*π)).sin.deriv
    convert h using 1 <;> simp <;> ring
  · simp [field,e]
private theorem dx {d : ℕ} (a b : Fin d) (t : ℝ) (x : Fin d → ℝ) (i j : Fin d) :
    partialSpace (field a b) t x i j =
      if i=a ∧ j=b then (2*π)*cos (2*π*(x b-t)) else 0 := by
  by_cases e : i=a
  · subst i
    by_cases h : j=b
    · subst j
      simp only [partialSpace,field,if_pos rfl,Function.update_self,and_self,ite_true]
      have h := (((hasDerivAt_id (x b)).sub_const t).const_mul (2*π)).sin.deriv
      convert h using 1 <;> simp <;> ring
    · simp [partialSpace,field,Function.update_of_ne (Ne.symm h),h]
  · simp [partialSpace,field,e]

theorem full : type_of% @OMA.S_mo_481044.main := by
  intro d hd
  let a : Fin d := ⟨0,by omega⟩
  let b : Fin d := ⟨1,by omega⟩
  have ne : a≠b := by intro h;have v := congrArg Fin.val h;norm_num [a,b] at v
  refine ⟨field a b,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases e : i=a
    · simp only [field,if_pos e];fun_prop
    · simp only [field,if_neg e]; exact contDiff_const
  · intro t x k
    funext i
    by_cases e : i=a
    · simp only [field,if_pos e]
      rw [show 2*π*(x b+(k b:ℝ)-t) = 2*π*(x b-t)+(k b:ℝ)*(2*π) by ring]
      exact sin_add_int_mul_two_pi _ _
    · simp [field,e]
  · intro t x i
    by_cases e : i=a
    · subst i
      rw [dt,sum_eq_single b]
      · simp [dx,field,ne.symm] <;> ring
      · intro j _ h; simp [dx,h]
      · simp
    · simp [dt,dx,e]
  · intro t x
    apply sum_eq_zero
    intro i _
    have h : ¬(i=a ∧ i=b) := fun h => ne (h.1.symm.trans h.2)
    simp [dx,h]
  · refine ⟨0,fun _ => 0,a,?_⟩
    simp [dt,Real.pi_ne_zero]
end Deldor14.TravellingShear
theorem OMA.solution : type_of% @OMA.S_mo_481044.main := Deldor14.TravellingShear.full
