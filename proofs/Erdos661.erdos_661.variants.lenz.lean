import FormalConjectures.ErdosProblems.«661»

/-! Lenz's construction in two orthogonal coordinate planes. Both circles
have squared radius one half. Credit: @Deldor14. -/
open Finset
namespace OMA.Lenz
noncomputable section
private abbrev Space := EuclideanSpace ℝ (Fin 4)
private def t (i : Nat) : ℝ := 1 / ((i : ℝ)+2)
private def h (i : Nat) : ℝ := Real.sqrt (1/2 - (t i)^2)
private def x (i : Nat) : Space := WithLp.toLp 2 ![t i,h i,0,0]
private def y (i : Nat) : Space := WithLp.toLp 2 ![0,0,t i,h i]

private lemma radius (i : Nat) : (t i)^2 + (h i)^2 = 1/2 := by
  have hp : 0 < t i := by unfold t; positivity
  have he : t i ≤ 1/2 := by
    unfold t
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hn : 0 ≤ 1/2 - (t i)^2 := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr he)]
  rw [h,Real.sq_sqrt hn]
  ring

private lemma inj : Function.Injective t := by
  intro i j e
  simp only [t,one_div,inv_inj,add_left_inj,Nat.cast_inj] at e
  exact e

private lemma cross (i j : Nat) : dist (x i) (y j) = 1 := by
  rw [EuclideanSpace.dist_eq]
  change Real.sqrt (∑ k : Fin 4, dist (![t i,h i,0,0] k) (![0,0,t j,h j] k)^2) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero,Real.dist_eq,sub_zero,zero_sub,sq_abs]
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)]
  linarith [radius i,radius j]

end
end OMA.Lenz

open OMA.Lenz in
theorem OMA.solution : type_of% @Erdos661.erdos_661.variants.lenz := by
  intro n
  classical
  refine ⟨(range n).image x,(range n).image y,?_,?_,?_,?_⟩
  · rw [card_image_of_injective,card_range]
    intro i j e
    exact inj (congrArg (fun v : Space => v 0) e)
  · rw [card_image_of_injective,card_range]
    intro i j e
    exact inj (congrArg (fun v : Space => v 2) e)
  · rw [disjoint_left]
    intro v hv hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    obtain ⟨j,_,eq⟩ := mem_image.mp hw
    have hz := congrArg (fun v : Space => v 0) eq
    change 0 = t i at hz
    have : 0 < t i := by unfold t; positivity
    linarith
  · intro a ha b hb
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact cross i j
