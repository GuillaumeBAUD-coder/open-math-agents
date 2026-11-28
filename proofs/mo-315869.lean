import OMAStatements.S_mo_315869
import Mathlib

open scoped TensorProduct

open OMA.S_mo_315869



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315869.main) := by
  intro h
  let N := ℤ × ZMod 2
  let f : ℤ →ₗ[ℤ] N :=
    { toFun := fun a => (2*a,0)
      map_add' := by
        intro a b
        apply Prod.ext
        · exact mul_add 2 a b
        · change (0 : ZMod 2) = 0 + 0
          simp
      map_smul' := by
        intro a b
        apply Prod.ext
        · change 2 * (a*b) = a * (2*b)
          ring
        · change (0 : ZMod 2) = a • (0 : ZMod 2)
          simp }
  have hf : Function.Injective f := by
    intro a b he
    have h₁ := congrArg Prod.fst he
    change 2*a = 2*b at h₁
    omega
  let v : N := (0,1)
  let w : N := (1,0)
  have hV : (2 : ℤ) • v = 0 := by
    apply Prod.ext
    · change (2 : ℤ) * 0 = 0
      norm_num
    · change (2 : ℤ) • (1 : ZMod 2) = 0
      rw [two_zsmul]
      decide
  have hF : f 1 = (2 : ℤ) • w := by
    apply Prod.ext
    · change (2 : ℤ) * 1 = 2 * 1
      rfl
    · change (0 : ZMod 2) = (2 : ℤ) • (0 : ZMod 2)
      simp
  let T := TensorProduct.map f (LinearMap.id : N →ₗ[ℤ] N)
  have hT : T ((1 : ℤ) ⊗ₜ[ℤ] v) = T 0 := by
    change TensorProduct.map f (LinearMap.id : N →ₗ[ℤ] N) _ = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hF, TensorProduct.smul_tmul,
      hV, TensorProduct.tmul_zero, map_zero]
  have hh := congrArg (TensorProduct.lid ℤ N) (h ℤ ℤ N f hf hT)
  have hv : v = 0 := by simpa using hh
  have h01 : (1 : ZMod 2) = 0 := congrArg Prod.snd hv
  exact one_ne_zero h01
