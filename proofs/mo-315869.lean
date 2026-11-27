import OMAStatements.S_mo_315869
import Mathlib

-- Problem: mo-315869, is f tensor id_N : M tensor N -> N tensor N injective whenever
-- f : M -> N is injective?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Over the integers take M = Z, N = Z x Z/2 and f(n) = (2n, 0). Then 1 tensor (0, 1) is
-- nonzero in M tensor N = N, but it maps to (2, 0) tensor (0, 1) = (1, 0) tensor (0, 2) = 0.

open scoped TensorProduct

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315869.main) := by
  intro h
  let f : ℤ →ₗ[ℤ] (ℤ × ZMod 2) :=
    LinearMap.toSpanSingleton ℤ (ℤ × ZMod 2) ((2 : ℤ), (0 : ZMod 2))
  have hf1 : ∀ n : ℤ, f n = n • ((2 : ℤ), (0 : ZMod 2)) := fun n => rfl
  have hf : Function.Injective f := by
    intro a b hab
    rw [hf1, hf1] at hab
    have h1 : a * 2 = b * 2 := by simpa using congrArg Prod.fst hab
    omega
  have hinj := h ℤ ℤ (ℤ × ZMod 2) f hf
  have e1 : (1 : ℤ) • ((2 : ℤ), (0 : ZMod 2)) = (2 : ℤ) • ((1 : ℤ), (0 : ZMod 2)) := by
    ext <;> simp
  have e2 : (2 : ℤ) • ((0 : ℤ), (1 : ZMod 2)) = 0 := by
    rw [two_smul]
    ext
    · simp
    · show (1 : ZMod 2) + 1 = 0
      decide
  have h0 : TensorProduct.map f (LinearMap.id : (ℤ × ZMod 2) →ₗ[ℤ] (ℤ × ZMod 2))
      ((1 : ℤ) ⊗ₜ[ℤ] ((0 : ℤ), (1 : ZMod 2))) = 0 := by
    rw [TensorProduct.map_tmul, hf1, e1, TensorProduct.smul_tmul, LinearMap.id_apply, e2,
      TensorProduct.tmul_zero]
  have h1 : (1 : ℤ) ⊗ₜ[ℤ] ((0 : ℤ), (1 : ZMod 2)) = 0 := by
    apply hinj
    rw [h0, map_zero]
  have h2 : (1 : ℤ) • ((0 : ℤ), (1 : ZMod 2)) = 0 := by
    have h3 := congrArg (TensorProduct.lid ℤ (ℤ × ZMod 2)) h1
    rw [TensorProduct.lid_tmul, map_zero] at h3
    exact h3
  rw [one_smul] at h2
  have h4 : (1 : ZMod 2) = 0 := congrArg Prod.snd h2
  exact absurd h4 (by decide)
