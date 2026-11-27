import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H1_R1
import Mathlib

-- Step Green100.green_100.variants.operator_norm.R1.H1.R1.H3: hypothesis H3 of reduction Green100.green_100.variants.operator_norm.R1.H1.R1
-- Credit: @ivillar

/-!
Doubling the lattice coordinate is an injective, non-surjective endomorphism of `ℤ³ ⋊ L`.
-/
namespace F2G100

theorem doubling : ∀ (L : Type) [Group L] (a : L →* MulAut (Multiplicative (Fin 3 → ℤ))),
    let B := Multiplicative (Fin 3 → ℤ) ⋊[a] L
    ∃ φ : B →* B, Function.Injective φ ∧ ¬Function.Surjective φ := by
  intro L _ a
  let sq : Multiplicative (Fin 3 → ℤ) →* Multiplicative (Fin 3 → ℤ) := powMonoidHom 2
  have hsq : ∀ x y : Multiplicative (Fin 3 → ℤ), x ^ 2 = y ^ 2 → x = y := by
    intro x y h
    have h' : (2 : ℕ) • Multiplicative.toAdd x = (2 : ℕ) • Multiplicative.toAdd y := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    have : Multiplicative.toAdd x = Multiplicative.toAdd y := by
      funext i
      have hi := congrFun h' i
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at hi
      omega
    exact Multiplicative.toAdd.injective this
  refine ⟨SemidirectProduct.map sq (MonoidHom.id L) (fun g => ?_), ?_, ?_⟩
  · ext x
    simp [sq]
  · intro x y h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    simp only [SemidirectProduct.map_left, SemidirectProduct.map_right, MonoidHom.id_apply] at hl hr
    exact SemidirectProduct.ext (hsq _ _ (by simpa [sq] using hl)) hr
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj ⟨Multiplicative.ofAdd (fun _ => (1 : ℤ)), 1⟩
    have hl := congrArg SemidirectProduct.left hx
    simp only [SemidirectProduct.map_left] at hl
    have h0 := congrFun (congrArg Multiplicative.toAdd hl) 0
    simp [sq] at h0
    omega

end F2G100

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1.H3 :=
  F2G100.doubling
