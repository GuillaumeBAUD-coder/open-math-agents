import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

/-! The two-charge equilibrium set is a subsingleton.
Credit: @harshshah1618. The proof uses the Coulomb gradient, its norm balance,
and the resulting fixed ratio of distances to the two distinct charge locations.
-/

open InnerProductSpace
open scoped RealInnerProductSpace Gradient

namespace OMA.Maxwell
abbrev E := EuclideanSpace ℝ (Fin 3)

lemma charge_hasGradient (q : ℝ) (a x : E) (hxa : x ≠ a) :
    HasGradientAt (fun y : E => q / dist y a) ((-q / ‖x-a‖^3) • (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : E => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : E => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
      <;> norm_num
  have hi := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hi using 1 <;> ext v <;>
    simp [dist_eq_norm, div_eq_mul_inv, toDual_apply_apply, inner_smul_left, smul_smul]
  <;> field_simp [hn]
  <;> simp
  <;> ring

end OMA.Maxwell

namespace OMA.MaxwellAlgebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma balance_ratio (p q : ℝ) (hp : p ≠ 0) (a b x : E)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (h : (p / ‖x-a‖^3) • (x-a) + (q / ‖x-b‖^3) • (x-b) = 0) :
    (‖x-b‖ / ‖x-a‖)^2 = |q| / |p| := by
  have hra : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hrb : ‖x-b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxb)
  have hn := congrArg norm (eq_neg_iff_add_eq_zero.mpr h)
  simp only [norm_smul, norm_neg, Real.norm_eq_abs, abs_div, abs_pow, abs_norm] at hn
  have hn' : |p| / ‖x-a‖^2 = |q| / ‖x-b‖^2 := by
    convert hn using 1 <;> field_simp [hra, hrb] <;> ring
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hra) (abs_ne_zero.mpr hp)]
  have hh := (div_eq_div_iff (pow_ne_zero 2 hra) (pow_ne_zero 2 hrb)).mp hn'
  nlinarith only [hh]

lemma balance_smul (s t : ℝ) (u v : E) (ht : t ≠ 0)
    (h : s • u + t • v = 0) : v = (-s/t) • u := by
  have h' : t • v = -(s • u) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h)
  have hh := congrArg (fun z : E => t⁻¹ • z) h'
  simp only [smul_neg, smul_smul, inv_mul_cancel₀ ht, one_smul, ← neg_smul] at hh
  simpa only [div_eq_mul_inv, neg_mul, mul_comm] using hh

lemma coefficient (p q ra rb : ℝ) (hq : q ≠ 0) (hra : ra ≠ 0) (hrb : rb ≠ 0) :
    -(p / ra^3) / (q / rb^3) = -(p/q) * (rb/ra)^3 := by
  field_simp
  <;> ring

lemma critical_unique (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (a b x y : E)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : (p / ‖x-a‖^3) • (x-a) + (q / ‖x-b‖^3) • (x-b) = 0)
    (hy : (p / ‖y-a‖^3) • (y-a) + (q / ‖y-b‖^3) • (y-b) = 0) : x = y := by
  have hra : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hrb : ‖x-b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxb)
  have hsa : ‖y-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hya)
  have hsb : ‖y-b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyb)
  have hratio : ‖x-b‖ / ‖x-a‖ = ‖y-b‖ / ‖y-a‖ :=
    (sq_eq_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
      (div_nonneg (norm_nonneg _) (norm_nonneg _))).mp
      ((balance_ratio p q hp a b x hxa hxb hx).trans
        (balance_ratio p q hp a b y hya hyb hy).symm)
  let k := -(p / ‖x-a‖^3) / (q / ‖x-b‖^3)
  have hk : -(p / ‖y-a‖^3) / (q / ‖y-b‖^3) = k := by
    dsimp [k]
    rw [coefficient p q _ _ hq hsa hsb, coefficient p q _ _ hq hra hrb, hratio]
  have hxv : x-b = k • (x-a) :=
    balance_smul _ _ _ _ (div_ne_zero hq (pow_ne_zero 3 hrb)) hx
  have hyv : y-b = k • (y-a) := by
    rw [← hk]
    exact balance_smul _ _ _ _ (div_ne_zero hq (pow_ne_zero 3 hsb)) hy
  have hk1 : k ≠ 1 := by
    intro he
    have hh : x-b = x-a := by simpa [he] using hxv
    exact hab (sub_right_inj.mp hh).symm
  have heq : x-y = k • (x-y) := by
    calc x-y = (x-b)-(y-b) := by abel
         _ = k • (x-a) - k • (y-a) := congrArg₂ (· - ·) hxv hyv
         _ = k • (x-y) := by rw [← smul_sub]; congr 1; abel
  have hz : (1-k) • (x-y) = 0 := by rw [sub_smul, one_smul, ← heq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hk1.symm))

end OMA.MaxwellAlgebra




namespace OMA.Maxwell
open Arxiv.«2607.27197»

lemma equilibrium_balance (q : Fin 2 → ℝ) (a : Fin 2 → E) (x : E)
    (hx : x ∈ equilibria q a) :
    (q 0 / ‖x-a 0‖^3) • (x-a 0) + (q 1 / ‖x-a 1‖^3) • (x-a 1) = 0 := by
  have hn (j : Fin 2) : x ≠ a j := fun h => hx.1 ⟨j, h.symm⟩
  have h0 := charge_hasGradient (q 0) (a 0) x (hn 0)
  have h1 := charge_hasGradient (q 1) (a 1) x (hn 1)
  have hd : HasGradientAt (potential q a)
      (((-q 0) / ‖x-a 0‖^3) • (x-a 0) + ((-q 1) / ‖x-a 1‖^3) • (x-a 1)) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hf : potential q a =
        (fun y => q 0 / dist y (a 0)) + (fun y => q 1 / dist y (a 1)) := by
      funext y
      exact Fin.sum_univ_two (fun j => q j / dist y (a j))
    rw [hf, map_add]
    exact h0.hasFDerivAt.add h1.hasFDerivAt
  have hz := hd.gradient.symm.trans hx.2
  simpa only [neg_div, neg_smul, ← neg_add, neg_eq_zero] using hz

lemma result (q : Fin 2 → ℝ) (a : Fin 2 → E) (ha : Function.Injective a)
    (hq : ∀ j, q j ≠ 0) : (equilibria q a).encard ≤ 1 := by
  apply Set.encard_le_one_iff.mpr
  intro x y hx hy
  have hn {z : E} (hz : z ∈ equilibria q a) (j : Fin 2) : z ≠ a j :=
    fun h => hz.1 ⟨j, h.symm⟩
  exact OMA.MaxwellAlgebra.critical_unique (q 0) (q 1) (hq 0) (hq 1)
    (a 0) (a 1) x y (ha.ne (by decide)) (hn hx 0) (hn hx 1) (hn hy 0) (hn hy 1)
    (equilibrium_balance q a x hx) (equilibrium_balance q a y hy)

end OMA.Maxwell

theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.two_charges := by
  intro q a ha hq
  exact OMA.Maxwell.result q a ha hq
