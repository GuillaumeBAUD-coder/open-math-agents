import OMAStatements.S_mo_289024
import Mathlib


namespace H289024
open NumberField QuadraticAlgebra

abbrev K := QuadraticAlgebra ℚ 3 0

lemma no_sqrt : ∀ r : ℚ, r ^ 2 ≠ 3 + 0 * r := by
  intro r h
  have h3 : Irrational (Real.sqrt 3) := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 3)
  apply h3
  refine ⟨|r|, ?_⟩
  have h' : ((r : ℝ)) ^ 2 = 3 := by exact_mod_cast (by simpa using h)
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, h']

instance fact3 : Fact (∀ r : ℚ, r ^ 2 ≠ 3 + 0 * r) := ⟨no_sqrt⟩

instance nf : NumberField K := { }

instance quadext : Algebra.IsQuadraticExtension ℚ K := ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

lemma norm_eq (z : K) : Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  rfl

lemma zmod3 : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide

lemma desc : ∀ n : ℕ, ∀ X Y Z : ℤ, Y.natAbs = n → X ^ 2 + Y ^ 2 = 3 * Z ^ 2 → Y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y Z hn h
  by_contra hY
  have h3 : ((X : ZMod 3)) ^ 2 + ((Y : ZMod 3)) ^ 2 = 0 := by
    have := congrArg (fun t : ℤ => (t : ZMod 3)) h
    push_cast at this
    rw [this]
    have : (3 : ZMod 3) = 0 := rfl
    rw [this, zero_mul]
  obtain ⟨hx, hy⟩ := zmod3 _ _ h3
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx hy
  have hx' : (3 : ℤ) ∣ X := by exact_mod_cast hx
  have hy' : (3 : ℤ) ∣ Y := by exact_mod_cast hy
  obtain ⟨X', rfl⟩ := hx'
  obtain ⟨Y', rfl⟩ := hy'
  have hZ2 : (3 : ℤ) ∣ Z ^ 2 := ⟨X' ^ 2 + Y' ^ 2, by have := h; ring_nf at this; linarith⟩
  obtain ⟨Z', rfl⟩ := Int.prime_three.dvd_of_dvd_pow hZ2
  have h' : X' ^ 2 + Y' ^ 2 = 3 * Z' ^ 2 := by have := h; ring_nf at this; linarith
  have hY' : Y' ≠ 0 := by rintro rfl; simp at hY
  have := ih Y'.natAbs (by rw [← hn, Int.natAbs_mul]; have := Int.natAbs_pos.mpr hY'; simp; omega)
    X' Y' Z' rfl h'
  exact hY' this

lemma no_neg_one (x y : ℚ) : x ^ 2 - 3 * y ^ 2 ≠ -1 := by
  intro h
  have hq := x.den_nz
  have hs := y.den_nz
  have e1 : (x.num : ℚ) = x * x.den := by rw [Rat.mul_den_eq_num]
  have e2 : (y.num : ℚ) = y * y.den := by rw [Rat.mul_den_eq_num]
  have key : (x.num * y.den) ^ 2 + (x.den * y.den : ℤ) ^ 2 = 3 * (y.num * x.den) ^ 2 := by
    have : ((x.num * y.den : ℤ) : ℚ) ^ 2 + ((x.den * y.den : ℤ) : ℚ) ^ 2 =
        3 * ((y.num * x.den : ℤ) : ℚ) ^ 2 := by
      push_cast
      rw [e1, e2]
      linear_combination (↑x.den * ↑y.den : ℚ) ^ 2 * h
    exact_mod_cast this
  have := desc _ _ _ _ rfl key
  simp at this

lemma norm_unit (ε : (𝓞 K)ˣ) : QuadraticAlgebra.norm ((ε : 𝓞 K) : K) = 1 := by
  have h := NumberField.Units.norm K ε
  rw [norm_eq] at h
  rcases abs_eq (zero_le_one) |>.mp h with h | h
  · exact h
  · exfalso
    apply no_neg_one ((ε : 𝓞 K) : K).re ((ε : 𝓞 K) : K).im
    rw [← h, norm_def]
    ring

lemma aut_cases (σ : K ≃ₐ[ℚ] K) (z : K) : σ z = z ∨ σ z = star z := by
  have hω : σ ω * σ ω = 3 := by
    rw [← map_mul, omega_mul_omega_eq_mk]
    have : (⟨3, 0⟩ : K) = algebraMap ℚ K 3 := rfl
    rw [this, AlgEquiv.commutes]
    rfl
  have hz : z = algebraMap ℚ K z.re + algebraMap ℚ K z.im * ω := by
    ext <;> simp
  have hsq : (σ ω - ω) * (σ ω + ω) = 0 := by
    have h2 : (ω : K) * ω = 3 := by rw [omega_mul_omega_eq_mk]; rfl
    linear_combination hω - h2
  rcases mul_eq_zero.mp hsq with h | h
  · left
    rw [hz, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, sub_eq_zero.mp h]
  · right
    rw [hz, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, eq_neg_of_add_eq_zero_left h]
    ext <;> simp

lemma inv_coe (ε : (𝓞 K)ˣ) :
    (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = star ((ε : 𝓞 K) : K) := by
  have hstar : ((ε : 𝓞 K) : K) * star ((ε : 𝓞 K) : K) = 1 := by
    rw [← algebraMap_norm_eq_mul_star, norm_unit, map_one]
  have h1 : (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((ε : 𝓞 K) : K) = 1 := by
    have := congrArg (fun x : 𝓞 K => (x : K)) ε.inv_mul
    simpa using this
  linear_combination (-(((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * hstar + star ((ε : 𝓞 K) : K) * h1

lemma sub_zpowers (ε : (𝓞 K)ˣ) :
    OMA.S_mo_289024.conjugateSubgroup ε ≤ Subgroup.zpowers ε := by
  rw [OMA.S_mo_289024.conjugateSubgroup, Subgroup.closure_le]
  rintro u ⟨σ, hσ⟩
  rcases aut_cases σ ((ε : 𝓞 K) : K) with h | h
  · have : u = ε := by
      apply Units.ext
      apply RingOfIntegers.ext
      rw [hσ, h]
    rw [this]
    exact Subgroup.mem_zpowers ε
  · have : u = ε⁻¹ := by
      apply Units.ext
      apply RingOfIntegers.ext
      rw [hσ, h, inv_coe]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ε)

noncomputable def f (x : K) : ℝ := x.re + x.im * Real.sqrt 3

lemma f_mul (x y : K) : f (x * y) = f x * f y := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [f, re_mul, im_mul]
  push_cast
  linear_combination (-((x.im : ℝ) * y.im)) * h3

lemma f_pow (x : K) (n : ℕ) : f (x ^ n) = f x ^ n := by
  induction n with
  | zero => simp [f]
  | succ n ih => rw [pow_succ, f_mul, ih, pow_succ]

lemma omega_int : IsIntegral ℤ (ω : K) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 3, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  have h2 : (ω : K) * ω = 3 := by rw [omega_mul_omega_eq_mk]; rfl
  simp [pow_two, h2]

end H289024

open NumberField QuadraticAlgebra H289024

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_289024.main) := by
  intro h
  obtain ⟨ε, hrank, hodd⟩ := h K
  have hm1 : (-1 : (𝓞 K)ˣ) ∈ OMA.S_mo_289024.conjugateSubgroup ε := by
    have := Subgroup.pow_index_mem (OMA.S_mo_289024.conjugateSubgroup ε) (-1)
    rwa [Odd.neg_one_pow hodd] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (sub_zpowers ε hm1)
  have hne : (-1 : (𝓞 K)ˣ) ≠ 1 := by
    intro h1
    have := congrArg (fun x : (𝓞 K)ˣ => (((x : 𝓞 K) : K)).re) h1
    norm_num at this
  have hfo : IsOfFinOrder ε := by
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨2 * k, ?_, ?_⟩
    · intro h0
      have hk0 : k = 0 := by omega
      rw [hk0, zpow_zero] at hk
      exact hne hk.symm
    · rw [mul_comm, zpow_mul, hk]
      simp
  obtain ⟨m, hm0, hm⟩ := (isOfFinOrder_iff_pow_eq_one).mp hfo
  have hzm : ((ε : 𝓞 K) : K) ^ m = 1 := by
    have := congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K)) hm
    simp at this
    exact this
  have hfz : |f ((ε : 𝓞 K) : K)| = 1 := by
    have h1 : f ((ε : 𝓞 K) : K) ^ m = 1 := by
      rw [← f_pow, hzm]
      simp [f]
    have h2 := congrArg abs h1
    rw [abs_pow, abs_one] at h2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm0.ne').mp h2
  have hω2 : (ω : K) * ω = 3 := by rw [omega_mul_omega_eq_mk]; rfl
  let a0 : 𝓞 K := ⟨2 + ω, (isIntegral_algebraMap (x := (2 : ℤ))).add omega_int⟩
  let b0 : 𝓞 K := ⟨2 - ω, (isIntegral_algebraMap (x := (2 : ℤ))).sub omega_int⟩
  have hab : ((a0 * b0 : 𝓞 K) : K) = 1 := by
    simp only [a0, b0]
    show (2 + ω) * (2 - ω) = (1 : K)
    linear_combination (-1 : K) * hω2
  let u0 : (𝓞 K)ˣ := ⟨a0, b0, RingOfIntegers.ext (by rw [hab]; simp),
    RingOfIntegers.ext (by rw [mul_comm, hab]; simp)⟩
  obtain ⟨n, hn0, hn⟩ := hrank u0
  have hz := sub_zpowers ε hn
  rw [← hfo.mem_powers_iff_mem_zpowers] at hz
  obtain ⟨i, hi⟩ := hz
  have hK : ((ε : 𝓞 K) : K) ^ i = (2 + ω) ^ n := by
    have := congrArg (fun x : (𝓞 K)ˣ => algebraMap (𝓞 K) K (x : 𝓞 K)) hi
    simp only [Units.val_pow_eq_pow_val, map_pow] at this
    exact this
  have hf := congrArg (fun x => |f x|) hK
  simp only [f_pow, abs_pow, hfz, one_pow] at hf
  have hf2 : f (2 + ω) = 2 + Real.sqrt 3 := by simp [f]
  rw [hf2] at hf
  have hpos : (1 : ℝ) < |2 + Real.sqrt 3| := by
    rw [abs_of_pos (by positivity)]
    have := Real.sqrt_nonneg 3
    linarith
  exact absurd hf (ne_of_lt (one_lt_pow₀ hpos hn0.ne'))
