import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2

-- Step RegularPrimes.isRegularPrime_iff_Bernoulli.R2.H1: hypothesis H1 of reduction RegularPrimes.isRegularPrime_iff_Bernoulli.R2
-- Credit: @chris01-dev
-- H1 := ∀ (p : ℕ) [Fact p.Prime],     classNumber (maximalRealSubfield (CyclotomicField p ℚ)) ∣ classNumber (CyclotomicField p ℚ)  /-- The reflection step. If the real class number is divisible by p, then the relative class number is divisible by p as well. -/

/-!
The real class number divides the class number of `ℚ(ζ_p)`.

Let `K = ℚ(ζ_p)` and `K⁺` its maximal real subfield.  We prove `h(K⁺) ∣ h(K)` by showing that
extension of ideals `Cl(K⁺) → Cl(K)` is an injective group homomorphism (Washington,
*Introduction to cyclotomic fields*, Theorem 4.14).

Let `I` be an ideal of `𝓞 K⁺` with `I 𝓞 K = (α)`.  Since `I` is real, `conj α = u * α` for a
unit `u` with `u * conj u = 1`, so `u` is a root of unity (Kronecker), i.e. `u = ± ζ ^ r`.
Write `ζ ^ r = η ^ 2` with `η` a root of unity and put `β = α * η`, another generator.

* If `u = ζ ^ r` then `conj β = β`, so `β ∈ 𝓞 K⁺` and `I = (β)` because extension of ideals is
  injective (faithful flatness).
* If `u = -ζ ^ r` then `conj β = -β`.  With `δ = ζ - ζ⁻¹` (also `conj δ = -δ`) the product
  `β * δ = c` is real, and `I 𝓞 K * (δ) = (c)`.  Taking absolute norms gives
  `N(I) ^ 2 * p = N(c) ^ 2`, since `N(δ) = N(ζ ^ 2 - 1) = p`; this is impossible.

For `p = 2` both fields are `ℚ`.
-/

open NumberField Module
open scoped nonZeroDivisors

namespace OMA.HPlus

/-- If extension of ideals reflects principality, the class number of `R` divides that of `S`:
extension of ideals induces an injective homomorphism of class groups. -/
theorem card_classGroup_dvd {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (H : ∀ I : Ideal R, I ≠ ⊥ → (I.map (algebraMap R S)).IsPrincipal → I.IsPrincipal) :
    Nat.card (ClassGroup R) ∣ Nat.card (ClassGroup S) := by
  have hmap : ∀ I : (Ideal R)⁰, (I : Ideal R).map (algebraMap R S) ∈ (Ideal S)⁰ := by
    intro I
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have h0 : (I : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero I
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
    exact h0
  let g : (Ideal R)⁰ →* (Ideal S)⁰ :=
    { toFun := fun I => ⟨_, hmap I⟩
      map_one' := Subtype.ext (by simp [Ideal.map_top])
      map_mul' := fun I J => Subtype.ext (by simp [Ideal.map_mul]) }
  let ψ : (Ideal R)⁰ →* ClassGroup S := ClassGroup.mk0.comp g
  have hψ : ∀ I J, ClassGroup.mk0 I = ClassGroup.mk0 J → ψ I = ψ J := by
    intro I J h
    obtain ⟨x, y, hx, hy, e⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨algebraMap R S x, algebraMap R S y, ?_, ?_, ?_⟩
    · exact (map_ne_zero_iff _ hinj).mpr hx
    · exact (map_ne_zero_iff _ hinj).mpr hy
    · have := congrArg (Ideal.map (algebraMap R S)) e
      change Ideal.span {algebraMap R S x} * Ideal.map (algebraMap R S) I =
        Ideal.span {algebraMap R S y} * Ideal.map (algebraMap R S) J
      simpa [Ideal.map_mul, Ideal.map_span] using this
  let f : ClassGroup R → ClassGroup S :=
    fun c => ψ (Classical.choose (ClassGroup.mk0_surjective c))
  have hf : ∀ I, f (ClassGroup.mk0 I) = ψ I := fun I =>
    hψ _ _ (Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    have e : ClassGroup.mk0 I * ClassGroup.mk0 J = ClassGroup.mk0 (I * J) :=
      (map_mul ClassGroup.mk0 I J).symm
    rw [e, hf, hf, hf]
    exact map_mul ψ I J
  let F : ClassGroup R →* ClassGroup S := MonoidHom.mk' f hmul
  refine Subgroup.card_dvd_of_injective F ?_
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
  change f _ = 1 at ha
  rw [hf] at ha
  have hp := (ClassGroup.mk0_eq_one_iff (hmap I)).mp ha
  have hI := H I (nonZeroDivisors.coe_ne_zero I) hp
  obtain ⟨I, hI0⟩ := I
  exact (ClassGroup.mk0_eq_one_iff hI0).mpr hI

/-- `p * a ^ 2` is never a square. -/
theorem no_sq (p a b : ℕ) (hp : p.Prime) (ha : a ≠ 0) (h : a ^ 2 * p = b ^ 2) : False := by
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : a ^ 2 * p = 0 := by simpa using h
    rcases Nat.mul_eq_zero.mp h0 with h1 | h1
    · exact ha (by simpa using h1)
    · exact hp.ne_zero h1
  have := Fact.mk hp
  have h1 := congrArg (padicValNat p) h
  rw [padicValNat.mul (pow_ne_zero 2 ha) hp.ne_zero, padicValNat.pow a 2, padicValNat.pow b 2,
    padicValNat_self] at h1
  omega

/-- A number field of degree one has class number one. -/
theorem classNumber_eq_one_of_finrank_one (F : Type*) [Field F] [NumberField F]
    (h : finrank ℚ F = 1) : classNumber F = 1 := by
  rw [classNumber_eq_one_iff]
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
    intro x
    have htop : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
    have hx : (x : F) ∈ (⊥ : Subalgebra ℚ F) := htop ▸ Algebra.mem_top
    obtain ⟨q, hq⟩ := Algebra.mem_bot.mp hx
    have hint : IsIntegral ℤ q := by
      have h1 : IsIntegral ℤ (algebraMap ℚ F q) := hq ▸ x.isIntegral_coe
      exact (isIntegral_algebraMap_iff (algebraMap ℚ F).injective).mp h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨n, RingOfIntegers.ext ?_⟩
    rw [← hq, ← hn]
    simp
  exact IsPrincipalIdealRing.of_surjective (algebraMap ℤ (𝓞 F)) hsurj

section conj

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

open IsCMField

/-- Complex conjugation inverts roots of unity. -/
theorem conj_mul_self (x : 𝓞 K) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) :
    ringOfIntegersComplexConj K x * x = 1 := by
  have hxu : IsUnit x := IsUnit.of_pow_eq_one hx hn.ne'
  have hv : hxu.unit ∈ Units.torsion K := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa using hx)⟩
  have h1 := complexConj_torsion K ⟨hxu.unit, hv⟩
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    have : x = 0 := RingOfIntegers.ext (by simpa using h0)
    exact hxu.ne_zero this
  apply RingOfIntegers.ext
  have h2 : complexConj K (x : K) = (x : K)⁻¹ := by simpa using h1
  change complexConj K (x : K) * (x : K) = 1
  rw [h2, inv_mul_cancel₀ hx0]

end conj

section core

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

open IsCMField

/-- The capitulation kernel is trivial: an ideal of the real subfield which becomes principal in
the cyclotomic field is already principal. -/
theorem isPrincipal_of_map (hp2 : p ≠ 2) {I : Ideal (𝓞 (maximalRealSubfield K))} (hI : I ≠ ⊥)
    (h : (I.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).IsPrincipal) : I.IsPrincipal := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨α, hα⟩ := h
  change Ideal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) I = Ideal.span {α} at hα
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hI
    rw [← Ideal.map_eq_bot_iff_of_injective hinj, hα]
    simp
  have hσσ : ∀ x : 𝓞 K, ringOfIntegersComplexConj K (ringOfIntegersComplexConj K x) = x :=
    fun x => RingOfIntegers.ext (complexConj_apply_apply K x)
  -- the conjugate of `α` generates the same ideal
  have h1 : Ideal.map (ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K)
      (Ideal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) I) = Ideal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) I := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact congrArg _ ((ringOfIntegersComplexConj K).commutes r)
  rw [hα, Ideal.map_span, Set.image_singleton] at h1
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h1.symm
  replace hu : α * u = ringOfIntegersComplexConj K α := hu
  -- `u * conj u = 1`
  have h3 : (u : 𝓞 K) * ringOfIntegersComplexConj K u = 1 := by
    apply mul_left_cancel₀ hα0
    rw [mul_one, ← mul_assoc, hu, ← map_mul, hu, hσσ]
  have huK : (u : K) * complexConj K (u : K) = 1 := by
    have := congrArg (algebraMap (𝓞 K) K) h3
    simpa using this
  -- hence `u` is a root of unity
  have hut : u ∈ Units.torsion K := by
    rw [Units.mem_torsion]
    intro w
    have h4 : w (u : K) * w (complexConj K (u : K)) = 1 := by rw [← map_mul, huK, map_one]
    rw [infinitePlace_complexConj] at h4
    rcases mul_self_eq_one_iff.mp h4 with h5 | h5
    · exact h5
    · have := apply_nonneg w (u : K)
      linarith
  have hfin : IsOfFinOrder (u : K) := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hut
    obtain ⟨n, hn, hun⟩ := hut
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) hun
    simpa using this
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨r, -, hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (hp.out.odd_of_ne_two hp2) hfin
  set zz : 𝓞 K := hζ.toInteger with hzz
  have hzzp : zz ^ p = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hσz : ringOfIntegersComplexConj K zz * zz = 1 := conj_mul_self K zz p hp.out.pos hzzp
  have hu' : (u : 𝓞 K) = zz ^ r ∨ (u : 𝓞 K) = -zz ^ r := by
    rcases hr with hr | hr
    · left
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u : 𝓞 K) = algebraMap (𝓞 K) K (zz ^ r)
      rw [map_pow]
      exact hr
    · right
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u : 𝓞 K) = algebraMap (𝓞 K) K (-zz ^ r)
      rw [map_neg, map_pow]
      exact hr
  obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    exact ⟨k + 1, by omega⟩
  set η : 𝓞 K := zz ^ (r * m) with hη
  have hη2 : η ^ 2 = zz ^ r := by
    rw [hη, ← pow_mul, show r * m * 2 = r + p * r by nlinarith, pow_add, pow_mul, hzzp, one_pow,
      mul_one]
  have hηp : η ^ p = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, hzzp, one_pow]
  have hση : ringOfIntegersComplexConj K η * η = 1 := conj_mul_self K η p hp.out.pos hηp
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηp hp.out.ne_zero
  have hβspan : Ideal.span {α * η} = Ideal.span {α} := Ideal.span_singleton_mul_right_unit hηu α
  rcases hu' with hu' | hu'
  · -- `α * η` is real
    have hβ : ringOfIntegersComplexConj K (α * η) = α * η := by
      rw [map_mul, ← hu, hu', ← hη2]
      linear_combination (α * η) * hση
    obtain ⟨b, hb⟩ := (ringOfIntegersComplexConj_eq_self_iff K (α * η)).mp hβ
    have e : I.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) =
        (Ideal.span {b}).map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
      rw [hα, Ideal.map_span, Set.image_singleton, hb, hβspan]
    have e' := congrArg (Ideal.comap (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))) e
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.comap_map_eq_self_of_faithfullyFlat] at e'
    exact ⟨⟨b, e'⟩⟩
  · -- `α * η` is purely imaginary: impossible by a norm computation
    exfalso
    have hβ : ringOfIntegersComplexConj K (α * η) = -(α * η) := by
      rw [map_mul, ← hu, hu', ← hη2]
      linear_combination (-(α * η)) * hση
    set δ : 𝓞 K := zz - ringOfIntegersComplexConj K zz with hδ
    have hσδ : ringOfIntegersComplexConj K δ = -δ := by
      rw [hδ, map_sub, hσσ]
      ring
    have hγ : ringOfIntegersComplexConj K (α * η * δ) = α * η * δ := by
      rw [map_mul, hβ, hσδ]
      ring
    obtain ⟨c, hc⟩ := (ringOfIntegersComplexConj_eq_self_iff K (α * η * δ)).mp hγ
    have e : I.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) * Ideal.span {δ} =
        (Ideal.span {c}).map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
      rw [hα, Ideal.map_span, Set.image_singleton, hc, ← hβspan,
        Ideal.span_singleton_mul_span_singleton]
    have hzu : IsUnit zz := IsUnit.of_pow_eq_one hzzp hp.out.ne_zero
    have hδz : δ * zz = zz ^ 2 - 1 := by
      rw [hδ]
      linear_combination (-1 : 𝓞 K) * hσz
    have hnorm : Ideal.absNorm (Ideal.span {δ}) = p := by
      rw [← Ideal.span_singleton_mul_right_unit hzu δ, hδz, Ideal.absNorm_span_singleton]
      have hζ2 : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K ^ 2) p :=
        hζ.pow_of_coprime 2 ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
      have hn := hζ2.norm_sub_one_of_prime_ne_two' (K := ℚ)
        (Polynomial.cyclotomic.irreducible_rat hp.out.pos) hp2
      have hz : Algebra.norm ℤ (zz ^ 2 - 1) = (p : ℤ) := by
        apply Int.cast_injective (α := ℚ)
        rw [Algebra.coe_norm_int]
        change Algebra.norm ℚ (algebraMap (𝓞 K) K (zz ^ 2 - 1)) = _
        rw [map_sub, map_pow, map_one]
        exact hn
      rw [hz, Int.natAbs_natCast]
    have hfr : finrank (𝓞 (maximalRealSubfield K)) (𝓞 K) = 2 := by
      rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield K)) (maximalRealSubfield K) (𝓞 K) K]
      exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K
    have e2 := congrArg Ideal.absNorm e
    rw [map_mul, hnorm, Ideal.absNorm_algebraMap, Ideal.absNorm_algebraMap, hfr] at e2
    exact no_sq p _ _ hp.out (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) e2

end core

theorem main (p : ℕ) [hp : Fact p.Prime] :
    classNumber (maximalRealSubfield (CyclotomicField p ℚ)) ∣
      classNumber (CyclotomicField p ℚ) := by
  have inst : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  by_cases hp2 : p = 2
  · subst hp2
    have h1 : finrank ℚ (CyclotomicField 2 ℚ) = 1 := by
      rw [IsCyclotomicExtension.finrank (n := 2) (CyclotomicField 2 ℚ)
        (Polynomial.cyclotomic.irreducible_rat two_pos)]
      rfl
    have h2 : finrank ℚ (maximalRealSubfield (CyclotomicField 2 ℚ)) = 1 := by
      have hle : finrank ℚ (maximalRealSubfield (CyclotomicField 2 ℚ)) ≤
          finrank ℚ (CyclotomicField 2 ℚ) :=
        LinearMap.finrank_le_finrank_of_injective
          (f := (maximalRealSubfield (CyclotomicField 2 ℚ)).subtype.toRatAlgHom.toLinearMap)
          Subtype.val_injective
      have hpos : 0 < finrank ℚ (maximalRealSubfield (CyclotomicField 2 ℚ)) := Module.finrank_pos
      omega
    rw [classNumber_eq_one_of_finrank_one _ h2]
    exact one_dvd _
  · have h2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    have : IsCMField (CyclotomicField p ℚ) :=
      IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p}) ⟨p, rfl, h2⟩
    unfold classNumber
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact card_classGroup_dvd (FaithfulSMul.algebraMap_injective _ _)
      (fun I hI h => isPrincipal_of_map p (CyclotomicField p ℚ) hp2 hI h)

end OMA.HPlus

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2.H1 := by
  intro p hp
  exact OMA.HPlus.main p
