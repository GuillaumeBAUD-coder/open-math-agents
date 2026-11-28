import FormalConjectures.Wikipedia.SmallCohenMacaulayModules

/-!
# Small Cohen–Macaulay modules in dimension at most two

Choose parameters in the original ring, then pass to a complete domain component
of the same dimension. In dimension two, write the images of the parameters as
`x, y` and consider the ideals `D n = (x^n) : y^∞`. Localizing at a prime
containing `x` and avoiding `y` shows that their intersection is zero.
Chevalley's lemma then puts a sufficiently late `D n` inside any prescribed
power of the maximal ideal. Artin–Rees gives a power whose intersection with
`D 1` lies in `(x)`. Thus `D (n+1) ≤ (x)` for some `n`, and cancellation
shows that `y` acts injectively on `D n / x D n`. The ideal `D n`, viewed
as a module over the original ring, is the desired witness.
-/

namespace OMA.SmallCM2

open IsLocalRing RingTheory.Sequence

universe u

section Parameters

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A generating set of the right size with the maximal ideal minimal over it
is a system of parameters, since every prime of a local ring lies under its maximal ideal. -/
theorem exists_parameters : ∃ rs : List R, IsSystemOfParameters R rs := by
  classical
  obtain ⟨s, hmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  refine ⟨s.toList, ⟨?_, ?_⟩⟩
  · rw [Finset.length_toList, ← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hcard
  · have heq : Ideal.ofList s.toList = Ideal.span (s : Set R) := by
      unfold Ideal.ofList
      congr 1
      ext x
      exact Finset.mem_toList
    rw [heq]
    refine le_antisymm ((inferInstance : (maximalIdeal R).IsPrime).radical_le_iff.mpr hmin.le) ?_
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun q ⟨hq, hp⟩ ↦ hmin.2 ⟨hp, hq⟩ (le_maximalIdeal hp.ne_top)

theorem exists_parameters_pair (hd : ringKrullDim R = 2) :
    ∃ x y : R, IsSystemOfParameters R [x, y] := by
  obtain ⟨rs, hs⟩ := exists_parameters R
  have hlen : rs.length = 2 := by exact_mod_cast hs.length_eq.trans hd
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  exact ⟨x, y, hs⟩

theorem smallCM_of_dim_le_one (hd : ringKrullDim R ≤ 1) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), Module.IsSmallCohenMacaulay R M := by
  obtain ⟨rs, hs⟩ := exists_parameters R
  have hlen : rs.length ≤ 1 := by exact_mod_cast hs.length_eq.trans_le hd
  cases rs with
  | nil =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, [], hs, .nil R R⟩
  | cons x tail =>
    have htail : tail = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst tail
    obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ maximalIdeal R)
    have : P.IsPrime := hP.isPrime
    have hstrict : P ≠ maximalIdeal R := by
      intro h
      have hh := Ideal.height_eq_zero_iff.mpr hP
      rw [h] at hh
      have hd0 : ringKrullDim R = 0 := by rw [← maximalIdeal_height_eq_ringKrullDim, hh]; rfl
      simpa [hd0] using hs.length_eq
    have hx : x ∉ P := by
      intro hx
      apply hstrict
      apply le_antisymm hle
      rw [← hs.radical_eq]
      exact ‹P.IsPrime›.radical_le_iff.mpr (by simpa [Ideal.ofList_singleton] using hx)
    refine ⟨R ⧸ P, inferInstance, inferInstance, inferInstance, [x], hs, ?_⟩
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr
    · rw [isWeaklyRegular_singleton_iff]
      intro a b h
      exact mul_left_cancel₀ (show Ideal.Quotient.mk P x ≠ 0 from
        fun hx0 ↦ hx ((Ideal.Quotient.eq_zero_iff_mem).mp hx0)) h
    · exact fun z hz ↦ hs.mem_maximalIdeal hz

end Parameters

section Components

/-- A longest chain of primes survives in the quotient by a minimal prime below its head. -/
theorem exists_fullDim_minimalPrime (R : Type*) [CommRing R] [FiniteRingKrullDim R] :
    ∃ P ∈ minimalPrimes R, ringKrullDim (R ⧸ P) = ringKrullDim R := by
  let c := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (J := c.head.asIdeal) bot_le
  let p : PrimeSpectrum R := ⟨P, hP.1.1⟩
  refine ⟨P, hP, le_antisymm (ringKrullDim_quotient_le P) ?_⟩
  rw [ringKrullDim_quotient]
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (Set.Ici p)
  rw [← Order.coheight_eq_krullDim_Ici, Order.krullDim_eq_length_of_finiteDimensionalOrder]
  exact WithBot.coe_le_coe.mpr (Order.length_le_coheight (p := c) (x := p) hle)

/-- A nontrivial quotient of a complete Noetherian local ring is complete at its maximal ideal. -/
theorem adicComplete_quotient (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (P : Ideal R) [IsLocalRing (R ⧸ P)] :
    IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective]
  apply (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (R ⧸ P)).mpr
  refine (isAdicComplete_iff _ _).mpr ⟨inferInstance, AdicCompletion.of_surjective_iff.mp ?_⟩
  let q := (Ideal.Quotient.mkₐ R P).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  intro z
  obtain ⟨v, hv⟩ := AdicCompletion.map_surjective (maximalIdeal R) hq z
  obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective (maximalIdeal R) R v
  exact ⟨q a, (AdicCompletion.map_of (maximalIdeal R) q a).symm.trans hv⟩

end Components

section ArtinRees

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsLocalRing A] in
/-- On a finite ideal, elementwise annihilation modulo I by powers of y is uniform. -/
private theorem uniform_exponent (I J : Ideal A) (y : A)
    (h : ∀ a ∈ J, ∃ k : ℕ, a * y ^ k ∈ I) :
    ∃ k : ℕ, ∀ a ∈ J, a * y ^ k ∈ I := by
  let F : ℕ →o Ideal A :=
    { toFun := fun k => I.colon {y ^ k}
      monotone' := monotone_nat_of_le_succ fun k a ha => by
        rw [Submodule.mem_colon_singleton] at ha ⊢
        simpa [pow_succ, mul_assoc, smul_eq_mul] using I.mul_mem_right y ha }
  obtain ⟨k, hk⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨k, fun a ha => ?_⟩
  obtain ⟨j, hj⟩ := h a ha
  have hmem : a ∈ F j := Submodule.mem_colon_singleton.mpr hj
  have hmem' := F.monotone (le_max_left j k) hmem
  rw [← hk (max j k) (le_max_right j k)] at hmem'
  exact Submodule.mem_colon_singleton.mp hmem'

/-- The subspace topology on the y-power torsion modulo x is discrete. -/
theorem exists_pow_inf_le_parameter {x y : A} (hs : IsSystemOfParameters A [x, y])
    (J : Ideal A) (ht : ∀ a ∈ J, ∃ k : ℕ, a * y ^ k ∈ Ideal.span {x}) :
    ∃ n : ℕ, maximalIdeal A ^ n ⊓ J ≤ Ideal.span {x} := by
  let I : Ideal A := Ideal.span {x}
  let C := I.colon (J : Set A)
  obtain ⟨k, hk⟩ := uniform_exponent I J y ht
  have hx : x ∈ C := Submodule.mem_colon.mpr fun a _ =>
    I.mul_mem_right a (Ideal.subset_span (Set.mem_singleton x))
  have hy : y ^ k ∈ C := Submodule.mem_colon.mpr fun a ha => by
    simpa [smul_eq_mul, mul_comm] using hk a ha
  have hr : maximalIdeal A ≤ C.radical := by
    rw [← hs.radical_eq, Ideal.radical_le_radical_iff, Ideal.ofList_cons, Ideal.ofList_singleton]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.le_radical hx))
      ((Ideal.span_singleton_le_iff_mem _).mpr ⟨k, hy⟩)
  obtain ⟨d, hd⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr
    (IsNoetherian.noetherian _)
  obtain ⟨e, he⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal A) J
  have hprod : C * J ≤ I := Ideal.mul_le.mpr fun _ h _ ha => Submodule.mem_colon.mp h _ ha
  specialize he (d + e) (by omega)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel] at he
  exact ⟨d + e, he.le.trans ((mul_le_mul' hd inf_le_right).trans hprod)⟩

end ArtinRees

section SaturatedPowers

/-- The contraction of the principal ideal generated by the `n`th power of `x`
after inverting `y`, described by clearing a power of `y`. -/
def satPower {A : Type*} [CommRing A] (x y : A) (n : ℕ) : Ideal A where
  carrier := {a | ∃ k : ℕ, y ^ k * a ∈ Ideal.span {x ^ n}}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have ha := (Ideal.span {x ^ n}).mul_mem_left (y ^ l) hk
    have hb := (Ideal.span {x ^ n}).mul_mem_left (y ^ k) hl
    convert (Ideal.span {x ^ n}).add_mem ha hb using 1
    ring
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    convert (Ideal.span {x ^ n}).mul_mem_left c hk using 1
    ring

theorem mem_satPower {A : Type*} [CommRing A] {x y a : A} {n : ℕ} :
    a ∈ satPower x y n ↔ ∃ k : ℕ, y ^ k * a ∈ Ideal.span {x ^ n} := Iff.rfl

open scoped Pointwise

/-- Once a saturated power is contained in `(x)`, the preceding saturated ideal
supports the parameter pair as a regular sequence. -/
theorem regular_satPower {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] {x y : A} (hx : x ≠ 0)
    (hxm : x ∈ maximalIdeal A) (hym : y ∈ maximalIdeal A) {n : ℕ}
    (hsmall : satPower x y (n + 1) ≤ Ideal.span {x}) :
    IsRegular (satPower x y n) [x, y] := by
  let D := satPower x y n
  have hpow : x ^ n ∈ D := mem_satPower.mpr ⟨0, by simp⟩
  have : Nontrivial D := ⟨⟨⟨x ^ n, hpow⟩, 0, fun h ↦
    pow_ne_zero n hx (congrArg Subtype.val h)⟩⟩
  have hm : ∀ a ∈ [x, y], a ∈ maximalIdeal A := by simpa using And.intro hxm hym
  apply (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr
  apply IsWeaklyRegular.cons ((show IsSMulRegular A x from fun _ _ h ↦
    mul_left_cancel₀ hx h).submodule D x)
  apply IsWeaklyRegular.cons _ (IsWeaklyRegular.nil _ _)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro a ha
  obtain ⟨b, -, hba⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha
  have heq : x * (b : A) = y * (a : A) := congrArg Subtype.val hba
  obtain ⟨k, hk⟩ := mem_satPower.mp b.property
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
  have hnext : (a : A) ∈ satPower x y (n + 1) := by
    apply mem_satPower.mpr
    refine ⟨k + 1, Ideal.mem_span_singleton.mpr ⟨c, ?_⟩⟩
    calc
      y ^ (k + 1) * (a : A) = y ^ k * (y * (a : A)) := by ring
      _ = x * (y ^ k * (b : A)) := by rw [← heq]; ring
      _ = x ^ (n + 1) * c := by rw [hc]; ring
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hsmall hnext)
  obtain ⟨l, hl⟩ := mem_satPower.mp hnext
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hl
  have hdD : d ∈ D := by
    apply mem_satPower.mpr
    refine ⟨l, Ideal.mem_span_singleton.mpr ⟨e, mul_left_cancel₀ hx ?_⟩⟩
    calc
      x * (y ^ l * d) = y ^ l * (a : A) := by rw [hd]; ring
      _ = x * (x ^ n * e) := by rw [he]; ring
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨⟨d, hdD⟩, Submodule.mem_top, Subtype.ext hd.symm⟩

end SaturatedPowers

section Separation

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A prime minimal over the first parameter cannot contain the second. -/
theorem exists_prime_separating_parameters {x y : R} (hs : IsSystemOfParameters R [x, y]) :
    ∃ p : Ideal R, p.IsPrime ∧ x ∈ p ∧ y ∉ p := by
  have hx : x ∈ maximalIdeal R := hs.mem_maximalIdeal (by simp)
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  refine ⟨p, hp.isPrime, hp.le (Ideal.mem_span_singleton_self x), ?_⟩
  intro hy
  have hall : Ideal.ofList [x, y] ≤ p := by
    simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq] using
      sup_le hp.le ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  have heq : p = maximalIdeal R := hpm.antisymm <|
    hs.radical_eq ▸ hp.isPrime.radical_le_iff.mpr hall
  have hht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  rw [heq] at hht
  have hh : ringKrullDim R ≤ 1 := by
    rw [← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hht
  have hlen := hs.length_eq.trans_le hh
  norm_num at hlen

theorem parameter_pair_nonzero {x y : R} (hs : IsSystemOfParameters R [x, y]) :
    x ≠ 0 ∧ y ≠ 0 := by
  have rev : IsSystemOfParameters R [y, x] := ⟨hs.length_eq, by
    simpa [sup_comm] using hs.radical_eq⟩
  obtain ⟨p, _, _, hx⟩ := exists_prime_separating_parameters rev
  obtain ⟨q, _, _, hy⟩ := exists_prime_separating_parameters hs
  exact ⟨fun h ↦ hx (h ▸ p.zero_mem), fun h ↦ hy (h ▸ q.zero_mem)⟩

/-- Localizing above the first parameter turns the second into a unit.
Krull intersection at this prime then kills the intersection of the saturations. -/
theorem eq_zero_of_parameter_divisibility [IsDomain R] {x y a : R}
    (hs : IsSystemOfParameters R [x, y])
    (ha : ∀ n : ℕ, ∃ k : ℕ, x ^ n ∣ y ^ k * a) : a = 0 := by
  obtain ⟨p, hp, hx, hy⟩ := exists_prime_separating_parameters hs
  let B := Localization.AtPrime p
  let f := algebraMap R B
  have hu : IsUnit (f y) := (IsLocalization.AtPrime.isUnit_to_map_iff B p y).mpr hy
  have hx' : f x ∈ maximalIdeal B := (IsLocalization.AtPrime.to_map_mem_maximal_iff B p x).mpr hx
  have hall : f a ∈ ⨅ n : ℕ, maximalIdeal B ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    obtain ⟨k, hk⟩ := ha n
    have hd : f x ^ n ∣ f y ^ k * f a := by simpa only [map_pow, map_mul] using map_dvd f hk
    have hmem : f y ^ k * f a ∈ maximalIdeal B ^ n :=
      Ideal.mem_of_dvd _ hd (Ideal.pow_mem_pow hx' n)
    exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow k)).mp hmem
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top] at hall
  exact (FaithfulSMul.algebraMap_injective R B) (by simpa [f] using hall)

end Separation

section Chevalley

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

private theorem powQuotientArtinian (k : ℕ) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ k) := by
  let I := maximalIdeal R ^ k
  by_cases hI : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI
    exact inferInstanceAs (IsArtinianRing (R ⧸ I))
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ I)).mpr
  refine ⟨k, ?_⟩
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

private theorem stable_mod_power (D : ℕ → Ideal R) (hD : Antitone D) (k : ℕ) :
    ∃ j, ∀ n, j ≤ n → D j ⊔ maximalIdeal R ^ k = D n ⊔ maximalIdeal R ^ k := by
  let I := maximalIdeal R ^ k
  let := powQuotientArtinian (R := R) k
  let f : ℕ →o (Ideal (R ⧸ I))ᵒᵈ :=
    ⟨fun n ↦ (D n).map (Ideal.Quotient.mk I), fun _ _ h ↦ Ideal.map_mono (hD h)⟩
  obtain ⟨j, hj⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨j, fun n hn ↦ ?_⟩
  have eq : (D j).map (Ideal.Quotient.mk I) = (D n).map (Ideal.Quotient.mk I) := hj n hn
  ext x
  simpa only [← Ideal.mem_quotient_iff_mem_sup] using
    (show Ideal.Quotient.mk I x ∈ (D j).map (Ideal.Quotient.mk I) ↔
        Ideal.Quotient.mk I x ∈ (D n).map (Ideal.Quotient.mk I) from
      eq ▸ Iff.rfl)

private theorem mem_of_mem_sup_all_powers {J : Ideal R} {a : R}
    (ha : ∀ k : ℕ, a ∈ J ⊔ maximalIdeal R ^ k) : a ∈ J := by
  apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
  apply (inferInstance : IsHausdorff (maximalIdeal R) (R ⧸ J)).haus
  intro k
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (ha k)
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, SModEq.zero]
  simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using
    (Submodule.smul_mem_smul hc (show (1 : R ⧸ J) ∈ (⊤ : Submodule R (R ⧸ J)) from trivial))

/-- In a complete Noetherian local ring, a descending family of ideals with zero intersection
is eventually contained in each power of the maximal ideal. -/
theorem chevalley_ideals [IsAdicComplete (maximalIdeal R) R]
    (D : ℕ → Ideal R) (hD : Antitone D) (hzero : ⨅ n, D n = ⊥) (k : ℕ) :
    ∃ n, D n ≤ maximalIdeal R ^ k := by
  classical
  let m := maximalIdeal R
  -- At each precision, take the stable image of the descending ideals.
  choose j hj using stable_mod_power D hD
  let C (r : ℕ) := D (j r) ⊔ m ^ r
  have hC (r n : ℕ) : C r ≤ D n ⊔ m ^ r := by
    rw [show C r = D (max (j r) n) ⊔ m ^ r from hj r _ (le_max_left _ _)]
    exact sup_le_sup_right (hD (le_max_right _ _)) _
  have lift (r : ℕ) (a : C r) : ∃ b : C (r + 1), (a : R) - b ∈ m ^ r := by
    obtain ⟨b, hb, c, hc, eq⟩ := Submodule.mem_sup.mp (hC r (j (r + 1)) a.property)
    refine ⟨⟨b, Submodule.mem_sup_left hb⟩, ?_⟩
    simpa [← eq] using hc
  choose next hnext using lift
  refine ⟨j k, fun x hx ↦ ?_⟩
  let s : (i : ℕ) → C (k + i) :=
    Nat.rec (motive := fun i ↦ C (k + i)) ⟨x, Submodule.mem_sup_left hx⟩
      (fun i a ↦ next (k + i) a)
  have step (i : ℕ) : (s i).val - (s (i + 1)).val ∈ m ^ (k + i) :=
    hnext (k + i) (s i)
  have coherent {i l : ℕ} (h : i ≤ l) : (s i).val - (s l).val ∈ m ^ (k + i) := by
    induction l, h using Nat.le_induction with
    | base => simp
    | succ l hl ih =>
      have hh := Ideal.pow_le_pow_right (I := m) (Nat.add_le_add_left hl k) (step l)
      simpa using (m ^ (k + i)).add_mem ih hh
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete m R).prec
    (f := fun i ↦ (s i).val) (fun {i l} h ↦ by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_add_left _ _) (coherent h))
  have limdiff (i : ℕ) : (s i).val - L ∈ m ^ i := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL i
  -- Each ideal D n is closed, so it contains the limit of the compatible lifts.
  have hz : L ∈ ⨅ n, D n := by
    refine (Submodule.mem_iInf _).mpr fun n ↦ mem_of_mem_sup_all_powers fun i ↦ ?_
    have hs : (s i).val ∈ D n ⊔ m ^ i :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_add_left _ _)) (D n))
        (hC (k + i) n (s i).property)
    simpa using (D n ⊔ m ^ i).sub_mem hs (Submodule.mem_sup_right (limdiff i))
  rw [hzero, Submodule.mem_bot] at hz
  have hi : (s k).val ∈ m ^ k := by simpa [hz] using limdiff k
  have h0 : (s 0).val - (s k).val ∈ m ^ k := by simpa using coherent (Nat.zero_le k)
  simpa [s] using (m ^ k).add_mem h0 hi

end Chevalley

section Transfer

/-- Taking the image of a parameter list in a full-dimensional quotient preserves it. -/
theorem parameters_map_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hd : ringKrullDim S = ringKrullDim R) {rs : List R} (hs : IsSystemOfParameters R rs) :
    IsSystemOfParameters S (rs.map f) := by
  constructor
  · rw [List.length_map, hd, hs.length_eq]
  · rw [← Ideal.map_ofList]
    refine le_antisymm ?_ ?_
    · apply (inferInstance : (maximalIdeal S).IsPrime).radical_le_iff.mpr
      rw [← map_maximalIdeal_of_surjective f hf]
      exact Ideal.map_mono (Ideal.le_radical.trans hs.radical_eq.le)
    · rw [← map_maximalIdeal_of_surjective f hf, ← hs.radical_eq]
      exact Ideal.map_radical_le f

private theorem satPower_antitone {A : Type*} [CommRing A] (x y : A) :
    Antitone (satPower x y) := by
  rintro i j hij a ⟨k, hk⟩
  exact ⟨k, Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow x hij) hk⟩

private theorem satPower_inf_eq_bot {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] {x y : A} (hs : IsSystemOfParameters A [x, y]) :
    (⨅ n : ℕ, satPower x y n) = ⊥ := by
  refine bot_unique fun a ha => ?_
  apply eq_zero_of_parameter_divisibility hs
  intro n
  obtain ⟨k, hk⟩ := mem_satPower.mp ((Ideal.mem_iInf.mp ha) n)
  exact ⟨k, Ideal.mem_span_singleton.mp hk⟩

/-- A separated descending sequence of saturated powers yields a finite regular module
as soon as the sequence is cofinal with the powers of the maximal ideal. -/
theorem exists_regular_ideal_of_cofinal {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] {x y : A} (hs : IsSystemOfParameters A [x, y])
    (hc : ∀ k : ℕ, ∃ n : ℕ, satPower x y n ≤ maximalIdeal A ^ k) :
    ∃ J : Ideal A, IsRegular J [x, y] := by
  obtain ⟨k, hk⟩ := exists_pow_inf_le_parameter hs (satPower x y 1) (by
    rintro a ⟨i, hi⟩
    exact ⟨i, by simpa only [pow_one, mul_comm] using hi⟩)
  obtain ⟨n, hn⟩ := hc k
  have hle := satPower_antitone x y
  exact ⟨satPower x y n, regular_satPower (parameter_pair_nonzero hs).1
    (hs.mem_maximalIdeal (by simp)) (hs.mem_maximalIdeal (by simp))
    ((le_inf ((hle (Nat.le_succ n)).trans hn) (hle (by omega))).trans hk)⟩

/-- Restrict the action on an ideal of the component to the original local ring. -/
theorem smallCM_of_regular_quotient_ideal {R : Type u} [CommRing R] [IsLocalRing R]
    (P : Ideal R) [IsNoetherianRing (R ⧸ P)] {rs : List R} (hs : IsSystemOfParameters R rs)
    (J : Ideal (R ⧸ P)) (hr : IsRegular J (rs.map (Ideal.Quotient.mk P))) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), Module.IsSmallCohenMacaulay R M := by
  have : Module.Finite R J := Module.Finite.trans (R ⧸ P) J
  refine ⟨J, inferInstance, inferInstance, this, rs, hs, ?_⟩
  exact (AddEquiv.refl J).isRegular_congr (as := rs) (bs := rs.map (Ideal.Quotient.mk P))
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ _ => rfl)) |>.mpr hr

end Transfer

theorem exists_smallCM_dim_two (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (hd : ringKrullDim R = 2) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), Module.IsSmallCohenMacaulay R M := by
  obtain ⟨x, y, hs⟩ := exists_parameters_pair R hd
  obtain ⟨P, hp, hdim⟩ := exists_fullDim_minimalPrime R
  let A := R ⧸ P
  have : P.IsPrime := hp.isPrime
  let f := Ideal.Quotient.mk P
  have : IsLocalRing A := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal A) A := adicComplete_quotient R P
  have hs' : IsSystemOfParameters A [f x, f y] :=
    parameters_map_of_surjective f Ideal.Quotient.mk_surjective hdim hs
  obtain ⟨J, hJ⟩ := exists_regular_ideal_of_cofinal hs' <|
    chevalley_ideals (satPower (f x) (f y)) (satPower_antitone _ _) (satPower_inf_eq_bot hs')
  exact smallCM_of_regular_quotient_ideal P hs J hJ

end OMA.SmallCM2

theorem OMA.solution :
    type_of% @SmallCohenMacaulayModules.exists_isSmallCohenMacaulay.variants.ringKrullDim_le_two := by
  intro R _ _ _ _ hd
  by_cases h : ringKrullDim R ≤ 1
  · exact OMA.SmallCM2.smallCM_of_dim_le_one R h
  · apply OMA.SmallCM2.exists_smallCM_dim_two R
    obtain ⟨rs, hrs⟩ := OMA.SmallCM2.exists_parameters R
    rw [← hrs.length_eq] at hd h ⊢
    have hlen : rs.length ≤ 2 := by exact_mod_cast hd
    have hgt : ¬ rs.length ≤ 1 := fun h' => h (by exact_mod_cast h')
    exact_mod_cast (show rs.length = 2 by omega)
