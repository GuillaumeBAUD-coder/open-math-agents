import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
import Mathlib

/-! The polynomial-value sieve for Erdős 976. For weights with divisor-bounded
growth, a dyadic short-sum estimate on polynomials with no fixed prime divisor
is enough. Affine residue classes handle fixed divisors, an upper bound on the
prime product, proved here, supplies one inverse logarithm, and a prefix-sum estimate gives
the result on the full interval.

The analytic short-sum input follows Nair and Tenenbaum, “Short sums of certain
arithmetic functions”, Acta Math. 180 (1998), Corollary 3. The affine
normalization is also formalized by Jason Davies in nair-tenenbaum-short-sums
at 9c3c9236a66f9ba1e04a237089ff836adde0cd6c. The prime-product proof adapts
@steveDOTdigital’s prime-root Mertens bound in Open Math Agents #3752. -/

section
/- From @steveDOTdigital, accepted OMA #3752, prime-root Mertens lower bound. -/
namespace OMA.Erdos975Lower
open Polynomial Finset Filter Asymptotics


lemma irreducible_monic_replacement (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    Irreducible f.integralNormalization := by
  let F := f.map (Int.castRingHom ℚ)
  let G := f.integralNormalization.map (Int.castRingHom ℚ)
  let a := (f.leadingCoeff : ℚ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (leadingCoeff_ne_zero.mpr hf.ne_zero)
  let : Invertible a := invertibleOfNonzero ha
  let e := algEquivCMulXAddC a 0
  have mon := monic_integralNormalization hf.ne_zero
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mpr
  change Irreducible G
  apply (MulEquiv.irreducible_iff e).mp
  have he : e G = C (a^(f.natDegree-1))*F := by
    apply Polynomial.funext
    intro x
    change (G.comp (C a * X + C 0)).eval x = (C (a^(f.natDegree-1))*F).eval x
    simp only [map_zero, add_zero, eval_comp, eval_mul, eval_C, eval_X, G, F, eval_map]
    exact integralNormalization_eval₂_leadingCoeff_mul (p:=f) (by omega) (Int.castRingHom ℚ) x
  rw [he]
  have unit : IsUnit (C (a^(f.natDegree-1)) : ℚ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha))
  exact (irreducible_isUnit_mul unit).2
    ((IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf)

-- The representatives in [0,d) enumerate the entire residue ring.
lemma count_root_ring (f : ℤ[X]) (d : ℕ) [NeZero d] :
    Nat.count (fun r : ℕ => (d:ℤ) ∣ f.eval (r:ℤ)) d =
      ∑ x : ZMod d, (if f.eval₂ (Int.castRingHom (ZMod d)) x = 0 then 1 else 0 : ℕ) := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_filter, ← Fin.sum_univ_eq_sum_range,
    ← Equiv.sum_comp (ZMod.finEquiv d).toEquiv]
  apply sum_congr rfl
  intro i _
  have coeff : (ZMod.finEquiv d) i = (i.val : ZMod d) := by
    have v : ((ZMod.finEquiv d) i).val = i.val := by
      cases d with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    rw [← v, ZMod.natCast_zmod_val]
  rw [show (ZMod.finEquiv d).toEquiv i = (i.val:ZMod d) from coeff]
  have h := Polynomial.eval₂_hom (p:=f) (Int.castRingHom (ZMod d)) (i.val:ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at h
  simp only [h, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma unit_residue_of_coprime (a : ℤ) (d : ℕ) (hc : d.Coprime a.natAbs) :
    IsUnit (a : ZMod d) := by
  cases a with
  | ofNat n => simpa using (ZMod.isUnit_iff_coprime n d).mpr hc.symm
  | negSucc n =>
    have u : IsUnit ((n+1 : ℕ) : ZMod d) :=
      (ZMod.isUnit_iff_coprime (n+1) d).mpr hc.symm
    simpa using u.neg

-- Multiplication by the leading coefficient permutes the residue ring when
-- it is a unit, so normalization preserves the number of zeros.
lemma monic_residue_counts (f : ℤ[X]) (hf : f.natDegree ≠ 0) (d : ℕ) (hd : 0 < d)
    (hc : d.Coprime f.leadingCoeff.natAbs) :
    Nat.count (fun r : ℕ => (d:ℤ) ∣ f.integralNormalization.eval (r:ℤ)) d =
      Nat.count (fun r : ℕ => (d:ℤ) ∣ f.eval (r:ℤ)) d := by
  classical
  let : NeZero d := ⟨by omega⟩
  rw [count_root_ring, count_root_ring]
  let φ := Int.castRingHom (ZMod d)
  have hu := unit_residue_of_coprime f.leadingCoeff d hc
  let e := Units.mulLeft hu.unit
  have changeSum := Equiv.sum_comp e
    (fun x => if f.integralNormalization.eval₂ φ x = 0 then (1:ℕ) else 0)
  rw [← changeSum]
  apply sum_congr rfl
  intro y _
  have hy : e y = φ f.leadingCoeff * y := by
    change (hu.unit : ZMod d)*y = _
    rw [hu.unit_spec]
    rfl
  rw [hy, integralNormalization_eval₂_leadingCoeff_mul (by omega)]
  have u : IsUnit ((φ f.leadingCoeff)^(f.natDegree-1)) := hu.pow _
  simp only [u.isRegular.left.mul_left_eq_zero_iff]
  rfl

namespace PrimeIdeals

open Finset Polynomial UniqueFactorizationMonoid

open Finset Polynomial UniqueFactorizationMonoid
lemma linear_factor_count {k : Type*} [Field k] [Fintype k] [DecidableEq k] (f : k[X])
    (hf : f ≠ 0) :
    ((normalizedFactors f).toFinset.filter (fun q => q.natDegree = 1)).card =
      (univ.filter (fun x : k => f.eval x = 0)).card := by
  classical
  let R := univ.filter (fun x : k => f.eval x = 0)
  let L := (normalizedFactors f).toFinset.filter (fun q => q.natDegree = 1)
  let q (x : k) : k[X] := X-C x
  have same : R.image q = L := by
    ext a
    constructor
    · intro ha
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      refine mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ?_,natDegree_X_sub_C _⟩
      exact (Polynomial.mem_normalizedFactors_iff hf).mpr
        ⟨irreducible_X_sub_C _,monic_X_sub_C _,dvd_iff_isRoot.mpr (mem_filter.mp hx).2⟩
    · intro ha
      obtain ⟨hfactor,hdeg⟩ := mem_filter.mp ha
      have facts := (Polynomial.mem_normalizedFactors_iff hf).mp (Multiset.mem_toFinset.mp hfactor)
      have eq : q (-(a.coeff 0)) = a := by simpa [q] using (facts.2.1.eq_X_add_C hdeg).symm
      have root : f.IsRoot (-(a.coeff 0)) := dvd_iff_isRoot.mp (show q _ ∣ f by rw [eq]; exact facts.2.2)
      exact mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,root⟩,eq⟩
  have inj : Function.Injective q := fun a b h => C_injective (sub_right_inj.mp h)
  change L.card = R.card
  rw [← same,card_image_of_injective _ inj]


open Ideal NumberField Algebra Polynomial
lemma powerbasis_exponent_pos (K : Type*) [Field K] [NumberField K]
    (B : PowerBasis ℚ K) (θ : 𝓞 K) (gen : B.gen = (θ:K)) :
    0 < RingOfIntegers.exponent θ := by
  have hint : IsIntegral ℤ B.gen := gen ▸ θ.2
  have dint : IsIntegral ℤ (discr ℚ B.basis) := discr_isIntegral ℚ (fun i => by
    rw [B.basis_eq_pow]; exact hint.pow _)
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp dint
  have dn := (discr_isUnit_of_basis ℚ B.basis).ne_zero
  have zn : z ≠ 0 := by intro h; apply dn; rw [← hz,h,map_zero]
  have mem : z ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change (algebraMap ℤ (𝓞 K) z) ∈ conductor ℤ θ
    apply mem_conductor_iff.mpr
    intro t
    have into := discr_mul_isIntegral_mem_adjoin ℚ hint t.2
    rw [gen, adjoin_singleton_eq_range_aeval] at into
    obtain ⟨q,hq⟩ := into
    rw [adjoin_singleton_eq_range_aeval]
    refine ⟨q, NumberField.RingOfIntegers.ext ?_⟩
    have project := Polynomial.aeval_algebraMap_apply K θ q
    change algebraMap (𝓞 K) K (aeval θ q) = algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) z * t)
    rw [← project, map_mul, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq]
    change aeval ((algebraMap (𝓞 K) K) θ) q = discr ℚ B.basis • (t:K) at hq
    rw [hq, ← hz, Algebra.smul_def]
    simp
  by_contra! no
  have h0 : RingOfIntegers.exponent θ = 0 := by omega
  have bot := Ideal.absNorm_eq_zero_iff.mp h0
  rw [bot] at mem
  exact zn (Ideal.mem_bot.mp mem)


lemma choose_field (g : ℤ[X]) (hm : g.Monic) (irr : Irreducible g) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : 𝓞 K),
        minpoly ℤ θ = g ∧ 0 < RingOfIntegers.exponent θ := by
  let F := g.map (algebraMap ℤ ℚ)
  have irF : Irreducible F := hm.irreducible_iff_irreducible_map_fraction_map.mp irr
  let : Fact (Irreducible F) := ⟨irF⟩
  let K := AdjoinRoot F
  let B := AdjoinRoot.powerBasis irF.ne_zero
  let : FiniteDimensional ℚ K := B.finite
  let : NumberField K := ⟨⟩
  have zero : aeval (AdjoinRoot.root F) g = 0 := by
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self
  let θ : 𝓞 K := ⟨AdjoinRoot.root F,⟨g,hm,zero⟩⟩
  have gen : B.gen = (θ:K) := AdjoinRoot.powerBasis_gen irF.ne_zero
  refine ⟨K,inferInstance,inferInstance,θ,?_,powerbasis_exponent_pos K B θ gen⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral]
  change minpoly ℚ (AdjoinRoot.root F) = F
  apply (minpoly.eq_of_irreducible_of_monic irF ?_ (hm.map _)).symm
  change aeval (AdjoinRoot.root F) (g.map (algebraMap ℤ ℚ)) = 0
  rw [Polynomial.aeval_map_algebraMap]
  exact zero


open NumberField Ideal IsDedekindDomain


lemma fiber_spec (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)) : Set (Ideal (𝓞 K))) = (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := by
  let : Fact p.Prime := ⟨hp⟩
  let : (Ideal.span {(p:ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  exact IsDedekindDomain.coe_primesOverFinset (by simp [hp.ne_zero]) _

lemma fiber_count (K : Type*) [Field K] [NumberField K] (θ : 𝓞 K)
    {p : ℕ} (hp : p.Prime) (good : ¬p ∣ RingOfIntegers.exponent θ) :
    (((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))).filter (fun I => I.inertiaDeg ℤ = 1)).card =
      Nat.count (fun r : ℕ => (p:ℤ) ∣ (minpoly ℤ θ).eval (r:ℤ)) p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let G := RingOfIntegers.monicFactorsMod θ p
  let e : ↥((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))) ≃ ↥G := (Equiv.setCongr (fiber_spec K hp)).trans
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod good)
  have eq (i : ↥((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)))) : i.val.inertiaDeg ℤ = (e i).val.natDegree := by
    have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      good (e i).prop
    change ((e.symm (e i)).val).inertiaDeg ℤ = _ at h
    rwa [Equiv.symm_apply_apply] at h
  have bij : (((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))).filter (fun I => I.inertiaDeg ℤ = 1)).card =
      (G.filter (fun q => q.natDegree = 1)).card := by
    apply card_bij (fun i hi => (e ⟨i,(mem_filter.mp hi).1⟩).val)
    · intro i hi
      exact mem_filter.mpr ⟨(e _).prop,(eq ⟨i,(mem_filter.mp hi).1⟩).symm.trans (mem_filter.mp hi).2⟩
    · intro i hi j hj h
      exact congrArg Subtype.val (e.injective (Subtype.ext h))
    · intro q hq
      let a : ↥G := ⟨q,(mem_filter.mp hq).1⟩
      let i := e.symm a
      have hi : i.val.inertiaDeg ℤ = 1 := (eq i).trans (by simpa [i,a] using (mem_filter.mp hq).2)
      exact ⟨i.val,mem_filter.mpr ⟨i.prop,hi⟩,congrArg Subtype.val (e.apply_symm_apply a)⟩
  rw [bij, count_root_ring]
  rw [← Finset.card_filter]
  have non := ((minpoly.monic θ.isIntegral).map (Int.castRingHom (ZMod p))).ne_zero
  simpa only [G,RingOfIntegers.monicFactorsMod,Polynomial.eval_map] using
    linear_factor_count _ non


lemma fiber_info (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {I : Ideal (𝓞 K)} (h : I ∈ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))) :
    I.IsPrime ∧ I.under ℤ = Ideal.span {(p:ℤ)} ∧ 0 < I.inertiaDeg ℤ ∧
      p^(I.inertiaDeg ℤ) = I.absNorm := by
  have hh : I ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := (fiber_spec K hp) ▸ h
  let : I.IsPrime := hh.1
  let : I.LiesOver (Ideal.span {(p:ℤ)}) := hh.2
  exact ⟨hh.1,hh.2.over.symm,I.inertiaDeg_pos ℤ,I.pow_inertiaDeg p⟩

lemma fiber_card_le (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))).card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : (Ideal.span {(p:ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let V := (Ideal.span {(p:ℤ)}).primesOver (𝓞 K)
  let e : ↥((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))) ≃ ↥V := Equiv.setCongr (fiber_spec K hp)
  have id := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p:ℤ)}) (𝓞 K)
  rw [← id, ← Fintype.card_coe, Fintype.card_congr e, ← @Finset.card_univ (↥V) _, Finset.card_eq_sum_ones]
  apply sum_le_sum
  intro i _
  let : i.val.IsPrime := i.prop.1
  exact Nat.mul_pos (i.val.ramificationIdx_pos ℤ) (i.val.inertiaDeg_pos ℤ)

lemma belongs_to_fiber (K : Type*) [Field K] [NumberField K] {Q I : Ideal (𝓞 K)}
    (hQ : Prime Q) (hI : I ≠ 0) (dvd : Q ∣ I) :
    ∃ p : ℕ, p.Prime ∧ p ≤ I.absNorm ∧ Q ∈ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)) := by
  let : Q.IsPrime := Ideal.isPrime_of_prime hQ
  let m : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ.ne_zero
  obtain ⟨p,n,hn,mem,hp,eq⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
  let : Fact p.Prime := ⟨hp⟩
  have maxp := Int.ideal_span_isMaximal_of_prime p
  have under : Ideal.span {(p:ℤ)} = Q.under ℤ := maxp.eq_of_le
    (inferInstance : (Q.under ℤ).IsPrime).ne_top (by rw [Ideal.span_singleton_le_iff_mem]; change algebraMap ℤ (𝓞 K) (p:ℤ) ∈ Q; simpa using mem)
  have pd : p ∣ Q.absNorm := eq ▸ dvd_pow_self p (by omega)
  have pos : 0 < I.absNorm := Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨p,hp,Nat.le_of_dvd pos (pd.trans (map_dvd Ideal.absNorm dvd)),?_⟩
  have hmem : Q ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := ⟨inferInstance,⟨under⟩⟩
  change Q ∈ ((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)) : Set (Ideal (𝓞 K)))
  rw [fiber_spec K hp]
  exact hmem

open Finset Real Filter Ideal NumberField Topology

lemma weighted_prefix_lower (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (density : ∀ n : ℕ, c*n ≤ ∑ j ∈ range n, a j) (n : ℕ) :
    c*log ((n:ℝ)+1) ≤ ∑ j ∈ range n, a j/((j:ℝ)+1) := by
  let A (n : ℕ) := ∑ j ∈ range n, a j
  have strong (k : ℕ) : (A k-c*k)/((k:ℝ)+1) ≤
      (∑ j ∈ range k, a j/((j:ℝ)+1)) - c*(harmonic k:ℝ) := by
    induction k with
    | zero => simp [A]
    | succ k ih =>
      have step : A (k+1) = A k + a k := sum_range_succ ..
      have h1 : 0 < (k:ℝ)+1 := by positivity
      have h2 : 0 < ((k+1:ℕ):ℝ)+1 := by positivity
      have mono : (A (k+1)-c*(k+1:ℕ))/(((k+1:ℕ):ℝ)+1) ≤
          (A (k+1)-c*(k+1:ℕ))/((k:ℝ)+1) := by
        apply div_le_div_of_nonneg_left (sub_nonneg.mpr (density (k+1))) h1
        push_cast
        linarith
      calc
        _ ≤ _ := mono
        _ = (A k-c*k)/((k:ℝ)+1) + a k/((k:ℝ)+1) - c/((k:ℝ)+1) := by
          rw [step]; push_cast; field_simp; ring
        _ ≤ _ := by
          rw [sum_range_succ, harmonic_succ]
          push_cast
          rw [mul_add, ← div_eq_mul_inv]
          linarith
  have hn : 0 ≤ (A n-c*n)/((n:ℝ)+1) := div_nonneg (sub_nonneg.mpr (density n)) (by positivity)
  have hlog := mul_le_mul_of_nonneg_left (log_add_one_le_harmonic n) hc
  push_cast at hlog
  linarith [strong n]



lemma ideal_harmonic_lower (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*log ((n:ℝ)+1) ≤
      ∑ j ∈ range n, ((Nat.card {I : Ideal (𝓞 K) // absNorm I = j+1}):ℝ)/((j:ℝ)+1) := by
  classical
  let a (j : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // absNorm I = j+1})
  have shift (n : ℕ) : (∑ j ∈ range n, a j) = ∑ k ∈ Icc 1 n, ((Nat.card {I : Ideal (𝓞 K) // absNorm I = k}):ℝ) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]
  have lim : Tendsto (fun n : ℕ => (∑ j ∈ range n, a j)/(n:ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
    apply ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    intro n
    rw [shift]
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr 2
    -- Count by norm fibers, as in Mathlib's proof of the class number formula.
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  let R := NumberField.dedekindZeta_residue K
  have hR : 0 < R := NumberField.dedekindZeta_residue_pos K
  have ev := lim.eventually_const_lt (show R/2 < R by linarith)
  obtain ⟨M,hM⟩ := eventually_atTop.1 ev
  let c := min (R/2) (1/((M:ℝ)+1))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c,hc,fun n => weighted_prefix_lower a c hc.le (fun m => ?_) n⟩
  rcases m with _ | m
  · simp
  have hm : (0:ℝ)<((m+1:ℕ):ℝ) := by positivity
  by_cases h : M ≤ m+1
  · have hh := (lt_div_iff₀ hm).mp (hM (m+1) h)
    exact (mul_le_mul_of_nonneg_right (min_le_left ..) hm.le).trans hh.le
  · have one : a 0 = 1 := by simp [a, Ideal.absNorm_eq_one_iff]
    have atleast : 1 ≤ ∑ j ∈ range (m+1), a j := by
      rw [← one]
      exact single_le_sum (fun j _ => by dsimp [a]; positivity) (mem_range.mpr (Nat.succ_pos _))
    apply le_trans _ atleast
    calc
      _ ≤ (1/((M:ℝ)+1))*((m+1:ℕ):ℝ) := mul_le_mul_of_nonneg_right (min_le_right ..) hm.le
      _ ≤ 1 := by
        have lb : ((m+1:ℕ):ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast (by omega : m+1 ≤ M+1)
        rw [one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith


open Finset Real
set_option maxHeartbeats 1000000 in
lemma finite_euler_majorant {ι κ : Type*} [Fintype ι] (S : Finset κ)
    (e : κ → ι → ℕ) (inj : Set.InjOn e (S : Set κ)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (lt : ∀ i, w i < 1) :
    (∑ a ∈ S, ∏ i, (w i)^(e a i)) ≤ ∏ i, (1-w i)⁻¹ := by
  classical
  let M := S.sup (fun a => univ.sup (e a))
  have cap (a : κ) (ha : a ∈ S) (i : ι) : e a i < M+1 :=
    Nat.lt_succ_of_le ((le_sup (s:=univ) (f:=e a) (mem_univ i)).trans (le_sup (f:=fun a => univ.sup (e a)) ha))
  let Z (a : κ) : ι → Fin (M+1) := fun i => ⟨min (e a i) M, by omega⟩
  have val (a : κ) (ha : a ∈ S) (i : ι) : (Z a i).val = e a i :=
    min_eq_left (Nat.le_of_lt_succ (cap a ha i))
  have zj : Set.InjOn Z (S : Set κ) := by
    intro a ha b hb h
    apply inj ha hb
    funext i
    rw [← val a ha, ← val b hb, h]
  let F (v : ι → Fin (M+1)) := ∏ i, (w i)^((v i).val)
  have localbound (i : ι) : (∑ j : Fin (M+1), (w i)^j.val) ≤ (1-w i)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range]
    have hpos : 0 < 1-w i := by linarith [lt i]
    rw [← one_div, le_div_iff₀ hpos]
    have eq := geom_sum_mul (w i) (M+1)
    nlinarith [pow_nonneg (hw i) (M+1)]
  calc
    _ = ∑ a ∈ S, F (Z a) := by
      apply sum_congr rfl
      intro a ha
      simp only [F,val a ha]
    _ = ∑ v ∈ S.image Z, F v := (sum_image zj).symm
    _ ≤ ∑ v : ι → Fin (M+1), F v := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun v _ _ => prod_nonneg (fun i _ => pow_nonneg (hw i) _))
    _ = ∏ i, ∑ j : Fin (M+1), (w i)^j.val := (Fintype.prod_sum (fun (i : ι) (j : Fin (M+1)) => (w i)^j.val)).symm
    _ ≤ _ := prod_le_prod (fun i _ => sum_nonneg fun j _ => pow_nonneg (hw i) _) (fun i _ => localbound i)


-- Every ideal of norm at most N is a product of prime ideals over p ≤ N.
lemma ideal_euler_upper (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    (∑ j ∈ range N, ((Nat.card {I : Ideal (𝓞 K) // absNorm I = j+1}):ℝ)/((j:ℝ)+1)) ≤
      ∏ p ∈ (Icc 2 N).filter Nat.Prime, ∏ I ∈ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)), (1-((p:ℝ)⁻¹)^(I.inertiaDeg ℤ))⁻¹ := by
  classical
  let A := (Icc 2 N).filter Nat.Prime
  let U := A.biUnion (fun p : ℕ => IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))
  let T (j : ℕ) : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOfPred_absNorm_eq (j+1)).toFinset
  let S := (range N).biUnion T
  let norm (I : Ideal (𝓞 K)) : ℝ := I.absNorm
  have atn (j : ℕ) (I : Ideal (𝓞 K)) : I ∈ T j ↔ I.absNorm = j+1 := Set.Finite.mem_toFinset _
  have norm_at (j : ℕ) (I : Ideal (𝓞 K)) (h : I ∈ T j) : norm I = (j:ℝ)+1 := by
    dsimp [norm]; exact_mod_cast (atn j I).mp h
  have sdisj : (range N : Set ℕ).PairwiseDisjoint T := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro I hi hj
    exact ne (Nat.succ.inj (((atn i I).mp hi).symm.trans ((atn j I).mp hj)))
  have mass : (∑ j ∈ range N, ((Nat.card {I : Ideal (𝓞 K) // absNorm I = j+1}):ℝ)/((j:ℝ)+1)) =
      ∑ I ∈ S, (norm I)⁻¹ := by
    rw [sum_biUnion sdisj]
    apply sum_congr rfl
    intro j _
    have cnt : (Nat.card {I : Ideal (𝓞 K) // absNorm I = j+1}) = (T j).card :=
      Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq (j+1))
    rw [cnt]
    simp_rw [sum_congr rfl (fun I (hi : I ∈ T j) => congrArg Inv.inv (norm_at j I hi))]
    simp [div_eq_mul_inv]
  have ns (I : Ideal (𝓞 K)) (h : I ∈ S) : I ≠ 0 ∧ I.absNorm ≤ N := by
    obtain ⟨j,hj,hi⟩ := mem_biUnion.mp h
    have eq := (atn j I).mp hi
    have pos : 0 < I.absNorm := by omega
    exact ⟨fun hz => (Nat.ne_of_gt pos) (Ideal.absNorm_eq_zero_iff.mpr hz),eq ▸ mem_range.mp hj⟩
  let e (I : Ideal (𝓞 K)) (q : ↥U) : ℕ := (normalizedFactors I).count q.val
  have repr (I : Ideal (𝓞 K)) (h : I ∈ S) : (∏ q : ↥U, q.val^(e I q)) = I := by
    have hin : (normalizedFactors I).toFinset ⊆ U := by
      intro q hq
      have mem := Multiset.mem_toFinset.mp hq
      obtain ⟨p,hp,hle,inc⟩ := belongs_to_fiber K (prime_of_normalized_factor q mem) (ns I h).1
        (dvd_of_mem_normalizedFactors mem)
      exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,hle.trans (ns I h).2⟩,hp⟩,inc⟩
    change (∏ q : ↥U, q.val^((normalizedFactors I).count q.val)) = I
    rw [prod_coe_sort U (fun q => q^((normalizedFactors I).count q)), ← prod_multiset_count_of_subset _ _ hin]
    exact associated_iff_eq.mp (prod_normalizedFactors (ns I h).1)
  have inj : Set.InjOn e (S : Set (Ideal (𝓞 K))) := by
    intro I hI J hJ eq
    rw [← repr I hI, ← repr J hJ, eq]
  have wgt (q : ↥U) : 1 < norm q.val := by
    obtain ⟨p,hp,hq⟩ := mem_biUnion.mp q.prop
    have prime := (mem_filter.mp hp).2
    have inf := fiber_info K prime hq
    change (1:ℝ) < (q.val.absNorm:ℝ)
    exact_mod_cast (inf.2.2.2 ▸ (one_lt_pow₀ prime.one_lt inf.2.2.1.ne'))
  have vals (I : Ideal (𝓞 K)) (hi : I ∈ S) :
      (norm I)⁻¹ = ∏ q : ↥U, ((norm q.val)⁻¹)^(e I q) := by
    have eq := congrArg Ideal.absNorm (repr I hi)
    simp only [map_prod,map_pow] at eq
    dsimp [norm]
    rw [← eq, Nat.cast_prod, ← prod_inv_distrib]
    apply prod_congr rfl
    intro i _
    simp
  have disj : (A : Set ℕ).PairwiseDisjoint (fun p : ℕ => IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)) := by
    intro p hp q hq ne
    apply Finset.disjoint_left.mpr
    intro I hP hQ
    have E := (fiber_info K (mem_filter.mp hp).2 hP).2.1.symm.trans
      (fiber_info K (mem_filter.mp hq).2 hQ).2.1
    exact ne (by simpa using congrArg Ideal.absNorm E)
  calc
    _ = ∑ I ∈ S, ∏ q : ↥U, ((norm q.val)⁻¹)^(e I q) := mass.trans (sum_congr rfl vals)
    _ ≤ ∏ q : ↥U, (1-(norm q.val)⁻¹)⁻¹ := finite_euler_majorant S e inj _
      (fun q => inv_nonneg.mpr (zero_le_one.trans (wgt q).le))
      (fun q => inv_lt_one_of_one_lt₀ (wgt q))
    _ = ∏ p ∈ A, ∏ I ∈ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)), (1-(norm I)⁻¹)⁻¹ := by rw [prod_coe_sort U (fun q => (1-(norm q)⁻¹)⁻¹),prod_biUnion disj]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      apply prod_congr rfl
      intro I hI
      simp only [norm, ← (fiber_info K (mem_filter.mp hp).2 hI).2.2.2, Nat.cast_pow,inv_pow]


open Finset Real

-- Compare a complete local prime-ideal factor with its degree-one term.
lemma local_euler_compare {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, 0 < f i) (x : ℝ) (hx : 0 ≤ x) (hh : x ≤ 1/2) :
    (∏ i ∈ S, (1-x^(f i))⁻¹) ≤
      (1+((S.filter (fun i => f i = 1)).card:ℝ)*x)*exp ((2*(S.card:ℝ)+(S.card:ℝ)^2)*x^2) := by
  classical
  let d := (S.card:ℝ)
  let r := ((S.filter (fun i => f i = 1)).card:ℝ)
  let v (i : ι) := if f i = 1 then x else 0
  have hx1 : x ≤ 1 := by linarith
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hrd : r ≤ d := by dsimp [r,d]; exact_mod_cast (card_filter_le S (fun i => f i = 1))
  have localbound (i : ι) (hi : i ∈ S) : (1-x^(f i))⁻¹ ≤ exp (v i + 2*x^2) := by
    have hp : x^(f i) ≤ x := by
      simpa using pow_le_pow_of_le_one hx hx1 (hf i hi)
    have pos : 0 < 1-x^(f i) := by linarith
    apply le_trans _ (add_one_le_exp (v i + 2*x^2))
    rw [inv_le_iff_one_le_mul₀ pos]
    by_cases h : f i = 1
    · simp only [v,h,if_true,pow_one]
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x by linarith)]
    · have h2 : 2 ≤ f i := by have := hf i hi; omega
      have hs := pow_le_pow_of_le_one hx hx1 h2
      simp only [v,h,if_false,zero_add]
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x^(f i) by linarith)]
  have sumv : (∑ i ∈ S, v i) = r*x := by
    simp only [v,r,← sum_filter,sum_const,nsmul_eq_mul]
  have ry : 0 ≤ r*x := mul_nonneg hr hx
  have corr : r*x-(r*x)^2 ≤ log (1+r*x) := by
    apply le_trans _ (one_sub_inv_le_log_of_pos (by linarith))
    have hpos : 0<1+r*x := by linarith
    have id : (1-(1+r*x)⁻¹)*(1+r*x) = r*x := by field_simp; ring
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    rw [id]
    nlinarith [pow_nonneg ry 3]
  have rd2 : (r*x)^2 ≤ d^2*x^2 := by
    rw [mul_pow]
    gcongr
  calc
    _ ≤ ∏ i ∈ S, exp (v i + 2*x^2) := prod_le_prod (fun i hi => by
      have : x^(f i) ≤ x := by simpa using pow_le_pow_of_le_one hx hx1 (hf i hi)
      exact inv_nonneg.mpr (by linarith)) localbound
    _ = exp (r*x+d*(2*x^2)) := by rw [← exp_sum, sum_add_distrib,sumv,sum_const,nsmul_eq_mul]
    _ ≤ exp (log (1+r*x)+(2*d+d^2)*x^2) := exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [exp_add, exp_log (by linarith : 0<1+r*x)]


open Ideal NumberField Finset Real
lemma euler_product_correction {ι : Type*} (A : Finset ℕ) (pr : ∀ p ∈ A, p.Prime)
    (S : ℕ → Finset ι) (f : ι → ℕ) (pos : ∀ p ∈ A, ∀ i ∈ S p, 0 < f i)
    (D : ℕ) (bound : ∀ p ∈ A, (S p).card ≤ D) :
    (∏ p ∈ A, ∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹) ≤
      exp ((2*(D:ℝ)+(D:ℝ)^2) * ∑' k : ℕ, ((k:ℝ)^2)⁻¹) *
        ∏ p ∈ A, (1 + (((S p).filter (fun i => f i = 1)).card:ℝ)/p) := by
  classical
  let C := 2*(D:ℝ)+(D:ℝ)^2
  let W (p : ℕ) := 1 + (((S p).filter (fun i => f i = 1)).card:ℝ)/p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have point (p : ℕ) (hp : p ∈ A) : (∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹) ≤
      W p * exp (C*((p:ℝ)^2)⁻¹) := by
    have hpn : (0:ℝ)<p := by exact_mod_cast (pr p hp).pos
    have half : (p:ℝ)⁻¹ ≤ 1/2 := by
      rw [← one_div, div_le_div_iff₀ hpn (by norm_num : (0:ℝ)<2)]
      have : (2:ℝ)≤p := by exact_mod_cast (pr p hp).two_le
      linarith
    have first := local_euler_compare (S p) f (pos p hp) (p:ℝ)⁻¹ (by positivity) half
    rw [← div_eq_mul_inv, inv_pow] at first
    apply first.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : ((S p).card:ℝ) ≤ D := by exact_mod_cast bound p hp
    dsimp [C]
    gcongr
  have nonneg (p : ℕ) (hp : p ∈ A) : 0 ≤ ∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹ := by
    apply prod_nonneg
    intro i hi
    have h1 : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (pr p hp).one_le)
    exact inv_nonneg.mpr (sub_nonneg.mpr (pow_le_one₀ (by positivity) h1))
  have sumsq : (∑ p ∈ A, ((p:ℝ)^2)⁻¹) ≤ ∑' k : ℕ, ((k:ℝ)^2)⁻¹ :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).sum_le_tsum _ (fun _ _ => by positivity)
  calc
    _ ≤ ∏ p ∈ A, W p*exp (C*((p:ℝ)^2)⁻¹) := prod_le_prod nonneg point
    _ = (∏ p ∈ A, W p)*exp (C*∑ p ∈ A, ((p:ℝ)^2)⁻¹) := by
      rw [prod_mul_distrib, ← exp_sum, mul_sum]
    _ ≤ _ := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right (exp_le_exp.mpr (mul_le_mul_of_nonneg_left sumsq hC))
      exact prod_nonneg (fun p _ => by dsimp [W]; positivity)


open Finset Real
lemma omit_bad_primes (N b t D : ℕ) (hb : 0 < b) (ht : 0 < t)
    (a r : ℕ → ℕ) (bound : ∀ p : ℕ, p.Prime → a p ≤ D)
    (good : ∀ p : ℕ, p.Prime → ¬p ∣ t → a p = r p) :
    (∏ p ∈ (Icc 2 N).filter Nat.Prime, (1+(a p:ℝ)/p)) ≤
      (1+(D:ℝ))^((b*t).primeFactors.card) *
        ∏ p ∈ (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b), (1+(r p:ℝ)/p) := by
  classical
  let A := (Icc 2 N).filter Nat.Prime
  let B := A.filter (fun p => p ∣ b*t)
  let G := A \ B
  let T := (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b)
  have sub : B ⊆ A := filter_subset ..
  have subB : B ⊆ (b*t).primeFactors := by
    intro p hp
    obtain ⟨hA,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hA).2,hd,(Nat.mul_pos hb ht).ne'⟩
  have hpG {p : ℕ} (hp : p ∈ G) : p ∈ T ∧ a p = r p := by
    obtain ⟨hA,hB⟩ := mem_sdiff.mp hp
    obtain ⟨hN,prime⟩ := mem_filter.mp hA
    have hd : ¬ p ∣ b*t := fun h => hB (mem_filter.mpr ⟨hA,h⟩)
    have h1 : ¬p ∣ b := fun h => hd (dvd_mul_of_dvd_left h t)
    have h2 : ¬p ∣ t := fun h => hd (dvd_mul_of_dvd_right h b)
    exact ⟨mem_filter.mpr ⟨hN,prime,prime.coprime_iff_not_dvd.mpr h1⟩,good p prime h2⟩
  have bad : (∏ p ∈ B, (1+(a p:ℝ)/p)) ≤ (1+(D:ℝ))^((b*t).primeFactors.card) := by
    calc
      _ ≤ ∏ _p ∈ B, (1+(D:ℝ)) := by
        apply prod_le_prod (fun p _ => by positivity)
        intro p hp
        have prime := (mem_filter.mp (sub hp)).2
        have hp1 : (1:ℝ) ≤ p := by exact_mod_cast prime.one_le
        have leD : (a p:ℝ) ≤ D := by exact_mod_cast bound p prime
        linarith [div_le_self (Nat.cast_nonneg (a p)) hp1]
      _ ≤ _ := by
        rw [prod_const]
        exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) D]) (card_le_card subB)
  have clean : (∏ p ∈ G, (1+(a p:ℝ)/p)) ≤ ∏ p ∈ T, (1+(r p:ℝ)/p) := calc
    _ = ∏ p ∈ G, (1+(r p:ℝ)/p) := prod_congr rfl (fun p hp => by rw [(hpG hp).2])
    _ ≤ _ := prod_le_prod_of_subset_of_one_le (fun _ h => (hpG h).1)
      (fun p _ => by positivity) (fun p _ _ => le_add_of_nonneg_right (by positivity))
  have mult := prod_sdiff sub (f:=fun p => 1+(a p:ℝ)/p)
  change (∏ p ∈ G, (1+(a p:ℝ)/p))*(∏ p ∈ B, (1+(a p:ℝ)/p)) = _ at mult
  rw [← mult,mul_comm]
  exact mul_le_mul bad clean (prod_nonneg (fun p _ => by positivity)) (by positivity)


lemma prime_roots_mertens : ∀ g : ℤ[X], g.Monic → Irreducible g → g.natDegree ≠ 0 →
  ∀ b : ℕ, 0 < b → ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    c * Real.log ((N:ℝ)+1) ≤ (∏ p ∈ (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b),
        (1 + ((Nat.count (fun r : ℕ => (p:ℤ) ∣ g.eval (r:ℤ)) p : ℕ) : ℝ) / p)) := by
  classical
  intro g hm irr _degree b hb
  obtain ⟨K,field,nf,θ,hg,ht⟩ := choose_field g hm irr
  let D := Module.finrank ℤ (𝓞 K)
  let E := exp ((2*(D:ℝ)+(D:ℝ)^2) * ∑' k : ℕ, ((k:ℝ)^2)⁻¹)
  let B := (1+(D:ℝ))^((b*RingOfIntegers.exponent θ).primeFactors.card)
  let a (p : ℕ) := (((IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))).filter (fun I => I.inertiaDeg ℤ = 1)).card
  let r (p : ℕ) := Nat.count (fun k : ℕ => (p:ℤ) ∣ g.eval (k:ℤ)) p
  have hd : ∀ p : ℕ, p.Prime → a p ≤ D := fun p hp => (card_filter_le ..).trans (fiber_card_le K hp)
  have eq (p : ℕ) (hp : p.Prime) (nd : ¬p ∣ RingOfIntegers.exponent θ) : a p = r p := by
    simpa only [a,r,← hg] using fiber_count K θ hp nd
  obtain ⟨c,hc,lb⟩ := ideal_harmonic_lower K
  have posE : 0 < E := exp_pos _
  have posB : 0 < B := by dsimp [B]; positivity
  refine ⟨c/(E*B),by positivity,?_⟩
  intro N _hN
  let A := (Icc 2 N).filter Nat.Prime
  let T := (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b)
  let Z := ∏ p ∈ T, (1+(r p:ℝ)/p)
  have bound := euler_product_correction A (fun p hp => (mem_filter.mp hp).2) (fun p : ℕ => IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K))
    (fun I => I.inertiaDeg ℤ) (fun p hp I hI => (fiber_info K (mem_filter.mp hp).2 hI).2.2.1)
    D (fun p hp => fiber_card_le K (mem_filter.mp hp).2)
  have final : c*log ((N:ℝ)+1) ≤ E*B*Z := calc
    _ ≤ _ := lb N
    _ ≤ _ := ideal_euler_upper K N
    _ ≤ E * (∏ p ∈ A, (1+(a p:ℝ)/p)) := bound
    _ ≤ E*(B*Z) := mul_le_mul_of_nonneg_left (omit_bad_primes N b _ D hb ht a r hd eq) posE.le
    _ = _ := by ring
  change (c/(E*B))*log ((N:ℝ)+1) ≤ Z
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos posE posB)]
  linarith only [final,mul_comm (E*B) Z]

end PrimeIdeals

end OMA.Erdos975Lower

/- The lower Euler product controls the upper complementary sieve product. -/
namespace OMA.SieveProduct976
open Finset

theorem complementary_prod {ι α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (S : Finset ι) (u : ι → α) (P : ι → Prop)
    [DecidablePred P] (hu : ∀ p ∈ S, 0 ≤ u p ∧ u p ≤ 1) :
    (∏ p ∈ S, (1-u p)) * (∏ p ∈ S.filter P, (1+u p)) ≤ 1 := by
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ p ∈ S, (1 : α) := by
      apply Finset.prod_le_prod
      · intro p hp
        have H := hu p hp
        apply mul_nonneg (sub_nonneg.mpr H.2)
        split
        · exact add_nonneg zero_le_one H.1
        · exact zero_le_one
      · intro p hp
        have H := hu p hp
        split
        · rw [← (Commute.one_left (u p)).mul_self_sub_mul_self_eq', one_mul]
          exact sub_le_self _ (mul_nonneg H.1 H.1)
        · rw [mul_one]
          exact sub_le_self _ H.1
    _ = 1 := by simp

end OMA.SieveProduct976

/- Convert the root-prime lower bound of @steveDOTdigital (OMA #3752) into the upper bound for the sieve density. -/
open Polynomial Finset Real
namespace OMA.SieveProduct976

theorem root_sieve (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∏ p ∈ (Icc 2 N).filter Nat.Prime,
        (1 - (Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p : ℝ) / p)) ≤
        C / log ((N : ℝ) + 1) := by
  classical
  let b := f.leadingCoeff.natAbs
  have bpos : 0 < b := Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero)
  obtain ⟨c,hc,lower⟩ := OMA.Erdos975Lower.PrimeIdeals.prime_roots_mertens
    f.integralNormalization (monic_integralNormalization hf.ne_zero)
    (OMA.Erdos975Lower.irreducible_monic_replacement f hf hd)
    (by simpa only [natDegree_integralNormalization] using hd) b bpos
  refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
  intro N hN
  let S := (Icc 2 N).filter Nat.Prime
  let u (p : ℕ) := (Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p : ℝ) / p
  have hu (p) (hp : p ∈ S) : 0 ≤ u p ∧ u p ≤ 1 := by
    have pos : 0 < (p:ℝ) := Nat.cast_pos.mpr (mem_filter.mp hp).2.pos
    exact ⟨div_nonneg (Nat.cast_nonneg _) pos.le,
      (div_le_one pos).mpr (by exact_mod_cast Nat.count_le (p := fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)))⟩
  have low : c*log ((N : ℝ)+1) ≤ ∏ p ∈ S.filter (fun p => p.Coprime b), (1+u p) := by
    dsimp only [S]
    rw [Finset.filter_filter]
    refine (lower N hN).trans_eq (Finset.prod_congr rfl fun p hp => ?_)
    have cond := (mem_filter.mp hp).2
    rw [OMA.Erdos975Lower.monic_residue_counts f hd p cond.1.pos cond.2]
  have posprod : 0 ≤ ∏ p ∈ S, (1-u p) := prod_nonneg fun p hp => sub_nonneg.mpr (hu p hp).2
  have bound := (mul_le_mul_of_nonneg_left low posprod).trans
    (complementary_prod S u (fun p => p.Coprime b) hu)
  have logpos : 0 < log ((N : ℝ)+1) := log_pos (by exact_mod_cast (by omega : 1 < N+1))
  change (∏ p ∈ S, (1-u p)) ≤ c⁻¹ / _
  apply (le_div_iff₀ logpos).mpr
  rw [← one_div, le_div_iff₀ hc]
  convert bound using 1
  ring
end OMA.SieveProduct976

open Filter in
theorem OMA.SieveProduct976.root_sieve_half (Q : ℤ[X]) (irr : Irreducible Q) (hd : 2 ≤ Q.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      (∏ p ∈ (Icc 1 (n/2)).filter Nat.Prime,
        (1 - (Nat.count (fun r : ℕ => (p : ℤ) ∣ Q.eval (r : ℤ)) p : ℝ) / p)) ≤ A/log n := by
  obtain ⟨C,hC,H⟩ := OMA.SieveProduct976.root_sieve Q irr (by omega)
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 4] with n hn
  have eq : (Icc 1 (n/2)).filter Nat.Prime = (Icc 2 (n/2)).filter Nat.Prime := by
    ext p
    simp only [mem_filter,mem_Icc]
    constructor <;> rintro ⟨⟨h,hn⟩,hp⟩
    · exact ⟨⟨hp.two_le,hn⟩,hp⟩
    · exact ⟨⟨by omega,hn⟩,hp⟩
  rw [eq]
  refine (H (n/2) (by omega)).trans ?_
  have npos : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1<n)
  have hlarge : (n:ℝ) ≤ ((n/2:ℕ)+1 : ℝ)^2 := by
    have y : n ≤ (n/2+1)^2 := by nlinarith [show n ≤ 2*(n/2)+1 by omega, sq_nonneg (n/2)]
    exact_mod_cast y
  have hlog := log_le_log (by linarith : 0 < (n:ℝ)) hlarge
  rw [log_pow] at hlog
  have lpos : 0 < log ((n/2:ℕ)+1 : ℝ) := log_pos (by exact_mod_cast (by omega : 1<n/2+1))
  rw [div_le_div_iff₀ lpos (log_pos npos)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hC.le]
end

open Polynomial Finset

namespace Erdos976Sieve

/-- Passing to the polynomial left after extracting the content on a residue class
costs at most the modulus of that class in each root count. -/
theorem affine_root_count (R Q : ℤ[X]) {M a : ℕ} (ha : a < M)
    (divides : ∀ u : ℕ, R.eval (u : ℤ) ∣ Q.eval ((a + M*u : ℕ) : ℤ)) (d : ℕ) :
    Nat.count (fun u : ℕ => (d : ℤ) ∣ R.eval (u : ℤ)) d ≤
      M * Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  have hdpos := Nat.pos_of_ne_zero hd
  simp only [Nat.count_eq_card_filter_range]
  rw [← card_range M, ← card_product]
  let key (u : ℕ) := ((a + M*u)/d, (a + M*u)%d)
  apply card_le_card_of_injOn key
  · intro u hu
    obtain ⟨hu, hr⟩ := mem_filter.mp hu
    have hul := mem_range.mp hu
    have hLt : a + M*u < M*d := calc
      a + M*u < M + M*u := by omega
      _ = M*(u+1) := by ring
      _ ≤ M*d := Nat.mul_le_mul_left _ hul
    let v := a + M*u
    have hmod : v % d ≡ v [MOD d] := Nat.mod_modEq _ _
    have hdiff := (Int.natCast_modEq_iff.mpr hmod).dvd
    have hEval := Int.modEq_of_dvd (hdiff.trans (sub_dvd_eval_sub (v:ℤ) (↑(v%d):ℤ) Q))
    exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hdpos).mpr hLt),
      mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hdpos), hEval.dvd_iff.mpr (hr.trans (divides u))⟩⟩
  · intro u _ v _ huv
    have quot : (a+M*u)/d = (a+M*v)/d := congrArg Prod.fst huv
    have rem : (a+M*u)%d = (a+M*v)%d := congrArg Prod.snd huv
    have eqv : a+M*u = a+M*v := by
      calc
        _ = (a+M*u)%d+d*((a+M*u)/d) := (Nat.mod_add_div _ _).symm
        _ = (a+M*v)%d+d*((a+M*v)/d) := by rw [quot, rem]
        _ = _ := Nat.mod_add_div _ _
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) (Nat.add_left_cancel eqv)

theorem affine_root_sum (R Q : ℤ[X]) {M a : ℕ} (ha : a < M)
    (divides : ∀ u : ℕ, R.eval (u : ℤ) ∣ Q.eval ((a + M*u : ℕ) : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    (∑ d ∈ Icc 1 N, (Nat.count (fun u : ℕ => (d : ℤ) ∣ R.eval (u : ℤ)) d : ℝ)*w d/d) ≤
      M * (∑ d ∈ Icc 1 N, (Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d : ℝ)*w d/d) := by
  rw [mul_sum]
  apply sum_le_sum
  intro d _
  have h := affine_root_count R Q ha divides d
  push_cast at *
  calc
    _ ≤ (((M:ℝ) * Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d) * w d / d) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (hw d)) (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos976Sieve

open Polynomial Finset Real Filter
namespace Erdos976Sieve

/-- Count each positive integer once in its affine residue class. The constant
term covers the initial quotient zero in each class. -/
theorem affine_prefix (f : ℤ[X]) {M : ℕ} (hM : 0 < M) (R : Fin M → ℤ[X]) (c : Fin M → ℤ)
    (affine : ∀ a : Fin M, ∀ u : ℕ, f.eval ((a.val + M*u : ℕ) : ℤ) = c a * (R a).eval (u : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {t : ℝ}
    (growth : ∀ a b : ℕ, w (a*b) ≤ w a * (b.divisors.card : ℝ)^t) (n : ℕ) :
    (∑ m ∈ Icc 1 n, w (f.eval (m:ℤ)).natAbs) ≤
      ∑ a : Fin M, (((c a).natAbs.divisors.card:ℝ)^t *
        (w ((R a).eval 0).natAbs + ∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs)) := by
  classical
  let index (m : ℕ) : Fin M × ℕ := (⟨m%M, Nat.mod_lt _ hM⟩, m/M)
  have hinj : Function.Injective index := by
    intro m k eqv
    have h₁ : m%M = k%M := congrArg (fun z : Fin M × ℕ => z.1.val) eqv
    have h₂ : m/M=k/M := congrArg Prod.snd eqv
    simpa only [h₁, h₂, Nat.mod_add_div] using (Nat.mod_add_div m M).symm
  let weight (p : Fin M × ℕ) := ((c p.1).natAbs.divisors.card:ℝ)^t *
    w ((R p.1).eval (p.2:ℤ)).natAbs
  let T := (univ : Finset (Fin M)) ×ˢ insert 0 (Icc 1 n)
  have hsub : (Icc 1 n).image index ⊆ T := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have hle : m/M ≤ n := (Nat.div_le_self ..).trans (mem_Icc.mp hm).2
    exact mem_product.mpr ⟨mem_univ _,mem_insert.mpr (by
      change m/M = 0 ∨ m/M ∈ Icc 1 n
      by_cases h : m/M = 0
      · exact Or.inl h
      · exact Or.inr (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, hle⟩))⟩
  calc
    _ ≤ ∑ m ∈ Icc 1 n, weight (index m) := by
      apply sum_le_sum
      intro m _
      have h := affine (index m).1 (m/M)
      simp only [index, Nat.mod_add_div] at h
      rw [h, Int.natAbs_mul, Nat.mul_comm]
      simpa only [weight, mul_comm] using (growth ((R (index m).1).eval (↑(m/M):ℤ)).natAbs (c (index m).1).natAbs)
    _ = ∑ p ∈ (Icc 1 n).image index, weight p := (sum_image (fun _ _ _ _ e => hinj e)).symm
    _ ≤ ∑ p ∈ T, weight p := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hw _))
    _ = _ := by
      rw [show T = _ from rfl, sum_product]
      apply sum_congr rfl
      intro a _
      rw [sum_insert (by simp), mul_add, mul_sum]
      rfl

end Erdos976Sieve

open Polynomial Finset Real Filter
namespace Erdos976Sieve

/-- Long-prefix estimates for primitive parts on finitely many progressions
give the original estimate, even when the weight vanishes on some integers. -/
theorem affine_long (f : ℤ[X]) {M : ℕ} (hM : 0 < M) (R : Fin M → ℤ[X]) (c : Fin M → ℤ)
    (affine : ∀ a : Fin M, ∀ u : ℕ, f.eval ((a.val + M*u : ℕ) : ℤ) = c a * (R a).eval (u : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {t : ℝ}
    (growth : ∀ a b : ℕ, w (a*b) ≤ w a * (b.divisors.card : ℝ)^t) :
    let H (Q : ℤ[X]) (n : ℕ) := ∑ d ∈ Icc 1 n,
      (Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d : ℝ)*w d/d
    (∀ a : Fin M, ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs) ≤ B*((n:ℝ)/log n)*H (R a) n) →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Icc 1 n, w (f.eval (u:ℤ)).natAbs) ≤ B*((n:ℝ)/log n)*H f n := by
  intro H rows
  classical
  choose B Bpos bounds using rows
  let s (a : Fin M) := ((c a).natAbs.divisors.card:ℝ)^t
  let z (a : Fin M) := (((R a).eval 0).natAbs.divisors.card:ℝ)^t
  let K := ∑ a : Fin M, s a * (z a + B a * M)
  have hs a : 0 ≤ s a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz a : 0 ≤ z a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK : 0 ≤ K := sum_nonneg (fun a _ => mul_nonneg (hs a) (add_nonneg (hz a)
    (mul_nonneg (Bpos a).le (Nat.cast_nonneg M))))
  refine ⟨K+1, by linarith, ?_⟩
  filter_upwards [eventually_all.mpr bounds, eventually_ge_atTop 2] with n hrow hn
  have logpos : 0 < log n := Real.log_pos (by exact_mod_cast (show 1< n by omega))
  let x : ℝ := n / log n
  have hx : 1 ≤ x := (one_le_div logpos).mpr (Real.log_le_self (Nat.cast_nonneg _))
  have Hnonneg : 0 ≤ H f n := by dsimp only [H]; exact sum_nonneg (fun i _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  have Hbase : w 1 ≤ H f n := by
    have h1 : (1:ℕ) ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl,by omega⟩
    have h := single_le_sum (f := fun d : ℕ =>
      (Nat.count (fun u : ℕ => (d:ℤ) ∣ f.eval (u:ℤ)) d : ℝ)*w d/d)
      (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _)) h1
    simpa [Nat.count_succ, H] using h
  have hscale : H f n ≤ x*H f n := le_mul_of_one_le_left Hnonneg hx
  have zeroTerm (a : Fin M) : w ((R a).eval 0).natAbs ≤ z a*(x*H f n) := by
    have hzero : w ((R a).eval 0).natAbs ≤ w 1*z a := by
      simpa [z] using (growth 1 ((R a).eval 0).natAbs)
    refine hzero.trans ?_
    rw [mul_comm (w 1)]
    exact mul_le_mul_of_nonneg_left (Hbase.trans hscale) (hz a)
  have term (a : Fin M) : w ((R a).eval 0).natAbs + (∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs)
        ≤ (z a+B a*M)*(x*H f n) := by
    have root : H (R a) n ≤ (M:ℝ)*H f n := affine_root_sum _ _ a.isLt (fun u =>
      (affine a u).symm ▸ dvd_mul_left _ _) w hw n
    have rest := (hrow a).trans (mul_le_mul_of_nonneg_left root (mul_nonneg (Bpos a).le (le_trans zero_le_one hx)))
    calc
      _ ≤ z a*(x*H f n)+ B a*x*((M:ℝ)*H f n) := add_le_add (zeroTerm a) rest
      _ = _ := by ring
  calc
    _ ≤ _ := affine_prefix f hM R c affine w hw growth n
    _ ≤ ∑ a : Fin M, s a * ((z a+B a*M)*(x*H f n)) :=
      sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (term a) (hs a))
    _ = K*(x*H f n) := by simp only [K, sum_mul, mul_assoc]
    _ ≤ (K+1)*(x*H f n) := mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (le_trans zero_le_one hx) Hnonneg)
    _ = _ := by ring

end Erdos976Sieve

namespace TenenbaumDirect
open Finset Real Filter

/-- A half-interval estimate with the factor n / log n sums with uniform
constant on a prefix, for any nondecreasing positive cumulative weight. -/
theorem log_prefix (F H : ℕ → ℝ) (mono : Monotone H) (pos : 0 < H 1)
    (band : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      F n - F (n/2) ≤ c * ((n:ℝ)/log n) * H n) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      F n ≤ B * ((n:ℝ)/log n) * H n := by
  obtain ⟨c,cp,localbound⟩ := band
  obtain ⟨N,hN⟩ := eventually_atTop.mp localbound
  let T := N+24
  let D := ∑ i ∈ range (T+1),max (F i) 0
  have D0 : 0 ≤ D := sum_nonneg (fun i _ => le_max_right _ _)
  have start (n : ℕ) (small : n ≤ T) : F n ≤ D :=
    (le_max_left _ _).trans (single_le_sum (f:=fun i => max (F i) 0)
      (fun i _ => le_max_right _ _) (mem_range.mpr (by omega : n< T+1)))
  have bound (n : ℕ) (two : 2≤ n) : F n ≤ D+4*c*((n:ℝ)/log n)*H n := by
    induction n using Nat.strong_induction_on with | h n ih =>
    have hn : 0 < H n := pos.trans_le (mono (by omega))
    have logpos : 0< log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1< n))
    by_cases small : n≤ T
    · exact (start n small).trans (le_add_of_nonneg_right (by positivity))
    let m := n/2
    have large : N+24< n := Nat.lt_of_not_ge small
    have data : 9≤ m ∧ m< n ∧ 2*m≤ n ∧ n≤3*m := by dsimp [m];omega
    obtain ⟨m9,mn,mhalf,nt⟩ := data
    have mh : 0< H m := pos.trans_le (mono (by omega))
    have ml : 0< log (m:ℝ) := log_pos (by exact_mod_cast (by omega : 1< m))
    have three_le : log (9:ℝ) ≤ log (m:ℝ) := log_le_log (by norm_num) (by exact_mod_cast m9)
    have twice : log (9:ℝ) = 2*log (3:ℝ) := by rw [show (9:ℝ)=3*3 by norm_num,log_mul (by norm_num) (by norm_num)]; ring
    have high := log_le_log (show 0<(n:ℝ) by positivity) (show (n:ℝ)≤3*(m:ℝ) by exact_mod_cast nt)
    rw [log_mul (by norm_num) (ne_of_gt (show 0<(m:ℝ) by positivity))] at high
    have qlog : 2*log (n:ℝ) ≤ 3*log (m:ℝ) := by linarith
    have half : 2*(m:ℝ) ≤ n := by exact_mod_cast mhalf
    have ratio : 4*((m:ℝ)/log m) ≤ 3*((n:ℝ)/log n) := by
      field_simp [ml.ne',logpos.ne']
      nlinarith [mul_le_mul_of_nonneg_left qlog (show 0≤2*(m:ℝ) by positivity),
        mul_le_mul_of_nonneg_right half ml.le]
    have lt := mul_le_mul_of_nonneg_right ratio mh.le
    have hi := mul_le_mul_of_nonneg_left (mono mn.le) (show 0≤3*((n:ℝ)/log n) by positivity)
    have fine := mul_le_mul_of_nonneg_left (lt.trans hi) cp.le
    have prev := ih m mn (by omega)
    have lastBand := hN n (by omega)
    change F n - F m ≤ _ at lastBand
    linarith
  refine ⟨D/H 1+4*c,by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n n2
  have logpos : 0< log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1< n))
  have nb : 1 ≤ (n:ℝ)/log n := (one_le_div logpos).mpr (by linarith [log_le_sub_one_of_pos (show 0<(n:ℝ) by positivity)])
  have HH := mono (show 1≤ n by omega)
  have bb := mul_le_mul_of_nonneg_left ((show H 1≤((n:ℝ)/log n)*H n from
    HH.trans (le_mul_of_one_le_left (pos.le.trans HH) nb))) (show 0≤ D/H 1 by positivity)
  have e : D/H 1 * H 1 = D := div_mul_cancel₀ _ pos.ne'
  linarith [bound n n2]

end TenenbaumDirect

namespace OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1_H3_R1
open Finset Real Filter Polynomial

/-- The single-polynomial short-sum sieve on a half interval, for polynomials
with no fixed prime divisor (Nair–Tenenbaum, Corollary 3, with k=1). -/
def H1 : Prop :=
  let roots (Q : ℤ[X]) (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  ∀ Q : ℤ[X], Irreducible Q → 2 ≤ Q.natDegree → (∀ p : ℕ, p.Prime → roots Q p < p) →
    ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) →
    (∀ a b : ℕ, w (a*b) ≤ w a*(b.divisors.card:ℝ)^(3/2:ℝ)) →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Ioc (n/2) n, w (Q.eval (u:ℤ)).natAbs) ≤
        C*n*(∏ p ∈ (Icc 1 (n/2)).filter Nat.Prime, (1-(roots Q p:ℝ)/p))*
          (∑ d ∈ Icc 1 n, (roots Q d:ℝ)*w d/d)

/-- Finitely many affine residue classes remove every fixed prime divisor while
preserving the degree and irreducibility of each primitive part. -/
def H2 : Prop :=
  let roots (Q : ℤ[X]) (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  ∀ f : ℤ[X], Irreducible f → 2 ≤ f.natDegree →
    ∃ M : ℕ, 0 < M ∧ ∃ R : Fin M → ℤ[X], ∃ c : Fin M → ℤ, ∀ a : Fin M,
      Irreducible (R a) ∧ 2 ≤ (R a).natDegree ∧ (∀ p : ℕ, p.Prime → roots (R a) p < p) ∧
      ∀ u : ℕ, f.eval ((a.val+M*u:ℕ):ℤ) = c a*(R a).eval (u:ℤ)

theorem main : H1 → H2 → OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1.H3 := by
  intro short normalize f hirr hdeg w hw growth
  classical
  obtain ⟨M,hM,R,c,good⟩ := normalize f hirr hdeg
  apply Erdos976Sieve.affine_long f hM R c (fun a => (good a).2.2.2) w hw growth
  intro a
  obtain ⟨hR,hdegR,hfix,_⟩ := good a
  let Q := R a
  let ρ (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  let H (n : ℕ) := ∑ d ∈ Icc 1 n, (ρ d:ℝ)*w d/d
  let F (n : ℕ) := ∑ u ∈ Icc 1 n, w (Q.eval (u:ℤ)).natAbs
  change ∃ B : ℝ, 0< B ∧ ∀ᶠ n : ℕ in atTop, F n ≤ B*((n:ℝ)/log n)*H n
  by_cases h0 : w 1 = 0
  · have hz (b : ℕ) : w b = 0 := le_antisymm (by simpa [h0] using growth 1 b) (hw b)
    exact ⟨1,zero_lt_one,Eventually.of_forall (by simp [F,H,hz])⟩
  apply TenenbaumDirect.log_prefix F H
  · intro n k hnk
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hnk) (fun d _ _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  · simpa [H,ρ,Nat.count_succ] using lt_of_le_of_ne (hw 1) (Ne.symm h0)
  obtain ⟨C,hC,hshort⟩ := short Q hR hdegR hfix w hw growth
  obtain ⟨A,hA,hprod⟩ := OMA.SieveProduct976.root_sieve_half Q hR hdegR
  refine ⟨C*A,mul_pos hC hA,?_⟩
  filter_upwards [hshort,hprod] with n hS hP
  have hpart : Icc 1 n = Icc 1 (n/2) ∪ Ioc (n/2) n := by
    ext i
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have hdis : Disjoint (Icc 1 (n/2)) (Ioc (n/2) n) := disjoint_left.mpr (by
    intro i hi hj
    exact (not_lt_of_ge (mem_Icc.mp hi).2) (mem_Ioc.mp hj).1)
  have hex : F n-F (n/2) = ∑ u ∈ Ioc (n/2) n, w (Q.eval (u:ℤ)).natAbs := by
    dsimp only [F]
    rw [hpart, sum_union hdis, add_sub_cancel_left]
  have hnn : 0 ≤ H n := sum_nonneg (fun d _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  rw [hex]
  apply hS.trans
  calc
    _ ≤ (C*n*(A/log n))*H n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (mul_nonneg hC.le (Nat.cast_nonneg _))) hnn
    _ = _ := by ring

end OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1_H3_R1
