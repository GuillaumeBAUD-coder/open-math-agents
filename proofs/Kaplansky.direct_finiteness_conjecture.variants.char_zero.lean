import FormalConjectures.Wikipedia.Kaplansky
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Cardinality

-- Problem: Kaplansky's Conjectures — char zero
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Kaplansky.lean:185 (declaration Kaplansky.direct_finiteness_conjecture.variants.char_zero)
-- Credit: @kintonc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

noncomputable section

namespace OMA.KaplanskyCharZero

private abbrev l2G (G : Type*) := lp (fun _ : G => ℂ) 2

private def shiftIso (G : Type*) (e : G ≃ G) : l2G G ≃ₗᵢ[ℂ] l2G G where
  toFun f :=
    ⟨fun h => f (e h), by
      change Memℓp (fun h => f (e h)) 2
      rw [memℓp_gen_iff (by norm_num)]
      exact (e.summable_iff (f := fun h => ‖f h‖ ^ (2 : ENNReal).toReal)).mpr
        ((memℓp_gen_iff (by norm_num)).mp (lp.memℓp f))⟩
  invFun f :=
    ⟨fun h => f (e.symm h), by
      change Memℓp (fun h => f (e.symm h)) 2
      rw [memℓp_gen_iff (by norm_num)]
      exact (e.symm.summable_iff (f := fun h => ‖f h‖ ^ (2 : ENNReal).toReal)).mpr
        ((memℓp_gen_iff (by norm_num)).mp (lp.memℓp f))⟩
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp
  map_add' f g := by ext h; rfl
  map_smul' c f := by ext h; rfl
  norm_map' f := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    congr 1
    exact e.tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal)

private def L_shift {G : Type*} [Group G] (g : G) : l2G G →L[ℂ] l2G G :=
  (shiftIso G (Equiv.mulLeft g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

private def R_shift {G : Type*} [Group G] (g : G) : l2G G →L[ℂ] l2G G :=
  (shiftIso G (Equiv.mulRight g)).toContinuousLinearEquiv.toContinuousLinearMap

private lemma L_shift_apply {G : Type*} [Group G] (g : G) (f : l2G G) (h : G) :
    L_shift g f h = f (g⁻¹ * h) := rfl

private lemma R_shift_apply {G : Type*} [Group G] (g : G) (f : l2G G) (h : G) :
    R_shift g f h = f (h * g) := rfl

private lemma L_shift_one {G : Type*} [Group G] : L_shift (1 : G) = 1 := by
  ext f h; simp [L_shift_apply]

private lemma L_shift_mul {G : Type*} [Group G] (g₁ g₂ : G) :
    L_shift (g₁ * g₂) = L_shift g₁ * L_shift g₂ := by
  ext f h; simp [L_shift_apply, mul_assoc]

private lemma L_shift_comm_R_shift {G : Type*} [Group G] (k g : G) :
    L_shift k * R_shift g = R_shift g * L_shift k := by
  ext f h; simp [L_shift_apply, R_shift_apply, mul_assoc]

private lemma inner_R_shift {G : Type*} [Group G] (g : G) (x y : l2G G) :
    inner ℂ (R_shift g x) y = inner ℂ x (R_shift g⁻¹ y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine ((Equiv.mulRight g⁻¹).tsum_eq (fun h => inner ℂ (R_shift g x h) (y h))).symm.trans ?_
  congr 1
  ext h
  simp [R_shift_apply, mul_assoc]

private lemma inner_R_shift_right {G : Type*} [Group G] (g : G) (x y : l2G G) :
    inner ℂ x (R_shift g y) = inner ℂ (R_shift g⁻¹ x) y := by
  rw [inner_R_shift, inv_inv]

private def delta {G : Type*} [DecidableEq G] (g : G) : l2G G :=
  lp.single 2 g (1 : ℂ)

private lemma R_shift_delta_one {G : Type*} [Group G] [DecidableEq G] (g : G) :
    R_shift g⁻¹ (delta (1 : G)) = delta g := by
  ext h
  simp only [R_shift_apply, delta, lp.single_apply, Pi.single_apply, mul_inv_eq_one]

private lemma inner_delta_left {G : Type*} [DecidableEq G] (g : G) (f : l2G G) :
    inner ℂ (delta g) f = f g := by
  rw [lp.inner_eq_tsum]
  refine (tsum_eq_single g (fun h hh => ?_)).trans ?_
  · simp [delta, lp.single_apply, hh]
  · simp [delta, lp.single_apply]

private lemma inner_delta_right {G : Type*} [DecidableEq G] (g : G) (f : l2G G) :
    inner ℂ f (delta g) = star (f g) := by
  rw [lp.inner_eq_tsum]
  refine (tsum_eq_single g (fun h hh => ?_)).trans ?_
  · simp [delta, lp.single_apply, hh]
  · simp [delta, lp.single_apply, RCLike.inner_apply]

private def CommutesRight {G : Type*} [Group G] (T : l2G G →L[ℂ] l2G G) : Prop :=
  ∀ g : G, T * R_shift g = R_shift g * T

private lemma CommutesRight.adjoint {G : Type*} [Group G] {T : l2G G →L[ℂ] l2G G}
    (hT : CommutesRight T) : CommutesRight T.adjoint := by
  intro g
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (T.adjoint (R_shift g y)) = inner ℂ x (R_shift g (T.adjoint y))
  rw [ContinuousLinearMap.adjoint_inner_right, inner_R_shift_right]
  have h1 : R_shift g⁻¹ (T x) = T (R_shift g⁻¹ x) := by
    simpa using DFunLike.congr_fun (hT g⁻¹).symm x
  rw [h1, ← ContinuousLinearMap.adjoint_inner_right, ← inner_R_shift_right]

private lemma apply_delta_one {G : Type*} [Group G] [DecidableEq G] {T : l2G G →L[ℂ] l2G G}
    (hT : CommutesRight T) (g : G) :
    (T (delta (1 : G))) g = star ((T.adjoint (delta (1 : G))) g⁻¹) := by
  rw [← inner_delta_left g (T (delta 1)), ← R_shift_delta_one g, inner_R_shift, inv_inv]
  have h1 : R_shift g (T (delta (1 : G))) = T (R_shift g (delta 1)) := by
    simpa using DFunLike.congr_fun (hT g).symm (delta 1)
  rw [h1]
  have h2 : R_shift g (delta (1 : G)) = delta g⁻¹ := by
    simpa using R_shift_delta_one g⁻¹
  rw [h2, ← ContinuousLinearMap.adjoint_inner_left, inner_delta_right]

private lemma trace_comm {G : Type*} [Group G] [DecidableEq G] {S T : l2G G →L[ℂ] l2G G}
    (hS : CommutesRight S) (hT : CommutesRight T) :
    inner ℂ (delta (1 : G)) ((S * T) (delta 1)) = inner ℂ (delta (1 : G)) ((T * S) (delta 1)) := by
  change inner ℂ (delta (1 : G)) (S (T (delta 1))) = inner ℂ (delta (1 : G)) (T (S (delta 1)))
  conv_lhs => rw [← ContinuousLinearMap.adjoint_inner_left]
  conv_rhs => rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hS' : ∀ g : G, (S.adjoint (delta (1 : G))) g = star ((S (delta 1)) g⁻¹) := by
    intro g
    have h := apply_delta_one hS.adjoint g
    simpa [ContinuousLinearMap.adjoint_adjoint] using h
  have hT' : ∀ g : G, (T (delta (1 : G))) g = star ((T.adjoint (delta 1)) g⁻¹) :=
    apply_delta_one hT
  have hL : (∑' g : G, inner ℂ ((S.adjoint (delta 1)) g) ((T (delta 1)) g)) =
      ∑' g : G, (S (delta 1)) g⁻¹ * star ((T.adjoint (delta 1)) g⁻¹) := by
    congr 1; ext g
    simp [RCLike.inner_apply, hS' g, hT' g, mul_comm]
  rw [hL]
  exact ((Equiv.inv G).tsum_eq (fun g => (S (delta 1)) g * star ((T.adjoint (delta 1)) g))).trans
    (by congr 1)

private def L_alg (G : Type*) [Group G] : MonoidAlgebra ℂ G →ₐ[ℂ] (l2G G →L[ℂ] l2G G) :=
  MonoidAlgebra.lift ℂ (l2G G →L[ℂ] l2G G) G
    { toFun := L_shift, map_one' := L_shift_one, map_mul' := L_shift_mul }

private lemma L_alg_of {G : Type*} [Group G] (g : G) :
    L_alg G (MonoidAlgebra.of ℂ G g) = L_shift g := by
  simp [L_alg]

private lemma L_alg_commutesRight {G : Type*} [Group G] (x : MonoidAlgebra ℂ G) :
    CommutesRight (L_alg G x) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    rw [L_alg_of]
    intro g
    exact L_shift_comm_R_shift m g
  | add x y hx hy =>
    intro g
    rw [map_add, add_mul, mul_add, hx g, hy g]
  | smul r x hx =>
    intro g
    rw [map_smul, smul_mul_assoc, mul_smul_comm, hx g]

private lemma L_alg_delta_one {G : Type*} [Group G] [DecidableEq G]
    (x : MonoidAlgebra ℂ G) (g : G) :
    (L_alg G x (delta (1 : G))) g = x.coeff g := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    rw [L_alg_of]
    have hL : L_shift m (delta (1 : G)) = delta m := by
      ext h
      simp [L_shift_apply, delta, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
    rw [hL, delta, lp.single_apply, Pi.single_apply]
    change (if g = m then (1 : ℂ) else 0) = (Finsupp.single m (1 : ℂ)) g
    simp [Finsupp.single_apply, eq_comm]
  | add x y hx hy =>
    simp [hx, hy]
  | smul r x hx =>
    simp [hx, smul_eq_mul]

private theorem direct_finiteness_complex (G : Type*) [Group G] :
    IsDedekindFiniteMonoid (MonoidAlgebra ℂ G) := by
  classical
  rw [isDedekindFiniteMonoid_iff]
  intro a b hab
  set A := L_alg G a
  set B := L_alg G b
  set E := (1 : l2G G →L[ℂ] l2G G) - B * A
  have hAB : A * B = 1 := by rw [← map_mul (L_alg G), hab, map_one]
  let Ksub : Submodule ℂ (l2G G) := LinearMap.ker A.toLinearMap
  have hKclosed : IsClosed (Ksub : Set (l2G G)) := isClosed_singleton.preimage A.continuous
  have : CompleteSpace Ksub := hKclosed.completeSpace_coe
  set P := Ksub.starProjection
  have hPmem : ∀ v, P v ∈ Ksub := fun v => by
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hPorth : ∀ v, v - P v ∈ Ksubᗮ := Submodule.sub_starProjection_mem_orthogonal
  have hPE_mem : ∀ v, E v ∈ Ksub := fun v => by
    change A (E v) = 0
    have h1 : A * E = 0 := by
      dsimp [E]
      rw [mul_sub, mul_one, ← mul_assoc, hAB, one_mul, sub_self]
    simpa using DFunLike.congr_fun h1 v
  have hPE : P * E = E := by
    ext1 v
    exact Submodule.starProjection_eq_self_iff.mpr (hPE_mem v)
  have hEP : E * P = P := by
    ext1 v
    have hAPv : A (P v) = 0 := hPmem v
    change P v - B (A (P v)) = P v
    rw [hAPv, map_zero, sub_zero]
  have hPcomm : CommutesRight P := by
    intro g
    ext1 v
    change P (R_shift g v) = R_shift g (P v)
    have h1 : R_shift g (P v) ∈ Ksub := by
      change A (R_shift g (P v)) = 0
      have hc : A * R_shift g = R_shift g * A := L_alg_commutesRight a g
      have hAp : A (R_shift g (P v)) = R_shift g (A (P v)) :=
        DFunLike.congr_fun hc (P v)
      rw [hAp, show A (P v) = 0 from hPmem v, map_zero]
    have h2 : R_shift g (v - P v) ∈ Ksubᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      rw [inner_R_shift_right]
      have hw' : R_shift g⁻¹ w ∈ Ksub := by
        change A (R_shift g⁻¹ w) = 0
        have hc : A * R_shift g⁻¹ = R_shift g⁻¹ * A := L_alg_commutesRight a g⁻¹
        have hAw : A (R_shift g⁻¹ w) = R_shift g⁻¹ (A w) :=
          DFunLike.congr_fun hc w
        rw [hAw, show A w = 0 from hw, map_zero]
      exact (Submodule.mem_orthogonal _ _).mp (hPorth v) (R_shift g⁻¹ w) hw'
    have hsplit : R_shift g v = R_shift g (P v) + R_shift g (v - P v) := by
      rw [← map_add, add_sub_cancel]
    rw [hsplit, map_add, Submodule.starProjection_eq_self_iff.mpr h1]
    have hzero : P (R_shift g (v - P v)) = 0 := by
      rw [Submodule.starProjection_apply]
      have h0 : Ksub.orthogonalProjectionOnto (R_shift g (v - P v)) = 0 :=
        (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr h2
      rw [h0, Submodule.coe_zero]
    rw [hzero, add_zero]
  have hEcomm : CommutesRight E := by
    intro g
    dsimp [E]
    rw [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, L_alg_commutesRight a g,
      ← mul_assoc, L_alg_commutesRight b g, mul_assoc]
  have htr1 : inner ℂ (delta (1 : G)) (P (delta 1)) = 0 := by
    have h1 : inner ℂ (delta (1 : G)) (P (delta 1)) =
        inner ℂ (delta (1 : G)) ((E * P) (delta 1)) := by rw [hEP]
    rw [h1, trace_comm hEcomm hPcomm, hPE]
    change inner ℂ (delta (1 : G)) (delta 1 - (B * A) (delta 1)) = 0
    rw [inner_sub_right, trace_comm (L_alg_commutesRight b) (L_alg_commutesRight a), hAB]
    simp
  have hPnorm : inner ℂ (P (delta (1 : G))) (P (delta 1)) = 0 := by
    have hR : ∀ x y : l2G G, inner ℂ x (P y) = inner ℂ (P x) (P y) := by
      intro x y
      have hx : x = P x + (x - P x) := (add_sub_cancel (P x) x).symm
      conv_lhs => rw [hx]
      rw [inner_add_left]
      have h0 : inner ℂ (x - P x) (P y) = 0 := by
        rw [← inner_conj_symm]
        simp [(Submodule.mem_orthogonal _ _).mp (hPorth x) (P y) (hPmem y)]
      rw [h0, add_zero]
    exact (hR (delta 1) (delta 1)).symm.trans htr1
  have hPdelta1 : P (delta (1 : G)) = 0 := inner_self_eq_zero.mp hPnorm
  have hPdelta : ∀ g : G, P (delta g) = 0 := by
    intro g
    rw [← R_shift_delta_one g]
    have hc : P (R_shift g⁻¹ (delta 1)) = R_shift g⁻¹ (P (delta 1)) :=
      DFunLike.congr_fun (hPcomm g⁻¹) (delta 1)
    rw [hc, hPdelta1, map_zero]
  have hPzero : P = 0 := by
    ext v g
    change (P v) g = 0
    rw [← inner_delta_left g (P v)]
    have hself : inner ℂ (delta g) (P v) = inner ℂ (P (delta g)) v := by
      have hv : v = P v + (v - P v) := (add_sub_cancel (P v) v).symm
      have hg : delta g = P (delta g) + (delta g - P (delta g)) :=
        (add_sub_cancel (P (delta g)) (delta g)).symm
      have h1 : inner ℂ (delta g) (P v) = inner ℂ (P (delta g)) (P v) := by
        conv_lhs => rw [hg]
        rw [inner_add_left]
        have h0 : inner ℂ (delta g - P (delta g)) (P v) = 0 := by
          rw [← inner_conj_symm]
          simp [(Submodule.mem_orthogonal _ _).mp (hPorth (delta g)) (P v) (hPmem v)]
        rw [h0, add_zero]
      have h2 : inner ℂ (P (delta g)) v = inner ℂ (P (delta g)) (P v) := by
        conv_lhs => rw [hv]
        rw [inner_add_right, (Submodule.mem_orthogonal _ _).mp (hPorth v) (P (delta g)) (hPmem (delta g)), add_zero]
      exact h1.trans h2.symm
    rw [hself, hPdelta g, inner_zero_left]
  have hEzero : E = 0 := by rw [← hPE, hPzero, zero_mul]
  have h1ba : 1 - b * a = 0 := by
    ext g
    have hL : (1 - b * a).coeff g = (L_alg G (1 - b * a) (delta (1 : G))) g :=
      (L_alg_delta_one (1 - b * a) g).symm
    have hL2 : L_alg G (1 - b * a) = E := by
      dsimp [E, A, B]
      rw [map_sub, map_one, map_mul]
    rw [hL, hL2, hEzero]
    simp
  exact (sub_eq_zero.mp h1ba).symm

private lemma countable_polynomial {F : Type*} [Semiring F] [Countable F] :
    Countable (Polynomial F) := by
  refine Function.Injective.countable
    (f := fun p : Polynomial F => List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) ?_
  intro p q h
  have hlen : p.natDegree + 1 = q.natDegree + 1 := by
    simpa [List.length_ofFn] using congr_arg List.length h
  have hdeg : p.natDegree = q.natDegree := Nat.succ.inj hlen
  ext n
  by_cases hn : n < p.natDegree + 1
  · have hget := congr_arg (fun l : List F => l[n]?) h
    rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hn, dif_pos (hdeg ▸ hn)] at hget
    exact Option.some.inj hget
  · have hp : p.natDegree < n := by omega
    have hq : q.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp, Polynomial.coeff_eq_zero_of_natDegree_lt hq]

private theorem exists_subfield_hom_complex (K : Type*) [Field K] [CharZero K] (S : Finset K) :
    ∃ (F : Subfield K) (_ : Countable F) (φ : F →+* ℂ), (S : Set K) ⊆ F := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    let F : Subfield K := RingHom.fieldRange (Rat.castHom K)
    have hCount : Countable F := by
      have hset : Set.Countable (F : Set K) := Set.countable_range (Rat.castHom K)
      exact hset.to_subtype
    let e : ℚ ≃+* F := RingEquiv.ofBijective
      ((Rat.castHom K).codRestrict F (fun q => ⟨q, rfl⟩))
      ⟨fun a b h => (Rat.castHom K).injective (congr_arg Subtype.val h),
       fun ⟨y, q, hq⟩ => ⟨q, Subtype.ext hq⟩⟩
    exact ⟨F, hCount, (Rat.castHom ℂ).comp e.symm.toRingHom, by simp⟩
  | insert x S hxS ih =>
    obtain ⟨F, hCount, φ, hSF⟩ := ih
    let F' : Subfield K := Subfield.closure (insert x (F : Set K))
    let evalF : Polynomial F →+* K := Polynomial.eval₂RingHom (algebraMap F K) x
    let R : Set K := { z | ∃ p q : Polynomial F, evalF q ≠ 0 ∧ z = evalF p / evalF q }
    have hR0 : (0 : K) ∈ R := ⟨0, 1, by simp [evalF], by simp [evalF]⟩
    have hR1 : (1 : K) ∈ R := ⟨1, 1, by simp [evalF], by simp [evalF]⟩
    have hRadd : ∀ {a b : K}, a ∈ R → b ∈ R → a + b ∈ R := by
      rintro a b ⟨p₁, q₁, hq₁, rfl⟩ ⟨p₂, q₂, hq₂, rfl⟩
      refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, by simp [hq₁, hq₂], ?_⟩
      rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hq₁ hq₂]
      ring
    have hRneg : ∀ {a : K}, a ∈ R → -a ∈ R := by
      rintro a ⟨p, q, hq, rfl⟩
      exact ⟨-p, q, hq, by rw [map_neg, neg_div]⟩
    have hRmul : ∀ {a b : K}, a ∈ R → b ∈ R → a * b ∈ R := by
      rintro a b ⟨p₁, q₁, hq₁, rfl⟩ ⟨p₂, q₂, hq₂, rfl⟩
      exact ⟨p₁ * p₂, q₁ * q₂, by simp [hq₁, hq₂], by rw [map_mul, map_mul, div_mul_div_comm]⟩
    have hRinv : ∀ {a : K}, a ∈ R → a⁻¹ ∈ R := by
      rintro a ⟨p, q, hq, rfl⟩
      by_cases hp : evalF p = 0
      · simp [hp, hR0]
      · exact ⟨q, p, hp, by rw [inv_div]⟩
    let Rsub : Subfield K :=
      { carrier := R
        zero_mem' := hR0
        one_mem' := hR1
        add_mem' := hRadd
        neg_mem' := hRneg
        mul_mem' := hRmul
        inv_mem' := fun _ ha => hRinv ha }
    have hFR : insert x (F : Set K) ⊆ R := by
      intro y hy
      rcases hy with rfl | hyF
      · exact ⟨Polynomial.X, 1, by simp [evalF], by simp [evalF]⟩
      · exact ⟨Polynomial.C ⟨y, hyF⟩, 1, by simp [evalF], by simp [evalF]; rfl⟩
    have hF'R : (F' : Set K) ⊆ R := show F' ≤ Rsub from Subfield.closure_le.mpr hFR
    have hCountPoly : Countable (Polynomial F) := countable_polynomial
    have hCountF' : Countable F' := by
      let g : Polynomial F × Polynomial F → K := fun pq => evalF pq.1 / evalF pq.2
      have hsurj : (F' : Set K) ⊆ Set.range g := by
        intro y hy
        obtain ⟨p, q, _, rfl⟩ := hF'R hy
        exact ⟨(p, q), rfl⟩
      have hset : Set.Countable (F' : Set K) := (Set.countable_range g).mono hsurj
      exact hset.to_subtype
    have hSF' : ((insert x S : Finset K) : Set K) ⊆ F' := by
      intro y hy
      rw [Finset.coe_insert] at hy
      rcases hy with rfl | hyS
      · exact Subfield.subset_closure (Set.mem_insert _ _)
      · exact Subfield.subset_closure (Set.mem_insert_of_mem x (hSF hyS))
    by_cases halg : ∃ p : Polynomial F, p ≠ 0 ∧ evalF p = 0
    · obtain ⟨p, hp0, hpval⟩ := halg
      have hisAlg : IsAlgebraic F x := ⟨p, hp0, by simpa [evalF, Polynomial.aeval_def] using hpval⟩
      let m := minpoly F x
      have hm_irr : Irreducible m := minpoly.irreducible hisAlg.isIntegral
      have hm_deg : (m.map φ).degree ≠ 0 := by
        refine ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp ?_)
        rw [Polynomial.natDegree_map_eq_of_injective φ.injective]
        exact hm_irr.natDegree_pos
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (m.map φ) hm_deg
      have hmz : Polynomial.eval₂ φ z m = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_map] using hz
      let Ralg : Set K := Set.range evalF
      let Ralg_sub : Subfield K :=
        { carrier := Ralg
          zero_mem' := ⟨0, map_zero evalF⟩
          one_mem' := ⟨1, map_one evalF⟩
          add_mem' := by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, map_add evalF p q⟩
          neg_mem' := by rintro _ ⟨p, rfl⟩; exact ⟨-p, map_neg evalF p⟩
          mul_mem' := by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p * q, map_mul evalF p q⟩
          inv_mem' := by
            rintro _ ⟨q, rfl⟩
            by_cases hq : evalF q = 0
            · exact ⟨0, by simp [hq]⟩
            · have hndvd : ¬ m ∣ q := by
                intro hd
                obtain ⟨r, rfl⟩ := hd
                have hm0 : evalF m = 0 := by simpa [evalF, Polynomial.aeval_def] using minpoly.aeval F x
                exact hq (by simp [hm0])
              obtain ⟨u, v, huv⟩ := hm_irr.coprime_iff_not_dvd.mpr hndvd
              refine ⟨v, ?_⟩
              have h1 : evalF u * evalF m + evalF v * evalF q = 1 := by
                simpa [map_add, map_mul] using congr_arg evalF huv
              have hm0 : evalF m = 0 := by simpa [evalF, Polynomial.aeval_def] using minpoly.aeval F x
              rw [hm0, mul_zero, zero_add] at h1
              exact eq_inv_of_mul_eq_one_left h1 }
      have hF'alg : (F' : Set K) ⊆ Ralg := by
        change F' ≤ Ralg_sub
        refine Subfield.closure_le.mpr ?_
        intro y hy
        rcases hy with rfl | hyF
        · exact ⟨Polynomial.X, by simp [evalF]⟩
        · exact ⟨Polynomial.C ⟨y, hyF⟩, by simp [evalF]; rfl⟩
      have hwelldef : ∀ q₁ q₂ : Polynomial F, evalF q₁ = evalF q₂ →
          Polynomial.eval₂ φ z q₁ = Polynomial.eval₂ φ z q₂ := by
        intro q₁ q₂ hq
        have hdvd : m ∣ (q₁ - q₂) := minpoly.dvd F x (by
          simpa [evalF, Polynomial.aeval_def, sub_eq_zero] using hq)
        obtain ⟨r, hr⟩ := hdvd
        have h0 : Polynomial.eval₂ φ z (q₁ - q₂) = 0 := by
          rw [hr, Polynomial.eval₂_mul, hmz, zero_mul]
        simpa [Polynomial.eval₂_sub, sub_eq_zero] using h0
      have hex : ∀ y : F', ∃ q : Polynomial F, (y : K) = evalF q := fun y =>
        let ⟨q, hq⟩ := hF'alg y.2
        ⟨q, hq.symm⟩
      let ψ : F' →+* ℂ :=
        { toFun := fun y => Polynomial.eval₂ φ z (Classical.choose (hex y))
          map_one' := by
            have h := hwelldef _ 1 (by simpa using (Classical.choose_spec (hex 1)).symm)
            simpa using h
          map_mul' := fun a b => by
            have h := hwelldef (Classical.choose (hex (a * b)))
              (Classical.choose (hex a) * Classical.choose (hex b)) (by
                rw [map_mul, ← Classical.choose_spec (hex a), ← Classical.choose_spec (hex b),
                  ← Classical.choose_spec (hex (a * b))]; rfl)
            simpa [Polynomial.eval₂_mul] using h
          map_zero' := by
            have h := hwelldef _ 0 (by simpa using (Classical.choose_spec (hex 0)).symm)
            simpa using h
          map_add' := fun a b => by
            have h := hwelldef (Classical.choose (hex (a + b)))
              (Classical.choose (hex a) + Classical.choose (hex b)) (by
                rw [map_add, ← Classical.choose_spec (hex a), ← Classical.choose_spec (hex b),
                  ← Classical.choose_spec (hex (a + b))]; rfl)
            simpa [Polynomial.eval₂_add] using h }
      exact ⟨F', hCountF', ψ, hSF'⟩
    · push Not at halg
      let U : Set ℂ := ⋃ (p : { p : Polynomial F // p ≠ 0 }), ((p.1.map φ).roots.toFinset : Set ℂ)
      have hU : Set.Countable U := Set.countable_iUnion fun p => (Finset.finite_toSet _).countable
      have hUnc : Uncountable ℂ := Complex.ofReal_injective.uncountable
      have hne : U ≠ Set.univ := fun h => by
        have hc : Countable ℂ := by
          rw [← Set.countable_univ_iff, ← h]
          exact hU
        exact not_countable hc
      obtain ⟨z, hzU⟩ : ∃ z : ℂ, z ∉ U := by
        by_contra h
        push Not at h
        exact hne (Set.eq_univ_of_forall h)
      have hz_nonzero : ∀ p : Polynomial F, p ≠ 0 → Polynomial.eval₂ φ z p ≠ 0 := by
        intro p hp hzp
        apply hzU
        refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots]
        · simpa [Polynomial.IsRoot, Polynomial.eval_map] using hzp
        · exact Polynomial.map_ne_zero hp
      have hex : ∀ y : F', ∃ pq : Polynomial F × Polynomial F,
          evalF pq.2 ≠ 0 ∧ (y : K) = evalF pq.1 / evalF pq.2 := fun y =>
        let ⟨p, q, hq, hpq⟩ := hF'R y.2
        ⟨(p, q), hq, hpq⟩
      have hwelldef : ∀ p₁ q₁ p₂ q₂ : Polynomial F,
          evalF q₁ ≠ 0 → evalF q₂ ≠ 0 →
          evalF p₁ / evalF q₁ = evalF p₂ / evalF q₂ →
          Polynomial.eval₂ φ z p₁ / Polynomial.eval₂ φ z q₁ =
            Polynomial.eval₂ φ z p₂ / Polynomial.eval₂ φ z q₂ := by
        intro p₁ q₁ p₂ q₂ hq₁ hq₂ hdiv
        have hq₁0 : q₁ ≠ 0 := fun h => hq₁ (by simp [h])
        have hq₂0 : q₂ ≠ 0 := fun h => hq₂ (by simp [h])
        have hcross : evalF (p₁ * q₂ - p₂ * q₁) = 0 := by
          rw [map_sub, map_mul, map_mul, sub_eq_zero]
          exact (div_eq_div_iff hq₁ hq₂).mp hdiv
        have hpoly : p₁ * q₂ - p₂ * q₁ = 0 := by
          by_contra hne0
          exact halg _ hne0 hcross
        have hpoly' : p₁ * q₂ = p₂ * q₁ := sub_eq_zero.mp hpoly
        have hC := congr_arg (Polynomial.eval₂ φ z) hpoly'
        simp only [Polynomial.eval₂_mul] at hC
        exact (div_eq_div_iff (hz_nonzero q₁ hq₁0) (hz_nonzero q₂ hq₂0)).mpr hC
      let ψ : F' →+* ℂ :=
        { toFun := fun y =>
            Polynomial.eval₂ φ z (Classical.choose (hex y)).1 /
              Polynomial.eval₂ φ z (Classical.choose (hex y)).2
          map_one' := by
            have hs := Classical.choose_spec (hex 1)
            have h := hwelldef _ _ 1 1 hs.1 (by simp [evalF]) (by rw [← hs.2]; simp [evalF])
            exact h.trans (by simp)
          map_mul' := fun a b => by
            have hsa := Classical.choose_spec (hex a)
            have hsb := Classical.choose_spec (hex b)
            have hsab := Classical.choose_spec (hex (a * b))
            have hdiv : evalF (Classical.choose (hex (a * b))).1 /
                  evalF (Classical.choose (hex (a * b))).2 =
                evalF ((Classical.choose (hex a)).1 * (Classical.choose (hex b)).1) /
                evalF ((Classical.choose (hex a)).2 * (Classical.choose (hex b)).2) := by
              rw [← hsab.2, Subring.coe_mul]
              conv_lhs => rw [hsa.2, hsb.2]
              rw [div_mul_div_comm, map_mul, map_mul]
            have h := hwelldef _ _ _ _ hsab.1 (by simp [hsa.1, hsb.1]) hdiv
            exact h.trans (by simp [Polynomial.eval₂_mul, div_mul_div_comm])
          map_zero' := by
            have hs := Classical.choose_spec (hex 0)
            have h := hwelldef _ _ 0 1 hs.1 (by simp [evalF]) (by rw [← hs.2]; simp [evalF])
            exact h.trans (by simp)
          map_add' := fun a b => by
            have hsa := Classical.choose_spec (hex a)
            have hsb := Classical.choose_spec (hex b)
            have hsab := Classical.choose_spec (hex (a + b))
            have hdiv : evalF (Classical.choose (hex (a + b))).1 /
                  evalF (Classical.choose (hex (a + b))).2 =
                evalF ((Classical.choose (hex a)).1 * (Classical.choose (hex b)).2 +
                  (Classical.choose (hex b)).1 * (Classical.choose (hex a)).2) /
                evalF ((Classical.choose (hex a)).2 * (Classical.choose (hex b)).2) := by
              rw [← hsab.2, Subring.coe_add]
              conv_lhs => rw [hsa.2, hsb.2]
              rw [div_add_div _ _ hsa.1 hsb.1, map_add, map_mul, map_mul, map_mul]
              ring_nf
            have h := hwelldef _ _ _ _ hsab.1 (by simp [hsa.1, hsb.1]) hdiv
            have hqa0 : Polynomial.eval₂ φ z (Classical.choose (hex a)).2 ≠ 0 :=
              hz_nonzero _ (fun h => hsa.1 (by simp [h]))
            have hqb0 : Polynomial.eval₂ φ z (Classical.choose (hex b)).2 ≠ 0 :=
              hz_nonzero _ (fun h => hsb.1 (by simp [h]))
            exact h.trans (by
              simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul]
              rw [div_add_div _ _ hqa0 hqb0]
              ring) }
      exact ⟨F', hCountF', ψ, hSF'⟩

private lemma mapRingHom_single {A B : Type*} [Field A] [Field B] (G : Type*) [Group G]
    (f : A →+* B) (g : G) (c : A) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) = MonoidAlgebra.single g (f c) := by
  simp [MonoidAlgebra.mapRingHom]

private lemma mapRingHom_inj {A B : Type*} [Field A] [Field B] (G : Type*) [Group G]
    (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro x y hxy
  ext g
  apply hf
  have h := congr_arg (fun z : MonoidAlgebra B G => z.coeff g) hxy
  simpa using h

private lemma ma_coeff_single {A : Type*} [Field A] (G : Type*) [DecidableEq G] (g k : G) (c : A) :
    (MonoidAlgebra.single g c).coeff k = if g = k then c else 0 := by
  change (Finsupp.single g c) k = if g = k then c else 0
  simp [Finsupp.single_apply]

private lemma ma_coeff_sum {A : Type*} [Field A] (G : Type*) [DecidableEq G] (s : Finset G)
    (f : G → MonoidAlgebra A G) (k : G) :
    (∑ g ∈ s, f g).coeff k = ∑ g ∈ s, (f g).coeff k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

private theorem char_zero_main (K : Type*) [Field K] [CharZero K] (G : Type*) [Group G] :
    IsDedekindFiniteMonoid (MonoidAlgebra K G) := by
  classical
  rw [isDedekindFiniteMonoid_iff]
  intro a b hab
  let S : Finset K := a.coeff.support.image a.coeff ∪ b.coeff.support.image b.coeff
  obtain ⟨F, _, φ, hSF⟩ := exists_subfield_hom_complex K S
  have haF : ∀ g : G, a.coeff g ∈ F := fun g => by
    by_cases hg : g ∈ a.coeff.support
    · exact hSF (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg))
    · simp [Finsupp.notMem_support_iff.mp hg, F.zero_mem]
  have hbF : ∀ g : G, b.coeff g ∈ F := fun g => by
    by_cases hg : g ∈ b.coeff.support
    · exact hSF (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg))
    · simp [Finsupp.notMem_support_iff.mp hg, F.zero_mem]
  let aF : MonoidAlgebra F G :=
    ∑ g ∈ a.coeff.support, MonoidAlgebra.single g ⟨a.coeff g, haF g⟩
  let bF : MonoidAlgebra F G :=
    ∑ g ∈ b.coeff.support, MonoidAlgebra.single g ⟨b.coeff g, hbF g⟩
  have haF_map : MonoidAlgebra.mapRingHom G F.subtype aF = a := by
    dsimp [aF]
    rw [map_sum]
    ext k
    rw [ma_coeff_sum]
    simp only [mapRingHom_single, ma_coeff_single]
    by_cases hk : k ∈ a.coeff.support
    · rw [Finset.sum_eq_single k (fun g _ hgk => if_neg hgk) (fun h => absurd hk h)]
      simp
    · rw [Finset.sum_eq_zero (fun g hg => if_neg (fun hgk => hk (by rwa [← hgk])))]
      exact (Finsupp.notMem_support_iff.mp hk).symm
  have hbF_map : MonoidAlgebra.mapRingHom G F.subtype bF = b := by
    dsimp [bF]
    rw [map_sum]
    ext k
    rw [ma_coeff_sum]
    simp only [mapRingHom_single, ma_coeff_single]
    by_cases hk : k ∈ b.coeff.support
    · rw [Finset.sum_eq_single k (fun g _ hgk => if_neg hgk) (fun h => absurd hk h)]
      simp
    · rw [Finset.sum_eq_zero (fun g hg => if_neg (fun hgk => hk (by rwa [← hgk])))]
      exact (Finsupp.notMem_support_iff.mp hk).symm
  have habF : aF * bF = 1 := by
    apply mapRingHom_inj G F.subtype F.subtype.injective
    rw [map_mul, haF_map, hbF_map, hab, map_one]
  have hbaC : (MonoidAlgebra.mapRingHom G φ bF) * (MonoidAlgebra.mapRingHom G φ aF) = 1 :=
    (isDedekindFiniteMonoid_iff _).mp (direct_finiteness_complex G)
      (by rw [← map_mul, habF, map_one])
  have hbaF : bF * aF = 1 := by
    apply mapRingHom_inj G φ φ.injective
    rw [map_mul, hbaC, map_one]
  rw [← hbF_map, ← haF_map, ← map_mul, hbaF, map_one]

end OMA.KaplanskyCharZero

theorem OMA.solution : type_of% @Kaplansky.direct_finiteness_conjecture.variants.char_zero :=
  OMA.KaplanskyCharZero.char_zero_main
