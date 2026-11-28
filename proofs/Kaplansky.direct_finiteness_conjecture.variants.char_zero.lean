import FormalConjectures.Wikipedia.Kaplansky

/-!
# Direct finiteness of group algebras in characteristic zero

Over the complex numbers, the orthogonal projection onto the range of the idempotent
`1 - b * a` has the same coefficient at the identity as the idempotent itself.
For a general field of characteristic zero, adjoining the inverse of a nonzero
coefficient ensures that it survives specialization to the complex numbers.
-/

namespace OMA.KaplanskyDF

noncomputable section

open scoped ENNReal

abbrev Hil (G : Type*) := lp (fun _ : G => ℂ) 2

variable {G : Type*}

private def pull (e : G ≃ G) (f : Hil G) : Hil G :=
  ⟨fun x => f (e x), memℓp_gen <| (e.summable_iff).2 <| f.prop.summable (by norm_num)⟩

private theorem pull_le (e : G ≃ G) (f : Hil G) : ‖pull e f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg f)
  intro s
  simpa [pull] using lp.sum_rpow_le_norm_rpow (by norm_num) f (s.map e.toEmbedding)

private def permute (e : G ≃ G) : Hil G ≃ₗᵢ[ℂ] Hil G where
  toFun := pull e
  invFun := pull e.symm
  left_inv f := lp.ext (funext fun x => by simp [pull])
  right_inv f := lp.ext (funext fun x => by simp [pull])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := le_antisymm (pull_le e f) <| by
    have h := pull_le e.symm (pull e f)
    have he : pull e.symm (pull e f) = f := lp.ext (funext fun x => by simp [pull])
    rwa [he] at h

def delta (g : G) : Hil G := by
  classical
  exact lp.single 2 g 1

theorem inner_delta (g : G) (f : Hil G) : inner ℂ (delta g) f = f g := by
  classical
  simp [delta, lp.inner_single_left, RCLike.inner_apply]

private theorem delta_apply (g x : G) [DecidableEq G] :
    delta g x = if x = g then 1 else 0 := by
  classical
  simp [delta, Pi.single_apply]

variable [Group G]

def right (g : G) : Hil G ≃ₗᵢ[ℂ] Hil G := permute (Equiv.mulRight g)

theorem right_apply (g : G) (f : Hil G) (x : G) : right g f x = f (x * g) := rfl

private def leftAction : G →* (Hil G →L[ℂ] Hil G) where
  toFun g := (permute (Equiv.mulLeft g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by
    ext f x
    change f (1⁻¹ * x) = f x
    simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]

def regular : MonoidAlgebra ℂ G →ₐ[ℂ] (Hil G →L[ℂ] Hil G) :=
  MonoidAlgebra.lift ℂ _ G leftAction

theorem regular_apply (a : MonoidAlgebra ℂ G) (f : Hil G) (x : G) :
    regular a f x = ∑ s ∈ a.coeff.support, a.coeff s * f (s⁻¹ * x) := by
  simp only [regular, MonoidAlgebra.lift_apply, Finsupp.sum, sum_apply, smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  rfl

theorem right_delta (g : G) : right g⁻¹ (delta 1) = delta g := by
  classical
  apply lp.ext
  funext x
  simp [right_apply, delta_apply, mul_inv_eq_one]

theorem regular_right (a : MonoidAlgebra ℂ G) (g : G) (f : Hil G) :
    regular a (right g f) = right g (regular a f) := by
  apply lp.ext
  funext x
  simp [regular_apply, right_apply, mul_assoc]

theorem regular_delta (a : MonoidAlgebra ℂ G) :
    regular a (delta 1) = ∑ s ∈ a.coeff.support, a.coeff s • delta s := by
  classical
  apply lp.ext
  funext x
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [regular_apply, delta_apply, lp.coeFn_smul, inv_mul_eq_one, eq_comm]

theorem regular_delta_apply (a : MonoidAlgebra ℂ G) (x : G) :
    regular a (delta 1) x = a.coeff x := by
  classical
  simp [regular_apply, delta_apply, inv_mul_eq_one, mul_ite, Finsupp.mem_support_iff, eq_comm]

/-- Orthogonal projection onto the range of an idempotent respects its unitary symmetries. -/
theorem existsProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : H →L[ℂ] H) (hP : ∀ f, P (P f) = P f) :
    ∃ E : H →L[ℂ] H, (∀ f, E (P f) = P f) ∧ (∀ f, P (E f) = E f) ∧
      (∀ f, E (E f) = E f) ∧ (∀ u v, inner ℂ (E u) v = inner ℂ u (E v)) ∧
      (∀ (U : H ≃ₗᵢ[ℂ] H), (∀ f, P (U f) = U (P f)) → ∀ f, E (U f) = U (E f)) := by
  have h : IsIdempotentElem P := ContinuousLinearMap.ext hP
  let M := P.range
  let : M.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range h
  have hfix {x : H} : x ∈ M ↔ P x = x :=
    LinearMap.IsIdempotentElem.mem_range_iff (ContinuousLinearMap.IsIdempotentElem.toLinearMap h)
  refine ⟨M.starProjection, fun f ↦ Submodule.starProjection_eq_self_iff.mpr ⟨f, rfl⟩,
    fun f ↦ hfix.mp (M.starProjection_apply_mem f),
    fun f ↦ Submodule.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem f),
    M.inner_starProjection_left_eq_right, ?_⟩
  intro U hU f
  have hm : M.map (U.toLinearEquiv : H →ₗ[ℂ] H) = M := by
    ext y
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨U v, hU v⟩
    · rintro ⟨v, rfl⟩
      refine ⟨P (U.symm v), ⟨_, rfl⟩, ?_⟩
      change U (P (U.symm v)) = P v
      rw [← hU, U.apply_symm_apply]
  simpa only [hm, U.symm_apply_apply] using M.starProjection_map_apply U (U f)

private theorem coeff_one_mul_comm (a b : MonoidAlgebra ℂ G) :
    (a * b).coeff 1 = (b * a).coeff 1 := by
  simp [MonoidAlgebra.coeff_mul_apply_left a b, MonoidAlgebra.coeff_mul_apply_right b a, mul_comm]

/-- On the identity vector, convolution and a right-translation invariant operator
have the same identity coefficient in either order. Only the support of `p` is summed. -/
private theorem trace_comm (p : MonoidAlgebra ℂ G) (E : Hil G →L[ℂ] Hil G)
    (hE : ∀ g f, E (right g f) = right g (E f)) :
    regular p (E (delta 1)) 1 = E (regular p (delta 1)) 1 := by
  have h (s : G) : E (delta s) 1 = E (delta 1) s⁻¹ := by
    rw [← right_delta s, hE, right_apply, one_mul]
  rw [regular_apply, regular_delta, map_sum]
  simp only [map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, h, mul_one]

private theorem complex_direct (a b : MonoidAlgebra ℂ G) (hab : a * b = 1) : b * a = 1 := by
  let p := 1 - b * a
  have hpp : p * p = p := by
    apply IsIdempotentElem.one_sub
    calc
      (b * a) * (b * a) = b * (a * b) * a := by simp only [mul_assoc]
      _ = b * a := by rw [hab, mul_one]
  have hp₁ : p.coeff 1 = 0 := by
    simp [p, coeff_one_mul_comm b a, hab]
  obtain ⟨E, hEP, hPE, hEE, hself, hcomm⟩ := existsProjection (regular p) (fun f ↦ by
    change ((regular p * regular p) f) = _
    rw [← map_mul, hpp])
  have hR (g : G) := hcomm (right g) (regular_right p g)
  have he : E (delta (1 : G)) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [hself, hEE, inner_delta, ← hPE (delta 1), trace_comm p E hR, hEP,
      regular_delta_apply, hp₁]
  have hd (g : G) : E (delta g) = 0 := by rw [← right_delta g, hR, he, map_zero]
  have hz : regular p (delta 1) = 0 := by
    calc
      _ = E (regular p (delta 1)) := (hEP _).symm
      _ = 0 := by simp [regular_delta, map_sum, hd]
  suffices p = 0 from (sub_eq_zero.mp this).symm
  ext x
  change p.coeff x = 0
  rw [← regular_delta_apply, hz]
  rfl

open MonoidAlgebra

variable {K : Type*} [Field K] [CharZero K]

/-- Specialize a finite type rational algebra at a complex point. -/
private theorem existsComplexPoint (R : Type*) [CommRing R] [Nontrivial R]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] : Nonempty (R →+* ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[ℚ] ℂ).toRingHom.comp (Ideal.Quotient.mk m)⟩

private theorem liftCoeffs (R : Subalgebra ℚ K) (a : MonoidAlgebra K G)
    (ha : Set.range a.coeff ⊆ R) :
    ∃ x, mapRingHom G R.val.toRingHom x = a := by
  change a ∈ Set.range (MonoidAlgebra.map (M := G) R.val.toRingHom.toAddMonoidHom)
  rw [range_map]
  exact fun i => ⟨⟨a.coeff i, ha ⟨i, rfl⟩⟩, rfl⟩

theorem fromComplex (hc : ∀ (a b : MonoidAlgebra ℂ G), a * b = 1 → b * a = 1)
    (a b : MonoidAlgebra K G) (hab : a * b = 1) : b * a = 1 := by
  classical
  ext g
  by_contra hn
  let c := (1 - b * a).coeff g
  have hne : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  let S := Set.range a.coeff ∪ Set.range b.coeff ∪ {c⁻¹}
  let R := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ R :=
    Algebra.FiniteType.adjoin_of_finite ((a.coeff.finite_range.union b.coeff.finite_range).union
      (Set.finite_singleton _))
  obtain ⟨x, hx⟩ := liftCoeffs R a (fun _ hi => Algebra.subset_adjoin (Or.inl (Or.inl hi)))
  obtain ⟨y, hy⟩ := liftCoeffs R b (fun _ hi => Algebra.subset_adjoin (Or.inl (Or.inr hi)))
  let I := mapRingHom G R.val.toRingHom
  have hxy : x * y = 1 := by
    apply MonoidAlgebra.map_injective (M := G) R.val.toRingHom.toAddMonoidHom Subtype.val_injective
    change I (x * y) = I 1
    simpa only [map_mul, map_one, I, hx, hy] using hab
  let r := (1 - y * x).coeff g
  have hr : (r : K) = c := by
    calc
      _ = (I (1 - y * x)).coeff g := (coeff_mapRingHom R.val.toRingHom _ _).symm
      _ = c := by simp only [map_sub, map_one, map_mul, I, hx, hy, c]
  let t : R := ⟨c⁻¹, Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))⟩
  have hrt : r * t = 1 := Subtype.ext (by change (r : K) * c⁻¹ = 1; rw [hr, mul_inv_cancel₀ hne])
  obtain ⟨φ⟩ := existsComplexPoint R
  let J := mapRingHom G φ
  have hyx := hc (J x) (J y) (by rw [← map_mul, hxy, map_one])
  have hJ : J (1 - y * x) = 0 := by rw [map_sub, map_one, map_mul, hyx, sub_self]
  have hz : φ r = 0 := by
    simpa only [J, coeff_mapRingHom, coeff_zero, Finsupp.zero_apply, r] using
      congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) hJ
  have := congrArg φ hrt
  simp [hz] at this

end

end OMA.KaplanskyDF

theorem OMA.solution :
    type_of% @Kaplansky.direct_finiteness_conjecture.variants.char_zero := by
  intro K _ _ G _
  exact ⟨fun {a b} hab ↦ OMA.KaplanskyDF.fromComplex OMA.KaplanskyDF.complex_direct a b hab⟩
