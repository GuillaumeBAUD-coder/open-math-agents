import FormalConjectures.Paper.KaplanskyUInvariant

/-!
Kaplansky's proof that no field of characteristic ≠ 2 has u-invariant 5.
-/

-- Problem: Kaplansky's problem on the values of the $u$-invariant - not five
-- Upstream: formal-conjectures FormalConjectures/Paper/KaplanskyUInvariant.lean:158 (declaration KaplanskyUInvariant.u_invariant_values.variants.not_five)
-- Credit: @kintonc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.KaplanskyNotFive

open QuadraticMap QuadraticForm

/-- The 5-to-6 norm identity behind Kaplansky's proof that u = 5 is impossible. -/
lemma key5 {F : Type} [Field F] (u v c : F)
    (h5 : ∀ x₁ y₁ x₂ y₂ z : F,
      x₁ ^ 2 + u * y₁ ^ 2 + v * x₂ ^ 2 + u * v * y₂ ^ 2 + c * z ^ 2 = 0 →
      x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ z = 0)
    (x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (heq : x₁ ^ 2 + u * y₁ ^ 2 + v * x₂ ^ 2 + u * v * y₂ ^ 2 +
      c * x₃ ^ 2 + c * u * y₃ ^ 2 = 0) :
    x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ x₃ = 0 ∧ y₃ = 0 := by
  by_cases hN : x₃ ^ 2 + u * y₃ ^ 2 = 0
  · have h1 : x₃ ^ 2 + u * y₃ ^ 2 + v * 0 ^ 2 + u * v * 0 ^ 2 + c * 0 ^ 2 = 0 := by
      linear_combination hN
    obtain ⟨hx₃, hy₃, -, -, -⟩ := h5 _ _ _ _ _ h1
    subst hx₃ hy₃
    have h2 : x₁ ^ 2 + u * y₁ ^ 2 + v * x₂ ^ 2 + u * v * y₂ ^ 2 + c * 0 ^ 2 = 0 := by
      linear_combination heq
    obtain ⟨hx₁, hy₁, hx₂, hy₂, -⟩ := h5 _ _ _ _ _ h2
    exact ⟨hx₁, hy₁, hx₂, hy₂, rfl, rfl⟩
  · exfalso
    have h3 : (x₁ * x₃ - u * y₁ * y₃) ^ 2 + u * (x₁ * y₃ + y₁ * x₃) ^ 2 +
        v * (x₂ * x₃ - u * y₂ * y₃) ^ 2 + u * v * (x₂ * y₃ + y₂ * x₃) ^ 2 +
        c * (x₃ ^ 2 + u * y₃ ^ 2) ^ 2 = 0 := by
      linear_combination (x₃ ^ 2 + u * y₃ ^ 2) * heq
    exact hN (h5 _ _ _ _ _ h3).2.2.2.2

end OMA.KaplanskyNotFive

open QuadraticMap QuadraticForm OMA.KaplanskyNotFive in
theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.not_five := by
  rintro ⟨F, _, _, hmax, hub⟩
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmax
  have : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hQ0 : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    have := hQ _ h0
    simpa using this
  have hm : Module.finrank F (Fin 5 → F) = 5 := by simp
  generalize Module.finrank F (Fin 5 → F) = m at w hQ0 hm
  subst hm
  have hw : ∀ i : Fin 5, w i ≠ 0 := by
    intro i hi
    have h0 : weightedSumSquares F w (Pi.single i (1 : F)) = 0 := by
      simp [weightedSumSquares_apply, Pi.single_apply, hi]
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congr_fun (hQ0 _ h0) i)
  set d : F := ∏ i : Fin 5, w i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hw i
  -- Step 2: Find v₀ with weightedSumSquares F w v₀ = d
  let w₆ : Fin 6 → F := ![w 0, w 1, w 2, w 3, w 4, -d]
  have h6_not : ¬ (6 ∈ anisotropicDims F) := fun h => by
    have := hub h
    omega
  have ⟨z, hz_ne, hz_eq⟩ : ∃ z : Fin 6 → F, z ≠ 0 ∧ weightedSumSquares F w₆ z = 0 := by
    by_contra h
    push Not at h
    exact h6_not (mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F w₆,
      fun x hx => by_contra fun hx0 => h x hx0 hx⟩)
  have hz_sum : ∑ i : Fin 5, w i * z i.castSucc ^ 2 - d * z 5 ^ 2 = 0 := by
    have hw₆ : ∀ i : Fin 5, w₆ i.castSucc = w i := fun i => by fin_cases i <;> rfl
    have hw₆_5 : w₆ (Fin.last 5) = -d := rfl
    have hlast : z (Fin.last 5) = z 5 := rfl
    rw [weightedSumSquares_apply, Fin.sum_univ_castSucc] at hz_eq
    simp only [smul_eq_mul] at hz_eq
    rw [hw₆_5, hlast] at hz_eq
    have hsum5 : ∑ i : Fin 5, w₆ i.castSucc * (z i.castSucc * z i.castSucc) =
        ∑ i : Fin 5, w i * z i.castSucc ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hw₆]; ring
    rw [hsum5] at hz_eq
    linear_combination hz_eq
  have hz5 : z 5 ≠ 0 := by
    intro hz5_0
    have hz'_eq : weightedSumSquares F w (fun i : Fin 5 => z i.castSucc) = 0 := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      have hsum5' : ∑ x : Fin 5, w x * (z x.castSucc * z x.castSucc) =
          ∑ i : Fin 5, w i * z i.castSucc ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hsum5']
      rw [hz5_0] at hz_sum
      linear_combination hz_sum
    have hz'_0 := hQ0 _ hz'_eq
    apply hz_ne
    funext i
    fin_cases i
    · exact congr_fun hz'_0 0
    · exact congr_fun hz'_0 1
    · exact congr_fun hz'_0 2
    · exact congr_fun hz'_0 3
    · exact congr_fun hz'_0 4
    · exact hz5_0
  let v₀ : Fin 5 → F := fun i => z i.castSucc / z 5
  have hv₀ : weightedSumSquares F w v₀ = d := by
    simp only [weightedSumSquares_apply, smul_eq_mul, v₀]
    have hmul : (∑ i : Fin 5, w i * (z i.castSucc / z 5 * (z i.castSucc / z 5))) * z 5 ^ 2 =
        ∑ i : Fin 5, w i * z i.castSucc ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hz5]
    have hnum : ∑ i : Fin 5, w i * z i.castSucc ^ 2 = d * z 5 ^ 2 := by
      linear_combination hz_sum
    have hz5_sq : z 5 ^ 2 ≠ 0 := pow_ne_zero 2 hz5
    exact mul_right_cancel₀ hz5_sq (hmul.trans hnum)
  -- Step 3: Orthogonal complement W of v₀ and diagonalization of Q₀|_W
  let φ : (Fin 5 → F) →ₗ[F] F :=
    { toFun := fun x => ∑ i : Fin 5, w i * v₀ i * x i
      map_add' := fun x y => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hφv₀ : φ v₀ = d := by
    have : φ v₀ = weightedSumSquares F w v₀ := by
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, weightedSumSquares_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hv₀]
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨(c / d) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul, hφv₀, div_mul_cancel₀ _ hd]
  let W : Submodule F (Fin 5 → F) := LinearMap.ker φ
  have hW_rank : Module.finrank F W = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
    rw [hr, finrank_top, Module.finrank_self] at h
    have h5 : Module.finrank F (Fin 5 → F) = 5 := by simp
    rw [h5] at h
    change 1 + Module.finrank F W = 5 at h
    omega
  have hQ_orth : ∀ t : F, ∀ y ∈ W,
      weightedSumSquares F w (t • v₀ + y) = d * t ^ 2 + weightedSumSquares F w y := by
    intro t y hy
    have hφy : φ y = 0 := LinearMap.mem_ker.mp hy
    have hcross : ∑ i : Fin 5, w i * v₀ i * y i = 0 := hφy
    have hsum : weightedSumSquares F w (t • v₀ + y) =
        t ^ 2 * weightedSumSquares F w v₀ +
        2 * t * (∑ i : Fin 5, w i * v₀ i * y i) +
        weightedSumSquares F w y := by
      simp only [weightedSumSquares_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, hv₀, hcross]
    ring
  let Q_W : QuadraticForm F W := (weightedSumSquares F w).comp W.subtype
  have hQ_W_aniso : Q_W.Anisotropic := fun y hy => Subtype.ext (hQ0 (y : Fin 5 → F) hy)
  obtain ⟨p, ⟨eW⟩⟩ := Q_W.equivalent_weightedSumSquares
  generalize Module.finrank F W = mW at p eW hW_rank
  subst hW_rank
  let E : (Fin 5 → F) →ₗ[F] (Fin 5 → F) :=
    { toFun := fun x => (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 4 => x j.succ))
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul]
        have : (fun j : Fin 4 => x j.succ + y j.succ) =
            (fun j : Fin 4 => x j.succ) + (fun j : Fin 4 => y j.succ) := rfl
        rw [this, map_add, map_add]
        abel
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
        have : (fun j : Fin 4 => a * x j.succ) = a • (fun j : Fin 4 => x j.succ) := rfl
        rw [this, map_smul, map_smul] }
  let w₂ : Fin 5 → F := ![d, p 0, p 1, p 2, p 3]
  have hQE : ∀ x : Fin 5 → F, weightedSumSquares F w (E x) = weightedSumSquares F w₂ x := by
    intro x
    have hmem : W.subtype (eW.symm (fun j : Fin 4 => x j.succ)) ∈ W :=
      Submodule.coe_mem _
    have h1 := hQ_orth (x 0) _ hmem
    have h2 : weightedSumSquares F w (W.subtype (eW.symm (fun j : Fin 4 => x j.succ))) =
        Q_W (eW.symm (fun j : Fin 4 => x j.succ)) := rfl
    have h3 : Q_W (eW.symm (fun j : Fin 4 => x j.succ)) =
        weightedSumSquares F p (fun j : Fin 4 => x j.succ) := by
      rw [← eW.map_app (eW.symm (fun j : Fin 4 => x j.succ))]
      simp
    have h4 : weightedSumSquares F w₂ x =
        d * x 0 ^ 2 + weightedSumSquares F p (fun j : Fin 4 => x j.succ) := by
      simp only [weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul]
      have hw₂0 : w₂ 0 = d := rfl
      have hw₂s : ∀ j : Fin 4, w₂ j.succ = p j := fun j => by fin_cases j <;> rfl
      simp only [hw₂0, hw₂s]
      ring
    change weightedSumSquares F w ((x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 4 => x j.succ))) = _
    rw [h1, h2, h3, h4]
  have hE_inj : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hφx : φ (E x) = 0 := by rw [hx, map_zero]
    have hker : φ (W.subtype (eW.symm (fun j : Fin 4 => x j.succ))) = 0 :=
      LinearMap.mem_ker.mp (Submodule.coe_mem _)
    have hφE : φ (E x) = x 0 * d := by
      change φ ((x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 4 => x j.succ))) = _
      rw [map_add, map_smul, smul_eq_mul, hφv₀, hker, add_zero]
    have hx0 : x 0 = 0 := mul_eq_zero.mp (hφE.symm.trans hφx) |>.resolve_right hd
    have hW0 : W.subtype (eW.symm (fun j : Fin 4 => x j.succ)) = 0 := by
      have hx' : (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 4 => x j.succ)) = 0 := hx
      rw [hx0, zero_smul, zero_add] at hx'
      exact hx'
    have hsub0 : eW.symm (fun j : Fin 4 => x j.succ) = 0 := Subtype.coe_injective hW0
    have htail : (fun j : Fin 4 => x j.succ) = 0 := by
      simpa using congrArg eW hsub0
    funext i
    fin_cases i
    · exact hx0
    · exact congr_fun htail 0
    · exact congr_fun htail 1
    · exact congr_fun htail 2
    · exact congr_fun htail 3
  -- Step 4: Gram-matrix determinant gives p 0 * p 1 * p 2 * p 3 = c₀ ^ 2
  let eE : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) := LinearEquiv.ofInjectiveEndo E hE_inj
  let M : Matrix (Fin 5) (Fin 5) F := LinearMap.toMatrix' eE.toLinearMap
  let M_inv : Matrix (Fin 5) (Fin 5) F := LinearMap.toMatrix' eE.symm.toLinearMap
  have hc₀ : M.det ≠ 0 := by
    have hMM : M * M_inv = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have hcomp : eE.toLinearMap.comp eE.symm.toLinearMap = LinearMap.id :=
        LinearMap.ext fun x => eE.apply_symm_apply x
      rw [hcomp, LinearMap.toMatrix'_id]
    have hdet := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact left_ne_zero_of_mul_eq_one hdet
  have hgram : M.transpose * Matrix.diagonal w * M = Matrix.diagonal w₂ := by
    have hpol : ∀ x y : Fin 5 → F,
        ∑ k : Fin 5, w k * E x k * E y k = ∑ k : Fin 5, w₂ k * x k * y k := by
      intro x y
      have hdiff := congrArg (fun f : (Fin 5 → F) → F => f (x + y) - f x - f y)
        (funext hQE)
      have hL : weightedSumSquares F w (E (x + y)) - weightedSumSquares F w (E x) -
          weightedSumSquares F w (E y) = 2 * ∑ k : Fin 5, w k * E x k * E y k := by
        rw [map_add]
        simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hR : weightedSumSquares F w₂ (x + y) - weightedSumSquares F w₂ x -
          weightedSumSquares F w₂ y = 2 * ∑ k : Fin 5, w₂ k * x k * y k := by
        simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hL, hR] at hdiff
      exact mul_left_cancel₀ (NeZero.ne (2 : F)) hdiff
    ext i j
    have hij := hpol (Pi.single i (1 : F)) (Pi.single j (1 : F))
    have hM_col : ∀ a k : Fin 5, E (Pi.single a (1 : F)) k = M k a := by
      intro a k
      have heE : (eE.toLinearMap : (Fin 5 → F) → (Fin 5 → F)) = E := rfl
      simp [M, LinearMap.toMatrix'_apply, heE]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    have hL' : (∑ x : Fin 5, (∑ x_1 : Fin 5, M x_1 i *
        (if x_1 = x then w x_1 else 0)) * M x j) =
        ∑ k : Fin 5, w k * E (Pi.single i (1 : F)) k * E (Pi.single j (1 : F)) k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun a _ ha => by simp [ha]) (fun hk => absurd (Finset.mem_univ k) hk)]
      simp only [ite_true, hM_col i k, hM_col j k]
      ring
    have hR' : (if i = j then w₂ i else 0) =
        ∑ k : Fin 5, w₂ k * (Pi.single i (1 : F) : Fin 5 → F) k *
          (Pi.single j (1 : F) : Fin 5 → F) k := by
      rw [Finset.sum_eq_single i]
      · by_cases h : i = j <;> simp [h]
      · intro k _ hk; simp [Pi.single_apply, hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hL', hR', hij]
  have hdet_gram := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_diagonal] at hdet_gram
  have hprod_w : (∏ i : Fin 5, w i) = d := rfl
  have hprod_w2 : (∏ i : Fin 5, w₂ i) = d * (p 0 * p 1 * p 2 * p 3) := by
    simp [Fin.prod_univ_five, w₂, mul_assoc]
  rw [hprod_w, hprod_w2] at hdet_gram
  set c₀ := M.det
  have hp_sq : p 0 * p 1 * p 2 * p 3 = c₀ ^ 2 := by
    have h1 : d * (c₀ ^ 2) = d * (p 0 * p 1 * p 2 * p 3) := by
      linear_combination hdet_gram
    exact (mul_left_cancel₀ hd h1).symm
  have hp_ne : p 0 * p 1 * p 2 * p 3 ≠ 0 := by
    rw [hp_sq]
    exact pow_ne_zero 2 hc₀
  have hp0 : p 0 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp1 : p 1 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp2 : p 2 ≠ 0 := fun h => hp_ne (by simp [h])
  -- Step 5: Rescale to anisotropic <1, u, v, u * v, c>
  set u := p 1 / p 0
  set v := p 2 / p 0
  set c := d / p 0
  set lam := c₀ / (p 1 * p 2)
  have hlam : lam ≠ 0 := div_ne_zero hc₀ (mul_ne_zero hp1 hp2)
  have h5 : ∀ x₁ y₁ x₂ y₂ z : F,
      x₁ ^ 2 + u * y₁ ^ 2 + v * x₂ ^ 2 + u * v * y₂ ^ 2 + c * z ^ 2 = 0 →
      x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ z = 0 := by
    intro x₁ y₁ x₂ y₂ z hz
    let vec : Fin 5 → F := ![z, x₁, y₁, x₂, y₂ / lam]
    have hQ_vec : weightedSumSquares F w (E vec) = 0 := by
      rw [hQE vec]
      simp only [weightedSumSquares_apply, Fin.sum_univ_five, smul_eq_mul, w₂, vec]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      have hid : d * (z * z) + p 0 * (x₁ * x₁) + p 1 * (y₁ * y₁) + p 2 * (x₂ * x₂) +
          p 3 * (y₂ / lam * (y₂ / lam)) =
          p 0 * (x₁ ^ 2 + u * y₁ ^ 2 + v * x₂ ^ 2 + u * v * y₂ ^ 2 + c * z ^ 2) := by
        have hp3_eq : p 3 = c₀ ^ 2 / (p 0 * p 1 * p 2) := by
          rw [← hp_sq]
          field_simp [hp0, hp1, hp2]
        rw [hp3_eq]
        simp only [u, v, c, lam]
        field_simp [hp0, hp1, hp2, hc₀]
        ring
      rw [hid, hz, mul_zero]
    have hE_vec : E vec = 0 := hQ0 _ hQ_vec
    have hvec : vec = 0 := hE_inj (hE_vec.trans (map_zero E).symm)
    have hz0 : z = 0 := by simpa [vec] using congr_fun hvec 0
    have hx1 : x₁ = 0 := by simpa [vec] using congr_fun hvec 1
    have hy1 : y₁ = 0 := by simpa [vec] using congr_fun hvec 2
    have hx2 : x₂ = 0 := by simpa [vec] using congr_fun hvec 3
    have hy2_lam : y₂ / lam = 0 := by simpa [vec] using congr_fun hvec 4
    have hy2 : y₂ = 0 := (div_eq_zero_iff.mp hy2_lam).resolve_right hlam
    exact ⟨hx1, hy1, hx2, hy2, hz0⟩
  -- Step 6: Final contradiction via key5 on <1, u, v, u * v, c, c * u>
  have h6 : 6 ∈ anisotropicDims F := by
    rw [mem_anisotropicDims_iff]
    refine ⟨weightedSumSquares F ![1, u, v, u * v, c, c * u], ?_⟩
    intro x hx
    simp only [weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul] at hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at hx
    have h5val : ![1, u, v, u * v, c, c * u] 5 = c * u := rfl
    rw [h5val] at hx
    obtain ⟨h0, h1, h2, h3, h4, h5'⟩ := key5 u v c h5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
      (by linear_combination hx)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5'
  have := hub h6
  omega
