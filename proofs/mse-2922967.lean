import OMAStatements.S_mse_2922967

/-! A Lyapunov solution with the requested norm is attained via the Sion minimax theorem.
Positive trace-one matrices are the strategies. The transpose equation is dual under
the trace pairing, and the inverse-trace identity forces the optimal value.

The mathematical minimax value is established in LDJAI's research note
A trace formula for optimal input covariance (November 26, 2026), pages 1–2,
https://github.com/LDJAI/open-math-agents/blob/71185716f56c94bf427e8dc9475406ac3267c7d6/lyapunov-trace.pdf.
This Lean formalization establishes the positive Lyapunov solver by spectral separation and
a continuous path. The original question is Ludwig's Math Stack Exchange post 2922967. -/


namespace OMA.Lyapunov

open Polynomial

private theorem aeval_intertwines {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B P : Matrix n n K) (h : A * P = P * B) (f : K[X]) :
    aeval A f * P = P * aeval B f := by
  have hp (i : ℕ) : A ^ i * P = P * B ^ i := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, add_mul, mul_add, hf, hg]
  | monomial i c =>
    simp only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mul, Matrix.mul_smul, hp]

private theorem eq_zero_of_intertwines {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B P : Matrix n n K) (h : A * P = P * B) (hc : IsCoprime A.charpoly B.charpoly) : P = 0 := by
  have hp : P * aeval B A.charpoly = 0 := by
    rw [← aeval_intertwines A B P h, Matrix.aeval_self_charpoly, zero_mul]
  obtain ⟨f, g, hg⟩ := hc
  have he := congr_arg (fun u : K[X] => P * aeval B u) hg
  change P * aeval B (f * A.charpoly + g * B.charpoly) = _ at he
  rw [mul_comm f, map_add, map_mul, map_mul, Matrix.aeval_self_charpoly B, mul_zero,
    add_zero, ← mul_assoc, hp, zero_mul, map_one, mul_one] at he
  exact he.symm

private theorem coprime_charpoly_of_no_common_root {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (h : ∀ x, x ∈ spectrum ℂ A → x ∉ spectrum ℂ B) :
    IsCoprime A.charpoly B.charpoly := by
  rw [← isRelPrime_iff_isCoprime]
  intro d hd₁ hd₂
  by_contra! hu
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root d (fun hdeg => hu (isUnit_iff_degree_eq_zero.mpr hdeg))
  exact h x (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (hx.dvd hd₁))
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (hx.dvd hd₂))

/-- Hurwitz stability makes the homogeneous real Lyapunov equation injective. -/
theorem eq_zero_of_lyapunov {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hP : A * P + P * A.transpose = 0) : P = 0 := by
  let C := Complex.ofRealHom
  let A' := C.mapMatrix A
  let P' := C.mapMatrix P
  have hh : A' * P' + P' * A'.transpose = 0 := by
    have he := congr_arg C.mapMatrix hP
    have hT : C.mapMatrix A.transpose = A'.transpose := rfl
    rw [map_add, map_mul, map_mul, map_zero, hT] at he
    exact he
  have hrel : A' * P' = P' * (-A'.transpose) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left hh
  have hdis (x : ℂ) (hx : x ∈ spectrum ℂ A') : x ∉ spectrum ℂ (-A'.transpose) := by
    intro hy
    rw [← spectrum.neg_eq, Set.mem_neg] at hy
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
      ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hy
    have hx' := hA x hx
    have hy' := hA (-x) hy
    simp only [Complex.neg_re] at hy'
    linarith
  have hz : P' = 0 := eq_zero_of_intertwines A' _ P' hrel
    (coprime_charpoly_of_no_common_root A' _ hdis)
  ext i j
  have hij := congr_fun (congr_fun hz i) j
  exact Complex.ofReal_eq_zero.mp hij

/-- With a Hurwitz coefficient, the negative Lyapunov operator has no kernel. -/
theorem lyapunov_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) :
    Function.Injective (fun P : Matrix (Fin n) (Fin n) ℝ => -(A * P) - P * A.transpose) := by
  intro P Q h
  apply sub_eq_zero.mp
  apply eq_zero_of_lyapunov A (P - Q) hA
  rw [mul_sub, sub_mul]
  have h' := congr_arg Neg.neg h
  simp only [neg_sub, sub_neg_eq_add] at h'
  rw [show A * P - A * Q + (P * A.transpose - Q * A.transpose) =
    (P * A.transpose + A * P) - (Q * A.transpose + A * Q) by abel]
  exact sub_eq_zero.mpr h'

/-- The negative Lyapunov endomorphism on the full real matrix space. -/
def lyapunov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Module.End ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toFun P := -(A * P) - P * A.transpose
  map_add' P Q := by simp only [mul_add, add_mul]; abel
  map_smul' c P := by simp [smul_sub]

@[simp] theorem lyapunov_apply {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    lyapunov A P = -(A * P) - P * A.transpose := rfl

/-- In finite dimension, the injective Lyapunov map is also surjective. -/
theorem lyapunov_bijective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) :
    Function.Bijective (lyapunov A) :=
  ⟨lyapunov_injective A hA,
    LinearMap.surjective_of_injective (f := lyapunov A) (lyapunov_injective A hA)⟩

end OMA.Lyapunov


open Matrix Set Filter
open scoped Topology Pointwise

namespace OMA.LyapunovPositivity

private theorem continuous_quad {T : Type*} [TopologicalSpace T]
    {n : ℕ} {f : T → Matrix (Fin n) (Fin n) ℝ} {v : T → Fin n → ℝ}
    (hf : Continuous f) (hv : Continuous v) :
    Continuous (fun t => v t ⬝ᵥ (f t *ᵥ v t)) := by
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i |>.comp hv).mul
    (continuous_finsetSum _ (fun j _ => (hf.matrix_elem i j).mul
      ((continuous_apply j).comp hv))))

private theorem closed_posSemidef_path {T : Type*} [TopologicalSpace T]
    {n : ℕ} {f : T → Matrix (Fin n) (Fin n) ℝ} (hf : Continuous f)
    (hs : ∀ t, (f t).IsHermitian) : IsClosed {t | (f t).PosSemidef} := by
  have he : {t | (f t).PosSemidef} = ⋂ v : Fin n → ℝ, {t | 0 ≤ v ⬝ᵥ (f t *ᵥ v)} := by
    ext t
    rw [Set.mem_ofPred_eq, Matrix.posSemidef_iff_dotProduct_mulVec]
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, star_trivial, hs t, true_and]
  rw [he]
  exact isClosed_iInter (fun v => isClosed_le continuous_const (continuous_quad hf continuous_const))

private theorem open_posDef_path {T : Type*} [TopologicalSpace T]
    {n : ℕ} {f : T → Matrix (Fin n) (Fin n) ℝ} (hf : Continuous f)
    (hs : ∀ t, (f t).IsHermitian) : IsOpen {t | (f t).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  change (f t).PosDef at ht
  let K : Set (Fin n → ℝ) := {v | ‖v‖ = 1}
  have hK : IsCompact K := by
    have he : K = Metric.sphere 0 1 := by
      ext v
      simp [K]
    rw [he]
    exact isCompact_sphere 0 1
  have c : Continuous (fun z : T × (Fin n → ℝ) => z.2 ⬝ᵥ (f z.1 *ᵥ z.2)) :=
    continuous_quad (hf.comp continuous_fst) continuous_snd
  have ev : ∀ᶠ t' in 𝓝 t, ∀ v ∈ K, 0 < v ⬝ᵥ (f t' *ᵥ v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      intro e
      simp [K, e] at hv
    exact (isOpen_lt continuous_const c).mem_nhds (by simpa [star_trivial] using ht.dotProduct_mulVec_pos hv0)
  filter_upwards [ev] with t' ht'
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hs t')
  intro v hv
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : u ∈ K := by
    change ‖‖v‖⁻¹ • v‖ = 1
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)] using inv_mul_cancel₀ hp.ne'
  have he : u ⬝ᵥ (f t' *ᵥ u) = ‖v‖⁻¹ * ‖v‖⁻¹ * (v ⬝ᵥ (f t' *ᵥ v)) := by
    simp only [u, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hv' := ht' u hu
  rw [he] at hv'
  simpa [star_trivial] using pos_of_mul_pos_right hv' (by positivity : 0 ≤ ‖v‖⁻¹ * ‖v‖⁻¹)

theorem positive_path {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    {n : ℕ} {f : T → Matrix (Fin n) (Fin n) ℝ} (hf : Continuous f)
    (hs : ∀ t, (f t).IsHermitian) (hu : ∀ t, IsUnit (f t))
    {t₀ : T} (h₀ : (f t₀).PosDef) (t : T) : (f t).PosDef := by
  let K : Set T := {t | (f t).PosDef}
  have he : K = {t | (f t).PosSemidef} := by
    ext s
    exact ⟨Matrix.PosDef.posSemidef, fun h => h.posDef_iff_isUnit.mpr (hu s)⟩
  have hc : IsClopen K := ⟨he ▸ closed_posSemidef_path hf hs, open_posDef_path hf hs⟩
  have hf' : (Set.univ : Set T) ⊆ K :=
    isPreconnected_univ.subset_isClopen hc ⟨t₀, Set.mem_univ t₀, h₀⟩
  exact hf' (Set.mem_univ t)


private def pathA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - t) • A - t • (1 : Matrix (Fin n) (Fin n) ℝ)

private theorem continuous_pathA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (pathA A) := by
  unfold pathA
  fun_prop

private theorem hurwitz_path {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ μ ∈ spectrum ℂ ((pathA A t).map Complex.ofReal), μ.re < 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let B := A.map Complex.ofReal
  have hp : (pathA A t).map Complex.ofReal =
      algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (-(t : ℂ)) + (1 - (t : ℂ)) • B := by
    ext i j
    classical
    simp [B, pathA, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, sub_eq_add_neg, mul_comm,
      Complex.ofReal_mul]
    by_cases h : i = j <;> simp [h, add_comm]
  intro μ hμ
  rw [hp, ← spectrum.singleton_add_eq] at hμ
  rcases Set.mem_add.mp hμ with ⟨a, ha, b, hb, hab⟩
  rw [Set.mem_singleton_iff.mp ha] at hab
  by_cases ht1 : t = 1
  · subst t
    simp only [Complex.ofReal_one, sub_self, zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hb
    rw [← hab, hb]
    norm_num
  · have hc : 1 - (t : ℂ) ≠ 0 := by
      intro he
      exact ht1 (by exact_mod_cast (sub_eq_zero.mp he).symm)
    let k := Units.mk0 (1 - (t : ℂ)) hc
    have hks : spectrum ℂ ((1 - (t : ℂ)) • B) = (1 - (t : ℂ)) • spectrum ℂ B := by
      exact spectrum.unit_smul_eq_smul B k
    rw [hks] at hb
    obtain ⟨ν, hν, hνb⟩ := Set.mem_smul_set.mp hb
    rw [← hab, ← hνb]
    have hν' := hA ν hν
    have ht' : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
    have hm := mul_neg_of_pos_of_neg ht' hν'
    change ((-(t : ℂ)) + (1 - (t : ℂ)) * ν).re < 0
    simp [Complex.mul_re]
    linarith [ht.1]

private def flat {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ :=
  fun ij => P ij.1 ij.2

private def unflat {n : ℕ} (P : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P (i,j)

private theorem flat_inj {n : ℕ} : Function.Injective (@flat n) := by
  intro P Q e
  ext i j
  exact congr_fun e (i,j)

private theorem unflat_inj {n : ℕ} : Function.Injective (@unflat n) := by
  intro P Q e
  funext ij
  exact congr_fun (congr_fun e ij.1) ij.2

private def op {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun P := flat (OMA.Lyapunov.lyapunov A (unflat P))
  map_add' P Q := by
    change flat (OMA.Lyapunov.lyapunov A (unflat P + unflat Q)) = _
    simp only [map_add]
    rfl
  map_smul' c P := by
    change flat (OMA.Lyapunov.lyapunov A (c • unflat P)) = _
    simp only [map_smul]
    rfl

private def opMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := LinearMap.toMatrix' (op A)

private theorem opMatrix_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Fin n × Fin n → ℝ) : opMatrix A *ᵥ P = flat (OMA.Lyapunov.lyapunov A (unflat P)) := by
  change (Matrix.toLin' (opMatrix A)) P = _
  rw [opMatrix, Matrix.toLin'_toMatrix']
  rfl

private theorem continuous_opMatrix {n : ℕ} :
    Continuous (@opMatrix n) := by
  apply continuous_matrix
  intro i j
  simp only [opMatrix, LinearMap.toMatrix'_apply]
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℝ =>
    (- (A * unflat (Pi.single j 1)) - unflat (Pi.single j 1) * A.transpose) i.1 i.2)
  exact (continuous_id.matrix_mul continuous_const |>.neg.sub
    (continuous_const.matrix_mul continuous_id.matrix_transpose)).matrix_elem _ _

private theorem opMatrix_unit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) : IsUnit (opMatrix A) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro P Q e
  rw [opMatrix_apply, opMatrix_apply] at e
  exact unflat_inj ((OMA.Lyapunov.lyapunov_bijective A hA).injective (flat_inj e))

private noncomputable def solution {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  unflat ((opMatrix A)⁻¹ *ᵥ flat X)

private theorem solution_eq {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) :
    OMA.Lyapunov.lyapunov A (solution A X) = X := by
  apply flat_inj
  change flat (OMA.Lyapunov.lyapunov A (unflat ((opMatrix A)⁻¹ *ᵥ flat X))) = _
  rw [← opMatrix_apply, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (opMatrix_unit A hA)),
    Matrix.one_mulVec]

private theorem continuous_solution {T : Type*} [TopologicalSpace T] {n : ℕ}
    {f : T → Matrix (Fin n) (Fin n) ℝ} (hf : Continuous f)
    (h : ∀ t, ∀ μ ∈ spectrum ℂ ((f t).map Complex.ofReal), μ.re < 0)
    (X : Matrix (Fin n) (Fin n) ℝ) : Continuous (fun t => solution (f t) X) := by
  have cM := continuous_opMatrix.comp hf
  have cInv : Continuous (fun t => (opMatrix (f t))⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (opMatrix_unit (f t) (h t))
    have c : ContinuousAt (Ring.inverse : ℝ → ℝ) (opMatrix (f t)).det := by
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_id.inv₀ hu.ne_zero
    have hInv : ContinuousAt (Inv.inv : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ →
        Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (opMatrix (f t)) :=
      continuousAt_matrix_inv (opMatrix (f t)) c
    exact ContinuousAt.comp' (f := fun s : T => opMatrix (f s)) hInv cM.continuousAt
  apply continuous_matrix
  intro i j
  change Continuous (fun t => ((opMatrix (f t))⁻¹ *ᵥ flat X) (i,j))
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ (fun k _ => (cInv.matrix_elem (i,j) k).mul continuous_const)


private theorem hermitian_solution {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hX : X.IsHermitian) : (solution A X).IsHermitian := by
  let P := solution A X
  have h := solution_eq A X hA
  change OMA.Lyapunov.lyapunov A P = X at h
  have ht := congrArg Matrix.transpose h
  have hXt : X.transpose = X := by simpa using hX.eq
  rw [hXt] at ht
  simp only [OMA.Lyapunov.lyapunov_apply, Matrix.transpose_sub, Matrix.transpose_neg,
    Matrix.transpose_mul, Matrix.transpose_transpose] at ht
  have ht' : OMA.Lyapunov.lyapunov A P.transpose = X := by
    rw [← ht, OMA.Lyapunov.lyapunov_apply]
    abel
  have he := (OMA.Lyapunov.lyapunov_bijective A hA).injective (ht'.trans h.symm)
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using he

private theorem isUnit_of_lyapunov_posDef {n : ℕ} {A P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) (hX : X.PosDef) (hEq : OMA.Lyapunov.lyapunov A P = X) :
    IsUnit P := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  apply sub_eq_zero.mp
  by_contra hne
  let w := u - v
  have hz : P *ᵥ w = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  have ht : P.transpose = P := by simpa using hP.eq
  have hz' : w ᵥ* P = 0 := by rw [← ht, Matrix.vecMul_transpose, hz]
  have hn : 0 < w ⬝ᵥ (X *ᵥ w) := by
    simpa only [star_trivial] using hX.dotProduct_mulVec_pos hne
  have he : w ⬝ᵥ (X *ᵥ w) = 0 := by
    rw [← hEq, OMA.Lyapunov.lyapunov_apply, Matrix.sub_mulVec,
      Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg,
      ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, dotProduct_zero,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hz', zero_dotProduct]
    simp
  rw [he] at hn
  exact (lt_irrefl 0 hn)

private theorem posDef_solution {n : ℕ} (hn : 0 < n)
    (A X : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hX : X.PosDef) : (solution A X).PosDef := by
  let J := Set.Icc (0 : ℝ) 1
  let t₀ : J := ⟨1, by simp [J]⟩
  let t₁ : J := ⟨0, by simp [J]⟩
  let a : J → Matrix (Fin n) (Fin n) ℝ := fun t => pathA A t
  let p : J → Matrix (Fin n) (Fin n) ℝ := fun t => solution (a t) X
  have ha (t : J) : ∀ μ ∈ spectrum ℂ ((a t).map Complex.ofReal), μ.re < 0 :=
    hurwitz_path hn hA t.2
  have hs (t : J) : (p t).IsHermitian := hermitian_solution (a t) X (ha t) hX.isHermitian
  have hu (t : J) : IsUnit (p t) := isUnit_of_lyapunov_posDef (hs t) hX (solution_eq (a t) X (ha t))
  have hbase : p t₀ = (1 / 2 : ℝ) • X := by
    apply (OMA.Lyapunov.lyapunov_bijective (a t₀) (ha t₀)).injective
    rw [show OMA.Lyapunov.lyapunov (a t₀) (p t₀) = X from solution_eq (a t₀) X (ha t₀)]
    have he : a t₀ = -1 := by simp [a, t₀, pathA]
    rw [he, OMA.Lyapunov.lyapunov_apply]
    ext i j
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.mul_neg, Matrix.mul_one, sub_neg_eq_add,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp : Continuous p := continuous_solution ((continuous_pathA A).comp continuous_subtype_val) ha X
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hout := positive_path hp hs hu (hbase ▸ hX.smul (by norm_num : (0 : ℝ) < 1 / 2)) t₁
  simpa [p, a, t₁, pathA] using hout

private theorem posSemidef_solution {n : ℕ} (hn : 0 < n)
    (A X : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hX : X.PosSemidef) : (solution A X).PosSemidef := by
  let Y : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => X + t • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hY : Continuous Y := by unfold Y; fun_prop
  have hYs (t : ℝ) : (Y t).IsHermitian := by
    have hXt : X.transpose = X := by simpa using hX.isHermitian.eq
    have ht : (Y t).transpose = Y t := by simp [Y, Matrix.transpose_add, hXt]
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using ht
  have hP : Continuous (fun t => solution A (Y t)) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun t => ((opMatrix A)⁻¹ *ᵥ flat (Y t)) (i,j))
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (hY.matrix_elem k.1 k.2))
  have hc := closed_posSemidef_path hP (fun t => hermitian_solution A (Y t) hA (hYs t))
  have hsub : Set.Ioi (0 : ℝ) ⊆ {t : ℝ | (solution A (Y t)).PosSemidef} := by
    intro t ht
    have ht' : 0 < t := ht
    have hpos : (Y t).PosDef := by
      have hOne : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
      have hs := (hOne.smul ht').add_posSemidef hX
      simpa [Y, add_comm] using hs
    exact (posDef_solution hn A (Y t) hA hpos).posSemidef
  have hzero := (closure_minimal hsub hc) (show (0 : ℝ) ∈ closure (Set.Ioi 0) by simp [closure_Ioi])
  simpa [Y] using hzero

/-- A positive definite forcing term gives a positive definite Lyapunov solution. -/
theorem lyapunov_posDef {n : ℕ} (hn : 0 < n)
    (A X P : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hX : X.PosDef) (hP : OMA.Lyapunov.lyapunov A P = X) : P.PosDef := by
  have he := (OMA.Lyapunov.lyapunov_bijective A hA).injective ((solution_eq A X hA).trans hP.symm)
  exact he ▸ posDef_solution hn A X hA hX

/-- For a Hurwitz matrix, positive semidefinite Lyapunov right-hand sides have
positive semidefinite solutions. -/
theorem lyapunov_posSemidef {n : ℕ} (hn : 0 < n)
    (A X P : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0)
    (hX : X.PosSemidef) (hP : OMA.Lyapunov.lyapunov A P = X) : P.PosSemidef := by
  have he := (OMA.Lyapunov.lyapunov_bijective A hA).injective ((solution_eq A X hA).trans hP.symm)
  exact he ▸ posSemidef_solution hn A X hA hX

end OMA.LyapunovPositivity


namespace OMA.LyapunovOptimum

/-- A continuous bilinear payoff on a compact convex strategy space has a saddle point. -/
theorem exists_bilinear_saddle {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [FiniteDimensional ℝ E] {D : Set E} (hne : D.Nonempty) (hconv : Convex ℝ D)
    (hcompact : IsCompact D) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    ∃ a ∈ D, ∃ b ∈ D, ∀ x ∈ D, ∀ y ∈ D, B a y ≤ B x b := by
  exact Sion.exists_isSaddlePointOn' (f := fun x y => B x y)
    hne hcompact
    (fun y _ => (B.flip y).continuous_of_finiteDimensional.continuousOn.lowerSemicontinuousOn)
    (fun y _ => ((B.flip y).convexOn hconv).quasiconvexOn)
    hconv hcompact
    (fun x _ => (B x).continuous_of_finiteDimensional.continuousOn.upperSemicontinuousOn)
    (fun x _ => ((B x).concaveOn hconv).quasiconcaveOn)
    hconv hne

end OMA.LyapunovOptimum


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

namespace OMA.LyapunovOptimum

private abbrev Mat (n : Type*) := Matrix n n ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Contracting the Lyapunov equation against the inverse solution recovers the trace of A. -/
theorem inverse_trace_identity {A P X : (Mat n)}
    (hP : P.PosDef) (h : -(A * P + P * Aᵀ) = X) :
    (P⁻¹ * X).trace = -2 * A.trace := by
  rw [← h, mul_neg, trace_neg, mul_add, trace_add]
  have hU : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have h₁ : (P⁻¹ * (A * P)).trace = A.trace := by
    rw [Matrix.trace_mul_cycle' _ _ _, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU]
    simp
  have h₂ : (P⁻¹ * (P * Aᵀ)).trace = A.trace := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU]
    simp
  rw [h₁,h₂]
  ring

/-- The trace pairing interchanges the two transpose-related Lyapunov operators. -/
theorem trace_pairing {A P Y : (Mat n)} :
    (Y * (-(A * P + P * Aᵀ))).trace =
      ((-(Aᵀ * Y + Y * A)) * P).trace := by
  simp only [mul_neg, neg_mul, trace_neg, mul_add, add_mul, trace_add]
  congr 1
  have h₁ : (Y * (A * P)).trace = ((Y * A) * P).trace := by rw [Matrix.mul_assoc]
  have h₂ : (Y * (P * Aᵀ)).trace = ((Aᵀ * Y) * P).trace := by
    rw [← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle _ _ _
  rw [h₁, h₂, add_comm]

private theorem trace_diagonal_product (v : n → ℝ) (A : (Mat n)) :
    (diagonal v * A).trace = ∑ i, v i * A i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem trace_mul_conjugate (B C : (Mat n)) (U : Matrix.unitaryGroup n ℝ) :
    (B * ((U : (Mat n)) * C * (star U : (Mat n)))).trace =
      (C * ((star U : (Mat n)) * B * (U : (Mat n)))).trace := by
  calc
    _ = (((B * (U : (Mat n))) * C) * (star U : (Mat n))).trace := by simp only [Matrix.mul_assoc]
    _ = (((star U : (Mat n)) * (B * (U : (Mat n)))) * C).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [Matrix.trace_mul_comm (((star U : (Mat n)) * (B * (U : (Mat n))))) C]
      simp only [Matrix.mul_assoc]

/-- A positive definite matrix pairs positively with a nonzero positive semidefinite one. -/
theorem trace_mul_pos {A B : (Mat n)} (hA : A.PosDef) (hB : B.PosSemidef) (hB0 : B ≠ 0) :
    0 < (A * B).trace := by
  let U := hB.isHermitian.eigenvectorUnitary
  let v := hB.isHermitian.eigenvalues
  have hDiag : B = (U : (Mat n)) * diagonal v * (star U : (Mat n)) := by
    simpa [U, v, Unitary.conjStarAlgAut_apply] using hB.isHermitian.spectral_theorem
  have hA' : ((star U : (Mat n)) * A * (U : (Mat n))).PosDef := by
    change ((U : (Mat n))ᴴ * A * (U : (Mat n))).PosDef
    exact hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (Unitary.isUnit_coe (U := U)))
  have hv : ∀ i, 0 ≤ v i := hB.eigenvalues_nonneg
  have hv0 : ∃ i, 0 < v i := by
    by_contra! h
    apply hB0
    rw [hDiag, show v = 0 from funext (fun i => le_antisymm (h i) (hv i)) ]
    simp [Pi.zero_def]
  rw [hDiag, trace_mul_conjugate, trace_diagonal_product]
  obtain ⟨i, hi⟩ := hv0
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hv j) (hA'.diag_pos (i := j)).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (hA'.diag_pos (i := i))⟩

/-- The Euclidean operator norm of a real Hermitian matrix is the maximum absolute eigenvalue. -/
theorem norm_eq_eigenvalues {A : (Mat n)} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  let U := hA.eigenvectorUnitary
  change ‖(U : (Mat n)) * diagonal hA.eigenvalues * (star U : (Mat n))‖ = _
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary _ (star U), CStarRing.norm_coe_unitary_mul U,
    Matrix.l2_opNorm_diagonal]

theorem norm_le_trace_of_psd {A : (Mat n)} (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace := by
  rw [norm_eq_eigenvalues hA.isHermitian, Matrix.IsHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i))).mpr
    (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
      exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i))

omit [DecidableEq n] in
theorem isClosed_psd : IsClosed {P : (Mat n) | P.PosSemidef} := by
  have hsym : IsClosed {P : (Mat n) | P.IsHermitian} :=
    isClosed_eq (by fun_prop : Continuous fun P : (Mat n) => Pᴴ) continuous_id
  have hnonneg (x : n → ℝ) :
      IsClosed {P : (Mat n) | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have heq : {P : (Mat n) | P.PosSemidef} =
      {P : (Mat n) | P.IsHermitian} ∩ ⋂ x : n → ℝ, {P : (Mat n) | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp [Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [heq]
  exact hsym.inter (isClosed_iInter hnonneg)

omit [Fintype n] [DecidableEq n] in
theorem convex_psd : Convex ℝ {P : (Mat n) | P.PosSemidef} := by
  intro X hX Y hY a b ha hb _
  exact (hX.smul ha).add (hY.smul hb)

/-- Trace-one positive matrices in the real matrix space. -/
def density (n : Type*) [Fintype n] : Set (Matrix n n ℝ) :=
  {P | P.PosSemidef ∧ P.trace = 1}

omit [DecidableEq n] in
theorem convex_density : Convex ℝ (density n) := by
  intro X hX Y hY a b ha hb hab
  exact ⟨(hX.1.smul ha).add (hY.1.smul hb), by simpa [Matrix.trace_add, Matrix.trace_smul,
    hX.2, hY.2] using hab⟩

theorem compact_density : IsCompact (density n) := by
  have hclosed : IsClosed (density n) := by
    exact isClosed_psd.inter (isClosed_eq (by fun_prop : Continuous fun M : (Mat n) => M.trace) continuous_const)
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : (Mat n)) 1) hclosed
  intro P hP
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_trace_of_psd hP.1).trans_eq hP.2

private theorem apply_unitary_diag_eq {A : (Mat n)} (hA : A.IsHermitian) :
    Unitary.conjStarAlgAut ℝ (Mat n) hA.eigenvectorUnitary (diagonal hA.eigenvalues) = A := by
  simpa using hA.spectral_theorem.symm

/-- The diagonal weights of a density matrix in an orthonormal basis sum to one. -/
private theorem trace_change_basis (X : (Mat n)) (U : unitary (Mat n)) :
    ((star U : (Mat n)) * X * (U : (Mat n))).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]

private theorem inverse_diagonal_form {A : (Mat n)} (hA : A.PosDef) :
    A⁻¹ = Unitary.conjStarAlgAut ℝ (Mat n) hA.isHermitian.eigenvectorUnitary
      (diagonal fun i => (hA.isHermitian.eigenvalues i)⁻¹) := by
  let e := Unitary.conjStarAlgAut ℝ (Mat n) hA.isHermitian.eigenvectorUnitary
  apply Matrix.inv_eq_left_inv
  change e (diagonal fun i => (hA.isHermitian.eigenvalues i)⁻¹) * A = 1
  conv_lhs => arg 2; rw [← apply_unitary_diag_eq hA.isHermitian]
  change e (diagonal fun i => (hA.isHermitian.eigenvalues i)⁻¹) *
    e (diagonal hA.isHermitian.eigenvalues) = 1
  rw [← map_mul, diagonal_mul_diagonal]
  have heq : (fun i => (hA.isHermitian.eigenvalues i)⁻¹ * hA.isHermitian.eigenvalues i) =
      (fun _ => (1 : ℝ)) := funext (fun i => inv_mul_cancel₀ (hA.eigenvalues_pos i).ne')
  rw [heq, diagonal_one, map_one]

private theorem inverse_trace_as_sum {A : (Mat n)} (hA : A.PosDef) (X : (Mat n)) :
    (A⁻¹ * X).trace =
      ∑ i, (hA.isHermitian.eigenvalues i)⁻¹ *
        ((star hA.isHermitian.eigenvectorUnitary : (Mat n)) * X *
          (hA.isHermitian.eigenvectorUnitary : (Mat n))) i i := by
  rw [inverse_diagonal_form hA, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    trace_mul_conjugate, trace_diagonal_product]

omit [DecidableEq n] in
private theorem trace_weighted_strict (a b w : n → ℝ)
    (hab : ∀ i, a i < b i) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    (∑ i, a i * w i) < ∑ i, b i * w i := by
  have hpos : ∃ i, 0 < w i := by
    by_contra! h
    have hz : w = 0 := funext (fun i => le_antisymm (h i) (hw i))
    simp [hz] at hs
  obtain ⟨i, hi⟩ := hpos
  exact Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_right (hab j).le (hw j))
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_right (hab i) hi⟩

theorem inverse_trace_lt_of_eigen_gt {A X : (Mat n)} (hA : A.PosDef) (hX : X ∈ density n)
    {c : ℝ} (hc : 0 < c) (h : ∀ i, c < hA.isHermitian.eigenvalues i) :
    (A⁻¹ * X).trace < c⁻¹ := by
  let U := hA.isHermitian.eigenvectorUnitary
  let W := (star U : (Mat n)) * X * (U : (Mat n))
  have hW : W.PosSemidef := hX.1.conjTranspose_mul_mul_same (U : (Mat n))
  have hs : ∑ i, W i i = 1 := by
    change W.trace = 1
    rw [trace_change_basis, hX.2]
  rw [inverse_trace_as_sum hA]
  have hb (i : n) : (hA.isHermitian.eigenvalues i)⁻¹ < c⁻¹ :=
    by simpa [one_div] using one_div_lt_one_div_of_lt hc (h i)
  calc
    _ < ∑ i, c⁻¹ * W i i := trace_weighted_strict _ _ _ hb
      (fun i => hW.diag_nonneg (i := i)) hs
    _ = c⁻¹ := by rw [← Finset.mul_sum, hs, mul_one]

theorem inverse_trace_gt_of_eigen_lt {A X : (Mat n)} (hA : A.PosDef) (hX : X ∈ density n)
    {c : ℝ} (h : ∀ i, hA.isHermitian.eigenvalues i < c) :
    c⁻¹ < (A⁻¹ * X).trace := by
  let U := hA.isHermitian.eigenvectorUnitary
  let W := (star U : (Mat n)) * X * (U : (Mat n))
  have hW : W.PosSemidef := hX.1.conjTranspose_mul_mul_same (U : (Mat n))
  have hs : ∑ i, W i i = 1 := by
    change W.trace = 1
    rw [trace_change_basis, hX.2]
  rw [inverse_trace_as_sum hA]
  have hb (i : n) : c⁻¹ < (hA.isHermitian.eigenvalues i)⁻¹ :=
    by simpa [one_div] using one_div_lt_one_div_of_lt (hA.eigenvalues_pos i) (h i)
  calc
    _ = ∑ i, c⁻¹ * W i i := by rw [← Finset.mul_sum, hs, mul_one]
    _ < _ := trace_weighted_strict _ _ _ hb (fun i => hW.diag_nonneg (i := i)) hs

omit [Fintype n] in
private theorem diag_const (c : ℝ) : diagonal (fun _ : n => c) = c • (1 : (Mat n)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

set_option maxHeartbeats 800000 in
/-- Subtracting a scalar shifts every eigenvalue by that scalar. -/
theorem eigen_gt_of_posDef_sub_scalar {A : (Mat n)} (hA : A.IsHermitian) {c : ℝ}
    (h : (A - c • (1 : (Mat n))).PosDef) (i : n) : c < hA.eigenvalues i := by
  let U := hA.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℝ (Mat n) U
  have heq : e (diagonal fun j => hA.eigenvalues j - c) = A - c • (1 : (Mat n)) := by
    have hdiag := (Matrix.diagonal_sub hA.eigenvalues (fun _ => c)).symm
    have ha : e (diagonal hA.eigenvalues) = A := apply_unitary_diag_eq hA
    rw [hdiag, map_sub, ha, diag_const, map_smul, map_one]
  rw [← heq] at h
  change ((U : (Mat n)) * diagonal (fun j => hA.eigenvalues j - c) * (star U : (Mat n))).PosDef at h
  have hd := (Unitary.isUnit_coe (U := U)).posDef_star_right_conjugate_iff.mp h
  have hi := (Matrix.posDef_diagonal_iff.mp hd) i
  linarith

set_option maxHeartbeats 800000 in
theorem norm_le_of_scalar_sub_psd {A : (Mat n)} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : (c • (1 : (Mat n)) - A).PosSemidef) : ‖A‖ ≤ c := by
  let U := hA.isHermitian.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℝ (Mat n) U
  have heq : e (diagonal fun j => c - hA.isHermitian.eigenvalues j) = c • (1 : (Mat n)) - A := by
    have hdiag := (Matrix.diagonal_sub (fun _ => c) hA.isHermitian.eigenvalues).symm
    have ha : e (diagonal hA.isHermitian.eigenvalues) = A := apply_unitary_diag_eq hA.isHermitian
    rw [hdiag, map_sub, ha, diag_const, map_smul, map_one]
  rw [← heq] at h
  change ((U : (Mat n)) * diagonal (fun j => c - hA.isHermitian.eigenvalues j) * (star U : (Mat n))).PosSemidef at h
  have hd := (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff.mp h
  rw [norm_eq_eigenvalues hA.isHermitian]
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact sub_nonneg.mp (Matrix.posSemidef_diagonal_iff.mp hd i)

end OMA.LyapunovOptimum


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

namespace OMA.LyapunovOptimum

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem dot_sq_pos {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  simpa using (dotProduct_star_self_pos_iff (v := v)).mpr hv

private noncomputable def probe (v : n → ℝ) : (Mat n) :=
  (v ⬝ᵥ v)⁻¹ • vecMulVec v v

omit [DecidableEq n] in
theorem probe_density {v : n → ℝ} (hv : v ≠ 0) : probe v ∈ density n := by
  have h₀ : (vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  refine ⟨h₀.smul (inv_nonneg.mpr (dot_sq_pos hv).le), ?_⟩
  rw [probe, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul,
    inv_mul_cancel₀ (dot_sq_pos hv).ne']

omit [DecidableEq n] in
private theorem trace_probe (A : (Mat n)) (v : n → ℝ) :
    (A * probe v).trace = (v ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ v) := by
  have hcol : A * replicateCol Unit v = replicateCol Unit (A *ᵥ v) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [probe, Matrix.mul_smul, Matrix.trace_smul, Matrix.vecMulVec_eq Unit,
    ← Matrix.mul_assoc, hcol, Matrix.trace_replicateCol_mul_replicateRow,
    smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [dotProduct_comm (A *ᵥ v)]

omit [Fintype n] in
private theorem isHermitian_real_smul_one (c : ℝ) : (c • (1 : (Mat n))).IsHermitian :=
  Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])

theorem psd_from_trace_upper {P : (Mat n)} (hP : P.IsHermitian) {c : ℝ}
    (h : ∀ X ∈ density n, (P * X).trace ≤ c) : (c • (1 : (Mat n)) - P).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((isHermitian_real_smul_one c).sub hP)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have ht := h (probe v) (probe_density hv)
  rw [trace_probe, div_le_iff₀ (dot_sq_pos hv)] at ht
  have heq : star v = v := by simp
  rw [heq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  linarith

theorem posDef_from_trace_lower {P : (Mat n)} (hP : P.IsHermitian) {c : ℝ}
    (h : ∀ X ∈ density n, c < (P * X).trace) : (P - c • (1 : (Mat n))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hP.sub (isHermitian_real_smul_one c))
  intro v hv
  have ht := h (probe v) (probe_density hv)
  rw [trace_probe, lt_div_iff₀ (dot_sq_pos hv)] at ht
  have heq : star v = v := by simp
  rw [heq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  linarith

end OMA.LyapunovOptimum

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

namespace OMA.LyapunovOptimum

open OMA.Lyapunov OMA.LyapunovPositivity

private theorem hurwitz_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) :
    ∀ μ ∈ spectrum ℂ (Aᵀ.map Complex.ofReal), μ.re < 0 := by
  intro μ hμ
  change μ ∈ spectrum ℂ (A.map Complex.ofReal)ᵀ at hμ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  exact hA μ hμ

private theorem attainable_trace_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0) :
    ∃ X P : Matrix (Fin n) (Fin n) ℝ, X ∈ density (Fin n) ∧ P.PosSemidef ∧
      -(A * P + P * Aᵀ) = X ∧ ‖P‖ = (-2 * A.trace)⁻¹ := by
  let Mat := Matrix (Fin n) (Fin n) ℝ
  let D := density (Fin n)
  let E := LinearEquiv.ofBijective (lyapunov A) (lyapunov_bijective A hA)
  let F := LinearEquiv.ofBijective (lyapunov Aᵀ)
    (lyapunov_bijective Aᵀ (hurwitz_transpose A hA))
  let T := E.symm
  let U := F.symm
  have hT (X : Mat) : lyapunov A (T X) = X := E.apply_symm_apply X
  have hU (Y : Mat) : lyapunov Aᵀ (U Y) = Y := F.apply_symm_apply Y
  have hT' (X : Mat) : -(A * T X + T X * Aᵀ) = X := by
    simpa [lyapunov_apply, neg_add, sub_eq_add_neg, add_comm] using hT X
  have hU' (Y : Mat) : -(Aᵀ * U Y + U Y * A) = Y := by
    simpa [lyapunov_apply, neg_add, sub_eq_add_neg, add_comm] using hU Y
  have hPair (X Y : Mat) : (T X * Y).trace = (U Y * X).trace := by
    have hh := trace_pairing (A := A) (P := T X) (Y := U Y)
    rw [hT', hU'] at hh
    rw [Matrix.trace_mul_comm (T X) Y]
    exact hh.symm

  let X₀ : Mat := (n : ℝ)⁻¹ • (1 : Mat)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hX₀pos : X₀.PosDef := Matrix.PosDef.one.smul (inv_pos.mpr hnR)
  have hX₀ : X₀ ∈ D := by
    refine ⟨hX₀pos.posSemidef, ?_⟩
    change (((n : ℝ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ)).trace = 1
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    exact inv_mul_cancel₀ hnR.ne' 
  have hP₀pos : (T X₀).PosDef := lyapunov_posDef hn A X₀ (T X₀) hA hX₀pos (hT X₀)
  have hd : 0 < -2 * A.trace := by
    rw [← inverse_trace_identity hP₀pos (hT' X₀)]
    have ht : X₀.trace = 1 := hX₀.2
    exact trace_mul_pos hP₀pos.inv hX₀.1 (by intro h; simp [h] at ht)
  let c := (-2 * A.trace)⁻¹
  have hc : 0 < c := inv_pos.mpr hd

  let pay : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun X Y => (T X * Y).trace)
    (by simp [add_mul, trace_add])
    (by simp [trace_smul])
    (by simp [mul_add, trace_add])
    (by simp [trace_smul])
  obtain ⟨X, hX, Y, hY, hs⟩ :=
    exists_bilinear_saddle (show D.Nonempty from ⟨X₀, hX₀⟩)
      convex_density compact_density pay
  have hYpos : (U Y).PosSemidef :=
    lyapunov_posSemidef hn Aᵀ Y (U Y) (hurwitz_transpose A hA) hY.1 (hU Y)
  obtain ⟨V, hV, hVle⟩ : ∃ V ∈ D, (U Y * V).trace ≤ c := by
    by_contra! h
    have hGt := posDef_from_trace_lower hYpos.isHermitian h
    have hZ : (U Y).PosDef := by
      simpa using hGt.add (Matrix.PosDef.one.smul hc)
    have hEigs := eigen_gt_of_posDef_sub_scalar hZ.isHermitian hGt
    have hh := inverse_trace_lt_of_eigen_gt hZ hY hc hEigs
    have hL : - (Aᵀ * U Y + U Y * Aᵀᵀ) = Y := by simpa using hU' Y
    rw [inverse_trace_identity hZ hL, Matrix.trace_transpose] at hh
    simp [c] at hh

  have hP : (T X).PosSemidef := lyapunov_posSemidef hn A X (T X) hA hX.1 (hT X)
  have hupper (Z : Mat) (hZ : Z ∈ D) : (T X * Z).trace ≤ c := by
    have h₁ : (T X * Z).trace ≤ (T V * Y).trace := hs V hV Z hZ
    exact h₁.trans ((hPair V Y).symm ▸ hVle)
  have hle : ‖T X‖ ≤ c := norm_le_of_scalar_sub_psd hP hc.le
    (psd_from_trace_upper hP.isHermitian hupper)

  have hpos_lower (V : Mat) (hV : V ∈ D) (hVpos : V.PosDef) : c ≤ ‖T V‖ := by
    by_contra! hsmall
    have hVP : (T V).PosDef := lyapunov_posDef hn A V (T V) hA hVpos (hT V)
    have hev (i : Fin n) : hVP.isHermitian.eigenvalues i < c := by
      have hcoord := norm_le_pi_norm hVP.isHermitian.eigenvalues i
      rw [← norm_eq_eigenvalues hVP.isHermitian] at hcoord
      exact (Real.le_norm_self _).trans_lt (hcoord.trans_lt hsmall)
    have hh := inverse_trace_gt_of_eigen_lt hVP hV hev
    rw [inverse_trace_identity hVP (hT' V)] at hh
    simp [c] at hh

  have hlower : c ≤ ‖T X‖ := by
    by_contra! hsmall
    let e : ℝ := min (1/2) ((c - ‖T X‖) / (2 * (‖T X₀‖ + 1)))
    have he : 0 < e := lt_min (by norm_num) (div_pos (sub_pos.mpr hsmall) (by positivity))
    have heOn : e ≤ 1 / 2 := min_le_left _ _
    have heBd : e * (‖T X₀‖ + 1) ≤ (c - ‖T X‖) / 2 := by
      have he' : e ≤ (c - ‖T X‖) / (2 * (‖T X₀‖ + 1)) := min_le_right _ _
      have hD : 0 < 2 * (‖T X₀‖ + 1) := by positivity
      have hh := (le_div_iff₀ hD).mp he'
      linarith only [show e * (2 * (‖T X₀‖ + 1)) = 2 * (e * (‖T X₀‖ + 1)) by ring, hh]
    have hone : 0 ≤ 1 - e := by linarith
    let W : Mat := (1-e) • X + e • X₀
    have hW : W ∈ D := convex_density hX hX₀ hone he.le (by ring)
    have hWpos : W.PosDef := Matrix.PosDef.posSemidef_add (hX.1.smul hone) (hX₀pos.smul he)
    apply (not_lt_of_ge (hpos_lower W hW hWpos))
    have hNorm : ‖T W‖ ≤ (1-e) * ‖T X‖ + e * ‖T X₀‖ := by
      rw [show T W = (1-e) • T X + e • T X₀ by simp [W]]
      calc
        _ ≤ ‖(1-e) • T X‖ + ‖e • T X₀‖ := norm_add_le _ _
        _ = _ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hone,
            abs_of_pos he]
    nlinarith [mul_nonneg he.le (norm_nonneg (T X))]
  exact ⟨X, T X, hX, hP, hT' X, le_antisymm hle hlower⟩

end OMA.LyapunovOptimum

theorem OMA.solution : type_of% @OMA.S_mse_2922967.main := by
  intro n hn A hA
  obtain ⟨X, P, hX, hp, he, ht⟩ :=
    OMA.LyapunovOptimum.attainable_trace_bound hn A hA
  refine ⟨X, P, hX.1, hX.2, hp, ?_, ?_⟩
  · exact neg_injective (by simpa using he)
  · rw [one_div, ← ht]
    rfl
