import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1

-- Order six in the Erdős 723 reduction.
-- Credit: @avivorly

open Matrix Finset

namespace OrderSix

variable {n : ℕ}

def incidenceMatrix (incidence : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if incidence i j = true then 1 else 0

lemma incidence_gram (incidence : Fin n → Fin n → Bool) (size : ℕ)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = size)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    incidenceMatrix incidence * (incidenceMatrix incidence)ᵀ =
      Matrix.of (fun i j => if i = j then (size : ℤ) else 1) := by
  ext i j
  rw [Matrix.mul_apply]
  change ∑ k, (if incidence i k = true then (1 : ℤ) else 0) *
    (if incidence j k = true then 1 else 0) = (if i = j then (size : ℤ) else 1)
  calc
    _ = ∑ k, if incidence i k = true ∧ incidence j k = true then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hi : incidence i k = true <;> by_cases hj : incidence j k = true <;> simp [hi, hj]
    _ = ((Finset.univ.filter fun k => incidence i k = true ∧ incidence j k = true).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by
      by_cases hij : i = j
      · subst j
        simp [rowSize]
      · obtain ⟨point, onBoth, unique⟩ := rowPairs i j hij
        have filter_eq : (Finset.univ.filter fun k => incidence i k = true ∧ incidence j k = true) =
            {point} := by
          ext candidate
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨unique candidate, fun equal => equal ▸ onBoth⟩
        simp [filter_eq, hij]

lemma incidence_row_sum (incidence : Fin n → Fin n → Bool) (size : ℕ)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = size) (i : Fin n) :
    ∑ j, incidenceMatrix incidence i j = (size : ℤ) := by
  change ∑ j, (if incidence i j = true then (1 : ℤ) else 0) = _
  rw [← Finset.sum_filter]
  simp [rowSize]

def sumZeroVector {R : Type} [CommRing R] (x : Fin n → R) : Fin (n + 1) → R :=
  Fin.cons (-∑ i, x i) x

lemma sum_sumZeroVector {R : Type} [CommRing R] (x : Fin n → R) :
    ∑ i, sumZeroVector x i = 0 := by
  rw [Fin.sum_univ_succ]
  simp [sumZeroVector]

def restrictMatrix {R : Type} [CommRing R] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => A i.succ j.succ - A i.succ 0

lemma restrictMatrix_mulVec {R : Type} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (x : Fin n → R)
    (c : R) (columnSums : ∀ j, ∑ i, A i j = c) :
    A *ᵥ sumZeroVector x = sumZeroVector (restrictMatrix A *ᵥ x) := by
  have tail (i : Fin n) : (A *ᵥ sumZeroVector x) i.succ = (restrictMatrix A *ᵥ x) i := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sumZeroVector, Fin.cons_zero,
      Fin.cons_succ, restrictMatrix, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have sum_eq : ∑ i, (A *ᵥ sumZeroVector x) i = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, columnSums]
    rw [← Finset.mul_sum, sum_sumZeroVector, mul_zero]
  rw [Fin.sum_univ_succ] at sum_eq
  simp_rw [tail] at sum_eq
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [sumZeroVector, Fin.cons_zero] using eq_neg_of_add_eq_zero_left sum_eq
  · simpa only [sumZeroVector, Fin.cons_succ] using tail j

def onesMatrix {R : Type} [One R] : Matrix (Fin n) (Fin n) R := Matrix.of fun _ _ => 1

lemma onesMatrix_mulVec {R : Type} [CommRing R] (x : Fin n → R) :
    onesMatrix *ᵥ x = fun _ => ∑ j, x j := by
  ext i
  simp [onesMatrix, Matrix.mulVec, dotProduct]

lemma dotProduct_sumZeroVector {R : Type} [CommRing R] (x y : Fin n → R) :
    sumZeroVector x ⬝ᵥ sumZeroVector y = x ⬝ᵥ ((1 + onesMatrix) *ᵥ y) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, onesMatrix_mulVec, dotProduct_add]
  simp only [dotProduct, Fin.sum_univ_succ, sumZeroVector, Fin.cons_zero, Fin.cons_succ,
    neg_mul_neg, ← Finset.sum_mul]
  exact add_comm _ _

-- Restricting to the sum-zero subspace removes the all-ones matrix from the Gram identity.
lemma restrictMatrix_pairing {R : Type} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (c factor : R)
    (columnSums : ∀ j, ∑ i, A i j = c)
    (gram : Aᵀ * A = factor • 1 + onesMatrix) (x y : Fin n → R) :
    (restrictMatrix A *ᵥ x) ⬝ᵥ ((1 + onesMatrix) *ᵥ (restrictMatrix A *ᵥ y)) =
      factor * (x ⬝ᵥ ((1 + onesMatrix) *ᵥ y)) := by
  rw [← dotProduct_sumZeroVector, ← dotProduct_sumZeroVector,
    ← restrictMatrix_mulVec A x c columnSums, ← restrictMatrix_mulVec A y c columnSums]
  have move_transpose (u v : Fin (n + 1) → R) :
      (A *ᵥ u) ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ ((Aᵀ * A) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]
  rw [move_transpose, gram, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    onesMatrix_mulVec, sum_sumZeroVector]
  simp [dotProduct_smul]

lemma incidence_six_pairing (incidence : Fin 43 → Fin 43 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 7)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (x y : Fin 42 → ℤ) :
    (restrictMatrix (incidenceMatrix incidence)ᵀ *ᵥ x) ⬝ᵥ
      ((1 + onesMatrix) *ᵥ (restrictMatrix (incidenceMatrix incidence)ᵀ *ᵥ y)) =
        6 * (x ⬝ᵥ ((1 + onesMatrix) *ᵥ y)) := by
  apply restrictMatrix_pairing _ 7 6
  · exact incidence_row_sum incidence 7 rowSize
  · rw [Matrix.transpose_transpose, incidence_gram incidence 7 rowSize rowPairs]
    ext i j
    change (if i = j then (7 : ℤ) else 1) = 6 * (1 : Matrix (Fin 43) (Fin 43) ℤ) i j + 1
    by_cases eq : i = j <;> simp [Matrix.one_apply, eq]

def modThree (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  B.map (Int.castRingHom (ZMod 3))

def reduceVector (x : Fin n → ℤ) : Fin n → ZMod 3 := fun i => x i

def liftVector (x : Fin n → ZMod 3) : Fin n → ℤ := fun i => (x i).val

lemma reduce_lift (x : Fin n → ZMod 3) : reduceVector (liftVector x) = x := by
  funext i
  simp [reduceVector, liftVector]

lemma reduce_mulVec (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    reduceVector (B *ᵥ x) = modThree B *ᵥ reduceVector x := by
  funext i
  exact RingHom.map_mulVec (Int.castRingHom (ZMod 3)) B x i

lemma reduce_pairing (G : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    ((x ⬝ᵥ (G *ᵥ y) : ℤ) : ZMod 3) = reduceVector x ⬝ᵥ (modThree G *ᵥ reduceVector y) := by
  change (Int.castRingHom (ZMod 3)) (x ⬝ᵥ (G *ᵥ y)) = _
  rw [RingHom.map_dotProduct]
  change reduceVector x ⬝ᵥ reduceVector (G *ᵥ y) = _
  rw [reduce_mulVec]

lemma kernel_lift_multiple (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod 3)
    (inKernel : modThree B *ᵥ x = 0) : ∃ y : Fin n → ℤ, B *ᵥ liftVector x = (3 : ℤ) • y := by
  classical
  have each (i : Fin n) : (3 : ℤ) ∣ (B *ᵥ liftVector x) i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    change reduceVector (B *ᵥ liftVector x) i = 0
    rw [reduce_mulVec, reduce_lift, inKernel]
    rfl
  choose y hy using each
  refine ⟨y, ?_⟩
  funext i
  exact hy i

lemma image_isotropic (B G : Matrix (Fin n) (Fin n) ℤ)
    (scale : ∀ x y, (B *ᵥ x) ⬝ᵥ (G *ᵥ (B *ᵥ y)) = 6 * (x ⬝ᵥ (G *ᵥ y)))
    (x y : Fin n → ZMod 3) :
    (modThree B *ᵥ x) ⬝ᵥ (modThree G *ᵥ (modThree B *ᵥ y)) = 0 := by
  have reduced := congrArg (Int.castRingHom (ZMod 3)) (scale (liftVector x) (liftVector y))
  change (((B *ᵥ liftVector x) ⬝ᵥ (G *ᵥ (B *ᵥ liftVector y)) : ℤ) : ZMod 3) = _ at reduced
  rw [reduce_pairing, reduce_mulVec, reduce_mulVec, reduce_lift, reduce_lift] at reduced
  simpa [show (6 : ZMod 3) = 0 by decide] using reduced

-- The images of two integral lifts of kernel vectors have all coordinates divisible by three.
-- Their pairing is divisible by nine, so the original pairing is divisible by three.
lemma kernel_isotropic (B G : Matrix (Fin n) (Fin n) ℤ)
    (scale : ∀ x y, (B *ᵥ x) ⬝ᵥ (G *ᵥ (B *ᵥ y)) = 6 * (x ⬝ᵥ (G *ᵥ y)))
    (x y : Fin n → ZMod 3) (xKernel : modThree B *ᵥ x = 0) (yKernel : modThree B *ᵥ y = 0) :
    x ⬝ᵥ (modThree G *ᵥ y) = 0 := by
  obtain ⟨u, hu⟩ := kernel_lift_multiple B x xKernel
  obtain ⟨v, hv⟩ := kernel_lift_multiple B y yKernel
  have scaled := scale (liftVector x) (liftVector y)
  rw [hu, hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul] at scaled
  change 3 * (3 * (u ⬝ᵥ (G *ᵥ v))) = 6 * (liftVector x ⬝ᵥ (G *ᵥ liftVector y)) at scaled
  have dvd_pairing : (3 : ℤ) ∣ liftVector x ⬝ᵥ (G *ᵥ liftVector y) := by
    exact ⟨(liftVector x ⬝ᵥ (G *ᵥ liftVector y)) - (u ⬝ᵥ (G *ᵥ v)), by omega⟩
  have reduced := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr dvd_pairing
  rwa [reduce_pairing, reduce_lift, reduce_lift] at reduced

lemma det_block_swap {F I : Type} [CommRing F] [Fintype I] [DecidableEq I] :
    (Matrix.fromBlocks (0 : Matrix I I F) (1 : Matrix I I F) 1 0).det =
      (-1 : F) ^ Fintype.card I := by
  let L : Matrix (I ⊕ I) (I ⊕ I) F := Matrix.fromBlocks 1 0 1 1
  let U : Matrix (I ⊕ I) (I ⊕ I) F := Matrix.fromBlocks 1 (-1) 0 1
  let D : Matrix (I ⊕ I) (I ⊕ I) F := Matrix.fromBlocks 1 0 0 (-1)
  have product_eq : L * U * L * D = Matrix.fromBlocks 0 1 1 0 := by
    simp [L, U, D, Matrix.fromBlocks_multiply]
  have detL : L.det = 1 := by simp [L]
  have detU : U.det = 1 := by simp [U]
  have detD : D.det = (-1 : F) ^ Fintype.card I := by
    simp [D, Matrix.det_neg]
  rw [← product_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, detL, detU, detD]
  simp

lemma determinant_of_isotropic_block (Q : Matrix (Fin 21 ⊕ Fin 21) (Fin 21 ⊕ Fin 21) (ZMod 3))
    (symm : Qᵀ = Q) (zeroBlock : ∀ i j, Q (Sum.inl i) (Sum.inl j) = 0) :
    ∃ d : ZMod 3, Q.det = -(d ^ 2) := by
  let C : Matrix (Fin 21) (Fin 21) (ZMod 3) := Matrix.of fun i j => Q (Sum.inl i) (Sum.inr j)
  let D : Matrix (Fin 21) (Fin 21) (ZMod 3) := Matrix.of fun i j => Q (Sum.inr i) (Sum.inr j)
  have form : Q = Matrix.fromBlocks 0 C Cᵀ D := by
    ext (i | i) (j | j)
    · exact zeroBlock _ _
    · rfl
    · exact congrFun (congrFun symm (Sum.inl j)) (Sum.inr i)
    · rfl
  have swap : Matrix.fromBlocks 0 1 1 0 * Q = Matrix.fromBlocks Cᵀ D 0 C := by
    rw [form, Matrix.fromBlocks_multiply]
    simp
  have determinant := congrArg Matrix.det swap
  rw [Matrix.det_mul, det_block_swap, Fintype.card_fin, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_transpose, show (-1 : ZMod 3)^21 = -1 by decide, neg_one_mul] at determinant
  exact ⟨C.det, by rw [sq, ← determinant, neg_neg]⟩

abbrev OrderSixIndex := Fin 21 ⊕ Fin 21

-- A basis starting with 21 isotropic vectors would give a Gram determinant that is both a
-- nonzero square and the negative of a square over the field with three elements.
lemma isotropic_finrank_lt_half {I : Type} [Fintype I] [DecidableEq I] (card : Fintype.card I = 42)
    (G : Matrix I I (ZMod 3))
    (symmetric : Gᵀ = G) (determinant : G.det = 1)
    (U : Submodule (ZMod 3) (I → ZMod 3))
    (isotropic : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ (G *ᵥ y) = 0) :
    Module.finrank (ZMod 3) U ≤ 20 := by
  classical
  by_contra! h
  have ambientDim : Module.finrank (ZMod 3) (I → ZMod 3) = 42 := by simp [card]
  let b := Module.finBasis (ZMod 3) U
  let index : Fin 21 → Fin (Module.finrank (ZMod 3) U) := Fin.castLE h
  let vectors : Fin 21 → (I → ZMod 3) := fun i => b (index i)
  have independent : LinearIndependent (ZMod 3) vectors := by
    exact (b.linearIndependent.comp index (Fin.castLE_injective h)).map' U.subtype (by simp)
  let W := Submodule.span (ZMod 3) (Set.range vectors)
  have W_le : W ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (b (index i)).property
  have W_dim : Module.finrank (ZMod 3) W = 21 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card independent
  obtain ⟨C, complementary⟩ := Submodule.exists_isCompl W
  have C_dim : Module.finrank (ZMod 3) C = 21 := by
    have add_dims := Submodule.finrank_add_eq_of_isCompl complementary
    rw [W_dim, ambientDim] at add_dims
    omega
  let e := (Module.finBasisOfFinrankEq (ZMod 3) W W_dim).prod
    (Module.finBasisOfFinrankEq (ZMod 3) C C_dim)
  let basis := e.map (W.prodEquivOfIsCompl C complementary)
  have left_mem (i : Fin 21) : basis (Sum.inl i) ∈ U := W_le (by
    simp [basis, e, Submodule.coe_prodEquivOfIsCompl'])
  let blockIndex : OrderSixIndex ≃ I := Fintype.equivOfCardEq (by simp [OrderSixIndex, card])
  let indexedBasis := basis.reindex blockIndex
  let standard := Pi.basisFun (ZMod 3) I
  let P := standard.toMatrix indexedBasis
  have P_entry (i j : I) : P i j = indexedBasis j i := by
    simp [P, standard, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have P_det_ne : P.det ≠ 0 := by
    have product_eq := standard.toMatrix_mul_toMatrix_flip indexedBasis
    change P * indexedBasis.toMatrix standard = 1 at product_eq
    have hdet := congrArg Matrix.det product_eq
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    intro zero
    simp [zero] at hdet
  let Q := Pᵀ * G * P
  have Q_symmetric : Qᵀ = Q := by
    simp [Q, Matrix.transpose_mul, symmetric, Matrix.mul_assoc]
  let Q_block := Matrix.reindex blockIndex.symm blockIndex.symm Q
  have Q_block_symmetric : Q_blockᵀ = Q_block := by
    ext i j
    change Qᵀ (blockIndex i) (blockIndex j) = Q (blockIndex i) (blockIndex j)
    rw [Q_symmetric]
  have Q_zeroBlock (i j : Fin 21) : Q_block (Sum.inl i) (Sum.inl j) = 0 := by
    change (Pᵀ * G * P) (blockIndex (Sum.inl i)) (blockIndex (Sum.inl j)) = 0
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, P_entry, Matrix.mul_apply, indexedBasis,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    exact isotropic _ (left_mem i) _ (left_mem j)
  obtain ⟨d, Q_det⟩ := determinant_of_isotropic_block Q_block Q_block_symmetric Q_zeroBlock
  rw [show Q_block.det = Q.det from Matrix.det_reindex_self _ _] at Q_det
  have squares : P.det ^ 2 = -(d ^ 2) := by
    simpa [Q, Matrix.det_mul, Matrix.det_transpose, determinant, sq] using Q_det
  have no_nonzero_square : ∀ a d : ZMod 3, a ^ 2 = -(d ^ 2) → a = 0 := by decide
  exact P_det_ne (no_nonzero_square _ _ squares)

lemma reduced_gram_properties :
    let G : Matrix (Fin 42) (Fin 42) (ZMod 3) := modThree (1 + onesMatrix)
    Gᵀ = G ∧ G.det = 1 := by
  have cast_gram : modThree (1 + onesMatrix : Matrix (Fin 42) (Fin 42) ℤ) =
      (1 + onesMatrix : Matrix (Fin 42) (Fin 42) (ZMod 3)) := by
    ext i j
    change (((1 : Matrix (Fin 42) (Fin 42) ℤ) i j + 1 : ℤ) : ZMod 3) =
      (1 : Matrix (Fin 42) (Fin 42) (ZMod 3)) i j + 1
    by_cases eq : i = j
    · simp [Matrix.one_apply, eq]
      decide
    · simp [Matrix.one_apply, eq]
  dsimp only
  rw [cast_gram]
  constructor
  · ext i j
    change (1 : Matrix (Fin 42) (Fin 42) (ZMod 3)) j i + 1 =
      (1 : Matrix (Fin 42) (Fin 42) (ZMod 3)) i j + 1
    simp [Matrix.one_apply, eq_comm]
  · let ones : Fin 42 → ZMod 3 := fun _ => 1
    have allOnes : (onesMatrix : Matrix (Fin 42) (Fin 42) (ZMod 3)) =
        Matrix.replicateCol Unit ones * Matrix.replicateRow Unit ones := by
      ext i j
      simp [onesMatrix, Matrix.mul_apply, ones]
    rw [allOnes, Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) ones ones]
    have dotOnes : ones ⬝ᵥ ones = (42 : ZMod 3) := by simp [ones, dotProduct]
    rw [dotOnes]
    decide

-- Rank-nullity rules out a kernel and image that are both at most 20-dimensional.
lemma no_factor_six (B G : Matrix (Fin 42) (Fin 42) ℤ)
    (symmetric : (modThree G)ᵀ = modThree G) (determinant : (modThree G).det = 1)
    (scale : ∀ x y, (B *ᵥ x) ⬝ᵥ (G *ᵥ (B *ᵥ y)) = 6 * (x ⬝ᵥ (G *ᵥ y))) : False := by
  let T : (Fin 42 → ZMod 3) →ₗ[ZMod 3] (Fin 42 → ZMod 3) := (modThree B).mulVecLin
  have apply_T (x : Fin 42 → ZMod 3) : T x = modThree B *ᵥ x := rfl
  have dimension := LinearMap.finrank_range_add_finrank_ker T
  have dim42 : Module.finrank (ZMod 3) (Fin 42 → ZMod 3) = 42 := by simp
  have card42 : Fintype.card (Fin 42) = 42 := by simp
  rw [dim42] at dimension
  have kernelProperty : ∀ x ∈ LinearMap.ker T, ∀ y ∈ LinearMap.ker T,
      x ⬝ᵥ (modThree G *ᵥ y) = 0 := by
    intro x hx y hy
    rw [LinearMap.mem_ker, apply_T] at hx hy
    exact kernel_isotropic B G scale x y hx hy
  have rangeProperty : ∀ x ∈ LinearMap.range T, ∀ y ∈ LinearMap.range T,
      x ⬝ᵥ (modThree G *ᵥ y) = 0 := by
    intro x hx y hy
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hx
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hy
    rw [apply_T] at hu hv
    rw [← hu, ← hv]
    exact image_isotropic B G scale u v
  have kerBound := isotropic_finrank_lt_half card42 (modThree G) symmetric determinant
    (LinearMap.ker T) kernelProperty
  have rangeBound := isotropic_finrank_lt_half card42 (modThree G) symmetric determinant
    (LinearMap.range T) rangeProperty
  omega

theorem no_order_six (incidence : Fin 43 → Fin 43 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 7)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) : False :=
  no_factor_six (restrictMatrix (incidenceMatrix incidence)ᵀ) (1 + onesMatrix)
    reduced_gram_properties.1 reduced_gram_properties.2
    (incidence_six_pairing incidence rowSize rowPairs)

end OrderSix

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1.H1 := by
  intro incidence rowSize _columnSize rowPairs _columnPairs
  exact OrderSix.no_order_six incidence rowSize rowPairs
