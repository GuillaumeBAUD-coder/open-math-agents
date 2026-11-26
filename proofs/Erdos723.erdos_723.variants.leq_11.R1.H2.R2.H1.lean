import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2

/-! A hypothetical plane of order ten forces a weight-fifteen, weight-sixteen, or primitive weight-nineteen codeword. -/

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

def onesMatrix {R : Type} [One R] : Matrix (Fin n) (Fin n) R := Matrix.of fun _ _ => 1

lemma onesMatrix_mulVec {R : Type} [CommRing R] (x : Fin n → R) :
    onesMatrix *ᵥ x = fun _ => ∑ j, x j := by
  ext i
  simp [onesMatrix, Matrix.mulVec, dotProduct]

end OrderSix

open Matrix Finset

namespace OrderTen

def integerExtendedIncidence (incidence : Fin 111 → Fin 111 → Bool) :
    Matrix (Fin 111) (Fin 112) ℤ :=
  Matrix.of fun i => Fin.cons 1 (fun j => OrderSix.incidenceMatrix incidence i j)

def extendedIncidence (incidence : Fin 111 → Fin 111 → Bool) :
    Matrix (Fin 111) (Fin 112) (ZMod 2) :=
  (integerExtendedIncidence incidence).map (Int.castRingHom (ZMod 2))

lemma extendedIncidence_gram_zero (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    extendedIncidence incidence * (extendedIncidence incidence)ᵀ = 0 := by
  let A := OrderSix.incidenceMatrix incidence
  have gram : A * Aᵀ = Matrix.of (fun i j => if i = j then (11 : ℤ) else 1) :=
    OrderSix.incidence_gram incidence 11 rowSize rowPairs
  ext i j
  have entry : ∑ k, A i k * A j k = (if i = j then (11 : ℤ) else 1) := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] using
      congrFun (congrFun gram i) j
  have reduced := congrArg (Int.castRingHom (ZMod 2)) entry
  rw [map_sum] at reduced
  simp only [map_mul] at reduced
  change (∑ k, (A i k : ZMod 2) * (A j k : ZMod 2)) =
    ((if i = j then (11 : ℤ) else 1 : ℤ) : ZMod 2) at reduced
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.transpose_apply, extendedIncidence, Matrix.map_apply, integerExtendedIncidence,
    Matrix.of_apply, Fin.cons_zero,
    Fin.cons_succ, Matrix.zero_apply]
  change ((1 : ℤ) : ZMod 2) * ((1 : ℤ) : ZMod 2) +
    (∑ k, (A i k : ZMod 2) * (A j k : ZMod 2)) = 0
  rw [reduced]
  by_cases eq : i = j
  · simp only [eq, if_true]
    decide
  · simp only [if_neg eq]
    decide

-- The columns of the transpose generate the binary code of the extended incidence matrix.
lemma extended_row_code_isotropic (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (x y : Fin 111 → ZMod 2) :
    ((extendedIncidence incidence)ᵀ *ᵥ x) ⬝ᵥ ((extendedIncidence incidence)ᵀ *ᵥ y) = 0 := by
  let B := extendedIncidence incidence
  have gram : B * Bᵀ = 0 := extendedIncidence_gram_zero incidence rowSize rowPairs
  change (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = 0
  have pairing : (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ ((B * Bᵀ) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec x, mulVec_transpose]
  rw [pairing, gram, Matrix.zero_mulVec, dotProduct_zero]

lemma binary_values : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

lemma hammingNorm_sum_indicator {I : Type} [Fintype I] (u : I → ZMod 2) :
    hammingNorm u = ∑ i, if u i ≠ 0 then (1 : ℕ) else 0 := by
  rw [← Finset.sum_filter]
  simp [hammingNorm]

lemma extended_row_weight (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11) (i : Fin 111) :
    hammingNorm (extendedIncidence incidence i) = 12 := by
  rw [hammingNorm_sum_indicator, Fin.sum_univ_succ]
  simp only [extendedIncidence, Matrix.map_apply, integerExtendedIncidence, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ]
  change (if ((1 : ℤ) : ZMod 2) ≠ 0 then (1 : ℕ) else 0) +
    (∑ j, if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) = 12
  have tail : (∑ j, if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j => incidence i j = true).card := by
    have indicator (j : Fin 111) :
        (if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) =
          (if incidence i j = true then 1 else 0) := by
      by_cases bit : incidence i j = true <;> simp [OrderSix.incidenceMatrix, bit]
    simp_rw [indicator]
    rw [← Finset.sum_filter]
    simp
  rw [tail, rowSize]
  decide

lemma overlap_even {I : Type} [Fintype I] (x y : I → ZMod 2) (orthogonal : x ⬝ᵥ y = 0) :
    2 ∣ (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card := by
  have dot_eq : x ⬝ᵥ y = ((Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card : ZMod 2) := by
    calc
      _ = ∑ i, if x i ≠ 0 ∧ y i ≠ 0 then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rcases binary_values (x i) with hx | hx <;> rcases binary_values (y i) with hy | hy <;>
          simp [hx, hy]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [dot_eq] at orthogonal
  exact (ZMod.natCast_eq_zero_iff _ 2).mp orthogonal

lemma weight_add_of_orthogonal {I : Type} [Fintype I] (x y : I → ZMod 2)
    (orthogonal : x ⬝ᵥ y = 0) (hx : 4 ∣ hammingNorm x) (hy : 4 ∣ hammingNorm y) :
    4 ∣ hammingNorm (x + y) := by
  have indicator (i : I) :
      (if (x + y) i ≠ 0 then (1 : ℕ) else 0) + 2 * (if x i ≠ 0 ∧ y i ≠ 0 then 1 else 0) =
        (if x i ≠ 0 then 1 else 0) + (if y i ≠ 0 then 1 else 0) := by
    rcases binary_values (x i) with h | h <;> rcases binary_values (y i) with k | k <;>
      simp [Pi.add_apply, h, k, show (1 : ZMod 2) + 1 = 0 by decide]
  have count := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => indicator i)
  have overlapSum : (∑ j, if x j ≠ 0 ∧ y j ≠ 0 then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at count
  rw [← hammingNorm_sum_indicator (x + y), ← hammingNorm_sum_indicator x,
    ← hammingNorm_sum_indicator y, overlapSum] at count
  have overlap := overlap_even x y orthogonal
  omega

-- Every word of the extended binary incidence code has weight divisible by four.
lemma extended_code_doubly_even (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (a : Fin 111 → ZMod 2) : 4 ∣ hammingNorm ((extendedIncidence incidence)ᵀ *ᵥ a) := by
  let B := extendedIncidence incidence
  have membership : Bᵀ *ᵥ a ∈ Submodule.span (ZMod 2) (Set.range Bᵀ.col) := by
    rw [← Matrix.range_mulVecLin]
    exact ⟨a, rfl⟩
  refine Submodule.span_induction (p := fun x _ => 4 ∣ hammingNorm x) ?_ ?_ ?_ ?_ membership
  · rintro _ ⟨i, rfl⟩
    change 4 ∣ hammingNorm (extendedIncidence incidence i)
    rw [extended_row_weight incidence rowSize]
    decide
  · simp
  · intro x y hx hy hweightX hweightY
    rw [← Matrix.range_mulVecLin] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact weight_add_of_orthogonal _ _
      (extended_row_code_isotropic incidence rowSize rowPairs a b) hweightX hweightY
  · intro c x _ h
    rcases binary_values c with rfl | rfl <;> simp [h]

lemma integerExtended_gram (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    integerExtendedIncidence incidence * (integerExtendedIncidence incidence)ᵀ =
      (10 : ℤ) • 1 + (2 : ℤ) • OrderSix.onesMatrix := by
  let A := OrderSix.incidenceMatrix incidence
  have gram : A * Aᵀ = Matrix.of (fun i j => if i = j then (11 : ℤ) else 1) :=
    OrderSix.incidence_gram incidence 11 rowSize rowPairs
  ext i j
  have entry : ∑ k, A i k * A j k = (if i = j then (11 : ℤ) else 1) := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] using
      congrFun (congrFun gram i) j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  change 1 * 1 + (∑ k, A i k * A j k) = 10 * (1 : Matrix (Fin 111) (Fin 111) ℤ) i j + 2 * 1
  rw [entry]
  by_cases eq : i = j <;> simp [Matrix.one_apply, eq]

lemma integerExtended_pairing (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (x y : Fin 111 → ℤ) :
    ((integerExtendedIncidence incidence)ᵀ *ᵥ x) ⬝ᵥ ((integerExtendedIncidence incidence)ᵀ *ᵥ y) =
      10 * (x ⬝ᵥ y) + 2 * ((∑ j, x j) * ∑ j, y j) := by
  let B := integerExtendedIncidence incidence
  change _ = _
  have pairing : (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ ((B * Bᵀ) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec x, mulVec_transpose]
  rw [pairing, integerExtended_gram incidence rowSize rowPairs, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, OrderSix.onesMatrix_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul, dotProduct, ← Finset.sum_mul]

lemma integerExtended_head (incidence : Fin 111 → Fin 111 → Bool) (x : Fin 111 → ℤ) :
    ((integerExtendedIncidence incidence)ᵀ *ᵥ x) 0 = ∑ i, x i := by
  simp [Matrix.mulVec, integerExtendedIncidence, dotProduct]

-- A lifted kernel vector has even image coordinates, including its coordinate sum.
lemma extended_kernel_lift (incidence : Fin 111 → Fin 111 → Bool)
    (x : Fin 111 → ZMod 2) (hx : (extendedIncidence incidence)ᵀ *ᵥ x = 0) :
    ∃ u : Fin 112 → ℤ,
      (integerExtendedIncidence incidence)ᵀ *ᵥ (fun i => (x i).val) = (2 : ℤ) • u := by
  let X : Fin 111 → ℤ := fun i => (x i).val
  let B := integerExtendedIncidence incidence
  have reduce_X : (fun i => (X i : ZMod 2)) = x := by
    funext i
    simp [X]
  have each (j : Fin 112) : (2 : ℤ) ∣ (Bᵀ *ᵥ X) j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    have cast := RingHom.map_mulVec (Int.castRingHom (ZMod 2)) Bᵀ X j
    change ((Bᵀ *ᵥ X) j : ZMod 2) =
      (((extendedIncidence incidence)ᵀ) *ᵥ (fun i => (X i : ZMod 2))) j at cast
    rw [reduce_X, hx] at cast
    exact cast
  choose u hu using each
  exact ⟨u, funext hu⟩

-- The two lifted images have pairing divisible by four. The Gram identity then
-- forces the original pairing of the kernel vectors to vanish modulo two.
lemma extended_kernel_isotropic (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (x y : Fin 111 → ZMod 2)
    (hx : (extendedIncidence incidence)ᵀ *ᵥ x = 0)
    (hy : (extendedIncidence incidence)ᵀ *ᵥ y = 0) : x ⬝ᵥ y = 0 := by
  let X : Fin 111 → ℤ := fun i => (x i).val
  let Y : Fin 111 → ℤ := fun i => (y i).val
  obtain ⟨u, hu⟩ := extended_kernel_lift incidence x hx
  obtain ⟨v, hv⟩ := extended_kernel_lift incidence y hy
  have headX : (∑ i, X i) = 2 * u 0 :=
    (integerExtended_head incidence X).symm.trans (congrFun hu 0)
  have headY : (∑ i, Y i) = 2 * v 0 :=
    (integerExtended_head incidence Y).symm.trans (congrFun hv 0)
  have pairing := integerExtended_pairing incidence rowSize rowPairs X Y
  change (integerExtendedIncidence incidence)ᵀ *ᵥ X = (2 : ℤ) • u at hu
  change (integerExtendedIncidence incidence)ᵀ *ᵥ Y = (2 : ℤ) • v at hv
  rw [hu, hv, smul_dotProduct, dotProduct_smul, headX, headY] at pairing
  change 2 * (2 * (u ⬝ᵥ v)) = 10 * (X ⬝ᵥ Y) + 2 * ((2 * u 0) * (2 * v 0)) at pairing
  have simplified : 4 * (u ⬝ᵥ v) = 10 * (X ⬝ᵥ Y) + 8 * (u 0 * v 0) := by
    calc
      4 * (u ⬝ᵥ v) = 2 * (2 * (u ⬝ᵥ v)) := by ring
      _ = 10 * (X ⬝ᵥ Y) + 2 * ((2 * u 0) * (2 * v 0)) := pairing
      _ = _ := by ring
  have even_pairing : (2 : ℤ) ∣ X ⬝ᵥ Y := by omega
  have reduced := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr even_pairing
  change (Int.castRingHom (ZMod 2)) (X ⬝ᵥ Y) = 0 at reduced
  rw [RingHom.map_dotProduct] at reduced
  simpa [X, Y, Function.comp_def] using reduced

def dotForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  (1 : Matrix (Fin n) (Fin n) (ZMod 2)).toBilin'

lemma dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by simp)

lemma le_dotComplement {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (isotropic : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) : U ≤ (dotForm n).orthogonal U := by
  intro y hy
  apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
  intro x hx
  simpa [dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec] using isotropic x hx y hy

lemma isotropic_finrank_bound {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (isotropic : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) :
    Module.finrank (ZMod 2) U ≤ n / 2 := by
  have le_rank := Submodule.finrank_mono (le_dotComplement U isotropic)
  rw [LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate n)] at le_rank
  have ambient : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  rw [ambient] at le_rank
  omega

lemma extended_code_self_dual (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    let C := LinearMap.range ((extendedIncidence incidence)ᵀ).mulVecLin
    Module.finrank (ZMod 2) C = 56 ∧ C = (dotForm 112).orthogonal C := by
  let T := ((extendedIncidence incidence)ᵀ).mulVecLin
  let C := LinearMap.range T
  have apply_T (x : Fin 111 → ZMod 2) : T x = (extendedIncidence incidence)ᵀ *ᵥ x := rfl
  have kernelBound : Module.finrank (ZMod 2) (LinearMap.ker T) ≤ 111 / 2 := by
    apply isotropic_finrank_bound
    intro x hx y hy
    rw [LinearMap.mem_ker, apply_T] at hx hy
    exact extended_kernel_isotropic incidence rowSize rowPairs x y hx hy
  have imageIsotropic : ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hx
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
    rw [apply_T] at ha hb
    rw [← ha, ← hb]
    exact extended_row_code_isotropic incidence rowSize rowPairs a b
  have imageBound := isotropic_finrank_bound C imageIsotropic
  have dimensions := LinearMap.finrank_range_add_finrank_ker T
  change Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) (LinearMap.ker T) = _ at dimensions
  have dimDomain : Module.finrank (ZMod 2) (Fin 111 → ZMod 2) = 111 := by simp
  rw [dimDomain] at dimensions
  have dimC : Module.finrank (ZMod 2) C = 56 := by omega
  refine ⟨dimC, Submodule.eq_of_le_of_finrank_le (le_dotComplement C imageIsotropic) ?_⟩
  rw [LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate 112), dimC]
  simp

def pointSupport (w : Fin 112 → ZMod 2) : Finset (Fin 111) :=
  Finset.univ.filter fun p => w p.succ ≠ 0

def pointsOnLine (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (l : Fin 111) :
    Finset (Fin 111) :=
  S.filter fun p => incidence l p = true

lemma extended_weight_eq (w : Fin 112 → ZMod 2) :
    hammingNorm w = (if w 0 ≠ 0 then 1 else 0) + (pointSupport w).card := by
  rw [hammingNorm_sum_indicator, Fin.sum_univ_succ]
  exact congrArg (fun n : ℕ => (if w 0 ≠ 0 then 1 else 0) + n)
    (hammingNorm_sum_indicator (fun p : Fin 111 => w p.succ)).symm

lemma row_dot_word (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) (w : Fin 112 → ZMod 2) :
    extendedIncidence incidence l ⬝ᵥ w = w 0 + ((pointsOnLine incidence (pointSupport w) l).card : ZMod 2) := by
  rw [dotProduct, Fin.sum_univ_succ]
  have head : extendedIncidence incidence l 0 = 1 := by
    simp [extendedIncidence, integerExtendedIncidence]
  rw [head, one_mul]
  have sum_eq : (∑ j : Fin 111, extendedIncidence incidence l j.succ * w j.succ) =
      ((pointsOnLine incidence (pointSupport w) l).card : ZMod 2) := by
    calc
      _ = ∑ j : Fin 111, if w j.succ ≠ 0 ∧ incidence l j = true then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        change (OrderSix.incidenceMatrix incidence l j : ZMod 2) * w j.succ = _
        by_cases bit : incidence l j = true <;>
          rcases binary_values (w j.succ) with hz | hz <;>
          simp [OrderSix.incidenceMatrix, bit, hz]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [pointsOnLine, pointSupport, Finset.filter_filter, and_comm]
  exact congrArg (w 0 + ·) sum_eq

lemma sum_pointsOnLine (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (S : Finset (Fin 111)) :
    (∑ l, (pointsOnLine incidence S l).card) = S.card * 11 := by
  calc
    _ = ∑ l : Fin 111, ∑ p ∈ S, if incidence l p = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [pointsOnLine]
    _ = ∑ p ∈ S, (Finset.univ.filter fun l => incidence l p = true).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simp
    _ = _ := by simp [columnSize]

-- Distinct lines through a point must meet a set that avoids that point in distinct points.
lemma pencil_bound (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (p : Fin 111) (L S : Finset (Fin 111)) (outside : p ∉ S)
    (through : ∀ l ∈ L, incidence l p = true)
    (meets : ∀ l ∈ L, ∃ q ∈ S, incidence l q = true) : L.card ≤ S.card := by
  classical
  have choiceSet (l : ↥L) := meets l l.property
  choose q in_S on_l using choiceSet
  let f : ↥L → ↥S := fun l => ⟨q l, in_S l⟩
  have injective : Function.Injective f := by
    intro l m same
    have same_point : q l = q m := congrArg Subtype.val same
    have distinct : p ≠ q l := fun h => outside (h.symm ▸ in_S l)
    obtain ⟨line, _, unique⟩ := columnPairs p (q l) distinct
    apply Subtype.ext
    exact (unique l ⟨through l l.property, on_l l⟩).trans
      (unique m ⟨through m m.property, by rw [same_point]; exact on_l m⟩).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f injective

lemma even_intersections_large_support (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (hS : S.Nonempty)
    (evenLines : ∀ l, 2 ∣ (pointsOnLine incidence S l).card) : 12 ≤ S.card := by
  classical
  obtain ⟨p, hp⟩ := hS
  let L := Finset.univ.filter fun l => incidence l p = true
  have contains_p (l : Fin 111) (hl : l ∈ L) : incidence l p = true := (Finset.mem_filter.mp hl).2
  have second_point (l : Fin 111) (hl : l ∈ L) : ∃ q ∈ S.erase p, incidence l q = true := by
    let T := pointsOnLine incidence S l
    have p_mem : p ∈ T := Finset.mem_filter.mpr ⟨hp, contains_p l hl⟩
    have positive : 0 < T.card := Finset.card_pos.mpr ⟨p, p_mem⟩
    have even_card : 2 ∣ T.card := evenLines l
    have another : 0 < (T.erase p).card := by
      rw [Finset.card_erase_of_mem p_mem]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp another
    obtain ⟨ne, in_T⟩ := Finset.mem_erase.mp hq
    obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp in_T
    exact ⟨q, Finset.mem_erase.mpr ⟨ne, in_S⟩, on_l⟩
  have bound := pencil_bound incidence columnPairs p L (S.erase p) (by simp) contains_p second_point
  rw [Finset.card_erase_of_mem hp] at bound
  change (Finset.univ.filter fun l => incidence l p = true).card ≤ S.card - 1 at bound
  rw [columnSize] at bound
  omega

lemma odd_intersections_eleven_is_line (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 11)
    (oddLines : ∀ l, (pointsOnLine incidence S l).card % 2 = 1) :
    ∃ l, S = Finset.univ.filter fun p => incidence l p = true := by
  classical
  have two_points : 1 < S.card := by rw [size]; decide
  obtain ⟨p, hp, q, hq, distinct⟩ := Finset.one_lt_card.mp two_points
  obtain ⟨l, ⟨on_p, on_q⟩, _⟩ := columnPairs p q distinct
  let L := Finset.univ.filter fun p => incidence l p = true
  let T := pointsOnLine incidence S l
  have at_least_two : 2 ≤ T.card := by
    have subset : ({p, q} : Finset (Fin 111)) ⊆ T := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨hp, on_p⟩
      · have same := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_filter.mpr ⟨hq, on_q⟩
    simpa [distinct] using Finset.card_le_card subset
  have odd_T : T.card % 2 = 1 := oddLines l
  have at_least_three : 3 ≤ T.card := by omega
  by_cases sameLine : S = L
  · exact ⟨l, sameLine⟩
  have not_subset : ¬ L ⊆ S := by
    intro sub
    have cardL : L.card = 11 := rowSize l
    exact sameLine (Finset.eq_of_subset_of_card_le sub (by rw [size, cardL])).symm
  obtain ⟨x, in_L, not_in_S⟩ := Finset.not_subset.mp not_subset
  have l_through : incidence l x = true := (Finset.mem_filter.mp in_L).2
  let K := (Finset.univ.filter fun k => incidence k x = true).erase l
  have contains_x (k : Fin 111) (hk : k ∈ K) : incidence k x = true :=
    (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
  have meets (k : Fin 111) (hk : k ∈ K) : ∃ p ∈ S \ L, incidence k p = true := by
    have positive : 0 < (pointsOnLine incidence S k).card := by
      have := oddLines k
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp positive
    obtain ⟨in_S, on_k⟩ := Finset.mem_filter.mp hy
    have not_on_l : y ∉ L := by
      intro in_L_y
      have ne : x ≠ y := fun eq => not_in_S (eq.symm ▸ in_S)
      have on_l_y : incidence l y = true := (Finset.mem_filter.mp in_L_y).2
      obtain ⟨line, _, unique⟩ := columnPairs x y ne
      exact (Finset.mem_erase.mp hk).1 ((unique k ⟨contains_x k hk, on_k⟩).trans
        (unique l ⟨l_through, on_l_y⟩).symm)
    exact ⟨y, Finset.mem_sdiff.mpr ⟨in_S, not_on_l⟩, on_k⟩
  have outside_ten := pencil_bound incidence columnPairs x K (S \ L)
    (fun mem => not_in_S (Finset.mem_sdiff.mp mem).1) contains_x meets
  have card_K : K.card = 10 := by
    change ((Finset.univ.filter fun k => incidence k x = true).erase l).card = _
    have member : l ∈ (Finset.univ.filter fun k => incidence k x = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, l_through⟩
    rw [Finset.card_erase_of_mem member, columnSize]
  have inter : S ∩ L = T := by
    ext y
    simp [L, T, pointsOnLine]
  have partition := Finset.card_sdiff_add_card_inter S L
  rw [inter, size] at partition
  rw [card_K] at outside_ten
  omega

-- A nonzero word in the extended incidence code has weight at least twelve.
lemma extended_code_minimum_weight (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (a : Fin 111 → ZMod 2) (nonzero : (extendedIncidence incidence)ᵀ *ᵥ a ≠ 0) :
    12 ≤ hammingNorm ((extendedIncidence incidence)ᵀ *ᵥ a) := by
  let w := (extendedIncidence incidence)ᵀ *ᵥ a
  let S := pointSupport w
  have lineParity (l : Fin 111) : w 0 + ((pointsOnLine incidence S l).card : ZMod 2) = 0 := by
    have ortho := extended_row_code_isotropic incidence rowSize rowPairs (Pi.single l 1) a
    rw [Matrix.mulVec_single_one] at ortho
    change extendedIncidence incidence l ⬝ᵥ w = 0 at ortho
    rwa [row_dot_word] at ortho
  change 12 ≤ hammingNorm w
  have weight : hammingNorm w = (if w 0 ≠ 0 then 1 else 0) + S.card := extended_weight_eq w
  rcases binary_values (w 0) with hzero | hone
  · have supportNonempty : S.Nonempty := by
      by_contra empty
      have emptyS := Finset.not_nonempty_iff_eq_empty.mp empty
      simp [hzero, emptyS] at weight
      exact nonzero weight
    have evenLines (l : Fin 111) : 2 ∣ (pointsOnLine incidence S l).card := by
      apply (ZMod.natCast_eq_zero_iff _ 2).mp
      simpa only [hzero, zero_add] using lineParity l
    have large := even_intersections_large_support incidence columnSize columnPairs S supportNonempty evenLines
    simpa [weight, hzero] using large
  · have each (l : Fin 111) : 1 ≤ (pointsOnLine incidence S l).card := by
      by_contra small
      have emptyCount : (pointsOnLine incidence S l).card = 0 := by omega
      have parity := lineParity l
      simp [hone, emptyCount] at parity
    have bound : (∑ _l : Fin 111, (1 : ℕ)) ≤ ∑ l, (pointsOnLine incidence S l).card :=
      Finset.sum_le_sum fun l _ => each l
    rw [sum_pointsOnLine incidence columnSize] at bound
    simp at bound
    rw [weight, hone, if_pos one_ne_zero]
    omega

end OrderTen
open Matrix Finset

namespace OrderTenWeights

-- The modulus exceeds both sides of the natural-number weight identity.
abbrev Count := ZMod 339456738992222314849

def binaryCharacter (x : ZMod 2) : Count := if x = 0 then 1 else -1

lemma binaryCharacter_add : ∀ x y : ZMod 2,
    binaryCharacter (x + y) = binaryCharacter x * binaryCharacter y := by decide

lemma binaryCharacter_zero : binaryCharacter 0 = 1 := rfl

lemma binaryCharacter_dot {n : ℕ} (x y : Fin n → ZMod 2) :
    binaryCharacter (x ⬝ᵥ y) = ∏ i, binaryCharacter (x i * y i) := by
  classical
  have transform (S : Finset (Fin n)) :
      binaryCharacter (∑ i ∈ S, x i * y i) = ∏ i ∈ S, binaryCharacter (x i * y i) := by
    induction S using Finset.induction_on with
    | empty => simp [binaryCharacter_zero]
    | insert i S hi ih => simp [hi, binaryCharacter_add, ih]
  exact transform Finset.univ

def coordinateMonomial {n : ℕ} (t : Fin n → Count) (word : Fin n → ZMod 2) : Count :=
  ∏ i, if word i = 0 then 1 else t i

lemma binaryCoordinateSum (x : ZMod 2) (t : Count) :
    (∑ b : ZMod 2, binaryCharacter (x * b) * (if b = 0 then 1 else t)) =
      1 + binaryCharacter x * t := by
  let f : ZMod 2 → Count := fun b => binaryCharacter (x * b) * (if b = 0 then 1 else t)
  have sum_eq := Fin.sum_univ_two (fun b : Fin 2 => f (show ZMod 2 from b))
  change (∑ b : ZMod 2, f b) = f 0 + f 1 at sum_eq
  change (∑ b : ZMod 2, f b) = _
  rw [sum_eq]
  simp [f, binaryCharacter_zero, show (1 : ZMod 2) ≠ 0 by decide]

lemma coordinate_character_transform {n : ℕ} (x : Fin n → ZMod 2) (t : Fin n → Count) :
    (∑ y : Fin n → ZMod 2, binaryCharacter (x ⬝ᵥ y) * coordinateMonomial t y) =
      ∏ i, (1 + binaryCharacter (x i) * t i) := by
  simp only [binaryCharacter_dot, coordinateMonomial, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : ZMod 2) => binaryCharacter (x i * y) * (if y = 0 then 1 else t i))]
  exact Finset.prod_congr rfl fun i _ => binaryCoordinateSum (x i) (t i)

-- Addition of any codeword with nontrivial character pairs off the two signs.
lemma character_sum_of_self_dual {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype C]
    [DecidablePred (· ∈ C)]
    (selfDual : C = (OrderTen.dotForm n).orthogonal C) (y : Fin n → ZMod 2) :
    (∑ c : C, binaryCharacter (c.val ⬝ᵥ y)) =
      if y ∈ C then (Fintype.card C : Count) else 0 := by
  classical
  have pairing (x : Fin n → ZMod 2) : OrderTen.dotForm n x y = x ⬝ᵥ y := by
    simp only [OrderTen.dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have mem_iff : y ∈ C ↔ ∀ c : C, c.val ⬝ᵥ y = 0 := by
    conv_lhs => rw [selfDual]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h c
      rw [← pairing]
      exact h c.val c.property
    · intro h x hx
      rw [pairing]
      exact h ⟨x, hx⟩
  by_cases mem : y ∈ C
  · simp [mem, mem_iff.mp mem, binaryCharacter_zero]
  · rw [if_neg mem]
    have nontrivial := mt mem_iff.mpr mem
    obtain ⟨a, ha⟩ := not_forall.mp nontrivial
    have aSign : binaryCharacter (a.val ⬝ᵥ y) = -1 := if_neg ha
    have negate_sum : -(∑ c : C, binaryCharacter (c.val ⬝ᵥ y)) =
        ∑ c : C, binaryCharacter (c.val ⬝ᵥ y) := by
      have translated := Equiv.sum_comp (Equiv.addRight a) (fun c : C => binaryCharacter (c.val ⬝ᵥ y))
      change (∑ c : C, binaryCharacter (((c + a : C) : Fin n → ZMod 2) ⬝ᵥ y)) = _ at translated
      simpa only [Submodule.coe_add, add_dotProduct, binaryCharacter_add,
        aSign, mul_neg_one, Finset.sum_neg_distrib] using translated
    let s := ∑ c : C, binaryCharacter (c.val ⬝ᵥ y)
    change -s = s at negate_sum
    have twice : (2 : Count) * s = 0 := by
      rw [two_mul]
      calc
        s + s = -s + s := congrArg (· + s) negate_sum.symm
        _ = 0 := neg_add_cancel s
    calc
      s = 169728369496111157425 * (2 * s) := by
        rw [← mul_assoc, show (169728369496111157425 : Count) * 2 = 1 by decide, one_mul]
      _ = 0 := by rw [twice, mul_zero]

-- MacWilliams transformation with a separate weight parameter for each coordinate.
lemma macWilliams_self_dual {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype C]
    (selfDual : C = (OrderTen.dotForm n).orthogonal C) (t : Fin n → Count) :
    (∑ c : C, ∏ i, (1 + binaryCharacter (c.val i) * t i)) =
      (Fintype.card C : Count) * ∑ c : C, coordinateMonomial t c.val := by
  classical
  calc
    _ = ∑ c : C, ∑ y : Fin n → ZMod 2, binaryCharacter (c.val ⬝ᵥ y) * coordinateMonomial t y := by
      apply Finset.sum_congr rfl
      intro c _
      exact (coordinate_character_transform c.val t).symm
    _ = ∑ y : Fin n → ZMod 2, (∑ c : C, binaryCharacter (c.val ⬝ᵥ y)) * coordinateMonomial t y := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = (Fintype.card C : Count) * ∑ c : C, coordinateMonomial t c.val := by
      simp_rw [character_sum_of_self_dual C selfDual, ite_mul, zero_mul]
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      exact congrArg ((Fintype.card C : Count) * ·)
        (Finset.sum_subtype _ (fun y => by simp) (coordinateMonomial t))

def tailWeight (w : Fin 112 → ZMod 2) : ℕ := (OrderTen.pointSupport w).card

def tailParameters (x : Count) : Fin 112 → Count := Fin.cons 0 (fun _ : Fin 111 => x)

lemma tail_monomial (x : Count) (w : Fin 112 → ZMod 2) :
    coordinateMonomial (tailParameters x) w = if w 0 = 0 then x ^ tailWeight w else 0 := by
  rw [coordinateMonomial, Fin.prod_univ_succ]
  simp only [tailParameters, Fin.cons_zero, Fin.cons_succ]
  have tail : (∏ i : Fin 111, if w i.succ = 0 then (1 : Count) else x) = x ^ tailWeight w := by
    rw [Finset.prod_ite]
    simp [tailWeight, OrderTen.pointSupport]
  rw [tail]
  split_ifs <;> simp

lemma tail_transform (x : Count) (w : Fin 112 → ZMod 2) :
    (∏ i, (1 + binaryCharacter (w i) * tailParameters x i)) =
      (1+x)^(111 - tailWeight w) * (1-x)^tailWeight w := by
  rw [Fin.prod_univ_succ]
  simp only [tailParameters, Fin.cons_zero, Fin.cons_succ, mul_zero, add_zero, one_mul]
  have factor (i : Fin 111) : 1 + binaryCharacter (w i.succ) * x =
      if w i.succ = 0 then 1 + x else 1 - x := by
    by_cases bit : w i.succ = 0 <;> simp [binaryCharacter, bit, sub_eq_add_neg]
  simp_rw [factor]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  change (1+x)^(Finset.univ.filter fun i : Fin 111 => w i.succ = 0).card * (1-x)^tailWeight w = _
  have counts := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 111)))
    (fun i => w i.succ = 0)
  rw [Finset.card_univ, Fintype.card_fin] at counts
  have countZeros : (Finset.univ.filter fun i : Fin 111 => w i.succ = 0).card = 111 - tailWeight w := by
    change _ + tailWeight w = _ at counts
    omega
  rw [countZeros]

def singleWeightRow (x : Count) (w : ℕ) : Count :=
  (1 + x)^(111-w) * (1-x)^w - 2^56 * (if w % 2 = 0 then x^w else 0)

lemma tail_parity_of_doublyEven (w : Fin 112 → ZMod 2) (even : 4 ∣ hammingNorm w) :
    (w 0 = 0 ↔ tailWeight w % 2 = 0) ∧ (tailWeight w % 4 = 0 ∨ tailWeight w % 4 = 3) := by
  have weight := OrderTen.extended_weight_eq w
  change _ = _ + tailWeight w at weight
  rcases OrderTen.binary_values (w 0) with h | h
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_add] at weight
    rw [weight] at even
    simp only [h, true_iff]
    omega
  · have oneNeZero : (1 : ZMod 2) ≠ 0 := by decide
    rw [h, if_pos oneNeZero] at weight
    rw [weight] at even
    simp only [h, oneNeZero, false_iff]
    omega

lemma tail_weight_identity (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (selfDual : C = (OrderTen.dotForm 112).orthogonal C)
    (size : Fintype.card C = 2^56)
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val) (x : Count) :
    (∑ c : C, singleWeightRow x (tailWeight c.val)) = 0 := by
  have transformed := macWilliams_self_dual C selfDual (tailParameters x)
  simp_rw [tail_monomial, tail_transform, size, Nat.cast_pow, Nat.cast_ofNat] at transformed
  have headEven (c : C) := (tail_parity_of_doublyEven c.val (doublyEven c)).1
  simp_rw [headEven] at transformed
  simp only [singleWeightRow, Finset.sum_sub_distrib, ← Finset.mul_sum]
  exact sub_eq_zero.mpr transformed

def admissibleWeight (i : Fin 56) : Prop :=
  (i.val = 0 ∨ 11 ≤ i.val) ∧ (i.val % 4 = 0 ∨ i.val % 4 = 3)

instance (i : Fin 56) : Decidable (admissibleWeight i) := by
  unfold admissibleWeight
  infer_instance

-- The two complementary weights add to 111. Only their even member survives
-- on the right of MacWilliams when the extra coordinate has parameter zero.
def pairedWeightRow (x : Count) (i : Fin 56) : Count :=
  let j := 111 - i.val
  let evenWeight := if i.val % 2 = 0 then i.val else j
  (1 + x)^j * (1 - x)^i.val + (1 + x)^i.val * (1 - x)^j - 2^56 * x^evenWeight

def evaluationPoints : Fin 19 → Count :=
  ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18, 19, 21, 22, 23]

def evaluationCoefficients : Fin 19 → Count :=
  ![181295082614010868710, 298589620664916442695, 10587033868723149573,
    258630786687014004292, 255805490046459290227, 117261976948294505767,
    88414232949357630591, 16886352687342961225, 147306162735810802936,
    186559953932833931040, 111358608625861144016, 4662165841723207292,
    287200561744918393905, 91053926928345981921, 132580288414918648036,
    256605581542936018393, 29132300553643771008, 223935088176763646810,
    216632048293712966196]

def delta (w i : Fin 56) : Count := if i = w then 1 else 0

-- A certificate found by modular elimination and checked in the kernel.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma weight_certificate (i : Fin 56) (h : admissibleWeight i) :
    (∑ k : Fin 19, evaluationCoefficients k * pairedWeightRow (evaluationPoints k) i) =
      delta 19 i - 63525 * delta 0 i + 350 * delta 11 i -
        141 * delta 12 i + 27 * delta 15 i - 7 * delta 16 i := by
  have checked : ∀ j : Fin 56, admissibleWeight j →
      (∑ k : Fin 19, evaluationCoefficients k * pairedWeightRow (evaluationPoints k) j) =
        delta 19 j - 63525 * delta 0 j + 350 * delta 11 j -
          141 * delta 12 j + 27 * delta 15 j - 7 * delta 16 j := by decide
  exact checked i h

lemma weight_count_relation (counts : Fin 56 → Count)
    (support : ∀ i, ¬admissibleWeight i → counts i = 0)
    (zeroWord : counts 0 = 1) (lineWords : counts 11 = 111)
    (identities : ∀ x : Count, ∑ i : Fin 56, pairedWeightRow x i * counts i = 0) :
    counts 19 - 63525 + 350 * 111 - 141 * counts 12 + 27 * counts 15 - 7 * counts 16 = 0 := by
  have relation : (∑ i : Fin 56,
      (∑ k : Fin 19, evaluationCoefficients k * pairedWeightRow (evaluationPoints k) i) * counts i) = 0 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, identities, mul_zero, Finset.sum_const_zero]
  have rewriteRows : (∑ i : Fin 56,
      (∑ k : Fin 19, evaluationCoefficients k * pairedWeightRow (evaluationPoints k) i) * counts i) =
      ∑ i : Fin 56, (delta 19 i - 63525 * delta 0 i + 350 * delta 11 i -
        141 * delta 12 i + 27 * delta 15 i - 7 * delta 16 i) * counts i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases admissible : admissibleWeight i
    · rw [weight_certificate i admissible]
    · rw [support i admissible, mul_zero, mul_zero]
  rw [rewriteRows] at relation
  have select (i : Fin 56) : (∑ j : Fin 56, delta i j * counts j) = counts i := by
    simp [delta, ite_mul]
  simpa only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum, select, zeroWord, lineWords, mul_one] using relation

lemma pairedWeightRow_eq (x : Count) (i : Fin 56) :
    pairedWeightRow x i = singleWeightRow x i.val + singleWeightRow x (111-i.val) := by
  have bound := i.isLt
  have subtract : 111 - (111 - i.val) = i.val := by omega
  have parity : (111 - i.val) % 2 = 0 ↔ ¬ i.val % 2 = 0 := by omega
  by_cases ev : i.val % 2 = 0 <;>
    simp [pairedWeightRow, singleWeightRow, subtract, parity, ev] <;> ring

lemma tailWeight_le (w : Fin 112 → ZMod 2) : tailWeight w ≤ 111 := by
  simpa [tailWeight] using Finset.card_le_univ (OrderTen.pointSupport w)

lemma tailWeight_add_ones (w : Fin 112 → ZMod 2) : tailWeight (w + 1) = 111 - tailWeight w := by
  have support : OrderTen.pointSupport (w + 1) = (Finset.univ.filter fun i : Fin 111 => w i.succ = 0) := by
    ext i
    rcases OrderTen.binary_values (w i.succ) with bit | bit <;>
      simp [OrderTen.pointSupport, Pi.add_apply, bit, show (1 : ZMod 2) + 1 = 0 by decide]
  have total := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 111)))
    (fun i => w i.succ = 0)
  rw [Finset.card_univ, Fintype.card_fin] at total
  change _ + tailWeight w = _ at total
  change (OrderTen.pointSupport (w + 1)).card = _
  rw [support]
  omega

lemma dot_ones_eq_weight {n : ℕ} (x : Fin n → ZMod 2) :
    x ⬝ᵥ (1 : Fin n → ZMod 2) = (hammingNorm x : ZMod 2) := by
  calc
    _ = ∑ i, if x i ≠ 0 then (1 : ZMod 2) else 0 := by
      simp only [dotProduct, Pi.one_apply, mul_one]
      apply Finset.sum_congr rfl
      intro i _
      rcases OrderTen.binary_values (x i) with bit | bit <;> simp [bit]
    _ = _ := by rw [← Finset.sum_filter]; simp [hammingNorm]

lemma ones_in_code (C : Submodule (ZMod 2) (Fin 112 → ZMod 2))
    (selfDual : C = (OrderTen.dotForm 112).orthogonal C)
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val) : (1 : Fin 112 → ZMod 2) ∈ C := by
  rw [selfDual]
  apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
  intro x hx
  rw [OrderTen.dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec, dot_ones_eq_weight]
  apply (ZMod.natCast_eq_zero_iff _ 2).mpr
  have even := doublyEven ⟨x, hx⟩
  change 4 ∣ hammingNorm x at even
  omega

def weightCount (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C] (i : ℕ) : ℕ :=
  (Finset.univ.filter fun c : C => tailWeight c.val = i).card

-- Addition of the all-ones word pairs each weight below 56 with one above it.
lemma sum_by_paired_weights (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (ones_mem : (1 : Fin 112 → ZMod 2) ∈ C) (f : ℕ → Count) :
    (∑ c : C, f (tailWeight c.val)) =
      ∑ i : Fin 56, (f i.val + f (111 - i.val)) * (weightCount C i.val : Count) := by
  classical
  let ones : C := ⟨1, ones_mem⟩
  let L := Finset.univ.filter fun c : C => tailWeight c.val < 56
  have flipWeight (c : C) : tailWeight (c + ones).val = 111 - tailWeight c.val := tailWeight_add_ones c.val
  have high_after_flip (c : C) : ¬tailWeight (c + ones).val < 56 ↔ tailWeight c.val < 56 := by
    have bound := tailWeight_le c.val
    rw [flipWeight]
    omega
  have reindex := Equiv.sum_comp (Equiv.addRight ones) (fun c : C =>
    if ¬tailWeight c.val < 56 then f (tailWeight c.val) else 0)
  change (∑ c : C, if ¬tailWeight (c + ones).val < 56 then f (tailWeight (c + ones).val) else 0) = _ at reindex
  simp_rw [high_after_flip, flipWeight] at reindex
  rw [← Finset.sum_filter, ← Finset.sum_filter] at reindex
  have split := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset C)
    (fun c => tailWeight c.val < 56) (fun c => f (tailWeight c.val))
  calc
    _ = ∑ c ∈ L, (f (tailWeight c.val) + f (111 - tailWeight c.val)) := by
      rw [Finset.sum_add_distrib]
      change _ = (∑ c ∈ Finset.univ.filter (fun c : C => tailWeight c.val < 56),
        f (tailWeight c.val)) + _
      rw [reindex]
      exact split.symm
    _ = ∑ i ∈ Finset.range 56, (f i + f (111 - i)) * (weightCount C i : Count) := by
      have maps : ∀ c ∈ L, tailWeight c.val ∈ Finset.range 56 := by
        intro c hc
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2
      rw [← Finset.sum_fiberwise_of_maps_to maps]
      apply Finset.sum_congr rfl
      intro i hi
      have fiber : L.filter (fun c => tailWeight c.val = i) =
          (Finset.univ.filter fun c : C => tailWeight c.val = i) := by
        ext c
        have small := Finset.mem_range.mp hi
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun h => ⟨h.symm ▸ small, h⟩⟩
      rw [fiber]
      calc
        _ = ∑ c ∈ (Finset.univ.filter fun c : C => tailWeight c.val = i), (f i + f (111-i)) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [(Finset.mem_filter.mp hc).2]
        _ = _ := by simp [weightCount, nsmul_eq_mul, mul_comm, add_mul]
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i => (f i + f (111-i)) * (weightCount C i : Count)) 56).symm

lemma tailWeight_zero (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val) : weightCount C 0 = 1 := by
  classical
  have filter : (Finset.univ.filter fun c : C => tailWeight c.val = 0) = {0} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have extended := OrderTen.extended_weight_eq c.val
      change hammingNorm c.val = _ + tailWeight c.val at extended
      rw [h, add_zero] at extended
      have weight := doublyEven c
      have zero : hammingNorm c.val = 0 := by
        split_ifs at extended <;> omega
      exact Subtype.ext (hammingNorm_eq_zero.mp zero)
    · rintro rfl
      simp [tailWeight, OrderTen.pointSupport]
  rw [weightCount, filter, Finset.card_singleton]

lemma support_admissible (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val)
    (minWeight : ∀ c : C, c ≠ 0 → 12 ≤ hammingNorm c.val) (i : Fin 56)
    (outside : ¬admissibleWeight i) : weightCount C i.val = 0 := by
  classical
  have none (c : C) : tailWeight c.val ≠ i.val := by
    intro weight
    apply outside
    have residue := (tail_parity_of_doublyEven c.val (doublyEven c)).2
    rw [weight] at residue
    refine ⟨?_, residue⟩
    by_cases zero : c = 0
    · subst c
      left
      simpa [tailWeight, OrderTen.pointSupport] using weight.symm
    · right
      have extended := OrderTen.extended_weight_eq c.val
      change hammingNorm c.val = _ + tailWeight c.val at extended
      have large := minWeight c zero
      rw [weight] at extended
      split_ifs at extended <;> omega
  simp [weightCount, none]

lemma weight_nineteen_count (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (selfDual : C = (OrderTen.dotForm 112).orthogonal C)
    (size : Fintype.card C = 2^56)
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val)
    (minWeight : ∀ c : C, c ≠ 0 → 12 ≤ hammingNorm c.val)
    (lineCount : weightCount C 11 = 111)
    (none15 : weightCount C 15 = 0) (none16 : weightCount C 16 = 0) :
    weightCount C 19 = 24675 + 141 * weightCount C 12 := by
  let counts (i : Fin 56) : Count := weightCount C i.val
  have equations (x : Count) : (∑ i : Fin 56, pairedWeightRow x i * counts i) = 0 := by
    have identity := tail_weight_identity C selfDual size doublyEven x
    rw [sum_by_paired_weights C (ones_in_code C selfDual doublyEven), ← Finset.sum_congr rfl
      (fun i _ => congrArg (· * (weightCount C i.val : Count)) (pairedWeightRow_eq x i))] at identity
    exact identity
  have relation := weight_count_relation counts
    (fun i h => by simp [counts, support_admissible C doublyEven minWeight i h])
    (by simp [counts, tailWeight_zero C doublyEven]) (by simp [counts, lineCount]) equations
  change (weightCount C 19 : Count) - 63525 + 350 * 111 -
    141 * (weightCount C 12 : Count) + 27 * (weightCount C 15 : Count) -
    7 * (weightCount C 16 : Count) = 0 at relation
  have castEq : (weightCount C 19 : Count) = (↑(24675 + 141 * weightCount C 12) : Count) := by
    simp only [none15, none16, Nat.cast_zero, mul_zero, add_zero, sub_zero] at relation
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    change (weightCount C 19 : Count) = 24675 + 141 * (weightCount C 12 : Count)
    apply sub_eq_zero.mp
    convert relation using 1
    ring
  have le (k : ℕ) : weightCount C k ≤ 2^56 := by
    rw [← size]
    exact Finset.card_le_univ _
  have left_bound : weightCount C 19 < 339456738992222314849 := by
    have := le 19
    omega
  have right_bound : 24675 + 141 * weightCount C 12 < 339456738992222314849 := by
    have := le 12
    omega
  have valueEq := congrArg ZMod.val castEq
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt left_bound,
    Nat.mod_eq_of_lt right_bound] at valueEq

lemma extendedIncidence_entry (incidence : Fin 111 → Fin 111 → Bool) (l p : Fin 111) :
    OrderTen.extendedIncidence incidence l p.succ = if incidence l p = true then 1 else 0 := by
  change (OrderSix.incidenceMatrix incidence l p : ZMod 2) = _
  by_cases bit : incidence l p = true <;> simp [OrderSix.incidenceMatrix, bit]

lemma extendedIncidence_head (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) :
    OrderTen.extendedIncidence incidence l 0 = 1 := by
  simp [OrderTen.extendedIncidence, OrderTen.integerExtendedIncidence]

lemma row_support (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) :
    OrderTen.pointSupport (OrderTen.extendedIncidence incidence l) =
      Finset.univ.filter fun p => incidence l p = true := by
  ext p
  simp only [OrderTen.pointSupport, Finset.mem_filter, Finset.mem_univ, true_and, extendedIncidence_entry]
  split_ifs <;> simp_all

lemma word_of_weight_eleven_is_row (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (a : Fin 111 → ZMod 2) (weight : tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a) = 11) :
    ∃ l, (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a = OrderTen.extendedIncidence incidence l := by
  let w := (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
  have head : w 0 = 1 := by
    apply (OrderTen.binary_values (w 0)).resolve_left
    intro zero
    have odd := (tail_parity_of_doublyEven w (OrderTen.extended_code_doubly_even incidence rowSize rowPairs a)).1.mp zero
    change tailWeight w = 11 at weight
    rw [weight] at odd
    exact (by decide : 11 % 2 ≠ 0) odd
  have oddLines (l : Fin 111) : (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card % 2 = 1 := by
    have ortho := OrderTen.extended_row_code_isotropic incidence rowSize rowPairs (Pi.single l 1) a
    rw [Matrix.mulVec_single_one] at ortho
    change OrderTen.extendedIncidence incidence l ⬝ᵥ w = 0 at ortho
    rw [OrderTen.row_dot_word, head] at ortho
    let count := (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card
    have cast_one : (count : ZMod 2) = 1 := by
      rcases OrderTen.binary_values (count : ZMod 2) with zero | one
      · change 1 + (count : ZMod 2) = 0 at ortho
        rw [zero, add_zero] at ortho
        exact ((by decide : (1 : ZMod 2) ≠ 0) ortho).elim
      · exact one
    have modulo := congrArg ZMod.val cast_one
    rwa [ZMod.val_natCast] at modulo
  obtain ⟨l, support⟩ := OrderTen.odd_intersections_eleven_is_line incidence rowSize columnSize columnPairs
    (OrderTen.pointSupport w) weight oddLines
  refine ⟨l, ?_⟩
  change w = _
  funext i
  refine Fin.cases ?_ (fun p => ?_) i
  · rw [head, extendedIncidence_head]
  · rw [extendedIncidence_entry]
    have iff_on : w p.succ ≠ 0 ↔ incidence l p = true := by
      have eq := congrArg (fun s : Finset (Fin 111) => p ∈ s) support
      simpa [OrderTen.pointSupport] using Iff.of_eq eq
    by_cases bit : incidence l p = true
    · rw [if_pos bit]
      exact (OrderTen.binary_values (w p.succ)).resolve_left (iff_on.mpr bit)
    · rw [if_neg bit]
      exact not_not.mp (mt iff_on.mp bit)

lemma weight_eleven_count (incidence : Fin 111 → Fin 111 → Bool)
    [Fintype (LinearMap.range ((OrderTen.extendedIncidence incidence)ᵀ).mulVecLin)]
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) :
    weightCount (LinearMap.range ((OrderTen.extendedIncidence incidence)ᵀ).mulVecLin) 11 = 111 := by
  classical
  let B := OrderTen.extendedIncidence incidence
  let T := Bᵀ.mulVecLin
  let C := LinearMap.range T
  have apply_T (a : Fin 111 → ZMod 2) : T a = Bᵀ *ᵥ a := rfl
  let row (l : Fin 111) : C := ⟨B l, ⟨Pi.single l 1, by rw [apply_T, Matrix.mulVec_single_one]; rfl⟩⟩
  have rowInWeight (l : Fin 111) : tailWeight (row l).val = 11 := by
    change (OrderTen.pointSupport (B l)).card = 11
    rw [row_support, rowSize]
  have rowsInjective : Function.Injective row := by
    intro l m equal
    by_contra distinct
    have rowsEqual : B l = B m := congrArg Subtype.val equal
    have supportEqual : (Finset.univ.filter fun p => incidence l p = true) =
        (Finset.univ.filter fun p => incidence m p = true) := by
      rw [← row_support incidence l, ← row_support incidence m]
      exact congrArg OrderTen.pointSupport rowsEqual
    have big : 1 < (Finset.univ.filter fun p => incidence l p = true).card := by
      rw [rowSize]
      decide
    obtain ⟨p, hp, q, hq, ne⟩ := Finset.one_lt_card.mp big
    have hp_m := supportEqual ▸ hp
    have hq_m := supportEqual ▸ hq
    obtain ⟨point, _, unique⟩ := rowPairs l m distinct
    exact ne ((unique p ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hp_m).2⟩).trans
      (unique q ⟨(Finset.mem_filter.mp hq).2, (Finset.mem_filter.mp hq_m).2⟩).symm)
  have listing : (Finset.univ.filter fun c : C => tailWeight c.val = 11) = Finset.univ.image row := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro weight
      obtain ⟨a, ha⟩ := LinearMap.mem_range.mp c.property
      rw [apply_T] at ha
      rw [← ha] at weight
      obtain ⟨l, hl⟩ := word_of_weight_eleven_is_row incidence rowSize rowPairs columnSize columnPairs a weight
      exact ⟨l, Subtype.ext (hl.symm.trans ha)⟩
    · rintro ⟨l, rfl⟩
      exact rowInWeight l
  change (Finset.univ.filter fun c : C => tailWeight c.val = 11).card = _
  rw [listing, Finset.card_image_of_injective _ rowsInjective]
  simp

lemma extended_word_explicit (incidence : Fin 111 → Fin 111 → Bool) (a : Fin 111 → ZMod 2) :
    (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a =
      Fin.cons (∑ l, a l) (fun p => ∑ l, a l * (if incidence l p = true then 1 else 0)) := by
  funext i
  refine Fin.cases ?_ (fun p => ?_) i
  · simp [Matrix.mulVec, dotProduct, extendedIncidence_head]
  · simp [Matrix.mulVec, dotProduct, extendedIncidence_entry, mul_comm]

lemma primitive_word_of_weight_nineteen
    (C : Submodule (ZMod 2) (Fin 112 → ZMod 2)) [Fintype C]
    (doublyEven : ∀ c : C, 4 ∣ hammingNorm c.val)
    (minWeight : ∀ c : C, c ≠ 0 → 12 ≤ hammingNorm c.val)
    (lineCount : weightCount C 11 = 111)
    (none15 : ∀ c : C, tailWeight c.val ≠ 15) (none16 : ∀ c : C, tailWeight c.val ≠ 16)
    (weight19Count : weightCount C 19 = 24675 + 141 * weightCount C 12) :
    ∃ c : C, tailWeight c.val = 19 ∧ ∀ a b : C,
      tailWeight a.val < 19 → tailWeight b.val < 19 → c ≠ a + b := by
  classical
  by_contra! no_primitive
  have small (c : C) (nonzero : c ≠ 0) (weight : tailWeight c.val < 19) :
      tailWeight c.val = 11 ∨ tailWeight c.val = 12 := by
    have large := minWeight c nonzero
    have extended := OrderTen.extended_weight_eq c.val
    change hammingNorm c.val = _ + tailWeight c.val at extended
    rw [extended] at large
    have residues := (tail_parity_of_doublyEven c.val (doublyEven c)).2
    have not15 := none15 c
    have not16 := none16 c
    split_ifs at large <;> omega
  have head11 (c : C) (weight : tailWeight c.val = 11) : c.val 0 = 1 := by
    apply (OrderTen.binary_values (c.val 0)).resolve_left
    intro zero
    have parity := (tail_parity_of_doublyEven c.val (doublyEven c)).1.mp zero
    omega
  have head12 (c : C) (weight : tailWeight c.val = 12) : c.val 0 = 0 :=
    (tail_parity_of_doublyEven c.val (doublyEven c)).1.mpr (by omega)
  let W (k : ℕ) := {c : C // tailWeight c.val = k}
  let (k : ℕ) : Fintype (W k) := Fintype.ofFinite (W k)
  have count (k : ℕ) : Fintype.card (W k) = weightCount C k := by
    unfold weightCount
    exact Fintype.card_of_subtype _ (fun c => by simp)
  have pair (c : W 19) : ∃ p : W 11 × W 12, c.val = p.1.val + p.2.val := by
    obtain ⟨a, b, ha, hb, sum⟩ := no_primitive c.val c.property
    have a_nonzero : a ≠ 0 := by
      intro zero
      rw [zero, zero_add] at sum
      have weight := congrArg (fun t : C => tailWeight t.val) sum
      exact (Nat.ne_of_gt hb) (c.property.symm.trans weight)
    have b_nonzero : b ≠ 0 := by
      intro zero
      rw [zero, add_zero] at sum
      have weight := congrArg (fun t : C => tailWeight t.val) sum
      exact (Nat.ne_of_gt ha) (c.property.symm.trans weight)
    have c_head : c.val.val 0 = 1 := by
      apply (OrderTen.binary_values (c.val.val 0)).resolve_left
      intro zero
      have parity := (tail_parity_of_doublyEven c.val.val (doublyEven c.val)).1.mp zero
      have weight := c.property
      omega
    have heads := congrArg (fun t : C => t.val 0) sum
    change c.val.val 0 = a.val 0 + b.val 0 at heads
    rcases small a a_nonzero ha with a11 | a12 <;> rcases small b b_nonzero hb with b11 | b12
    · rw [c_head, head11 a a11, head11 b b11] at heads
      exact ((by decide : (1 : ZMod 2) ≠ 1 + 1) heads).elim
    · exact ⟨(⟨a, a11⟩, ⟨b, b12⟩), sum⟩
    · exact ⟨(⟨b, b11⟩, ⟨a, a12⟩), sum.trans (add_comm a b)⟩
    · rw [c_head, head12 a a12, head12 b b12] at heads
      exact ((by decide : (1 : ZMod 2) ≠ 0 + 0) heads).elim
  choose decomposition result using pair
  have injective : Function.Injective decomposition := by
    intro c d same
    apply Subtype.ext
    rw [result c, result d, same]
  have bound := Fintype.card_le_of_injective _ injective
  rw [Fintype.card_prod, count, count, count, lineCount, weight19Count] at bound
  omega

theorem order_ten_requires_fifteen_sixteen_or_primitive (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) :
    let V := fun a : Fin 111 → ZMod 2 => (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
    let weight := fun a => tailWeight (V a)
    ∃ a, weight a = 15 ∨ weight a = 16 ∨
      (weight a = 19 ∧ ∀ b c, weight b < 19 → weight c < 19 → V a ≠ V b + V c) := by
  classical
  intro V weight
  by_cases small : ∃ a, weight a = 15 ∨ weight a = 16
  · obtain ⟨a, h | h⟩ := small
    · exact ⟨a, Or.inl h⟩
    · exact ⟨a, Or.inr (Or.inl h)⟩
  let T := ((OrderTen.extendedIncidence incidence)ᵀ).mulVecLin
  let C := LinearMap.range T
  let : Fintype C := Fintype.ofFinite C
  have apply_T (a : Fin 111 → ZMod 2) : T a = V a := rfl
  have structural := OrderTen.extended_code_self_dual incidence rowSize rowPairs
  change Module.finrank (ZMod 2) C = 56 ∧ C = (OrderTen.dotForm 112).orthogonal C at structural
  have size : Fintype.card C = 2^56 := by
    calc
      _ = Fintype.card (Fin (Module.finrank (ZMod 2) C) → ZMod 2) :=
        Fintype.card_congr (Module.finBasis (ZMod 2) C).equivFun.toEquiv
      _ = _ := by rw [structural.1]; simp [Fintype.card_pi, ZMod.card]
  have double (c : C) : 4 ∣ hammingNorm c.val := by
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp c.property
    rw [apply_T] at ha
    rw [← ha]
    exact OrderTen.extended_code_doubly_even incidence rowSize rowPairs a
  have minimum (c : C) (nonzero : c ≠ 0) : 12 ≤ hammingNorm c.val := by
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp c.property
    rw [apply_T] at ha
    rw [← ha]
    exact OrderTen.extended_code_minimum_weight incidence rowSize rowPairs columnSize columnPairs a
      (fun h => nonzero (Subtype.ext (ha.symm.trans h)))
  have line_count : weightCount C 11 = 111 :=
    weight_eleven_count incidence rowSize rowPairs columnSize columnPairs
  have none (k : ℕ) (h : k = 15 ∨ k = 16) (c : C) : tailWeight c.val ≠ k := by
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp c.property
    rw [apply_T] at ha
    intro weight_eq
    have eq : weight a = k := (congrArg tailWeight ha).trans weight_eq
    exact small ⟨a, by simpa only [eq] using h⟩
  have none15 := none 15 (Or.inl rfl)
  have none16 := none 16 (Or.inr rfl)
  have count19 := weight_nineteen_count C structural.2 size double minimum line_count
    (by simp [weightCount, none15]) (by simp [weightCount, none16])
  obtain ⟨v, hv, primitive⟩ := primitive_word_of_weight_nineteen C double minimum
    line_count none15 none16 count19
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp v.property
  rw [apply_T] at ha
  refine ⟨a, Or.inr (Or.inr ⟨(congrArg tailWeight ha).trans hv, ?_⟩)⟩
  intro b c hb hc sum
  let B : C := ⟨V b, LinearMap.mem_range.mpr ⟨b, apply_T b⟩⟩
  let D : C := ⟨V c, LinearMap.mem_range.mpr ⟨c, apply_T c⟩⟩
  apply primitive B D hb hc
  apply Subtype.ext
  change v.val = V b + V c
  exact ha.symm.trans sum

end OrderTenWeights

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2.H1 := by
  intro incidence rowSizes columnSizes rowPairs columnPairs
  have required := OrderTenWeights.order_ten_requires_fifteen_sixteen_or_primitive
    incidence rowSizes columnSizes rowPairs columnPairs
  dsimp only at required ⊢
  simpa only [OrderTenWeights.extended_word_explicit, OrderTenWeights.tailWeight,
    OrderTen.pointSupport, hammingNorm, Fin.cons_succ] using required
