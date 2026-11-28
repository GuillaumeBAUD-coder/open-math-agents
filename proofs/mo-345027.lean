import OMAStatements.S_mo_345027
import Mathlib

namespace OMA.P345027
open Matrix Finset OMA.S_mo_345027
open scoped Matrix

lemma symm_dot {n : ℕ} {M : Mat n} (hM : M.PosSemidef) (x y : Vec n) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have hT : Mᵀ = M := IsSymm.eq hM.1
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma psd_quad {n : ℕ} {M : Mat n} (hM : M.PosSemidef) (x : Vec n) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  simpa using hM.dotProduct_mulVec_nonneg x

lemma cs_step {n : ℕ} {M : Mat n} (hM : M.PosSemidef) (y u : Vec n) (t : ℝ) :
    0 ≤ y ⬝ᵥ (M *ᵥ y) - 2 * t * (y ⬝ᵥ (M *ᵥ u)) + t ^ 2 * (u ⬝ᵥ (M *ᵥ u)) := by
  have h := psd_quad hM (y - t • u)
  have hs := symm_dot hM u y
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at h
  rw [hs] at h
  linarith [h]

variable {n m : ℕ} {A : Fin m → Mat n} {u : Vec n}

lemma weight_pos (h : admissible A u) (j : Fin m) : 0 < weight A u j :=
  Real.sqrt_pos.mpr (h.2.2 j)

lemma weight_sq (h : admissible A u) (j : Fin m) :
    weight A u j * weight A u j = u ⬝ᵥ (A j *ᵥ u) :=
  Real.mul_self_sqrt (h.2.2 j).le

lemma cols_mulVec (x : Vec m) :
    cols A u *ᵥ x = ∑ j, (x j / weight A u j) • (A j *ᵥ u) := by
  ext i
  simp only [mulVec, dotProduct, cols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dot_output (x : Vec m) :
    x ⬝ᵥ (output A u *ᵥ x) = (cols A u *ᵥ x) ⬝ᵥ ((∑ j, A j)⁻¹ *ᵥ (cols A u *ᵥ x)) := by
  rw [output, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma S_inv_mul (h : admissible A u) (v : Vec n) :
    (∑ j, A j) *ᵥ ((∑ j, A j)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((h.2.1.isUnit).map Matrix.detMonoidHom), one_mulVec]

lemma key_ineq (h : admissible A u) (x : Vec m) :
    x ⬝ᵥ (output A u *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [dot_output]
  set S := ∑ j, A j with hSdef
  set v := cols A u *ᵥ x with hv
  set y := S⁻¹ *ᵥ v with hy
  have hSy : S *ᵥ y = v := S_inv_mul h v
  have hQ1 : v ⬝ᵥ y = ∑ j, y ⬝ᵥ (A j *ᵥ y) := by
    rw [dotProduct_comm, ← hSy, hSdef, sum_mulVec, dotProduct_sum]
  have hQ2 : v ⬝ᵥ y = ∑ j, (x j / weight A u j) * (y ⬝ᵥ (A j *ᵥ u)) := by
    rw [dotProduct_comm, hv, cols_mulVec, dotProduct_sum]
    simp [dotProduct_smul]
  have hj : ∀ j, 2 * ((x j / weight A u j) * (y ⬝ᵥ (A j *ᵥ u))) ≤
      y ⬝ᵥ (A j *ᵥ y) + x j * x j := by
    intro j
    have c := cs_step (h.1 j) y u (x j / weight A u j)
    have hw := weight_pos h j
    have e : (x j / weight A u j) ^ 2 * (u ⬝ᵥ (A j *ᵥ u)) = x j * x j := by
      rw [← weight_sq h j]; field_simp
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← hQ2, ← hQ1] at hsum
  have : x ⬝ᵥ x = ∑ j, x j * x j := rfl
  linarith

lemma output_psd (h : admissible A u) : (output A u).PosSemidef := by
  have := (h.2.1.inv.posSemidef).conjTranspose_mul_mul_same (cols A u)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma one_sub_output_psd (h : admissible A u) : (1 - output A u).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact isHermitian_one.sub (output_psd h).1
  · simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub]
    linarith [key_ineq h x]

lemma output_weight (h : admissible A u) :
    output A u *ᵥ (weight A u) = weight A u := by
  rw [output, ← mulVec_mulVec, ← mulVec_mulVec, cols_mulVec]
  have h1 : (∑ j, (weight A u j / weight A u j) • (A j *ᵥ u)) = (∑ j, A j) *ᵥ u := by
    rw [sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_self (weight_pos h j).ne', one_smul]
  have h2 : (∑ j, A j)⁻¹ *ᵥ ((∑ j, A j) *ᵥ u) = u := by
    rw [mulVec_mulVec, nonsing_inv_mul _ ((h.2.1.isUnit).map Matrix.detMonoidHom),
      one_mulVec]
  rw [h1, h2]
  ext k
  rw [mulVec_transpose]
  simp only [vecMul, dotProduct, cols]
  have hw := weight_pos h k
  simp only [mul_div_assoc']
  rw [← Finset.sum_div]
  have : ∑ i, u i * (A k *ᵥ u) i = weight A u k * weight A u k := by
    rw [weight_sq h k]; rfl
  rw [this]; field_simp

lemma part1 (hm : 0 < m) (h : admissible A u) :
    eligible (output A u) ∧ IsGreatest (eigs (output A u)) 1 ∧
    ∀ t ∈ eigs (output A u), 0 ≤ t := by
  have hP := output_psd h
  refine ⟨⟨hP, one_sub_output_psd h, weight A u, weight_pos h, output_weight h⟩, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨weight A u, ?_, by rw [one_smul]; exact output_weight h⟩
    intro h0
    have := weight_pos h ⟨0, hm⟩
    rw [h0] at this
    exact lt_irrefl _ this
  · rintro t ⟨x, hx, hBx⟩
    have hpos : 0 < x ⬝ᵥ x := by
      rcases Function.ne_iff.mp hx with ⟨i, hi⟩
      have : 0 < x i * x i := mul_self_pos.mpr hi
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
    have hk := key_ineq h x
    rw [hBx, dotProduct_smul, smul_eq_mul] at hk
    nlinarith
  · rintro t ⟨x, hx, hBx⟩
    have hpos : 0 < x ⬝ᵥ x := by
      rcases Function.ne_iff.mp hx with ⟨i, hi⟩
      have : 0 < x i * x i := mul_self_pos.mpr hi
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
    have hk := psd_quad hP x
    rw [hBx, dotProduct_smul, smul_eq_mul] at hk
    nlinarith

section conv
open scoped MatrixOrder

lemma sqrt_fix {m : ℕ} {B : Mat m} (hB : B.PosSemidef) {w : Vec m} (hw : B *ᵥ w = w) :
    CFC.sqrt B *ᵥ w = w := by
  set R := CFC.sqrt B with hR
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hRp : R.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hD : (R + 1).PosDef := PosDef.posSemidef_add hRp PosDef.one
  have e : (R + 1) *ᵥ (R *ᵥ w - w) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, add_mul, hRR, one_mul, add_mulVec, add_mulVec, hw,
      one_mulVec]
    abel
  by_contra hne
  have hz : R *ᵥ w - w ≠ 0 := sub_ne_zero.mpr hne
  have := hD.dotProduct_mulVec_pos hz
  rw [e, dotProduct_zero] at this
  exact lt_irrefl _ this

noncomputable def mkA {m : ℕ} (hm : 0 < m) (B : Mat m) (j : Fin m) : Mat m :=
  vecMulVec (fun i => CFC.sqrt B i j) (fun i => CFC.sqrt B i j) +
    (if j = ⟨0, hm⟩ then 1 - B else 0)

lemma part2 {m : ℕ} (hm : 0 < m) (B : Mat m) (hE : eligible B) :
    ∃ (A : Fin m → Mat m) (u : Vec m), admissible A u ∧ (∑ j,A j)=1 ∧ output A u=B := by
  obtain ⟨hB, hB1, w, hwpos, hBw⟩ := hE
  set R := CFC.sqrt B with hR
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hRp : R.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hRT : Rᵀ = R := IsSymm.eq hRp.1
  have hRw : R *ᵥ w = w := sqrt_fix hB hBw
  have hBw0 : (1 - B) *ᵥ w = 0 := by rw [sub_mulVec, one_mulVec, hBw, sub_self]
  have hcol : ∀ j, (fun i => R i j) ⬝ᵥ w = w j := by
    intro j
    have := congrFun hRw j
    rw [← hRT] at this
    simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
  have hAw : ∀ j, mkA hm B j *ᵥ w = w j • (fun i => R i j) := by
    intro j
    rw [mkA, add_mulVec, vecMulVec_mulVec, ← hR, hcol]
    split_ifs
    · rw [hBw0, add_zero]; ext i; simp [mul_comm]
    · rw [zero_mulVec, add_zero]; ext i; simp [mul_comm]
  have hq : ∀ j, w ⬝ᵥ (mkA hm B j *ᵥ w) = w j * w j := by
    intro j
    rw [hAw, dotProduct_smul, dotProduct_comm, hcol, smul_eq_mul]
  have hsum : ∑ j, mkA hm B j = 1 := by
    have h1 : ∑ j, vecMulVec (fun i => R i j) (fun i => R i j) = R * Rᵀ := by
      ext a b
      simp [vecMulVec_apply, mul_apply, Matrix.sum_apply]
    have h2 : ∑ j : Fin m, (if j = ⟨0, hm⟩ then 1 - B else 0) = 1 - B := by
      rw [Finset.sum_ite_eq']; simp
    simp only [mkA, Finset.sum_add_distrib, ← hR, h1, h2, hRT, hRR]
    abel
  have hadm : admissible (mkA hm B) w := by
    refine ⟨fun j => ?_, ?_, fun j => ?_⟩
    · refine PosSemidef.add ?_ ?_
      · simpa using posSemidef_vecMulVec_self_star (fun i => CFC.sqrt B i j)
      · split_ifs
        · exact hB1
        · exact PosSemidef.zero
    · rw [hsum]; exact PosDef.one
    · rw [hq]; exact mul_pos (hwpos j) (hwpos j)
  have hwt : ∀ j, weight (mkA hm B) w j = w j := by
    intro j
    rw [weight, hq, Real.sqrt_mul_self (hwpos j).le]
  have hcols : cols (mkA hm B) w = R := by
    ext i j
    rw [cols, hAw, hwt]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(hwpos j).ne']
  refine ⟨mkA hm B, w, hadm, hsum, ?_⟩
  rw [output, hcols, hsum, inv_one, mul_one, hRT, hRR]

end conv

end OMA.P345027

theorem OMA.solution : type_of% @OMA.S_mo_345027.main := by
  refine ⟨fun m n A u hm h => OMA.P345027.part1 hm h, fun m B hm => ⟨?_, ?_⟩⟩
  · exact OMA.P345027.part2 hm B
  · rintro ⟨A, u, h, -, rfl⟩
    exact (OMA.P345027.part1 hm h).1
