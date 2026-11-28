import OMAStatements.S_mo_442655

open OMA.S_mo_442655 Matrix

namespace UnitaryAntiunitaryDistance

lemma euclid_sq {n : ℕ} (x : Fin n → ℂ) :
    euclid x ^ 2 = ∑ i : Fin n, Complex.normSq (x i) := by
  unfold euclid
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Complex.sq_norm (x i)

lemma euclid_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ euclid x := norm_nonneg _

lemma euclid_pos_of_ne_zero {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < euclid x := by
  unfold euclid
  refine norm_pos_iff.mpr fun h ↦ hx ?_
  ext i
  exact congr_fun (congr_arg WithLp.ofLp h) i

lemma euclid_star {n : ℕ} (x : Fin n → ℂ) : euclid (star x) = euclid x := by
  have hsq : euclid (star x) ^ 2 = euclid x ^ 2 := by
    rw [euclid_sq, euclid_sq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Complex.normSq_conj]
  nlinarith [euclid_nonneg (star x), euclid_nonneg x]

lemma euclid_smul {n : ℕ} (c : ℂ) (x : Fin n → ℂ) : euclid (c • x) = ‖c‖ * euclid x := by
  unfold euclid
  change ‖c • (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ = _
  rw [norm_smul]

lemma euclid_unitary_mulVec {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℂ) :
    euclid ((U : Mat n) *ᵥ x) = euclid x := by
  have hsq : euclid ((U : Mat n) *ᵥ x) ^ 2 = euclid x ^ 2 := by
    have hdot : star ((U : Mat n) *ᵥ x) ⬝ᵥ ((U : Mat n) *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff'.mp U.property, vecMul_one]
    have hre := congr_arg Complex.re hdot
    rw [euclid_sq, euclid_sq]
    have hvec : ∀ y : Fin n → ℂ, (star y ⬝ᵥ y).re = ∑ i : Fin n, Complex.normSq (y i) := fun y ↦ by
      simp only [dotProduct, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [Complex.normSq_apply]
    rw [← hvec, ← hvec, hre]
  nlinarith [euclid_nonneg ((U : Mat n) *ᵥ x), euclid_nonneg x]

lemma euclid_sub_add_sq {n : ℕ} (x y : Fin n → ℂ) :
    euclid (x - y) ^ 2 + euclid (x + y) ^ 2 = 2 * euclid x ^ 2 + 2 * euclid y ^ 2 := by
  rw [euclid_sq, euclid_sq, euclid_sq, euclid_sq, ← Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.sub_apply, Pi.add_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

def skewBlock (k : ℕ) : Mat (2 * k) :=
  Matrix.of fun i j ↦
    if i.val / 2 = j.val / 2 then
      if i.val % 2 = 0 ∧ j.val % 2 = 1 then -1
      else if i.val % 2 = 1 ∧ j.val % 2 = 0 then 1
      else 0
    else 0

lemma skewBlock_mem_unitary (k : ℕ) : skewBlock k ∈ Matrix.unitaryGroup (Fin (2 * k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  let partner : Fin (2 * k) :=
    ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by split_ifs <;> omega⟩
  have hsum :
      ∑ l : Fin (2 * k), skewBlock k i l * star (skewBlock k j l) =
        skewBlock k i partner * star (skewBlock k j partner) := by
    refine Finset.sum_eq_single partner (fun l _ hl ↦ ?_) (fun h ↦ (h (Finset.mem_univ _)).elim)
    have h0 : skewBlock k i l = 0 := by
      unfold skewBlock
      simp only [Matrix.of_apply]
      split_ifs with h1 h2 h3
      · exfalso; apply hl; ext; dsimp [partner]; split_ifs <;> omega
      · exfalso; apply hl; ext; dsimp [partner]; split_ifs <;> omega
      · rfl
      · rfl
    rw [h0, zero_mul]
  rw [hsum]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    unfold skewBlock
    simp only [Matrix.of_apply]
    have hp : i.val / 2 = partner.val / 2 := by dsimp [partner]; split_ifs <;> omega
    rw [if_pos hp]
    split_ifs with h2 h3
    · simp
    · simp
    · exfalso; dsimp [partner] at h2 h3; split_ifs at h2 h3 <;> omega
  · rw [if_neg hij]
    have h0 : skewBlock k j partner = 0 := by
      unfold skewBlock
      simp only [Matrix.of_apply]
      split_ifs with h1 h2 h3
      · exfalso; apply hij; ext; dsimp [partner] at h1 h2; split_ifs at h1 h2 <;> omega
      · exfalso; apply hij; ext; dsimp [partner] at h1 h3; split_ifs at h1 h3 <;> omega
      · rfl
      · rfl
    rw [h0, star_zero, mul_zero]

lemma skewBlock_antisymm (k : ℕ) (i j : Fin (2 * k)) :
    skewBlock k j i = -skewBlock k i j := by
  unfold skewBlock
  simp only [Matrix.of_apply]
  by_cases hdiv : i.val / 2 = j.val / 2
  · rw [if_pos hdiv.symm, if_pos hdiv]
    split_ifs <;> first | omega | ring
  · rw [if_neg (Ne.symm hdiv), if_neg hdiv, neg_zero]

lemma sqrt_two_mem_radii_even {n : ℕ} (heven : Even n) : Real.sqrt 2 ∈ radii n := by
  rcases heven with ⟨k, rfl⟩
  rw [show k + k = 2 * k by omega]
  refine ⟨Real.sqrt_nonneg 2, 1, ⟨skewBlock k, skewBlock_mem_unitary k⟩, fun x ↦ ?_⟩
  have hsq : euclid ((1 : Mat (2 * k)) *ᵥ x - skewBlock k *ᵥ star x) ^ 2 = 2 * euclid x ^ 2 := by
    have horth : star x ⬝ᵥ (skewBlock k *ᵥ star x) = 0 := by
      have hneg : star x ⬝ᵥ (skewBlock k *ᵥ star x) = -(star x ⬝ᵥ (skewBlock k *ᵥ star x)) := by
        simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [skewBlock_antisymm k i j]; ring
      linear_combination (1 / 2 : ℂ) * hneg
    have hunit : euclid (skewBlock k *ᵥ star x) = euclid x := by
      have h1 := euclid_unitary_mulVec ⟨skewBlock k, skewBlock_mem_unitary k⟩ (star x)
      rwa [euclid_star] at h1
    have hdot :
        star (x - skewBlock k *ᵥ star x) ⬝ᵥ (x - skewBlock k *ᵥ star x) =
          star x ⬝ᵥ x + star (skewBlock k *ᵥ star x) ⬝ᵥ (skewBlock k *ᵥ star x) := by
      have h1 : star (skewBlock k *ᵥ star x) ⬝ᵥ x = star (star x ⬝ᵥ (skewBlock k *ᵥ star x)) := by
        rw [star_dotProduct]
      rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, horth, star_zero]
      ring
    have hvec : ∀ y : Fin (2 * k) → ℂ, (star y ⬝ᵥ y).re = euclid y ^ 2 := fun y ↦ by
      rw [euclid_sq]; simp only [dotProduct, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ ↦ by simp [Complex.normSq_apply]
    rw [one_mulVec]
    have hre := congr_arg Complex.re hdot
    rw [Complex.add_re, hvec, hvec, hvec, hunit] at hre
    linarith
  have hrhs : (Real.sqrt 2 * euclid x) ^ 2 = 2 * euclid x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hle : euclid ((1 : Mat (2 * k)) *ᵥ x - skewBlock k *ᵥ star x) ^ 2 ≤
      (Real.sqrt 2 * euclid x) ^ 2 := by linarith
  change euclid ((1 : Mat (2 * k)) *ᵥ x - skewBlock k *ᵥ star x) ≤ Real.sqrt 2 * euclid x
  nlinarith [euclid_nonneg ((1 : Mat (2 * k)) *ᵥ x - skewBlock k *ᵥ star x),
    mul_nonneg (Real.sqrt_nonneg 2) (euclid_nonneg x)]

lemma two_mem_radii (n : ℕ) : (2 : ℝ) ∈ radii n := by
  refine ⟨by norm_num, 1, 1, fun x ↦ ?_⟩
  rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) = 1 from rfl, one_mulVec, one_mulVec]
  unfold euclid
  have h1 : ‖(WithLp.toLp 2 (x - star x) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ +
        ‖(WithLp.toLp 2 (star x) : EuclideanSpace ℂ (Fin n))‖ := norm_sub_le _ _
  have h2 : ‖(WithLp.toLp 2 (star x) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := euclid_star x
  linarith

lemma sqrt_two_le_of_mem_radii {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : r ∈ radii n) :
    Real.sqrt 2 ≤ r := by
  rcases hr with ⟨hr0, U, V, hUV⟩
  let W : Mat n := (U : Mat n)ᴴ * (V : Mat n)
  have hW : ∀ x : Fin n → ℂ, euclid (x - W *ᵥ star x) ≤ r * euclid x := fun x ↦ by
    have h1 := euclid_unitary_mulVec U (x - W *ᵥ star x)
    have h2 : (U : Mat n) *ᵥ (x - W *ᵥ star x) = (U : Mat n) *ᵥ x - (V : Mat n) *ᵥ star x := by
      rw [mulVec_sub, mulVec_mulVec]
      dsimp [W]
      rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.one_mul]
    rw [← h1, h2]; exact hUV x
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  have hx1 : euclid x = 1 := by
    have hsq : euclid x ^ 2 = 1 := by
      rw [euclid_sq]
      rw [Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj ↦ by simp [x, hj]) (fun h ↦ (h (Finset.mem_univ _)).elim)]
      simp [x]
    nlinarith [euclid_nonneg x]
  have hWstar : euclid (W *ᵥ star x) = 1 := by
    have h1 : euclid (W *ᵥ star x) = euclid ((V : Mat n) *ᵥ star x) := by
      have hU := euclid_unitary_mulVec U (W *ᵥ star x)
      have hmul : (U : Mat n) *ᵥ (W *ᵥ star x) = (V : Mat n) *ᵥ star x := by
        rw [mulVec_mulVec]; dsimp [W]
        rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
          Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.one_mul]
      rw [← hU, hmul]
    rw [h1, euclid_unitary_mulVec V, euclid_star, hx1]
  have hb1 : euclid (x - W *ᵥ star x) ≤ r := by simpa [hx1] using hW x
  have hb2 : euclid (x + W *ᵥ star x) ≤ r := by
    have hIx := hW (Complex.I • x)
    have h1 : Complex.I • x - W *ᵥ star (Complex.I • x) = Complex.I • (x + W *ᵥ star x) := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_smul,
        Complex.star_def, Complex.conj_I, mulVec_smul, neg_mul, sub_neg_eq_add]
      ring
    rw [h1, euclid_smul, euclid_smul, Complex.norm_I, one_mul, one_mul, hx1, mul_one] at hIx
    exact hIx
  have hpar := euclid_sub_add_sq x (W *ᵥ star x)
  rw [hx1, hWstar] at hpar
  have hr2 : 2 ≤ r ^ 2 := by
    nlinarith [euclid_nonneg (x - W *ᵥ star x), euclid_nonneg (x + W *ᵥ star x)]
  rw [Real.sqrt_le_iff]
  exact ⟨hr0, hr2⟩

lemma two_le_of_mem_radii_odd {n : ℕ} (hodd : Odd n) {r : ℝ} (hr : r ∈ radii n) :
    2 ≤ r := by
  rcases hr with ⟨hr0, U, V, hUV⟩
  let W : Mat n := (U : Mat n)ᴴ * (V : Mat n)
  have hW_mem : W ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    dsimp [W]
    have hU' : (U : Mat n)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, ← Matrix.star_eq_conjTranspose, star_star]
      exact Matrix.mem_unitaryGroup_iff'.mp U.property
    exact Submonoid.mul_mem _ hU' V.property
  have hW_right : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hW_mem
  have hW : ∀ x : Fin n → ℂ, euclid (x - W *ᵥ star x) ≤ r * euclid x := fun x ↦ by
    have h1 := euclid_unitary_mulVec U (x - W *ᵥ star x)
    have h2 : (U : Mat n) *ᵥ (x - W *ᵥ star x) = (U : Mat n) *ᵥ x - (V : Mat n) *ᵥ star x := by
      rw [mulVec_sub, mulVec_mulVec]
      dsimp [W]
      rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.one_mul]
    rw [← h1, h2]; exact hUV x
  let S : Mat n := W - Wᵀ
  have hS_skew : Sᵀ = -S := by dsimp [S]; ext i j; simp
  have hdet0 : S.det = 0 := by
    have h1 : S.det = (-S).det := by rw [← hS_skew, Matrix.det_transpose]
    rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow] at h1
    linear_combination (1 / 2 : ℂ) * h1
  obtain ⟨u, hu0, hSu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  have hWu : W *ᵥ u = Wᵀ *ᵥ u := sub_eq_zero.mp (by simpa [S, sub_mulVec] using hSu)
  let v : Fin n → ℂ := star u
  have hv0 : v ≠ 0 := fun h ↦ hu0 (by simpa [v] using congr_arg star h)
  have hWstar_v : W *ᵥ star (W *ᵥ star v) = v := by
    have hconj : star (W *ᵥ star v) = Wᴴ *ᵥ v := by
      have h1 : star (W *ᵥ u) = star (Wᵀ *ᵥ u) := congr_arg star hWu
      have h2 : star (Wᵀ *ᵥ u) = Wᴴ *ᵥ star u := by
        ext i; simp only [Pi.star_apply, mulVec, dotProduct, Matrix.transpose_apply,
          Matrix.conjTranspose_apply, star_sum, star_mul']
      simpa [v] using h1.trans h2
    rw [hconj, mulVec_mulVec, hW_right, one_mulVec]
  by_cases hx : v - W *ᵥ star v = 0
  · have hfix : W *ᵥ star v = v := (sub_eq_zero.mp hx).symm
    let y : Fin n → ℂ := Complex.I • v
    have hy0 : y ≠ 0 := smul_ne_zero Complex.I_ne_zero hv0
    have hWy : W *ᵥ star y = -y := by
      ext i
      simp only [y, star_smul, Complex.star_def, Complex.conj_I, mulVec_smul, hfix,
        Pi.smul_apply, Pi.neg_apply, smul_eq_mul, neg_mul]
    have hb := hW y
    rw [hWy, sub_neg_eq_add, show y + y = (2 : ℂ) • y by ext i; simp; ring, euclid_smul] at hb
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2] at hb
    exact le_of_mul_le_mul_right hb (euclid_pos_of_ne_zero hy0)
  · let x : Fin n → ℂ := v - W *ᵥ star v
    have hWx : W *ᵥ star x = -x := by
      dsimp [x]
      rw [star_sub, mulVec_sub, hWstar_v]; ext i; simp
    have hb := hW x
    rw [hWx, sub_neg_eq_add, show x + x = (2 : ℂ) • x by ext i; simp; ring, euclid_smul] at hb
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2] at hb
    exact le_of_mul_le_mul_right hb (euclid_pos_of_ne_zero hx)

end UnitaryAntiunitaryDistance

theorem OMA.solution : type_of% @OMA.S_mo_442655.main := by
  open UnitaryAntiunitaryDistance in
  intro n hn
  split_ifs with heven
  · exact ⟨sqrt_two_mem_radii_even heven, fun r hr ↦ sqrt_two_le_of_mem_radii hn hr⟩
  · exact ⟨two_mem_radii n, fun r hr ↦ two_le_of_mem_radii_odd (Nat.not_even_iff_odd.mp heven) hr⟩
