import OMAStatements.S_mo_462055

open OMA.S_mo_462055 Matrix Filter Topology

namespace SchoenbergGaussianGram

lemma posSemidef_ones (n : ℕ) : (Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ))).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun v ↦ ?_)
  · ext i j; simp
  · simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, one_mul]
    have : ∑ i : Fin n, v i * ∑ j : Fin n, v j = (∑ i : Fin n, v i) ^ 2 := by
      rw [sq, Finset.sum_mul]
    rw [this]; exact sq_nonneg _

lemma posSemidef_hadamardPow {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) :
    ∀ k : ℕ, (Matrix.of (fun i j ↦ G i j ^ k)).PosSemidef
  | 0 => by simpa using posSemidef_ones n
  | k + 1 => by
    have hprev := posSemidef_hadamardPow hG k
    have heq : Matrix.of (fun i j ↦ G i j ^ (k + 1)) = Matrix.of (fun i j ↦ G i j ^ k) ⊙ G := by
      ext i j; simp [hadamard_apply, pow_succ]
    rw [heq]
    exact hprev.hadamard hG

lemma posSemidef_entrywiseExp {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) :
    (Matrix.of (fun i j ↦ Real.exp (G i j))).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun v ↦ ?_)
  · ext i j
    have hsym : G j i = G i j := congr_fun (congr_fun hG.isHermitian i) j
    simp [hsym]
  · have hpart : ∀ N : ℕ,
        0 ≤ ∑ i : Fin n, v i * ∑ j : Fin n,
          (∑ k ∈ Finset.range N, G i j ^ k / (k.factorial : ℝ)) * v j := fun N ↦ by
      have hswap :
          (∑ i : Fin n, v i * ∑ j : Fin n,
            (∑ k ∈ Finset.range N, G i j ^ k / (k.factorial : ℝ)) * v j) =
          ∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ *
            (star v ⬝ᵥ (Matrix.of (fun i j ↦ G i j ^ k)) *ᵥ v) := by
        simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum,
          Finset.sum_mul, div_eq_inv_mul]
        calc
          ∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ Finset.range N, v i * ((k.factorial : ℝ)⁻¹ * G i j ^ k * v j) =
              ∑ i : Fin n, ∑ k ∈ Finset.range N, ∑ j : Fin n, v i * ((k.factorial : ℝ)⁻¹ * G i j ^ k * v j) :=
            Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
          _ = ∑ k ∈ Finset.range N, ∑ i : Fin n, ∑ j : Fin n, v i * ((k.factorial : ℝ)⁻¹ * G i j ^ k * v j) :=
            Finset.sum_comm
          _ = ∑ k ∈ Finset.range N, ∑ i : Fin n, ∑ j : Fin n,
                (k.factorial : ℝ)⁻¹ * (v i * (G i j ^ k * v j)) :=
            Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hswap]
      refine Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) ?_
      exact (posSemidef_iff_dotProduct_mulVec.mp (posSemidef_hadamardPow hG k)).2 v
    have htend_entry : ∀ i j : Fin n,
        Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, G i j ^ k / (k.factorial : ℝ))
          atTop (𝓝 (Real.exp (G i j))) := fun i j ↦ by
      have hs : HasSum (fun k : ℕ ↦ G i j ^ k / (k.factorial : ℝ)) (Real.exp (G i j)) := by
        simpa [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (x := G i j))
      exact hs.tendsto_sum_nat
    have htend :
        Tendsto (fun N : ℕ ↦ ∑ i : Fin n, v i * ∑ j : Fin n,
          (∑ k ∈ Finset.range N, G i j ^ k / (k.factorial : ℝ)) * v j)
          atTop (𝓝 (star v ⬝ᵥ (Matrix.of (fun i j ↦ Real.exp (G i j))) *ᵥ v)) := by
      simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply]
      refine tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.mul ?_
      refine tendsto_finsetSum _ fun j _ ↦ (htend_entry i j).mul tendsto_const_nhds
    exact ge_of_tendsto' htend hpart

lemma gaussian_imp_pw_posSemidef {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hG : Gaussian C)
    {t : ℝ} (ht : 0 < t) : (pw C t).PosSemidef := by
  rcases hG with ⟨x, hx⟩
  let X : Matrix (Fin n) (Fin n) ℝ := Matrix.of x
  let G : Matrix (Fin n) (Fin n) ℝ := (2 * t) • (X * Xᵀ)
  have hGram : G.PosSemidef := by
    have hXX : (X * Xᵀ).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self Xᵀ
    exact hXX.smul (by positivity)
  have hexp : (Matrix.of (fun i j ↦ Real.exp (G i j))).PosSemidef := posSemidef_entrywiseExp hGram
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun v ↦ ?_)
  · ext i j
    simp only [conjTranspose_apply, star_trivial, pw, Matrix.of_apply, hx]
    congr 3; refine Finset.sum_congr rfl fun l _ ↦ by ring
  · let d : Fin n → ℝ := fun i ↦ Real.exp (-t * ∑ l : Fin n, x i l ^ 2)
    have hquad :
        star v ⬝ᵥ (pw C t) *ᵥ v =
          star (fun i ↦ d i * v i) ⬝ᵥ (Matrix.of (fun i j ↦ Real.exp (G i j))) *ᵥ
            (fun i ↦ d i * v i) := by
      simp only [star_trivial, dotProduct, mulVec, pw, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      have hCij : C i j ^ t = d i * d j * Real.exp (G i j) := by
        rw [hx i j, ← Real.exp_mul]
        dsimp [d, G, X]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.mul_sum]
        have hsum :
            -(∑ l : Fin n, (x i l - x j l) ^ 2) * t =
              ∑ l : Fin n, (-t * x i l ^ 2 + -t * x j l ^ 2 + 2 * t * (x i l * x j l)) := by
          rw [← Finset.sum_neg_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ ↦ by ring
        rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [hCij]; ring
    rw [hquad]
    exact (posSemidef_iff_dotProduct_mulVec.mp hexp).2 (fun i ↦ d i * v i)

lemma anch_posSemidef {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hsym : C.IsSymm) (hdiag : ∀ i, C i i = 1) (hpos : ∀ i j, 0 < C i j)
    (hpw : ∀ t : ℝ, 0 < t → (pw C t).PosSemidef) (a : Fin n) :
    (anch C a).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun v ↦ ?_)
  · ext i j
    have hij : C j i = C i j := hsym.apply i j
    have hia : C a i = C i a := hsym.apply i a
    have hja : C j a = C a j := hsym.apply a j
    simp only [conjTranspose_apply, star_trivial, anch, Matrix.of_apply, hij, hia, hja]
    ring
  · let s : ℝ := ∑ k : Fin n, v k
    let u : Fin n → ℝ := fun i ↦ if i = a then v i - s else v i
    have husum : ∑ i : Fin n, u i = 0 := by
      have hsplit : ∑ i : Fin n, u i = (∑ i : Fin n, v i) - s := by
        dsimp [u]
        have : ∀ i : Fin n, (if i = a then v i - s else v i) = v i - (if i = a then s else 0) :=
          fun i ↦ by split_ifs <;> ring
        simp_rw [this]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a (fun _ ↦ s)]
        simp
      rw [hsplit]; dsimp [s]; ring
    have hnonneg : ∀ t : ℝ, 0 < t →
        0 ≤ ∑ i : Fin n, u i * ∑ j : Fin n, ((C i j ^ t - 1) / t) * u j := fun t ht ↦ by
      have hpsd := (posSemidef_iff_dotProduct_mulVec.mp (hpw t ht)).2 u
      simp only [star_trivial, dotProduct, mulVec, pw, Matrix.of_apply] at hpsd
      have hzero : ∑ i : Fin n, u i * ∑ j : Fin n, (1 : ℝ) * u j = 0 := by
        simp [husum]
      have hrew :
          (∑ i : Fin n, u i * ∑ j : Fin n, ((C i j ^ t - 1) / t) * u j) =
            ((∑ i : Fin n, u i * ∑ j : Fin n, C i j ^ t * u j) -
              (∑ i : Fin n, u i * ∑ j : Fin n, (1 : ℝ) * u j)) / t := by
        simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hrew, hzero, sub_zero]
      exact div_nonneg hpsd ht.le
    have htend_log : ∀ i j : Fin n,
        Tendsto (fun t : ℝ ↦ (C i j ^ t - 1) / t) (𝓝[>] 0) (𝓝 (Real.log (C i j))) := fun i j ↦ by
      have hd : HasDerivAt (fun t : ℝ ↦ Real.exp (Real.log (C i j) * t)) (Real.log (C i j)) 0 := by
        have h := ((hasDerivAt_id (0 : ℝ)).const_mul (Real.log (C i j))).exp
        simpa using h
      simp_rw [Real.rpow_def_of_pos (hpos i j)]
      have hslope := hd.tendsto_slope_zero_right
      simpa [slope_def_field, div_eq_inv_mul] using hslope
    have htend :
        Tendsto (fun t : ℝ ↦ ∑ i : Fin n, u i * ∑ j : Fin n, ((C i j ^ t - 1) / t) * u j)
          (𝓝[>] 0) (𝓝 (∑ i : Fin n, u i * ∑ j : Fin n, Real.log (C i j) * u j)) := by
      refine tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.mul ?_
      refine tendsto_finsetSum _ fun j _ ↦ (htend_log i j).mul tendsto_const_nhds
    have hlog_nonneg : 0 ≤ ∑ i : Fin n, u i * ∑ j : Fin n, Real.log (C i j) * u j :=
      ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht ↦ hnonneg t ht)
    have hlog_aa : Real.log (C a a) = 0 := by rw [hdiag a, Real.log_one]
    have hident :
        ∑ i : Fin n, u i * ∑ j : Fin n, Real.log (C i j) * u j =
          2 * (star v ⬝ᵥ (anch C a) *ᵥ v) := by
      have h1 :
          ∑ i : Fin n, u i * ∑ j : Fin n, Real.log (C i j) * u j =
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j)) -
            s * (∑ j : Fin n, v j * Real.log (C a j)) -
            s * (∑ i : Fin n, v i * Real.log (C i a)) +
            s * s * Real.log (C a a) := by
        have hu_eq : ∀ i : Fin n, u i = v i - if i = a then s else 0 := fun i ↦ by
          dsimp [u]; split_ifs <;> ring
        have hstep :
            ∑ i : Fin n, u i * ∑ j : Fin n, Real.log (C i j) * u j =
              ∑ i : Fin n, ∑ j : Fin n,
                (v i * v j * Real.log (C i j) -
                  (if i = a then s * (v j * Real.log (C i j)) else 0) -
                  (if j = a then s * (v i * Real.log (C i j)) else 0) +
                  (if i = a then (if j = a then s * s * Real.log (C i j) else 0) else 0)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hu_eq i, hu_eq j]; split_ifs <;> ring
        rw [hstep]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hterm1 : (∑ i : Fin n, ∑ j : Fin n, if i = a then s * (v j * Real.log (C i j)) else 0) =
            s * ∑ j : Fin n, v j * Real.log (C a j) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_ite_eq' Finset.univ a (fun i ↦ s * (v _ * Real.log (C i _)))]
          simp [Finset.mul_sum]
        have hterm2 : (∑ i : Fin n, ∑ j : Fin n, if j = a then s * (v i * Real.log (C i j)) else 0) =
            s * ∑ i : Fin n, v i * Real.log (C i a) := by
          simp_rw [Finset.sum_ite_eq' Finset.univ a (fun j ↦ s * (v _ * Real.log (C _ j)))]
          simp [Finset.mul_sum]
        have hterm3 : (∑ i : Fin n, ∑ j : Fin n,
            if i = a then (if j = a then s * s * Real.log (C i j) else 0) else 0) =
            s * s * Real.log (C a a) := by
          simp
        rw [hterm1, hterm2, hterm3]
      have h2 :
          2 * (star v ⬝ᵥ (anch C a) *ᵥ v) =
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j)) -
            s * (∑ j : Fin n, v j * Real.log (C a j)) -
            s * (∑ i : Fin n, v i * Real.log (C i a)) := by
        have hstep :
            2 * (star v ⬝ᵥ (anch C a) *ᵥ v) =
              ∑ i : Fin n, ∑ j : Fin n,
                (v i * v j * Real.log (C i j) - v i * v j * Real.log (C a j) -
                  v i * v j * Real.log (C i a)) := by
          simp only [star_trivial, dotProduct, mulVec, anch, Matrix.of_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
        rw [hstep]
        simp only [Finset.sum_sub_distrib]
        have hs1 : ∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C a j) =
            s * ∑ j : Fin n, v j * Real.log (C a j) := by
          dsimp [s]; rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ by ring
        have hs2 : ∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i a) =
            s * ∑ i : Fin n, v i * Real.log (C i a) := by
          rw [Finset.sum_comm]; dsimp [s]; rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ by ring
        rw [hs1, hs2]
      rw [h1, hlog_aa, mul_zero, add_zero, h2]
    linarith

lemma posSemidef_imp_gaussian {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hsym : C.IsSymm) (hdiag : ∀ i, C i i = 1) (hpos : ∀ i j, 0 < C i j)
    (hpw : ∀ t : ℝ, 0 < t → (pw C t).PosSemidef) : Gaussian C := by
  by_cases hn : n = 0
  · subst hn; exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  · let a : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let M : Matrix (Fin n) (Fin n) ℝ := anch C a
    have hM : M.PosSemidef := anch_posSemidef hsym hdiag hpos hpw a
    have hH : M.IsHermitian := hM.isHermitian
    let U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    let lam : Fin n → ℝ := hH.eigenvalues
    let x : Fin n → Fin n → ℝ := fun i l ↦ Real.sqrt (lam l) * U i l
    have hspec : ∀ i j : Fin n, M i j = ∑ l : Fin n, x i l * x j l := fun i j ↦ by
      have hst := congr_fun (congr_fun hH.spectral_theorem i) j
      simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
        Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] at hst
      rw [hst]
      trans (∑ l : Fin n, U i l * lam l * U j l)
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
        rfl
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        dsimp [x]
        have hsq : Real.sqrt (lam l) * Real.sqrt (lam l) = lam l :=
          Real.mul_self_sqrt (hM.eigenvalues_nonneg l)
        calc
          U i l * lam l * U j l = (Real.sqrt (lam l) * Real.sqrt (lam l)) * (U i l * U j l) := by
            rw [hsq]; ring
          _ = Real.sqrt (lam l) * U i l * (Real.sqrt (lam l) * U j l) := by ring
    refine ⟨x, fun i j ↦ ?_⟩
    have hdist : ∑ l : Fin n, (x i l - x j l) ^ 2 = M i i + M j j - 2 * M i j := by
      have hexp : ∀ l : Fin n, (x i l - x j l) ^ 2 = x i l * x i l + x j l * x j l - 2 * (x i l * x j l) :=
        fun l ↦ by ring
      simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hspec]
    have hMii : M i i = -Real.log (C i a) := by
      have hia : C a i = C i a := hsym.apply i a
      dsimp [M, anch]; rw [hdiag i, Real.log_one, hia]; ring
    have hMjj : M j j = -Real.log (C a j) := by
      have hja : C j a = C a j := hsym.apply a j
      dsimp [M, anch]; rw [hdiag j, Real.log_one, hja]; ring
    have hneg : -(∑ l : Fin n, (x i l - x j l) ^ 2) = Real.log (C i j) := by
      rw [hdist, hMii, hMjj]
      dsimp [M, anch]
      ring
    rw [hneg, Real.exp_log (hpos i j)]

end SchoenbergGaussianGram

theorem OMA.solution : type_of% @OMA.S_mo_462055.main := by
  open SchoenbergGaussianGram in
  intro n C
  constructor
  · intro hG
    rcases hG with ⟨x, hx⟩
    refine ⟨?_, fun i ↦ ?_, fun i j ↦ ?_, fun t ht ↦ gaussian_imp_pw_posSemidef ⟨x, hx⟩ ht⟩
    · ext i j; simp only [Matrix.transpose_apply, hx]
      congr 2; refine Finset.sum_congr rfl fun l _ ↦ by ring
    · simp [hx]
    · rw [hx i j]; exact Real.exp_pos _
  · rintro ⟨hsym, hdiag, hpos, hpw⟩
    exact posSemidef_imp_gaussian hsym hdiag hpos hpw
