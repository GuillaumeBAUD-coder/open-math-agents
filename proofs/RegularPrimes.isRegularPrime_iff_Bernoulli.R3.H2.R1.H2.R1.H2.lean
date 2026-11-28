import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1

-- Step RegularPrimes.isRegularPrime_iff_Bernoulli.R3.H2.R1.H2.R1.H2:
-- hypothesis H2 of reduction RegularPrimes.isRegularPrime_iff_Bernoulli.R3.H2.R1.H2.R1
-- Credit: @sukhman31
-- H2 := ∀ (p : ℕ) [Fact p.Prime], 3 ≤ p →
--   (Matrix.det (fun j a : Fin ((p - 3) / 2) =>
--     ((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1)) ≠ 0

private lemma lowerOnes_det {R : Type*} [CommRing R] (m : ℕ) :
    Matrix.det (fun j k : Fin m => if k ≤ j then (1 : R) else 0) = 1 := by
  have htri : Matrix.BlockTriangular (fun j k : Fin m => if k ≤ j then (1 : R) else 0)
      (OrderDual.toDual : Fin m → (Fin m)ᵒᵈ) := by
    intro j k hjk
    have hnot : ¬ k ≤ j := not_le.mpr hjk
    simp [hnot]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp

private lemma geom_sum_fin {R : Type*} [CommRing R] (m : ℕ) (j : Fin m) (x : R) :
    (∑ k : Fin m, (if k ≤ j then (1 : R) else 0) * (x ^ k.val * (x - 1))) =
      x ^ (j.val + 1) - 1 := by
  have h1 :
      (∑ k : Fin m, (if k ≤ j then (1 : R) else 0) * (x ^ k.val * (x - 1))) =
        (∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), x ^ k.val) * (x - 1) := by
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [h1]
  have h2 :
      (∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), x ^ k.val) =
        ∑ r ∈ Finset.range (j.val + 1), x ^ r := by
    refine Finset.sum_nbij (fun k : Fin m => k.val) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
      exact Nat.lt_succ_of_le hk
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_range] at hr
      refine ⟨⟨r, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.le_of_lt_succ hr
    · intro k _
      rfl
  rw [h2, geom_sum_mul]

private lemma sq_node_ne_one {p : ℕ} [Fact p.Prime] (a : Fin ((p - 3) / 2)) :
    (((a.val + 2 : ℕ) : ZMod p) ^ 2) - 1 ≠ 0 := by
  intro h
  have hfac :
      (((a.val + 2 : ℕ) : ZMod p) - 1) * (((a.val + 2 : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hfac with hsub | hadd
  · have hcast : ((a.val + 1 : ℕ) : ZMod p) = 0 := by
      push_cast at hsub ⊢
      linear_combination hsub
    have hdvd : p ∣ a.val + 1 := (ZMod.natCast_eq_zero_iff (a.val + 1) p).mp hcast
    have hle : p ≤ a.val + 1 := Nat.le_of_dvd (by omega) hdvd
    have ha := a.isLt
    omega
  · have hcast : ((a.val + 3 : ℕ) : ZMod p) = 0 := by
      push_cast at hadd ⊢
      linear_combination hadd
    have hdvd : p ∣ a.val + 3 := (ZMod.natCast_eq_zero_iff (a.val + 3) p).mp hcast
    have hle : p ≤ a.val + 3 := Nat.le_of_dvd (by omega) hdvd
    have ha := a.isLt
    omega

private lemma sq_node_sub_ne_zero {p : ℕ} [Fact p.Prime] {a b : Fin ((p - 3) / 2)}
    (hab : a < b) :
    (((b.val + 2 : ℕ) : ZMod p) ^ 2) - (((a.val + 2 : ℕ) : ZMod p) ^ 2) ≠ 0 := by
  intro h
  have hfac :
      (((b.val + 2 : ℕ) : ZMod p) - ((a.val + 2 : ℕ) : ZMod p)) *
      (((b.val + 2 : ℕ) : ZMod p) + ((a.val + 2 : ℕ) : ZMod p)) = 0 := by
    linear_combination h
  have halt : a.val < b.val := hab
  have hb : b.val < (p - 3) / 2 := b.isLt
  rcases mul_eq_zero.mp hfac with hsub | hadd
  · have hcast : ((b.val - a.val : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub halt.le]
      push_cast at hsub
      linear_combination hsub
    have hdvd : p ∣ b.val - a.val := (ZMod.natCast_eq_zero_iff (b.val - a.val) p).mp hcast
    have hle : p ≤ b.val - a.val := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hcast : ((a.val + b.val + 4 : ℕ) : ZMod p) = 0 := by
      push_cast at hadd ⊢
      linear_combination hadd
    have hdvd : p ∣ a.val + b.val + 4 := (ZMod.natCast_eq_zero_iff (a.val + b.val + 4) p).mp hcast
    have hle : p ≤ a.val + b.val + 4 := Nat.le_of_dvd (by omega) hdvd
    omega

theorem OMA.solution :
    OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H2 := by
  intro p hp _
  let m := (p - 3) / 2
  let x : Fin m → ZMod p := fun a => ((a.val + 2 : ℕ) : ZMod p) ^ 2
  let L : Matrix (Fin m) (Fin m) (ZMod p) := fun j k => if k ≤ j then 1 else 0
  let V : Matrix (Fin m) (Fin m) (ZMod p) := (Matrix.vandermonde x).transpose
  let D : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.diagonal (fun a => x a - 1)
  have hM : (fun j a : Fin m => ((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1) =
      L * (V * D) := by
    ext j a
    rw [Matrix.mul_apply]
    simp only [L, V, D, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [geom_sum_fin m j (x a)]
    simp only [x, ← pow_mul]
  rw [hM, Matrix.det_mul, Matrix.det_mul, lowerOnes_det, one_mul]
  have hV : V.det ≠ 0 := by
    simp only [V, Matrix.det_transpose, Matrix.det_vandermonde]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact sq_node_sub_ne_zero (Finset.mem_Ioi.mp hj)
  have hD : D.det ≠ 0 := by
    simp only [D, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro a _
    exact sq_node_ne_one a
  exact mul_ne_zero hV hD
