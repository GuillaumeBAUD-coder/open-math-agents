import OMAStatements.S_mo_294123

open OMA.S_mo_294123
open scoped Matrix

namespace HyperbolicWronskian

lemma cosh_star (z : ℂ) : Complex.cosh (star z) = star (Complex.cosh z) := by
  rw [Complex.cosh, Complex.cosh]
  simp only [Complex.star_def, map_div₀, map_add, map_ofNat, ← Complex.exp_conj, map_neg]

lemma sinh_star (z : ℂ) : Complex.sinh (star z) = star (Complex.sinh z) := by
  rw [Complex.sinh, Complex.sinh]
  simp only [Complex.star_def, map_div₀, map_sub, map_ofNat, ← Complex.exp_conj, map_neg]

lemma cosh_sq_sub_sinh_sq_eq_one (z : ℂ) :
    Complex.cosh z ^ 2 - Complex.sinh z ^ 2 = 1 := by
  rw [Complex.cosh, Complex.sinh, Complex.exp_neg]
  have hne : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  field_simp [hne]
  ring

lemma eval_map_conj (p : Polynomial ℂ) (z : ℂ) :
    (p.map (starRingEnd ℂ)).eval z = star (p.eval (star z)) := by
  have h := Polynomial.hom_eval₂ p (RingHom.id ℂ) (starRingEnd ℂ) (starRingEnd ℂ z)
  simp only [RingHom.comp_id, starRingEnd_self_apply, Polynomial.eval₂_eq_eval_map,
    Polynomial.map_id] at h
  exact h.symm

lemma det_eq_zero_of_not_injective {n : ℕ} (k : Fin n → ℂ) (x : ℝ)
    (hnot : ¬ Function.Injective (fun i ↦ k i ^ 2)) :
    (wronskian k x).det = 0 := by
  unfold Function.Injective at hnot
  push Not at hnot
  rcases hnot with ⟨i, j, hsq, hij⟩
  have hpm : k j = k i ∨ k j = -k i := sq_eq_sq_iff_eq_or_eq_neg.mp hsq.symm
  refine Matrix.det_zero_of_column_eq (i := Sum.inl i) (j := Sum.inl j) (by simp [hij]) ?_
  intro r
  cases r with
  | inl a =>
    dsimp only [wronskian]
    rcases hpm with h | h
    · rw [h]
    · rw [h, neg_sq, neg_mul, Complex.cosh_neg]
  | inr a =>
    dsimp only [wronskian]
    rcases hpm with h | h
    · rw [h]
    · rw [h, neg_sq, neg_mul, Complex.sinh_neg]
      ring

lemma det_ne_zero_of_injective {n : ℕ} (hn : 0 < n) (k : Fin n → ℂ)
    (hk_ne : ∀ i : Fin n, k i ≠ 0) (x : ℝ)
    (hinj : Function.Injective (fun i ↦ k i ^ 2)) :
    (wronskian k x).det ≠ 0 := by
  intro hdet
  have hdetT : (wronskian k x)ᵀ.det = 0 := by
    rw [Matrix.det_transpose, hdet]
  obtain ⟨w, hw_ne, hw_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  let P : Polynomial ℂ := ∑ a : Fin n, Polynomial.C (w (.inl a)) * Polynomial.X ^ (a : ℕ)
  let Q : Polynomial ℂ := ∑ a : Fin n, Polynomial.C (w (.inr a)) * Polynomial.X ^ (a : ℕ)
  let Pb : Polynomial ℂ := P.map (starRingEnd ℂ)
  let Qb : Polynomial ℂ := Q.map (starRingEnd ℂ)
  have hP_eval : ∀ z : ℂ, P.eval z = ∑ a : Fin n, w (.inl a) * z ^ (a : ℕ) := fun z ↦ by
    simp [P, Polynomial.eval_finsetSum]
  have hQ_eval : ∀ z : ℂ, Q.eval z = ∑ a : Fin n, w (.inr a) * z ^ (a : ℕ) := fun z ↦ by
    simp [Q, Polynomial.eval_finsetSum]
  have h1 : ∀ i : Fin n,
      P.eval (k i ^ 2) * Complex.cosh (k i * x) +
        Q.eval (k i ^ 2) * k i * Complex.sinh (k i * x) = 0 := fun i ↦ by
    have hi := congr_fun hw_mul (Sum.inl i)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
      Fintype.sum_sum_type] at hi
    dsimp only [wronskian] at hi
    rw [hP_eval, hQ_eval, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    have hL : ∑ a : Fin n, w (.inl a) * (k i ^ 2) ^ (a : ℕ) * Complex.cosh (k i * x) =
        ∑ a : Fin n, (k i ^ 2) ^ (a : ℕ) * Complex.cosh (k i * x) * w (.inl a) :=
      Finset.sum_congr rfl fun _ _ ↦ by ring
    have hR : ∑ a : Fin n, w (.inr a) * (k i ^ 2) ^ (a : ℕ) * k i * Complex.sinh (k i * x) =
        ∑ a : Fin n, (k i ^ 2) ^ (a : ℕ) * k i * Complex.sinh (k i * x) * w (.inr a) :=
      Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hL, hR]
    exact hi
  have h2 : ∀ i : Fin n,
      P.eval (star (k i) ^ 2) * Complex.sinh (star (k i) * x) +
        Q.eval (star (k i) ^ 2) * star (k i) * Complex.cosh (star (k i) * x) = 0 := fun i ↦ by
    have hi := congr_fun hw_mul (Sum.inr i)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
      Fintype.sum_sum_type] at hi
    dsimp only [wronskian] at hi
    rw [hP_eval, hQ_eval, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    have hL : ∑ a : Fin n, w (.inl a) * (star (k i) ^ 2) ^ (a : ℕ) * Complex.sinh (star (k i) * x) =
        ∑ a : Fin n, (star (k i) ^ 2) ^ (a : ℕ) * Complex.sinh (star (k i) * x) * w (.inl a) :=
      Finset.sum_congr rfl fun _ _ ↦ by ring
    have hR : ∑ a : Fin n, w (.inr a) * (star (k i) ^ 2) ^ (a : ℕ) * star (k i) *
          Complex.cosh (star (k i) * x) =
        ∑ a : Fin n, (star (k i) ^ 2) ^ (a : ℕ) * star (k i) *
          Complex.cosh (star (k i) * x) * w (.inr a) :=
      Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hL, hR]
    exact hi
  have h2c : ∀ i : Fin n,
      Pb.eval (k i ^ 2) * Complex.sinh (k i * x) +
        Qb.eval (k i ^ 2) * k i * Complex.cosh (k i * x) = 0 := fun i ↦ by
    have hc := congr_arg star (h2 i)
    have hx_star : star (x : ℂ) = (x : ℂ) := by simp
    have hsq_star : star (k i ^ 2) = star (k i) ^ 2 := by simp
    have hkx_star : star (star (k i) * (x : ℂ)) = k i * (x : ℂ) := by
      rw [star_mul', star_star, hx_star]
    simp only [star_zero, star_add, star_mul'] at hc
    rw [← cosh_star, ← sinh_star, hkx_star, star_star] at hc
    have hP_eq : star (P.eval (star (k i) ^ 2)) = Pb.eval (k i ^ 2) := by
      rw [eval_map_conj, hsq_star]
    have hQ_eq : star (Q.eval (star (k i) ^ 2)) = Qb.eval (k i ^ 2) := by
      rw [eval_map_conj, hsq_star]
    rw [hP_eq, hQ_eq] at hc
    linear_combination hc
  let R : Polynomial ℂ := P * Pb - Polynomial.X * Q * Qb
  have hR_root_k : ∀ i : Fin n, R.eval (k i ^ 2) = 0 := fun i ↦ by
    have hc1 := h1 i
    have hc2 := h2c i
    have hcs := cosh_sq_sub_sinh_sq_eq_one (k i * x)
    have heval : R.eval (k i ^ 2) =
        P.eval (k i ^ 2) * Pb.eval (k i ^ 2) - k i ^ 2 * Q.eval (k i ^ 2) * Qb.eval (k i ^ 2) := by
      simp [R]
    have hmul_c : R.eval (k i ^ 2) * Complex.cosh (k i * x) = 0 := by
      rw [heval]
      linear_combination Pb.eval (k i ^ 2) * hc1 - k i * Q.eval (k i ^ 2) * hc2
    have hmul_s : R.eval (k i ^ 2) * Complex.sinh (k i * x) = 0 := by
      rw [heval]
      linear_combination P.eval (k i ^ 2) * hc2 - k i * Qb.eval (k i ^ 2) * hc1
    linear_combination Complex.cosh (k i * x) * hmul_c - Complex.sinh (k i * x) * hmul_s -
      R.eval (k i ^ 2) * hcs
  have hR_conj : ∀ z : ℂ, R.eval (star z) = star (R.eval z) := fun z ↦ by
    simp only [R, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      star_sub, star_mul']
    have h1' : Pb.eval (star z) = star (P.eval z) := by
      rw [eval_map_conj, star_star]
    have h2' : Qb.eval (star z) = star (Q.eval z) := by
      rw [eval_map_conj, star_star]
    have h3' : star (Pb.eval z) = P.eval (star z) := by
      rw [eval_map_conj, star_star]
    have h4' : star (Qb.eval z) = Q.eval (star z) := by
      rw [eval_map_conj, star_star]
    rw [h1', h2', h3', h4']
    ring
  have hR_root_conj : ∀ i : Fin n, R.eval (star (k i ^ 2)) = 0 := fun i ↦ by
    rw [hR_conj, hR_root_k i, star_zero]
  have hPQ_vanish : ∀ i j : Fin n, k i ^ 2 = star (k j ^ 2) →
      P.eval (k i ^ 2) = 0 ∧ Q.eval (k i ^ 2) = 0 := fun i j hij ↦ by
    have hsq : star (k j) ^ 2 = k i ^ 2 := by
      simpa using hij.symm
    have hpm : star (k j) = k i ∨ star (k j) = -k i := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    have h2' : P.eval (k i ^ 2) * Complex.sinh (k i * x) +
        Q.eval (k i ^ 2) * k i * Complex.cosh (k i * x) = 0 := by
      have hj := h2 j
      rw [hsq] at hj
      rcases hpm with h | h
      · rw [h] at hj; exact hj
      · rw [h, neg_mul, Complex.sinh_neg, Complex.cosh_neg] at hj
        linear_combination -hj
    have hcs := cosh_sq_sub_sinh_sq_eq_one (k i * x)
    have hP0 : P.eval (k i ^ 2) = 0 := by
      linear_combination Complex.cosh (k i * x) * h1 i - Complex.sinh (k i * x) * h2' -
        P.eval (k i ^ 2) * hcs
    have hQk0 : Q.eval (k i ^ 2) * k i = 0 := by
      linear_combination Complex.cosh (k i * x) * h2' - Complex.sinh (k i * x) * h1 i -
        Q.eval (k i ^ 2) * k i * hcs
    exact ⟨hP0, (mul_eq_zero.mp hQk0).resolve_right (hk_ne i)⟩
  have hR_double : ∀ i j : Fin n, k i ^ 2 = star (k j ^ 2) →
      (Polynomial.X - Polynomial.C (k i ^ 2)) ^ 2 ∣ R := fun i j hij ↦ by
    have ⟨hP1, hQ1⟩ := hPQ_vanish i j hij
    have hji : k j ^ 2 = star (k i ^ 2) := by
      have := congr_arg star hij
      simpa using this.symm
    have ⟨hP2, hQ2⟩ := hPQ_vanish j i hji
    have hPb1 : Pb.eval (k i ^ 2) = 0 := by
      rw [eval_map_conj, ← hji, hP2, star_zero]
    have hQb1 : Qb.eval (k i ^ 2) = 0 := by
      rw [eval_map_conj, ← hji, hQ2, star_zero]
    have hdP : Polynomial.X - Polynomial.C (k i ^ 2) ∣ P := Polynomial.dvd_iff_isRoot.mpr hP1
    have hdPb : Polynomial.X - Polynomial.C (k i ^ 2) ∣ Pb := Polynomial.dvd_iff_isRoot.mpr hPb1
    have hdQ : Polynomial.X - Polynomial.C (k i ^ 2) ∣ Q := Polynomial.dvd_iff_isRoot.mpr hQ1
    have hdQb : Polynomial.X - Polynomial.C (k i ^ 2) ∣ Qb := Polynomial.dvd_iff_isRoot.mpr hQb1
    have hd1 : (Polynomial.X - Polynomial.C (k i ^ 2)) ^ 2 ∣ P * Pb := by
      rw [sq]
      exact mul_dvd_mul hdP hdPb
    have hd2 : (Polynomial.X - Polynomial.C (k i ^ 2)) ^ 2 ∣ Polynomial.X * Q * Qb := by
      rw [mul_assoc, sq]
      exact dvd_mul_of_dvd_right (mul_dvd_mul hdQ hdQb) Polynomial.X
    exact dvd_sub hd1 hd2
  have hP_deg : P.natDegree ≤ n - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
  have hQ_deg : Q.natDegree ≤ n - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
  have hPb_deg : Pb.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective (starRingEnd ℂ)) P
  have hQb_deg : Qb.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective (starRingEnd ℂ)) Q
  have hR_deg : R.natDegree ≤ 2 * n - 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by omega)
    · have hXQ : (Polynomial.X * Q).natDegree ≤ n :=
        Polynomial.natDegree_mul_le.trans (by simp only [Polynomial.natDegree_X]; omega)
      exact Polynomial.natDegree_mul_le.trans (by omega)
  have hR_zero : R = 0 := by
    by_contra hR_ne
    let M1 : Multiset ℂ := (Finset.univ : Finset (Fin n)).val.map (fun i ↦ k i ^ 2)
    let M2 : Multiset ℂ := (Finset.univ : Finset (Fin n)).val.map (fun i ↦ star (k i ^ 2))
    let M : Multiset ℂ := M1 + M2
    have hM1_nd : M1.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
    have hM2_nd : M2.Nodup :=
      Multiset.Nodup.map (star_injective.comp hinj) Finset.univ.nodup
    have hM_le : M ≤ R.roots := by
      rw [Multiset.le_iff_count]
      intro z
      rw [Polynomial.count_roots, Multiset.count_add]
      have hc1 : M1.count z ≤ 1 := Multiset.nodup_iff_count_le_one.mp hM1_nd z
      have hc2 : M2.count z ≤ 1 := Multiset.nodup_iff_count_le_one.mp hM2_nd z
      by_cases h1pos : M1.count z = 0
      · by_cases h2pos : M2.count z = 0
        · omega
        · have hz2 : z ∈ M2 := Multiset.count_pos.mp (by omega)
          rcases Multiset.mem_map.mp hz2 with ⟨i, _, rfl⟩
          have hpos : 0 < R.rootMultiplicity (star (k i ^ 2)) :=
            (Polynomial.rootMultiplicity_pos hR_ne).mpr (hR_root_conj i)
          omega
      · by_cases h2pos : M2.count z = 0
        · have hz1 : z ∈ M1 := Multiset.count_pos.mp (by omega)
          rcases Multiset.mem_map.mp hz1 with ⟨i, _, rfl⟩
          have hpos : 0 < R.rootMultiplicity (k i ^ 2) :=
            (Polynomial.rootMultiplicity_pos hR_ne).mpr (hR_root_k i)
          omega
        · have hz1 : z ∈ M1 := Multiset.count_pos.mp (by omega)
          have hz2 : z ∈ M2 := Multiset.count_pos.mp (by omega)
          rcases Multiset.mem_map.mp hz1 with ⟨i, _, rfl⟩
          rcases Multiset.mem_map.mp hz2 with ⟨j, _, hjz⟩
          have h2le : 2 ≤ R.rootMultiplicity (k i ^ 2) :=
            (Polynomial.le_rootMultiplicity_iff hR_ne).mpr (hR_double i j hjz.symm)
          omega
    have hM_card : M.card = 2 * n := by
      simp [M, M1, M2, two_mul]
    have hcard_le : 2 * n ≤ R.natDegree := by
      calc
        2 * n = M.card := hM_card.symm
        _ ≤ R.roots.card := Multiset.card_le_card hM_le
        _ ≤ R.natDegree := Polynomial.card_roots' R
    omega
  have hEq : P * Pb = Polynomial.X * Q * Qb := sub_eq_zero.mp hR_zero
  have hP_zero : P = 0 := by
    by_contra hP_ne
    have hPb_ne : Pb ≠ 0 := by
      rwa [ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective (starRingEnd ℂ))]
    have hQ_ne : Q ≠ 0 := by
      intro hQ0
      rw [hQ0, mul_zero, zero_mul] at hEq
      exact mul_ne_zero hP_ne hPb_ne hEq
    have hQb_ne : Qb ≠ 0 := by
      rwa [ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective (starRingEnd ℂ))]
    have hdegL : (P * Pb).natDegree = 2 * P.natDegree := by
      rw [Polynomial.natDegree_mul hP_ne hPb_ne, hPb_deg]
      omega
    have hdegR : (Polynomial.X * Q * Qb).natDegree = 2 * Q.natDegree + 1 := by
      rw [Polynomial.natDegree_mul (mul_ne_zero Polynomial.X_ne_zero hQ_ne) hQb_ne,
        Polynomial.natDegree_mul Polynomial.X_ne_zero hQ_ne, Polynomial.natDegree_X, hQb_deg]
      omega
    rw [hEq] at hdegL
    omega
  have hQ_zero : Q = 0 := by
    by_contra hQ_ne
    have hQb_ne : Qb ≠ 0 := by
      rwa [ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective (starRingEnd ℂ))]
    rw [hP_zero, zero_mul] at hEq
    exact mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ_ne) hQb_ne hEq.symm
  apply hw_ne
  ext r
  cases r with
  | inl a =>
    have hc := congr_arg (fun p : Polynomial ℂ ↦ p.coeff (a : ℕ)) hP_zero
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single a] at hc
    · simpa using hc
    · intro b _ hba
      rw [if_neg (by intro h; exact hba (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ a) h
  | inr a =>
    have hc := congr_arg (fun p : Polynomial ℂ ↦ p.coeff (a : ℕ)) hQ_zero
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single a] at hc
    · simpa using hc
    · intro b _ hba
      rw [if_neg (by intro h; exact hba (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ a) h

end HyperbolicWronskian

theorem OMA.solution : type_of% @OMA.S_mo_294123.main := by
  intro n hn k hk x
  refine ⟨fun hdet ↦ ?_, fun hinj ↦ ?_⟩
  · by_contra hnot
    exact hdet (HyperbolicWronskian.det_eq_zero_of_not_injective k x hnot)
  · refine HyperbolicWronskian.det_ne_zero_of_injective hn k (fun i ↦ ?_) x hinj
    intro h0
    exact (hk i).1 (by simp [h0])
