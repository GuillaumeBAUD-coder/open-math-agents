import OMAStatements.S_oeis_a128381

namespace OMA.S_oeis_a128381

open PowerSeries



lemma coeff_mul_one' (f g : PowerSeries ℤ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma coeff_mul_two' (f g : PowerSeries ℤ) :
    coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma pow1 (n : ℕ) :
    coeff 0 ((1 - (X : PowerSeries ℤ)) ^ n) = 1 ∧
    coeff 1 ((1 - (X : PowerSeries ℤ)) ^ n) = -(n : ℤ) ∧
    coeff 2 ((1 - (X : PowerSeries ℤ)) ^ n) = (n.choose 2 : ℤ) := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e : (1 - (X : PowerSeries ℤ)) ^ (n + 1) = (1 - X) ^ n - (1 - X) ^ n * X ^ 1 := by ring
    rw [e]
    simp only [map_sub, coeff_mul_X_pow']
    refine ⟨?_, ?_, ?_⟩
    · norm_num [h0]
    · norm_num [h0, h1]
      ring
    · norm_num [h1, h2, Nat.choose_succ_succ]
      ring

lemma pow2 (n : ℕ) :
    coeff 0 ((1 - (X : PowerSeries ℤ) ^ 2) ^ n) = 1 ∧
    coeff 1 ((1 - (X : PowerSeries ℤ) ^ 2) ^ n) = 0 ∧
    coeff 2 ((1 - (X : PowerSeries ℤ) ^ 2) ^ n) = -(n : ℤ) := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e : (1 - (X : PowerSeries ℤ) ^ 2) ^ (n + 1) = (1 - X ^ 2) ^ n - (1 - X ^ 2) ^ n * X ^ 2 := by
      ring
    rw [e]
    simp only [map_sub, coeff_mul_X_pow']
    norm_num [h0, h1, h2]
    ring

lemma pow3 (n : ℕ) :
    coeff 0 ((1 - (X : PowerSeries ℤ) ^ 3) ^ n) = 1 ∧
    coeff 1 ((1 - (X : PowerSeries ℤ) ^ 3) ^ n) = 0 ∧
    coeff 2 ((1 - (X : PowerSeries ℤ) ^ 3) ^ n) = 0 := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e : (1 - (X : PowerSeries ℤ) ^ 3) ^ (n + 1) = (1 - X ^ 3) ^ n - (1 - X ^ 3) ^ n * X ^ 3 := by
      ring
    rw [e]
    simp only [map_sub, coeff_mul_X_pow']
    norm_num [h0, h1, h2]

lemma tau_succ (n : ℕ) :
    tau (n + 1) = coeff n (∏ m ∈ Finset.range (n + 1), (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 24) := by
  unfold tau
  rw [coeff_succ_X_mul]

lemma tau_one : tau 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, tau_succ]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add, pow_one]
  exact (pow1 24).1

lemma tau_two : tau 2 = -24 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, tau_succ]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add, pow_one,
    Nat.reduceAdd]
  rw [coeff_mul_one', (pow1 24).1, (pow1 24).2.1, (pow2 24).1, (pow2 24).2.1]
  norm_num

lemma tau_three : tau 3 = 252 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, tau_succ]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add, pow_one,
    Nat.reduceAdd]
  rw [coeff_mul_two', coeff_mul_one', coeff_mul_two', (pow1 24).1, (pow1 24).2.1, (pow1 24).2.2,
    (pow2 24).1, (pow2 24).2.1, (pow2 24).2.2, (pow3 24).1, (pow3 24).2.1, (pow3 24).2.2]
  norm_num [Nat.choose]

/-- The first three terms of the `k`-th binomial transform. -/
lemma bto_iter (k : ℕ) (a : ℕ → ℤ) :
    (bto^[k] a) 0 = a 0 ∧ (bto^[k] a) 1 = a 1 + k * a 0 ∧
      (bto^[k] a) 2 = a 2 + 2 * k * a 1 + k ^ 2 * a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, ?_⟩
    · simp [bto, h0]
    · simp [bto, Finset.sum_range_succ, h0, h1]
      ring
    · simp [bto, Finset.sum_range_succ, h0, h1, h2]
      ring

lemma terms (k : ℕ) :
    (bto^[k] fun j => tau (j + 1)) 1 = k - 24 ∧
      (bto^[k] fun j => tau (j + 1)) 2 = ((k : ℤ) - 6) * ((k : ℤ) - 42) := by
  obtain ⟨-, h1, h2⟩ := bto_iter k fun j => tau (j + 1)
  refine ⟨?_, ?_⟩
  · rw [h1]
    simp only [Nat.reduceAdd, tau_one, tau_two]
    ring
  · rw [h2]
    simp only [Nat.reduceAdd, tau_one, tau_two, tau_three]
    ring

/-- Controls: the zeros the entry knows, at k = 6 (index 2) and k = 24 (index 1). -/
lemma control : (bto^[6] fun j => tau (j + 1)) 2 = 0 ∧ (bto^[24] fun j => tau (j + 1)) 1 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [(terms 6).2]
    norm_num
  · rw [(terms 24).1]
    norm_num

theorem disproof :
    ¬ ((∀ k : ℕ, 1 ≤ k → ((∃ i : ℕ, (bto^[k] fun j => tau (j + 1)) i = 0) ↔ (k = 6 ∨ k = 24))) ∧
      List.map (bto^[6] fun j => tau (j + 1)) (List.range 6) = [1, -18, 0, 688, 4494, 5508]) := by
  rintro ⟨h, -⟩
  have hz : (bto^[42] fun j => tau (j + 1)) 2 = 0 := by
    rw [(terms 42).2]
    norm_num
  have h42 := (h 42 (by norm_num)).1 ⟨2, hz⟩
  omega

end OMA.S_oeis_a128381

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128381.main) :=
  OMA.S_oeis_a128381.disproof
