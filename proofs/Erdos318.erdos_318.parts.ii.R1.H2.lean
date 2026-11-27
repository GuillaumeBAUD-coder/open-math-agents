import OMAReductions.R_Erdos318_erdos_318_parts_ii_R1

-- Step Erdos318.erdos_318.parts.ii.R1.H2: hypothesis H2 of reduction Erdos318.erdos_318.parts.ii.R1
-- Credit: @ishaanzee
-- Proof idea: if n^2 is not in Z then n has a divisor at least N * 2^N, or is divisible by p^2
-- for a prime p > N. Summing 1/n^2 over such n is at most 4/(N 2^N) + 4/N^3 <= 1/(10 N^2).

open Finset

namespace OMA.E318H2Aux

/-- If every divisor of `n` is below `N * 2 ^ N` and no prime above `N` divides `n` twice,
then `n ^ 2` lies in the set `Z`. -/
lemma sq_mem_of_good (N n : ℕ) (hn : n ≠ 0)
    (hd : ∀ d, d ∣ n → d < N * 2 ^ N)
    (hp : ∀ p, p.Prime → N < p → ¬ p ^ 2 ∣ n) :
    n ^ 2 ∈ ((((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)) ×ˢ
      (((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)).powerset).image
      (fun x => x.1 * ∏ q ∈ x.2, q) := by
  set S := n.primeFactors.filter (fun p => N < p) with hS
  set b := ∏ p ∈ n.primeFactors.filter (fun p => ¬ N < p), p ^ n.factorization p with hb
  have hfac1 : ∀ p ∈ S, n.factorization p = 1 := by
    intro p hpS
    rw [hS, mem_filter, Nat.mem_primeFactors] at hpS
    obtain ⟨⟨hpp, hpn, -⟩, hNp⟩ := hpS
    have h1 : 1 ≤ n.factorization p :=
      (hpp.pow_dvd_iff_le_factorization hn).1 (by simpa using hpn)
    have h2 : ¬ 2 ≤ n.factorization p := fun h =>
      hp p hpp hNp ((hpp.pow_dvd_iff_le_factorization hn).2 h)
    omega
  have hprodS : ∏ p ∈ S, p ^ n.factorization p = ∏ p ∈ S, p :=
    prod_congr rfl (fun p hp => by rw [hfac1 p hp, pow_one])
  have hn_eq : b * ∏ p ∈ S, p = n := by
    rw [← hprodS, mul_comm, hS, hb, prod_filter_mul_prod_filter_not]
    have := Nat.factorization_prod_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have hbn : b ∣ n := ⟨_, hn_eq.symm⟩
  have hSn : ∏ p ∈ S, p ∣ n := ⟨b, by rw [mul_comm]; exact hn_eq.symm⟩
  have hb0 : 0 < b := Nat.pos_of_ne_zero (fun h => hn (by rw [← hn_eq, h, zero_mul]))
  have hbX : b < N * 2 ^ N := hd b hbn
  have hbP : ∀ p ∈ b.primeFactors, p ≤ N := by
    intro p hpb
    rw [Nat.mem_primeFactors] at hpb
    obtain ⟨hpp, hpb, -⟩ := hpb
    by_contra h
    push_neg at h
    have hpS : p ∈ S := by
      rw [hS, mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hpp, dvd_trans hpb hbn, hn⟩, h⟩
    have h2 : p ^ 2 ∣ n := by
      rw [pow_two, ← hn_eq]
      exact mul_dvd_mul hpb (dvd_prod_of_mem _ hpS)
    exact hp p hpp h h2
  have hSsub : S ⊆ (range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p) := by
    intro q hq
    have hq' := hq
    rw [hS, mem_filter, Nat.mem_primeFactors] at hq'
    obtain ⟨⟨hqp, hqn, -⟩, hNq⟩ := hq'
    exact mem_filter.2 ⟨mem_range.2 (hd q hqn), hqp, hNq⟩
  rw [mem_image]
  refine ⟨(b ^ 2, S.image (· ^ 2)), mem_product.2 ⟨?_, ?_⟩, ?_⟩
  · exact mem_image.2 ⟨b, mem_filter.2 ⟨mem_range.2 hbX, hb0, hbP⟩, rfl⟩
  · exact mem_powerset.2 (image_subset_image hSsub)
  · have hinj : Set.InjOn (fun p : ℕ => p ^ 2) (S : Set ℕ) :=
      fun x _ y _ h => Nat.pow_left_injective two_ne_zero h
    simp only
    rw [prod_image hinj, prod_pow, ← mul_pow, hn_eq]

/-- Every `n` whose square is outside `Z` is a multiple `d * k` with `d ≥ N * 2 ^ N`, or a
multiple `m ^ 2 * k` with `m > N`. -/
lemma bad_cover (N M n : ℕ) (hn : n ∈ Ico 2 M)
    (hZ : n ^ 2 ∉ ((((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)) ×ˢ
      (((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)).powerset).image
      (fun x => x.1 * ∏ q ∈ x.2, q)) :
    n ∈ (Ico (N * 2 ^ N) M ×ˢ Ico 1 M).image (fun x => x.1 * x.2) ∪
      (Ioo N M ×ˢ Ico 1 M).image (fun x => x.1 ^ 2 * x.2) := by
  rw [mem_Ico] at hn
  have hn0 : n ≠ 0 := by omega
  by_cases h1 : ∃ d, d ∣ n ∧ N * 2 ^ N ≤ d
  · obtain ⟨d, ⟨k, hk⟩, hXd⟩ := h1
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    have hdn : d ≤ n := Nat.le_of_dvd (by omega) ⟨k, hk⟩
    have hkn : k ≤ n := Nat.le_of_dvd (by omega) ⟨d, by rw [hk, mul_comm]⟩
    apply mem_union_left
    exact mem_image.2 ⟨(d, k), mem_product.2 ⟨mem_Ico.2 ⟨hXd, by omega⟩,
      mem_Ico.2 ⟨by omega, by omega⟩⟩, hk.symm⟩
  · push_neg at h1
    by_cases h2 : ∃ p, p.Prime ∧ N < p ∧ p ^ 2 ∣ n
    · obtain ⟨p, hpp, hNp, ⟨k, hk⟩⟩ := h2
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
      have hpn : p ^ 2 ≤ n := Nat.le_of_dvd (by omega) ⟨k, hk⟩
      have hp2 : p ≤ p ^ 2 := by nlinarith [hpp.one_lt]
      have hkn : k ≤ n := Nat.le_of_dvd (by omega) ⟨p ^ 2, by rw [hk, mul_comm]⟩
      apply mem_union_right
      exact mem_image.2 ⟨(p, k), mem_product.2 ⟨mem_Ioo.2 ⟨hNp, by omega⟩,
        mem_Ico.2 ⟨by omega, by omega⟩⟩, hk.symm⟩
    · push_neg at h2
      exact absurd (sq_mem_of_good N n hn0 h1 (fun p hp hNp => h2 p hp hNp)) hZ

lemma sum_inv_sq_Ico_one (M : ℕ) : ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  have h : Ico 1 M = Ioo 0 M := by ext x; simp only [mem_Ico, mem_Ioo]; omega
  rw [h]
  simpa [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) 0 M)

lemma sum_inv_sq_Ico_ge (X M : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Ico X M, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 / X := by
  have h : Ico X M = Ioo (X - 1) M := by ext x; simp only [mem_Ico, mem_Ioo]; omega
  rw [h]
  have := sum_Ioo_inv_sq_le (α := ℝ) (X - 1) M
  have hc : ((X - 1 : ℕ) : ℝ) + 1 = X := by
    rw [Nat.cast_sub hX]; ring
  rw [hc] at this
  simpa [one_div] using this

lemma sum_inv_fourth_Ioo (N M : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Ioo N M, (1 : ℝ) / ((m : ℝ) ^ 2) ^ 2 ≤ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc ∑ m ∈ Ioo N M, (1 : ℝ) / ((m : ℝ) ^ 2) ^ 2
      ≤ ∑ m ∈ Ioo N M, (1 / (N : ℝ) ^ 2) * ((m : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro m hm
        rw [mem_Ioo] at hm
        have hm' : (N : ℝ) < m := by exact_mod_cast hm.1
        have hmpos : (0 : ℝ) < m := lt_trans hNpos hm'
        have hNm : (N : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
        have heq : (1 / (N : ℝ) ^ 2) * ((m : ℝ) ^ 2)⁻¹ = 1 / ((N : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
          field_simp
        rw [heq]
        apply one_div_le_one_div_of_le (by positivity)
        rw [pow_two ((m : ℝ) ^ 2)]
        exact mul_le_mul_of_nonneg_right hNm (by positivity)
    _ = (1 / (N : ℝ) ^ 2) * ∑ m ∈ Ioo N M, ((m : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ (1 / (N : ℝ) ^ 2) * (2 / ((N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le N M) (by positivity)
    _ ≤ 2 / (N : ℝ) ^ 3 := by
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hNpos 2, pow_pos hNpos 3]

lemma eighty_mul_le_two_pow (N : ℕ) (hN : 80 ≤ N) : 80 * N ≤ 2 ^ N := by
  have h := @Nat.lt_two_pow_self (N - 7)
  have : 2 ^ N = 2 ^ 7 * 2 ^ (N - 7) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  omega

end OMA.E318H2Aux

open OMA.E318H2Aux

theorem OMA.solution : OMA.R_Erdos318_erdos_318_parts_ii_R1.H2 := by
  refine ⟨80, fun N hN => ?_⟩
  intro B Q Z M
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set X := N * 2 ^ N with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hXbig : 80 * N ^ 2 ≤ X := by
    rw [hXdef, pow_two]
    have := eighty_mul_le_two_pow N hN
    nlinarith
  have hXbigR : (80 : ℝ) * (N : ℝ) ^ 2 ≤ X := by exact_mod_cast hXbig
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by rw [hf]; positivity
  set A := (Ico X M ×ˢ Ico 1 M).image (fun x => x.1 * x.2) with hA
  set C := (Ioo N M ×ˢ Ico 1 M).image (fun x => x.1 ^ 2 * x.2) with hC
  have hsub : (Ico 2 M).filter (fun n => n ^ 2 ∉ Z) ⊆ A ∪ C := by
    intro n hn
    rw [mem_filter] at hn
    exact bad_cover N M n hn.1 hn.2
  have step1 : ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), f n ≤ ∑ n ∈ A ∪ C, f n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
  have step2 : ∑ n ∈ A ∪ C, f n ≤ ∑ n ∈ A, f n + ∑ n ∈ C, f n := by
    rw [← sum_union_inter]
    have : 0 ≤ ∑ n ∈ A ∩ C, f n := sum_nonneg (fun n _ => hf0 n)
    linarith
  have stepA : ∑ n ∈ A, f n ≤
      (∑ d ∈ Ico X M, (1 : ℝ) / (d : ℝ) ^ 2) * ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [hA]
    refine le_trans (sum_image_le_of_nonneg (fun u _ => hf0 u)) (le_of_eq ?_)
    rw [sum_product, sum_mul_sum]
    apply sum_congr rfl; intro d _; apply sum_congr rfl; intro k _
    rw [hf]; simp only; push_cast
    rw [mul_pow, one_div_mul_one_div]
  have stepC : ∑ n ∈ C, f n ≤
      (∑ m ∈ Ioo N M, (1 : ℝ) / ((m : ℝ) ^ 2) ^ 2) * ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [hC]
    refine le_trans (sum_image_le_of_nonneg (fun u _ => hf0 u)) (le_of_eq ?_)
    rw [sum_product, sum_mul_sum]
    apply sum_congr rfl; intro m _; apply sum_congr rfl; intro k _
    rw [hf]; simp only; push_cast
    rw [mul_pow, one_div_mul_one_div]
  have hk := sum_inv_sq_Ico_one M
  have hk0 : 0 ≤ ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 := sum_nonneg (fun k _ => by positivity)
  have hd := sum_inv_sq_Ico_ge X M hX1
  have hd0 : 0 ≤ ∑ d ∈ Ico X M, (1 : ℝ) / (d : ℝ) ^ 2 := sum_nonneg (fun k _ => by positivity)
  have hm := sum_inv_fourth_Ioo N M hN1
  have hm0 : 0 ≤ ∑ m ∈ Ioo N M, (1 : ℝ) / ((m : ℝ) ^ 2) ^ 2 :=
    sum_nonneg (fun k _ => by positivity)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have e1 : (2 / (X : ℝ)) * 2 ≤ 1 / (20 * (N : ℝ) ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hXpos (by positivity)]
    nlinarith
  have hN80 : (80 : ℝ) ≤ N := by exact_mod_cast hN
  have e2 : (2 / (N : ℝ) ^ 3) * 2 ≤ 1 / (20 * (N : ℝ) ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hNpos 2]
  have e3 : 1 / (20 * (N : ℝ) ^ 2) + 1 / (20 * (N : ℝ) ^ 2) = 1 / (10 * (N : ℝ) ^ 2) := by
    field_simp; ring
  calc ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), (1 : ℝ) / (n : ℝ) ^ 2
      = ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), f n := rfl
    _ ≤ ∑ n ∈ A, f n + ∑ n ∈ C, f n := le_trans step1 step2
    _ ≤ (∑ d ∈ Ico X M, (1 : ℝ) / (d : ℝ) ^ 2) * ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 +
        (∑ m ∈ Ioo N M, (1 : ℝ) / ((m : ℝ) ^ 2) ^ 2) * ∑ k ∈ Ico 1 M, (1 : ℝ) / (k : ℝ) ^ 2 :=
        add_le_add stepA stepC
    _ ≤ (2 / (X : ℝ)) * 2 + (2 / (N : ℝ) ^ 3) * 2 := by
        apply add_le_add
        · exact mul_le_mul hd hk hk0 (by positivity)
        · exact mul_le_mul hm hk hk0 (by positivity)
    _ ≤ 1 / (10 * (N : ℝ) ^ 2) := by linarith

