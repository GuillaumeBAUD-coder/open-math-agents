import OMAStatements.S_mo_495575

open Finset

namespace OMA.P_mo_495575

private def term (k m : ℕ) : ℚ :=
  (1 / (m : ℚ)) * (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m)

private lemma term_nonneg (k m : ℕ) : 0 ≤ term k m := by
  unfold term; positivity

private lemma summand_eq (k m : ℕ) :
    ((-1 : ℚ) ^ m / (m : ℚ)) * (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m) =
      (-1 : ℚ) ^ m * term k m := by
  unfold term; ring

private lemma two_pow_sub_two_ge (k : ℕ) (hk : 25 ≤ k) : k ^ 4 ≤ 2 ^ (k - 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction t with
  | zero => norm_num
  | succ t ih =>
    have h1 : 25 + (t + 1) - 2 = (25 + t - 2) + 1 := by omega
    rw [h1, pow_succ' 2]
    have hstep : (25 + (t + 1)) ^ 4 ≤ 2 * (25 + t) ^ 4 := by
      have hdiff : (2 * (25 + t) ^ 4 : ℤ) - (25 + (t + 1)) ^ 4 =
          (t : ℤ) ^ 4 + 96 * (t : ℤ) ^ 3 + 3444 * (t : ℤ) ^ 2 + 54696 * (t : ℤ) + 324274 := by
        ring
      have hpos : (0 : ℤ) ≤ (2 * (25 + t) ^ 4 : ℤ) - (25 + (t + 1)) ^ 4 := by
        rw [hdiff]; positivity
      exact_mod_cast sub_nonneg.mp hpos
    exact le_trans hstep (Nat.mul_le_mul_left 2 (ih (by omega)))

private lemma three_pow_ge_pow_eight (k : ℕ) (hk : 25 ≤ k) : k ^ 8 ≤ 3 ^ k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [show 25 + (t + 1) = (25 + t) + 1 by omega, pow_succ' 3]
    have hstep : ((25 + t) + 1) ^ 8 ≤ 3 * (25 + t) ^ 8 := by
      have hdiff : (3 * (25 + t) ^ 8 : ℤ) - ((25 + t) + 1) ^ 8 =
          2 * (t : ℤ) ^ 8 + 392 * (t : ℤ) ^ 7 + 33572 * (t : ℤ) ^ 6 + 1640744 * (t : ℤ) ^ 5 +
          50042930 * (t : ℤ) ^ 4 + 975267944 * (t : ℤ) ^ 3 + 11858170772 * (t : ℤ) ^ 2 +
          82229893592 * (t : ℤ) + 248936607299 := by
        ring
      have hpos : (0 : ℤ) ≤ (3 * (25 + t) ^ 8 : ℤ) - ((25 + t) + 1) ^ 8 := by
        rw [hdiff]; positivity
      exact_mod_cast sub_nonneg.mp hpos
    exact le_trans hstep (Nat.mul_le_mul_left 3 (ih (by omega)))

private lemma pow_ge_k_pow_four (k m : ℕ) (hk : 25 ≤ k) (hm1 : 5 ≤ m) (hm2 : m ≤ k - 2) :
    k ^ 4 ≤ (k - m) ^ m := by
  by_cases hlast : m = k - 2
  · subst hlast
    have hsub : k - (k - 2) = 2 := by omega
    rw [hsub]
    exact two_pow_sub_two_ge k hk
  · have hm3 : m ≤ k - 3 := by omega
    by_cases h5 : m = 5
    · subst h5
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hsub : 25 + t - 5 = 20 + t := by omega
      rw [hsub]
      have hdiff : ((20 + t : ℤ) ^ 5) - ((25 + t : ℤ) ^ 4) =
          (t : ℤ) ^ 5 + 99 * (t : ℤ) ^ 4 + 3900 * (t : ℤ) ^ 3 + 76250 * (t : ℤ) ^ 2 +
          737500 * (t : ℤ) + 2809375 := by
        ring
      have hpos : (0 : ℤ) ≤ ((20 + t : ℤ) ^ 5) - ((25 + t : ℤ) ^ 4) := by
        rw [hdiff]; positivity
      exact_mod_cast sub_nonneg.mp hpos
    · have hm6 : 6 ≤ m := by omega
      by_cases hhalf : 2 * m ≤ k
      · have hbase : k ≤ 2 * (k - m) := by omega
        have h1 : k ^ 6 ≤ (2 * (k - m)) ^ 6 := Nat.pow_le_pow_left hbase 6
        have h2 : (2 * (k - m)) ^ 6 = 64 * (k - m) ^ 6 := by ring
        have h3 : 64 * k ^ 4 ≤ k ^ 6 := by
          have : 64 ≤ k ^ 2 := by nlinarith
          calc 64 * k ^ 4 ≤ k ^ 2 * k ^ 4 := Nat.mul_le_mul_right _ this
            _ = k ^ 6 := by ring
        have h4 : k ^ 4 ≤ (k - m) ^ 6 := by omega
        exact le_trans h4 (Nat.pow_le_pow_right (by omega) hm6)
      · have hge3 : 3 ≤ k - m := by omega
        have hsq1 : (k ^ 4) ^ 2 = k ^ 8 := by ring
        have hsq2 : k ^ 8 ≤ 3 ^ k := three_pow_ge_pow_eight k hk
        have hsq3 : 3 ^ k ≤ 3 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hsq4 : 3 ^ (2 * m) = (3 ^ m) ^ 2 := by rw [mul_comm, pow_mul]
        have hsq5 : 3 ^ m ≤ (k - m) ^ m := Nat.pow_le_pow_left hge3 m
        have hsq6 : (3 ^ m) ^ 2 ≤ ((k - m) ^ m) ^ 2 := Nat.pow_le_pow_left hsq5 2
        have htot : (k ^ 4) ^ 2 ≤ ((k - m) ^ m) ^ 2 := by
          calc (k ^ 4) ^ 2 = k ^ 8 := hsq1
            _ ≤ 3 ^ k := hsq2
            _ ≤ 3 ^ (2 * m) := hsq3
            _ = (3 ^ m) ^ 2 := hsq4
            _ ≤ ((k - m) ^ m) ^ 2 := hsq6
        by_contra hlt
        have hlt1 : (k - m) ^ m < k ^ 4 := Nat.lt_of_not_ge hlt
        have hlt2 : ((k - m) ^ m) ^ 2 < (k ^ 4) ^ 2 := Nat.pow_lt_pow_left hlt1 (by norm_num)
        omega

private lemma term_le_tail (k m : ℕ) (hk : 25 ≤ k) (hm1 : 5 ≤ m) (hm2 : m ≤ k - 2) :
    term k m ≤ 2 / (5 * (k : ℚ) ^ 4) := by
  unfold term
  have hm_pos : (0 : ℚ) < (m : ℚ) := by positivity
  have hkm_pos : (0 : ℚ) < ((k - m : ℕ) : ℚ) := by
    have : 0 < k - m := by omega
    positivity
  have hkm1_le : ((k - m : ℕ) : ℚ) ^ m ≤ ((k - m + 1 : ℕ) : ℚ) ^ m := by
    gcongr; omega
  have h1 : 1 / ((k - m + 1 : ℕ) : ℚ) ^ m ≤ 1 / ((k - m : ℕ) : ℚ) ^ m :=
    one_div_le_one_div_of_le (pow_pos hkm_pos m) hkm1_le
  have hpow : (k : ℚ) ^ 4 ≤ ((k - m : ℕ) : ℚ) ^ m := by
    exact_mod_cast pow_ge_k_pow_four k m hk hm1 hm2
  have h2 : 1 / ((k - m : ℕ) : ℚ) ^ m ≤ 1 / (k : ℚ) ^ 4 :=
    one_div_le_one_div_of_le (by positivity) hpow
  have h3 : (1 / (m : ℚ)) ≤ 1 / 5 := by
    have : (5 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
    exact one_div_le_one_div_of_le (by norm_num) this
  calc
    1 / (m : ℚ) * (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m)
        ≤ 1 / 5 * (1 / (k : ℚ) ^ 4 + 1 / (k : ℚ) ^ 4) := by
          gcongr
          linarith
    _ = 2 / (5 * (k : ℚ) ^ 4) := by ring

private lemma middle_sum_lower_bound (k : ℕ) (hk : 25 ≤ k) :
    -(2 / (5 * (k : ℚ) ^ 3)) ≤ ∑ m ∈ Ico 4 (k - 1), (-1 : ℚ) ^ m * term k m := by
  have hpt : ∀ m ∈ Ico 4 (k - 1), -(2 / (5 * (k : ℚ) ^ 4)) ≤ (-1 : ℚ) ^ m * term k m := by
    intro m hm
    rw [mem_Ico] at hm
    rcases Nat.even_or_odd m with hev | hodd
    · rw [hev.neg_one_pow, one_mul]
      have hnn : 0 ≤ term k m := term_nonneg k m
      have hpos : (0 : ℚ) ≤ 2 / (5 * (k : ℚ) ^ 4) := by positivity
      linarith
    · rw [hodd.neg_one_pow]
      have hm5 : 5 ≤ m := by
        rcases hodd with ⟨r, rfl⟩
        omega
      have hle := term_le_tail k m hk hm5 (by omega)
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((k - 1 - 4 : ℕ) : ℚ) ≤ (k : ℚ) := by
    exact_mod_cast (show k - 1 - 4 ≤ k by omega)
  have hpos : (0 : ℚ) ≤ 2 / (5 * (k : ℚ) ^ 4) := by positivity
  have hk_ne : (k : ℚ) ≠ 0 := by positivity
  calc
    -(2 / (5 * (k : ℚ) ^ 3)) = (k : ℚ) * -(2 / (5 * (k : ℚ) ^ 4)) := by field_simp
    _ ≤ ((k - 1 - 4 : ℕ) : ℚ) * -(2 / (5 * (k : ℚ) ^ 4)) := by nlinarith
    _ ≤ ∑ m ∈ Ico 4 (k - 1), (-1 : ℚ) ^ m * term k m := hsum

private lemma split_sum (k : ℕ) (hk : 5 ≤ k) :
    ∑ m ∈ Ico 2 k, (-1 : ℚ) ^ m * term k m =
      term k 2 - term k 3 + (-1 : ℚ) ^ (k - 1) * term k (k - 1) +
        ∑ m ∈ Ico 4 (k - 1), (-1 : ℚ) ^ m * term k m := by
  have h1 : Ico 2 k = insert (k - 1) (Ico 2 (k - 1)) := by
    ext m
    simp only [mem_Ico, mem_insert]
    omega
  have h1_not : k - 1 ∉ Ico 2 (k - 1) := by simp
  have h2 : Ico 2 (k - 1) = insert 2 (insert 3 (Ico 4 (k - 1))) := by
    ext m
    simp only [mem_Ico, mem_insert]
    omega
  have h2_not : 2 ∉ insert 3 (Ico 4 (k - 1)) := by simp
  have h3_not : 3 ∉ Ico 4 (k - 1) := by simp
  rw [h1, sum_insert h1_not, h2, sum_insert h2_not, sum_insert h3_not]
  norm_num
  ring

private lemma term_three_le (k : ℕ) (hk : 5 ≤ k) :
    term k 3 ≤ 2 / (3 * ((k - 3 : ℕ) : ℚ) ^ 3) := by
  unfold term
  have hpos : (0 : ℚ) < ((k - 3 : ℕ) : ℚ) := by
    have : 0 < k - 3 := by omega
    positivity
  have hle : ((k - 3 : ℕ) : ℚ) ^ 3 ≤ ((k - 3 + 1 : ℕ) : ℚ) ^ 3 := by
    gcongr; omega
  have hdiv : 1 / ((k - 3 + 1 : ℕ) : ℚ) ^ 3 ≤ 1 / ((k - 3 : ℕ) : ℚ) ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hpos 3) hle
  calc
    1 / (3 : ℚ) * (1 / ((k - 3 : ℕ) : ℚ) ^ 3 + 1 / ((k - 3 + 1 : ℕ) : ℚ) ^ 3)
        ≤ 1 / 3 * (1 / ((k - 3 : ℕ) : ℚ) ^ 3 + 1 / ((k - 3 : ℕ) : ℚ) ^ 3) := by gcongr
    _ = 2 / (3 * ((k - 3 : ℕ) : ℚ) ^ 3) := by ring

private lemma main_large (k : ℕ) (hk : 25 ≤ k) :
    (-1 : ℚ) ^ (k - 1) / (k : ℚ) <
      ∑ m ∈ Ico 2 k, ((-1 : ℚ) ^ m / (m : ℚ)) *
        (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m) := by
  have hrew :
      ∑ m ∈ Ico 2 k, ((-1 : ℚ) ^ m / (m : ℚ)) *
        (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m) =
      ∑ m ∈ Ico 2 k, (-1 : ℚ) ^ m * term k m :=
    Finset.sum_congr rfl fun m _ => summand_eq k m
  rw [hrew, split_sum k (by omega)]
  have hmid := middle_sum_lower_bound k hk
  have hm3 := term_three_le k (by omega)
  have hkm3 : ((k - 3 : ℕ) : ℚ) = (k : ℚ) - 3 := by
    have : 3 ≤ k := by omega
    exact Nat.cast_sub this
  have hkm2 : ((k - 2 : ℕ) : ℚ) = (k : ℚ) - 2 := by
    have : 2 ≤ k := by omega
    exact Nat.cast_sub this
  have hkm1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    have : 1 ≤ k := by omega
    exact Nat.cast_sub this
  have hterm_last : term k (k - 1) = 1 / ((k : ℚ) - 1) + 1 / (((k : ℚ) - 1) * 2 ^ (k - 1)) := by
    unfold term
    have hsub1 : k - (k - 1) = 1 := by omega
    rw [hsub1, hkm1]
    simp only [Nat.cast_one, one_pow, div_one, one_add_one_eq_two]
    have hk1_ne : (k : ℚ) - 1 ≠ 0 := by
      have : (25 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
      linarith
    field_simp
    ring
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have ht_nn : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg t
  rcases Nat.even_or_odd (25 + t) with hev | hodd
  · -- Even k = 25 + t
    have hodd1 : Odd (25 + t - 1) := by
      rcases hev with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    rw [hodd1.neg_one_pow]
    have h2pow : ((25 + t : ℕ) : ℚ) ^ 4 ≤ (2 : ℚ) ^ (25 + t - 1) := by
      have h1 : (25 + t) ^ 4 ≤ 2 ^ (25 + t - 2) := two_pow_sub_two_ge (25 + t) (by omega)
      have h2 : 2 ^ (25 + t - 2) ≤ 2 ^ (25 + t - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast le_trans h1 h2
    have hlast_le :
        1 / (((25 + t : ℕ) : ℚ) - 1) + 1 / ((((25 + t : ℕ) : ℚ) - 1) * (2 : ℚ) ^ (25 + t - 1)) ≤
        1 / (((25 + t : ℕ) : ℚ) - 1) + 1 / ((25 + t : ℕ) : ℚ) ^ 4 := by
      have hk_gt : (1 : ℚ) ≤ ((25 + t : ℕ) : ℚ) - 1 := by push_cast; linarith
      have hmul : ((25 + t : ℕ) : ℚ) ^ 4 ≤ (((25 + t : ℕ) : ℚ) - 1) * (2 : ℚ) ^ (25 + t - 1) := by
        calc
          ((25 + t : ℕ) : ℚ) ^ 4 = 1 * ((25 + t : ℕ) : ℚ) ^ 4 := (one_mul _).symm
          _ ≤ (((25 + t : ℕ) : ℚ) - 1) * (2 : ℚ) ^ (25 + t - 1) :=
            mul_le_mul hk_gt h2pow (by positivity) (by linarith)
      have hdiv : 1 / ((((25 + t : ℕ) : ℚ) - 1) * (2 : ℚ) ^ (25 + t - 1)) ≤
          1 / ((25 + t : ℕ) : ℚ) ^ 4 :=
        one_div_le_one_div_of_le (by positivity) hmul
      linarith
    have hterm2 : term (25 + t) 2 =
        1 / (2 * (((25 + t : ℕ) : ℚ) - 2) ^ 2) + 1 / (2 * (((25 + t : ℕ) : ℚ) - 1) ^ 2) := by
      unfold term
      rw [hkm2]
      have hadd1 : ((25 + t - 2 + 1 : ℕ) : ℚ) = ((25 + t : ℕ) : ℚ) - 1 := by
        have : 25 + t - 2 + 1 = 25 + t - 1 := by omega
        rw [this, hkm1]
      rw [hadd1]
      have hk1_ne : ((25 + t : ℕ) : ℚ) - 1 ≠ 0 := by push_cast; linarith
      have hk2_ne : ((25 + t : ℕ) : ℚ) - 2 ≠ 0 := by push_cast; linarith
      field_simp
      ring
    set K : ℚ := ((25 + t : ℕ) : ℚ)
    have hK_eq : K = (t : ℚ) + 25 := by dsimp [K]; push_cast; ring
    have hK_pos : 0 < K := by linarith
    have hK1_pos : 0 < K - 1 := by linarith
    have hK2_pos : 0 < K - 2 := by linarith
    have hK3_pos : 0 < K - 3 := by linarith
    have hmain_pos :
        (4 * K ^ 2 - 11 * K + 8) / (2 * K ^ 5) ≤
          1 / (2 * (K - 2) ^ 2) + 1 / (2 * (K - 1) ^ 2) - 1 / (K - 1) + 1 / K := by
      have hid :
          1 / (2 * (K - 2) ^ 2) + 1 / (2 * (K - 1) ^ 2) - 1 / (K - 1) + 1 / K =
          (4 * K ^ 2 - 11 * K + 8) / (2 * K * (K - 1) ^ 2 * (K - 2) ^ 2) := by
        field_simp; ring
      rw [hid]
      have hnum : 0 ≤ 4 * K ^ 2 - 11 * K + 8 := by rw [hK_eq]; nlinarith
      have hden : 2 * K * (K - 1) ^ 2 * (K - 2) ^ 2 ≤ 2 * K ^ 5 := by
        have h1 : (K - 1) ^ 2 ≤ K ^ 2 := by nlinarith
        have h2 : (K - 2) ^ 2 ≤ K ^ 2 := by nlinarith
        have h3 : (K - 1) ^ 2 * (K - 2) ^ 2 ≤ K ^ 2 * K ^ 2 :=
          mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
        calc
          2 * K * (K - 1) ^ 2 * (K - 2) ^ 2 = 2 * K * ((K - 1) ^ 2 * (K - 2) ^ 2) := by ring
          _ ≤ 2 * K * (K ^ 2 * K ^ 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
          _ = 2 * K ^ 5 := by ring
      exact div_le_div_of_nonneg_left hnum (by positivity) hden
    have hstrict :
        2 / (3 * (K - 3) ^ 3) + 1 / K ^ 4 + 2 / (5 * K ^ 3) <
          (4 * K ^ 2 - 11 * K + 8) / (2 * K ^ 5) := by
      rw [← sub_pos]
      have hsub :
          (4 * K ^ 2 - 11 * K + 8) / (2 * K ^ 5) -
            (2 / (3 * (K - 3) ^ 3) + 1 / K ^ 4 + 2 / (5 * K ^ 3)) =
          (15 * (4 * K ^ 2 - 11 * K + 8) * (K - 3) ^ 3 -
            (20 * K ^ 5 + 30 * K * (K - 3) ^ 3 + 12 * K ^ 2 * (K - 3) ^ 3)) /
          (30 * K ^ 5 * (K - 3) ^ 3) := by
        field_simp; ring
      rw [hsub]
      apply div_pos _ (by positivity)
      rw [hK_eq]
      have hpoly :
          15 * (4 * ((t : ℚ) + 25) ^ 2 - 11 * ((t : ℚ) + 25) + 8) * (((t : ℚ) + 25) - 3) ^ 3 -
            (20 * ((t : ℚ) + 25) ^ 5 + 30 * ((t : ℚ) + 25) * (((t : ℚ) + 25) - 3) ^ 3 +
              12 * ((t : ℚ) + 25) ^ 2 * (((t : ℚ) + 25) - 3) ^ 3) =
          28 * (t : ℚ) ^ 5 + 2873 * (t : ℚ) ^ 4 + 115471 * (t : ℚ) ^ 3 +
            2253934 * (t : ℚ) ^ 2 + 21072080 * (t : ℚ) + 73496260 := by
        ring
      rw [hpoly]
      positivity
    rw [hterm_last, hterm2]
    rw [hkm3] at hm3
    have hneg : (-1 : ℚ) / K = -(1 / K) := by ring
    rw [hneg]
    linarith
  · -- Odd k = 25 + t
    have hev1 : Even (25 + t - 1) := by
      rcases hodd with ⟨r, hr⟩
      exact ⟨r, by omega⟩
    rw [hev1.neg_one_pow]
    set K : ℚ := ((25 + t : ℕ) : ℚ)
    have hK_eq : K = (t : ℚ) + 25 := by dsimp [K]; push_cast; ring
    have hK_pos : 0 < K := by linarith
    have hK1_pos : 0 < K - 1 := by linarith
    have hK3_pos : 0 < K - 3 := by linarith
    have hterm2_nn : 0 ≤ term (25 + t) 2 := term_nonneg _ _
    have hlast_ge : 1 / (K - 1) ≤ term (25 + t) (25 + t - 1) := by
      rw [hterm_last]
      have : (0 : ℚ) ≤ 1 / ((K - 1) * (2 : ℚ) ^ (25 + t - 1)) := by positivity
      linarith
    have hdiff_ge : 1 / K ^ 2 ≤ 1 / (K - 1) - 1 / K := by
      have hid : 1 / (K - 1) - 1 / K = 1 / (K * (K - 1)) := by field_simp; ring
      rw [hid]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstrict : 2 / (3 * (K - 3) ^ 3) + 2 / (5 * K ^ 3) < 1 / K ^ 2 := by
      rw [← sub_pos]
      have hsub :
          1 / K ^ 2 - (2 / (3 * (K - 3) ^ 3) + 2 / (5 * K ^ 3)) =
          (15 * K * (K - 3) ^ 3 - 10 * K ^ 3 - 6 * (K - 3) ^ 3) / (15 * K ^ 3 * (K - 3) ^ 3) := by
        field_simp; ring
      rw [hsub]
      apply div_pos _ (by positivity)
      rw [hK_eq]
      have hpoly :
          15 * ((t : ℚ) + 25) * (((t : ℚ) + 25) - 3) ^ 3 - 10 * ((t : ℚ) + 25) ^ 3 -
            6 * (((t : ℚ) + 25) - 3) ^ 3 =
          15 * (t : ℚ) ^ 4 + 1349 * (t : ℚ) ^ 3 + 45384 * (t : ℚ) ^ 2 +
            676758 * (t : ℚ) + 3772862 := by
        ring
      rw [hpoly]
      positivity
    rw [hkm3] at hm3
    linarith

private lemma main_small (k : ℕ) (hk1 : 4 ≤ k) (hk2 : k ≤ 24) :
    (-1 : ℚ) ^ (k - 1) / (k : ℚ) <
      ∑ m ∈ Ico 2 k, ((-1 : ℚ) ^ m / (m : ℚ)) *
        (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m) := by
  interval_cases k <;> norm_num [Finset.sum_Ico_succ_top]

end OMA.P_mo_495575

open OMA.P_mo_495575 in
theorem OMA.solution : type_of% @OMA.S_mo_495575.main := by
  intro k hk
  by_cases h : 25 ≤ k
  · exact main_large k h
  · exact main_small k hk (by omega)
