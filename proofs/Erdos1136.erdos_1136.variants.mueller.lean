import FormalConjectures.ErdosProblems.«1136»

/-! The odd part characterizes the set and gives a counting recurrence. -/

open Erdos1136 Filter Topology

lemma OMA.mueller_mem (n : ℕ) : n ∈ muellerSet ↔ ∃ i t : ℕ, n = 2 ^ i * (4 * t + 3) := by
  constructor
  · rintro ⟨i, hi⟩
    have hlt : 3 * 2 ^ i < (2 : ℕ) ^ (i + 2) := by
      rw [pow_add]
      norm_num
      have hpos : 0 < (2 : ℕ) ^ i := by positivity
      omega
    have hmod : n % ((2 : ℕ) ^ (i + 2)) = 3 * 2 ^ i := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using hi
    refine ⟨i, n / (2 ^ (i + 2)), ?_⟩
    calc
      n = n % (2 ^ (i + 2)) + (2 ^ (i + 2)) * (n / (2 ^ (i + 2))) :=
        (Nat.mod_add_div _ _).symm
      _ = _ := by
        rw [hmod]
        have hpow : (2 : ℕ) ^ (i + 2) = 2 ^ i * 4 := by rw [pow_add]; norm_num
        simp only [hpow]
        ring
  · rintro ⟨i, t, rfl⟩
    refine ⟨i, ?_⟩
    have heq : (2 : ℕ) ^ i * (4 * t + 3) = 3 * 2 ^ i + 2 ^ (i + 2) * t := by
      rw [pow_add]
      norm_num
      ring
    rw [heq]
    have hm : (2 : ℕ) ^ (i + 2) * t ≡ 0 [MOD 2 ^ (i + 2)] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    simpa only [add_zero] using hm.add_left (3 * 2 ^ i)

lemma OMA.odd_factor_not_power (i t k : ℕ) (hodd : Odd t) (ht : 1 < t) :
    (2 : ℕ) ^ i * t ≠ 2 ^ k := by
  intro heq
  have hd : t ∣ (2 : ℕ) ^ k := by
    rw [← heq]
    exact dvd_mul_left _ _
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases j with
  | zero =>
    rw [pow_zero] at hj
    omega
  | succ j =>
    rw [pow_succ'] at hj
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨2 ^ j, by omega⟩

lemma OMA.mueller_sum_of_lt (i j u v k : ℕ) (hij : i < j) :
    (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ j * (4 * v + 3) ≠ 2 ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
  have heq : (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ (i + 1 + d) * (4 * v + 3) =
      2 ^ i * ((4 * u + 3) + 2 * (2 ^ d * (4 * v + 3))) := by
    rw [pow_add (2 : ℕ) (i + 1) d, pow_succ (2 : ℕ) i]
    ring
  rw [heq]
  apply OMA.odd_factor_not_power
  · exact ⟨2 * u + 1 + 2 ^ d * (4 * v + 3), by omega⟩
  · omega

lemma OMA.mueller_avoids : AvoidsPowersOfTwo muellerSet := by
  intro a ha b hb k
  obtain ⟨i, u, rfl⟩ := (OMA.mueller_mem a).mp ha
  obtain ⟨j, v, rfl⟩ := (OMA.mueller_mem b).mp hb
  rcases lt_trichotomy i j with hij | hij | hji
  · exact OMA.mueller_sum_of_lt i j u v k hij
  · subst j
    rw [show (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ i * (4 * v + 3) =
      2 ^ (i + 1) * (2 * (u + v + 1) + 1) by rw [pow_succ]; ring]
    exact OMA.odd_factor_not_power (i + 1) _ k ⟨u + v + 1, rfl⟩ (by omega)
  · rw [add_comm]
    exact OMA.mueller_sum_of_lt j i v u k hji

lemma OMA.mueller_even (n : ℕ) : 2 * n ∈ muellerSet ↔ n ∈ muellerSet := by
  rw [OMA.mueller_mem, OMA.mueller_mem]
  constructor
  · rintro ⟨i, t, hi⟩
    cases i with
    | zero =>
      simp only [pow_zero, one_mul] at hi
      omega
    | succ i =>
      refine ⟨i, t, Nat.mul_left_cancel (by decide : 0 < (2 : ℕ)) ?_⟩
      simpa only [pow_succ', mul_assoc] using hi
  · rintro ⟨i, t, hi⟩
    exact ⟨i + 1, t, by rw [pow_succ', mul_assoc, ← hi]⟩

lemma OMA.mueller_odd (n : ℕ) : 2 * n + 1 ∈ muellerSet ↔ n % 2 = 1 := by
  rw [OMA.mueller_mem]
  constructor
  · rintro ⟨i, t, hi⟩
    cases i with
    | zero =>
      simp only [pow_zero, one_mul] at hi
      omega
    | succ i =>
      rw [pow_succ', mul_assoc] at hi
      omega
  · intro h
    exact ⟨0, n / 2, by simp only [pow_zero, one_mul]; omega⟩

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.mueller := by
  classical
  refine ⟨OMA.mueller_avoids, ?_⟩
  let χ (n : ℕ) : ℕ := if n ∈ muellerSet then 1 else 0
  let C (n : ℕ) := ∑ k ∈ Finset.range n, χ k
  have hsucc (n : ℕ) : C (n + 1) = C n + χ n := Finset.sum_range_succ χ n
  have hχeven (n : ℕ) : χ (2 * n) = χ n := by simp only [χ, OMA.mueller_even]
  have hχodd (n : ℕ) : χ (2 * n + 1) = n % 2 := by
    simp only [χ, OMA.mueller_odd]
    split <;> omega
  have hχle (n : ℕ) : χ n ≤ 1 := by
    dsimp only [χ]
    split <;> decide
  have hdbl (n : ℕ) : C (2 * n) = C n + n / 2 := by
    induction n with
    | zero => simp [C]
    | succ n ih =>
      calc
        C (2 * (n + 1)) = C (2 * n) + χ (2 * n) + χ (2 * n + 1) := by
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, hsucc (2 * n + 1),
            hsucc (2 * n)]
        _ = C (n + 1) + (n + 1) / 2 := by
          rw [ih, hχeven, hχodd, hsucc n]
          omega
  let T (n : ℕ) : ℝ := 2 * (C n : ℝ) - (n : ℝ)
  have hrec (n : ℕ) : |T n| ≤ |T (n / 2)| + 2 := by
    let q := n / 2
    have hnq : n = 2 * q ∨ n = 2 * q + 1 := by dsimp only [q]; omega
    have hCn : C q + q / 2 ≤ C n ∧ C n ≤ C q + q / 2 + 1 := by
      rcases hnq with hn | hn
      · rw [hn, hdbl]
        exact ⟨le_rfl, Nat.le_succ _⟩
      · rw [hn, hsucc, hdbl]
        have h := hχle (2 * q)
        omega
    have hClo : (C q : ℝ) + (q / 2 : ℕ) ≤ (C n : ℝ) := by exact_mod_cast hCn.1
    have hChi : (C n : ℝ) ≤ (C q : ℝ) + (q / 2 : ℕ) + 1 := by exact_mod_cast hCn.2
    have hnlo : (2 : ℝ) * q ≤ (n : ℝ) := by
      exact_mod_cast (show 2 * q ≤ n by dsimp only [q]; omega)
    have hnhi : (n : ℝ) ≤ (2 : ℝ) * q + 1 := by
      exact_mod_cast (show n ≤ 2 * q + 1 by dsimp only [q]; omega)
    have hqlo : (q : ℝ) ≤ 2 * (q / 2 : ℕ) + 1 := by
      exact_mod_cast (show q ≤ 2 * (q / 2) + 1 by omega)
    have hqhi : (2 : ℝ) * (q / 2 : ℕ) ≤ (q : ℝ) := by
      exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
    change |T n| ≤ |T q| + 2
    have htlo : T q - 2 ≤ T n := by dsimp only [T]; linarith
    have hthi : T n ≤ T q + 2 := by dsimp only [T]; linarith
    exact abs_le.mpr ⟨by linarith [neg_abs_le (T q)], by linarith [le_abs_self (T q)]⟩
  have hT (n : ℕ) : |T n| ≤ 8 * Real.sqrt (n : ℝ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · simp [hn, T, C]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsub : n / 2 < n := Nat.div_lt_self hnpos (by decide)
      have hsmall : ((n / 2 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) ^ 2 * (n : ℝ) := by
        have h : (2 : ℝ) * (n / 2 : ℕ) ≤ (n : ℝ) := by
          exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
        nlinarith only [h, Nat.cast_nonneg (α := ℝ) n]
      have hroot : Real.sqrt ((n / 2 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt (n : ℝ) := by
        simpa only [Real.sqrt_mul (sq_nonneg (3 / 4 : ℝ)),
          Real.sqrt_sq (by norm_num : 0 ≤ (3 / 4 : ℝ))] using Real.sqrt_le_sqrt hsmall
      have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr
        (by exact_mod_cast hnpos)
      linarith only [hrec n, ih _ hsub, hroot, hs]
  have hcount (n : ℕ) : (muellerSet ∩ Set.Iio n).ncard = C n := by
    have heq : (↑((Finset.range n).filter (· ∈ muellerSet)) : Set ℕ) =
        muellerSet ∩ Set.Iio n := by
      ext k
      simp [and_comm]
    rw [← heq, Set.ncard_coe_finset]
    simp [C, χ]
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
    hcount, Set.ncard_Iio_nat]
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hzero : Tendsto (fun n : ℕ => 4 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 4
  refine squeeze_zero' (.of_forall fun n => abs_nonneg _) ?_ hzero
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
  have hden : 0 < 2 * (n : ℝ) := by positivity
  have heq : (C n : ℝ) / (n : ℝ) - 1 / 2 = T n / (2 * (n : ℝ)) := by
    dsimp only [T]
    field_simp [hnpos.ne']
  rw [heq, abs_div, abs_of_pos hden]
  calc
    _ ≤ (8 * Real.sqrt (n : ℝ)) / (2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right (hT n) hden.le
    _ = 4 / Real.sqrt (n : ℝ) := by
      apply (div_eq_div_iff hden.ne' hspos.ne').mpr
      nlinarith only [Real.sq_sqrt hnpos.le]