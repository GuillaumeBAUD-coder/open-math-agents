import FormalConjectures.ErdosProblems.«929»

/-! The set is periodic modulo `2 * (k + 1)!` and contains `1`, so it has positive density. -/

open Filter Erdos929

theorem OMA.solution : type_of% @Erdos929.erdos_929.variants.trivial_upper := by
  classical
  intro k
  apply S_le
  set D := 2 * (k + 1).factorial
  set p := AllHaveSmallPrimeFactor (k + 1) k
  have hD : 2 ≤ D := by have := Nat.factorial_pos (k + 1); omega
  have per (n : ℕ) : p (D + n) = p n := propext <| forall₂_congr fun i _ =>
    exists_congr fun q => and_congr_right fun hq => and_congr_right fun h => by
      rw [add_assoc]; exact Nat.dvd_add_right ((Nat.dvd_factorial hq.pos h).mul_left 2)
  have hc (n : ℕ) : Nat.count p (D + n) = Nat.count p D + Nat.count p n := by
    rw [Nat.count_add]; simp only [per]
  have h1 : p 1 := fun i hi => by
    simp only [Finset.mem_Icc] at hi
    exact ⟨_, Nat.minFac_prime (by omega), (Nat.minFac_le (by omega)).trans (by omega),
      Nat.minFac_dvd _⟩
  have hpos := (Nat.count_lt_count_succ_iff.2 h1).trans_le (Nat.count_monotone p hD)
  set c := (Nat.count p D : ℝ) / D
  have hDc : (D : ℝ) * c = Nat.count p D := mul_div_cancel₀ _ (by positivity)
  have hc1 : c ≤ 1 := div_le_one_of_le₀ (mod_cast Nat.count_le _) (by positivity)
  have hc0 : 0 < c := div_pos (mod_cast (Nat.zero_le _).trans_lt hpos) (by positivity)
  clear_value c
  set e := fun n : ℕ => (Nat.count p n : ℝ) - n * c
  have he : Function.Periodic e D := fun n => by
    simp only [e, add_comm n, hc]; push_cast; linear_combination -hDc
  have hb (n : ℕ) : |e n| ≤ D := by
    rw [← he.map_mod_nat]
    have h2 : (Nat.count p (n % D) : ℝ) ≤ (n % D : ℕ) := mod_cast Nat.count_le _
    have h3 : ((n % D : ℕ) : ℝ) < D := mod_cast Nat.mod_lt n (by omega)
    have h4 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (n % D)) hc0.le
    have h5 := mul_le_mul_of_nonneg_left hc1 (Nat.cast_nonneg (α := ℝ) (n % D))
    rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (Nat.count p (n % D))]
  refine ⟨c, hc0, ?_⟩
  rw [Set.HasDensity, ← add_zero c]
  refine (tendsto_const_nhds.add (squeeze_zero_norm' (f := fun n : ℕ => e n / n) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (D : ℝ)))).congr' ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_div, Real.norm_eq_abs, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (hb n) n.cast_nonneg
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      show {m | p m} ∩ Set.Iio n = ↑((Finset.range n).filter p) by ext; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range, ← Finset.coe_range,
      Set.ncard_coe_finset, Finset.card_range]
    field_simp
    simp only [e]; ring
