import OMAStatements.S_oeis_a121669

namespace OMA.A121669Proof

open Filter Topology OMA.S_oeis_a121669

lemma count_bound (n : ℕ) : count n ≤ 10 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp [Word])

theorem ratio_tends_to_zero :
    Tendsto (fun n : ℕ => (count n : ℝ) / proposed n) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ => (200 : ℝ) / n) _ _ (tendsto_const_div_atTop_nhds_zero_nat 200)
  · filter_upwards with n
    unfold proposed
    positivity
  · filter_upwards [eventually_ge_atTop 12] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
    have hm : 10 ≤ m := by omega
    have hpow : (10 : ℝ)^m ≤ (m : ℝ)^m := by
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _
    have hb : (count (m+2) : ℝ) ≤ 100 * (m : ℝ)^m := by
      calc
        _ ≤ (10 : ℝ)^(m+2) := by exact_mod_cast count_bound (m+2)
        _ = 100 * 10^m := by rw [pow_add]; ring
        _ ≤ _ := by linarith
    have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    simp only [proposed, Nat.add_sub_cancel, show m+2-1=m+1 by omega, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (100 * (m : ℝ)^m) * ((m : ℝ) + 2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hp.le (pow_nonneg hp.le m)]

end OMA.A121669Proof

open Filter Topology OMA.S_oeis_a121669

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a121669.main) := by
  rintro ⟨k, hk, h⟩
  exact (ne_of_gt hk) (tendsto_nhds_unique h OMA.A121669Proof.ratio_tends_to_zero)
