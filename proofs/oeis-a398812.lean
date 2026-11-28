import OMAStatements.S_oeis_a398812

open Finset
-- Problem: A398812, a(n)/n^2 -> 1 (A138808(n) <= n tau(n) <= 2 n sqrt n).
-- Credit: @bnb9001

namespace OMA_A398812_Proof

open Filter Topology OMA.S_oeis_a398812

lemma card_divisors_le_two_sqrt (n : ℕ) : n.divisors.card ≤ 2 * Nat.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set S1 := n.divisors.filter (fun d => d * d ≤ n)
  set S2 := n.divisors.filter (fun d => ¬ d * d ≤ n)
  have hsplit : S1.card + S2.card = n.divisors.card :=
    card_filter_add_card_filter_not (s := n.divisors) (fun d => d * d ≤ n)
  have h1 : S1.card ≤ Nat.sqrt n := by
    calc S1.card ≤ (Icc 1 (Nat.sqrt n)).card := by
          apply card_le_card
          intro d hd
          simp only [S1, mem_filter, Nat.mem_divisors] at hd
          simp only [mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 hn, Nat.le_sqrt.2 hd.2⟩
      _ = Nat.sqrt n := by simp
  have h2 : S2.card ≤ S1.card := by
    apply card_le_card_of_injOn (fun d => n / d)
    · intro d hd
      simp only [S2, S1, mem_coe, mem_filter, Nat.mem_divisors, not_le] at hd ⊢
      obtain ⟨⟨hdn, hn0⟩, hdd⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      have hq : d * (n / d) = n := Nat.mul_div_cancel' hdn
      refine ⟨⟨Nat.div_dvd_of_dvd hdn, hn0⟩, ?_⟩
      have hlt : n / d < d := by
        by_contra h
        rw [not_lt] at h
        have : d * d ≤ d * (n / d) := Nat.mul_le_mul_left d h
        omega
      calc n / d * (n / d) ≤ d * (n / d) := Nat.mul_le_mul_right _ hlt.le
        _ = n := hq
    · intro x hx y hy hxy
      simp only [S2, mem_coe, mem_filter, Nat.mem_divisors] at hx hy
      have := congrArg (fun t => n / t) hxy
      simp only at this
      rwa [Nat.div_div_self hx.1.1 hx.1.2, Nat.div_div_self hy.1.1 hy.1.2] at this
  omega

lemma B_le (n : ℕ) : B n ≤ n * n.divisors.card := by
  unfold B
  calc _ ≤ (n.divisors.biUnion (fun p => Icc 1 p ×ˢ Icc 1 (n / p))).card := by
        apply card_le_card
        intro xy hxy
        simp only [mem_filter, mem_product, mem_Icc] at hxy
        obtain ⟨⟨⟨hx1, -⟩, hy1, -⟩, p, hp, hxp, hyp⟩ := hxy
        simp only [mem_biUnion, mem_product, mem_Icc]
        exact ⟨p, hp, ⟨hx1, hxp⟩, hy1, hyp⟩
    _ ≤ ∑ p ∈ n.divisors, (Icc 1 p ×ˢ Icc 1 (n / p)).card := card_biUnion_le
    _ = ∑ p ∈ n.divisors, n := by
        refine sum_congr rfl fun p hp => ?_
        rw [card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]
        exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hp)
    _ = n * n.divisors.card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma B_le_sq (n : ℕ) : B n ≤ n ^ 2 := by
  unfold B
  calc _ ≤ (Icc 1 n ×ˢ Icc 1 n).card := card_filter_le _ _
    _ = n ^ 2 := by simp [sq]

end OMA_A398812_Proof

open Filter Topology OMA_A398812_Proof OMA.S_oeis_a398812 in
theorem OMA.solution : type_of% @OMA.S_oeis_a398812.main := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 2 / Real.sqrt n) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hsq).const_mul 2
    simpa [div_eq_mul_inv] using this
  have hB : Tendsto (fun n : ℕ => (B n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (B n : ℝ) ≤ n * (2 * Real.sqrt n) := by
      have hb : (B n : ℝ) ≤ n * (n.divisors.card : ℝ) := by exact_mod_cast B_le n
      have hd : (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
        have : (n.divisors.card : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
          exact_mod_cast card_divisors_le_two_sqrt n
        exact this.trans (by gcongr; exact Real.nat_sqrt_le_real_sqrt)
      exact hb.trans (by gcongr)
    have hsqn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    rw [div_le_div_iff₀ (by positivity) hs0]
    nlinarith
  have := hB.const_sub 1
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold a
  rw [Nat.cast_sub (B_le_sq n)]
  push_cast
  field_simp
