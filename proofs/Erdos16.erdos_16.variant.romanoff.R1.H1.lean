import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1
import Mathlib.NumberTheory.Chebyshev

-- Step Erdos16.erdos_16.variant.romanoff.R1.H1: hypothesis H1 of reduction Erdos16.erdos_16.variant.romanoff.R1
-- Credit: @OrangeHeadz

/-!
Informal plan (the first moment in Romanoff's theorem for 2 ^ k + p).

The sum over n ≤ x of the number of k is the number of pairs (n, k) (Finset.card_sigma).
Let y = x / 2 and L = Nat.log 2 y. Each odd prime p ≤ y and each 1 ≤ k ≤ L give the pair
(p + 2 ^ k, k) with p + 2 ^ k ≤ 2y ≤ x, and this map is injective. So the sum is at least
(π(y) - 1) L.
Since y < 2 ^ (L + 1) and L ≥ 1, log y < 2 L log 2. Chebyshev.pi_ge gives
π(y) log y ≥ y log 2 - log (y + 1), so
  (π(y) - 1) L log 2 ≥ (y log 2 - log (y + 1) - log y) / 2 ≥ y / 8   for y ≥ 50.
As log 2 ≤ 1 and x ≤ 2y + 1, the sum is at least x / 32.
-/

theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  unfold OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1
  refine ⟨1 / 32, by norm_num, 100, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x / 2 := ⟨_, rfl⟩
  have hy1 : 2 * y ≤ x := by omega
  have hy2 : x ≤ 2 * y + 1 := by omega
  have hy50 : 50 ≤ y := by omega
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.log 2 y := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Nat.log_pos (by norm_num) (by omega)
  -- the pairs
  obtain ⟨S, hS⟩ : ∃ S : Finset (Σ _ : ℕ, ℕ), S = (Finset.range (x + 1)).sigma (fun n =>
      (Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)) := ⟨_, rfl⟩
  have hsum : (∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ)) = (S.card : ℝ) := by
    rw [hS, Finset.card_sigma, Nat.cast_sum]
  rw [hsum]
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℕ, Q = ((Finset.range (y + 1)).filter Nat.Prime).erase 2 :=
    ⟨_, rfl⟩
  have hinj : (Q ×ˢ Finset.Icc 1 L).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => (⟨q.1 + 2 ^ q.2, q.2⟩ : Σ _ : ℕ, ℕ))
    · intro q hq
      have hq' := Finset.mem_product.mp hq
      rw [hQ, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hq'
      obtain ⟨⟨hq2, hqy, hqp⟩, hqk⟩ := hq'
      rw [Finset.mem_Icc] at hqk
      have hpow : 2 ^ q.2 ≤ y := Nat.pow_le_of_le_log (by omega) (by omega)
      have hk : q.2 < 2 ^ q.2 := Nat.lt_pow_self (by norm_num)
      have hp1 : 1 ≤ q.1 := hqp.pos
      show (⟨q.1 + 2 ^ q.2, q.2⟩ : Σ _ : ℕ, ℕ) ∈ S
      rw [hS]
      refine Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hqk.1, ?_, ?_, ?_⟩⟩
      · show q.1 + 2 ^ q.2 < x + 1
        omega
      · show q.2 < q.1 + 2 ^ q.2
        omega
      · show 2 ^ q.2 < q.1 + 2 ^ q.2
        omega
      · show (q.1 + 2 ^ q.2 - 2 ^ q.2).Prime
        rw [Nat.add_sub_cancel]
        exact hqp
      · show q.1 + 2 ^ q.2 - 2 ^ q.2 ≠ 2
        rw [Nat.add_sub_cancel]
        exact hq2
    · intro q _ q' _ h
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at h1
      exact Prod.ext (by omega) h2
  rw [Finset.card_product, Nat.card_Icc] at hinj
  have hQcard : Nat.primeCounting y ≤ Q.card + 1 := by
    have h : ((Finset.range (y + 1)).filter Nat.Prime).card = Nat.primeCounting y := by
      show _ = Nat.count Nat.Prime (y + 1)
      rw [Nat.count_eq_card_filter_range]
    rw [← h, hQ, Finset.card_erase_add_one (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩)]
  -- real estimates
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hy50' : (50 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy50
  have hylog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hpi_ge := Chebyshev.pi_ge y
  rw [div_le_iff₀ hylog] at hpi_ge
  have hLlog : Real.log y < 2 * ((L : ℝ) * Real.log 2) := by
    have h1 : y < 2 ^ (L + 1) := by
      rw [hLdef]
      exact Nat.lt_pow_succ_log_self (by norm_num) y
    have h2 : (y : ℝ) < (2 : ℝ) ^ (L + 1) := by exact_mod_cast h1
    have h3 := Real.log_lt_log hy0 h2
    rw [Real.log_pow] at h3
    have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    push_cast at h3
    nlinarith
  have hlog1 : Real.log ((y : ℝ) + 1) ≤ Real.log 8 + (((y : ℝ) + 1) / 8 - 1) := by
    have h : Real.log (((y : ℝ) + 1) / 8) ≤ ((y : ℝ) + 1) / 8 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlogy : Real.log y ≤ Real.log ((y : ℝ) + 1) := Real.log_le_log hy0 (by linarith)
  have h69 : (y : ℝ) * 0.69 ≤ (y : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) hy0.le
  have hQ0 : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  have hQpi : (Nat.primeCounting y : ℝ) ≤ (Q.card : ℝ) + 1 := by exact_mod_cast hQcard
  -- (π - 1) log y ≤ 2 Q L log 2
  have hA : (Q.card : ℝ) * Real.log y ≤ (Q.card : ℝ) * (2 * ((L : ℝ) * Real.log 2)) :=
    mul_le_mul_of_nonneg_left hLlog.le hQ0
  have hB : (Nat.primeCounting y : ℝ) * Real.log y ≤ ((Q.card : ℝ) + 1) * Real.log y :=
    mul_le_mul_of_nonneg_right hQpi hylog.le
  have hC : (y : ℝ) / 4 ≤ 2 * ((Q.card : ℝ) * (L : ℝ) * Real.log 2) := by
    nlinarith
  have hD : (Q.card : ℝ) * (L : ℝ) * Real.log 2 ≤ (Q.card : ℝ) * (L : ℝ) := by
    have hQL : (0 : ℝ) ≤ (Q.card : ℝ) * (L : ℝ) := by positivity
    nlinarith
  have hx : (x : ℝ) ≤ 2 * (y : ℝ) + 1 := by exact_mod_cast hy2
  have hE : (1 : ℝ) / 32 * x ≤ ((Q.card * (L + 1 - 1) : ℕ) : ℝ) := by
    rw [Nat.add_sub_cancel]
    push_cast
    linarith
  exact le_trans hE (by exact_mod_cast hinj)
