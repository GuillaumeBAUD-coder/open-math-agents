import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1
import Mathlib

/-! Proof of `Erdos946.erdos_946.variants.heathbrown_lower_bound.R1.H1.R1.H1.R1.H2`:
for fixed `a > 0`, `b : ℕ`, `δ > 0`, `K > 0`, the number of `n ∈ [1, ⌊x⌋]` such that
`a * n + b` is divisible by `p^2` for some prime `p > x^δ` is `O(x^{1 - δ} + √(a x + b))`,
which is eventually `≤ x / (K * (log x)^7)`. -/

namespace OMA.Erdos946SquareLoss

open Filter Finset Real

private lemma card_filter_dvd_linear {a b N q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q) :
    ((Icc 1 N).filter (fun n => q ∣ a * n + b)).card ≤ N / q + 1 := by
  have hcard : (Icc 0 (N / q)).card = N / q + 1 := by
    simp [Nat.card_Icc]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun n => n / q) ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩
  · intro n1 hn1 n2 hn2 hdiv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
    have hstep : ∀ x y : ℕ, q ∣ a * x + b → q ∣ a * y + b → x / q = y / q → y ≤ x → x = y := by
      intro x y hx hy hxy hle
      have hdiff_lt : x - y < q := by
        have h1 := Nat.div_add_mod x q
        have h2 := Nat.div_add_mod y q
        rw [hxy] at h1
        have hm1 := Nat.mod_lt x hq
        have hm2 := Nat.mod_lt y hq
        omega
      have hdvd_diff : q ∣ a * (x - y) := by
        have hsub : q ∣ (a * x + b) - (a * y + b) := Nat.dvd_sub hx hy
        have heq : (a * x + b) - (a * y + b) = a * (x - y) := by
          rw [Nat.mul_sub_left_distrib]
          have : a * y ≤ a * x := Nat.mul_le_mul_left a hle
          omega
        rwa [heq] at hsub
      have hdvd : q ∣ x - y := hcop.symm.dvd_of_dvd_mul_left hdvd_diff
      rcases Nat.eq_zero_or_pos (x - y) with h0 | hpos
      · omega
      · have := Nat.le_of_dvd hpos hdvd
        omega
    rcases le_total n2 n1 with hle | hle
    · exact hstep n1 n2 hn1.2 hn2.2 hdiv hle
    · exact (hstep n2 n1 hn2.2 hn1.2 hdiv.symm hle).symm

private lemma sum_inv_sq_le (M U : ℕ) (hM : 1 ≤ M) :
    ∑ p ∈ Icc (M + 1) U, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 / (M : ℝ) - 1 / ((max M U : ℕ) : ℝ) := by
  induction U with
  | zero =>
    have hI : Icc (M + 1) 0 = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [hI, Finset.sum_empty, Nat.max_eq_left (Nat.zero_le M), sub_self]
  | succ k ih =>
    by_cases hlt : k < M
    · have hI : Icc (M + 1) (k + 1) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        omega
      rw [hI, Finset.sum_empty, Nat.max_eq_left (by omega), sub_self]
    · push Not at hlt
      rw [Finset.sum_Icc_succ_top (by omega : M + 1 ≤ k + 1)]
      have hmax1 : max M k = k := Nat.max_eq_right hlt
      have hmax2 : max M (k + 1) = k + 1 := Nat.max_eq_right (by omega)
      rw [hmax1] at ih
      rw [hmax2]
      have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 (by omega)
      have hk1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
      have hstep : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
        have hdiff : (1 : ℝ) / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) =
            1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp [hkpos.ne', (show (k : ℝ) + 1 ≠ 0 by positivity)]
          ring
        rw [hdiff]
        refine one_div_le_one_div_of_le (mul_pos hkpos hk1pos) ?_
        push_cast
        nlinarith
      linarith

private lemma solve_H2 :
    OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1.H2 := by
  classical
  intro a b ha δ K hδ hK
  have hlog1 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 7 ≤ x ^ δ / (4 * K) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (7 : ℝ) hδ
    have hbound := hlo.bound (show (0 : ℝ) < 1 / (4 * K) by positivity)
    filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlogpos : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hxpos : 0 < x := by linarith
    have hrp : (Real.log x) ^ (7 : ℝ) = (Real.log x) ^ (7 : ℕ) := Real.rpow_natCast _ 7
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos _),
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _), hrp, one_div_mul_eq_div] at hx
    exact hx
  have hlog2 : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ 7 ≤ x ^ ((1 : ℝ) / 2) / (2 * K * Real.sqrt ((a : ℝ) + (b : ℝ))) := by
    have hsqpos : 0 < Real.sqrt ((a : ℝ) + (b : ℝ)) := by
      apply Real.sqrt_pos.2
      have : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.2 ha
      positivity
    have hlo := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
    have hbound := hlo.bound (show (0 : ℝ) < 1 / (2 * K * Real.sqrt ((a : ℝ) + (b : ℝ))) by positivity)
    filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlogpos : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hxpos : 0 < x := by linarith
    have hrp : (Real.log x) ^ (7 : ℝ) = (Real.log x) ^ (7 : ℕ) := Real.rpow_natCast _ 7
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos _),
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _), hrp, one_div_mul_eq_div] at hx
    exact hx
  have hpow_large : ∀ᶠ x : ℝ in atTop, ((max (a + 1) 2 : ℕ) : ℝ) ≤ x ^ δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℝ), hpow_large, hlog1, hlog2] with x hx2 hpow hl1 hl2
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  set N : ℕ := ⌊x⌋₊
  set M : ℕ := ⌊x ^ δ⌋₊
  set U : ℕ := Nat.sqrt (a * N + b)
  have hMge : max (a + 1) 2 ≤ M := Nat.le_floor hpow
  have hM1 : 1 ≤ M := le_trans (by omega) hMge
  have hMa : a + 1 ≤ M := le_trans (le_max_left _ _) hMge
  set E : Finset ℕ := (Icc 1 N).filter fun n =>
    ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b
  have hsub : E ⊆ (Icc (M + 1) U).biUnion fun p =>
      if Nat.Coprime a (p ^ 2) then (Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b) else ∅ := by
    intro n hn
    simp only [E, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, p, hp_mem, hp_gt, hp_sq⟩ := hn
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_lo : M + 1 ≤ p := by
      have h1 : (M : ℝ) ≤ x ^ δ := Nat.floor_le (Real.rpow_nonneg hxpos.le δ)
      have h2 : (M : ℝ) < (p : ℝ) := lt_of_le_of_lt h1 hp_gt
      have h3 : M < p := by exact_mod_cast h2
      omega
    have hp_hi : p ≤ U := by
      have hpos_ab : 0 < a * n + b := by
        have : 1 ≤ a * n := Nat.mul_pos ha hn1
        omega
      have hle1 : p ^ 2 ≤ a * n + b := Nat.le_of_dvd hpos_ab hp_sq
      have hle2 : a * n + b ≤ a * N + b := by
        have := Nat.mul_le_mul_left a hnN
        omega
      exact Nat.le_sqrt.2 (by nlinarith)
    have hcop : Nat.Coprime a (p ^ 2) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm]
      apply hp_prime.coprime_iff_not_dvd.2
      intro hdvd
      have := Nat.le_of_dvd ha hdvd
      omega
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_Icc.2 ⟨hp_lo, hp_hi⟩, ?_⟩
    rw [if_pos hcop, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn1, hnN⟩, hp_sq⟩
  have hE_nat : E.card ≤ ∑ p ∈ Icc (M + 1) U, (N / p ^ 2 + 1) := by
    calc
      E.card ≤ ((Icc (M + 1) U).biUnion fun p =>
          if Nat.Coprime a (p ^ 2) then (Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b) else ∅).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ p ∈ Icc (M + 1) U,
          (if Nat.Coprime a (p ^ 2) then (Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b) else ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Icc (M + 1) U, (N / p ^ 2 + 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        split_ifs with hcop
        · have hp1 : 0 < p := by
            have := (Finset.mem_Icc.1 hp).1
            omega
          have hp_pos : 0 < p ^ 2 := by positivity
          exact card_filter_dvd_linear hp_pos hcop
        · simp
  have hE_real : (E.card : ℝ) ≤ x / (M : ℝ) + (U : ℝ) := by
    have h1 : (E.card : ℝ) ≤ ∑ p ∈ Icc (M + 1) U, ((N : ℝ) / ((p : ℝ) ^ 2) + 1) := by
      have hcast : (E.card : ℝ) ≤ ∑ p ∈ Icc (M + 1) U, ((N / p ^ 2 + 1 : ℕ) : ℝ) := by
        exact_mod_cast hE_nat
      refine le_trans hcast (Finset.sum_le_sum fun p _ => ?_)
      push_cast
      have hdiv : ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) ^ 2) := by
        have := Nat.cast_div_le (m := N) (n := p ^ 2) (α := ℝ)
        simpa using this
      linarith
    have h2 : ∑ p ∈ Icc (M + 1) U, ((N : ℝ) / ((p : ℝ) ^ 2) + 1) =
        (N : ℝ) * (∑ p ∈ Icc (M + 1) U, (1 : ℝ) / ((p : ℝ) ^ 2)) + ((Icc (M + 1) U).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun p _ => ?_
        ring
      · simp
    have hsum_le : ∑ p ∈ Icc (M + 1) U, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
      have hs := sum_inv_sq_le M U hM1
      have hnn : (0 : ℝ) ≤ 1 / ((max M U : ℕ) : ℝ) := by positivity
      linarith
    have hcard_le : ((Icc (M + 1) U).card : ℝ) ≤ (U : ℝ) := by
      have hc : (Icc (M + 1) U).card ≤ U := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hc
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hxpos.le
    calc
      (E.card : ℝ) ≤ (N : ℝ) * (∑ p ∈ Icc (M + 1) U, (1 : ℝ) / ((p : ℝ) ^ 2)) +
          ((Icc (M + 1) U).card : ℝ) := h2 ▸ h1
      _ ≤ x * (1 / (M : ℝ)) + (U : ℝ) := by
        have hmul : (N : ℝ) * (∑ p ∈ Icc (M + 1) U, (1 : ℝ) / ((p : ℝ) ^ 2)) ≤ x * (1 / (M : ℝ)) := by
          refine mul_le_mul hNx hsum_le (Finset.sum_nonneg fun _ _ => by positivity) hxpos.le
        linarith
      _ = x / (M : ℝ) + (U : ℝ) := by ring
  have hM_half : x ^ δ / 2 ≤ (M : ℝ) := by
    have hlt : x ^ δ - 1 < (M : ℝ) := Nat.sub_one_lt_floor (x ^ δ)
    have hge2 : (2 : ℝ) ≤ x ^ δ := le_trans (by exact_mod_cast le_max_right (a + 1) 2) hpow
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.2 hM1
  have hterm1 : K * (x / (M : ℝ)) ≤ x / (2 * (Real.log x) ^ 7) := by
    have h1 : x / (M : ℝ) ≤ 2 * x / x ^ δ := by
      have hdiv : 1 / (M : ℝ) ≤ 2 / x ^ δ := by
        rw [div_le_div_iff₀ hMpos (Real.rpow_pos_of_pos hxpos δ)]
        linarith
      calc
        x / (M : ℝ) = x * (1 / (M : ℝ)) := by ring
        _ ≤ x * (2 / x ^ δ) := mul_le_mul_of_nonneg_left hdiv hxpos.le
        _ = 2 * x / x ^ δ := by ring
    have h2 : K * (2 * x / x ^ δ) ≤ x / (2 * (Real.log x) ^ 7) := by
      have hlog7 : 0 < (Real.log x) ^ 7 := pow_pos hlogpos 7
      have hxd : 0 < x ^ δ := Real.rpow_pos_of_pos hxpos δ
      have hl1' : 4 * K * (Real.log x) ^ 7 ≤ x ^ δ := by
        have := (le_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).1 hl1
        linarith
      have hmul : 2 * K * x * (2 * (Real.log x) ^ 7) ≤ x * x ^ δ := by
        have : 2 * K * x * (2 * (Real.log x) ^ 7) = x * (4 * K * (Real.log x) ^ 7) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hl1' hxpos.le
      rw [show K * (2 * x / x ^ δ) = (2 * K * x) / x ^ δ by ring,
          div_le_div_iff₀ hxd (by positivity)]
      exact hmul
    exact le_trans (mul_le_mul_of_nonneg_left h1 hK.le) h2
  have hU_le : (U : ℝ) ≤ Real.sqrt ((a : ℝ) + (b : ℝ)) * x ^ ((1 : ℝ) / 2) := by
    have hU2 : ((U : ℝ)) ^ 2 ≤ ((a : ℝ) + (b : ℝ)) * x := by
      have hnat : U ^ 2 ≤ a * N + b := by
        simpa [pow_two] using Nat.sqrt_le (a * N + b)
      have hcast : ((U : ℝ)) ^ 2 ≤ (a : ℝ) * (N : ℝ) + (b : ℝ) := by exact_mod_cast hnat
      have hNx : (N : ℝ) ≤ x := Nat.floor_le hxpos.le
      have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      nlinarith
    have hsq := Real.sqrt_le_sqrt hU2
    rw [Real.sqrt_sq (Nat.cast_nonneg U), Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow x] at hsq
    exact hsq
  have hterm2 : K * (U : ℝ) ≤ x / (2 * (Real.log x) ^ 7) := by
    have hsqpos : 0 < Real.sqrt ((a : ℝ) + (b : ℝ)) := by
      apply Real.sqrt_pos.2
      have : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.2 ha
      positivity
    have hlog7 : 0 < (Real.log x) ^ 7 := pow_pos hlogpos 7
    have hx12 : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _
    have hmul_eq : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hl2' : 2 * K * Real.sqrt ((a : ℝ) + (b : ℝ)) * (Real.log x) ^ 7 ≤ x ^ ((1 : ℝ) / 2) := by
      have := (le_div_iff₀ (show (0 : ℝ) < 2 * K * Real.sqrt ((a : ℝ) + (b : ℝ)) by positivity)).1 hl2
      linarith
    have h1 : K * (U : ℝ) ≤ K * (Real.sqrt ((a : ℝ) + (b : ℝ)) * x ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hU_le hK.le
    refine le_trans h1 ?_
    rw [le_div_iff₀ (by positivity)]
    calc
      K * (Real.sqrt ((a : ℝ) + (b : ℝ)) * x ^ ((1 : ℝ) / 2)) * (2 * (Real.log x) ^ 7)
          = (2 * K * Real.sqrt ((a : ℝ) + (b : ℝ)) * (Real.log x) ^ 7) * x ^ ((1 : ℝ) / 2) := by ring
      _ ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hl2' hx12.le
      _ = x := hmul_eq
  calc
    K * (E.card : ℝ) ≤ K * (x / (M : ℝ) + (U : ℝ)) := mul_le_mul_of_nonneg_left hE_real hK.le
    _ = K * (x / (M : ℝ)) + K * (U : ℝ) := by ring
    _ ≤ x / (2 * (Real.log x) ^ 7) + x / (2 * (Real.log x) ^ 7) := add_le_add hterm1 hterm2
    _ = x / (Real.log x) ^ 7 := by ring

end OMA.Erdos946SquareLoss

theorem OMA.solution :
    OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1.H2 :=
  OMA.Erdos946SquareLoss.solve_H2
