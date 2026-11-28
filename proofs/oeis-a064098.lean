import OMAStatements.S_oeis_a064098
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Problem: A064098: Markov-number recurrence doubly exponential growth
-- Credit: @Luckylamb666

open Filter Topology OMA.S_oeis_a064098

namespace OMA_A064098_Proof

lemma a_recurrence (n : ℕ) (hn : 1 ≤ n) :
    a (n + 3) = (a (n + 2) ^ 2 + a (n + 1) ^ 2) / a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

lemma a_props (n : ℕ) (hn : 1 ≤ n) :
    0 < a n ∧ a n ≤ a (n + 1) ∧ a (n + 1) ≤ a (n + 2) ∧
    a n ^ 2 + a (n + 1) ^ 2 + a (n + 2) ^ 2 = 3 * a n * a (n + 1) * a (n + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction k with
  | zero =>
    decide
  | succ k ih =>
    obtain ⟨hpos, hle1, hle2, hmarkov⟩ := ih (by omega)
    have hrec : a (k + 4) = (a (k + 3) ^ 2 + a (k + 2) ^ 2) / a (k + 1) := rfl
    have hnum : a (k + 3) ^ 2 + a (k + 2) ^ 2 = a (k + 1) * (3 * a (k + 2) * a (k + 3) - a (k + 1)) := by
      have hge : a (k + 1) ≤ 3 * a (k + 2) * a (k + 3) := by nlinarith
      zify [hge]
      zify at hmarkov
      linarith
    have ha4 : a (k + 4) = 3 * a (k + 2) * a (k + 3) - a (k + 1) := by
      rw [hrec, hnum, Nat.mul_div_cancel_left _ hpos]
    have hge_sub : a (k + 1) ≤ 3 * a (k + 2) * a (k + 3) := by nlinarith
    have hle3 : a (k + 3) ≤ a (k + 4) := by
      zify [hge_sub] at ha4 ⊢
      nlinarith
    have hmarkov' : a (k + 2) ^ 2 + a (k + 3) ^ 2 + a (k + 4) ^ 2 =
        3 * a (k + 2) * a (k + 3) * a (k + 4) := by
      zify [hge_sub] at ha4 ⊢
      zify at hmarkov
      nlinarith
    exact ⟨by omega, hle2, hle3, hmarkov'⟩

lemma a_linear_rec (n : ℕ) (hn : 1 ≤ n) :
    a (n + 3) = 3 * a (n + 2) * a (n + 1) - a n := by
  obtain ⟨hpos, hle1, hle2, hmarkov⟩ := a_props n hn
  have hrec := a_recurrence n hn
  have hge : a n ≤ 3 * a (n + 2) * a (n + 1) := by nlinarith
  have hnum : a (n + 2) ^ 2 + a (n + 1) ^ 2 = a n * (3 * a (n + 2) * a (n + 1) - a n) := by
    zify [hge]
    zify at hmarkov
    linarith
  rw [hrec, hnum, Nat.mul_div_cancel_left _ hpos]

lemma a_upper_step (n : ℕ) (hn : 1 ≤ n) :
    a (n + 3) ≤ 3 * a (n + 2) * a (n + 1) := by
  rw [a_linear_rec n hn]
  exact Nat.sub_le _ _

lemma a_lower_step (n : ℕ) (hn : 1 ≤ n) :
    2 * a (n + 2) * a (n + 1) ≤ a (n + 3) := by
  obtain ⟨hpos, hle1, hle2, _⟩ := a_props n hn
  rw [a_linear_rec n hn]
  have h1 : a n ≤ a (n + 2) * a (n + 1) := by nlinarith
  have h2 : a n + 2 * a (n + 2) * a (n + 1) ≤ 3 * a (n + 2) * a (n + 1) := by nlinarith
  omega

lemma fib_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Nat.fib n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · decide
    · decide
    · rw [Nat.fib_add_two]
      have := ih k (by omega)
      omega

lemma a_le_three_pow_fib : ∀ n : ℕ, 1 ≤ n → a n ≤ 3 ^ (Nat.fib n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | _ | _ | _ | m
    · omega
    · decide
    · decide
    · decide
    · have h1 := ih (m + 3) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have hstep := a_upper_step (m + 1) (by omega)
      have hf1 : 1 ≤ Nat.fib (m + 2) := fib_pos_of_pos (by omega)
      have hf2 : 1 ≤ Nat.fib (m + 3) := fib_pos_of_pos (by omega)
      have hfib : Nat.fib (m + 4) - 1 = 1 + (Nat.fib (m + 3) - 1) + (Nat.fib (m + 2) - 1) := by
        have : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
        omega
      calc
        a (m + 4) ≤ 3 * a (m + 3) * a (m + 2) := hstep
        _ ≤ 3 * 3 ^ (Nat.fib (m + 3) - 1) * 3 ^ (Nat.fib (m + 2) - 1) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2
            simpa [mul_assoc] using this
        _ = 3 ^ (1 + (Nat.fib (m + 3) - 1) + (Nat.fib (m + 2) - 1)) := by
            rw [pow_add, pow_add, pow_one]
        _ = 3 ^ (Nat.fib (m + 4) - 1) := by rw [← hfib]

lemma two_pow_fib_le_a : ∀ n : ℕ, 4 ≤ n → 2 ^ (Nat.fib (n - 1) - 1) ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | _ | _ | _ | _ | _ | m
    · omega
    · omega
    · omega
    · omega
    · decide
    · decide
    · have h1 := ih (m + 5) (by omega) (by omega)
      have h2 := ih (m + 4) (by omega) (by omega)
      have hstep := a_lower_step (m + 3) (by omega)
      have hf1 : 1 ≤ Nat.fib (m + 3) := fib_pos_of_pos (by omega)
      have hf2 : 1 ≤ Nat.fib (m + 4) := fib_pos_of_pos (by omega)
      have hfib : Nat.fib (m + 5) - 1 = 1 + (Nat.fib (m + 4) - 1) + (Nat.fib (m + 3) - 1) := by
        have : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := Nat.fib_add_two
        omega
      calc
        2 ^ (Nat.fib (m + 6 - 1) - 1)
          = 2 ^ (1 + (Nat.fib (m + 4) - 1) + (Nat.fib (m + 3) - 1)) := by
            rw [show m + 6 - 1 = m + 5 by omega, hfib]
        _ = 2 * 2 ^ (Nat.fib (m + 4) - 1) * 2 ^ (Nat.fib (m + 3) - 1) := by
            rw [pow_add, pow_add, pow_one]
        _ ≤ 2 * a (m + 5) * a (m + 4) := by
            rw [show m + 4 = m + 5 - 1 by omega, show m + 3 = m + 4 - 1 by omega]
            exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
        _ ≤ a (m + 6) := hstep

noncomputable def phi : ℝ := (Real.sqrt 5 + 1) / 2

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma phi_gt_one : 1 < phi := by
  unfold phi
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma phi_lt_two : phi < 2 := by
  unfold phi
  have h5 : Real.sqrt 5 < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma phi_pos : 0 < phi := by linarith [phi_gt_one]

lemma fib_le_phi_pow : ∀ n : ℕ, (Nat.fib n : ℝ) ≤ phi ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · simp
    · simpa using le_of_lt phi_gt_one
    · rw [Nat.fib_add_two, Nat.cast_add]
      have h1 := ih m (by omega)
      have h2 := ih (m + 1) (by omega)
      have hpow : phi ^ (m + 2) = phi ^ m + phi ^ (m + 1) := by
        calc
          phi ^ (m + 2) = phi ^ m * phi ^ 2 := by rw [pow_add]
          _ = phi ^ m * (phi + 1) := by rw [phi_sq]
          _ = phi ^ m + phi ^ (m + 1) := by rw [pow_succ]; ring
      linarith

lemma phi_pow_div_five_le_fib : ∀ n : ℕ, 1 ≤ n → (1 / 5 : ℝ) * phi ^ n ≤ (Nat.fib n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | _ | _ | m
    · omega
    · rw [show Nat.fib 1 = 1 from rfl, Nat.cast_one, pow_one]
      linarith [phi_lt_two]
    · rw [show Nat.fib 2 = 1 from rfl, Nat.cast_one, phi_sq]
      linarith [phi_lt_two]
    · rw [Nat.fib_add_two, Nat.cast_add]
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have hpow : phi ^ (m + 3) = phi ^ (m + 1) + phi ^ (m + 2) := by
        calc
          phi ^ (m + 3) = phi ^ (m + 1) * phi ^ 2 := by rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
          _ = phi ^ (m + 1) * (phi + 1) := by rw [phi_sq]
          _ = phi ^ (m + 1) + phi ^ (m + 2) := by rw [pow_succ]; ring
      linarith

lemma fib_ge_five {n : ℕ} (hn : 5 ≤ n) : 5 ≤ Nat.fib n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    have hmono : Nat.fib (k + 5) ≤ Nat.fib (k + 6) := Nat.fib_mono (by omega)
    rw [show k + 1 + 5 = k + 6 by omega]
    omega

end OMA_A064098_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a064098.main := by
  change Tendsto (fun n : ℕ => Real.log (Real.log (a n)) / n) atTop
    (𝓝 (Real.log OMA_A064098_Proof.phi))
  let φ := OMA_A064098_Proof.phi
  have hφ_pos : 0 < φ := OMA_A064098_Proof.phi_pos
  have hφ_gt1 : 1 < φ := OMA_A064098_Proof.phi_gt_one
  let cLow : ℝ := (1 / 10 : ℝ) * Real.log 2 / φ
  let cHigh : ℝ := Real.log 3
  have hcLow_pos : 0 < cLow := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hcHigh_pos : 0 < cHigh := Real.log_pos (by norm_num)
  have hlow_lim : Tendsto (fun n : ℕ => Real.log cLow / (n : ℝ) + Real.log φ) atTop (𝓝 (Real.log φ)) := by
    have h0 : Tendsto (fun n : ℕ => Real.log cLow / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log cLow)
    simpa using h0.add tendsto_const_nhds
  have hhigh_lim : Tendsto (fun n : ℕ => Real.log cHigh / (n : ℝ) + Real.log φ) atTop (𝓝 (Real.log φ)) := by
    have h0 : Tendsto (fun n : ℕ => Real.log cHigh / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log cHigh)
    simpa using h0.add tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have hna : (0 : ℝ) < (n : ℝ) := by positivity
    have ha_ge : (2 : ℝ) ^ (Nat.fib (n - 1) - 1) ≤ (a n : ℝ) := by
      exact_mod_cast OMA_A064098_Proof.two_pow_fib_le_a n (by omega)
    have hfib5 : 5 ≤ Nat.fib (n - 1) := OMA_A064098_Proof.fib_ge_five (by omega)
    have hfib_half : (1 / 2 : ℝ) * (Nat.fib (n - 1) : ℝ) ≤ ((Nat.fib (n - 1) - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.fib (n - 1)), Nat.cast_one]
      have : (5 : ℝ) ≤ (Nat.fib (n - 1) : ℝ) := by exact_mod_cast hfib5
      linarith
    have hfib_phi : (1 / 5 : ℝ) * φ ^ (n - 1) ≤ (Nat.fib (n - 1) : ℝ) :=
      OMA_A064098_Proof.phi_pow_div_five_le_fib (n - 1) (by omega)
    have hphi_shift : φ ^ n = φ ^ (n - 1) * φ := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.fib (n - 1) - 1) := by positivity
    have hlog_a_ge : cLow * φ ^ n ≤ Real.log (a n) := by
      have h1 : Real.log ((2 : ℝ) ^ (Nat.fib (n - 1) - 1)) ≤ Real.log (a n) :=
        Real.log_le_log hpow_pos ha_ge
      rw [Real.log_pow] at h1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : cLow * φ ^ n ≤ ((Nat.fib (n - 1) - 1 : ℕ) : ℝ) * Real.log 2 := by
        dsimp only [cLow]
        rw [hphi_shift]
        have hmul : (1 / 10 : ℝ) * Real.log 2 / φ * (φ ^ (n - 1) * φ) =
            ((1 / 2 : ℝ) * ((1 / 5 : ℝ) * φ ^ (n - 1))) * Real.log 2 := by
          field_simp [ne_of_gt hφ_pos]
          ring
        rw [hmul]
        nlinarith
      linarith
    have hlog_log_ge : Real.log cLow + (n : ℝ) * Real.log φ ≤ Real.log (Real.log (a n)) := by
      have hcphi_pos : 0 < cLow * φ ^ n := by positivity
      have h1 := Real.log_le_log hcphi_pos hlog_a_ge
      rw [Real.log_mul (ne_of_gt hcLow_pos) (ne_of_gt (pow_pos hφ_pos n)), Real.log_pow] at h1
      exact h1
    rw [le_div_iff₀ hna]
    have : (Real.log cLow / (n : ℝ) + Real.log φ) * (n : ℝ) = Real.log cLow + (n : ℝ) * Real.log φ := by
      field_simp [ne_of_gt hna]
    linarith
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have hna : (0 : ℝ) < (n : ℝ) := by positivity
    have ha_le : (a n : ℝ) ≤ (3 : ℝ) ^ (Nat.fib n) := by
      have h1 := OMA_A064098_Proof.a_le_three_pow_fib n (by omega)
      have h2 : 3 ^ (Nat.fib n - 1) ≤ 3 ^ (Nat.fib n) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      exact_mod_cast h1.trans h2
    have ha_ge2 : (2 : ℝ) ≤ (a n : ℝ) := by
      have h1 := OMA_A064098_Proof.two_pow_fib_le_a n (by omega)
      have hfib5 := OMA_A064098_Proof.fib_ge_five (by omega : 5 ≤ n - 1)
      have h2 : 2 ≤ 2 ^ (Nat.fib (n - 1) - 1) := by
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ (Nat.fib (n - 1) - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast h2.trans h1
    have hlog_a_pos : 0 < Real.log (a n) := Real.log_pos (by linarith)
    have hlog_a_le : Real.log (a n) ≤ cHigh * φ ^ n := by
      have h1 : Real.log (a n) ≤ Real.log ((3 : ℝ) ^ (Nat.fib n)) :=
        Real.log_le_log (by linarith) ha_le
      rw [Real.log_pow] at h1
      have hfib_le := OMA_A064098_Proof.fib_le_phi_pow n
      have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      dsimp only [cHigh]
      nlinarith
    have hlog_log_le : Real.log (Real.log (a n)) ≤ Real.log cHigh + (n : ℝ) * Real.log φ := by
      have h1 := Real.log_le_log hlog_a_pos hlog_a_le
      rw [Real.log_mul (ne_of_gt hcHigh_pos) (ne_of_gt (pow_pos hφ_pos n)), Real.log_pow] at h1
      exact h1
    rw [div_le_iff₀ hna]
    have : (Real.log cHigh / (n : ℝ) + Real.log φ) * (n : ℝ) = Real.log cHigh + (n : ℝ) * Real.log φ := by
      field_simp [ne_of_gt hna]
    linarith
