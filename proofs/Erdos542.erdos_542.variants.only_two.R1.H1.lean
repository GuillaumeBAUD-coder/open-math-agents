import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1
import Mathlib.Analysis.Complex.ExponentialBounds

-- Step Erdos542.erdos_542.variants.only_two.R1.H1: hypothesis H1 of reduction Erdos542.erdos_542.variants.only_two.R1
-- Credit: @MrZaow
-- H1 := ∀ n : ℕ, 12 ≤ n → ...

private def sumAux (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumAux f k + f (k + 1)

private lemma sumAux_eq_sum_Icc (f : ℕ → ℕ) (n : ℕ) :
    sumAux f n = ∑ m ∈ Finset.Icc 1 n, f m := by
  induction n with
  | zero => simp [sumAux]
  | succ k ih =>
    rw [sumAux, ih]
    have hsub : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsub, Finset.sum_insert hnot, add_comm]

private def term1 (n m : ℕ) : ℕ :=
  if n < 2 * m ∧ m % 3 ≠ 0 then (10000 + m - 1) / m else 0

private def term2 (n b : ℕ) : ℕ :=
  if n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0 then (10000 + 2 * b - 1) / (2 * b) else 0

private def checkRange : ℕ → ℕ → Bool
  | _, 0 => true
  | start, len + 1 =>
    decide (3 * (sumAux (term1 start) start + sumAux (term2 start) start) ≤ 20000) &&
      checkRange (start + 1) len

private lemma checkRange_sound :
    ∀ len start n, checkRange start len = true → start ≤ n → n < start + len →
      3 * (sumAux (term1 n) n + sumAux (term2 n) n) ≤ 20000
  | 0, _, _, _, h1, h2 => by omega
  | len + 1, start, n, hchk, h1, h2 => by
    simp only [checkRange, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact hchk.1
    · exact checkRange_sound len (start + 1) n hchk.2 (by omega) (by omega)

private lemma check_small_1 : checkRange 12 60 = true := by decide

set_option maxRecDepth 2000 in
private lemma check_small_2 : checkRange 72 60 = true := by decide

set_option maxRecDepth 2000 in
private lemma check_small_3 : checkRange 132 48 = true := by decide

private lemma small_bound {n : ℕ} (h12 : 12 ≤ n) (hlt : n < 180) :
    3 * (sumAux (term1 n) n + sumAux (term2 n) n) ≤ 20000 := by
  by_cases h1 : n < 72
  · exact checkRange_sound 60 12 n check_small_1 h12 (by omega)
  · by_cases h2 : n < 132
    · exact checkRange_sound 60 72 n check_small_2 (by omega) (by omega)
    · exact checkRange_sound 48 132 n check_small_3 (by omega) (by omega)

private lemma inv_le_ceilDiv {B m : ℕ} (hB : 0 < B) (hm : 0 < m) :
    (1 : ℝ) / (m : ℝ) ≤ (((B + m - 1) / m : ℕ) : ℝ) / (B : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  rw [div_le_div_iff₀ hmR hBR, one_mul]
  have hnat : B ≤ (B + m - 1) / m * m := by
    have hdiv := Nat.div_add_mod (B + m - 1) m
    have hmod := Nat.mod_lt (B + m - 1) hm
    rw [Nat.mul_comm] at hdiv
    omega
  exact_mod_cast hnat

private lemma inv_le_log_sub {k : ℕ} (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hk1R : (0 : ℝ) < (k - 1 : ℕ) := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this
  have hlog := Real.log_le_sub_one_of_pos (div_pos hk1R hkR)
  rw [Real.log_div hk1R.ne' hkR.ne'] at hlog
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have h1 : 1 ≤ k := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hsub] at hlog
  have hdiv : ((k : ℝ) - 1) / (k : ℝ) - 1 = -((1 : ℝ) / (k : ℝ)) := by
    field_simp
    ring
  rw [hsub]
  linarith

private lemma telescope_log (k1 k2 : ℕ) (hle : k1 ≤ k2) :
    ∑ k ∈ Finset.Icc k1 k2, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (k2 : ℝ) - Real.log ((k1 - 1 : ℕ) : ℝ) := by
  induction k2, hle using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

private lemma sum_nonmult3_le_log {a b : ℕ} (ha : 6 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ (Finset.Icc a b).filter (fun m => m % 3 ≠ 0), (1 : ℝ) / (m : ℝ) ≤
      (2 / 3 : ℝ) * Real.log (((b / 3 : ℕ) : ℝ) / (((a / 3 - 1 : ℕ) : ℝ))) := by
  let s1 := (Finset.Icc a b).filter (fun m => m % 3 ≠ 0)
  let k1 := a / 3
  let k2 := b / 3
  have hk1 : 2 ≤ k1 := by omega
  have hk12 : k1 ≤ k2 := Nat.div_le_div_right hab
  let s2 := (Finset.Icc k1 k2).biUnion fun k => ({3 * k + 1, 3 * k + 2} : Finset ℕ)
  have hsub : s1 ⊆ s2 := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_biUnion]
    refine ⟨m / 3, Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hm.1.1, Nat.div_le_div_right hm.1.2⟩, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hstep1 : ∑ m ∈ s1, (1 : ℝ) / (m : ℝ) ≤ ∑ m ∈ s2, (1 : ℝ) / (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hdisj : ((Finset.Icc k1 k2 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun k => ({3 * k + 1, 3 * k + 2} : Finset ℕ) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    omega
  have hstep2 : ∑ m ∈ s2, (1 : ℝ) / (m : ℝ) =
      ∑ k ∈ Finset.Icc k1 k2,
        ((1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) + (1 : ℝ) / ((3 * k + 2 : ℕ) : ℝ)) := by
    dsimp [s2]
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_pair (by omega)]
  have hstep3 :
      ∑ k ∈ Finset.Icc k1 k2,
          ((1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) + (1 : ℝ) / ((3 * k + 2 : ℕ) : ℝ)) ≤
        ∑ k ∈ Finset.Icc k1 k2, (2 / 3 : ℝ) * (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := hk1.trans (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < k := by positivity
    have hpair :
        (1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) + (1 : ℝ) / ((3 * k + 2 : ℕ) : ℝ) ≤
          (2 / 3 : ℝ) * ((1 : ℝ) / (k : ℝ)) := by
      have h1 : (1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) ≤ 1 / (3 * (k : ℝ)) := by
        gcongr
        norm_cast
        omega
      have h2 : (1 : ℝ) / ((3 * k + 2 : ℕ) : ℝ) ≤ 1 / (3 * (k : ℝ)) := by
        gcongr
        norm_cast
        omega
      have hsum_eq : 1 / (3 * (k : ℝ)) + 1 / (3 * (k : ℝ)) = (2 / 3 : ℝ) * ((1 : ℝ) / (k : ℝ)) := by
        ring
      linarith [h1, h2, hsum_eq]
    exact hpair.trans (mul_le_mul_of_nonneg_left (inv_le_log_sub hk2) (by norm_num))
  have htel :
      ∑ k ∈ Finset.Icc k1 k2, (2 / 3 : ℝ) * (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
        (2 / 3 : ℝ) * Real.log (((k2 : ℕ) : ℝ) / (((k1 - 1 : ℕ) : ℝ))) := by
    rw [← Finset.mul_sum, telescope_log k1 k2 hk12]
    have hk2_pos : (0 : ℝ) < k2 := by
      have : 0 < k2 := by omega
      exact_mod_cast this
    have hk1_pos : (0 : ℝ) < (k1 - 1 : ℕ) := by
      have : 0 < k1 - 1 := by omega
      exact_mod_cast this
    rw [Real.log_div hk2_pos.ne' hk1_pos.ne']
  exact (hstep1.trans_eq hstep2).trans (hstep3.trans_eq htel)

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1.H1 := by
  intro n hn12
  by_cases hn_small : n < 180
  · have hsum1 :
        ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m ≤
          ((sumAux (term1 n) n : ℕ) : ℝ) / 10000 := by
      rw [sumAux_eq_sum_Icc, Nat.cast_sum, Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_le_sum fun m hm => ?_
      have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
      by_cases hcond : n < 2 * m ∧ m % 3 ≠ 0
      · dsimp only [term1]
        rw [if_pos hcond, if_pos hcond]
        exact inv_le_ceilDiv (B := 10000) (by decide) hm_pos
      · dsimp only [term1]
        rw [if_neg hcond, if_neg hcond]
        simp
    have hsum2 :
        ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
            (1 : ℝ) / (2 * b) ≤
          ((sumAux (term2 n) n : ℕ) : ℝ) / 10000 := by
      rw [sumAux_eq_sum_Icc, Nat.cast_sum, Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_le_sum fun b hb => ?_
      have hb_pos : 0 < b := (Finset.mem_Icc.mp hb).1
      by_cases hcond : n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0
      · dsimp only [term2]
        rw [if_pos hcond, if_pos hcond]
        have hdiv := inv_le_ceilDiv (B := 10000) (m := 2 * b) (by decide) (by omega)
        simpa [Nat.cast_mul, Nat.cast_ofNat] using hdiv
      · dsimp only [term2]
        rw [if_neg hcond, if_neg hcond]
        simp
    have hchk_nat : 3 * (sumAux (term1 n) n + sumAux (term2 n) n) ≤ 20000 :=
      small_bound hn12 hn_small
    have hchkR : 3 * ((sumAux (term1 n) n : ℝ) + (sumAux (term2 n) n : ℝ)) ≤ 20000 := by
      exact_mod_cast hchk_nat
    linarith
  · have hn180 : 180 ≤ n := by omega
    have hnR : (180 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn180
    have hsub1 : (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) ⊆
        (Finset.Icc (n / 2 + 1) n).filter (fun m => m % 3 ≠ 0) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      omega
    have hle1 :
        ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / (m : ℝ) ≤
          (2 / 3 : ℝ) * Real.log (2 * (n : ℝ) / ((n : ℝ) - 9)) := by
      have hs :
          ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / (m : ℝ) ≤
            ∑ m ∈ (Finset.Icc (n / 2 + 1) n).filter (fun m => m % 3 ≠ 0), (1 : ℝ) / (m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
      have hlog := sum_nonmult3_le_log (a := n / 2 + 1) (b := n) (by omega) (by omega)
      have harg : (((n / 3 : ℕ) : ℝ) / ((((n / 2 + 1) / 3 - 1 : ℕ) : ℝ))) ≤
          2 * (n : ℝ) / ((n : ℝ) - 9) := by
        have hnum : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
          have : 3 * (n / 3) ≤ n := by omega
          have : (3 : ℝ) * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        have hden : ((n : ℝ) - 9) / 6 ≤ (((n / 2 + 1) / 3 - 1 : ℕ) : ℝ) := by
          have : n - 9 ≤ 6 * ((n / 2 + 1) / 3 - 1) := by omega
          have : (n : ℝ) - 9 ≤ 6 * (((n / 2 + 1) / 3 - 1 : ℕ) : ℝ) := by
            have h1 : 9 ≤ n := by omega
            have h2 : ((n - 9 : ℕ) : ℝ) ≤ (6 * ((n / 2 + 1) / 3 - 1) : ℕ) := by exact_mod_cast this
            rw [Nat.cast_sub h1, Nat.cast_mul] at h2
            norm_num at h2
            linarith
          linarith
        have hden_pos : 0 < ((n : ℝ) - 9) / 6 := by linarith
        have hdiv := div_le_div₀ (by positivity) hnum hden_pos hden
        refine hdiv.trans_eq ?_
        field_simp
        ring
      have harg_pos : 0 < (((n / 3 : ℕ) : ℝ) / ((((n / 2 + 1) / 3 - 1 : ℕ) : ℝ))) := by
        have ha : 0 < n / 3 := by omega
        have hb : 0 < (n / 2 + 1) / 3 - 1 := by omega
        positivity
      exact hs.trans (hlog.trans (mul_le_mul_of_nonneg_left (Real.log_le_log harg_pos harg) (by norm_num)))
    have hsub2 : (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) ⊆
        (Finset.Icc (n / 3 + 1) (n / 2)).filter (fun b => b % 3 ≠ 0) := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
      omega
    have hle2 :
        ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
            (1 : ℝ) / (2 * b) ≤
          (1 / 3 : ℝ) * Real.log (3 * (n : ℝ) / (2 * ((n : ℝ) - 14))) := by
      have hrew :
          ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
              (1 : ℝ) / (2 * b) =
            (1 / 2 : ℝ) *
              ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
                (1 : ℝ) / (b : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by ring
      rw [hrew]
      have hs :
          ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0), (1 : ℝ) / (b : ℝ) ≤
            ∑ b ∈ (Finset.Icc (n / 3 + 1) (n / 2)).filter (fun b => b % 3 ≠ 0), (1 : ℝ) / (b : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity
      have hlog := sum_nonmult3_le_log (a := n / 3 + 1) (b := n / 2) (by omega) (by omega)
      have harg : ((((n / 2) / 3 : ℕ) : ℝ) / ((((n / 3 + 1) / 3 - 1 : ℕ) : ℝ))) ≤
          3 * (n : ℝ) / (2 * ((n : ℝ) - 14)) := by
        have hnum : (((n / 2) / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := by
          have : 6 * ((n / 2) / 3) ≤ n := by omega
          have : (6 : ℝ) * (((n / 2) / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        have hden : ((n : ℝ) - 14) / 9 ≤ (((n / 3 + 1) / 3 - 1 : ℕ) : ℝ) := by
          have : n - 14 ≤ 9 * ((n / 3 + 1) / 3 - 1) := by omega
          have : (n : ℝ) - 14 ≤ 9 * (((n / 3 + 1) / 3 - 1 : ℕ) : ℝ) := by
            have h1 : 14 ≤ n := by omega
            have h2 : ((n - 14 : ℕ) : ℝ) ≤ (9 * ((n / 3 + 1) / 3 - 1) : ℕ) := by exact_mod_cast this
            rw [Nat.cast_sub h1, Nat.cast_mul] at h2
            norm_num at h2
            linarith
          linarith
        have hden_pos : 0 < ((n : ℝ) - 14) / 9 := by linarith
        have hdiv := div_le_div₀ (by positivity) hnum hden_pos hden
        refine hdiv.trans_eq ?_
        field_simp
        ring
      have harg_pos : 0 < ((((n / 2) / 3 : ℕ) : ℝ) / ((((n / 3 + 1) / 3 - 1 : ℕ) : ℝ))) := by
        have ha : 0 < (n / 2) / 3 := by omega
        have hb : 0 < (n / 3 + 1) / 3 - 1 := by omega
        positivity
      have hcombined := hs.trans (hlog.trans (mul_le_mul_of_nonneg_left (Real.log_le_log harg_pos harg) (by norm_num)))
      linarith
    have hlog_comb :
        (2 / 3 : ℝ) * Real.log (2 * (n : ℝ) / ((n : ℝ) - 9)) +
            (1 / 3 : ℝ) * Real.log (3 * (n : ℝ) / (2 * ((n : ℝ) - 14))) =
          (1 / 3 : ℝ) * Real.log (6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14))) := by
      have ha_pos : 0 < 2 * (n : ℝ) / ((n : ℝ) - 9) := by
        have : 0 < (n : ℝ) - 9 := by linarith
        positivity
      have hb_pos : 0 < 3 * (n : ℝ) / (2 * ((n : ℝ) - 14)) := by
        have : 0 < (n : ℝ) - 14 := by linarith
        positivity
      have ha2_pos : 0 < (2 * (n : ℝ) / ((n : ℝ) - 9)) ^ 2 := sq_pos_of_pos ha_pos
      have hmul_log :
          2 * Real.log (2 * (n : ℝ) / ((n : ℝ) - 9)) + Real.log (3 * (n : ℝ) / (2 * ((n : ℝ) - 14))) =
            Real.log ((2 * (n : ℝ) / ((n : ℝ) - 9)) ^ 2 * (3 * (n : ℝ) / (2 * ((n : ℝ) - 14)))) := by
        rw [show (2 : ℝ) * Real.log (2 * (n : ℝ) / ((n : ℝ) - 9)) =
            Real.log ((2 * (n : ℝ) / ((n : ℝ) - 9)) ^ (2 : ℕ)) by rw [Real.log_pow]; norm_num,
          ← Real.log_mul ha2_pos.ne' hb_pos.ne']
      have hrat :
          (2 * (n : ℝ) / ((n : ℝ) - 9)) ^ 2 * (3 * (n : ℝ) / (2 * ((n : ℝ) - 14))) =
            6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14)) := by
        field_simp
        ring
      rw [hrat] at hmul_log
      linarith
    have hpoly : 60 * (n : ℝ) ^ 3 ≤ 73 * ((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14) := by
      let t : ℝ := (n : ℝ) - 180
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid : 73 * ((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14) - 60 * (n : ℝ) ^ 3 =
          13 * t ^ 3 + 4684 * t ^ 2 + 446949 * t + 4422438 := by
        dsimp [t]; ring
      have hnonneg : 0 ≤ 13 * t ^ 3 + 4684 * t ^ 2 + 446949 * t + 4422438 := by positivity
      linarith
    have hden_pos : 0 < ((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14) := by
      have h1 : 0 < (n : ℝ) - 9 := by linarith
      have h2 : 0 < (n : ℝ) - 14 := by linarith
      positivity
    have hnum_pos : 0 < 6 * (n : ℝ) ^ 3 := by positivity
    have hexp : (73 / 10 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    have hrat_exp : 6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14)) ≤ Real.exp 2 := by
      have h73 : 6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14)) ≤ 73 / 10 := by
        rw [div_le_div_iff₀ hden_pos (by norm_num)]
        linarith
      exact h73.trans hexp
    have hlog_exp : Real.log (6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14))) ≤ 2 := by
      have hpos_all : 0 < 6 * (n : ℝ) ^ 3 / (((n : ℝ) - 9) ^ 2 * ((n : ℝ) - 14)) :=
        div_pos hnum_pos hden_pos
      exact (Real.log_le_log hpos_all hrat_exp).trans_eq (Real.log_exp 2)
    linarith
