import OMAReductions.R_Erdos360_erdos_360_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Upper bound parameter existence and sieve estimate for Erdos Problem 360 -/

open Filter

section Helpers

private lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ a ∈ Finset.range M, r ^ a ≤ (1 - r)⁻¹ := by
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have hsum : (1 - r) * ∑ a ∈ Finset.range M, r ^ a = 1 - r ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  rw [← one_div, le_div_iff₀ h1, mul_comm, hsum]
  linarith [pow_nonneg hr0 M]

private lemma sum_mult_smooth_le (f : ℕ → ℝ) (hf0 : ∀ a, 0 ≤ f a) (hf1 : f 1 = 1)
    (hfmul : ∀ a b, f (a * b) = f a * f b) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hfQ : ∀ p ∈ Q, f p < 1) (M : ℕ) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ Q), f k ≤
      ∏ p ∈ Q, (1 - f p)⁻¹ := by
  classical
  induction Q using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.subset_empty, Nat.primeFactors_eq_empty]
    have hsub : (Finset.Icc 1 M).filter (fun k => k = 0 ∨ k = 1) ⊆ {1} := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hk ⊢
      omega
    calc
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k = 0 ∨ k = 1), f k
          ≤ ∑ k ∈ ({1} : Finset ℕ), f k := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf0 _
      _ = 1 := by simp [hf1]
  | insert p Q hpQ ih =>
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have hfp1 : f p < 1 := hfQ p (Finset.mem_insert_self p Q)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    have hfQ' : ∀ q ∈ Q, f q < 1 := fun q hq => hfQ q (Finset.mem_insert_of_mem hq)
    let S₁ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ insert p Q)
    let S₀ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ Q)
    let g : ℕ → ℕ × ℕ := fun k => (k.factorization p, k / p ^ (k.factorization p))
    have hginj : Set.InjOn g S₁ := by
      intro k₁ _ k₂ _ h
      calc
        k₁ = p ^ (k₁.factorization p) * (k₁ / p ^ (k₁.factorization p)) :=
          (Nat.mul_div_cancel' (Nat.ordProj_dvd k₁ p)).symm
        _ = p ^ (g k₁).1 * (g k₁).2 := rfl
        _ = p ^ (g k₂).1 * (g k₂).2 := by rw [h]
        _ = k₂ := Nat.mul_div_cancel' (Nat.ordProj_dvd k₂ p)
    have hgmem : ∀ k ∈ S₁, g k ∈ Finset.range (M + 1) ×ˢ S₀ := by
      intro k hk
      simp only [S₁, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hkM⟩, hkp⟩ := hk
      have hk0 : k ≠ 0 := by omega
      have hpow_dvd : p ^ (k.factorization p) ∣ k := Nat.ordProj_dvd k p
      have hpow_le : p ^ (k.factorization p) ≤ k := Nat.ordProj_le p hk0
      have ha_lt : k.factorization p < M + 1 := by
        have h2a : 2 ^ (k.factorization p) ≤ p ^ (k.factorization p) :=
          Nat.pow_le_pow_left hp.two_le _
        have hlt : k.factorization p < 2 ^ (k.factorization p) := Nat.lt_two_pow_self
        omega
      have hm1 : 1 ≤ k / p ^ (k.factorization p) := Nat.div_pos hpow_le (pow_pos hp.pos _)
      have hmM : k / p ^ (k.factorization p) ≤ M := (Nat.div_le_self k _).trans hkM
      have hm_not_dvd : ¬ p ∣ k / p ^ (k.factorization p) := by
        have hm0 : k / p ^ (k.factorization p) ≠ 0 := by omega
        rw [hp.dvd_iff_one_le_factorization hm0, Nat.factorization_div hpow_dvd]
        simp [hp.factorization]
      have hmQ : (k / p ^ (k.factorization p)).primeFactors ⊆ Q := by
        intro q hq
        have hq_mem : q ∈ k.primeFactors := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpow_dvd) hk0 hq
        have hqp : q ≠ p := by
          intro hqe
          subst hqe
          exact hm_not_dvd (Nat.dvd_of_mem_primeFactors hq)
        exact (Finset.mem_insert.mp (hkp hq_mem)).resolve_left hqp
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmM⟩, hmQ⟩⟩
    have hf_pow : ∀ a : ℕ, f (p ^ a) = (f p) ^ a := by
      intro a
      induction a with
      | zero => simp [hf1]
      | succ a iha => rw [pow_succ, hfmul, iha, pow_succ]
    have hf_g : ∀ k : ℕ, f k = (f p) ^ (g k).1 * f (g k).2 := by
      intro k
      calc
        f k = f (p ^ (k.factorization p) * (k / p ^ (k.factorization p))) := by
            rw [Nat.mul_div_cancel' (Nat.ordProj_dvd k p)]
        _ = f (p ^ (k.factorization p)) * f (k / p ^ (k.factorization p)) := hfmul _ _
        _ = (f p) ^ (g k).1 * f (g k).2 := by rw [hf_pow]
    have hsum_le : ∑ k ∈ S₁, f k ≤
        ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 := by
      calc
        ∑ k ∈ S₁, f k = ∑ k ∈ S₁, (f p) ^ (g k).1 * f (g k).2 :=
          Finset.sum_congr rfl fun k _ => hf_g k
        _ = ∑ x ∈ S₁.image g, (f p) ^ x.1 * f x.2 :=
          (Finset.sum_image (f := fun x : ℕ × ℕ => (f p) ^ x.1 * f x.2) hginj).symm
        _ ≤ ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
            exact hgmem k hk
          · intro x _ _
            exact mul_nonneg (pow_nonneg (hf0 p) _) (hf0 _)
    have hprod_sum : ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 =
        (∑ a ∈ Finset.range (M + 1), (f p) ^ a) * ∑ m ∈ S₀, f m := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only
      rw [← Finset.mul_sum]
    have hgeom : ∑ a ∈ Finset.range (M + 1), (f p) ^ a ≤ (1 - f p)⁻¹ :=
      geom_sum_le_inv_one_sub (hf0 p) hfp1 (M + 1)
    have hih : ∑ m ∈ S₀, f m ≤ ∏ q ∈ Q, (1 - f q)⁻¹ := ih hQ' hfQ'
    have hS0_nonneg : 0 ≤ ∑ m ∈ S₀, f m := Finset.sum_nonneg fun _ _ => hf0 _
    have hinv_nonneg : 0 ≤ (1 - f p)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hfp1).le
    rw [Finset.prod_insert hpQ]
    calc
      ∑ k ∈ S₁, f k ≤ (∑ a ∈ Finset.range (M + 1), (f p) ^ a) * ∑ m ∈ S₀, f m :=
        hsum_le.trans_eq hprod_sum
      _ ≤ (1 - f p)⁻¹ * ∏ q ∈ Q, (1 - f q)⁻¹ :=
        mul_le_mul hgeom hih hS0_nonneg hinv_nonneg

private lemma log_add_one_le_sum_inv (w : ℕ) :
    Real.log (w + 1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le w))]
    have hw0 : (0 : ℝ) < (w + 1 : ℕ) := by positivity
    have hw1 : (0 : ℝ) < (w + 2 : ℕ) := by positivity
    have hlog : Real.log ((w + 1 + 1 : ℕ) : ℝ) - Real.log ((w + 1 : ℕ) : ℝ) ≤
        ((w + 1 : ℕ) : ℝ)⁻¹ := by
      have hdiv : (0 : ℝ) < ((w + 1 + 1 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div hw1.ne' hw0.ne'] at h1
      have h2 : ((w + 1 + 1 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ) - 1 = ((w + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      linarith
    push_cast at hlog ih ⊢
    linarith

private lemma prod_one_sub_inv_primesLE_le (w : ℕ) (hw : 1 ≤ w) :
    ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) ≤ (Real.log (w + 1 : ℝ))⁻¹ := by
  have hlog_pos : 0 < Real.log (w + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < w + 1)
  have hsub : Finset.Icc 1 w ⊆ (Finset.Icc 1 w).filter (fun k => k.primeFactors ⊆ Nat.primesLE w) := by
    intro k hk
    refine Finset.mem_filter.mpr ⟨hk, fun p hp => ?_⟩
    have hkm := (Finset.mem_Icc.mp hk).2
    have hpk : p ≤ k := Nat.le_of_mem_primeFactors hp
    exact Nat.mem_primesLE.mpr ⟨hpk.trans hkm, Nat.prime_of_mem_primeFactors hp⟩
  have hsum : ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := by
    calc
      ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹
          ≤ ∑ m ∈ (Finset.Icc 1 w).filter (fun k => k.primeFactors ⊆ Nat.primesLE w), (m : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := by
        apply sum_mult_smooth_le (fun k => (k : ℝ)⁻¹) (fun _ => by positivity) (by simp)
          (fun a b => by push_cast; ring) (Nat.primesLE w)
          (fun p hp => Nat.prime_of_mem_primesLE hp)
          (fun p hp => by
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
            have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
            linarith) w
  have hprod_inv : Real.log (w + 1 : ℝ) ≤ (∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹))⁻¹ := by
    calc
      Real.log (w + 1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ := log_add_one_le_sum_inv w
      _ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := hsum
      _ = (∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹))⁻¹ := by rw [Finset.prod_inv_distrib]
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  exact (le_inv_comm₀ hlog_pos hprod_pos).mp hprod_inv

private lemma sq_add_one_le_two_pow_pred {j : ℕ} (hj : 7 ≤ j) : (j + 1) ^ 2 ≤ 2 ^ (j - 1) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    have hk1 : k + 1 - 1 = k - 1 + 1 := by omega
    calc
      (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := hstep
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1 - 1) := by rw [hk1, pow_succ, mul_comm]

private lemma dyadic_sum_prime_inv_le {z n : ℕ} (hz : 128 ≤ z) (hzn : z ≤ n)
    (hnz : n < (2 * z) ^ 5) :
    ∑ p ∈ (Nat.primesLE n).filter (fun p => z < p), (p : ℝ)⁻¹ ≤ 90 := by
  let a := Nat.log 2 z
  let b := Nat.log 2 n
  have ha7 : 7 ≤ a := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    norm_num
    exact hz
  have hab : a ≤ b := Nat.log_mono_right hzn
  let P := (Nat.primesLE n).filter (fun p => z < p)
  let B := fun j : ℕ => (Nat.primesLE (2 ^ (j + 1))).filter (fun p => 2 ^ j ≤ p ∧ p < 2 ^ (j + 1))
  have hsub : P ⊆ (Finset.Icc a b).biUnion B := by
    intro p hp
    simp only [P, B, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_biUnion, Finset.mem_Icc] at hp ⊢
    refine ⟨Nat.log 2 p, ⟨Nat.log_mono_right hp.2.le, Nat.log_mono_right hp.1.1⟩, ?_⟩
    exact ⟨⟨(Nat.lt_pow_succ_log_self Nat.one_lt_two p).le, hp.1.2⟩,
      Nat.pow_log_le_self 2 hp.1.2.ne_zero, Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩
  have hdisj : Set.PairwiseDisjoint (Finset.Icc a b : Set ℕ) B := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have hi := (Finset.mem_filter.mp hpi).2
    have hj' := (Finset.mem_filter.mp hpj).2
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hpow : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have hpow : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
      omega
  have hsum1 : ∑ p ∈ P, (p : ℝ)⁻¹ ≤
      ∑ j ∈ Finset.Icc a b, ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) := by
    calc
      ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ p ∈ (Finset.Icc a b).biUnion B, (p : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ j ∈ Finset.Icc a b, ∑ p ∈ B j, (p : ℝ)⁻¹ := Finset.sum_biUnion hdisj
      _ ≤ ∑ j ∈ Finset.Icc a b, ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hcard_le : (B j).card ≤ (Nat.primesLE (2 ^ (j + 1))).card :=
          Finset.card_filter_le _ _
        calc
          ∑ p ∈ B j, (p : ℝ)⁻¹ ≤ ∑ _p ∈ B j, (2 ^ j : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro p hp
            have h2j : (2 ^ j : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
            exact inv_anti₀ (by positivity) h2j
          _ = ((B j).card : ℝ) * (2 ^ j : ℝ)⁻¹ := by simp [nsmul_eq_mul]
          _ ≤ ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
  have hj_bound : ∀ j ∈ Finset.Icc a b,
      ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) ≤ 9 / (a + 1 : ℝ) := by
    intro j hj
    have hj7 : 7 ≤ j := ha7.trans (Finset.mem_Icc.mp hj).1
    have hja : a ≤ j := (Finset.mem_Icc.mp hj).1
    have hpi := Chebyshev.pi_le_log4_mul_div (x := ((2 ^ (j + 1) : ℕ) : ℝ))
      (by exact_mod_cast (by have : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2; omega : 1 < 2 ^ (j + 1)))
    have hfloor : ⌊((2 ^ (j + 1) : ℕ) : ℝ)⌋₊ = 2 ^ (j + 1) := Nat.floor_natCast _
    rw [hfloor, ← Nat.primesLE_card_eq_primeCounting] at hpi
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_sqrt : Real.log (Real.sqrt ((2 ^ (j + 1) : ℕ) : ℝ)) = ((j + 1 : ℝ) / 2) * Real.log 2 := by
      rw [Real.log_sqrt (by positivity), Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      ring
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hterm1 : Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) / Real.log (Real.sqrt ((2 ^ (j + 1) : ℕ) : ℝ)) =
        8 * (2 ^ j : ℝ) / (j + 1 : ℝ) := by
      rw [hlog_sqrt, hlog4]
      push_cast
      rw [pow_succ']
      field_simp [hlog2_pos.ne']
      ring
    have hterm2 : Real.sqrt ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (2 ^ j : ℝ) / (j + 1 : ℝ) := by
      rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
      have hsq : ((j + 1) ^ 2 : ℕ) ≤ 2 ^ (j - 1) := sq_add_one_le_two_pow_pred hj7
      have hpow : 2 ^ (j + 1) * (j + 1) ^ 2 ≤ (2 ^ j) ^ 2 := by
        calc
          2 ^ (j + 1) * (j + 1) ^ 2 ≤ 2 ^ (j + 1) * 2 ^ (j - 1) := Nat.mul_le_mul_left _ hsq
          _ = 2 ^ (j + 1 + (j - 1)) := (pow_add 2 _ _).symm
          _ = 2 ^ (2 * j) := by congr 1; omega
          _ = (2 ^ j) ^ 2 := by rw [mul_comm, pow_mul]
      exact_mod_cast hpow
    have hdiv : ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) ≤ 9 / (j + 1 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      calc
        ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) ≤
            8 * (2 ^ j : ℝ) / (j + 1 : ℝ) + (2 ^ j : ℝ) / (j + 1 : ℝ) := by linarith
        _ = 9 / (j + 1 : ℝ) * (2 ^ j : ℝ) := by ring
    calc
      ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) ≤ 9 / (j + 1 : ℝ) := hdiv
      _ ≤ 9 / (a + 1 : ℝ) := by
        gcongr
  have hb_lt : b < 5 * (a + 2) := by
    have h2b : 2 ^ b ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hza : z < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two z
    have hpow_lt : 2 ^ b < 2 ^ (5 * (a + 2)) := by
      calc
        2 ^ b ≤ n := h2b
        _ < (2 * z) ^ 5 := hnz
        _ ≤ (2 * 2 ^ (a + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
        _ = (2 ^ (a + 2)) ^ 5 := by rw [← pow_succ']
        _ = 2 ^ (5 * (a + 2)) := by rw [← pow_mul, mul_comm]
    exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow_lt
  have hcard_le : (Finset.Icc a b).card ≤ 10 * (a + 1) := by
    rw [Nat.card_Icc]
    omega
  calc
    ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ j ∈ Finset.Icc a b, ((Nat.primesLE (2 ^ (j + 1))).card : ℝ) / (2 ^ j : ℝ) :=
      hsum1
    _ ≤ ∑ _j ∈ Finset.Icc a b, 9 / (a + 1 : ℝ) := Finset.sum_le_sum hj_bound
    _ = ((Finset.Icc a b).card : ℝ) * (9 / (a + 1 : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ (10 * (a + 1 : ℝ)) * (9 / (a + 1 : ℝ)) := by
      gcongr
      exact_mod_cast hcard_le
    _ = 90 := by field_simp; ring

private lemma prod_one_sub_inv_gt_le {z n : ℕ} (hz : 128 ≤ z) (hzn : z ≤ n)
    (hnz : n < (2 * z) ^ 5) :
    ∏ p ∈ (Nat.primesLE n).filter (fun p => z < p), (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp 180 := by
  have hterm : ∀ p ∈ (Nat.primesLE n).filter (fun p => z < p),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
    intro p hp
    have hpz : z < p := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have hinv : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + ((p : ℝ) - 1)⁻¹ := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    have h2p : ((p : ℝ) - 1)⁻¹ ≤ 2 * (p : ℝ)⁻¹ := by
      rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hp1 (by linarith)]
      linarith
    rw [hinv]
    exact (by linarith : 1 + ((p : ℝ) - 1)⁻¹ ≤ 2 * (p : ℝ)⁻¹ + 1).trans (Real.add_one_le_exp _)
  calc
    ∏ p ∈ (Nat.primesLE n).filter (fun p => z < p), (1 - (p : ℝ)⁻¹)⁻¹
        ≤ ∏ p ∈ (Nat.primesLE n).filter (fun p => z < p), Real.exp (2 * (p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpz : z < p := (Finset.mem_filter.mp hp).2
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
        have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
        exact inv_nonneg.mpr (by linarith)
      · exact hterm
    _ = Real.exp (∑ p ∈ (Nat.primesLE n).filter (fun p => z < p), 2 * (p : ℝ)⁻¹) :=
      (Real.exp_sum _ _).symm
    _ = Real.exp (2 * ∑ p ∈ (Nat.primesLE n).filter (fun p => z < p), (p : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
    _ ≤ Real.exp 180 := by
      apply Real.exp_le_exp.mpr
      linarith [dyadic_sum_prime_inv_le hz hzn hnz]

private lemma card_primeFactors_le_log2 {n : ℕ} (hn : 1 ≤ n) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

private lemma prod_primeFactors_sqrt_inv_le {n : ℕ} (hn : 1 ≤ n) :
    ∏ p ∈ n.primeFactors, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) := by
  let S₁ := n.primeFactors.filter (fun p => p ≤ 64)
  let S₂ := n.primeFactors.filter (fun p => ¬ p ≤ 64)
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ 64)
    (fun p => (1 - (Real.sqrt p)⁻¹)⁻¹)
  have hS1_card : S₁.card ≤ 65 := by
    calc
      S₁.card ≤ (Finset.range 65).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2; omega)
      _ = 65 := Finset.card_range 65
  have hS1_bound : ∏ p ∈ S₁, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ (4 : ℝ) ^ 65 := by
    have hle : ∀ p ∈ S₁, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ (4 : ℝ) := by
      intro p hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
      have hsq : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp2)
      have hinv : (Real.sqrt p)⁻¹ ≤ (Real.sqrt 2)⁻¹ := inv_anti₀ (by positivity) hsq
      have hrt2 : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num), show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
        exact Real.le_sqrt_of_sq_le (by norm_num)
      have hpos : 0 < 1 - (Real.sqrt p)⁻¹ := by linarith
      rw [← one_div, div_le_iff₀ hpos]
      linarith
    calc
      ∏ p ∈ S₁, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ ∏ _p ∈ S₁, (4 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
          have hsq : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp2)
          have hinv : (Real.sqrt p)⁻¹ ≤ (Real.sqrt 2)⁻¹ := inv_anti₀ (by positivity) hsq
          have h1 : (Real.sqrt 2)⁻¹ < 1 := by
            rw [inv_lt_one_iff₀]
            right
            exact Real.lt_sqrt_of_sq_lt (by norm_num)
          exact inv_nonneg.mpr (by linarith)
        · exact hle
      _ = (4 : ℝ) ^ S₁.card := by simp
      _ ≤ (4 : ℝ) ^ 65 := pow_le_pow_right₀ (by norm_num) hS1_card
  have hS2_card : S₂.card ≤ Nat.log 2 n :=
    (Finset.card_filter_le _ _).trans (card_primeFactors_le_log2 hn)
  have hS2_bound : ∏ p ∈ S₂, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hle : ∀ p ∈ S₂, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ (8 / 7 : ℝ) := by
      intro p hp
      have hp64 : 64 < p := by have := (Finset.mem_filter.mp hp).2; omega
      have hsq : 8 < Real.sqrt p := Real.lt_sqrt_of_sq_lt (by exact_mod_cast (by omega : 64 < p))
      have hinv : (Real.sqrt p)⁻¹ < 1 / 8 := by
        rw [← one_div]
        exact one_div_lt_one_div_of_lt (by norm_num) hsq
      have hpos : 0 < 1 - (Real.sqrt p)⁻¹ := by linarith
      rw [← one_div, div_le_iff₀ hpos]
      linarith
    have hprod_pow : ∏ p ∈ S₂, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ (8 / 7 : ℝ) ^ (Nat.log 2 n) := by
      calc
        ∏ p ∈ S₂, (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ ∏ _p ∈ S₂, (8 / 7 : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp64 : 64 < p := by have := (Finset.mem_filter.mp hp).2; omega
            have hsq : 8 < Real.sqrt p := Real.lt_sqrt_of_sq_lt (by exact_mod_cast (by omega : 64 < p))
            have hinv : (Real.sqrt p)⁻¹ < 1 / 8 := by
              rw [← one_div]
              exact one_div_lt_one_div_of_lt (by norm_num) hsq
            exact inv_nonneg.mpr (by linarith)
          · exact hle
        _ = (8 / 7 : ℝ) ^ S₂.card := by rw [Finset.prod_const]
        _ ≤ (8 / 7 : ℝ) ^ (Nat.log 2 n) := pow_le_pow_right₀ (by norm_num) hS2_card
    have h5 : ((8 / 7 : ℝ) ^ (Nat.log 2 n)) ^ 5 ≤ (n : ℝ) := by
      calc
        ((8 / 7 : ℝ) ^ (Nat.log 2 n)) ^ 5 = ((8 / 7 : ℝ) ^ 5) ^ (Nat.log 2 n) := by
          rw [← pow_mul, mul_comm, pow_mul]
        _ ≤ (2 : ℝ) ^ (Nat.log 2 n) := by
          gcongr
          norm_num
        _ ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hrpow : (8 / 7 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      calc
        (8 / 7 : ℝ) ^ (Nat.log 2 n) = (((8 / 7 : ℝ) ^ (Nat.log 2 n)) ^ 5) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul (by positivity)]
          norm_num
        _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by gcongr
    exact hprod_pow.trans hrpow
  have hS2_nonneg : 0 ≤ ∏ p ∈ S₂, (1 - (Real.sqrt p)⁻¹)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hp64 : 64 < p := by have := (Finset.mem_filter.mp hp).2; omega
    have hsq : 8 < Real.sqrt p := Real.lt_sqrt_of_sq_lt (by exact_mod_cast (by omega : 64 < p))
    have hinv : (Real.sqrt p)⁻¹ < 1 / 8 := by
      rw [← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) hsq
    exact inv_nonneg.mpr (by linarith)
  rw [← hsplit]
  exact mul_le_mul hS1_bound hS2_bound hS2_nonneg (by positivity)

private lemma prime_interval_diff_eventually :
    ∀ᶠ X : ℕ in atTop, 3 * (X : ℝ) / Real.log X ≤ (Nat.primeCounting (16 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by
  have hlog16 : ∀ᶠ X : ℕ in atTop, Real.log (16 * X : ℝ) ≤ (3 / 2 : ℝ) * Real.log X := by
    have h := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [h.eventually_ge_atTop (2 * Real.log 16), eventually_ge_atTop 2] with X hX hX2
    simp only [Function.comp_def] at hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    rw [Real.log_mul (by norm_num) hXpos.ne']
    linarith
  have hlog16_1 : ∀ᶠ X : ℕ in atTop, Real.log (16 * X + 1 : ℝ) ≤ Real.log 2 * X := by
    have ho : Real.log =o[atTop] (fun x : ℝ => x) := by
      simpa using isLittleO_log_rpow_atTop (r := 1) zero_lt_one
    have hc : (0 : ℝ) < Real.log 2 / 32 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
    have hb := (ho.comp_tendsto ((tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 16)).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ))))).bound hc
    filter_upwards [hb, eventually_ge_atTop 2] with X hX hX2
    simp only [Function.comp_def, Real.norm_eq_abs] at hX
    have h1 : 0 ≤ Real.log (16 * (X : ℝ) + 1) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 16 * X + 1))
    have h2 : 0 ≤ 16 * (X : ℝ) + 1 := by positivity
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hX
    have hXpos : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hsqrt_le : ∀ᶠ X : ℕ in atTop, Real.sqrt X ≤ Real.log 2 * X / Real.log X := by
    have ho : (fun x : ℝ => Real.sqrt x * Real.log x) =o[atTop] (fun x : ℝ => x) := by
      have h' := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).mul_isBigO
        (Asymptotics.isBigO_refl (fun x : ℝ => x ^ (1 / 2 : ℝ)) atTop)
      have h'' : (fun x : ℝ => Real.log x * Real.sqrt x) =o[atTop] (fun x : ℝ => x) := by
        refine h'.congr' ?_ ?_
        · filter_upwards [eventually_ge_atTop 0] with x hx
          rw [Real.sqrt_eq_rpow]
        · filter_upwards [eventually_ge_atTop 1] with x hx
          rw [← Real.rpow_add (by linarith), show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
      refine h''.congr' ?_ (Eventually.of_forall fun _ => rfl)
      filter_upwards with x
      ring
    have hb := (ho.comp_tendsto tendsto_natCast_atTop_atTop).bound (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    filter_upwards [hb, eventually_ge_atTop 2] with X hX hX2
    simp only [Function.comp_def, Real.norm_eq_abs] at hX
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    have hX0 : 0 ≤ (X : ℝ) := by positivity
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlogX.le), abs_of_nonneg hX0] at hX
    exact (le_div_iff₀ hlogX).mpr hX
  filter_upwards [hlog16, hlog16_1, hsqrt_le, eventually_ge_atTop 16] with X h16 h16_1 hsq hX16
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlog16X : 0 < Real.log (16 * (X : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 16 * X))
  have hge := Chebyshev.pi_ge (16 * X)
  have hle := Chebyshev.pi_le_log4_mul_div (x := (X : ℝ)) (by exact_mod_cast (by omega : 1 < X))
  rw [Nat.floor_natCast] at hle
  push_cast at hge
  have hpi_ge : 10 * Real.log 2 * (X : ℝ) / Real.log X ≤ (Nat.primeCounting (16 * X) : ℝ) := by
    have hnum : 15 * Real.log 2 * (X : ℝ) ≤ (16 * (X : ℝ) * Real.log 2 - Real.log (16 * (X : ℝ) + 1)) := by linarith
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    have hnonneg : 0 ≤ 16 * (X : ℝ) * Real.log 2 - Real.log (16 * (X : ℝ) + 1) := by nlinarith
    have h1 : 10 * Real.log 2 * (X : ℝ) / Real.log X = (15 * Real.log 2 * (X : ℝ)) / ((3 / 2 : ℝ) * Real.log X) := by
      ring
    rw [h1]
    calc
      (15 * Real.log 2 * (X : ℝ)) / ((3 / 2 : ℝ) * Real.log X)
          ≤ (16 * (X : ℝ) * Real.log 2 - Real.log (16 * (X : ℝ) + 1)) / ((3 / 2 : ℝ) * Real.log X) := by
        gcongr
      _ ≤ (16 * (X : ℝ) * Real.log 2 - Real.log (16 * (X : ℝ) + 1)) / Real.log (16 * (X : ℝ)) := by
        exact div_le_div_of_nonneg_left hnonneg hlog16X h16
      _ ≤ (Nat.primeCounting (16 * X) : ℝ) := hge
  have hpi_le : (Nat.primeCounting X : ℝ) ≤ 5 * Real.log 2 * (X : ℝ) / Real.log X := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
    have hlog_sq : Real.log (Real.sqrt X) = (1 / 2 : ℝ) * Real.log X := by
      rw [Real.log_sqrt (by positivity)]; ring
    have hterm : Real.log 4 * (X : ℝ) / Real.log (Real.sqrt X) = 4 * Real.log 2 * (X : ℝ) / Real.log X := by
      rw [hlog4, hlog_sq]; ring
    have hsum5 : 4 * Real.log 2 * (X : ℝ) / Real.log X + Real.log 2 * (X : ℝ) / Real.log X =
        5 * Real.log 2 * (X : ℝ) / Real.log X := by ring
    linarith
  have h5log2 : 3 ≤ 5 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hdiff_eq : 5 * Real.log 2 * (X : ℝ) / Real.log X =
      10 * Real.log 2 * (X : ℝ) / Real.log X - 5 * Real.log 2 * (X : ℝ) / Real.log X := by ring
  calc
    3 * (X : ℝ) / Real.log X ≤ 5 * Real.log 2 * (X : ℝ) / Real.log X := by gcongr
    _ ≤ (Nat.primeCounting (16 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by linarith

private lemma exists_prime_interval_not_dvd {X n : ℕ} (hn : 1 ≤ n)
    (hcard : (n.primeFactors.card : ℝ) < (Nat.primeCounting (16 * X) : ℝ) - (Nat.primeCounting X : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p ≤ 16 * X ∧ ¬ p ∣ n := by
  let P := (Nat.primesLE (16 * X)).filter (fun p => X < p)
  have hP_eq : P = Nat.primesLE (16 * X) \ Nat.primesLE X := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
    by_cases hp : p.Prime <;> simp [hp]
  have hsub : Nat.primesLE X ⊆ Nat.primesLE (16 * X) :=
    Nat.primesLE_mono (by omega)
  have hP_card : (P.card : ℝ) = (Nat.primeCounting (16 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by
    rw [hP_eq, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting, Nat.cast_sub (Nat.monotone_primeCounting (by omega))]
  have hlt : n.primeFactors.card < P.card := by
    exact_mod_cast (hP_card ▸ hcard)
  have hne : (P \ n.primeFactors).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
    exact hlt.not_ge (Finset.card_le_card hempty)
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff] at hp
  have hpP := Finset.mem_filter.mp hp.1
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hpP.1
  have hp16 : p ≤ 16 * X := Nat.le_of_mem_primesLE hpP.1
  refine ⟨p, hpp, hpP.2, hp16, fun hdvd => hp.2 ?_⟩
  exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, by omega⟩

private lemma R_prime_card_bound {n d z : ℕ} (hn : 1 ≤ n) (_hd : 1 ≤ d) (hz : 128 ≤ z)
    (hzn : z ≤ n) (hnz : n < (2 * z) ^ 5) :
    let S := (Nat.primesLE z).filter (fun p => ¬ p ∣ n)
    let R' := (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)
    (R'.card : ℝ) ≤
      Real.sqrt (n / d : ℕ) * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) +
      (6 * Real.exp 180) * ((n / d : ℕ) : ℝ) / Real.log z * ((n : ℝ) / n.totient) := by
  intro S R'
  let X := n / d
  let A := R'.filter (fun t => t.primeFactors ⊆ n.primeFactors)
  let B := R'.filter (fun t => ¬ t.primeFactors ⊆ n.primeFactors)
  have hsplit : R'.card = A.card + B.card :=
    (Finset.card_filter_add_card_filter_not (s := R') (p := fun t => t.primeFactors ⊆ n.primeFactors)).symm
  have hA_sub : A ⊆ (Finset.Icc 1 X).filter (fun t => t.primeFactors ⊆ n.primeFactors) :=
    fun t ht => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1,
      (Finset.mem_filter.mp ht).2⟩
  have hA_card : (A.card : ℝ) ≤ Real.sqrt X * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hsumA : (A.card : ℝ) ≤ Real.sqrt X * ∑ t ∈ A, (Real.sqrt t)⁻¹ := by
      calc
        (A.card : ℝ) = ∑ _t ∈ A, (1 : ℝ) := by simp
        _ ≤ ∑ t ∈ A, Real.sqrt X * (Real.sqrt t)⁻¹ := by
          apply Finset.sum_le_sum
          intro t ht
          have ht_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
          have htpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < t))
          have hle : Real.sqrt t ≤ Real.sqrt X := Real.sqrt_le_sqrt (by exact_mod_cast ht_mem.2)
          calc
            1 = Real.sqrt t * (Real.sqrt t)⁻¹ := (mul_inv_cancel₀ htpos.ne').symm
            _ ≤ Real.sqrt X * (Real.sqrt t)⁻¹ := by gcongr
        _ = Real.sqrt X * ∑ t ∈ A, (Real.sqrt t)⁻¹ := (Finset.mul_sum ..).symm
    have hsum_smooth : ∑ t ∈ A, (Real.sqrt t)⁻¹ ≤
        ∏ p ∈ n.primeFactors, (1 - (Real.sqrt p)⁻¹)⁻¹ := by
      calc
        ∑ t ∈ A, (Real.sqrt t)⁻¹
            ≤ ∑ t ∈ (Finset.Icc 1 X).filter (fun t => t.primeFactors ⊆ n.primeFactors), (Real.sqrt t)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hA_sub fun _ _ _ => by positivity
        _ ≤ ∏ p ∈ n.primeFactors, (1 - (Real.sqrt p)⁻¹)⁻¹ := by
          apply sum_mult_smooth_le (fun t => (Real.sqrt t)⁻¹) (fun _ => by positivity) (by simp)
            (fun a b => by rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv])
            n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
            (fun p hp => by
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
              have hsq : 1 < Real.sqrt p := Real.lt_sqrt_of_sq_lt (by linarith)
              exact inv_lt_one_of_one_lt₀ hsq) X
    calc
      (A.card : ℝ) ≤ Real.sqrt X * ∑ t ∈ A, (Real.sqrt t)⁻¹ := hsumA
      _ ≤ Real.sqrt X * ∏ p ∈ n.primeFactors, (1 - (Real.sqrt p)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum_smooth (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt X * (4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (prod_primeFactors_sqrt_inv_le hn) (Real.sqrt_nonneg _)
      _ = Real.sqrt X * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) := by ring
  let K := (Finset.Icc 1 (X / (z + 1))).filter (fun k => ∀ q ∈ S, ¬ q ∣ k)
  have hB_sub : B ⊆ K.biUnion (fun k => (Nat.primesLE (X / k)).image (· * k)) := by
    intro t ht
    obtain ⟨htR, htNot⟩ := Finset.mem_filter.mp ht
    obtain ⟨htX, htS⟩ := Finset.mem_filter.mp htR
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp htX).1
    have htXle : t ≤ X := (Finset.mem_Icc.mp htX).2
    rw [Finset.not_subset] at htNot
    obtain ⟨p, hp_fac, hp_n⟩ := htNot
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_fac
    have hpdvd : p ∣ t := Nat.dvd_of_mem_primeFactors hp_fac
    have hp_not_n : ¬ p ∣ n := fun hdvd => hp_n (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, by omega⟩)
    have hpz : z < p := by
      by_contra hle
      have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hpp⟩, hp_not_n⟩
      exact htS p hpS hpdvd
    let k := t / p
    have hpk : k * p = t := Nat.div_mul_cancel hpdvd
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp h0)
      rw [hk0, zero_mul] at hpk
      omega
    have hk_le : k ≤ X / (z + 1) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc
        k * (z + 1) ≤ k * p := Nat.mul_le_mul_left k (by omega)
        _ = t := hpk
        _ ≤ X := htXle
    have hkS : ∀ q ∈ S, ¬ q ∣ k := fun q hq hdvd => htS q hq (hdvd.trans ⟨p, hpk.symm⟩)
    have hp_le : p ≤ X / k := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [mul_comm]
      exact hpk.le.trans htXle
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hk_le⟩, hkS⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨p, Nat.mem_primesLE.mpr ⟨hp_le, hpp⟩, by rw [mul_comm, hpk]⟩
  have hB_card1 : (B.card : ℝ) ≤ ∑ k ∈ K, (Nat.primeCounting (X / k) : ℝ) := by
    have hnat : B.card ≤ ∑ k ∈ K, Nat.primeCounting (X / k) := by
      calc
        B.card ≤ (K.biUnion (fun k => (Nat.primesLE (X / k)).image (· * k))).card :=
          Finset.card_le_card hB_sub
        _ ≤ ∑ k ∈ K, ((Nat.primesLE (X / k)).image (· * k)).card := Finset.card_biUnion_le
        _ ≤ ∑ k ∈ K, (Nat.primesLE (X / k)).card :=
          Finset.sum_le_sum fun k _ => Finset.card_image_le
        _ = ∑ k ∈ K, Nat.primeCounting (X / k) := by simp
    exact_mod_cast hnat
  have hz_log : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hB_term : ∀ k ∈ K, (Nat.primeCounting (X / k) : ℝ) ≤
      6 * (X : ℝ) / Real.log z * (k : ℝ)⁻¹ := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    have hk1 : 1 ≤ k := hk_mem.1
    have hzk : z + 1 ≤ X / k := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).mp hk_mem.2
      nlinarith
    have hy_gt : 1 < ((X / k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < X / k)
    have hpi := Chebyshev.pi_le_log4_mul_div hy_gt
    rw [Nat.floor_natCast] at hpi
    have hlog_y : 0 < Real.log ((X / k : ℕ) : ℝ) := Real.log_pos hy_gt
    have hlog_sq : Real.log (Real.sqrt ((X / k : ℕ) : ℝ)) = (1 / 2 : ℝ) * Real.log ((X / k : ℕ) : ℝ) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have hlog4 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      have h2e : Real.log 2 < 1 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        exact lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
      push_cast
      linarith
    have hsqrt_y : Real.sqrt ((X / k : ℕ) : ℝ) ≤ 2 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := by
      have hlog_rpow := Real.log_le_rpow_div (by positivity : 0 ≤ ((X / k : ℕ) : ℝ))
        (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at hlog_rpow
      have hsq_pos : 0 < Real.sqrt ((X / k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      rw [le_div_iff₀ hlog_y]
      calc
        Real.sqrt ((X / k : ℕ) : ℝ) * Real.log ((X / k : ℕ) : ℝ)
            ≤ Real.sqrt ((X / k : ℕ) : ℝ) * (Real.sqrt ((X / k : ℕ) : ℝ) / (1 / 2 : ℝ)) := by gcongr
        _ = 2 * (Real.sqrt ((X / k : ℕ) : ℝ) * Real.sqrt ((X / k : ℕ) : ℝ)) := by ring
        _ = 2 * ((X / k : ℕ) : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]
    have hpi_y : (Nat.primeCounting (X / k) : ℝ) ≤ 6 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := by
      rw [hlog_sq] at hpi
      have h1 : Real.log 4 * ((X / k : ℕ) : ℝ) / ((1 / 2 : ℝ) * Real.log ((X / k : ℕ) : ℝ)) ≤
          4 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := by
        have : Real.log 4 * ((X / k : ℕ) : ℝ) / ((1 / 2 : ℝ) * Real.log ((X / k : ℕ) : ℝ)) =
            (2 * Real.log 4) * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := by ring
        rw [this]
        gcongr
        linarith
      have hsum6 : 4 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) +
          2 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) =
          6 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := by ring
      linarith
    have hy_le : ((X / k : ℕ) : ℝ) ≤ (X : ℝ) * (k : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by exact_mod_cast (by omega : 0 < k))]
      exact_mod_cast Nat.div_mul_le_self X k
    have hlog_z_le : Real.log (z : ℝ) ≤ Real.log ((X / k : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < z))
      exact_mod_cast (by omega : z ≤ X / k)
    calc
      (Nat.primeCounting (X / k) : ℝ) ≤ 6 * ((X / k : ℕ) : ℝ) / Real.log ((X / k : ℕ) : ℝ) := hpi_y
      _ ≤ 6 * ((X : ℝ) * (k : ℝ)⁻¹) / Real.log (z : ℝ) := by
        apply div_le_div₀ (by positivity) (by gcongr) hz_log hlog_z_le
      _ = 6 * (X : ℝ) / Real.log z * (k : ℝ)⁻¹ := by ring
  let Q := n.primeFactors ∪ (Nat.primesLE n).filter (fun q => z < q)
  have hK_sub : K ⊆ (Finset.Icc 1 (X / (z + 1))).filter (fun k => k.primeFactors ⊆ Q) := by
    intro k hk
    obtain ⟨hkI, hkS⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkI, fun q hq => ?_⟩
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqk : q ≤ k := Nat.le_of_mem_primeFactors hq
    have hkn : k ≤ n := (Finset.mem_Icc.mp hkI).2.trans ((Nat.div_le_self X _).trans (Nat.div_le_self n d))
    have hqn : q ≤ n := hqk.trans hkn
    by_cases hqz : q ≤ z
    · by_cases hqdvd : q ∣ n
      · exact Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, by omega⟩)
      · exact False.elim (hkS q (Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqz, hqp⟩, hqdvd⟩)
          (Nat.dvd_of_mem_primeFactors hq))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqn, hqp⟩, by omega⟩)
  have hQ_prime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp hq with h1 | h2
    · exact Nat.prime_of_mem_primeFactors h1
    · exact Nat.prime_of_mem_primesLE (Finset.mem_filter.mp h2).1
  have hsumK : ∑ k ∈ K, (k : ℝ)⁻¹ ≤
      (∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹)⁻¹) *
      ∏ q ∈ (Nat.primesLE n).filter (fun q => z < q), (1 - (q : ℝ)⁻¹)⁻¹ := by
    have h1 : ∑ k ∈ K, (k : ℝ)⁻¹ ≤ ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)⁻¹ := by
      calc
        ∑ k ∈ K, (k : ℝ)⁻¹ ≤ ∑ k ∈ (Finset.Icc 1 (X / (z + 1))).filter (fun k => k.primeFactors ⊆ Q), (k : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hK_sub fun _ _ _ => by positivity
        _ ≤ ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)⁻¹ := by
          apply sum_mult_smooth_le (fun k => (k : ℝ)⁻¹) (fun _ => by positivity) (by simp)
            (fun a b => by push_cast; ring) Q hQ_prime
            (fun q hq => by
              have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ_prime q hq).two_le
              exact inv_lt_one_of_one_lt₀ (by linarith)) (X / (z + 1))
    have hprod_le : ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)⁻¹ ≤
        (∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹)⁻¹) *
        ∏ q ∈ (Nat.primesLE n).filter (fun q => z < q), (1 - (q : ℝ)⁻¹)⁻¹ := by
      have hsub1 : n.primeFactors ⊆ Q := Finset.subset_union_left
      have hsub2 : Q \ n.primeFactors ⊆ (Nat.primesLE n).filter (fun q => z < q) := by
        intro q hq
        rw [Finset.mem_sdiff] at hq
        exact (Finset.mem_union.mp hq.1).resolve_left hq.2
      rw [← Finset.prod_sdiff hsub1, mul_comm]
      apply mul_le_mul_of_nonneg_left
      · rw [← Finset.prod_sdiff hsub2]
        apply le_mul_of_one_le_left
        · apply Finset.prod_nonneg
          intro q hq
          rw [Finset.mem_sdiff] at hq
          have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ_prime q hq.1).two_le
          have : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hq2
          exact inv_nonneg.mpr (by linarith)
        · calc
            (1 : ℝ) = ∏ _q ∈ ((Nat.primesLE n).filter (fun q => z < q)) \ (Q \ n.primeFactors), (1 : ℝ) := by simp
            _ ≤ ∏ q ∈ ((Nat.primesLE n).filter (fun q => z < q)) \ (Q \ n.primeFactors), (1 - (q : ℝ)⁻¹)⁻¹ := by
              apply Finset.prod_le_prod
              · intro _ _; norm_num
              · intro q hq
                rw [Finset.mem_sdiff] at hq
                have hq2 : (2 : ℝ) ≤ q := by
                  exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq.1).1).two_le
                have : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hq2
                have hq_inv_pos : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr (by linarith)
                rw [← one_div, one_le_div (by linarith)]
                linarith
      · apply Finset.prod_nonneg
        intro q hq
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ_prime q (hsub1 hq)).two_le
        have : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hq2
        exact inv_nonneg.mpr (by linarith)
    exact h1.trans hprod_le
  have htot_eq : ∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹)⁻¹ = (n : ℝ) / n.totient := by
    have hQ := Nat.totient_eq_mul_prod_factors n
    have hR : (n.totient : ℝ) = (n : ℝ) * ∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹) := by
      have := congrArg (Rat.cast : ℚ → ℝ) hQ
      simpa using this
    have hntot : (n.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
    have hprod_pos : ∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹) ≠ 0 := by
      intro hz0
      rw [hz0, mul_zero] at hR
      exact hntot hR
    rw [Finset.prod_inv_distrib, ← one_div, div_eq_iff hprod_pos]
    rw [hR]
    field_simp [hntot, hprod_pos]
  have hB_card : (B.card : ℝ) ≤ 6 * Real.exp 180 * (X : ℝ) / Real.log z * ((n : ℝ) / n.totient) := by
    calc
      (B.card : ℝ) ≤ ∑ k ∈ K, 6 * (X : ℝ) / Real.log z * (k : ℝ)⁻¹ :=
        hB_card1.trans (Finset.sum_le_sum hB_term)
      _ = (6 * (X : ℝ) / Real.log z) * ∑ k ∈ K, (k : ℝ)⁻¹ := (Finset.mul_sum ..).symm
      _ ≤ (6 * (X : ℝ) / Real.log z) * ((n : ℝ) / n.totient * Real.exp 180) := by
        gcongr
        · exact hsumK.trans (by
            rw [htot_eq]
            exact mul_le_mul_of_nonneg_left (prod_one_sub_inv_gt_le hz hzn hnz) (by positivity))
      _ = 6 * Real.exp 180 * (X : ℝ) / Real.log z * ((n : ℝ) / n.totient) := by ring
  rw [hsplit, Nat.cast_add]
  exact add_le_add hA_card hB_card

private lemma get_prime_between (n X : ℕ) (hn1 : 1 ≤ n) (hlog_ge : 1000 ≤ Real.log (n : ℝ))
    (hloglog_rp : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 20)
    (hprime_all : ∀ Y : ℕ, ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ ≤ Y →
      3 * (Y : ℝ) / Real.log Y ≤ (Nat.primeCounting (16 * Y) : ℝ) - (Nat.primeCounting Y : ℝ))
    (hX_lo : (Real.log (n : ℝ)) ^ 2 / 2 ≤ (X : ℝ)) (hX_hi : (X : ℝ) ≤ (Real.log (n : ℝ)) ^ 5) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p ≤ 16 * X ∧ ¬ p ∣ n := by
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hX_floor : ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ ≤ X := Nat.floor_le_of_le hX_lo
  have hdiff := hprime_all X hX_floor
  have hX_ge_two : (2 : ℝ) ≤ (X : ℝ) := by
    have : (4 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
    linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogX_le : Real.log (X : ℝ) ≤ 5 * Real.log (Real.log (n : ℝ)) := by
    calc
      Real.log (X : ℝ) ≤ Real.log ((Real.log (n : ℝ)) ^ 5) := Real.log_le_log hXpos hX_hi
      _ = 5 * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; norm_num
  have hnf_le : (n.primeFactors.card : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcard : (n.primeFactors.card : ℝ) ≤ Nat.log 2 n := by exact_mod_cast card_primeFactors_le_log2 hn1
    have h2pow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog_nat : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      calc
        (Nat.log 2 n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (Nat.log 2 n)) := (Real.log_pow 2 _).symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) h2pow
    have hhalf : (Nat.log 2 n : ℝ) * (1 / 2) ≤ Real.log (n : ℝ) := by
      calc
        (Nat.log 2 n : ℝ) * (1 / 2) ≤ (Nat.log 2 n : ℝ) * Real.log 2 := by
          gcongr
          linarith [Real.log_two_gt_d9]
        _ ≤ Real.log (n : ℝ) := hlog_nat
    linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos (by linarith)
  have hcard_lt : (n.primeFactors.card : ℝ) < 3 * (X : ℝ) / Real.log (X : ℝ) := by
    have h3 : 10 * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) <
        3 * ((Real.log (n : ℝ)) ^ 2 / 2) := by
      have h10 : 10 * Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 2 := by linarith
      have hmul : 10 * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ 2 / 2 := by
        calc
          10 * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))
              = Real.log (n : ℝ) * (10 * Real.log (Real.log (n : ℝ))) := by ring
          _ ≤ Real.log (n : ℝ) * (Real.log (n : ℝ) / 2) := by gcongr
          _ = (Real.log (n : ℝ)) ^ 2 / 2 := by ring
      have hpos_sq : 0 < (Real.log (n : ℝ)) ^ 2 := by positivity
      linarith
    have h1 : 2 * Real.log (n : ℝ) < 3 * ((Real.log (n : ℝ)) ^ 2 / 2) / (5 * Real.log (Real.log (n : ℝ))) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h2 : 3 * ((Real.log (n : ℝ)) ^ 2 / 2) / (5 * Real.log (Real.log (n : ℝ))) ≤ 3 * (X : ℝ) / Real.log (X : ℝ) :=
      div_le_div₀ (by positivity) (by linarith) hlogX_pos hlogX_le
    linarith
  exact exists_prime_interval_not_dvd hn1 (hcard_lt.trans_le hdiff)

private lemma choose_d_params (n z w D₀ : ℕ) (d₀ : ℝ)
    (hn1 : 1 ≤ n) (hlog_ge : 1000 ≤ Real.log (n : ℝ))
    (hloglog_rp : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 20)
    (hprime_all : ∀ Y : ℕ, ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ ≤ Y →
      3 * (Y : ℝ) / Real.log Y ≤ (Nat.primeCounting (16 * Y) : ℝ) - (Nat.primeCounting Y : ℝ))
    (hwz : w ≤ z)
    (hD0_eq : D₀ = ∏ p ∈ (Nat.primesLE w).filter (fun p => ¬ p ∣ n), p)
    (hD0_pos : 1 ≤ D₀) (hD0_cop : Nat.Coprime D₀ n)
    (hD0_le_d0 : (D₀ : ℝ) ≤ d₀ / (Real.log (n : ℝ)) ^ 2) (hd0_pos : 0 < d₀)
    (hz_ge_512 : 512 * (Real.log (n : ℝ)) ^ 4 ≤ (z : ℝ)) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.Coprime d n ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ∈ (Nat.primesLE z).filter (fun t => ¬ t ∣ n)) ∧
      D₀ ∣ d ∧ d₀ < (d : ℝ) ∧ (d : ℝ) ≤ 16 * d₀ := by
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog_sq_ge : (1000000 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    have h := mul_le_mul hlog_ge hlog_ge (by positivity) (by positivity)
    linarith [show Real.log (n : ℝ) * Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ 2 by ring]
  let X₀ := ⌊(Real.log (n : ℝ)) ^ 2⌋₊ + 2
  have hX0_lo : (Real.log (n : ℝ)) ^ 2 / 2 ≤ (X₀ : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 2)
    push_cast [X₀]
    linarith
  have hX0_hi : (X₀ : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
    have hfl : (⌊(Real.log (n : ℝ)) ^ 2⌋₊ : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := Nat.floor_le (by positivity)
    have hX0_2 : (X₀ : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := by
      push_cast [X₀]
      linarith
    have hlog3 : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      have h1 : (2 : ℝ) ≤ Real.log (n : ℝ) := by linarith
      have h2 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by linarith
      calc
        (2 : ℝ) = 2 * 1 := by ring
        _ ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    calc
      (X₀ : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hX0_2
      _ ≤ (Real.log (n : ℝ)) ^ 3 * (Real.log (n : ℝ)) ^ 2 := by gcongr
      _ = (Real.log (n : ℝ)) ^ 5 := by ring
  obtain ⟨q, hq_prime, hq_gt, hq_le, hq_ndvd⟩ :=
    get_prime_between n X₀ hn1 hlog_ge hloglog_rp hprime_all hX0_lo hX0_hi
  have hq_le_real : (q : ℝ) ≤ 32 * (Real.log (n : ℝ)) ^ 2 := by
    have h1 : (q : ℝ) ≤ 16 * (X₀ : ℝ) := by exact_mod_cast hq_le
    have hfl : (⌊(Real.log (n : ℝ)) ^ 2⌋₊ : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := Nat.floor_le (by positivity)
    have h2 : (X₀ : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := by
      push_cast [X₀]
      linarith
    linarith
  let M := ⌊d₀ / ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2)⌋₊
  have hM1 : 1 ≤ M := by
    apply Nat.le_floor
    rw [Nat.cast_one, one_le_div (by positivity)]
    exact (le_div_iff₀ (by positivity)).mp hD0_le_d0
  let k := Nat.log q M
  let d₁ := D₀ * q ^ k
  have hd1_pos : 1 ≤ d₁ := Nat.mul_pos hD0_pos (Nat.pow_pos hq_prime.pos)
  have hd1_le : (d₁ : ℝ) ≤ d₀ / (Real.log (n : ℝ)) ^ 2 := by
    have hqk : (q : ℝ) ^ k ≤ (M : ℝ) := by exact_mod_cast Nat.pow_log_le_self q (by omega)
    have hM_le : (M : ℝ) ≤ d₀ / ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2) := Nat.floor_le (by positivity)
    have hD0r : (D₀ : ℝ) ≠ 0 := by exact_mod_cast (by omega : D₀ ≠ 0)
    calc
      (d₁ : ℝ) = (D₀ : ℝ) * (q : ℝ) ^ k := by push_cast [d₁]; rfl
      _ ≤ (D₀ : ℝ) * (d₀ / ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hqk.trans hM_le) (by positivity)
      _ = d₀ / (Real.log (n : ℝ)) ^ 2 := by field_simp [hD0r]
  have hd1_gt : d₀ / (Real.log (n : ℝ)) ^ 2 < (d₁ : ℝ) * (q : ℝ) := by
    have hlt : M < q ^ (k + 1) := Nat.lt_pow_succ_log_self hq_prime.one_lt M
    have hM_lt : d₀ / ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2) < ((M + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    have hq_succ : ((M + 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ (k + 1) := by exact_mod_cast hlt
    have h1 : d₀ / ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2) < (q : ℝ) ^ (k + 1) := hM_lt.trans_le hq_succ
    have h2 : d₀ / (Real.log (n : ℝ)) ^ 2 < (D₀ : ℝ) * (q : ℝ) ^ (k + 1) := by
      rw [div_lt_iff₀ (by positivity)]
      have h1' : d₀ < (q : ℝ) ^ (k + 1) * ((D₀ : ℝ) * (Real.log (n : ℝ)) ^ 2) :=
        (div_lt_iff₀ (by positivity)).mp h1
      linarith
    calc
      d₀ / (Real.log (n : ℝ)) ^ 2 < (D₀ : ℝ) * (q : ℝ) ^ (k + 1) := h2
      _ = (d₁ : ℝ) * (q : ℝ) := by
        push_cast [d₁]
        rw [pow_succ]
        ring
  let X₁ := ⌊d₀ / (d₁ : ℝ)⌋₊
  have hX1_lo : (Real.log (n : ℝ)) ^ 2 / 2 ≤ (X₁ : ℝ) := by
    have hdiv : (Real.log (n : ℝ)) ^ 2 ≤ d₀ / (d₁ : ℝ) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact (le_div_iff₀ (by positivity)).mp hd1_le
    have hlt := Nat.lt_floor_add_one (d₀ / (d₁ : ℝ))
    linarith
  have hX1_hi : (X₁ : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
    have hfl : (X₁ : ℝ) ≤ d₀ / (d₁ : ℝ) := Nat.floor_le (by positivity)
    have hd0_d1 : d₀ / (d₁ : ℝ) < (q : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have h := (div_lt_iff₀ (by positivity)).mp hd1_gt
      linarith
    have h32 : (q : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ 32 * (Real.log (n : ℝ)) ^ 4 := by
      calc
        (q : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (32 * (Real.log (n : ℝ)) ^ 2) * (Real.log (n : ℝ)) ^ 2 := by gcongr
        _ = 32 * (Real.log (n : ℝ)) ^ 4 := by ring
    have hpow5 : 32 * (Real.log (n : ℝ)) ^ 4 ≤ (Real.log (n : ℝ)) ^ 5 := by
      calc
        32 * (Real.log (n : ℝ)) ^ 4 ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by gcongr; linarith
        _ = (Real.log (n : ℝ)) ^ 5 := by ring
    linarith
  obtain ⟨p, hp_prime, hp_gt, hp_le, hp_ndvd⟩ :=
    get_prime_between n X₁ hn1 hlog_ge hloglog_rp hprime_all hX1_lo hX1_hi
  have hp_le_real : (p : ℝ) ≤ 512 * (Real.log (n : ℝ)) ^ 4 := by
    have h1 : (p : ℝ) ≤ 16 * (X₁ : ℝ) := by exact_mod_cast hp_le
    have hfl : (X₁ : ℝ) ≤ d₀ / (d₁ : ℝ) := Nat.floor_le (by positivity)
    have hd0_d1 : d₀ / (d₁ : ℝ) < (q : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have h := (div_lt_iff₀ (by positivity)).mp hd1_gt
      linarith
    have h32 : (q : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ 32 * (Real.log (n : ℝ)) ^ 4 := by
      calc
        (q : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (32 * (Real.log (n : ℝ)) ^ 2) * (Real.log (n : ℝ)) ^ 2 := by gcongr
        _ = 32 * (Real.log (n : ℝ)) ^ 4 := by ring
    linarith
  have hq_le_z : q ≤ z := by
    have h2 : 32 * (Real.log (n : ℝ)) ^ 2 ≤ 512 * (Real.log (n : ℝ)) ^ 4 := by
      calc
        32 * (Real.log (n : ℝ)) ^ 2 = 32 * (Real.log (n : ℝ)) ^ 2 * 1 := by ring
        _ ≤ 512 * (Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 2 := by
          gcongr
          · norm_num
          · exact le_trans (by norm_num) hlog_sq_ge
        _ = 512 * (Real.log (n : ℝ)) ^ 4 := by ring
    exact_mod_cast hq_le_real.trans (h2.trans hz_ge_512)
  have hp_le_z : p ≤ z := by exact_mod_cast hp_le_real.trans hz_ge_512
  refine ⟨d₁ * p, Nat.mul_pos hd1_pos hp_prime.pos, ?_, ?_, ⟨q ^ k * p, by dsimp [d₁]; ring⟩, ?_, ?_⟩
  · have hqk_cop : Nat.Coprime (q ^ k) n :=
      Nat.Coprime.pow_left k (hq_prime.coprime_iff_not_dvd.mpr hq_ndvd)
    have hp_cop : Nat.Coprime p n := hp_prime.coprime_iff_not_dvd.mpr hp_ndvd
    exact (hD0_cop.mul_left hqk_cop).mul_left hp_cop
  · intro r hr_prime hr_dvd
    rcases hr_prime.dvd_mul.mp hr_dvd with hr_d1 | hr_p
    · rcases hr_prime.dvd_mul.mp hr_d1 with hr_D0 | hr_qk
      · rw [hD0_eq, hr_prime.prime.dvd_finsetProd_iff] at hr_D0
        obtain ⟨t, ht_mem, hr_dvd_t⟩ := hr_D0
        have ht_mem' := Finset.mem_filter.mp ht_mem
        have ht_prime := Nat.prime_of_mem_primesLE ht_mem'.1
        have hrt : r = t := (Nat.prime_dvd_prime_iff_eq hr_prime ht_prime).mp hr_dvd_t
        subst hrt
        exact Finset.mem_filter.mpr ⟨Nat.primesLE_mono hwz ht_mem'.1, ht_mem'.2⟩
      · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow hr_qk)
        subst hrq
        exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hq_le_z, hq_prime⟩, hq_ndvd⟩
    · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp hr_p
      subst hrp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp_le_z, hp_prime⟩, hp_ndvd⟩
  · have hX1_lt : d₀ / (d₁ : ℝ) < (p : ℝ) := by
      have hfl := Nat.lt_floor_add_one (d₀ / (d₁ : ℝ))
      have hp_ge : ((X₁ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_gt
      push_cast [X₁] at hp_ge ⊢
      linarith
    push_cast
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < d₁)).mp hX1_lt |>.trans_eq (mul_comm _ _)
  · have hp16 : (p : ℝ) ≤ 16 * (X₁ : ℝ) := by exact_mod_cast hp_le
    have hfl : (X₁ : ℝ) ≤ d₀ / (d₁ : ℝ) := Nat.floor_le (by positivity)
    have h1 : (p : ℝ) ≤ 16 * (d₀ / (d₁ : ℝ)) := hp16.trans (by linarith)
    push_cast
    have hd1r : (d₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : d₁ ≠ 0)
    calc
      (d₁ : ℝ) * (p : ℝ) ≤ (d₁ : ℝ) * (16 * (d₀ / (d₁ : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * d₀ := by field_simp [hd1r]

private lemma bound_d_totient (n d D₀ w : ℕ) (d₀ ψ : ℝ)
    (hn1 : 1 ≤ n) (hd_pos : 1 ≤ d) (hw1 : 1 ≤ w)
    (hlog_pos : 0 < Real.log (n : ℝ)) (hloglog_pos : 0 < Real.log (Real.log (n : ℝ)))
    (hlog_w1 : Real.log (Real.log (n : ℝ)) / 2 ≤ Real.log (w + 1 : ℝ))
    (hD0_eq : D₀ = ∏ p ∈ (Nat.primesLE w).filter (fun p => ¬ p ∣ n), p)
    (hD0_dvd_d : D₀ ∣ d) (hd_le : (d : ℝ) ≤ 16 * d₀)
    (hd0_eq : d₀ = (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) /
      (Real.log (n : ℝ)) ^ (1 / 3 : ℝ))
    (hψ_eq : ψ = (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
      (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))) :
    2 * (d.totient : ℝ) ≤ 64 * ψ := by
  have hnr_pos : (0 : ℝ) < n := by positivity
  have hntot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1
  have hD0_pf : D₀.primeFactors = (Nat.primesLE w).filter (fun t => ¬ t ∣ n) := by
    ext r
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hr_prime, hr_dvd, _⟩
      rw [hD0_eq, hr_prime.prime.dvd_finsetProd_iff] at hr_dvd
      obtain ⟨t, ht_mem, hrt⟩ := hr_dvd
      have ht_prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp ht_mem).1
      rwa [(Nat.prime_dvd_prime_iff_eq hr_prime ht_prime).mp hrt]
    · intro hr_mem
      have hr_prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hr_mem).1
      refine ⟨hr_prime, ?_, ?_⟩
      · rw [hD0_eq]; exact Finset.dvd_prod_of_mem _ hr_mem
      · rw [hD0_eq]
        exact Finset.prod_ne_zero_iff.mpr fun t ht =>
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp ht).1).ne_zero
  have htot_d : (d.totient : ℝ) = (d : ℝ) * ∏ r ∈ d.primeFactors, (1 - (r : ℝ)⁻¹) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors d)
    simpa using this
  have hD0_sub : D₀.primeFactors ⊆ d.primeFactors := Nat.primeFactors_mono hD0_dvd_d (by omega)
  have hprod_d_le : ∏ r ∈ d.primeFactors, (1 - (r : ℝ)⁻¹) ≤
      ∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹) := by
    rw [← Finset.prod_sdiff hD0_sub]
    apply mul_le_of_le_one_left
    · apply Finset.prod_nonneg
      intro r hr
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).two_le
      have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
      linarith
    · apply Finset.prod_le_one
      · intro r hr
        have hr2 : (2 : ℝ) ≤ r := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hr).1).two_le
        have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
        linarith
      · intro r _
        have : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
        linarith
  let Wₙ := (Nat.primesLE w).filter (fun t => t ∣ n)
  have hdisj : Disjoint D₀.primeFactors Wₙ := by
    rw [hD0_pf]
    exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
  have hunion : D₀.primeFactors ∪ Wₙ = Nat.primesLE w := by
    rw [hD0_pf]
    ext t
    simp only [Wₙ, Finset.mem_union, Finset.mem_filter]
    tauto
  have hprod_w_split :
      (∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹)) * (∏ r ∈ Wₙ, (1 - (r : ℝ)⁻¹)) =
        ∏ r ∈ Nat.primesLE w, (1 - (r : ℝ)⁻¹) := by
    rw [← Finset.prod_union hdisj, hunion]
  have hWn_sub : Wₙ ⊆ n.primeFactors := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hr'.1, hr'.2, by omega⟩
  have htot_n : (n.totient : ℝ) / (n : ℝ) = ∏ r ∈ n.primeFactors, (1 - (r : ℝ)⁻¹) := by
    have hQ := Nat.totient_eq_mul_prod_factors n
    have hR : (n.totient : ℝ) = (n : ℝ) * ∏ r ∈ n.primeFactors, (1 - (r : ℝ)⁻¹) := by
      have := congrArg (Rat.cast : ℚ → ℝ) hQ
      simpa using this
    rw [hR, mul_div_cancel_left₀ _ hnr_pos.ne']
  have hWn_ge : (n.totient : ℝ) / (n : ℝ) ≤ ∏ r ∈ Wₙ, (1 - (r : ℝ)⁻¹) := by
    rw [htot_n, ← Finset.prod_sdiff hWn_sub]
    apply mul_le_of_le_one_left
    · apply Finset.prod_nonneg
      intro r hr
      have hr2 : (2 : ℝ) ≤ r := by
        exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hr).1).two_le
      have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
      linarith
    · apply Finset.prod_le_one
      · intro r hr
        have hr2 : (2 : ℝ) ≤ r := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hr).1).two_le
        have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
        linarith
      · intro r _
        have : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
        linarith
  have hD0_nonneg : 0 ≤ ∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro r hr
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).two_le
    have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
    linarith
  have hprod_w_le : ∏ r ∈ Nat.primesLE w, (1 - (r : ℝ)⁻¹) ≤ 2 / Real.log (Real.log (n : ℝ)) := by
    have h1 := prod_one_sub_inv_primesLE_le w hw1
    have h2 : (Real.log (w + 1 : ℝ))⁻¹ ≤ (Real.log (Real.log (n : ℝ)) / 2)⁻¹ :=
      inv_anti₀ (by positivity) hlog_w1
    calc
      ∏ r ∈ Nat.primesLE w, (1 - (r : ℝ)⁻¹) ≤ (Real.log (w + 1 : ℝ))⁻¹ := h1
      _ ≤ (Real.log (Real.log (n : ℝ)) / 2)⁻¹ := h2
      _ = 2 / Real.log (Real.log (n : ℝ)) := by ring
  have hD0_prod_le : ∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹) ≤
      ((n : ℝ) / n.totient) * (2 / Real.log (Real.log (n : ℝ))) := by
    have h1 : (∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹)) * ((n.totient : ℝ) / (n : ℝ)) ≤
        2 / Real.log (Real.log (n : ℝ)) := by
      calc
        (∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹)) * ((n.totient : ℝ) / (n : ℝ))
            ≤ (∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹)) * (∏ r ∈ Wₙ, (1 - (r : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hWn_ge hD0_nonneg
        _ = ∏ r ∈ Nat.primesLE w, (1 - (r : ℝ)⁻¹) := hprod_w_split
        _ ≤ 2 / Real.log (Real.log (n : ℝ)) := hprod_w_le
    have hdiv_pos : 0 < (n.totient : ℝ) / (n : ℝ) := by positivity
    have h2 := (le_div_iff₀ hdiv_pos).mpr h1
    calc
      ∏ r ∈ D₀.primeFactors, (1 - (r : ℝ)⁻¹) ≤ (2 / Real.log (Real.log (n : ℝ))) / ((n.totient : ℝ) / (n : ℝ)) := h2
      _ = ((n : ℝ) / n.totient) * (2 / Real.log (Real.log (n : ℝ))) := by
        field_simp [hnr_pos.ne', hntot_pos.ne']
  have hψ_eq_d0 : d₀ * (2 / Real.log (Real.log (n : ℝ))) * ((n : ℝ) / n.totient) = 2 * ψ := by
    have hloglog_rpow : Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) *
        Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) = Real.log (Real.log (n : ℝ)) := by
      rw [← Real.rpow_add hloglog_pos]
      norm_num
    rw [hd0_eq, hψ_eq]
    field_simp [hlog_pos.ne', hloglog_pos.ne', hntot_pos.ne']
    exact hloglog_rpow
  have hprod_d_nonneg : 0 ≤ ∏ r ∈ d.primeFactors, (1 - (r : ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro r hr
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).two_le
    have : (r : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hr2
    linarith
  have hd0_nonneg : 0 ≤ d₀ := by
    rw [hd0_eq]
    positivity
  calc
    2 * (d.totient : ℝ) = 2 * ((d : ℝ) * ∏ r ∈ d.primeFactors, (1 - (r : ℝ)⁻¹)) := by rw [htot_d]
    _ ≤ 2 * ((16 * d₀) * (((n : ℝ) / n.totient) * (2 / Real.log (Real.log (n : ℝ))))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hd_le (hprod_d_le.trans hD0_prod_le) hprod_d_nonneg (by linarith))
        (by norm_num)
    _ = 32 * (d₀ * (2 / Real.log (Real.log (n : ℝ))) * ((n : ℝ) / n.totient)) := by ring
    _ = 64 * ψ := by rw [hψ_eq_d0]; ring

private lemma bound_R_div_d (n d z : ℕ) (d₀ ψ : ℝ)
    (hn1 : 1 ≤ n) (hd_pos : 1 ≤ d) (hz_128 : 128 ≤ z) (hzn : z ≤ n) (hnz : n < (2 * z) ^ 5)
    (hlog_ge : 1000 ≤ Real.log (n : ℝ)) (hloglog_ge : 100 ≤ Real.log (Real.log (n : ℝ)))
    (hlog_z : Real.log (n : ℝ) / 6 ≤ Real.log (z : ℝ))
    (hlog_rp30 : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 30 : ℝ))
    (hconst_rp : (4 : ℝ) ^ 65 ≤ (n : ℝ) ^ (1 / 30 : ℝ))
    (hd_gt : d₀ < (d : ℝ)) (hd0_pos : 0 < d₀)
    (hd0_eq : d₀ = (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) /
      (Real.log (n : ℝ)) ^ (1 / 3 : ℝ))
    (hψ_eq : ψ = (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
      (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ)))
    (hψ_ge_div : (n : ℝ) ^ (1 / 3 : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤ ψ) :
    let S := (Nat.primesLE z).filter (fun p => ¬ p ∣ n)
    ((( (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) ).card / d : ℕ) : ℝ) ≤
      (1 + 36 * Real.exp 180) * ψ := by
  intro S
  have hnr_pos : (0 : ℝ) < n := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have hdr_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hntot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1
  have hR_bound := R_prime_card_bound hn1 hd_pos hz_128 hzn hnz
  have hnat_div : ((( (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) ).card / d : ℕ) : ℝ) ≤
      (( (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) ).card : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdr_pos]
    exact_mod_cast Nat.div_mul_le_self _ d
  have hnd_real : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdr_pos]
    exact_mod_cast Nat.div_mul_le_self n d
  have hd0_cube : d₀ ^ 3 = (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    rw [hd0_eq, div_pow, mul_pow]
    have h1 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
    have h2 : (Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ)) ^ 3 = Real.log (Real.log (n : ℝ)) := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
    have h3 : (Real.log (n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h1, h2, h3]
  have htermA_sq : (Real.sqrt ((n / d : ℕ) : ℝ) / (d : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    calc
      ((n / d : ℕ) : ℝ) / (d : ℝ) ^ 2 ≤ ((n : ℝ) / (d : ℝ)) / (d : ℝ) ^ 2 := by gcongr
      _ = (n : ℝ) / (d : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) / d₀ ^ 3 := by gcongr
      _ = Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
        rw [hd0_cube]
        field_simp [hnr_pos.ne', hlog_pos.ne', hloglog_pos.ne']
      _ ≤ Real.log (n : ℝ) := div_le_self hlog_pos.le (by linarith)
      _ = Real.log (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by gcongr; linarith
      _ = (Real.log (n : ℝ)) ^ 2 := by ring
  have htermA_sqrt : Real.sqrt ((n / d : ℕ) : ℝ) / (d : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.sqrt_sq (show 0 ≤ Real.sqrt ((n / d : ℕ) : ℝ) / (d : ℝ) by positivity), ← Real.sqrt_sq hlog_pos.le]
    exact Real.sqrt_le_sqrt htermA_sq
  have htermA : Real.sqrt ((n / d : ℕ) : ℝ) * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) / (d : ℝ) ≤ ψ := by
    have hlog2_rp : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (1 / 15 : ℝ) := by
      calc
        (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ (1 / 30 : ℝ)) ^ 2 := by gcongr
        _ = (n : ℝ) ^ (1 / 15 : ℝ) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
    have hmul_rp : 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
        (n : ℝ) ^ (1 / 3 : ℝ) := by
      calc
        4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 2
            ≤ (n : ℝ) ^ (1 / 30 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 30 : ℝ) *
                (n : ℝ) ^ (1 / 15 : ℝ) := by gcongr
        _ = (n : ℝ) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_add hnr_pos, ← Real.rpow_add hnr_pos, ← Real.rpow_add hnr_pos]
          norm_num
    have h1 : Real.sqrt ((n / d : ℕ) : ℝ) * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) / (d : ℝ) =
        (Real.sqrt ((n / d : ℕ) : ℝ) / (d : ℝ)) * (4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ)) := by ring
    rw [h1]
    calc
      (Real.sqrt ((n / d : ℕ) : ℝ) / (d : ℝ)) * (4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ))
          ≤ Real.log (n : ℝ) * (4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ)) := by gcongr
      _ = 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) / (Real.log (n : ℝ)) ^ 2 :=
        (le_div_iff₀ (by positivity)).mpr hmul_rp
      _ ≤ ψ := hψ_ge_div
  have htermB : (6 * Real.exp 180) * ((n / d : ℕ) : ℝ) / Real.log (z : ℝ) *
      ((n : ℝ) / n.totient) / (d : ℝ) ≤ (36 * Real.exp 180) * ψ := by
    have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
    have hd0_sq : d₀ ^ 2 * Real.log (n : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) *
        Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) * Real.log (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hn23 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
      have hll23 : (Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ)) ^ 2 =
          Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
      have hl23 : (Real.log (n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * Real.log (n : ℝ) ^ (1 / 3 : ℝ) =
          Real.log (n : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_add hlog_pos]
        norm_num
      have hl_pos : 0 < Real.log (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
      have hdiv : Real.log (n : ℝ) / (Real.log (n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = Real.log (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [div_eq_iff (pow_ne_zero 2 hl_pos.ne'), mul_comm]
        exact hl23.symm
      rw [hd0_eq, div_pow, mul_pow, hn23, hll23, div_mul_eq_mul_div, mul_div_assoc, hdiv]
    have h_n_div : (n : ℝ) / (d₀ ^ 2 * Real.log (n : ℝ)) * ((n : ℝ) / n.totient) = ψ := by
      have hn13 : (n : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hnr_pos]; norm_num
      rw [hd0_sq, hψ_eq]
      nth_rw 1 [hn13]
      have h23_pos : (0 : ℝ) < (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
      field_simp [h23_pos.ne', hlog_pos.ne', hloglog_pos.ne', hntot_pos.ne']
    calc
      (6 * Real.exp 180) * ((n / d : ℕ) : ℝ) / Real.log (z : ℝ) * ((n : ℝ) / n.totient) / (d : ℝ)
          ≤ (6 * Real.exp 180) * ((n : ℝ) / (d : ℝ)) / (Real.log (n : ℝ) / 6) *
              ((n : ℝ) / n.totient) / (d : ℝ) := by gcongr
      _ = (36 * Real.exp 180) * ((n : ℝ) / ((d : ℝ) ^ 2 * Real.log (n : ℝ)) * ((n : ℝ) / n.totient)) := by
            ring
      _ ≤ (36 * Real.exp 180) * ((n : ℝ) / (d₀ ^ 2 * Real.log (n : ℝ)) * ((n : ℝ) / n.totient)) := by
            gcongr
      _ = (36 * Real.exp 180) * ψ := by rw [h_n_div]
  calc
    ((( (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) ).card / d : ℕ) : ℝ)
        ≤ (( (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) ).card : ℝ) / (d : ℝ) := hnat_div
    _ ≤ (Real.sqrt ((n / d : ℕ) : ℝ) * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) +
          (6 * Real.exp 180) * ((n / d : ℕ) : ℝ) / Real.log (z : ℝ) * ((n : ℝ) / n.totient)) / (d : ℝ) := by
        gcongr
    _ = Real.sqrt ((n / d : ℕ) : ℝ) * 4 ^ 65 * (n : ℝ) ^ (1 / 5 : ℝ) / (d : ℝ) +
          (6 * Real.exp 180) * ((n / d : ℕ) : ℝ) / Real.log (z : ℝ) * ((n : ℝ) / n.totient) / (d : ℝ) := by
        ring
    _ ≤ ψ + (36 * Real.exp 180) * ψ := add_le_add htermA htermB
    _ = (1 + 36 * Real.exp 180) * ψ := by ring

private lemma erdos360_h2_pointwise (n : ℕ) (hn1 : 1 ≤ n)
    (hlog_ge : 1000 ≤ Real.log (n : ℝ)) (hloglog_ge : 100 ≤ Real.log (Real.log (n : ℝ)))
    (hlog_rp15 : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 15 : ℝ))
    (hlog_rp30 : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 30 : ℝ))
    (hlog_rp45 : 1024 * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hconst_rp : (4 : ℝ) ^ 65 ≤ (n : ℝ) ^ (1 / 30 : ℝ))
    (hloglog_rp : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 20)
    (hprime_all : ∀ Y : ℕ, ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ ≤ Y →
      3 * (Y : ℝ) / Real.log Y ≤ (Nat.primeCounting (16 * Y) : ℝ) - (Nat.primeCounting Y : ℝ)) :
    ∃ r d : ℕ, ∃ S : Finset ℕ,
      1 ≤ d ∧ (∀ p ∈ S, p.Prime ∧ ¬ p ∣ n) ∧ Nat.Coprime d n ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ∈ S) ∧
      let R' := (Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)
      ((r / 2 + S.card + 2 * d.totient + (R'.card / d + 1) : ℕ) : ℝ) ≤
        (67 + 36 * Real.exp 180) * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
          (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ))) := by
  have hnr_pos : (0 : ℝ) < n := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  let z := ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  have hz_ge_256 : (256 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have h10000 : (10000 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
      have h := mul_le_mul hlog_ge hlog_ge (by positivity) (by positivity)
      linarith [show Real.log (n : ℝ) * Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ 2 by ring]
    have h1 : (256 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      have h := mul_le_mul hlog_ge h10000 (by positivity) (by positivity)
      linarith [show Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 2 = (Real.log (n : ℝ)) ^ 3 by ring]
    have h2 : (Real.log (n : ℝ)) ^ 3 ≤ ((n : ℝ) ^ (1 / 15 : ℝ)) ^ 3 := by gcongr
    have h3 : ((n : ℝ) ^ (1 / 15 : ℝ)) ^ 3 = (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
    linarith
  have hz_rpow : (n : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ z := by
    have hlt := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 5 : ℝ))
    linarith
  have hz_128 : 128 ≤ z := (Nat.le_floor hz_ge_256).trans' (by norm_num)
  have hzn : z ≤ n := by
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
      _ = n := Real.rpow_one _
  have hnz : n < (2 * z) ^ 5 := by
    have hlt : (n : ℝ) ^ (1 / 5 : ℝ) < ((2 * z : ℕ) : ℝ) := by
      push_cast
      have hz_real : (128 : ℝ) ≤ z := by exact_mod_cast hz_128
      linarith [Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 5 : ℝ))]
    have hpow : (n : ℝ) < ((2 * z : ℕ) : ℝ) ^ 5 := by
      calc
        (n : ℝ) = ((n : ℝ) ^ (1 / 5 : ℝ)) ^ 5 := by
          rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul (by positivity)]; norm_num
        _ < ((2 * z : ℕ) : ℝ) ^ 5 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    exact_mod_cast hpow
  have hlog_z : Real.log (n : ℝ) / 6 ≤ Real.log (z : ℝ) := by
    have h1 : Real.log ((n : ℝ) ^ (1 / 5 : ℝ) / 2) ≤ Real.log (z : ℝ) :=
      Real.log_le_log (by positivity) hz_rpow
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hnr_pos] at h1
    have h2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      exact lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
    linarith
  let w := ⌊Real.log (n : ℝ) / 10⌋₊
  have hw1 : 1 ≤ w := Nat.le_floor (by linarith)
  have hwz : w ≤ z := by
    have hw_le : (w : ℝ) ≤ Real.log (n : ℝ) / 10 := Nat.floor_le (by positivity)
    have hz_le : Real.log (n : ℝ) / 10 ≤ z := by
      calc
        Real.log (n : ℝ) / 10 ≤ (n : ℝ) ^ (1 / 15 : ℝ) / 10 := by gcongr
        _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) / 2 := by
          have : (n : ℝ) ^ (1 / 15 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
          linarith
        _ ≤ z := hz_rpow
    exact_mod_cast hw_le.trans hz_le
  have hlog_w1 : Real.log (Real.log (n : ℝ)) / 2 ≤ Real.log (w + 1 : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.log (n : ℝ) / 10)
    have hsqrt : Real.sqrt (Real.log (n : ℝ)) ≤ (w + 1 : ℝ) := by
      have : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 10 := by
        rw [Real.sqrt_le_left (by positivity)]
        have h100 : (100 : ℝ) * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
          have h := mul_le_mul hlog_ge (le_refl (Real.log (n : ℝ))) (by positivity) (by positivity)
          linarith [show Real.log (n : ℝ) * Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ 2 by ring]
        linarith
      linarith
    have h1 := Real.log_le_log (Real.sqrt_pos.mpr hlog_pos) hsqrt
    rw [Real.log_sqrt hlog_pos.le] at h1
    linarith
  let D₀ := ∏ p ∈ (Nat.primesLE w).filter (fun p => ¬ p ∣ n), p
  have hD0_pos : 1 ≤ D₀ := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).ne_zero
  have hD0_cop : Nat.Coprime D₀ n := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primesLE hmem.1).coprime_iff_not_dvd.mpr hmem.2
  have hD0_le_4pow : (D₀ : ℝ) ≤ (4 : ℝ) ^ w := by
    have hnat : D₀ ≤ primorial w := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_le
    exact_mod_cast (hnat.trans (primorial_le_four_pow w))
  have h4pow_le : (4 : ℝ) ^ w ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hlog4 : Real.log 4 ≤ 2 := by
      have h4eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4eq, Real.log_pow]
      have h2e : Real.log 2 < 1 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        exact lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
      push_cast
      linarith
    have hw_le : (w : ℝ) ≤ Real.log (n : ℝ) / 10 := Nat.floor_le (by positivity)
    calc
      (4 : ℝ) ^ w = Real.exp (w * Real.log 4) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp ((1 / 5 : ℝ) * Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
      _ = (n : ℝ) ^ (1 / 5 : ℝ) := by rw [mul_comm, ← Real.rpow_def_of_pos hnr_pos]
  let d₀ := (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) /
    (Real.log (n : ℝ)) ^ (1 / 3 : ℝ)
  have hd0_pos : 0 < d₀ := by positivity
  have hD0_le_d0 : (D₀ : ℝ) ≤ d₀ / (Real.log (n : ℝ)) ^ 2 := by
    have hlog3 : (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ (2 / 15 : ℝ) := by
      calc
        (Real.log (n : ℝ)) ^ 3 ≤ ((n : ℝ) ^ (1 / 30 : ℝ)) ^ 3 := by gcongr
        _ = (n : ℝ) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (n : ℝ) ^ (2 / 15 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
    have h1 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ d₀ / (Real.log (n : ℝ)) ^ 2 := by
      have hrpow_mul : (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (2 / 15 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hnr_pos]; norm_num
      have hloglog_1 : 1 ≤ (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      have hden : (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by
        have hle1 : (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) ≤ Real.log (n : ℝ) := by
          calc
            (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) ≤ (Real.log (n : ℝ)) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = Real.log (n : ℝ) := Real.rpow_one _
        calc
          (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2
              ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by gcongr
          _ = (Real.log (n : ℝ)) ^ 3 := by ring
      have hnum : (n : ℝ) ^ (1 / 5 : ℝ) * ((Real.log (n : ℝ)) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤
          (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) := by
        calc
          (n : ℝ) ^ (1 / 5 : ℝ) * ((Real.log (n : ℝ)) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2)
              ≤ (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by gcongr
          _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (2 / 15 : ℝ) := by gcongr
          _ = (n : ℝ) ^ (1 / 3 : ℝ) := hrpow_mul
          _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (1 / 3 : ℝ) :=
            le_mul_of_one_le_right (by positivity) hloglog_1
      dsimp [d₀]
      rw [div_div, le_div_iff₀ (by positivity)]
      exact hnum
    exact (hD0_le_4pow.trans h4pow_le).trans h1
  have hz_512 : 512 * (Real.log (n : ℝ)) ^ 4 ≤ (z : ℝ) := by linarith
  obtain ⟨d, hd_pos, hd_cop, hd_fac, hD0_dvd_d, hd_gt, hd_le⟩ :=
    choose_d_params n z w D₀ d₀ hn1 hlog_ge hloglog_rp hprime_all hwz rfl hD0_pos hD0_cop
      hD0_le_d0 hd0_pos hz_512
  let S := (Nat.primesLE z).filter (fun p => ¬ p ∣ n)
  let ψ := (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
    (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))
  have hntot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1
  have htot_ge1 : 1 ≤ (n : ℝ) / n.totient := by
    rw [one_le_div hntot_pos]
    exact_mod_cast Nat.totient_le n
  have hden_le : Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 := by
    have h1 : Real.log (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.log (n : ℝ) := by
      calc
        Real.log (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.log (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log (n : ℝ) := Real.rpow_one _
    have h2 : Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤ Real.log (n : ℝ) := by
      calc
        Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤ Real.log (Real.log (n : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log (Real.log (n : ℝ)) := Real.rpow_one _
        _ ≤ Real.log (n : ℝ) := by linarith
    rw [sq]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hψ_ge_div : (n : ℝ) ^ (1 / 3 : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤ ψ := by
    have hnum : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / n.totient) :=
      le_mul_of_one_le_right (by positivity) htot_ge1
    exact div_le_div₀ (by positivity) hnum (by positivity) hden_le
  have hn15_le : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hlog2_rp : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (1 / 15 : ℝ) := by
      calc
        (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ (1 / 30 : ℝ)) ^ 2 := by gcongr
        _ = (n : ℝ) ^ (1 / 15 : ℝ) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
    calc
      (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 2
          ≤ (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 15 : ℝ) := by gcongr
      _ = (n : ℝ) ^ (4 / 15 : ℝ) := by rw [← Real.rpow_add hnr_pos]; norm_num
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
  have hS_le_ψ : (S.card : ℝ) ≤ ψ := by
    have hS_sub : S ⊆ Finset.Icc 1 z := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE ht'.1).one_le, Nat.le_of_mem_primesLE ht'.1⟩
    have hS_card : (S.card : ℝ) ≤ (z : ℝ) := by
      calc
        (S.card : ℝ) ≤ ((Finset.Icc 1 z).card : ℝ) := by exact_mod_cast Finset.card_le_card hS_sub
        _ = z := by simp
    exact hS_card.trans ((Nat.floor_le (by positivity)).trans (hn15_le.trans hψ_ge_div))
  have hone_le_ψ : (1 : ℝ) ≤ ψ := by
    have hz_real : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
    exact hz_real.trans ((Nat.floor_le (by positivity)).trans (hn15_le.trans hψ_ge_div))
  have hdtot_le := bound_d_totient n d D₀ w d₀ ψ hn1 hd_pos hw1 hlog_pos hloglog_pos hlog_w1
    rfl hD0_dvd_d hd_le rfl rfl
  have hR_div_le := bound_R_div_d n d z d₀ ψ hn1 hd_pos hz_128 hzn hnz hlog_ge hloglog_ge hlog_z
    hlog_rp30 hconst_rp hd_gt hd0_pos rfl rfl hψ_ge_div
  refine ⟨0, d, S, hd_pos, ?_, hd_cop, hd_fac, ?_⟩
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE hp'.1, hp'.2⟩
  · dsimp only
    push_cast
    simp only [zero_add]
    linarith

end Helpers

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1.H2 := by
  refine ⟨67 + 36 * Real.exp 180, by positivity, ?_⟩
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_atTop : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_atTop
  have hlog_lt_rpow15 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 15 : ℝ) := by
    have hb := ((isLittleO_log_rpow_atTop (r := 1 / 15) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb, eventually_ge_atTop 2] with n hn hn2
    simp only [Function.comp_def, Real.norm_eq_abs] at hn
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_nonneg (by positivity)] at hn
    linarith
  have hlog_lt_rpow30 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 30 : ℝ) := by
    have hb := ((isLittleO_log_rpow_atTop (r := 1 / 30) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb, eventually_ge_atTop 2] with n hn hn2
    simp only [Function.comp_def, Real.norm_eq_abs] at hn
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_nonneg (by positivity)] at hn
    linarith
  have hlog_lt_rpow45 : ∀ᶠ n : ℕ in atTop, 1024 * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hb := ((isLittleO_log_rpow_atTop (r := 1 / 25) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 8)
    filter_upwards [hb, eventually_ge_atTop 2] with n hn hn2
    simp only [Function.comp_def, Real.norm_eq_abs] at hn
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_nonneg (by positivity)] at hn
    have h4 : (Real.log (n : ℝ)) ^ 4 ≤ ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 25 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (Real.log_natCast_nonneg n) hn 4
    have h4' : 1024 * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ (4 / 25 : ℝ) := by
      calc
        1024 * (Real.log (n : ℝ)) ^ 4 ≤ 1024 * ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 25 : ℝ)) ^ 4 := by gcongr
        _ = (1 / 4 : ℝ) * ((n : ℝ) ^ (1 / 25 : ℝ)) ^ 4 := by ring
        _ ≤ ((n : ℝ) ^ (1 / 25 : ℝ)) ^ 4 := by linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 25 : ℝ)) 4]
        _ = (n : ℝ) ^ (4 / 25 : ℝ) := by
          rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]; norm_num
    have hle : (n : ℝ) ^ (4 / 25 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    exact h4'.trans hle
  have hconst_le_rpow : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ^ 65 ≤ (n : ℝ) ^ (1 / 30 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).comp tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop ((4 : ℝ) ^ 65)
  have hloglog_le : ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 20 := by
    have hb := ((isLittleO_log_rpow_atTop (r := 1) zero_lt_one).comp_tendsto hlog_atTop).bound
      (by norm_num : (0 : ℝ) < 1 / 20)
    filter_upwards [hb, hlog_atTop.eventually_ge_atTop 2] with n hn hln
    simp only [Function.comp_def, Real.norm_eq_abs, Real.rpow_one] at hn
    rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg (by linarith)] at hn
    linarith
  have h_int_prime_all : ∀ᶠ n : ℕ in atTop,
      ∀ X : ℕ, ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ ≤ X →
        3 * (X : ℝ) / Real.log X ≤ (Nat.primeCounting (16 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by
    obtain ⟨X_min, hX_min⟩ := eventually_atTop.mp prime_interval_diff_eventually
    filter_upwards [hlog_atTop.eventually_ge_atTop (Real.sqrt (2 * ((X_min : ℝ) + 1)) + 1)] with n hn X hX
    apply hX_min
    have h1 : 2 * ((X_min : ℝ) + 1) ≤ (Real.log (n : ℝ)) ^ 2 := by
      have : (Real.sqrt (2 * ((X_min : ℝ) + 1))) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * ((X_min : ℝ) + 1))]
      rwa [Real.sq_sqrt (by positivity)] at this
    have h2 : ((X_min + 1 : ℕ) : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 / 2 := by
      push_cast
      linarith
    have h3 : X_min + 1 ≤ ⌊(Real.log (n : ℝ)) ^ 2 / 2⌋₊ := Nat.le_floor h2
    omega
  filter_upwards [eventually_ge_atTop 1000, hlog_atTop.eventually_ge_atTop 1000,
    hloglog_atTop.eventually_ge_atTop 100, hlog_lt_rpow15, hlog_lt_rpow30, hlog_lt_rpow45,
    hconst_le_rpow, hloglog_le, h_int_prime_all] with
    n hn1000 hlog_ge hloglog_ge hlog_rp15 hlog_rp30 hlog_rp45 hconst_rp hloglog_rp hprime_all
  exact erdos360_h2_pointwise n (by omega) hlog_ge hloglog_ge hlog_rp15 hlog_rp30 hlog_rp45
    hconst_rp hloglog_rp hprime_all
