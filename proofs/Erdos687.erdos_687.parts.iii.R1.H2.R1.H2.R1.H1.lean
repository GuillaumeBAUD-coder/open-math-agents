import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1
-- Credit: @santiemanuel

/-!
# Mertens' Third Theorem Lower Bound

We prove `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1`:
there exists `c₀ > 0` (explicitly `c₀ = Real.exp (-11)`) such that for every `x ≥ 2`,
`c₀ / Real.log x ≤ ∏_{p ≤ x} (1 - 1 / p)`.

The proof follows Mertens' 1874 elementary method:
1. `prime_pow_div_dvd_factorial`: For each prime `p ≤ n`, `p ^ (n / p) ∣ n!`, hence
   `∏_{p ≤ n} p ^ (n / p) ≤ n! ≤ n ^ n`.
2. `mertens_first_upper`: Taking logarithms and applying `Chebyshev.theta_le_log4_mul_x` yields
   `∑_{p ≤ n} (log p) / p ≤ log n + log 4`.
3. `mertens_second_upper`: Discrete Abel summation gives
   `∑_{p ≤ x} 1 / p ≤ log (log x) + 10` for all `x ≥ 2`.
4. `OMA.solution`: Using the exact identity `(1 - p⁻¹)⁻¹ = 1 + p⁻¹ + (p * (p - 1))⁻¹` and the
   telescoping bound `∑_{p ≤ x} (p * (p - 1))⁻¹ ≤ 1` gives `∏_{p ≤ x} (1 - p⁻¹) ≥ exp (-11) / log x`.
-/

open Finset Real

private lemma finset_prod_dvd_of_coprime {S : Finset ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hcop : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime f))
    (hdvd : ∀ p ∈ S, f p ∣ n) : (∏ p ∈ S, f p) ∣ n := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    have hcop_s : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime f) :=
      hcop.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx))
    have hs_dvd : (∏ p ∈ s, f p) ∣ n := ih hcop_s (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
    have ha_dvd : f a ∣ n := hdvd a (Finset.mem_cons_self a s)
    have ha_cop : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
          (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hp))
          (fun heq => has (heq ▸ hp))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

private lemma prime_pow_div_dvd_factorial {p n : ℕ} (hp : 1 ≤ p) :
    p ^ (n / p) ∣ n.factorial := by
  have hfact : n.factorial = ∏ m ∈ Icc 1 n, m := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.factorial_succ, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.mul_comm]
  rw [hfact]
  have himg_sub : (Icc 1 (n / p)).image (fun j => p * j) ⊆ Icc 1 n := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hj' := mem_Icc.mp hj
    have hmul : p * j ≤ n := by
      have h1 : j * p ≤ (n / p) * p := Nat.mul_le_mul_right p hj'.2
      have h2 : (n / p) * p ≤ n := Nat.div_mul_le_self n p
      rw [Nat.mul_comm]
      exact h1.trans h2
    exact mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega), hmul⟩
  have hprod_dvd : (∏ m ∈ (Icc 1 (n / p)).image (fun j => p * j), m) ∣ ∏ m ∈ Icc 1 n, m :=
    Finset.prod_dvd_prod_of_subset _ _ _ himg_sub
  have hprod_eq : ∏ m ∈ (Icc 1 (n / p)).image (fun j => p * j), m =
      p ^ (n / p) * ∏ j ∈ Icc 1 (n / p), j := by
    rw [Finset.prod_image (fun j₁ _ j₂ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hprod_eq] at hprod_dvd
  exact dvd_trans (dvd_mul_right _ _) hprod_dvd

private lemma mertens_first_upper {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + 2 := by
  let P := (range (n + 1)).filter Nat.Prime
  have hcop : Set.Pairwise (P : Set ℕ) (Function.onFun Nat.Coprime (fun p => p ^ (n / p))) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (mem_filter.mp (mem_coe.mp hp)).2
      (mem_filter.mp (mem_coe.mp hq)).2).2 hpq).pow _ _
  have hdvd : (∏ p ∈ P, p ^ (n / p)) ∣ n.factorial :=
    finset_prod_dvd_of_coprime hcop fun p hp =>
      prime_pow_div_dvd_factorial (mem_filter.mp hp).2.one_le
  have hfact_le : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hprod_le : ∏ p ∈ P, p ^ (n / p) ≤ n ^ n :=
    (Nat.le_of_dvd (Nat.factorial_pos n) hdvd).trans hfact_le
  have hprod_pos : 0 < ∏ p ∈ P, p ^ (n / p) :=
    Finset.prod_pos fun p hp => pow_pos (mem_filter.mp hp).2.pos _
  have hlog_le : Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hprod_le)
  have hlhs_log : Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) =
      ∑ p ∈ P, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (pow_pos (mem_filter.mp hp).2.pos _).ne')]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hrhs_log : Real.log ((n ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlhs_log, hrhs_log] at hlog_le
  have hfloor : ∑ p ∈ P, ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
      ∑ p ∈ P, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : p.Prime := (mem_filter.mp hp).2
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hlt_nat : n < (n / p + 1) * p := by
      rw [Nat.add_mul, Nat.one_mul]
      have hdm : (n / p) * p + n % p = n := by rw [Nat.mul_comm]; exact Nat.div_add_mod n p
      have hml := Nat.mod_lt n hpp.pos
      omega
    have hlt_r : (n : ℝ) < (((n / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hlt_nat
    have hdiv_r : (n : ℝ) / (p : ℝ) - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have h1 : (n : ℝ) / (p : ℝ) ≤ ((n / p : ℕ) : ℝ) + 1 :=
        (div_le_iff₀ hp_pos).mpr hlt_r.le
      linarith
    exact mul_le_mul_of_nonneg_right hdiv_r hlogp_nn
  have hsplit : ∑ p ∈ P, ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) =
      (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have htheta : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ) := by
    have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hsum_eq : Chebyshev.theta (n : ℝ) = ∑ p ∈ P, Real.log (p : ℝ) := by
      rw [Chebyshev.theta]
      congr 1
      ext p
      simp only [P, mem_filter, mem_Ioc, mem_range, Nat.floor_natCast]
      constructor
      · rintro ⟨⟨_, hpn⟩, hpp⟩; exact ⟨by omega, hpp⟩
      · rintro ⟨hpn, hpp⟩; exact ⟨⟨hpp.pos, by omega⟩, hpp⟩
    rwa [hsum_eq] at hth
  have hlog4_le2 : Real.log 4 ≤ 2 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      rfl
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcomb : (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤
      (n : ℝ) * (Real.log (n : ℝ) + 2) := by
    have h1 := hfloor.trans hlog_le
    rw [hsplit] at h1
    have h2 : Real.log 4 * (n : ℝ) ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hlog4_le2 hn_pos.le
    linarith
  exact le_of_mul_le_mul_left hcomb hn_pos

private lemma mertens_second_upper {x : ℕ} (hx : 2 ≤ x) :
    ∑ p ∈ (range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      Real.log (Real.log (x : ℝ)) + 10 := by
  let M : ℕ → ℝ := fun k => ∑ p ∈ (range (k + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
  have habel : ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, (p : ℝ)⁻¹ =
        M n / Real.log (n : ℝ) +
          ∑ k ∈ Icc 2 (n - 1), M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have hP2 : (range 3).filter Nat.Prime = {2} := by decide
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 :=
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
      simp only [M, hP2, Finset.sum_singleton, Nat.cast_ofNat]
      have hemp : Icc 2 (2 - 1) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [hemp, Finset.sum_empty, add_zero]
      field_simp
    | succ m hm ih =>
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub]
      have hIcc : Icc 2 m = insert m (Icc 2 (m - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have hnotmem : m ∉ Icc 2 (m - 1) := by simp only [mem_Icc]; omega
      rw [hIcc, Finset.sum_insert hnotmem]
      have hstep_sum :
          ∑ p ∈ (range (m + 1 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ =
            (∑ p ∈ (range (m + 1)).filter Nat.Prime, (p : ℝ)⁻¹) +
              (M (m + 1) - M m) / Real.log ((m + 1 : ℕ) : ℝ) := by
        have hrange : range (m + 1 + 1) = insert (m + 1) (range (m + 1)) :=
          Finset.range_add_one
        have hnm : m + 1 ∉ range (m + 1) := Finset.notMem_range_self
        have hlogm1_ne : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))).ne'
        by_cases hp : (m + 1).Prime
        · have hf : (range (m + 1 + 1)).filter Nat.Prime =
              insert (m + 1) ((range (m + 1)).filter Nat.Prime) := by
            rw [hrange, Finset.filter_insert, if_pos hp]
          have hnmf : m + 1 ∉ (range (m + 1)).filter Nat.Prime := fun h => hnm (mem_filter.mp h).1
          rw [hf, Finset.sum_insert hnmf]
          have hMdiff : M (m + 1) - M m = Real.log ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
            dsimp [M]
            rw [hf, Finset.sum_insert hnmf]
            ring
          rw [hMdiff]
          field_simp
          ring
        · have hf : (range (m + 1 + 1)).filter Nat.Prime = (range (m + 1)).filter Nat.Prime := by
            rw [hrange, Finset.filter_insert, if_neg hp]
          have hMdiff : M (m + 1) - M m = 0 := by
            dsimp [M]
            rw [hf, sub_self]
          rw [hf, hMdiff, zero_div, add_zero]
      rw [hstep_sum, ih]
      ring
  rw [habel x hx]
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h1
    linarith
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogx_ge : Real.log 2 ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hterm1 : M x / Real.log (x : ℝ) ≤ 5 := by
    have hMx : M x ≤ Real.log (x : ℝ) + 2 := mertens_first_upper (by omega)
    have h1 : M x / Real.log (x : ℝ) ≤ (Real.log (x : ℝ) + 2) / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right hMx hlogx_pos.le
    have h2 : (Real.log (x : ℝ) + 2) / Real.log (x : ℝ) = 1 + 2 / Real.log (x : ℝ) := by
      field_simp
    have h3 : 2 / Real.log (x : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hlogx_pos]
      linarith
    linarith
  have hterm2 :
      ∑ k ∈ Icc 2 (x - 1), M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
        Real.log (Real.log (x : ℝ)) + 5 := by
    have hpt : ∀ k ∈ Icc 2 (x - 1),
        M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
          (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            2 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) := by
      intro k hk
      have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
      have hlk_pos : 0 < Real.log (k : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < k by omega))
      have hlk1_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
      have hlk_le : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast Nat.le_succ k)
      have hdiff_nn : 0 ≤ (Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ :=
        sub_nonneg.mpr (inv_anti₀ hlk_pos hlk_le)
      have hMk : M k ≤ Real.log (k : ℝ) + 2 := mertens_first_upper (by omega)
      have hstep1 : M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
          (Real.log (k : ℝ) + 2) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right hMk hdiff_nn
      have hstep2 : Real.log (k : ℝ) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) =
          1 - Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) := by
        field_simp
      have hlog_ineq : 1 - Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) ≤
          Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hlk_pos hlk1_pos)
        rw [Real.log_div hlk_pos.ne' hlk1_pos.ne'] at h
        linarith
      linarith
    have htele : ∀ n : ℕ, 2 ≤ n →
        ∑ k ∈ Icc 2 (n - 1),
          ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            2 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)) =
        (Real.log (Real.log (n : ℝ)) - Real.log (Real.log 2)) +
          2 * ((Real.log 2)⁻¹ - (Real.log (n : ℝ))⁻¹) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        have hemp : Icc 2 (2 - 1) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
        rw [hemp, Finset.sum_empty]
        simp
      | succ m hm ih =>
        have hsub : m + 1 - 1 = m := by omega
        rw [hsub]
        have hIcc : Icc 2 m = insert m (Icc 2 (m - 1)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have hnotmem : m ∉ Icc 2 (m - 1) := by simp only [mem_Icc]; omega
        rw [hIcc, Finset.sum_insert hnotmem, ih]
        ring
    have h1 := (Finset.sum_le_sum hpt).trans_eq (htele x hx)
    have hll2_ge : -1 ≤ Real.log (Real.log 2) := by
      have h1' : Real.log (2⁻¹ : ℝ) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_inv] at h1'
      linarith
    have hinv2_le : (Real.log 2)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have hinvx_nn : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hlogx_pos.le
    linarith
  linarith

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1 := by
  refine ⟨Real.exp (-11), by positivity, fun x hx => ?_⟩
  let P := (range (x + 1)).filter Nat.Prime
  have hlogx_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hV_pos : 0 < ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  have hinv_le : (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      Real.exp (∑ p ∈ P, (p : ℝ)⁻¹ + ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
    rw [← Finset.prod_inv_distrib, ← Finset.sum_add_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
      have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      have hpp : p.Prime := (mem_filter.mp hp).2
      have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      have hp1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show p - 1 ≠ 0 by have := hpp.two_le; omega)
      have hp_sub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
      have hp1_ne' : (p : ℝ) - 1 ≠ 0 := by rwa [hp_sub] at hp1_ne
      have hid : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + ((p : ℝ)⁻¹ + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
        rw [hp_sub]
        field_simp
        ring
      rw [hid]
      linarith [Real.add_one_le_exp ((p : ℝ)⁻¹ + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹)]
  have hsq_sum : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    have htele : ∀ m : ℕ, 2 ≤ m →
        ∑ n ∈ Icc 2 m, ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ = 1 - (m : ℝ)⁻¹ := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1), ih]
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub]
        have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring
    have hP_sub : P ⊆ Icc 2 x := by
      intro p hp
      have h := mem_filter.mp hp
      have hr := mem_range.mp h.1
      exact mem_Icc.mpr ⟨h.2.two_le, by omega⟩
    have h1 : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤
        ∑ n ∈ Icc 2 x, ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hP_sub (fun _ _ _ => by positivity)
    rw [htele x hx] at h1
    have hnn : (0 : ℝ) ≤ (x : ℝ)⁻¹ := by positivity
    linarith
  have hsum_le : ∑ p ∈ P, (p : ℝ)⁻¹ + ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤
      Real.log (Real.log (x : ℝ)) + 11 := by
    linarith [mertens_second_upper hx]
  have hinv_bound : (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ ≤ Real.exp 11 * Real.log (x : ℝ) := by
    calc
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹
          ≤ Real.exp (Real.log (Real.log (x : ℝ)) + 11) :=
        hinv_le.trans (Real.exp_le_exp.mpr hsum_le)
      _ = Real.exp 11 * Real.log (x : ℝ) := by
        rw [Real.exp_add, Real.exp_log hlogx_pos, mul_comm]
  rw [div_le_iff₀ hlogx_pos]
  have hmul : (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤
      (Real.exp 11 * Real.log (x : ℝ)) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) :=
    mul_le_mul_of_nonneg_right hinv_bound hV_pos.le
  rw [inv_mul_cancel₀ hV_pos.ne'] at hmul
  have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ Real.exp (-11))
  have hexp_cancel : Real.exp (-11) * (Real.exp 11 * Real.log (x : ℝ)) = Real.log (x : ℝ) := by
    rw [← mul_assoc, ← Real.exp_add]
    norm_num
  have hgoal : Real.exp (-11) ≤ Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by
    calc
      Real.exp (-11) = Real.exp (-11) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-11) * ((Real.exp 11 * Real.log (x : ℝ)) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹))) := hmul2
      _ = Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by rw [← mul_assoc, hexp_cancel]
  linarith
