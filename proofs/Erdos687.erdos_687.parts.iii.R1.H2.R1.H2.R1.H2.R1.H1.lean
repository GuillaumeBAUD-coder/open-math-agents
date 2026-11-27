import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1
-- Credit: @santiemanuel

/-!
# Unconditional $L^2$ Minor-Arc Mean-Square Bound (`R1.H2.R1.H2.R1.H2.R1.H1`)

We prove `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H1` with the explicit constant
`C = Real.exp 13`:
for every `x ≥ 2` and `L ≥ 1` (`D = L / (Nat.log 2 L + 1)`, `Q = ∏_{p ≤ x} p`),
`∑_{M < Q} S_min(M)^2 ≤ exp 13 * Q * L * log x`.

Proof outline:
1. Express `S_min(M)` as `(Z M).re` for the complex exponential sum `Z M` and bound
   `(S_min(M))^2 ≤ ‖Z M‖^2`.
2. Sum `‖Z M‖^2 = Z M * conj (Z M)` over `M ∈ range Q` using
   `spectral_orthogonality_on_primorial`, collapsing all off-diagonal pairs `(d₁, r₁) ≠ (d₂, r₂)` to zero.
3. Bound each diagonal Fejér fourth-moment sum `∑_{(r, d)=1} K_{d, r}^2 ≤ d * L` (via
   `fejer_sum_parseval` when `d ≤ L` and exact diagonal orthogonality when `d > L`).
4. Evaluate `∑_{d ∣ Q} d / φ(d)^2 = ∏_{p ≤ x} (1 + p / (p - 1)^2)` and bound it by
   `exp 13 * log x` via `p / (p - 1)^2 ≤ p⁻¹ + 3 / (p * (p - 1))` and Mertens' second upper bound.
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

private lemma fejer_fourth_moment_le {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L) :
    ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
        (L : ℝ)) ^ 2 ≤
      (d : ℝ) * (L : ℝ) := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- First show `K_{d, r} ≤ L`, so `K_{d, r} ^ 2 ≤ ‖∑ u < L, e(r u / d)‖ ^ 2`.
  have hpt : ∀ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
        (L : ℝ)) ^ 2 ≤
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    intro r _
    set N := ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖
    have hN_nn : 0 ≤ N := norm_nonneg _
    have hN_le : N ≤ (L : ℝ) := by
      calc
        N ≤ ∑ u ∈ range L,
            ‖Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
          norm_sum_le _ _
        _ = ∑ _u ∈ range L, (1 : ℝ) :=
          Finset.sum_congr rfl fun _ _ => Complex.norm_exp_ofReal_mul_I _
        _ = (L : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hN2_le : N ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hN_nn hN_le 2
    have hK_le : N ^ 2 / (L : ℝ) ≤ (L : ℝ) := by
      rw [div_le_iff₀ hL_pos]
      nlinarith
    have hK_nn : 0 ≤ N ^ 2 / (L : ℝ) := by positivity
    calc
      (N ^ 2 / (L : ℝ)) ^ 2 = (N ^ 2 / (L : ℝ)) * (N ^ 2 / (L : ℝ)) := sq _
      _ ≤ (L : ℝ) * (N ^ 2 / (L : ℝ)) := mul_le_mul_of_nonneg_right hK_le hK_nn
      _ = N ^ 2 := mul_div_cancel₀ _ hL_pos.ne'
  have hstep1 :
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        (‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
          (L : ℝ)) ^ 2 ≤
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        ‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
    Finset.sum_le_sum hpt
  by_cases hdL : d ≤ L
  · -- Case `d ≤ L`: apply `fejer_sum_parseval` (`≤ d ^ 2 / 4 ≤ d * L`).
    have hsub : (range d).filter (fun r => Nat.Coprime r d) ⊆ (range d).filter (fun r => r ≠ 0) := by
      intro r hr
      obtain ⟨hr_rng, hr_cop⟩ := mem_filter.mp hr
      refine mem_filter.mpr ⟨hr_rng, fun hr0 => ?_⟩
      subst hr0
      rw [Nat.coprime_zero_left] at hr_cop
      omega
    have hstep2 :
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        ∑ r ∈ (range d).filter (fun r => r ≠ 0),
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    have hp := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.fejer_sum_parseval (L := L) (by omega : 1 ≤ d)
    have hdL_r : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hdL
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact hstep1.trans (hstep2.trans (hp.trans (by nlinarith)))
  · -- Case `L < d`: sum over all `r ∈ range d` equals `d * L` by exact orthogonality mod `d`.
    push Not at hdL
    have hstep2 :
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        ∑ r ∈ range d,
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have hfull_c :
        (∑ r ∈ range d,
          ((‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) =
        ((d : ℝ) * (L : ℝ) : ℂ) := by
      have hnorm : ∀ r ∈ range d,
          ((‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
          ∑ u ∈ range L, ∑ v ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
        intro r _
        rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [Finset.sum_congr rfl hnorm]
      trans (∑ u ∈ range L, ∑ v ∈ range L, ∑ r ∈ range d,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      · simp_rw [OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.sum_exp_int_div (by omega : 1 ≤ d)]
        have hdiag : ∀ u ∈ range L,
            (∑ v ∈ range L, if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (d : ℂ) else 0) = (d : ℂ) := by
          intro u hu
          have huL : u < L := mem_range.mp hu
          have heq_if : ∀ v ∈ range L,
              (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (d : ℂ) else 0) =
              if v = u then (d : ℂ) else 0 := by
            intro v hv
            have hvL : v < L := mem_range.mp hv
            by_cases hvu : v = u
            · subst hvu; simp
            · rw [if_neg hvu, if_neg]
              rintro ⟨k, hk⟩
              have hlo : -(d : ℤ) < (u : ℤ) - (v : ℤ) := by omega
              have hhi : (u : ℤ) - (v : ℤ) < (d : ℤ) := by omega
              have hk0 : k = 0 := by nlinarith
              rw [hk0, mul_zero] at hk
              omega
          rw [Finset.sum_congr rfl heq_if, Finset.sum_ite_eq' (range L) u, if_pos hu]
        rw [Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    have hfull_r :
        ∑ r ∈ range d,
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
        (d : ℝ) * (L : ℝ) := by
      have hre := congrArg Complex.re hfull_c
      simp only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        mul_zero, sub_zero] at hre
      exact hre
    exact hstep1.trans (hstep2.trans_eq hfull_r)

private lemma divisors_mul_prime_of_coprime {q Q : ℕ} (hq : q.Prime) (hQ : 0 < Q) :
    (q * Q).divisors = Q.divisors ∪ Q.divisors.image (fun d => q * d) := by
  ext d
  simp only [Nat.mem_divisors, mem_union, mem_image]
  have hqQ : q * Q ≠ 0 := Nat.mul_ne_zero hq.ne_zero (by omega)
  constructor
  · rintro ⟨hdvd, _⟩
    by_cases hqd : q ∣ d
    · right
      obtain ⟨d', rfl⟩ := hqd
      exact ⟨d', ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd, by omega⟩, rfl⟩
    · left
      exact ⟨((hq.coprime_iff_not_dvd).mpr hqd).symm.dvd_of_dvd_mul_left hdvd, by omega⟩
  · rintro (⟨hdQ, _⟩ | ⟨d', ⟨hd'Q, _⟩, rfl⟩)
    · exact ⟨dvd_mul_of_dvd_right hdQ q, hqQ⟩
    · exact ⟨Nat.mul_dvd_mul_left q hd'Q, hqQ⟩

private lemma disjoint_divisors_mul_prime {q Q : ℕ} (hq : q.Prime) (hcop : Nat.Coprime q Q) :
    Disjoint Q.divisors (Q.divisors.image (fun d => q * d)) := by
  rw [Finset.disjoint_left]
  intro d hdQ hdim
  obtain ⟨d', _, rfl⟩ := mem_image.mp hdim
  have hqQ : q ∣ Q := dvd_trans (dvd_mul_right q d') (Nat.mem_divisors.mp hdQ).1
  have h1 := Nat.dvd_gcd dvd_rfl hqQ
  rw [hcop.gcd_eq_one] at h1
  exact hq.not_dvd_one h1

private lemma divisors_d_over_totient_sq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    let Q := ∏ p ∈ P, p
    (∀ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 ≤ 1) ∧
    (∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) =
      ∏ p ∈ P, (1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2))) := by
  induction P using Finset.cons_induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · intro d hd
      simp only [Finset.prod_empty, Nat.divisors_one, mem_singleton] at hd
      subst hd
      simp
    · simp
  | cons q T hqT ih =>
    have hq : q.Prime := hP q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_cons_of_mem hp)
    obtain ⟨ih_mob, ih_sum⟩ := ih hT
    let QT := ∏ p ∈ T, p
    have hQT_pos : 0 < QT := Finset.prod_pos fun p hp => (hT p hp).pos
    have hcop_qQT : Nat.Coprime q QT :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp)).2 (fun heq => hqT (heq ▸ hp))
    have hQ_eq : ∏ p ∈ cons q T hqT, p = q * QT := Finset.prod_cons hqT
    have hdiv_eq := divisors_mul_prime_of_coprime hq hQT_pos
    have hdiv_disj := disjoint_divisors_mul_prime hq hcop_qQT
    refine ⟨?_, ?_⟩
    · intro d hd
      rw [hQ_eq, hdiv_eq, mem_union] at hd
      rcases hd with hdT | hdim
      · exact ih_mob d hdT
      · obtain ⟨d', hd'T, rfl⟩ := mem_image.mp hdim
        have hcop_qd' : Nat.Coprime q d' := hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hd'T).1
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qd',
          ArithmeticFunction.moebius_apply_prime hq]
        push_cast
        nlinarith [ih_mob d' hd'T]
    · rw [hQ_eq, hdiv_eq, Finset.sum_union hdiv_disj,
        Finset.sum_image (fun k₁ _ k₂ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h),
        Finset.prod_cons hqT]
      have hsum2 : ∑ d ∈ QT.divisors, ((q * d : ℕ) : ℝ) / ((Nat.totient (q * d) : ℝ) ^ 2) =
          ((q : ℝ) / (((q - 1 : ℕ) : ℝ) ^ 2)) *
            ∑ d ∈ QT.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hcop_qd : Nat.Coprime q d := hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hd).1
        rw [Nat.totient_mul hcop_qd, Nat.totient_prime hq]
        push_cast
        ring
      rw [hsum2, ih_sum]
      ring

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H1 := by
  refine ⟨Real.exp 13, by positivity, fun x hx L hL => ?_⟩
  intro D Q
  let P := (range (x + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hQ_pos : 1 ≤ Q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hD_ge1 : 1 ≤ D := by
    dsimp [D]
    by_cases hL2 : 2 ≤ L
    · have hlt : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    · have hL1 : L = 1 := by omega
      subst hL1
      norm_num
  let S_D := Q.divisors.filter (fun d => D < d)
  let R : ℕ → Finset ℕ := fun d => (range d).filter (fun r => Nat.Coprime r d)
  let K : ℕ → ℕ → ℝ := fun d r =>
    ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 / (L : ℝ)
  let coeff : ℕ → ℕ → ℝ := fun d r =>
    ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) * K d r
  let Z : ℕ → ℂ := fun M =>
    ∑ d ∈ S_D, ∑ r ∈ R d,
      ((coeff d r : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)
  -- Step 1: Bound `(S_min M) ^ 2 = ((Z M).re) ^ 2 ≤ ‖Z M‖ ^ 2` for each `M ∈ range Q`.
  have hre_eq : ∀ M : ℕ,
      (∑ d ∈ S_D,
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ R d,
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * K d r) =
      (Z M).re := by
    intro M
    dsimp [Z, coeff]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  have hsq_le_norm :
      ∑ M ∈ range Q,
        (∑ d ∈ S_D,
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ R d,
              Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * K d r) ^ 2 ≤
      ∑ M ∈ range Q, ‖Z M‖ ^ 2 := by
    refine Finset.sum_le_sum fun M _ => ?_
    rw [hre_eq M, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (Z M).im]
  -- Step 2: Evaluate `∑_{M < Q} ‖Z M‖ ^ 2` via `spectral_orthogonality_on_primorial`.
  have hparseval_c :
      (∑ M ∈ range Q, ((‖Z M‖ ^ 2 : ℝ) : ℂ)) =
      (Q : ℂ) * ∑ d ∈ S_D, ∑ r ∈ R d, (((coeff d r) ^ 2 : ℝ) : ℂ) := by
    have hexpand : ∀ M ∈ range Q,
        ((‖Z M‖ ^ 2 : ℝ) : ℂ) =
        ∑ d₁ ∈ S_D, ∑ d₂ ∈ S_D, ∑ r₁ ∈ R d₁, ∑ r₂ ∈ R d₂,
          (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ) *
            (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
              starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))) := by
      intro M _
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      dsimp [Z]
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [Finset.sum_congr rfl hexpand]
    -- Swap `M` inside `(d₁, d₂, r₁, r₂)` and swap `d₂` with `r₁`.
    trans (∑ d₁ ∈ S_D, ∑ r₁ ∈ R d₁, ∑ d₂ ∈ S_D, ∑ r₂ ∈ R d₂, ∑ M ∈ range Q,
      (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ) *
        (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
          starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))))
    · trans (∑ d₁ ∈ S_D, ∑ d₂ ∈ S_D, ∑ r₁ ∈ R d₁, ∑ r₂ ∈ R d₂, ∑ M ∈ range Q,
        (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ) *
          (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
            starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))))
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_comm
      · refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r₁ hr₁ => ?_
      have hd₁Q : d₁ ∈ Q.divisors := (mem_filter.mp hd₁).1
      have hr₁_lt : r₁ < d₁ := mem_range.mp (mem_filter.mp hr₁).1
      have hr₁_cop : Nat.Coprime r₁ d₁ := (mem_filter.mp hr₁).2
      have hinner_d₂ : ∀ d₂ ∈ S_D,
          (∑ r₂ ∈ R d₂, ∑ M ∈ range Q,
            (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ) *
              (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
                starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I))))) =
          if d₂ = d₁ then (Q : ℂ) * (((coeff d₁ r₁) ^ 2 : ℝ) : ℂ) else 0 := by
        intro d₂ hd₂
        have hd₂Q : d₂ ∈ Q.divisors := (mem_filter.mp hd₂).1
        have horth_r₂ : ∀ r₂ ∈ R d₂,
            (∑ M ∈ range Q,
              (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ) *
                (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
                  starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I))))) =
            if d₁ = d₂ ∧ r₁ = r₂ then (Q : ℂ) * (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ)) else 0 := by
          intro r₂ hr₂
          rw [← Finset.mul_sum,
            OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.spectral_orthogonality_on_primorial
              hQ_pos L hd₁Q hd₂Q hr₁_lt hr₁_cop
              (mem_range.mp (mem_filter.mp hr₂).1) (mem_filter.mp hr₂).2]
          split_ifs
          · ring
          · simp
        rw [Finset.sum_congr rfl horth_r₂]
        by_cases hd_eq : d₂ = d₁
        · subst hd_eq
          rw [if_pos rfl]
          have hsimp : ∀ r₂ ∈ R d₂,
              (if d₂ = d₂ ∧ r₁ = r₂ then (Q : ℂ) * (((coeff d₂ r₁ * coeff d₂ r₂ : ℝ) : ℂ)) else 0) =
              if r₂ = r₁ then (Q : ℂ) * (((coeff d₂ r₁) ^ 2 : ℝ) : ℂ) else 0 := by
            intro r₂ _
            by_cases hr_eq : r₂ = r₁
            · subst hr_eq; simp [sq]
            · have hne : ¬ (d₂ = d₂ ∧ r₁ = r₂) := fun h => hr_eq h.2.symm
              rw [if_neg hne, if_neg hr_eq]
          rw [Finset.sum_congr rfl hsimp, Finset.sum_ite_eq' (R d₂) r₁, if_pos hr₁]
        · rw [if_neg hd_eq]
          have hzero : ∀ r₂ ∈ R d₂,
              (if d₁ = d₂ ∧ r₁ = r₂ then (Q : ℂ) * (((coeff d₁ r₁ * coeff d₂ r₂ : ℝ) : ℂ)) else 0) = 0 := by
            intro r₂ _
            have hne : ¬ (d₁ = d₂ ∧ r₁ = r₂) := fun h => hd_eq h.1.symm
            rw [if_neg hne]
          rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl hinner_d₂, Finset.sum_ite_eq' S_D d₁, if_pos hd₁]
  have hparseval_r :
      ∑ M ∈ range Q, ‖Z M‖ ^ 2 =
      (Q : ℝ) * ∑ d ∈ S_D, ∑ r ∈ R d, (coeff d r) ^ 2 := by
    have hre := congrArg Complex.re hparseval_c
    rw [Complex.re_sum, ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hre
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    exact hre
  -- Step 3: Bound the diagonal spectral sum using `fejer_fourth_moment_le` and `divisors_d_over_totient_sq`.
  obtain ⟨hmob_sq, hdiv_sum⟩ := divisors_d_over_totient_sq P hP
  have hdiag_le :
      ∑ d ∈ S_D, ∑ r ∈ R d, (coeff d r) ^ 2 ≤
      (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
    have hterm : ∀ d ∈ S_D,
        ∑ r ∈ R d, (coeff d r) ^ 2 ≤ (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) := by
      intro d hd
      have hdQ : d ∈ Q.divisors := (mem_filter.mp hd).1
      have hd2 : 2 ≤ d := by
        have := (mem_filter.mp hd).2
        omega
      have heq_r : ∀ r ∈ R d,
          (coeff d r) ^ 2 =
            ((ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) ^ 2)) * (K d r) ^ 2 := by
        intro r _
        dsimp [coeff]
        ring
      rw [Finset.sum_congr rfl heq_r, ← Finset.mul_sum]
      have hcoeff_le : (ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) ^ 2) ≤
          1 / ((Nat.totient d : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (hmob_sq d hdQ) (sq_nonneg _)
      have hK4 := fejer_fourth_moment_le (L := L) hd2 hL
      calc
        ((ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) ^ 2)) * ∑ r ∈ R d, (K d r) ^ 2
            ≤ (1 / ((Nat.totient d : ℝ) ^ 2)) * ((d : ℝ) * (L : ℝ)) :=
          mul_le_mul hcoeff_le hK4 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) := by ring
    calc
      ∑ d ∈ S_D, ∑ r ∈ R d, (coeff d r) ^ 2
          ≤ ∑ d ∈ S_D, (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) := Finset.sum_le_sum hterm
      _ = (L : ℝ) * ∑ d ∈ S_D, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  -- Step 4: Bound `∏_{p ∈ P} (1 + p / (p - 1)^2) ≤ exp 13 * log x`.
  have hprod_le :
      ∏ p ∈ P, (1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp 13 * Real.log (x : ℝ) := by
    have hlogx_pos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hlocal : ∀ p ∈ P,
        1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2) ≤
          Real.exp ((p : ℝ)⁻¹ + 3 * ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
      intro p hp
      have hpp : p.Prime := hP p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp_ne : (p : ℝ) ≠ 0 := by linarith
      have hp_sub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
      have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
      have halg : (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2) ≤
          (p : ℝ)⁻¹ + 3 * ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ := by
        rw [hp_sub]
        have hdiff : ((p : ℝ)⁻¹ + 3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) - (p : ℝ) / (((p : ℝ) - 1) ^ 2) =
            ((p : ℝ) - 2) / ((p : ℝ) * (((p : ℝ) - 1) ^ 2)) := by
          field_simp
          ring
        have hnn : 0 ≤ ((p : ℝ) - 2) / ((p : ℝ) * (((p : ℝ) - 1) ^ 2)) :=
          div_nonneg (by linarith) (by positivity)
        linarith
      linarith [Real.add_one_le_exp ((p : ℝ)⁻¹ + 3 * ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹)]
    have hexp_prod :
        ∏ p ∈ P, (1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2)) ≤
        Real.exp (∑ p ∈ P, (p : ℝ)⁻¹ + 3 * ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
      exact Finset.prod_le_prod (fun _ _ => by positivity) hlocal
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
      have hP_sub : P ⊆ Icc 2 x := fun p hp =>
        mem_Icc.mpr ⟨(hP p hp).two_le, by have := mem_range.mp (mem_filter.mp hp).1; omega⟩
      have h1 : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤
          ∑ n ∈ Icc 2 x, ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hP_sub (fun _ _ _ => by positivity)
      rw [htele x hx] at h1
      have hnn : (0 : ℝ) ≤ (x : ℝ)⁻¹ := by positivity
      linarith
    have hsum_le : ∑ p ∈ P, (p : ℝ)⁻¹ + 3 * ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤
        Real.log (Real.log (x : ℝ)) + 13 := by
      linarith [mertens_second_upper hx]
    calc
      ∏ p ∈ P, (1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2))
          ≤ Real.exp (Real.log (Real.log (x : ℝ)) + 13) :=
        hexp_prod.trans (Real.exp_le_exp.mpr hsum_le)
      _ = Real.exp 13 * Real.log (x : ℝ) := by
        rw [Real.exp_add, Real.exp_log hlogx_pos, mul_comm]
  -- Combine all four steps.
  calc
    ∑ M ∈ range Q,
        (∑ d ∈ S_D,
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ R d,
              Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * K d r) ^ 2
        ≤ ∑ M ∈ range Q, ‖Z M‖ ^ 2 := hsq_le_norm
    _ = (Q : ℝ) * ∑ d ∈ S_D, ∑ r ∈ R d, (coeff d r) ^ 2 := hparseval_r
    _ ≤ (Q : ℝ) * ((L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hdiag_le (Nat.cast_nonneg Q)
    _ = (Q : ℝ) * ((L : ℝ) * ∏ p ∈ P, (1 + (p : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2))) := by
        rw [hdiv_sum]
    _ ≤ (Q : ℝ) * ((L : ℝ) * (Real.exp 13 * Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg L)) (Nat.cast_nonneg Q)
    _ = Real.exp 13 * (Q : ℝ) * (L : ℝ) * Real.log (x : ℝ) := by ring
