import FormalConjectures.Wikipedia.RiemannZetaValues
import Mathlib.NumberTheory.Primorial

-- Problem: Particular values of the Riemann zeta function — infinite irrational at odd
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RiemannZetaValues.lean:91 (declaration RiemannZetaValues.infinite_irrational_at_odd)
-- Credit: @skhakim
-- Elementary Ball-Rivoal proof (no PNT, no Stirling, no Cauchy integrals).

/-!
Elementary Ball-Rivoal proof that infinitely many odd zeta values are irrational.
-/

namespace BallRivoalProof

open scoped BigOperators

/- Section 1: Elementary common denominator bound and factorial bounds -/

def commonDenom (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ (Nat.log p n)

lemma commonDenom_pos (n : ℕ) : 0 < commonDenom n := by
  unfold commonDenom
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Finset.mem_filter.mp hp).2.pos _

lemma dvd_commonDenom {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ commonDenom n := by
  have hk0 : k ≠ 0 := by omega
  have hD0 : commonDenom n ≠ 0 := (commonDenom_pos n).ne'
  rw [← Nat.factorization_le_iff_dvd hk0 hD0]
  intro p
  by_cases hp : p.Prime
  · by_cases hpe : k.factorization p = 0
    · simp [hpe]
    · have hpow_dvd : p ^ (k.factorization p) ∣ k := Nat.ordProj_dvd k p
      have hpow_le : p ^ (k.factorization p) ≤ k := Nat.le_of_dvd (by omega) hpow_dvd
      have hpow_le_n : p ^ (k.factorization p) ≤ n := le_trans hpow_le hkn
      have hp_le_n : p ≤ n := by
        have h1 : 1 ≤ k.factorization p := Nat.pos_of_ne_zero hpe
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (k.factorization p) := Nat.pow_le_pow_right hp.pos h1
          _ ≤ n := hpow_le_n
      have hlog : k.factorization p ≤ Nat.log p n :=
        Nat.le_log_of_pow_le hp.one_lt hpow_le_n
      have hmem : p ∈ (Finset.range (n + 1)).filter Nat.Prime := by
        simp [Finset.mem_filter, Finset.mem_range, hp, Nat.lt_succ_of_le hp_le_n]
      have hdvd_term : p ^ (k.factorization p) ∣ p ^ (Nat.log p n) :=
        Nat.pow_dvd_pow p hlog
      have hdvd_D : p ^ (k.factorization p) ∣ commonDenom n :=
        dvd_trans hdvd_term (Finset.dvd_prod_of_mem _ hmem)
      exact (hp.pow_dvd_iff_le_factorization hD0).mp hdvd_D
  · rw [Nat.factorization_eq_zero_of_not_prime k hp]
    exact Nat.zero_le _

lemma sq_succ_le_eight_pow (s : ℕ) (hs : 1 ≤ s) : (s + 1) ^ 2 ≤ 8 ^ s := by
  induction s with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => norm_num
    | succ k =>
      have hk : 1 ≤ k + 1 := by omega
      have hih := ih hk
      have hstep : (k + 1 + 1 + 1) ^ 2 ≤ 8 * (k + 1 + 1) ^ 2 := by nlinarith
      calc (k + 1 + 1 + 1) ^ 2 ≤ 8 * (k + 1 + 1) ^ 2 := hstep
        _ ≤ 8 * 8 ^ (k + 1) := Nat.mul_le_mul_left 8 hih
        _ = 8 ^ (k + 1 + 1) := by ring

lemma nat_pow_sqrt_le_eight_pow (n : ℕ) : n ^ Nat.sqrt n ≤ 8 ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · set s := Nat.sqrt n
    have hs1 : 1 ≤ s := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
    have hns : n ≤ (s + 1) ^ 2 := le_of_lt (by simpa [sq] using Nat.lt_succ_sqrt n)
    have h1 : n ≤ 8 ^ s := le_trans hns (sq_succ_le_eight_pow s hs1)
    have h2 : n ^ s ≤ (8 ^ s) ^ s := Nat.pow_le_pow_left h1 s
    have h3 : (8 ^ s) ^ s = 8 ^ (s * s) := (pow_mul 8 s s).symm
    have h4 : s * s ≤ n := Nat.sqrt_le n
    exact le_trans h2 (h3 ▸ Nat.pow_le_pow_right (by norm_num) h4)

lemma commonDenom_le_pow (n : ℕ) : commonDenom n ≤ 32 ^ n := by
  by_cases hn : n = 0
  · simp [commonDenom, hn]
  · unfold commonDenom
    set S := (Finset.range (n + 1)).filter Nat.Prime
    rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Nat.sqrt n)]
    have hleft : ∏ p ∈ S.filter (fun p => p ≤ Nat.sqrt n), p ^ Nat.log p n ≤ 8 ^ n := by
      have h1 : ∏ p ∈ S.filter (fun p => p ≤ Nat.sqrt n), p ^ Nat.log p n ≤
          ∏ _p ∈ S.filter (fun p => p ≤ Nat.sqrt n), n := by
        apply Finset.prod_le_prod'
        intro p _
        exact Nat.pow_log_le_self p hn
      rw [Finset.prod_const] at h1
      have hcard : (S.filter (fun p => p ≤ Nat.sqrt n)).card ≤ Nat.sqrt n := by
        have hsub : S.filter (fun p => p ≤ Nat.sqrt n) ⊆ Finset.Icc 1 (Nat.sqrt n) := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc, S] at hp ⊢
          exact ⟨hp.1.2.one_lt.le, hp.2⟩
        calc (S.filter (fun p => p ≤ Nat.sqrt n)).card
            ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card hsub
          _ = Nat.sqrt n := by simp
      calc ∏ p ∈ S.filter (fun p => p ≤ Nat.sqrt n), p ^ Nat.log p n
          ≤ n ^ (S.filter (fun p => p ≤ Nat.sqrt n)).card := h1
        _ ≤ n ^ Nat.sqrt n := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hcard
        _ ≤ 8 ^ n := nat_pow_sqrt_le_eight_pow n
    have hright : ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p ^ Nat.log p n ≤ 4 ^ n := by
      have h1 : ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p ^ Nat.log p n ≤
          ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p := by
        apply Finset.prod_le_prod'
        intro p hp
        simp only [Finset.mem_filter, not_le, S] at hp
        have hlt : n < p ^ 2 := Nat.sqrt_lt'.mp hp.2
        have hlog_lt : Nat.log p n < 2 := Nat.log_lt_of_lt_pow hn hlt
        have hlog_le : Nat.log p n ≤ 1 := by omega
        calc p ^ Nat.log p n ≤ p ^ 1 := Nat.pow_le_pow_right hp.1.2.pos hlog_le
          _ = p := pow_one p
      have h2 : ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p ≤ ∏ p ∈ S, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ S)
        intro p hp _
        exact (Finset.mem_filter.mp hp).2.pos
      have h3 : ∏ p ∈ S, p = primorial n := rfl
      exact le_trans h1 (le_trans h2 (h3 ▸ primorial_le_four_pow n))
    calc (∏ p ∈ S.filter (fun p => p ≤ Nat.sqrt n), p ^ Nat.log p n) *
          (∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p ^ Nat.log p n)
        ≤ 8 ^ n * 4 ^ n := Nat.mul_le_mul hleft hright
      _ = 32 ^ n := by rw [← mul_pow]; norm_num

lemma factorial_le_pow_self (n : ℕ) : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hm : (m : ℝ) ^ m ≤ ((m + 1 : ℕ) : ℝ) ^ m := by
      gcongr; exact_mod_cast Nat.le_succ m
    calc ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)
        ≤ ((m + 1 : ℕ) : ℝ) * (m : ℝ) ^ m := by gcongr
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ m := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by rw [pow_succ']

lemma pow_le_three_pow_mul_factorial (n : ℕ) : (n : ℝ) ^ n ≤ 3 ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => norm_num
    | succ k =>
      set m := k + 1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      have h1 : (1 + 1 / (m : ℝ)) ^ m ≤ 3 := by
        have hstep : 1 + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
          linarith [Real.add_one_le_exp (1 / (m : ℝ))]
        have hpow : (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / (m : ℝ))) ^ m :=
          pow_le_pow_left₀ (by positivity) hstep m
        rw [← Real.exp_nat_mul] at hpow
        have hmul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
        rw [hmul] at hpow
        linarith [Real.exp_one_lt_d9]
      have h2 : ((m + 1 : ℕ) : ℝ) ^ m ≤ 3 * (m : ℝ) ^ m := by
        have hEq : ((m + 1 : ℕ) : ℝ) = (m : ℝ) * (1 + 1 / (m : ℝ)) := by
          push_cast; field_simp
        rw [hEq, mul_pow]
        nlinarith [pow_nonneg hm_pos.le m]
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ', pow_succ]
      calc ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ m
          ≤ ((m + 1 : ℕ) : ℝ) * (3 * (m : ℝ) ^ m) := by gcongr
        _ ≤ ((m + 1 : ℕ) : ℝ) * (3 * (3 ^ m * (m.factorial : ℝ))) := by gcongr
        _ = 3 ^ m * 3 * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) := by ring

/- Section 2: Partial fraction algebra, integrality, and bounds -/

def evalPF (p n : ℕ) (c : ℕ → ℕ → ℚ) (t : ℚ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1), c j k / (t + (k : ℚ)) ^ j

lemma pf_split_single {t a b : ℚ} (hab : a ≠ b) (hta : t + a ≠ 0) (htb : t + b ≠ 0) :
    ∀ j : ℕ, 1 ≤ j →
      1 / ((t + a) ^ j * (t + b)) =
        (-1 : ℚ) ^ j / ((b - a) ^ j * (t + b)) +
        ∑ m ∈ Finset.Icc 1 j, (-1 : ℚ) ^ (j - m) / ((b - a) ^ (j + 1 - m) * (t + a) ^ m) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  intro j hj
  induction j with
  | zero => omega
  | succ j' ih =>
    cases j' with
    | zero =>
      simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, Nat.sub_self, pow_zero]
      field_simp [hba, hta, htb]
      ring
    | succ k =>
      have hk : 1 ≤ k + 1 := by omega
      have hih := ih hk
      have hstep : 1 / ((t + a) ^ (k + 1 + 1) * (t + b)) =
          (1 / (t + a)) * (1 / ((t + a) ^ (k + 1) * (t + b))) := by
        rw [pow_succ]; field_simp [hta, htb]
      rw [hstep, hih, mul_add]
      have hbase : (1 / (t + a)) * ((-1 : ℚ) ^ (k + 1) / ((b - a) ^ (k + 1) * (t + b))) =
          (-1 : ℚ) ^ (k + 1 + 1) / ((b - a) ^ (k + 1 + 1) * (t + b)) +
          (-1 : ℚ) ^ (k + 1) / ((b - a) ^ (k + 1 + 1) * (t + a)) := by
        have hba_pow : (b - a) ^ (k + 1) ≠ 0 := pow_ne_zero _ hba
        rw [pow_succ (-1 : ℚ), pow_succ (b - a)]
        field_simp [hba, hba_pow, hta, htb]
        ring
      rw [hbase, add_assoc]
      congr 1
      rw [Finset.mul_sum]
      have hsplit : Finset.Icc 1 (k + 1 + 1) =
          insert 1 (Finset.Icc 2 (k + 1 + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      congr 1
      · simp [pow_one]
      · refine Finset.sum_bij (fun m _ => m + 1) ?_ ?_ ?_ ?_
        · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
        · intro m1 _ m2 _ h; omega
        · intro m hm; simp only [Finset.mem_Icc] at hm
          exact ⟨m - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
        · intro m hm
          simp only [Finset.mem_Icc] at hm
          have he1 : k + 1 + 1 - (m + 1) = k + 1 - m := by omega
          have he2 : k + 1 + 1 + 1 - (m + 1) = k + 1 + 1 - m := by omega
          rw [he1, he2, pow_succ (t + a) m]
          field_simp [hta]

def mulPF (p n : ℕ) (u : ℕ → ℕ → ℚ) (v : ℕ → ℚ) (m k : ℕ) : ℚ :=
  if m = p + 1 then u p k * v k
  else if m = 1 then
    (∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc 1 p,
      u j k * v l * (-1 : ℚ) ^ (j - 1) / ((l : ℚ) - (k : ℚ)) ^ j) +
    (∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc 1 p,
      u j l * v k * (-1 : ℚ) ^ j / ((k : ℚ) - (l : ℚ)) ^ j)
  else if 2 ≤ m ∧ m ≤ p then
    u (m - 1) k * v k +
    ∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc m p,
      u j k * v l * (-1 : ℚ) ^ (j - m) / ((l : ℚ) - (k : ℚ)) ^ (j + 1 - m)
  else 0

lemma evalPF_mulPF {p n : ℕ} (hp : 1 ≤ p) (u : ℕ → ℕ → ℚ) (v : ℕ → ℚ) {t : ℚ}
    (ht : ∀ k ∈ Finset.range (n + 1), t + (k : ℚ) ≠ 0) :
    evalPF (p + 1) n (mulPF p n u v) t =
      evalPF p n u t * ∑ l ∈ Finset.range (n + 1), v l / (t + (l : ℚ)) := by
  -- Expand RHS into diagonal (l = k) and off-diagonal (l ≠ k)
  unfold evalPF
  rw [Finset.sum_mul]
  have hRHS :
      ∑ j ∈ Finset.Icc 1 p, (∑ k ∈ Finset.range (n + 1), u j k / (t + (k : ℚ)) ^ j) *
        (∑ l ∈ Finset.range (n + 1), v l / (t + (l : ℚ))) =
      (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        u j k * v k / (t + (k : ℚ)) ^ (j + 1)) +
      (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ((-1 : ℚ) ^ j / (((l : ℚ) - (k : ℚ)) ^ j * (t + (l : ℚ))) +
            ∑ m ∈ Finset.Icc 1 j,
              (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hk]
    congr 1
    · rw [pow_succ, div_mul_div_comm]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      have hklq : (k : ℚ) ≠ (l : ℚ) := by exact_mod_cast hlk.symm
      have h1 := pf_split_single hklq (ht k hk) (ht l (Finset.mem_of_mem_erase hl)) j
        (Finset.mem_Icc.mp hj).1
      have h2 : u j k / (t + (k : ℚ)) ^ j * (v l / (t + (l : ℚ))) =
          u j k * v l * (1 / ((t + (k : ℚ)) ^ j * (t + (l : ℚ)))) := by
        rw [div_mul_div_comm, mul_one_div]
      rw [h2, h1]
  rw [hRHS]
  -- Now split LHS over m = 1, 2 ≤ m ≤ p, m = p + 1
  have hIcc_split : Finset.Icc 1 (p + 1) =
      insert (p + 1) (insert 1 (Finset.Icc 2 p)) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc_split, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  -- Simplify each piece on LHS
  have htop : ∑ k ∈ Finset.range (n + 1), mulPF p n u v (p + 1) k / (t + (k : ℚ)) ^ (p + 1) =
      ∑ k ∈ Finset.range (n + 1), u p k * v k / (t + (k : ℚ)) ^ (p + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mulPF]
  have hmid : ∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
      mulPF p n u v m k / (t + (k : ℚ)) ^ m =
      (∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
        u (m - 1) k * v k / (t + (k : ℚ)) ^ m) +
      (∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc m p,
          u j k * v l * (-1 : ℚ) ^ (j - m) /
            (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm2 : 2 ≤ m ∧ m ≤ p := Finset.mem_Icc.mp hm
    have hmp : m ≠ p + 1 := by omega
    have hm1 : m ≠ 1 := by omega
    simp only [mulPF, hmp, hm1, hm2, and_self, ↓reduceIte, add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbot : ∑ k ∈ Finset.range (n + 1), mulPF p n u v 1 k / (t + (k : ℚ)) ^ 1 =
      (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
        ∑ j ∈ Finset.Icc 1 p,
          u j k * v l * (-1 : ℚ) ^ (j - 1) / (((l : ℚ) - (k : ℚ)) ^ j * (t + (k : ℚ)))) +
      (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
        ∑ j ∈ Finset.Icc 1 p,
          u j l * v k * (-1 : ℚ) ^ j / (((k : ℚ) - (l : ℚ)) ^ j * (t + (k : ℚ)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1p : (1 : ℕ) ≠ p + 1 := by omega
    simp only [mulPF, h1p, ↓reduceIte, pow_one, add_div, Finset.sum_div]
    congr 1 <;> refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by
      rw [div_div]
  rw [htop, hmid, hbot]
  -- Match diagonal terms: top + mid_diag = RHS_diag
  have hdiag :
      (∑ k ∈ Finset.range (n + 1), u p k * v k / (t + (k : ℚ)) ^ (p + 1)) +
      (∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
        u (m - 1) k * v k / (t + (k : ℚ)) ^ m) =
      ∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        u j k * v k / (t + (k : ℚ)) ^ (j + 1) := by
    have h1 : Finset.Icc 1 p = insert p (Finset.Icc 1 (p - 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp; omega)]
    congr 1
    refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
    · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_Icc] at hm1 hm2; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj
      exact ⟨j + 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have hm' : m - 1 + 1 = m := by omega
      rw [hm']
  -- Match the second part of hbot with the (t + l)⁻1 part of RHS
  have hswap_l :
      (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
        ∑ j ∈ Finset.Icc 1 p,
          u j l * v k * (-1 : ℚ) ^ j / (((k : ℚ) - (l : ℚ)) ^ j * (t + (k : ℚ)))) =
      ∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ((-1 : ℚ) ^ j / (((l : ℚ) - (k : ℚ)) ^ j * (t + (l : ℚ)))) := by
    -- Swap j to the outside, then swap (k, l)
    trans (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j l * v k * (-1 : ℚ) ^ j / (((k : ℚ) - (l : ℚ)) ^ j * (t + (k : ℚ))))
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
    · refine Finset.sum_congr rfl fun j _ => ?_
      -- Rewrite erase as filter and swap k, l
      have hfilt : ∀ f : ℕ → ℕ → ℚ,
          (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k, f k l) =
          ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), if l = k then 0 else f k l := by
        intro f
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← Finset.sum_erase_add _ _ hk]
        simp only [↓reduceIte, add_zero]
        refine Finset.sum_congr rfl fun l hl => ?_
        simp [(Finset.mem_erase.mp hl).1]
      rw [hfilt, hfilt, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases h : k = l
      · subst h; simp
      · have h' : l ≠ k := Ne.symm h
        simp only [h, h', ↓reduceIte]
        ring
  -- Match the (t + k)⁻m terms (m = 1 from hbot + 2 ≤ m ≤ p from hmid) with RHS
  have hswap_m :
      (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
        ∑ j ∈ Finset.Icc 1 p,
          u j k * v l * (-1 : ℚ) ^ (j - 1) / (((l : ℚ) - (k : ℚ)) ^ j * (t + (k : ℚ)))) +
      (∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc m p,
          u j k * v l * (-1 : ℚ) ^ (j - m) /
            (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m)) =
      ∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ∑ m ∈ Finset.Icc 1 j,
            (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m) := by
    have hcombine :
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
          ∑ j ∈ Finset.Icc 1 p,
            u j k * v l * (-1 : ℚ) ^ (j - 1) / (((l : ℚ) - (k : ℚ)) ^ j * (t + (k : ℚ)))) +
        (∑ m ∈ Finset.Icc 2 p, ∑ k ∈ Finset.range (n + 1),
          ∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc m p,
            u j k * v l * (-1 : ℚ) ^ (j - m) /
              (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m)) =
        ∑ m ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
          ∑ l ∈ (Finset.range (n + 1)).erase k, ∑ j ∈ Finset.Icc m p,
            u j k * v l * (-1 : ℚ) ^ (j - m) /
              (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m) := by
      have hsplit : Finset.Icc 1 p = insert 1 (Finset.Icc 2 p) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      conv_rhs => rw [hsplit, Finset.sum_insert (by simp)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => ?_
      simp [pow_one]
    rw [hcombine]
    -- Bring k, l outside and swap m, j
    trans (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
      ∑ m ∈ Finset.Icc 1 p, ∑ j ∈ Finset.Icc m p,
        u j k * v l * (-1 : ℚ) ^ (j - m) /
          (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m))
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
    · trans (∑ k ∈ Finset.range (n + 1), ∑ l ∈ (Finset.range (n + 1)).erase k,
        ∑ j ∈ Finset.Icc 1 p,
          u j k * v l * ∑ m ∈ Finset.Icc 1 j,
            (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m))
      · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        have htri : ∀ f : ℕ → ℕ → ℚ,
            (∑ m ∈ Finset.Icc 1 p, ∑ j ∈ Finset.Icc m p, f m j) =
            ∑ j ∈ Finset.Icc 1 p, ∑ m ∈ Finset.Icc 1 j, f m j := by
          intro f
          have h1 : ∀ m ∈ Finset.Icc 1 p,
              ∑ j ∈ Finset.Icc m p, f m j =
              ∑ j ∈ Finset.Icc 1 p, if m ≤ j then f m j else 0 := by
            intro m hm
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext j; simp only [Finset.mem_Icc, Finset.mem_filter]
            have := Finset.mem_Icc.mp hm; omega
          have h2 : ∀ j ∈ Finset.Icc 1 p,
              ∑ m ∈ Finset.Icc 1 j, f m j =
              ∑ m ∈ Finset.Icc 1 p, if m ≤ j then f m j else 0 := by
            intro j hj
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext m; simp only [Finset.mem_Icc, Finset.mem_filter]
            have := Finset.mem_Icc.mp hj; omega
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          exact Finset.sum_congr rfl fun j hj => (h2 j hj).symm
        rw [htri]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by rw [mul_div_assoc]
      · trans (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 p,
            ∑ l ∈ (Finset.range (n + 1)).erase k,
              u j k * v l * ∑ m ∈ Finset.Icc 1 j,
                (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m))
        · refine Finset.sum_congr rfl fun k _ => Finset.sum_comm
        · exact Finset.sum_comm
  -- Combine all parts!
  have hRHS_split :
      (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ((-1 : ℚ) ^ j / (((l : ℚ) - (k : ℚ)) ^ j * (t + (l : ℚ))) +
            ∑ m ∈ Finset.Icc 1 j,
              (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m))) =
      (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ((-1 : ℚ) ^ j / (((l : ℚ) - (k : ℚ)) ^ j * (t + (l : ℚ))))) +
      (∑ j ∈ Finset.Icc 1 p, ∑ k ∈ Finset.range (n + 1),
        ∑ l ∈ (Finset.range (n + 1)).erase k,
          u j k * v l * ∑ m ∈ Finset.Icc 1 j,
            (-1 : ℚ) ^ (j - m) / (((l : ℚ) - (k : ℚ)) ^ (j + 1 - m) * (t + (k : ℚ)) ^ m)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hRHS_split, ← hdiag, ← hswap_l, ← hswap_m]
  ring

lemma rat_div_sub_int_mul_commonDenom {n l k : ℕ} (hl : l ≤ n) (hk : k ≤ n) (hlk : l ≠ k) :
    ∃ z : ℤ, (commonDenom n : ℚ) / ((l : ℚ) - (k : ℚ)) = (z : ℚ) := by
  by_cases h : k < l
  · have hdvd : (l - k) ∣ commonDenom n := dvd_commonDenom (by omega) (by omega)
    rcases hdvd with ⟨q, hq⟩
    refine ⟨(q : ℤ), ?_⟩
    have hsub : (l : ℚ) - (k : ℚ) = ((l - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub h.le]
    have hne : ((l - k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show l - k ≠ 0 by omega)
    rw [hsub, div_eq_iff hne]
    exact_mod_cast hq.trans (mul_comm _ _)
  · have h' : l < k := by omega
    have hdvd : (k - l) ∣ commonDenom n := dvd_commonDenom (by omega) (by omega)
    rcases hdvd with ⟨q, hq⟩
    refine ⟨-(q : ℤ), ?_⟩
    have hsub : (l : ℚ) - (k : ℚ) = -((k - l : ℕ) : ℚ) := by
      rw [Nat.cast_sub h'.le]; ring
    have hne : -((k - l : ℕ) : ℚ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (show k - l ≠ 0 by omega))
    rw [hsub, div_eq_iff hne]
    push_cast
    have hq' : (commonDenom n : ℚ) = (q : ℚ) * ((k - l : ℕ) : ℚ) := by
      exact_mod_cast hq.trans (mul_comm _ _)
    linarith

lemma exists_int_add {x y : ℚ} (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z) :
    ∃ z : ℤ, x + y = z := by
  rcases hx with ⟨a, rfl⟩; rcases hy with ⟨b, rfl⟩; exact ⟨a + b, by push_cast; rfl⟩

lemma exists_int_mul {x y : ℚ} (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z) :
    ∃ z : ℤ, x * y = z := by
  rcases hx with ⟨a, rfl⟩; rcases hy with ⟨b, rfl⟩; exact ⟨a * b, by push_cast; rfl⟩

lemma exists_int_pow {x : ℚ} (hx : ∃ z : ℤ, x = z) (e : ℕ) :
    ∃ z : ℤ, x ^ e = z := by
  rcases hx with ⟨a, rfl⟩; exact ⟨a ^ e, by push_cast; rfl⟩

lemma exists_int_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ∃ z : ℤ, f i = z) : ∃ z : ℤ, ∑ i ∈ s, f i = z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact exists_int_add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma mulPF_int {p n : ℕ} (hp : 1 ≤ p) (u : ℕ → ℕ → ℚ) (v : ℕ → ℚ)
    (hu : ∀ j ∈ Finset.Icc 1 p, ∀ k ≤ n, ∃ z : ℤ, (commonDenom n : ℚ) ^ (p - j) * u j k = z)
    (hv : ∀ l ≤ n, ∃ z : ℤ, v l = z) :
    ∀ m ∈ Finset.Icc 1 (p + 1), ∀ k ≤ n,
      ∃ z : ℤ, (commonDenom n : ℚ) ^ (p + 1 - m) * mulPF p n u v m k = z := by
  intro m hm k hk
  simp only [Finset.mem_Icc] at hm
  unfold mulPF
  split_ifs with h1 h2 h3
  · subst h1
    simp only [Nat.sub_self, pow_zero, one_mul]
    have hup := hu p (by simp; omega) k hk
    simp only [Nat.sub_self, pow_zero, one_mul] at hup
    exact exists_int_mul hup (hv k hk)
  · subst h2
    rw [mul_add]
    apply exists_int_add
    · rw [Finset.mul_sum]
      apply exists_int_sum
      intro l hl
      have hl_le : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      rw [Finset.mul_sum]
      apply exists_int_sum
      intro j hj
      have hj_le : j ≤ p := (Finset.mem_Icc.mp hj).2
      have hsplit : (commonDenom n : ℚ) ^ (p + 1 - 1) *
          (u j k * v l * (-1 : ℚ) ^ (j - 1) / ((l : ℚ) - (k : ℚ)) ^ j) =
          ((commonDenom n : ℚ) ^ (p - j) * u j k) * v l * (-1 : ℚ) ^ (j - 1) *
            ((commonDenom n : ℚ) / ((l : ℚ) - (k : ℚ))) ^ j := by
        have hpj : p + 1 - 1 = (p - j) + j := by omega
        rw [hpj, pow_add, div_pow]; ring
      rw [hsplit]
      exact exists_int_mul (exists_int_mul (exists_int_mul (hu j hj k hk) (hv l hl_le))
        ⟨(-1 : ℤ) ^ (j - 1), by push_cast; rfl⟩)
        (exists_int_pow (rat_div_sub_int_mul_commonDenom hl_le hk hlk) j)
    · rw [Finset.mul_sum]
      apply exists_int_sum
      intro l hl
      have hl_le : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      rw [Finset.mul_sum]
      apply exists_int_sum
      intro j hj
      have hj_le : j ≤ p := (Finset.mem_Icc.mp hj).2
      have hsplit : (commonDenom n : ℚ) ^ (p + 1 - 1) *
          (u j l * v k * (-1 : ℚ) ^ j / ((k : ℚ) - (l : ℚ)) ^ j) =
          ((commonDenom n : ℚ) ^ (p - j) * u j l) * v k * (-1 : ℚ) ^ j *
            ((commonDenom n : ℚ) / ((k : ℚ) - (l : ℚ))) ^ j := by
        have hpj : p + 1 - 1 = (p - j) + j := by omega
        rw [hpj, pow_add, div_pow]; ring
      rw [hsplit]
      exact exists_int_mul (exists_int_mul (exists_int_mul (hu j hj l hl_le) (hv k hk))
        ⟨(-1 : ℤ) ^ j, by push_cast; rfl⟩)
        (exists_int_pow (rat_div_sub_int_mul_commonDenom hk hl_le hlk.symm) j)
  · rw [mul_add]
    apply exists_int_add
    · have hpow : p + 1 - m = p - (m - 1) := by omega
      rw [hpow, ← mul_assoc]
      exact exists_int_mul (hu (m - 1) (by simp only [Finset.mem_Icc]; omega) k hk) (hv k hk)
    · rw [Finset.mul_sum]
      apply exists_int_sum
      intro l hl
      have hl_le : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      rw [Finset.mul_sum]
      apply exists_int_sum
      intro j hj
      have hj_mem : j ∈ Finset.Icc 1 p := by
        simp only [Finset.mem_Icc] at hj ⊢; omega
      have hsplit : (commonDenom n : ℚ) ^ (p + 1 - m) *
          (u j k * v l * (-1 : ℚ) ^ (j - m) / ((l : ℚ) - (k : ℚ)) ^ (j + 1 - m)) =
          ((commonDenom n : ℚ) ^ (p - j) * u j k) * v l * (-1 : ℚ) ^ (j - m) *
            ((commonDenom n : ℚ) / ((l : ℚ) - (k : ℚ))) ^ (j + 1 - m) := by
        have hjm := Finset.mem_Icc.mp hj
        have hpj : p + 1 - m = (p - j) + (j + 1 - m) := by omega
        rw [hpj, pow_add, div_pow]; ring
      rw [hsplit]
      exact exists_int_mul (exists_int_mul (exists_int_mul (hu j hj_mem k hk) (hv l hl_le))
        ⟨(-1 : ℤ) ^ (j - m), by push_cast; rfl⟩)
        (exists_int_pow (rat_div_sub_int_mul_commonDenom hl_le hk hlk) (j + 1 - m))
  · omega

lemma one_le_abs_nat_sub_rat {l k : ℕ} (hlk : l ≠ k) : (1 : ℚ) ≤ |(l : ℚ) - (k : ℚ)| := by
  by_cases h : k < l
  · rw [abs_of_pos (by exact_mod_cast (show (k : ℚ) < l by exact_mod_cast h) |> sub_pos.mpr)]
    have : (1 : ℕ) + k ≤ l := by omega
    have : (1 : ℚ) + (k : ℚ) ≤ (l : ℚ) := by exact_mod_cast this
    linarith
  · have h' : l < k := by omega
    rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast h'))]
    have : (1 : ℕ) + l ≤ k := by omega
    have : (1 : ℚ) + (l : ℚ) ≤ (k : ℚ) := by exact_mod_cast this
    linarith

lemma mulPF_bound {p n : ℕ} (hp : 1 ≤ p) (u : ℕ → ℕ → ℚ) (v : ℕ → ℚ) {M V : ℚ}
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hu : ∀ j ∈ Finset.Icc 1 p, ∀ k ≤ n, |u j k| ≤ M)
    (hv : ∀ l ≤ n, |v l| ≤ V) :
    ∀ m ∈ Finset.Icc 1 (p + 1), ∀ k ≤ n,
      |mulPF p n u v m k| ≤ (2 * (p : ℚ) * ((n : ℚ) + 1)) * (M * V) := by
  intro m hm k hk
  simp only [Finset.mem_Icc] at hm
  have hMV : 0 ≤ M * V := mul_nonneg hM hV
  have hcard_erase : (((Finset.range (n + 1)).erase k).card : ℚ) ≤ (n : ℚ) := by
    have hk_mem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    rw [Finset.card_erase_of_mem hk_mem, Finset.card_range]
    simp
  have hterm_le : ∀ {j a b e : ℕ}, j ∈ Finset.Icc 1 p → a ≤ n → b ≤ n → a ≠ b →
      |u j a * v b * (-1 : ℚ) ^ e / ((b : ℚ) - (a : ℚ)) ^ (e + 1)| ≤ M * V := by
    intro j a b e hj ha hb hab
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow]
    have hden : (1 : ℚ) ≤ |(b : ℚ) - (a : ℚ)| ^ (e + 1) :=
      one_le_pow₀ (one_le_abs_nat_sub_rat hab.symm)
    calc |u j a| * |v b| / |(b : ℚ) - (a : ℚ)| ^ (e + 1)
        ≤ |u j a| * |v b| / 1 := div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          zero_lt_one hden
      _ = |u j a| * |v b| := div_one _
      _ ≤ M * V := mul_le_mul (hu j hj a ha) (hv b hb) (abs_nonneg _) hM
  unfold mulPF
  split_ifs with h1 h2 h3
  · rw [abs_mul]
    have hup : |u p k| ≤ M := hu p (by simp; omega) k hk
    have hbase : |u p k| * |v k| ≤ M * V := mul_le_mul hup (hv k hk) (abs_nonneg _) hM
    have hfac : (1 : ℚ) ≤ 2 * (p : ℚ) * ((n : ℚ) + 1) := by
      have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
      have hn1 : (1 : ℚ) ≤ (n : ℚ) + 1 := by linarith [Nat.cast_nonneg (α := ℚ) n]
      nlinarith
    nlinarith
  · calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ (n : ℚ) * ((p : ℚ) * (M * V)) + (n : ℚ) * ((p : ℚ) * (M * V)) := by
        apply add_le_add
        · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          calc ∑ l ∈ (Finset.range (n + 1)).erase k,
                |∑ j ∈ Finset.Icc 1 p, u j k * v l * (-1 : ℚ) ^ (j - 1) / ((l : ℚ) - (k : ℚ)) ^ j|
              ≤ ∑ _l ∈ (Finset.range (n + 1)).erase k, (p : ℚ) * (M * V) := by
                refine Finset.sum_le_sum fun l hl => ?_
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                calc ∑ j ∈ Finset.Icc 1 p,
                      |u j k * v l * (-1 : ℚ) ^ (j - 1) / ((l : ℚ) - (k : ℚ)) ^ j|
                    ≤ ∑ _j ∈ Finset.Icc 1 p, (M * V) := by
                      refine Finset.sum_le_sum fun j hj => ?_
                      have hl_le : l ≤ n :=
                        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
                      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
                      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
                      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow]
                      have hden : (1 : ℚ) ≤ |(l : ℚ) - (k : ℚ)| ^ j :=
                        one_le_pow₀ (one_le_abs_nat_sub_rat hlk)
                      calc |u j k| * |v l| / |(l : ℚ) - (k : ℚ)| ^ j
                          ≤ |u j k| * |v l| / 1 := div_le_div_of_nonneg_left
                            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_lt_one hden
                        _ = |u j k| * |v l| := div_one _
                        _ ≤ M * V := mul_le_mul (hu j hj k hk) (hv l hl_le) (abs_nonneg _) hM
                  _ = (p : ℚ) * (M * V) := by
                      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                      have : ((p + 1 - 1 : ℕ) : ℚ) = (p : ℚ) := by simp
                      rw [this]
            _ = (((Finset.range (n + 1)).erase k).card : ℚ) * ((p : ℚ) * (M * V)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (n : ℚ) * ((p : ℚ) * (M * V)) :=
                mul_le_mul_of_nonneg_right hcard_erase (by positivity)
        · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          calc ∑ l ∈ (Finset.range (n + 1)).erase k,
                |∑ j ∈ Finset.Icc 1 p, u j l * v k * (-1 : ℚ) ^ j / ((k : ℚ) - (l : ℚ)) ^ j|
              ≤ ∑ _l ∈ (Finset.range (n + 1)).erase k, (p : ℚ) * (M * V) := by
                refine Finset.sum_le_sum fun l hl => ?_
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                calc ∑ j ∈ Finset.Icc 1 p,
                      |u j l * v k * (-1 : ℚ) ^ j / ((k : ℚ) - (l : ℚ)) ^ j|
                    ≤ ∑ _j ∈ Finset.Icc 1 p, (M * V) := by
                      refine Finset.sum_le_sum fun j hj => ?_
                      have hl_le : l ≤ n :=
                        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
                      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
                      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow]
                      have hden : (1 : ℚ) ≤ |(k : ℚ) - (l : ℚ)| ^ j :=
                        one_le_pow₀ (one_le_abs_nat_sub_rat hlk.symm)
                      calc |u j l| * |v k| / |(k : ℚ) - (l : ℚ)| ^ j
                          ≤ |u j l| * |v k| / 1 := div_le_div_of_nonneg_left
                            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_lt_one hden
                        _ = |u j l| * |v k| := div_one _
                        _ ≤ M * V := mul_le_mul (hu j hj l hl_le) (hv k hk) (abs_nonneg _) hM
                  _ = (p : ℚ) * (M * V) := by
                      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                      have : ((p + 1 - 1 : ℕ) : ℚ) = (p : ℚ) := by simp
                      rw [this]
            _ = (((Finset.range (n + 1)).erase k).card : ℚ) * ((p : ℚ) * (M * V)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (n : ℚ) * ((p : ℚ) * (M * V)) :=
                mul_le_mul_of_nonneg_right hcard_erase (by positivity)
      _ ≤ (2 * (p : ℚ) * ((n : ℚ) + 1)) * (M * V) := by
        have hp0 : (0 : ℚ) ≤ (p : ℚ) := by positivity
        nlinarith
  · calc |_ + _| ≤ |u (m - 1) k * v k| + |_| := abs_add_le _ _
      _ ≤ M * V + (n : ℚ) * ((p : ℚ) * (M * V)) := by
        apply add_le_add
        · rw [abs_mul]
          exact mul_le_mul (hu (m - 1) (by simp only [Finset.mem_Icc]; omega) k hk)
            (hv k hk) (abs_nonneg _) hM
        · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          calc ∑ l ∈ (Finset.range (n + 1)).erase k,
                |∑ j ∈ Finset.Icc m p,
                  u j k * v l * (-1 : ℚ) ^ (j - m) / ((l : ℚ) - (k : ℚ)) ^ (j + 1 - m)|
              ≤ ∑ _l ∈ (Finset.range (n + 1)).erase k, (p : ℚ) * (M * V) := by
                refine Finset.sum_le_sum fun l hl => ?_
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                calc ∑ j ∈ Finset.Icc m p,
                      |u j k * v l * (-1 : ℚ) ^ (j - m) / ((l : ℚ) - (k : ℚ)) ^ (j + 1 - m)|
                    ≤ ∑ _j ∈ Finset.Icc m p, (M * V) := by
                      refine Finset.sum_le_sum fun j hj => ?_
                      have hl_le : l ≤ n :=
                        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
                      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
                      have hj_mem : j ∈ Finset.Icc 1 p := by
                        simp only [Finset.mem_Icc] at hj ⊢; omega
                      have hjm := Finset.mem_Icc.mp hj
                      have hje : j + 1 - m = (j - m) + 1 := by omega
                      rw [hje]
                      exact hterm_le hj_mem hk hl_le hlk.symm
                  _ = ((Finset.Icc m p).card : ℚ) * (M * V) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                  _ ≤ (p : ℚ) * (M * V) := by
                      rw [Nat.card_Icc]
                      have hcard_le : ((p + 1 - m : ℕ) : ℚ) ≤ (p : ℚ) := by
                        exact_mod_cast (show p + 1 - m ≤ p by omega)
                      exact mul_le_mul_of_nonneg_right hcard_le hMV
            _ = (((Finset.range (n + 1)).erase k).card : ℚ) * ((p : ℚ) * (M * V)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (n : ℚ) * ((p : ℚ) * (M * V)) :=
                mul_le_mul_of_nonneg_right hcard_erase (by positivity)
      _ ≤ (2 * (p : ℚ) * ((n : ℚ) + 1)) * (M * V) := by
        have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
        have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        have hfac : 1 + (n : ℚ) * (p : ℚ) ≤ 2 * (p : ℚ) * ((n : ℚ) + 1) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hfac hMV]
  · omega

def iterPF (n : ℕ) (v : ℕ → ℕ → ℚ) : ℕ → (ℕ → ℕ → ℚ)
  | 0 => fun _ _ => 0
  | 1 => fun j k => if j = 1 then v 0 k else 0
  | p + 1 => mulPF p n (iterPF n v p) (v p)

lemma evalPF_iterPF {n : ℕ} (v : ℕ → ℕ → ℚ) {t : ℚ}
    (ht : ∀ k ∈ Finset.range (n + 1), t + (k : ℚ) ≠ 0) :
    ∀ p : ℕ, 1 ≤ p →
      evalPF p n (iterPF n v p) t =
        ∏ i ∈ Finset.range p, ∑ k ∈ Finset.range (n + 1), v i k / (t + (k : ℚ)) := by
  intro p hp
  induction p with
  | zero => omega
  | succ p' ih =>
    cases p' with
    | zero =>
      simp [iterPF, evalPF]
    | succ q =>
      have hq : 1 ≤ q + 1 := by omega
      change evalPF (q + 1 + 1) n (mulPF (q + 1) n (iterPF n v (q + 1)) (v (q + 1))) t = _
      rw [evalPF_mulPF hq _ _ ht, ih hq, Finset.prod_range_succ _ (q + 1)]

lemma iterPF_int {n : ℕ} (v : ℕ → ℕ → ℚ) :
    ∀ p : ℕ, 1 ≤ p →
      (∀ i < p, ∀ k ≤ n, ∃ z : ℤ, v i k = z) →
      ∀ j ∈ Finset.Icc 1 p, ∀ k ≤ n,
        ∃ z : ℤ, (commonDenom n : ℚ) ^ (p - j) * iterPF n v p j k = z := by
  intro p hp hv
  induction p with
  | zero => omega
  | succ p' ih =>
    cases p' with
    | zero =>
      intro j hj k hk
      have hj1 : j = 1 := by simp only [Finset.mem_Icc] at hj; omega
      subst hj1
      simpa [iterPF] using hv 0 (by omega) k hk
    | succ q =>
      have hq : 1 ≤ q + 1 := by omega
      exact mulPF_int hq (iterPF n v (q + 1)) (v (q + 1))
        (ih hq fun i hi => hv i (by omega))
        (hv (q + 1) (by omega))

lemma iterPF_bound {n : ℕ} (v : ℕ → ℕ → ℚ) (V : ℕ → ℚ) :
    ∀ p : ℕ, 1 ≤ p →
      (∀ i < p, 0 ≤ V i) →
      (∀ i < p, ∀ k ≤ n, |v i k| ≤ V i) →
      ∀ j ∈ Finset.Icc 1 p, ∀ k ≤ n,
        |iterPF n v p j k| ≤
          (2 * (p : ℚ) * ((n : ℚ) + 1)) ^ p * ∏ i ∈ Finset.range p, V i := by
  intro p hp hV0 hv
  induction p with
  | zero => omega
  | succ p' ih =>
    cases p' with
    | zero =>
      intro j hj k hk
      have hj1 : j = 1 := by simp only [Finset.mem_Icc] at hj; omega
      subst hj1
      have heval : iterPF n v 1 1 k = v 0 k := by simp [iterPF]
      rw [heval, Finset.prod_range_one, pow_one, Nat.cast_one, mul_one]
      have hfac : (1 : ℚ) ≤ 2 * ((n : ℚ) + 1) := by linarith [Nat.cast_nonneg (α := ℚ) n]
      have h0 := hv 0 (by omega) k hk
      have hV0' := hV0 0 (by omega)
      nlinarith
    | succ q =>
      have hq : 1 ≤ q + 1 := by omega
      have hM0 : 0 ≤ (2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ (q + 1) *
          ∏ i ∈ Finset.range (q + 1), V i := by
        apply mul_nonneg
        · positivity
        · exact Finset.prod_nonneg fun i hi => hV0 i (by have := Finset.mem_range.mp hi; omega)
      have hstep := mulPF_bound hq (iterPF n v (q + 1)) (v (q + 1)) hM0 (hV0 (q + 1) (by omega))
        (ih hq (fun i hi => hV0 i (by omega)) (fun i hi => hv i (by omega)))
        (hv (q + 1) (by omega))
      intro j hj k hk
      refine le_trans (hstep j hj k hk) ?_
      rw [Finset.prod_range_succ _ (q + 1)]
      have hprod_nonneg : 0 ≤ (∏ i ∈ Finset.range (q + 1), V i) * V (q + 1) :=
        mul_nonneg (Finset.prod_nonneg fun i hi => hV0 i (by have := Finset.mem_range.mp hi; omega))
          (hV0 (q + 1) (by omega))
      have hbase_le : 2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1) ≤
          2 * ((q + 1 + 1 : ℕ) : ℚ) * ((n : ℚ) + 1) := by
        have hn1 : (0 : ℚ) ≤ (n : ℚ) + 1 := by linarith [Nat.cast_nonneg (α := ℚ) n]
        push_cast; nlinarith
      have hpow_le : (2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ (q + 1 + 1) ≤
          (2 * ((q + 1 + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ (q + 1 + 1) :=
        pow_le_pow_left₀ (by positivity) hbase_le _
      have heq : 2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1) *
          (((2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ (q + 1) *
            ∏ i ∈ Finset.range (q + 1), V i) * V (q + 1)) =
          (2 * ((q + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ (q + 1 + 1) *
            ((∏ i ∈ Finset.range (q + 1), V i) * V (q + 1)) := by
        rw [pow_succ']; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hpow_le hprod_nonneg

/- Section 2b: Lagrange partial fractions, Ball-Rivoal R_rat, uniqueness, symmetry, decay -/

lemma poly_eq_zero_of_eval_zero_on_finset (Q : Polynomial ℚ) (s : Finset ℚ)
    (hdeg : Q.natDegree < s.card) (hzero : ∀ x ∈ s, Q.eval x = 0) : Q = 0 := by
  by_contra hQ
  have hsub : s ⊆ Q.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hzero x hx
  have hcard : s.card ≤ Q.roots.card :=
    le_trans (Finset.card_le_card hsub) (Multiset.toFinset_card_le Q.roots)
  have hle := Polynomial.card_roots' Q
  omega

lemma prod_erase_sub_eq (n k : ℕ) (hk : k ≤ n) :
    ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ)) =
      (-1 : ℚ) ^ k * (k.factorial : ℚ) * ((n - k).factorial : ℚ) := by
  have hsplit : (Finset.range (n + 1)).erase k = Finset.range k ∪ Finset.Ioc k n := by
    ext m; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ioc k n) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_range, Finset.mem_Ioc] at hm1 hm2; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hleft : ∏ m ∈ Finset.range k, ((m : ℚ) - (k : ℚ)) = (-1 : ℚ) ^ k * (k.factorial : ℚ) := by
    have h1 : ∏ m ∈ Finset.range k, ((m : ℚ) - (k : ℚ)) =
        ∏ m ∈ Finset.range k, (-1 : ℚ) * ((k - m : ℕ) : ℚ) := by
      refine Finset.prod_congr rfl fun m hm => ?_
      have hmk : m ≤ k := le_of_lt (Finset.mem_range.mp hm)
      rw [Nat.cast_sub hmk]; ring
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    have hbij : ∏ m ∈ Finset.range k, ((k - m : ℕ) : ℚ) =
        ∏ i ∈ Finset.Icc 1 k, (i : ℚ) := by
      refine Finset.prod_bij (fun m _ => k - m) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
      · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_range] at hm1 hm2; omega
      · intro i hi; simp only [Finset.mem_Icc] at hi
        exact ⟨k - i, by simp only [Finset.mem_range]; omega, by omega⟩
      · intro _ _; rfl
    rw [hbij]
    clear h1 hbij hsplit hdisj hk
    induction k with
    | zero => simp
    | succ k' ih =>
      have hIcc : Finset.Icc 1 (k' + 1) = insert (k' + 1) (Finset.Icc 1 k') := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul]
  have hright : ∏ m ∈ Finset.Ioc k n, ((m : ℚ) - (k : ℚ)) = ((n - k).factorial : ℚ) := by
    have hbij : ∏ m ∈ Finset.Ioc k n, ((m : ℚ) - (k : ℚ)) =
        ∏ i ∈ Finset.Icc 1 (n - k), (i : ℚ) := by
      refine Finset.prod_bij (fun m _ => m - k) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Ioc] at hm; simp only [Finset.mem_Icc]; omega
      · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_Ioc] at hm1 hm2; omega
      · intro i hi; simp only [Finset.mem_Icc] at hi
        exact ⟨k + i, by simp only [Finset.mem_Ioc]; omega, by omega⟩
      · intro m hm
        have hkm : k ≤ m := le_of_lt (Finset.mem_Ioc.mp hm).1
        rw [Nat.cast_sub hkm]
    rw [hbij]
    generalize n - k = d
    induction d with
    | zero => simp
    | succ d' ih =>
      have hIcc : Finset.Icc 1 (d' + 1) = insert (d' + 1) (Finset.Icc 1 d') := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul]
  rw [hleft, hright]

lemma prod_Icc_shift_eq (M n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, ((M + i : ℕ) : ℚ) =
      (n.factorial : ℚ) * (Nat.choose (M + n) n : ℚ) := by
  have hnat : M.factorial * ∏ i ∈ Finset.Icc 1 n, (M + i) = (M + n).factorial := by
    induction n with
    | zero => simp
    | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp)]
      have hadd : M + (k + 1) = (M + k) + 1 := by omega
      rw [hadd, Nat.factorial_succ]
      calc M.factorial * ((M + k + 1) * ∏ i ∈ Finset.Icc 1 k, (M + i))
          = (M + k + 1) * (M.factorial * ∏ i ∈ Finset.Icc 1 k, (M + i)) := by ring
        _ = (M + k + 1) * (M + k).factorial := by rw [ih]
  have hch : Nat.choose (M + n) n * n.factorial * M.factorial = (M + n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ M + n by omega)
    simpa [Nat.add_sub_cancel] using h
  have heq_nat : ∏ i ∈ Finset.Icc 1 n, (M + i) = n.factorial * Nat.choose (M + n) n := by
    have hmul : M.factorial * ∏ i ∈ Finset.Icc 1 n, (M + i) =
        M.factorial * (n.factorial * Nat.choose (M + n) n) := by
      rw [hnat, ← hch]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos M) hmul
  have hcast := congr_arg (Nat.cast (R := ℚ)) heq_nat
  simpa using hcast

lemma lagrange_pf (n : ℕ) (P : Polynomial ℚ) (hdeg : P.natDegree ≤ n) {t : ℚ}
    (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    P.eval t / (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) =
      ∑ k ∈ Finset.range (n + 1),
        (P.eval (-(k : ℚ)) / ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ))) /
          (t + (k : ℚ)) := by
  let Q : Polynomial ℚ :=
    P - ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (P.eval (-(k : ℚ)) / ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ))) *
        ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ))
  have hQdeg : Q.natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le hdeg ?_)
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hsum : ∑ m ∈ (Finset.range (n + 1)).erase k,
        (Polynomial.X + Polynomial.C (m : ℚ)).natDegree ≤
        ∑ _m ∈ (Finset.range (n + 1)).erase k, 1 := by
      refine Finset.sum_le_sum fun m _ => ?_
      exact (Polynomial.natDegree_X_add_C (m : ℚ)).le
    refine le_trans hsum ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hk, Finset.card_range]
    omega
  have hQzero : ∀ k ∈ Finset.range (n + 1), Q.eval (-(k : ℚ)) = 0 := by
    intro k hk
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
    rw [Finset.sum_eq_single k]
    · have hprod_ne : ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro m hm
        exact sub_ne_zero.mpr (by exact_mod_cast (Finset.mem_erase.mp hm).1)
      have heq : ∏ m ∈ (Finset.range (n + 1)).erase k, (-(k : ℚ) + (m : ℚ)) =
          ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ)) := by
        refine Finset.prod_congr rfl fun m _ => by ring
      rw [heq, div_mul_cancel₀ _ hprod_ne, sub_self]
    · intro j hj hjk
      have hk_in : k ∈ (Finset.range (n + 1)).erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
      have hzero_prod : ∏ m ∈ (Finset.range (n + 1)).erase j, (-(k : ℚ) + (m : ℚ)) = 0 :=
        Finset.prod_eq_zero hk_in (by ring)
      rw [hzero_prod, mul_zero]
    · intro h; exact absurd hk h
  have hQ : Q = 0 := by
    let s : Finset ℚ := (Finset.range (n + 1)).image (fun k : ℕ => -(k : ℚ))
    have hcard : s.card = n + 1 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range (n + 1)
      · intro a b hab; simp only [neg_inj, Nat.cast_inj] at hab; exact hab
    apply poly_eq_zero_of_eval_zero_on_finset Q s (by omega)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact hQzero k hk
  have heval0 : Q.eval t = 0 := by rw [hQ, Polynomial.eval_zero]
  simp only [Q, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    sub_eq_zero] at heval0
  rw [heval0, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hprod_split : ∏ m ∈ Finset.range (n + 1), (t + (m : ℚ)) =
      (t + (k : ℚ)) * ∏ m ∈ (Finset.range (n + 1)).erase k, (t + (m : ℚ)) :=
    (Finset.mul_prod_erase (Finset.range (n + 1)) (fun m => t + (m : ℚ)) hk).symm
  have hne : ∏ m ∈ (Finset.range (n + 1)).erase k, (t + (m : ℚ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m hm
    exact ht m (Finset.mem_of_mem_erase hm)
  rw [hprod_split, mul_div_mul_right _ _ hne]

def R_rat (a r n : ℕ) (t : ℚ) : ℚ :=
  ((n.factorial : ℚ) ^ (a - 2 * r)) *
    (∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ))) *
    (∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ))) /
    (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) ^ a

def v_BR (r n : ℕ) (i k : ℕ) : ℚ :=
  if i < r then
    (-1 : ℚ) ^ (n + k) * (Nat.choose (k + i * n + n) n : ℚ) * (Nat.choose n k : ℚ)
  else if i < 2 * r then
    (-1 : ℚ) ^ k * (Nat.choose ((i - r + 2) * n - k) n : ℚ) * (Nat.choose n k : ℚ)
  else
    (-1 : ℚ) ^ k * (Nat.choose n k : ℚ)

lemma v_BR_int (r n i k : ℕ) : ∃ z : ℤ, v_BR r n i k = z := by
  unfold v_BR
  split_ifs
  · exact ⟨(-1 : ℤ) ^ (n + k) * (Nat.choose (k + i * n + n) n : ℤ) * (Nat.choose n k : ℤ),
      by push_cast; rfl⟩
  · exact ⟨(-1 : ℤ) ^ k * (Nat.choose ((i - r + 2) * n - k) n : ℤ) * (Nat.choose n k : ℤ),
      by push_cast; rfl⟩
  · exact ⟨(-1 : ℤ) ^ k * (Nat.choose n k : ℤ), by push_cast; rfl⟩

lemma choose_le_two_pow_rat (m k : ℕ) : (Nat.choose m k : ℚ) ≤ (2 : ℚ) ^ m := by
  exact_mod_cast (by
    calc Nat.choose m k ≤ ∑ i ∈ Finset.range (m + 1), Nat.choose m i := by
          by_cases hkm : k ≤ m
          · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm))
          · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
      _ = 2 ^ m := Nat.sum_range_choose m)

lemma v_BR_bound (r n i k : ℕ) (hk : k ≤ n) :
    |v_BR r n i k| ≤ if i < 2 * r then (2 : ℚ) ^ ((r + 2) * n) else (2 : ℚ) ^ n := by
  unfold v_BR
  split_ifs with h1 h2 h3
  · rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have hle1 : k + i * n + n ≤ (r + 1) * n := by
      have hi : i + 1 ≤ r := by omega
      calc k + i * n + n ≤ n + i * n + n := by omega
        _ = (i + 2) * n := by ring
        _ ≤ (r + 1) * n := Nat.mul_le_mul_right n (by omega)
    have h1' : (Nat.choose (k + i * n + n) n : ℚ) ≤ (2 : ℚ) ^ ((r + 1) * n) :=
      le_trans (choose_le_two_pow_rat _ _) (pow_le_pow_right₀ (by norm_num) hle1)
    have h2' : (Nat.choose n k : ℚ) ≤ (2 : ℚ) ^ n := choose_le_two_pow_rat n k
    calc (Nat.choose (k + i * n + n) n : ℚ) * (Nat.choose n k : ℚ)
        ≤ (2 : ℚ) ^ ((r + 1) * n) * (2 : ℚ) ^ n :=
          mul_le_mul h1' h2' (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℚ) ^ ((r + 2) * n) := by rw [← pow_add]; congr 1; ring
  · omega
  · rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have hle1 : (i - r + 2) * n - k ≤ (r + 1) * n := by
      have hi : i - r + 2 ≤ r + 1 := by omega
      calc (i - r + 2) * n - k ≤ (i - r + 2) * n := Nat.sub_le _ _
        _ ≤ (r + 1) * n := Nat.mul_le_mul_right n hi
    have h1' : (Nat.choose ((i - r + 2) * n - k) n : ℚ) ≤ (2 : ℚ) ^ ((r + 1) * n) :=
      le_trans (choose_le_two_pow_rat _ _) (pow_le_pow_right₀ (by norm_num) hle1)
    have h2' : (Nat.choose n k : ℚ) ≤ (2 : ℚ) ^ n := choose_le_two_pow_rat n k
    calc (Nat.choose ((i - r + 2) * n - k) n : ℚ) * (Nat.choose n k : ℚ)
        ≤ (2 : ℚ) ^ ((r + 1) * n) * (2 : ℚ) ^ n :=
          mul_le_mul h1' h2' (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℚ) ^ ((r + 2) * n) := by rw [← pow_add]; congr 1; ring
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact choose_le_two_pow_rat n k

lemma prod_Icc_mul_split (n : ℕ) (f : ℕ → ℚ) :
    ∀ r : ℕ, ∏ j ∈ Finset.Icc 1 (r * n), f j =
      ∏ s ∈ Finset.range r, ∏ i ∈ Finset.Icc 1 n, f (s * n + i) := by
  intro r
  induction r with
  | zero => simp
  | succ r' ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hsplit : Finset.Icc 1 ((r' + 1) * n) =
        Finset.Icc 1 (r' * n) ∪ Finset.Icc (r' * n + 1) ((r' + 1) * n) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union]
      have : (r' + 1) * n = r' * n + n := by ring
      omega
    have hdisj : Disjoint (Finset.Icc 1 (r' * n)) (Finset.Icc (r' * n + 1) ((r' + 1) * n)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2; simp only [Finset.mem_Icc] at hj1 hj2; omega
    rw [hsplit, Finset.prod_union hdisj]
    congr 1
    refine Finset.prod_bij (fun j _ => j - r' * n) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢
      have : (r' + 1) * n = r' * n + n := by ring
      omega
    · intro j1 hj1 j2 hj2 h; simp only [Finset.mem_Icc] at hj1 hj2; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      have : (r' + 1) * n = r' * n + n := by ring
      exact ⟨r' * n + i, by simp only [Finset.mem_Icc]; omega, by omega⟩
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have h1 : r' * n + (j - r' * n) = j := by omega
      rw [h1]

lemma eval_factor_A (n : ℕ) {t : ℚ} (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    (n.factorial : ℚ) / (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ k * (Nat.choose n k : ℚ)) / (t + (k : ℚ)) := by
  have h := lagrange_pf n (Polynomial.C (n.factorial : ℚ)) (by simp) ht
  simp only [Polynomial.eval_C] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [prod_erase_sub_eq n k hk_le]
  congr 1
  have hch : (n.factorial : ℚ) =
      (Nat.choose n k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk_le).symm
  have hf1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hf2 : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hsign : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hne : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  rw [hch]
  field_simp [hf1, hf2, hne]
  rw [hsign]; ring

lemma eval_factor_B (s n : ℕ) {t : ℚ} (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    (∏ i ∈ Finset.Icc 1 n, (t - ((s * n + i : ℕ) : ℚ))) /
        (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ (n + k) * (Nat.choose (k + s * n + n) n : ℚ) * (Nat.choose n k : ℚ)) /
          (t + (k : ℚ)) := by
  let P : Polynomial ℚ := ∏ i ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C ((s * n + i : ℕ) : ℚ))
  have hPdeg : P.natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hsum : ∑ i ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C ((s * n + i : ℕ) : ℚ)).natDegree ≤
        ∑ _i ∈ Finset.Icc 1 n, 1 :=
      Finset.sum_le_sum fun _ _ => Polynomial.natDegree_X_sub_C_le _
    refine le_trans hsum ?_
    simp
  have h := lagrange_pf n P hPdeg ht
  have hPt : P.eval t = ∏ i ∈ Finset.Icc 1 n, (t - ((s * n + i : ℕ) : ℚ)) := by
    simp [P, Polynomial.eval_prod]
  rw [← hPt, h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [prod_erase_sub_eq n k hk_le]
  congr 1
  have hPk : P.eval (-(k : ℚ)) =
      (-1 : ℚ) ^ n * ((n.factorial : ℚ) * (Nat.choose (k + s * n + n) n : ℚ)) := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have h1 : ∏ i ∈ Finset.Icc 1 n, (-(k : ℚ) - ((s * n + i : ℕ) : ℚ)) =
        ∏ i ∈ Finset.Icc 1 n, (-1 : ℚ) * (((k + s * n) + i : ℕ) : ℚ) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    rw [prod_Icc_shift_eq (k + s * n) n]
  rw [hPk]
  have hch : (n.factorial : ℚ) =
      (Nat.choose n k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk_le).symm
  have hf1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hf2 : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hsign : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hne : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  rw [hch, pow_add (-1 : ℚ) n k]
  field_simp [hf1, hf2, hne]
  rw [hsign]; ring

lemma eval_factor_C (s n : ℕ) {t : ℚ} (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    (∏ i ∈ Finset.Icc 1 n, (t + (((s + 1) * n + i : ℕ) : ℚ))) /
        (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ k * (Nat.choose ((s + 2) * n - k) n : ℚ) * (Nat.choose n k : ℚ)) /
          (t + (k : ℚ)) := by
  let P : Polynomial ℚ :=
    ∏ i ∈ Finset.Icc 1 n, (Polynomial.X + Polynomial.C (((s + 1) * n + i : ℕ) : ℚ))
  have hPdeg : P.natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hsum : ∑ i ∈ Finset.Icc 1 n,
        (Polynomial.X + Polynomial.C (((s + 1) * n + i : ℕ) : ℚ)).natDegree ≤
        ∑ _i ∈ Finset.Icc 1 n, 1 :=
      Finset.sum_le_sum fun _ _ => (Polynomial.natDegree_X_add_C _).le
    refine le_trans hsum ?_
    simp
  have h := lagrange_pf n P hPdeg ht
  have hPt : P.eval t = ∏ i ∈ Finset.Icc 1 n, (t + (((s + 1) * n + i : ℕ) : ℚ)) := by
    simp [P, Polynomial.eval_prod]
  rw [← hPt, h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [prod_erase_sub_eq n k hk_le]
  congr 1
  have hk_le_sn : k ≤ (s + 1) * n := le_trans hk_le (Nat.le_mul_of_pos_left n (by omega))
  have hPk : P.eval (-(k : ℚ)) =
      (n.factorial : ℚ) * (Nat.choose ((s + 2) * n - k) n : ℚ) := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have h1 : ∏ i ∈ Finset.Icc 1 n, (-(k : ℚ) + (((s + 1) * n + i : ℕ) : ℚ)) =
        ∏ i ∈ Finset.Icc 1 n, ((((s + 1) * n - k) + i : ℕ) : ℚ) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Nat.cast_add, Nat.cast_sub hk_le_sn]; ring
    rw [h1, prod_Icc_shift_eq ((s + 1) * n - k) n]
    have h2 : (s + 1) * n - k + n = (s + 2) * n - k := by
      have : (s + 2) * n = (s + 1) * n + n := by ring
      omega
    rw [h2]
  rw [hPk]
  have hch : (n.factorial : ℚ) =
      (Nat.choose n k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk_le).symm
  have hf1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hf2 : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hsign : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hne : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  rw [hch]
  field_simp [hf1, hf2, hne]
  rw [hsign]; ring

def c_BR (a r n : ℕ) : ℕ → ℕ → ℚ := iterPF n (v_BR r n) a

lemma evalPF_c_BR {a r n : ℕ} (ha : 2 * r + 2 ≤ a) {t : ℚ}
    (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    evalPF a n (c_BR a r n) t = R_rat a r n t := by
  have ha1 : 1 ≤ a := by omega
  unfold c_BR
  rw [evalPF_iterPF (v_BR r n) ht a ha1]
  have hsplit : Finset.range a =
      Finset.range r ∪ (Finset.Ico r (2 * r) ∪ Finset.Ico (2 * r) a) := by
    ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hd1 : Disjoint (Finset.range r) (Finset.Ico r (2 * r) ∪ Finset.Ico (2 * r) a) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hi1 hi2; omega
  have hd2 : Disjoint (Finset.Ico r (2 * r)) (Finset.Ico (2 * r) a) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2; simp only [Finset.mem_Ico] at hi1 hi2; omega
  rw [hsplit, Finset.prod_union hd1, Finset.prod_union hd2]
  set D := ∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))
  have hB : ∏ i ∈ Finset.range r, ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
      (∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ))) / D ^ r := by
    have h1 : ∀ i ∈ Finset.range r,
        ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
        (∏ j ∈ Finset.Icc 1 n, (t - ((i * n + j : ℕ) : ℚ))) / D := by
      intro i hi
      have hir : i < r := Finset.mem_range.mp hi
      rw [eval_factor_B i n ht]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [v_BR, hir]
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    exact (prod_Icc_mul_split n (fun j => t - (j : ℚ)) r).symm
  have hC : ∏ i ∈ Finset.Ico r (2 * r), ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
      (∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ))) / D ^ r := by
    have hbij : ∏ i ∈ Finset.Ico r (2 * r), ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
        ∏ s ∈ Finset.range r, (∏ j ∈ Finset.Icc 1 n, (t + (((s + 1) * n + j : ℕ) : ℚ))) / D := by
      refine Finset.prod_bij (fun i _ => i - r) ?_ ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_range]; omega
      · intro i1 hi1 i2 hi2 h; simp only [Finset.mem_Ico] at hi1 hi2; omega
      · intro s hs; simp only [Finset.mem_range] at hs
        exact ⟨s + r, by simp only [Finset.mem_Ico]; omega, by omega⟩
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        rw [eval_factor_C (i - r) n ht]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hnr : ¬ i < r := by omega
        have h2r : i < 2 * r := hi.2
        simp [v_BR, hnr, h2r]
    rw [hbij, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [prod_Icc_mul_split n (fun j => t + (n : ℚ) + (j : ℚ)) r]
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun j _ => ?_
    have : (s + 1) * n + j = n + (s * n + j) := by ring
    rw [this]; push_cast; ring
  have hA : ∏ i ∈ Finset.Ico (2 * r) a, ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
      (n.factorial : ℚ) ^ (a - 2 * r) / D ^ (a - 2 * r) := by
    have h1 : ∀ i ∈ Finset.Ico (2 * r) a,
        ∑ k ∈ Finset.range (n + 1), v_BR r n i k / (t + (k : ℚ)) =
        (n.factorial : ℚ) / D := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [eval_factor_A n ht]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnr : ¬ i < r := by omega
      have hn2r : ¬ i < 2 * r := by omega
      simp [v_BR, hnr, hn2r]
    rw [Finset.prod_congr rfl h1, Finset.prod_const, Nat.card_Ico, div_pow]
  rw [hB, hC, hA]
  unfold R_rat
  have hpow : D ^ r * (D ^ r * D ^ (a - 2 * r)) = D ^ a := by
    rw [← pow_add, ← pow_add]
    congr 1; omega
  rw [div_mul_div_comm, div_mul_div_comm, hpow]
  ring

lemma c_BR_int {a r n : ℕ} (ha : 1 ≤ a) :
    ∀ j ∈ Finset.Icc 1 a, ∀ k ≤ n,
      ∃ z : ℤ, (commonDenom n : ℚ) ^ (a - j) * c_BR a r n j k = z :=
  iterPF_int (v_BR r n) a ha fun i _ k _ => v_BR_int r n i k

lemma c_BR_bound {a r n : ℕ} (ha : 2 * r + 2 ≤ a) :
    ∀ j ∈ Finset.Icc 1 a, ∀ k ≤ n,
      |c_BR a r n j k| ≤
        (2 * (a : ℚ) * ((n : ℚ) + 1)) ^ a * (2 : ℚ) ^ ((a + 2 * r ^ 2 + 2 * r) * n) := by
  let V : ℕ → ℚ := fun i => if i < 2 * r then (2 : ℚ) ^ ((r + 2) * n) else (2 : ℚ) ^ n
  have hV0 : ∀ i < a, 0 ≤ V i := by intro i _; dsimp [V]; split_ifs <;> positivity
  have hv : ∀ i < a, ∀ k ≤ n, |v_BR r n i k| ≤ V i := fun i _ k hk => v_BR_bound r n i k hk
  have h := iterPF_bound (v_BR r n) V a (by omega) hV0 hv
  have hprod : ∏ i ∈ Finset.range a, V i = (2 : ℚ) ^ ((a + 2 * r ^ 2 + 2 * r) * n) := by
    have hsplit : Finset.range a = Finset.range (2 * r) ∪ Finset.Ico (2 * r) a := by
      ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.range (2 * r)) (Finset.Ico (2 * r) a) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2; simp only [Finset.mem_range, Finset.mem_Ico] at hi1 hi2; omega
    rw [hsplit, Finset.prod_union hd]
    have h1 : ∏ i ∈ Finset.range (2 * r), V i = ((2 : ℚ) ^ ((r + 2) * n)) ^ (2 * r) := by
      trans (∏ _i ∈ Finset.range (2 * r), (2 : ℚ) ^ ((r + 2) * n))
      · refine Finset.prod_congr rfl fun i hi => by simp [V, Finset.mem_range.mp hi]
      · rw [Finset.prod_const, Finset.card_range]
    have h2 : ∏ i ∈ Finset.Ico (2 * r) a, V i = ((2 : ℚ) ^ n) ^ (a - 2 * r) := by
      trans (∏ _i ∈ Finset.Ico (2 * r) a, (2 : ℚ) ^ n)
      · refine Finset.prod_congr rfl fun i hi => by
          have := (Finset.mem_Ico.mp hi).1
          simp [V, show ¬ i < 2 * r by omega]
      · rw [Finset.prod_const, Nat.card_Ico]
    rw [h1, h2, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    have hsub : (a - 2 * r) * n + 2 * r * n = a * n := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    calc (r + 2) * n * (2 * r) + n * (a - 2 * r)
        = (2 * r ^ 2 + 2 * r) * n + ((a - 2 * r) * n + 2 * r * n) := by ring
      _ = (2 * r ^ 2 + 2 * r) * n + a * n := by rw [hsub]
      _ = (a + 2 * r ^ 2 + 2 * r) * n := by ring
  intro j hj k hk
  rw [← hprod]
  exact h j hj k hk

noncomputable def clearedPoly (a n : ℕ) (u : ℕ → ℕ → ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (u j k) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (a - j) *
      ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a

lemma clearedPoly_eval (a n : ℕ) (u : ℕ → ℕ → ℚ) {t : ℚ}
    (ht : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0) :
    (clearedPoly a n u).eval t =
      (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ)) ^ a) * evalPF a n u t := by
  unfold clearedPoly evalPF
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_prod]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hsplit : ∏ m ∈ Finset.range (n + 1), (t + (m : ℚ)) ^ a =
      (t + (k : ℚ)) ^ a * ∏ m ∈ (Finset.range (n + 1)).erase k, (t + (m : ℚ)) ^ a :=
    (Finset.mul_prod_erase (Finset.range (n + 1)) (fun m => (t + (m : ℚ)) ^ a) hk).symm
  have hja : a - j + j = a := Nat.sub_add_cancel (Finset.mem_Icc.mp hj).2
  have htk : (t + (k : ℚ)) ^ j ≠ 0 := pow_ne_zero j (ht k hk)
  have hpow : (t + (k : ℚ)) ^ a = (t + (k : ℚ)) ^ (a - j) * (t + (k : ℚ)) ^ j := by
    rw [← pow_add, hja]
  rw [hsplit, hpow]
  field_simp [htk]

lemma evalPF_unique {a n : ℕ} (u : ℕ → ℕ → ℚ)
    (hzero : ∀ t : ℚ, 0 < t → evalPF a n u t = 0) :
    ∀ j ∈ Finset.Icc 1 a, ∀ k ≤ n, u j k = 0 := by
  have hH : clearedPoly a n u = 0 := by
    let s : Finset ℚ :=
      (Finset.range ((clearedPoly a n u).natDegree + 1)).image (fun m : ℕ => ((m + 1 : ℕ) : ℚ))
    have hcard : s.card = (clearedPoly a n u).natDegree + 1 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        have h1 : (x : ℚ) + 1 = (y : ℚ) + 1 := by simpa using hxy
        exact_mod_cast add_right_cancel h1
    apply poly_eq_zero_of_eval_zero_on_finset (clearedPoly a n u) s (by omega)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
    have hpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    have ht : ∀ l ∈ Finset.range (n + 1), ((m + 1 : ℕ) : ℚ) + (l : ℚ) ≠ 0 := by
      intro l _; positivity
    rw [clearedPoly_eval a n u ht, hzero _ hpos, mul_zero]
  intro j hj k hk
  have hk_mem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hstrong : ∀ d : ℕ, d < a → u (a - d) k = 0 := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro hd
      -- Factor (X + C k)^d out of clearedPoly a n u = 0
      let lin : Polynomial ℚ := Polynomial.X + Polynomial.C (k : ℚ)
      let Q : Polynomial ℚ :=
        (∑ j ∈ Finset.Icc 1 (a - d),
          Polynomial.C (u j k) * lin ^ (a - j - d) *
            ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a) +
        (∑ j ∈ Finset.Icc 1 a, ∑ l ∈ (Finset.range (n + 1)).erase k,
          Polynomial.C (u j l) * (Polynomial.X + Polynomial.C (l : ℚ)) ^ (a - j) *
            lin ^ (a - d) *
            ∏ m ∈ ((Finset.range (n + 1)).erase l).erase k,
              (Polynomial.X + Polynomial.C (m : ℚ)) ^ a)
      have hfactor : clearedPoly a n u = lin ^ d * Q := by
        unfold clearedPoly
        have hsplit_k : ∀ j ∈ Finset.Icc 1 a,
            ∑ l ∈ Finset.range (n + 1),
              Polynomial.C (u j l) * (Polynomial.X + Polynomial.C (l : ℚ)) ^ (a - j) *
                ∏ m ∈ (Finset.range (n + 1)).erase l, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a =
            (Polynomial.C (u j k) * lin ^ (a - j) *
              ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a) +
            ∑ l ∈ (Finset.range (n + 1)).erase k,
              Polynomial.C (u j l) * (Polynomial.X + Polynomial.C (l : ℚ)) ^ (a - j) *
                ∏ m ∈ (Finset.range (n + 1)).erase l, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a :=
          fun j _ => (Finset.add_sum_erase _ _ hk_mem).symm
        rw [Finset.sum_congr rfl hsplit_k, Finset.sum_add_distrib]
        dsimp only [Q]
        rw [mul_add]
        congr 1
        · rw [Finset.mul_sum]
          have hsub : Finset.Icc 1 (a - d) ⊆ Finset.Icc 1 a := by
            intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
          rw [← Finset.sum_subset hsub]
          · refine Finset.sum_congr rfl fun j hj' => ?_
            have hle : d ≤ a - j := by simp only [Finset.mem_Icc] at hj'; omega
            have hadd : d + (a - j - d) = a - j := Nat.add_sub_of_le hle
            calc Polynomial.C (u j k) * lin ^ (a - j) *
                  ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a
                = Polynomial.C (u j k) * (lin ^ d * lin ^ (a - j - d)) *
                  ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a := by
                  rw [← pow_add, hadd]
              _ = lin ^ d * (Polynomial.C (u j k) * lin ^ (a - j - d) *
                  ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a) := by
                  ring
          · intro j hj' hjnot
            simp only [Finset.mem_Icc] at hj' hjnot
            have hgt : a - d < j := by omega
            have hda : a - j < d := by omega
            have hzero_u : u j k = 0 := by
              have h1 := ih (a - j) hda (by omega)
              have h2 : a - (a - j) = j := by omega
              rwa [h2] at h1
            simp [hzero_u]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l hl => ?_
          have hkl : k ∈ (Finset.range (n + 1)).erase l :=
            Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1.symm, hk_mem⟩
          rw [← Finset.mul_prod_erase _ _ hkl]
          have hadd : d + (a - d) = a := Nat.add_sub_of_le (le_of_lt hd)
          have hlin : (Polynomial.X + Polynomial.C (k : ℚ)) ^ a = lin ^ d * lin ^ (a - d) := by
            rw [← pow_add, hadd]
          rw [hlin]; ring
      have hQzero : Q = 0 := by
        have hmul0 : lin ^ d * Q = 0 := by rw [← hfactor, hH]
        have hlin_ne : lin ^ d ≠ 0 := by
          apply pow_ne_zero
          intro h0
          have h1 := congr_arg (Polynomial.eval (1 - (k : ℚ))) h0
          simp [lin] at h1
        exact (mul_eq_zero.mp hmul0).resolve_left hlin_ne
      have heval : Q.eval (-(k : ℚ)) = 0 := by rw [hQzero, Polynomial.eval_zero]
      have hlin_eval : lin.eval (-(k : ℚ)) = 0 := by simp [lin]
      have hQeval : Q.eval (-(k : ℚ)) =
          u (a - d) k * ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ)) ^ a := by
        dsimp only [Q]
        simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_prod, hlin_eval,
          zero_pow (by omega : a - d ≠ 0), mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
        rw [Finset.sum_eq_single (a - d)]
        · have hsub0 : a - (a - d) - d = 0 := by omega
          rw [hsub0, pow_zero, mul_one]
          congr 1
          refine Finset.prod_congr rfl fun m _ => ?_
          simp only [Polynomial.eval_X]
          congr 1; ring
        · intro j hj' hjne
          have hpos : a - j - d ≠ 0 := by simp only [Finset.mem_Icc] at hj'; omega
          rw [zero_pow hpos]; ring
        · intro hnot; exfalso; apply hnot; simp only [Finset.mem_Icc]; omega
      rw [hQeval] at heval
      have hprod_ne : ∏ m ∈ (Finset.range (n + 1)).erase k, ((m : ℚ) - (k : ℚ)) ^ a ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro m hm
        exact pow_ne_zero a (sub_ne_zero.mpr (by exact_mod_cast (Finset.mem_erase.mp hm).1))
      exact (mul_eq_zero.mp heval).resolve_right hprod_ne
  have hj' := Finset.mem_Icc.mp hj
  have h1 := hstrong (a - j) (by omega)
  have h2 : a - (a - j) = j := by omega
  rwa [h2] at h1

lemma R_rat_symm {a r n : ℕ} (ha : Odd a) (hn : Even n) {t : ℚ} :
    R_rat a r n (-t - (n : ℚ)) = -R_rat a r n t := by
  unfold R_rat
  have h1 : ∏ j ∈ Finset.Icc 1 (r * n), (-t - (n : ℚ) - (j : ℚ)) =
      (-1 : ℚ) ^ (r * n) * ∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ)) := by
    have heq : ∏ j ∈ Finset.Icc 1 (r * n), (-t - (n : ℚ) - (j : ℚ)) =
        ∏ j ∈ Finset.Icc 1 (r * n), (-1 : ℚ) * (t + (n : ℚ) + (j : ℚ)) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [heq, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  have h2 : ∏ j ∈ Finset.Icc 1 (r * n), (-t - (n : ℚ) + (n : ℚ) + (j : ℚ)) =
      (-1 : ℚ) ^ (r * n) * ∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ)) := by
    have heq : ∏ j ∈ Finset.Icc 1 (r * n), (-t - (n : ℚ) + (n : ℚ) + (j : ℚ)) =
        ∏ j ∈ Finset.Icc 1 (r * n), (-1 : ℚ) * (t - (j : ℚ)) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [heq, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  have hden : (∏ m ∈ Finset.range (n + 1), (-t - (n : ℚ) + (m : ℚ))) ^ a =
      -(∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) ^ a := by
    have hbij : ∏ m ∈ Finset.range (n + 1), (-t - (n : ℚ) + (m : ℚ)) =
        ∏ m ∈ Finset.range (n + 1), (-1 : ℚ) * (t + (m : ℚ)) := by
      refine Finset.prod_bij (fun m _ => n - m) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
      · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_range] at hm1 hm2; omega
      · intro m hm; simp only [Finset.mem_range] at hm
        exact ⟨n - m, by simp only [Finset.mem_range]; omega, by omega⟩
      · intro m hm
        have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        rw [Nat.cast_sub hmn]; ring
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, mul_pow, ← pow_mul]
    have hodd : Odd ((n + 1) * a) := Odd.mul (Even.add_one hn) ha
    rw [hodd.neg_one_pow]; ring
  have hsign : (-1 : ℚ) ^ (r * n) * (-1 : ℚ) ^ (r * n) = 1 := by rw [← mul_pow]; norm_num
  rw [h1, h2, hden]
  calc (n.factorial : ℚ) ^ (a - 2 * r) *
        ((-1 : ℚ) ^ (r * n) * ∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ))) *
        ((-1 : ℚ) ^ (r * n) * ∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ))) /
        -(∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) ^ a
      = (((-1 : ℚ) ^ (r * n) * (-1 : ℚ) ^ (r * n)) *
        ((n.factorial : ℚ) ^ (a - 2 * r) *
          (∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ))) *
          (∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ))))) /
        -(∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) ^ a := by ring
    _ = -((n.factorial : ℚ) ^ (a - 2 * r) *
          (∏ j ∈ Finset.Icc 1 (r * n), (t - (j : ℚ))) *
          (∏ j ∈ Finset.Icc 1 (r * n), (t + (n : ℚ) + (j : ℚ))) /
        (∏ m ∈ Finset.range (n + 1), (t + (m : ℚ))) ^ a) := by rw [hsign, one_mul, div_neg]

lemma c_BR_even_sum_zero {a r n : ℕ} (ha : 2 * r + 2 ≤ a) (ha_odd : Odd a) (hn : Even n)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 a) (hj_even : Even j) :
    ∑ k ∈ Finset.range (n + 1), c_BR a r n j k = 0 := by
  let u : ℕ → ℕ → ℚ := fun j k => (-1 : ℚ) ^ j * c_BR a r n j (n - k) + c_BR a r n j k
  have hu_zero : ∀ t : ℚ, 0 < t → evalPF a n u t = 0 := by
    intro t ht
    have ht1 : ∀ m ∈ Finset.range (n + 1), t + (m : ℚ) ≠ 0 := fun m _ => by positivity
    have ht2 : ∀ m ∈ Finset.range (n + 1), -t - (n : ℚ) + (m : ℚ) ≠ 0 := by
      intro m hm
      have hmn : (m : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      linarith
    have hsplit : evalPF a n u t =
        evalPF a n (c_BR a r n) (-t - (n : ℚ)) + evalPF a n (c_BR a r n) t := by
      unfold evalPF
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      have hbij : ∑ k ∈ Finset.range (n + 1),
            c_BR a r n j' k / (-t - (n : ℚ) + (k : ℚ)) ^ j' =
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ j' * c_BR a r n j' (n - k) / (t + (k : ℚ)) ^ j' := by
        refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_range] at hk1 hk2; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨n - k, by simp only [Finset.mem_range]; omega, by omega⟩
        · intro k hk
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hnn : n - (n - k) = k := by omega
          rw [hnn]
          have hsub : -t - (n : ℚ) + (k : ℚ) = (-1 : ℚ) * (t + ((n - k : ℕ) : ℚ)) := by
            rw [Nat.cast_sub hkn]; ring
          have hsign : ((-1 : ℚ) ^ j') ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [hsub, mul_pow]
          have hne : (-1 : ℚ) ^ j' ≠ 0 := pow_ne_zero j' (by norm_num)
          have htk : (t + ((n - k : ℕ) : ℚ)) ^ j' ≠ 0 :=
            pow_ne_zero j' (ht1 (n - k) (by simp only [Finset.mem_range]; omega))
          field_simp [hne, htk]
          rw [hsign]; ring
      rw [hbij, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [u]; rw [add_div]
    rw [hsplit, evalPF_c_BR ha ht2, evalPF_c_BR ha ht1, R_rat_symm ha_odd hn, neg_add_cancel]
  have hpoint : ∀ k ≤ n, c_BR a r n j (n - k) + c_BR a r n j k = 0 := by
    intro k hk
    have h := evalPF_unique u hu_zero j hj k hk
    dsimp [u] at h
    rwa [hj_even.neg_one_pow, one_mul] at h
  have hrev : ∑ k ∈ Finset.range (n + 1), c_BR a r n j (n - k) =
      ∑ k ∈ Finset.range (n + 1), c_BR a r n j k := by
    refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_range] at hk1 hk2; omega
    · intro k hk; simp only [Finset.mem_range] at hk
      exact ⟨n - k, by simp only [Finset.mem_range]; omega, by omega⟩
    · intro _ _; rfl
  have hsum2 : (∑ k ∈ Finset.range (n + 1), c_BR a r n j k) +
      (∑ k ∈ Finset.range (n + 1), c_BR a r n j k) = 0 := by
    calc (∑ k ∈ Finset.range (n + 1), c_BR a r n j k) +
          (∑ k ∈ Finset.range (n + 1), c_BR a r n j k)
        = (∑ k ∈ Finset.range (n + 1), c_BR a r n j (n - k)) +
          (∑ k ∈ Finset.range (n + 1), c_BR a r n j k) := by rw [hrev]
      _ = ∑ k ∈ Finset.range (n + 1), (c_BR a r n j (n - k) + c_BR a r n j k) :=
          (Finset.sum_add_distrib).symm
      _ = 0 := Finset.sum_eq_zero fun k hk => hpoint k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  linarith

lemma c_BR_one_sum_zero {a r n : ℕ} (ha : 2 * r + 2 ≤ a) :
    ∑ k ∈ Finset.range (n + 1), c_BR a r n 1 k = 0 := by
  let Pnum : Polynomial ℚ :=
    Polynomial.C ((n.factorial : ℚ) ^ (a - 2 * r)) *
      (∏ j ∈ Finset.Icc 1 (r * n), (Polynomial.X - Polynomial.C (j : ℚ))) *
      (∏ j ∈ Finset.Icc 1 (r * n), (Polynomial.X + Polynomial.C ((n : ℚ) + (j : ℚ))))
  have hpoly_eq : clearedPoly a n (c_BR a r n) = Pnum := by
    let Q := clearedPoly a n (c_BR a r n) - Pnum
    suffices hQ : Q = 0 from sub_eq_zero.mp hQ
    let s : Finset ℚ := (Finset.range (Q.natDegree + 1)).image (fun m : ℕ => ((m + 1 : ℕ) : ℚ))
    have hcard : s.card = Q.natDegree + 1 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        have h1 : (x : ℚ) + 1 = (y : ℚ) + 1 := by simpa using hxy
        exact_mod_cast add_right_cancel h1
    apply poly_eq_zero_of_eval_zero_on_finset Q s (by omega)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
    have ht : ∀ l ∈ Finset.range (n + 1), ((m + 1 : ℕ) : ℚ) + (l : ℚ) ≠ 0 := by
      intro l _; positivity
    simp only [Q, Polynomial.eval_sub, sub_eq_zero]
    rw [clearedPoly_eval a n (c_BR a r n) ht, evalPF_c_BR ha ht]
    unfold R_rat
    rw [Finset.prod_pow]
    have hne : (∏ l ∈ Finset.range (n + 1), (((m + 1 : ℕ) : ℚ) + (l : ℚ))) ^ a ≠ 0 :=
      pow_ne_zero a (Finset.prod_ne_zero_iff.mpr fun l hl => ht l hl)
    rw [mul_div_cancel₀ _ hne]
    simp only [Pnum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X]
    congr 1
    refine Finset.prod_congr rfl fun j _ => by ring
  set D := a * (n + 1) - 1
  have hD_gt : 2 * r * n < D := by
    have h1 : 2 * r * n + 2 * n ≤ a * n := by
      have : (2 * r + 2) * n ≤ a * n := Nat.mul_le_mul_right n ha
      linarith
    have h2 : a * (n + 1) = a * n + a := by ring
    omega
  have hPnum_deg : Pnum.natDegree ≤ 2 * r * n := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.C ((n.factorial : ℚ) ^ (a - 2 * r)) *
        ∏ j ∈ Finset.Icc 1 (r * n), (Polynomial.X - Polynomial.C (j : ℚ))).natDegree ≤ r * n := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
      have hsum : ∑ j ∈ Finset.Icc 1 (r * n), (Polynomial.X - Polynomial.C (j : ℚ)).natDegree ≤
          ∑ _j ∈ Finset.Icc 1 (r * n), 1 :=
        Finset.sum_le_sum fun _ _ => Polynomial.natDegree_X_sub_C_le _
      exact le_trans hsum (by simp)
    have h2 : (∏ j ∈ Finset.Icc 1 (r * n),
        (Polynomial.X + Polynomial.C ((n : ℚ) + (j : ℚ)))).natDegree ≤ r * n := by
      refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
      have hsum : ∑ j ∈ Finset.Icc 1 (r * n),
          (Polynomial.X + Polynomial.C ((n : ℚ) + (j : ℚ))).natDegree ≤
          ∑ _j ∈ Finset.Icc 1 (r * n), 1 :=
        Finset.sum_le_sum fun _ _ => (Polynomial.natDegree_X_add_C _).le
      exact le_trans hsum (by simp)
    have h3 : r * n + r * n = 2 * r * n := by ring
    omega
  have hcoeff_rhs : Pnum.coeff D = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff_lhs : (clearedPoly a n (c_BR a r n)).coeff D =
      ∑ k ∈ Finset.range (n + 1), c_BR a r n 1 k := by
    unfold clearedPoly
    simp only [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 1]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [mul_assoc, Polynomial.coeff_C_mul]
      set q : Polynomial ℚ := (Polynomial.X + Polynomial.C (k : ℚ)) ^ (a - 1) *
        ∏ m ∈ (Finset.range (n + 1)).erase k, (Polynomial.X + Polynomial.C (m : ℚ)) ^ a
      have hmonic : q.Monic := by
        apply Polynomial.Monic.mul
        · exact (Polynomial.monic_X_add_C (k : ℚ)).pow (a - 1)
        · exact Polynomial.monic_prod_of_monic _ _ fun m _ =>
            (Polynomial.monic_X_add_C (m : ℚ)).pow a
      have hdegq : q.natDegree = D := by
        have h1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (a - 1)).Monic :=
          (Polynomial.monic_X_add_C _).pow _
        have h2 : (∏ m ∈ (Finset.range (n + 1)).erase k,
            (Polynomial.X + Polynomial.C (m : ℚ)) ^ a).Monic :=
          Polynomial.monic_prod_of_monic _ _ fun m _ => (Polynomial.monic_X_add_C _).pow a
        rw [Polynomial.Monic.natDegree_mul h1 h2,
          Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C _),
          Polynomial.natDegree_X_add_C, mul_one,
          Polynomial.natDegree_prod_of_monic _ _ fun m _ => (Polynomial.monic_X_add_C _).pow a]
        have hsum : ∑ m ∈ (Finset.range (n + 1)).erase k,
            ((Polynomial.X + Polynomial.C (m : ℚ)) ^ a).natDegree = n * a := by
          have : ∀ m ∈ (Finset.range (n + 1)).erase k,
              ((Polynomial.X + Polynomial.C (m : ℚ)) ^ a).natDegree = a := by
            intro m _
            rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C _),
              Polynomial.natDegree_X_add_C, mul_one]
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul,
            Finset.card_erase_of_mem hk, Finset.card_range]
          simp
        rw [hsum]
        have : a * (n + 1) = a + n * a := by ring
        omega
      rw [← hdegq, hmonic.coeff_natDegree, mul_one]
    · intro j hj hj1
      refine Finset.sum_eq_zero fun k hk => ?_
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      have h1 : (Polynomial.C (c_BR a r n j k) *
          (Polynomial.X + Polynomial.C (k : ℚ)) ^ (a - j)).natDegree ≤ a - j := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C _),
          Polynomial.natDegree_X_add_C, mul_one]
      have h2 : (∏ m ∈ (Finset.range (n + 1)).erase k,
          (Polynomial.X + Polynomial.C (m : ℚ)) ^ a).natDegree ≤ n * a := by
        refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
        have : ∀ m ∈ (Finset.range (n + 1)).erase k,
            ((Polynomial.X + Polynomial.C (m : ℚ)) ^ a).natDegree = a := fun m _ => by
          rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C _),
            Polynomial.natDegree_X_add_C, mul_one]
        rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul,
          Finset.card_erase_of_mem hk, Finset.card_range]
        simp
      have hj' := Finset.mem_Icc.mp hj
      have : a * (n + 1) = a + n * a := by ring
      omega
    · intro hnot; exfalso; apply hnot; simp only [Finset.mem_Icc]; omega
  rw [← hcoeff_lhs, hpoly_eq, hcoeff_rhs]

/- Section 3: Series evaluation into real zeta values -/

noncomputable def zetaReal (j : ℕ) : ℝ :=
  ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ j

lemma riemannZeta_nat_eq_zetaReal {j : ℕ} (hj : 2 ≤ j) :
    riemannZeta (j : ℂ) = (zetaReal j : ℂ) := by
  have hj1 : 1 < ((j : ℂ)).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (show 1 < j by omega)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hj1]
  unfold zetaReal
  rw [Complex.ofReal_tsum]
  congr 1; ext m
  push_cast
  rw [Complex.cpow_natCast]

lemma summable_one_div_nat_add_pow {j : ℕ} (hj : 2 ≤ j) (k : ℕ) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ j)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  have hshift := (summable_nat_add_iff (k + 1)).mpr hbase
  refine hshift.congr fun m => ?_
  rw [one_div]; congr 1; push_cast; ring

lemma hasSum_one_div_nat_add_pow {j : ℕ} (hj : 2 ≤ j) (k : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j)
      (zetaReal j - ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j) := by
  have hsum0 : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ j) := by
    simpa using summable_one_div_nat_add_pow hj 0
  have hshift := hsum0.sum_add_tsum_nat_add k
  have hfin : ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1) ^ j =
      ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j := by
    refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro i1 _ i2 _ h; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      exact ⟨i - 1, by simp only [Finset.mem_range]; omega, by omega⟩
    · intro i _; push_cast; rfl
  have htsum : ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j =
      zetaReal j - ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j := by
    have heq : (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j) =
        (fun m : ℕ => (1 : ℝ) / (((m + k : ℕ) : ℝ) + 1) ^ j) := by
      ext m; push_cast; ring_nf
    rw [heq]
    unfold zetaReal
    linarith
  rw [← htsum]
  exact (summable_one_div_nat_add_pow hj k).hasSum

lemma hasSum_harmonic_diff {n : ℕ} (w : ℕ → ℝ)
    (hsum0 : ∑ k ∈ Finset.range (n + 1), w k = 0) :
    HasSum (fun m : ℕ => ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ)))
      (-∑ k ∈ Finset.range (n + 1), w k * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ)) := by
  -- Show partial sums converge to the target and terms are absolutely summable
  have hsummable : Summable (fun m : ℕ =>
      ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ))) := by
    have hrew : ∀ m : ℕ,
        ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ)) =
        ∑ k ∈ Finset.range (n + 1), w k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1)) := by
      intro m
      simp_rw [mul_sub, Finset.sum_sub_distrib, mul_one_div, ← Finset.sum_div, hsum0, zero_div,
        sub_zero]
    rw [show (fun m : ℕ => ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ))) =
        (fun m : ℕ => ∑ k ∈ Finset.range (n + 1),
          w k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) from funext hrew]
    apply summable_sum
    intro k _
    have hbound : ∀ m : ℕ,
        ‖w k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))‖ ≤
        (|w k| * (k : ℝ)) * (1 / ((m : ℝ) + 1) ^ 2) := by
      intro m
      rw [Real.norm_eq_abs, abs_mul]
      have hdiff : 1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1) =
          -(k : ℝ) / (((m : ℝ) + 1 + (k : ℝ)) * ((m : ℝ) + 1)) := by
        have h1 : (m : ℝ) + 1 + (k : ℝ) ≠ 0 := by positivity
        have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp [h1, h2]; ring
      rw [hdiff, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k),
        abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1 + (k : ℝ)) * ((m : ℝ) + 1))]
      have hden : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1 + (k : ℝ)) * ((m : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
        nlinarith
      have hdiv : (k : ℝ) / (((m : ℝ) + 1 + (k : ℝ)) * ((m : ℝ) + 1)) ≤
          (k : ℝ) / ((m : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by positivity) hden
      calc |w k| * ((k : ℝ) / (((m : ℝ) + 1 + (k : ℝ)) * ((m : ℝ) + 1)))
          ≤ |w k| * ((k : ℝ) / ((m : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
        _ = |w k| * (k : ℝ) * (1 / ((m : ℝ) + 1) ^ 2) := by ring
    exact Summable.of_norm_bounded (((summable_one_div_nat_add_pow (j := 2) (by omega) 0).congr
      (fun m => by simp)).mul_left (|w k| * (k : ℝ))) hbound
  -- Identify the sum via limit of partial sums
  have htend : Filter.Tendsto
      (fun M : ℕ => ∑ m ∈ Finset.range M,
        ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ)))
      Filter.atTop
      (nhds (-∑ k ∈ Finset.range (n + 1), w k * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ))) := by
    have hpart : ∀ M : ℕ,
        ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (n + 1), w k / ((m : ℝ) + 1 + (k : ℝ)) =
        (-∑ k ∈ Finset.range (n + 1), w k * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ)) +
        ∑ k ∈ Finset.range (n + 1), w k * ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ) := by
      intro M
      rw [Finset.sum_comm]
      have hzero_M : ∑ k ∈ Finset.range (n + 1),
          w k * ∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (i : ℝ) = 0 := by
        rw [← Finset.sum_mul, hsum0, zero_mul]
      have hterm : ∀ k ∈ Finset.range (n + 1),
          ∑ m ∈ Finset.range M, w k / ((m : ℝ) + 1 + (k : ℝ)) =
          w k * (-(∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ)) +
            ∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (i : ℝ) +
            ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ)) := by
        intro k _
        have h1 : ∑ m ∈ Finset.range M, w k / ((m : ℝ) + 1 + (k : ℝ)) =
            w k * ∑ i ∈ Finset.Icc (k + 1) (M + k), (1 : ℝ) / (i : ℝ) := by
          have hrew : ∀ m : ℕ, w k / ((m : ℝ) + 1 + (k : ℝ)) =
              w k * ((1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ))) := fun m => by ring
          simp_rw [hrew, ← Finset.mul_sum]
          congr 1
          refine Finset.sum_bij (fun m _ => m + 1 + k) ?_ ?_ ?_ ?_
          · intro m hm; simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
          · intro m1 _ m2 _ h; omega
          · intro i hi; simp only [Finset.mem_Icc] at hi
            exact ⟨i - 1 - k, by simp only [Finset.mem_range]; omega, by omega⟩
          · intro m _; push_cast; rfl
        rw [h1]; congr 1
        have hI1 : Finset.Icc 1 (M + k) = Finset.Icc 1 k ∪ Finset.Icc (k + 1) (M + k) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hd1 : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) (M + k)) := by
          rw [Finset.disjoint_left]; intro i h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
        have hI2 : Finset.Icc 1 (M + k) = Finset.Icc 1 M ∪ Finset.Icc (M + 1) (M + k) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hd2 : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (M + k)) := by
          rw [Finset.disjoint_left]; intro i h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
        have hsum_eq : (∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ)) +
            ∑ i ∈ Finset.Icc (k + 1) (M + k), (1 : ℝ) / (i : ℝ) =
            (∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (i : ℝ)) +
            ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ) := by
          rw [← Finset.sum_union hd1, ← hI1, hI2, Finset.sum_union hd2]
        linarith
      rw [Finset.sum_congr rfl hterm]
      simp_rw [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      linarith
    simp_rw [hpart]
    have htail : Filter.Tendsto
        (fun M : ℕ => ∑ k ∈ Finset.range (n + 1),
          w k * ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ))
        Filter.atTop (nhds 0) := by
      have h0 : (0 : ℝ) = ∑ _k ∈ Finset.range (n + 1), (0 : ℝ) := by simp
      rw [h0]
      refine tendsto_finset_sum _ fun k _ => ?_
      have hbound : ∀ M : ℕ,
          ‖w k * ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ)‖ ≤
          (|w k| * (k : ℝ)) / ((M : ℝ) + 1) := by
        intro M
        have hsum_nn : 0 ≤ ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ) :=
          Finset.sum_nonneg fun _ _ => by positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsum_nn]
        have hsum_le : ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ) ≤
            (k : ℝ) / ((M : ℝ) + 1) := by
          calc ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ)
              ≤ ∑ _i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / ((M : ℝ) + 1) := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hiM : M + 1 ≤ i := (Finset.mem_Icc.mp hi).1
                exact div_le_div_of_nonneg_left zero_le_one (by positivity)
                  (by exact_mod_cast hiM)
            _ = ((Finset.Icc (M + 1) (M + k)).card : ℝ) * (1 / ((M : ℝ) + 1)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = (k : ℝ) / ((M : ℝ) + 1) := by
                rw [Nat.card_Icc]
                have : M + k + 1 - (M + 1) = k := by omega
                rw [this, mul_one_div]
        calc |w k| * ∑ i ∈ Finset.Icc (M + 1) (M + k), (1 : ℝ) / (i : ℝ)
            ≤ |w k| * ((k : ℝ) / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _)
          _ = |w k| * (k : ℝ) / ((M : ℝ) + 1) := by ring
      have hlim : Filter.Tendsto (fun M : ℕ => (|w k| * (k : ℝ)) / ((M : ℝ) + 1))
          Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds (x := |w k| * (k : ℝ))).mul
            (tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1
              tendsto_natCast_atTop_atTop))
      exact squeeze_zero_norm hbound hlim
    simpa using tendsto_const_nhds.add htail
  exact hsummable.hasSum_iff_tendsto_nat.mpr htend

noncomputable def S_BR (a r n : ℕ) : ℝ :=
  ∑' m : ℕ, (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ)

lemma S_BR_hasSum_linear_form {a r n : ℕ} (ha : 2 * r + 2 ≤ a) (ha_odd : Odd a) (hn : Even n) :
    HasSum (fun m : ℕ => (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ))
      ((-∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
          (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j) +
       ∑ j ∈ (Finset.Icc 3 a).filter Odd,
          (∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ)) * zetaReal j) := by
  have heq : ∀ m : ℕ,
      (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ) =
      (∑ k ∈ Finset.range (n + 1), (c_BR a r n 1 k : ℝ) / ((m : ℝ) + 1 + (k : ℝ))) +
      ∑ j ∈ Finset.Icc 2 a, ∑ k ∈ Finset.range (n + 1),
        (c_BR a r n j k : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j) := by
    intro m
    have ht : ∀ l ∈ Finset.range (n + 1), ((m + 1 : ℕ) : ℚ) + (l : ℚ) ≠ 0 := by
      intro l _; positivity
    rw [← evalPF_c_BR ha ht]
    unfold evalPF
    push_cast
    have hIcc : Finset.Icc 1 a = insert 1 (Finset.Icc 2 a) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => by simp [pow_one]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [show (fun m : ℕ => (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ)) = _ from funext heq]
  have h1 : HasSum (fun m : ℕ => ∑ k ∈ Finset.range (n + 1),
        (c_BR a r n 1 k : ℝ) / ((m : ℝ) + 1 + (k : ℝ)))
      (-∑ k ∈ Finset.range (n + 1),
        (c_BR a r n 1 k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ)) := by
    apply hasSum_harmonic_diff
    have h0 := c_BR_one_sum_zero (r := r) (n := n) ha
    exact_mod_cast h0
  have h2 : HasSum (fun m : ℕ => ∑ j ∈ Finset.Icc 2 a, ∑ k ∈ Finset.range (n + 1),
        (c_BR a r n j k : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ j))
      (∑ j ∈ Finset.Icc 2 a, ∑ k ∈ Finset.range (n + 1),
        (c_BR a r n j k : ℝ) * (zetaReal j - ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j)) := by
    apply hasSum_sum
    intro j hj
    apply hasSum_sum
    intro k _
    exact (hasSum_one_div_nat_add_pow (Finset.mem_Icc.mp hj).1 k).mul_left _
  convert h1.add h2 using 1
  -- Simplify RHS by separating zetaReal terms and rational terms, dropping even j
  have hIcc : Finset.Icc 1 a = insert 1 (Finset.Icc 2 a) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hpow1 : ∑ k ∈ Finset.range (n + 1),
      (c_BR a r n 1 k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ 1 =
      ∑ k ∈ Finset.range (n + 1),
      (c_BR a r n 1 k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) := by
    simp [pow_one]
  rw [hpow1]
  have hzeta_split :
      ∑ j ∈ Finset.Icc 2 a, (∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ)) * zetaReal j =
      ∑ j ∈ (Finset.Icc 3 a).filter Odd,
        (∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ)) * zetaReal j := by
    have hsub : (Finset.Icc 3 a).filter Odd ⊆ Finset.Icc 2 a := by
      intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
    rw [← Finset.sum_subset hsub]
    intro j hj hjnot
    simp only [Finset.mem_Icc, Finset.mem_filter, not_and] at hj hjnot
    have hjeven : Even j := by
      by_cases h2 : j = 2
      · subst h2; exact even_two
      · exact Nat.not_odd_iff_even.mp (hjnot ⟨by omega, hj.2⟩)
    have h0 : ∑ k ∈ Finset.range (n + 1), c_BR a r n j k = 0 :=
      c_BR_even_sum_zero ha ha_odd hn (by simp only [Finset.mem_Icc]; omega) hjeven
    have h0R : ∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ) = 0 := by exact_mod_cast h0
    rw [h0R, zero_mul]
  rw [hzeta_split]
  ring

lemma S_BR_integer_linear_form {a r n : ℕ} (ha : 2 * r + 2 ≤ a) (ha_odd : Odd a) (hn : Even n) :
    ∃ (p0 : ℤ) (p : ℕ → ℤ),
      ((commonDenom n : ℝ) ^ a) * S_BR a r n =
        (p0 : ℝ) + ∑ j ∈ (Finset.Icc 3 a).filter Odd, (p j : ℝ) * zetaReal j ∧
      |(p0 : ℝ)| ≤ (commonDenom n : ℝ) ^ a * (a : ℝ) * ((n : ℝ) + 1) ^ 2 *
          ((2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a * (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * n)) ∧
      ∀ j ∈ (Finset.Icc 3 a).filter Odd,
        |(p j : ℝ)| ≤ (commonDenom n : ℝ) ^ a * (a : ℝ) * ((n : ℝ) + 1) ^ 2 *
          ((2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a * (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * n)) := by
  have hS := (S_BR_hasSum_linear_form ha ha_odd hn).tsum_eq
  -- Integrality of p0 and p j in ℚ
  have hp0_int : ∃ z : ℤ,
      -((commonDenom n : ℚ) ^ a *
        ∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
          c_BR a r n j k * ∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / (i : ℚ) ^ j) = (z : ℚ) := by
    suffices h : ∃ z : ℤ,
        (commonDenom n : ℚ) ^ a *
          ∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
            c_BR a r n j k * ∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / (i : ℚ) ^ j = (z : ℚ) by
      rcases h with ⟨z, hz⟩; exact ⟨-z, by push_cast; linarith⟩
    rw [Finset.mul_sum]
    apply exists_int_sum
    intro j hj
    rw [Finset.mul_sum]
    apply exists_int_sum
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [← mul_assoc, Finset.mul_sum]
    apply exists_int_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hdvd : i ∣ commonDenom n := dvd_commonDenom hi'.1 (le_trans hi'.2 hk_le)
    rcases hdvd with ⟨q, hq⟩
    have hi_int : ∃ z : ℤ, (commonDenom n : ℚ) / (i : ℚ) = (z : ℚ) := by
      refine ⟨(q : ℤ), ?_⟩
      have hine : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
      rw [div_eq_iff hine]
      exact_mod_cast hq.trans (mul_comm _ _)
    have hsplit : (commonDenom n : ℚ) ^ a * c_BR a r n j k * ((1 : ℚ) / (i : ℚ) ^ j) =
        ((commonDenom n : ℚ) ^ (a - j) * c_BR a r n j k) *
          ((commonDenom n : ℚ) / (i : ℚ)) ^ j := by
      have hja : a - j + j = a := Nat.sub_add_cancel (Finset.mem_Icc.mp hj).2
      have hpow : (commonDenom n : ℚ) ^ a =
          (commonDenom n : ℚ) ^ (a - j) * (commonDenom n : ℚ) ^ j := by rw [← pow_add, hja]
      rw [hpow, div_pow]; ring
    rw [hsplit]
    exact exists_int_mul (c_BR_int (by omega) j hj k hk_le) (exists_int_pow hi_int j)
  have hpj_int : ∀ j ∈ Finset.Icc 1 a, ∃ z : ℤ,
      (commonDenom n : ℚ) ^ a * ∑ k ∈ Finset.range (n + 1), c_BR a r n j k = (z : ℚ) := by
    intro j hj
    rw [Finset.mul_sum]
    apply exists_int_sum
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hja : a - j + j = a := Nat.sub_add_cancel (Finset.mem_Icc.mp hj).2
    have hsplit : (commonDenom n : ℚ) ^ a * c_BR a r n j k =
        ((commonDenom n : ℚ) ^ (a - j) * c_BR a r n j k) * (commonDenom n : ℚ) ^ j := by
      have hpow : (commonDenom n : ℚ) ^ a =
          (commonDenom n : ℚ) ^ (a - j) * (commonDenom n : ℚ) ^ j := by rw [← pow_add, hja]
      rw [hpow]; ring
    rw [hsplit]
    exact exists_int_mul (c_BR_int (by omega) j hj k hk_le)
      ⟨(commonDenom n : ℤ) ^ j, by push_cast; rfl⟩
  choose p0 hp0 using hp0_int
  let p : ℕ → ℤ := fun j =>
    if hj : j ∈ Finset.Icc 1 a then (hpj_int j hj).choose else 0
  have hp_spec : ∀ j ∈ Finset.Icc 1 a,
      (p j : ℚ) = (commonDenom n : ℚ) ^ a * ∑ k ∈ Finset.range (n + 1), c_BR a r n j k := by
    intro j hj
    simp only [p, dif_pos hj]
    exact (hpj_int j hj).choose_spec.symm
  refine ⟨p0, p, ?_, ?_, ?_⟩
  · unfold S_BR
    rw [hS, mul_add, Finset.mul_sum]
    congr 1
    · have hcast := congr_arg (Rat.cast (K := ℝ)) hp0
      push_cast at hcast
      linarith
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ∈ Finset.Icc 1 a := by
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
      have hcast := congr_arg (Rat.cast (K := ℝ)) (hp_spec j hj')
      push_cast at hcast
      rw [hcast]; ring
  · set M : ℝ := (2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a * (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * n)
    have hM0 : 0 ≤ M := by positivity
    have hbound_c : ∀ j ∈ Finset.Icc 1 a, ∀ k ≤ n, |(c_BR a r n j k : ℝ)| ≤ M := by
      intro j hj k hk
      have hq := c_BR_bound ha j hj k hk
      have hr : ((|c_BR a r n j k| : ℚ) : ℝ) ≤
          (((2 * (a : ℚ) * ((n : ℚ) + 1)) ^ a *
            (2 : ℚ) ^ ((a + 2 * r ^ 2 + 2 * r) * n) : ℚ) : ℝ) := by exact_mod_cast hq
      simpa [M] using hr
    have hp0R : (p0 : ℝ) = -((commonDenom n : ℝ) ^ a *
        ∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
          (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j) := by
      have hcast := congr_arg (Rat.cast (K := ℝ)) hp0
      push_cast at hcast; linarith
    rw [hp0R, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (commonDenom n : ℝ) ^ a)]
    have hsum_le : |∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
          (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j| ≤
        (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∀ j ∈ Finset.Icc 1 a,
          |∑ k ∈ Finset.range (n + 1),
            (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j| ≤
          ((n : ℝ) + 1) ^ 2 * M := by
        intro j hj
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have h2 : ∀ k ∈ Finset.range (n + 1),
            |(c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j| ≤
            ((n : ℝ) + 1) * M := by
          intro k hk
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hharm_nn : 0 ≤ ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j :=
            Finset.sum_nonneg fun _ _ => by positivity
          rw [abs_mul, abs_of_nonneg hharm_nn]
          have hharm : ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j ≤ (n : ℝ) + 1 := by
            calc ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j
                ≤ ∑ _i ∈ Finset.Icc 1 k, (1 : ℝ) := by
                  refine Finset.sum_le_sum fun i hi => ?_
                  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).1
                  exact div_le_one_of_le₀ (one_le_pow₀ hi1) (by positivity)
              _ = (k : ℝ) := by simp
              _ ≤ (n : ℝ) + 1 := by exact_mod_cast (show k ≤ n + 1 by omega)
          calc |(c_BR a r n j k : ℝ)| * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j
              ≤ M * ((n : ℝ) + 1) := mul_le_mul (hbound_c j hj k hk_le) hharm
                (Finset.sum_nonneg fun _ _ => by positivity) hM0
            _ = ((n : ℝ) + 1) * M := mul_comm _ _
        calc ∑ k ∈ Finset.range (n + 1),
              |(c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j|
            ≤ ∑ _k ∈ Finset.range (n + 1), ((n : ℝ) + 1) * M := Finset.sum_le_sum h2
          _ = ((n : ℝ) + 1) ^ 2 * M := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      calc ∑ j ∈ Finset.Icc 1 a,
            |∑ k ∈ Finset.range (n + 1),
              (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j|
          ≤ ∑ _j ∈ Finset.Icc 1 a, ((n : ℝ) + 1) ^ 2 * M := Finset.sum_le_sum h1
        _ = (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            have : a + 1 - 1 = a := by omega
            rw [this]; ring
    calc (commonDenom n : ℝ) ^ a * |∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.range (n + 1),
            (c_BR a r n j k : ℝ) * ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ j|
        ≤ (commonDenom n : ℝ) ^ a * ((a : ℝ) * ((n : ℝ) + 1) ^ 2 * M) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (commonDenom n : ℝ) ^ a * (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by ring
  · intro j hj
    have hj' : j ∈ Finset.Icc 1 a := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
    set M : ℝ := (2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a * (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * n)
    have hM0 : 0 ≤ M := by positivity
    have hbound_c : ∀ k ≤ n, |(c_BR a r n j k : ℝ)| ≤ M := by
      intro k hk
      have hq := c_BR_bound ha j hj' k hk
      have hr : ((|c_BR a r n j k| : ℚ) : ℝ) ≤
          (((2 * (a : ℚ) * ((n : ℚ) + 1)) ^ a *
            (2 : ℚ) ^ ((a + 2 * r ^ 2 + 2 * r) * n) : ℚ) : ℝ) := by exact_mod_cast hq
      simpa [M] using hr
    have hpjR : (p j : ℝ) = (commonDenom n : ℝ) ^ a *
        ∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ) := by
      have hcast := congr_arg (Rat.cast (K := ℝ)) (hp_spec j hj')
      push_cast at hcast; exact hcast
    rw [hpjR, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (commonDenom n : ℝ) ^ a)]
    have hsum_le : |∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ)| ≤
        ((n : ℝ) + 1) * M := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ k ∈ Finset.range (n + 1), |(c_BR a r n j k : ℝ)|
          ≤ ∑ _k ∈ Finset.range (n + 1), M :=
            Finset.sum_le_sum fun k hk => hbound_c k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        _ = ((n : ℝ) + 1) * M := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
    have hfac : (1 : ℝ) ≤ (a : ℝ) * ((n : ℝ) + 1) := by
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith
    have hstep : ((n : ℝ) + 1) * M ≤ (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by
      have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) * M := by positivity
      calc ((n : ℝ) + 1) * M = 1 * (((n : ℝ) + 1) * M) := (one_mul _).symm
        _ ≤ ((a : ℝ) * ((n : ℝ) + 1)) * (((n : ℝ) + 1) * M) :=
          mul_le_mul_of_nonneg_right hfac hnn
        _ = (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by ring
    calc (commonDenom n : ℝ) ^ a * |∑ k ∈ Finset.range (n + 1), (c_BR a r n j k : ℝ)|
        ≤ (commonDenom n : ℝ) ^ a * ((a : ℝ) * ((n : ℝ) + 1) ^ 2 * M) :=
          mul_le_mul_of_nonneg_left (le_trans hsum_le hstep) (by positivity)
      _ = (commonDenom n : ℝ) ^ a * (a : ℝ) * ((n : ℝ) + 1) ^ 2 * M := by ring

/- Section 4: Asymptotic upper and lower bounds on S_BR -/

lemma sum_inv_sq_le_two : ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun m => by positivity)
  intro N
  cases N with
  | zero => norm_num
  | succ N' =>
    have hind : ∀ M : ℕ, ∑ m ∈ Finset.range (M + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤
        2 - 1 / ((M : ℝ) + 1) := by
      intro M
      induction M with
      | zero => norm_num
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hstep : (1 : ℝ) / ((k : ℝ) + 2) ^ 2 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
          have heq : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
              1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
            field_simp [hk1.ne', hk2.ne']; ring
          rw [heq]
          apply div_le_div_of_nonneg_left zero_le_one (by positivity)
          nlinarith
        have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        linarith
    have h1 := hind N'
    have hpos : (0 : ℝ) ≤ 1 / ((N' : ℝ) + 1) := by positivity
    linarith

lemma R_rat_nonneg {a r n m : ℕ} : 0 ≤ (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ) := by
  unfold R_rat
  push_cast
  by_cases hm : m + 1 ≤ r * n
  · have hmem : m + 1 ∈ Finset.Icc 1 (r * n) := by simp only [Finset.mem_Icc]; omega
    have hzero : ∏ j ∈ Finset.Icc 1 (r * n), ((m : ℝ) + 1 - (j : ℝ)) = 0 :=
      Finset.prod_eq_zero hmem (by push_cast; ring)
    rw [hzero, mul_zero, zero_mul, zero_div]
  · apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · apply Finset.prod_nonneg
          intro j hj
          have hj_le : j ≤ r * n := (Finset.mem_Icc.mp hj).2
          have : (j : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (show j ≤ m + 1 by omega)
          linarith
      · apply Finset.prod_nonneg
        intro j _
        positivity
    · apply pow_nonneg
      apply Finset.prod_nonneg
      intro l _
      positivity

lemma S_BR_lower_bound {a r n : ℕ} (hr : 1 ≤ r) (ha : 2 * r + 2 ≤ a) (ha_odd : Odd a)
    (hn : Even n) (hn1 : 1 ≤ n) :
    ((r + 2 : ℝ) * (n : ℝ)) ^ (-(a : ℤ)) *
        ((r : ℝ) ^ (2 * r) / ((3 : ℝ) * ((r : ℝ) + 2)) ^ a) ^ n ≤ S_BR a r n := by
  have hsum : Summable (fun m : ℕ => (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ)) :=
    (S_BR_hasSum_linear_form ha ha_odd hn).summable
  have hle : (R_rat a r n (((r * n) + 1 : ℕ) : ℚ) : ℝ) ≤ S_BR a r n :=
    hsum.le_tsum (r * n) (fun m _ => R_rat_nonneg)
  refine le_trans ?_ hle
  unfold R_rat
  push_cast
  -- Evaluate / bound each factor at t = r * n + 1
  have hnum1 : ∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 - (j : ℝ)) =
      ((r * n).factorial : ℝ) := by
    have hbij : ∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 - (j : ℝ)) =
        ∏ i ∈ Finset.Icc 1 (r * n), (i : ℝ) := by
      refine Finset.prod_bij (fun j _ => r * n + 1 - j) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro j1 hj1 j2 hj2 h; simp only [Finset.mem_Icc] at hj1 hj2; omega
      · intro i hi; simp only [Finset.mem_Icc] at hi
        exact ⟨r * n + 1 - i, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro j hj
        have hle' : j ≤ r * n + 1 := by simp only [Finset.mem_Icc] at hj; omega
        rw [Nat.cast_sub hle']; push_cast; ring
    rw [hbij]
    generalize r * n = N
    induction N with
    | zero => simp
    | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul]
  have hnum2 : ((r : ℝ) * (n : ℝ)) ^ (r * n) ≤
      ∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 + (n : ℝ) + (j : ℝ)) := by
    have h1 : ∏ _j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ)) ≤
        ∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 + (n : ℝ) + (j : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j _
      linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j]
    simpa [Finset.prod_const, Nat.card_Icc] using h1
  have hden : (∏ m ∈ Finset.range (n + 1), ((r : ℝ) * (n : ℝ) + 1 + (m : ℝ))) ^ a ≤
      (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1)) := by
    have h1 : ∏ m ∈ Finset.range (n + 1), ((r : ℝ) * (n : ℝ) + 1 + (m : ℝ)) ≤
        ∏ _m ∈ Finset.range (n + 1), (((r : ℝ) + 2) * (n : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro m hm
      have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith
    rw [Finset.prod_const, Finset.card_range] at h1
    calc (∏ m ∈ Finset.range (n + 1), ((r : ℝ) * (n : ℝ) + 1 + (m : ℝ))) ^ a
        ≤ ((((r : ℝ) + 2) * (n : ℝ)) ^ (n + 1)) ^ a :=
          pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => by positivity) h1 a
      _ = (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1)) := by rw [← pow_mul, mul_comm (n + 1) a]
  have hfac1 : ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith [pow_le_three_pow_mul_factorial n]
  have hfac2 : (((r : ℝ) * (n : ℝ)) / 3) ^ (r * n) ≤ ((r * n).factorial : ℝ) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have := pow_le_three_pow_mul_factorial (r * n)
    push_cast at this
    linarith
  have hnum_low :
      ((n : ℝ) / 3) ^ ((a - 2 * r) * n) * (((r : ℝ) * (n : ℝ)) / 3) ^ (r * n) *
          ((r : ℝ) * (n : ℝ)) ^ (r * n) ≤
      (n.factorial : ℝ) ^ (a - 2 * r) *
        (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 - (j : ℝ))) *
        (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 + (n : ℝ) + (j : ℝ))) := by
    rw [hnum1]
    have hpow1 : ((n : ℝ) / 3) ^ ((a - 2 * r) * n) ≤ (n.factorial : ℝ) ^ (a - 2 * r) := by
      rw [mul_comm (a - 2 * r) n, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hfac1 _
    exact mul_le_mul (mul_le_mul hpow1 hfac2 (by positivity) (by positivity)) hnum2
      (by positivity) (by positivity)
  have hden_pos : (0 : ℝ) < (∏ m ∈ Finset.range (n + 1), ((r : ℝ) * (n : ℝ) + 1 + (m : ℝ))) ^ a :=
    pow_pos (Finset.prod_pos fun _ _ => by positivity) a
  have hnum_nn : 0 ≤ (n.factorial : ℝ) ^ (a - 2 * r) *
      (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 - (j : ℝ))) *
      (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 + (n : ℝ) + (j : ℝ))) := by
    rw [hnum1]; positivity
  have hfrac :
      (((n : ℝ) / 3) ^ ((a - 2 * r) * n) * (((r : ℝ) * (n : ℝ)) / 3) ^ (r * n) *
          ((r : ℝ) * (n : ℝ)) ^ (r * n)) /
        (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1)) ≤
      ((n.factorial : ℝ) ^ (a - 2 * r) *
        (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 - (j : ℝ))) *
        (∏ j ∈ Finset.Icc 1 (r * n), ((r : ℝ) * (n : ℝ) + 1 + (n : ℝ) + (j : ℝ)))) /
        (∏ m ∈ Finset.range (n + 1), ((r : ℝ) * (n : ℝ) + 1 + (m : ℝ))) ^ a :=
    div_le_div₀ hnum_nn hnum_low hden_pos hden
  refine le_trans ?_ hfrac
  -- Algebraic simplification of the lower bound expression
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have h3_le : (3 : ℝ) ^ (r * n) ≥ (1 : ℝ) := one_le_pow₀ (by norm_num)
  have hexp_n : (a - 2 * r) * n + r * n + r * n = a * n := by
    have : (a - 2 * r) + r + r = a := by omega
    calc (a - 2 * r) * n + r * n + r * n = ((a - 2 * r) + r + r) * n := by ring
      _ = a * n := by rw [this]
  have hexp_3 : (a - 2 * r) * n + r * n + r * n = a * n := hexp_n
  have h3_le' : (3 : ℝ) ^ ((a - 2 * r) * n + r * n) ≤ (3 : ℝ) ^ (a * n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [zpow_neg, zpow_natCast]
  have hsimp :
      (((n : ℝ) / 3) ^ ((a - 2 * r) * n) * (((r : ℝ) * (n : ℝ)) / 3) ^ (r * n) *
          ((r : ℝ) * (n : ℝ)) ^ (r * n)) /
        (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1)) =
      ((r : ℝ) ^ (2 * r * n) * (n : ℝ) ^ (a * n)) /
        ((3 : ℝ) ^ ((a - 2 * r) * n + r * n) * (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1))) := by
    simp_rw [div_pow, mul_pow]
    have hpow_n : (n : ℝ) ^ ((a - 2 * r) * n) * (n : ℝ) ^ (r * n) * (n : ℝ) ^ (r * n) =
        (n : ℝ) ^ (a * n) := by rw [← pow_add, ← pow_add, hexp_n]
    have hpow_r : (r : ℝ) ^ (r * n) * (r : ℝ) ^ (r * n) = (r : ℝ) ^ (2 * r * n) := by
      rw [← pow_add]; congr 1; ring
    have hpow_3 : (3 : ℝ) ^ ((a - 2 * r) * n) * (3 : ℝ) ^ (r * n) =
        (3 : ℝ) ^ ((a - 2 * r) * n + r * n) := by rw [← pow_add]
    field_simp
    rw [← hpow_3, ← hpow_n, ← hpow_r]; ring
  rw [hsimp]
  have hden_eq : (((r : ℝ) + 2) * (n : ℝ)) ^ (a * (n + 1)) =
      (((r : ℝ) + 2) * (n : ℝ)) ^ a * ((r : ℝ) + 2) ^ (a * n) * (n : ℝ) ^ (a * n) := by
    have h1 : a * (n + 1) = a + a * n := by ring
    rw [h1, pow_add, mul_pow ((r : ℝ) + 2) (n : ℝ) (a * n)]; ring
  rw [hden_eq]
  have htarget_eq' : ((((r : ℝ) + 2) * (n : ℝ)) ^ a)⁻¹ *
      ((r : ℝ) ^ (2 * r) / ((3 : ℝ) * ((r : ℝ) + 2)) ^ a) ^ n =
      ((r : ℝ) ^ (2 * r * n) * (n : ℝ) ^ (a * n)) /
      ((3 : ℝ) ^ (a * n) * ((((r : ℝ) + 2) * (n : ℝ)) ^ a * ((r : ℝ) + 2) ^ (a * n) *
        (n : ℝ) ^ (a * n))) := by
    rw [div_pow, ← pow_mul, ← pow_mul, mul_pow (3 : ℝ) ((r : ℝ) + 2) (a * n)]
    have hn_ne : (n : ℝ) ^ (a * n) ≠ 0 := by positivity
    field_simp [hn_ne]
  rw [htarget_eq']
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right h3_le' (by positivity)

lemma S_BR_upper_bound {a r n : ℕ} (hr : 1 ≤ r) (ha : 2 * r + 2 ≤ a) (ha_odd : Odd a)
    (hn : Even n) (hn1 : 1 ≤ n) :
    S_BR a r n ≤ 2 * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n := by
  have hterm : ∀ m : ℕ, (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ) ≤
      (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n *
        ((1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    intro m
    by_cases hm : m + 1 ≤ r * n
    · unfold R_rat; push_cast
      have hmem : m + 1 ∈ Finset.Icc 1 (r * n) := by simp only [Finset.mem_Icc]; omega
      have hzero : ∏ j ∈ Finset.Icc 1 (r * n), ((m : ℝ) + 1 - (j : ℝ)) = 0 :=
        Finset.prod_eq_zero hmem (by push_cast; ring)
      rw [hzero, mul_zero, zero_mul, zero_div]
      positivity
    · set k := m + 1
      have hkrn : r * n < k := by omega
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hrn_pos : (0 : ℝ) < (r : ℝ) * (n : ℝ) := by positivity
      have hrn_le_k : (r : ℝ) * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkrn.le
      unfold R_rat; push_cast
      have hcast_k : (m : ℝ) + 1 = (k : ℝ) := by simp [k]
      simp_rw [hcast_k]
      have hfac : (n.factorial : ℝ) ^ (a - 2 * r) ≤ (n : ℝ) ^ ((a - 2 * r) * n) := by
        rw [mul_comm (a - 2 * r) n, pow_mul]
        exact pow_le_pow_left₀ (by positivity) (factorial_le_pow_self n) _
      have hp1 : ∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) - (j : ℝ)) ≤ (k : ℝ) ^ (r * n) := by
        have h1 : ∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) - (j : ℝ)) ≤
            ∏ _j ∈ Finset.Icc 1 (r * n), (k : ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            have : (j : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast le_trans (Finset.mem_Icc.mp hj).2 hkrn.le
            linarith
          · intro j _; linarith [Nat.cast_nonneg (α := ℝ) j]
        simpa [Finset.prod_const, Nat.card_Icc] using h1
      have hp2 : ∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) + (n : ℝ) + (j : ℝ)) ≤
          (4 * (k : ℝ)) ^ (r * n) := by
        have h1 : ∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) + (n : ℝ) + (j : ℝ)) ≤
            ∏ _j ∈ Finset.Icc 1 (r * n), (4 * (k : ℝ)) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro j hj
          have hj_le : (j : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast le_trans (Finset.mem_Icc.mp hj).2 hkrn.le
          have hn_le : (n : ℝ) ≤ (k : ℝ) := by
            have : n ≤ r * n := Nat.le_mul_of_pos_left n (by omega)
            exact_mod_cast le_trans this hkrn.le
          linarith
        simpa [Finset.prod_const, Nat.card_Icc] using h1
      have hden : (k : ℝ) ^ (a * (n + 1)) ≤
          (∏ l ∈ Finset.range (n + 1), ((k : ℝ) + (l : ℝ))) ^ a := by
        have h1 : ∏ _l ∈ Finset.range (n + 1), (k : ℝ) ≤
            ∏ l ∈ Finset.range (n + 1), ((k : ℝ) + (l : ℝ)) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro l _; linarith [Nat.cast_nonneg (α := ℝ) l]
        rw [Finset.prod_const, Finset.card_range] at h1
        calc (k : ℝ) ^ (a * (n + 1)) = ((k : ℝ) ^ (n + 1)) ^ a := by rw [← pow_mul, mul_comm]
          _ ≤ (∏ l ∈ Finset.range (n + 1), ((k : ℝ) + (l : ℝ))) ^ a :=
            pow_le_pow_left₀ (by positivity) h1 a
      have hnum_le : (n.factorial : ℝ) ^ (a - 2 * r) *
          (∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) - (j : ℝ))) *
          (∏ j ∈ Finset.Icc 1 (r * n), ((k : ℝ) + (n : ℝ) + (j : ℝ))) ≤
          (n : ℝ) ^ ((a - 2 * r) * n) * (k : ℝ) ^ (r * n) * (4 * (k : ℝ)) ^ (r * n) := by
        apply mul_le_mul
        · exact mul_le_mul hfac hp1
            (Finset.prod_nonneg fun j hj => by
              have : (j : ℝ) ≤ (k : ℝ) := by
                exact_mod_cast le_trans (Finset.mem_Icc.mp hj).2 hkrn.le
              linarith)
            (by positivity)
        · exact hp2
        · exact Finset.prod_nonneg fun _ _ => by positivity
        · positivity
      have hstep1 := div_le_div₀ (by positivity) hnum_le (by positivity : (0 : ℝ) < (k : ℝ) ^ (a * (n + 1))) hden
      refine le_trans hstep1 ?_
      -- Simplify (n^((a-2r)n) * k^(rn) * (4k)^(rn)) / k^(a(n+1))
      have hpow_k : (k : ℝ) ^ (a * (n + 1)) =
          (k : ℝ) ^ (2 * r * n) * (k : ℝ) ^ ((a - 2 * r) * n) * (k : ℝ) ^ (a - 2) * (k : ℝ) ^ 2 := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        have h1 : 2 * r * n + (a - 2 * r) * n = a * n := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
        have h2 : a - 2 + 2 = a := by omega
        linarith [show a * (n + 1) = a * n + a by ring]
      have hk_ge_1 : (1 : ℝ) ≤ (k : ℝ) ^ (a - 2) :=
        one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
      have hk_ge_rn : ((r : ℝ) * (n : ℝ)) ^ ((a - 2 * r) * n) ≤ (k : ℝ) ^ ((a - 2 * r) * n) :=
        pow_le_pow_left₀ (by positivity) hrn_le_k _
      have hden_low : (k : ℝ) ^ (2 * r * n) * ((r : ℝ) * (n : ℝ)) ^ ((a - 2 * r) * n) * (k : ℝ) ^ 2 ≤
          (k : ℝ) ^ (a * (n + 1)) := by
        rw [hpow_k]
        have h1 : (k : ℝ) ^ (2 * r * n) * ((r : ℝ) * (n : ℝ)) ^ ((a - 2 * r) * n) * 1 * (k : ℝ) ^ 2 ≤
            (k : ℝ) ^ (2 * r * n) * (k : ℝ) ^ ((a - 2 * r) * n) * (k : ℝ) ^ (a - 2) * (k : ℝ) ^ 2 := by
          gcongr
        simpa using h1
      have hstep2 :
          (n : ℝ) ^ ((a - 2 * r) * n) * (k : ℝ) ^ (r * n) * (4 * (k : ℝ)) ^ (r * n) /
            (k : ℝ) ^ (a * (n + 1)) ≤
          (n : ℝ) ^ ((a - 2 * r) * n) * (k : ℝ) ^ (r * n) * (4 * (k : ℝ)) ^ (r * n) /
            ((k : ℝ) ^ (2 * r * n) * ((r : ℝ) * (n : ℝ)) ^ ((a - 2 * r) * n) * (k : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity)
          (by positivity : (0 : ℝ) < (k : ℝ) ^ (2 * r * n) * ((r : ℝ) * (n : ℝ)) ^ ((a - 2 * r) * n) * (k : ℝ) ^ 2)
          hden_low
      refine le_trans hstep2 ?_
      rw [mul_pow (4 : ℝ) (k : ℝ) (r * n), mul_pow (r : ℝ) (n : ℝ) ((a - 2 * r) * n)]
      have hr_pow : (r : ℝ) ^ (2 * r * n) * (r : ℝ) ^ ((a - 2 * r) * n) = (r : ℝ) ^ (a * n) := by
        rw [← pow_add, ← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
      have hk2r : (k : ℝ) ^ (r * n) * (k : ℝ) ^ (r * n) = (k : ℝ) ^ (2 * r * n) := by
        rw [← pow_add]; congr 1; ring
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
      have hne1 : (k : ℝ) ^ (2 * r * n) ≠ 0 := by positivity
      have hne2 : (n : ℝ) ^ ((a - 2 * r) * n) ≠ 0 := by positivity
      have hne3 : (r : ℝ) ^ ((a - 2 * r) * n) ≠ 0 := by positivity
      have hne4 : (r : ℝ) ^ (a * n) ≠ 0 := by positivity
      have hne5 : (k : ℝ) ^ 2 ≠ 0 := by positivity
      apply le_of_eq
      field_simp [hne1, hne2, hne3, hne4, hne5]
      rw [← hk2r, ← hr_pow]; ring
  have hsum_L : Summable (fun m : ℕ => (R_rat a r n ((m + 1 : ℕ) : ℚ) : ℝ)) :=
    (S_BR_hasSum_linear_form ha ha_odd hn).summable
  have hsum_R : Summable (fun m : ℕ =>
      (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n *
        ((1 : ℝ) / ((m : ℝ) + 1) ^ 2)) :=
    ((summable_one_div_nat_add_pow (j := 2) (by omega) 0).congr (fun m => by simp)).mul_left _
  calc S_BR a r n
      ≤ ∑' m : ℕ, (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n *
          ((1 : ℝ) / ((m : ℝ) + 1) ^ 2) := hsum_L.tsum_le_tsum hterm hsum_R
    _ = (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n *
          ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n * 2 :=
          mul_le_mul_of_nonneg_left sum_inv_sq_le_two (by positivity)
    _ = 2 * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ n := mul_comm _ _

/- Section 5: Dirichlet Simultaneous Approximation and Nesterenko Criterion -/

lemma dirichlet_simultaneous {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ M ^ k ∧
      ∃ v : Fin k → ℤ, ∀ i, |(u : ℝ) * α i - (v i : ℝ)| ≤ 1 / (M : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  let box : Fin (M ^ k + 1) → (Fin k → Fin M) := fun x i =>
    ⟨Int.toNat ⌊(M : ℝ) * Int.fract ((x.val : ℝ) * α i)⌋, by
      have hf0 : 0 ≤ Int.fract ((x.val : ℝ) * α i) := Int.fract_nonneg _
      have hf1 : Int.fract ((x.val : ℝ) * α i) < 1 := Int.fract_lt_one _
      have hmul_lt : (M : ℝ) * Int.fract ((x.val : ℝ) * α i) < (M : ℝ) := by nlinarith
      have hfl_lt : ⌊(M : ℝ) * Int.fract ((x.val : ℝ) * α i)⌋ < (M : ℤ) :=
        Int.floor_lt.mpr (by exact_mod_cast hmul_lt)
      have hfl_nn : 0 ≤ ⌊(M : ℝ) * Int.fract ((x.val : ℝ) * α i)⌋ :=
        Int.floor_nonneg.mpr (by positivity)
      omega⟩
  have hcard : Fintype.card (Fin k → Fin M) < Fintype.card (Fin (M ^ k + 1)) := by
    simp [Fintype.card_fun, Fintype.card_fin]
  obtain ⟨x, y, hxy, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  have horder : x.val < y.val ∨ y.val < x.val := by
    have : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    omega
  suffices hgen : ∀ a b : Fin (M ^ k + 1), a.val < b.val → box a = box b →
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ M ^ k ∧
        ∃ v : Fin k → ℤ, ∀ i, |(u : ℝ) * α i - (v i : ℝ)| ≤ 1 / (M : ℝ) by
    rcases horder with hlt | hlt
    · exact hgen x y hlt hbox
    · exact hgen y x hlt hbox.symm
  intro a b hab heq
  refine ⟨b.val - a.val, by omega, by omega,
    fun i => ⌊(b.val : ℝ) * α i⌋ - ⌊(a.val : ℝ) * α i⌋, fun i => ?_⟩
  have hsame : (box a i).val = (box b i).val := congr_arg (fun f => (f i).val) heq
  have hfl_eq : ⌊(M : ℝ) * Int.fract ((a.val : ℝ) * α i)⌋ =
      ⌊(M : ℝ) * Int.fract ((b.val : ℝ) * α i)⌋ := by
    have ha_nn : 0 ≤ ⌊(M : ℝ) * Int.fract ((a.val : ℝ) * α i)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hMpos.le (Int.fract_nonneg _))
    have hb_nn : 0 ≤ ⌊(M : ℝ) * Int.fract ((b.val : ℝ) * α i)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hMpos.le (Int.fract_nonneg _))
    dsimp [box] at hsame
    omega
  set q : ℤ := ⌊(M : ℝ) * Int.fract ((a.val : ℝ) * α i)⌋
  have ha1 : (q : ℝ) ≤ (M : ℝ) * Int.fract ((a.val : ℝ) * α i) := Int.floor_le _
  have ha2 : (M : ℝ) * Int.fract ((a.val : ℝ) * α i) < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hb1 : (q : ℝ) ≤ (M : ℝ) * Int.fract ((b.val : ℝ) * α i) := hfl_eq ▸ Int.floor_le _
  have hb2 : (M : ℝ) * Int.fract ((b.val : ℝ) * α i) < (q : ℝ) + 1 :=
    hfl_eq ▸ Int.lt_floor_add_one _
  have hdiff_eq : ((b.val - a.val : ℕ) : ℝ) * α i -
      ((⌊(b.val : ℝ) * α i⌋ - ⌊(a.val : ℝ) * α i⌋ : ℤ) : ℝ) =
      Int.fract ((b.val : ℝ) * α i) - Int.fract ((a.val : ℝ) * α i) := by
    rw [Nat.cast_sub hab.le, Int.cast_sub, Int.fract, Int.fract]
    ring
  rw [hdiff_eq, abs_le]
  constructor
  · have hmul : -1 ≤ (M : ℝ) * (Int.fract ((b.val : ℝ) * α i) - Int.fract ((a.val : ℝ) * α i)) := by
      linarith
    have hdiv : -(1 / (M : ℝ)) = (-1 : ℝ) / (M : ℝ) := by ring
    rw [hdiv, div_le_iff₀ hMpos]
    linarith
  · have hmul : (M : ℝ) * (Int.fract ((b.val : ℝ) * α i) - Int.fract ((a.val : ℝ) * α i)) ≤ 1 := by
      linarith
    exact (le_div_iff₀ hMpos).mpr (by linarith)

lemma irrational_dist_pos {θ : ℝ} (hθ : Irrational θ) (M0 : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℕ, 1 ≤ u → u ≤ M0 → ∀ z : ℤ, δ ≤ |(u : ℝ) * θ - (z : ℝ)| := by
  by_cases hM0 : M0 = 0
  · refine ⟨1, zero_lt_one, fun u hu1 hu2 => by omega⟩
  · let dist : ℕ → ℝ := fun u =>
      min (Int.fract ((u : ℝ) * θ)) (1 - Int.fract ((u : ℝ) * θ))
    have hdist_pos : ∀ u ∈ Finset.Icc 1 M0, 0 < dist u := by
      intro u hu
      have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
      have hne0 : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
      have hirr : Irrational ((u : ℝ) * θ) := by
        simpa using hθ.ratCast_mul hne0
      have hf_ne0 : Int.fract ((u : ℝ) * θ) ≠ 0 := by
        intro hf0
        have hfl : (u : ℝ) * θ = (⌊(u : ℝ) * θ⌋ : ℝ) := by
          linarith [Int.fract_add_floor ((u : ℝ) * θ)]
        exact hirr ⟨(⌊(u : ℝ) * θ⌋ : ℚ), by exact_mod_cast hfl.symm⟩
      have hf_pos : 0 < Int.fract ((u : ℝ) * θ) :=
        lt_of_le_of_ne (Int.fract_nonneg _) hf_ne0.symm
      have hf_lt1 : Int.fract ((u : ℝ) * θ) < 1 := Int.fract_lt_one _
      exact lt_min hf_pos (sub_pos.mpr hf_lt1)
    have hne : (Finset.Icc 1 M0).Nonempty := ⟨1, by simp only [Finset.mem_Icc]; omega⟩
    refine ⟨(Finset.Icc 1 M0).inf' hne dist, ?_, fun u hu1 hu2 z => ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact hdist_pos
    · have hle_d : (Finset.Icc 1 M0).inf' hne dist ≤ dist u :=
        Finset.inf'_le dist (by simp only [Finset.mem_Icc]; omega)
      refine le_trans hle_d ?_
      have hfl := Int.fract_add_floor ((u : ℝ) * θ)
      by_cases hz : z ≤ ⌊(u : ℝ) * θ⌋
      · have hzR : (z : ℝ) ≤ (⌊(u : ℝ) * θ⌋ : ℝ) := by exact_mod_cast hz
        have hnonneg : 0 ≤ (u : ℝ) * θ - (z : ℝ) := by linarith [Int.fract_nonneg ((u : ℝ) * θ)]
        rw [abs_of_nonneg hnonneg]
        exact le_trans (min_le_left _ _) (by linarith)
      · have hz1 : ⌊(u : ℝ) * θ⌋ + 1 ≤ z := by omega
        have hzR : (⌊(u : ℝ) * θ⌋ : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
        have hneg : (u : ℝ) * θ - (z : ℝ) ≤ 0 := by linarith [Int.fract_lt_one ((u : ℝ) * θ)]
        rw [abs_of_nonpos hneg]
        exact le_trans (min_le_right _ _) (by linarith)

lemma nesterenko_criterion {d : ℕ} (hd : 2 ≤ d) (ω : Fin d → ℝ)
    (hω0 : ω ⟨0, by omega⟩ = 1) (hω1 : Irrational (ω ⟨1, by omega⟩))
    {A1 A2 B c1 c2 C : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (hA12 : A1 ≤ A2) (hA2_lt : A2 < 1)
    (hB : 0 < B) (hc1 : 0 < c1) (hc2 : 0 < c2) (hC : 0 < C)
    (hcrit : B ^ (d - 1) * A2 < (A1 / A2) ^ (d - 1))
    (N0 : ℕ) (q : ℕ → Fin d → ℤ)
    (hq_bound : ∀ m ≥ N0, ∀ i, |(q m i : ℝ)| ≤ C * B ^ m)
    (hq_lin : ∀ m ≥ N0,
      c1 * A1 ^ m ≤ |∑ i : Fin d, (q m i : ℝ) * ω i| ∧
      |∑ i : Fin d, (q m i : ℝ) * ω i| ≤ c2 * A2 ^ m) : False := by
  have hd1 : 1 ≤ d - 1 := by omega
  have hA12_le1 : (A1 / A2) ^ (d - 1) ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hA2).mpr hA12)
  have hBA2_lt1 : B ^ (d - 1) * A2 < 1 := lt_of_lt_of_le hcrit hA12_le1
  -- Find M1 ≥ N0 so that for all m ≥ M1 both asymptotic inequalities hold
  set K_err : ℝ := ((d : ℝ) * C) ^ (d - 1) * (4 * c2 / A2)
  set K_low : ℝ := (c1 * A2 / (4 * c2)) ^ (d - 1)
  have hK_low_pos : 0 < K_low := by positivity
  have hlim1 : Filter.Tendsto (fun m : ℕ => K_err * (B ^ (d - 1) * A2) ^ m)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := K_err)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hBA2_lt1)
  have hratio_lt1 : (B ^ (d - 1) * A2) / (A1 / A2) ^ (d - 1) < 1 :=
    (div_lt_one (by positivity)).mpr hcrit
  have hlim2 : Filter.Tendsto
      (fun m : ℕ => K_err * ((B ^ (d - 1) * A2) / (A1 / A2) ^ (d - 1)) ^ m)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := K_err)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hratio_lt1)
  have hev1 : ∀ᶠ m in Filter.atTop, K_err * (B ^ (d - 1) * A2) ^ m < (1 / 4 : ℝ) ^ (d - 1) :=
    hlim1.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ m in Filter.atTop,
      K_err * ((B ^ (d - 1) * A2) / (A1 / A2) ^ (d - 1)) ^ m < K_low :=
    hlim2.eventually (gt_mem_nhds hK_low_pos)
  rw [Filter.eventually_atTop] at hev1 hev2
  obtain ⟨M1a, hM1a⟩ := hev1
  obtain ⟨M1b, hM1b⟩ := hev2
  set M1 := max N0 (max M1a M1b)
  -- Pick M0 large enough that any u > M0 satisfies u * c2 * A2 ^ M1 ≥ 1 / 4
  obtain ⟨M0, hM0⟩ := exists_nat_gt (1 / (4 * c2 * A2 ^ M1))
  -- Pick M large enough so Dirichlet's u must exceed M0
  obtain ⟨δ, hδ_pos, hδ⟩ := irrational_dist_pos hω1 M0
  obtain ⟨M, hM_gt⟩ := exists_nat_gt (max 1 (1 / δ))
  have hM1_ge : 1 ≤ M := by
    have : (1 : ℝ) < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM_gt
    exact_mod_cast this.le
  let α : Fin (d - 1) → ℝ := fun i => ω ⟨i.val + 1, by omega⟩
  obtain ⟨u, hu1, hu_le, v, hv⟩ := dirichlet_simultaneous hd1 α M hM1_ge
  have hu_gt : M0 < u := by
    by_contra hle
    push_neg at hle
    have h1 := hδ u hu1 hle (v ⟨0, by omega⟩)
    have h2 := hv ⟨0, by omega⟩
    dsimp [α] at h2
    have hM_inv : 1 / (M : ℝ) < δ := by
      have hgt : 1 / δ < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM_gt
      have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
      rw [div_lt_iff₀ hMpos]
      have := (div_lt_iff₀ hδ_pos).mp hgt
      linarith
    linarith
  -- Choose smallest m ≥ N0 such that u * c2 * A2 ^ m < 1 / 4
  have hex_m : ∃ m : ℕ, N0 ≤ m ∧ (u : ℝ) * c2 * A2 ^ m < 1 / 4 := by
    have hlim : Filter.Tendsto (fun m : ℕ => (u : ℝ) * c2 * A2 ^ m) Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (u : ℝ) * c2)).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hA2.le hA2_lt)
    have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨m0, hm0⟩ := hev
    exact ⟨max N0 m0, le_max_left _ _, hm0 _ (le_max_right _ _)⟩
  classical
  set m := Nat.find hex_m
  have hm_spec : N0 ≤ m ∧ (u : ℝ) * c2 * A2 ^ m < 1 / 4 := Nat.find_spec hex_m
  have hm_gt_M1 : M1 < m := by
    by_contra hle
    push_neg at hle
    have hpow : A2 ^ M1 ≤ A2 ^ m := pow_le_pow_of_le_one hA2.le hA2_lt.le hle
    have huM0 : (M0 : ℝ) < (u : ℝ) := by exact_mod_cast hu_gt
    have h1 : 1 / 4 < (M0 : ℝ) * c2 * A2 ^ M1 := by
      have hden : 0 < 4 * c2 * A2 ^ M1 := by positivity
      have := (div_lt_iff₀ hden).mp hM0
      linarith
    have h2 : (M0 : ℝ) * c2 * A2 ^ M1 ≤ (u : ℝ) * c2 * A2 ^ m := by
      have : (M0 : ℝ) * c2 * A2 ^ M1 ≤ (u : ℝ) * c2 * A2 ^ M1 := by
        nlinarith [mul_pos hc2 (pow_pos hA2 M1)]
      exact le_trans this (mul_le_mul_of_nonneg_left hpow (by positivity))
    linarith [hm_spec.2]
  have hm_ge_N0 : N0 ≤ m := hm_spec.1
  have hm_pos : 1 ≤ m := by omega
  have hm_pred : (1 / 4 : ℝ) ≤ (u : ℝ) * c2 * A2 ^ (m - 1) := by
    by_contra hlt
    push_neg at hlt
    have hmin := Nat.find_min hex_m (show m - 1 < m by omega)
    exact hmin ⟨by omega, hlt⟩
  -- Define full integer vector uvec : Fin d → ℤ with uvec 0 = u, uvec (i+1) = v i
  let uvec : Fin d → ℤ := fun i =>
    if hi : i.val = 0 then (u : ℤ) else v ⟨i.val - 1, by omega⟩
  set S_int : ℤ := ∑ i : Fin d, q m i * uvec i
  set L : ℝ := ∑ i : Fin d, (q m i : ℝ) * ω i
  have hdiff_bound : |(S_int : ℝ) - (u : ℝ) * L| ≤ (d : ℝ) * C * B ^ m / (M : ℝ) := by
    have heq : (S_int : ℝ) - (u : ℝ) * L =
        ∑ i : Fin d, (q m i : ℝ) * ((uvec i : ℝ) - (u : ℝ) * ω i) := by
      simp only [S_int, L, Int.cast_sum, Int.cast_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i : Fin d,
        |(q m i : ℝ) * ((uvec i : ℝ) - (u : ℝ) * ω i)| ≤ C * B ^ m / (M : ℝ) := by
      intro i
      rw [abs_mul]
      have happrox : |(uvec i : ℝ) - (u : ℝ) * ω i| ≤ 1 / (M : ℝ) := by
        have hi_lt : i.val < d := i.isLt
        by_cases hi : i.val = 0
        · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
          rw [hi0]
          simp only [uvec, ↓reduceDIte, Int.cast_natCast, hω0, mul_one, sub_self, abs_zero]
          positivity
        · simp only [uvec, dif_neg hi]
          have hvi := hv ⟨i.val - 1, by omega⟩
          have hi_eq : (⟨(i.val - 1) + 1, by omega⟩ : Fin d) = i :=
            Fin.ext (show (i.val - 1) + 1 = i.val by omega)
          dsimp [α] at hvi
          rw [hi_eq] at hvi
          rwa [abs_sub_comm]
      calc |(q m i : ℝ)| * |(uvec i : ℝ) - (u : ℝ) * ω i|
          ≤ (C * B ^ m) * (1 / (M : ℝ)) :=
            mul_le_mul (hq_bound m hm_ge_N0 i) happrox (abs_nonneg _) (by positivity)
        _ = C * B ^ m / (M : ℝ) := by ring
    calc ∑ i : Fin d, |(q m i : ℝ) * ((uvec i : ℝ) - (u : ℝ) * ω i)|
        ≤ ∑ _i : Fin d, C * B ^ m / (M : ℝ) := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * C * B ^ m / (M : ℝ) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  -- Bound M^(d-1) from below using u ≤ M^(d-1) and u * c2 * A2^(m-1) ≥ 1/4
  have hM_pow_low : 1 / (4 * c2 * A2 ^ (m - 1)) ≤ (M : ℝ) ^ (d - 1) := by
    have hu_leR : (u : ℝ) ≤ (M : ℝ) ^ (d - 1) := by exact_mod_cast hu_le
    have h1 : 1 / (4 * c2 * A2 ^ (m - 1)) ≤ (u : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact le_trans h1 hu_leR
  have herr_pow : ((d : ℝ) * C * B ^ m / (M : ℝ)) ^ (d - 1) ≤
      K_err * (B ^ (d - 1) * A2) ^ m := by
    rw [div_pow, mul_pow, ← pow_mul, mul_comm m (d - 1), pow_mul]
    have hA2_eq : A2 ^ m = A2 * A2 ^ (m - 1) := by
      have : m = (m - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have hinv : 1 / (M : ℝ) ^ (d - 1) ≤ 4 * c2 * A2 ^ (m - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have hpos : (0 : ℝ) < 4 * c2 * A2 ^ (m - 1) := by positivity
      have := (div_le_iff₀ hpos).mp hM_pow_low
      linarith
    have hdiv_le : ((d : ℝ) * C) ^ (d - 1) * (B ^ (d - 1)) ^ m / (M : ℝ) ^ (d - 1) ≤
        ((d : ℝ) * C) ^ (d - 1) * (B ^ (d - 1)) ^ m * (4 * c2 * A2 ^ (m - 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    refine le_trans hdiv_le (le_of_eq ?_)
    dsimp [K_err]
    rw [mul_pow (B ^ (d - 1)) A2 m, hA2_eq]
    field_simp [hA2.ne']
  -- Deduce |(S_int : ℝ) - u * L| < 1 / 4, hence S_int = 0
  have herr_lt : |(S_int : ℝ) - (u : ℝ) * L| < 1 / 4 := by
    have hpow_lt : ((d : ℝ) * C * B ^ m / (M : ℝ)) ^ (d - 1) < (1 / 4 : ℝ) ^ (d - 1) :=
      lt_of_le_of_lt herr_pow (hM1a m (by omega))
    have hbase_lt : (d : ℝ) * C * B ^ m / (M : ℝ) < 1 / 4 := by
      by_contra hge
      push_neg at hge
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hge (d - 1)
      linarith
    exact lt_of_le_of_lt hdiff_bound hbase_lt
  have huL_lt : |(u : ℝ) * L| < 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg u)]
    calc (u : ℝ) * |L| ≤ (u : ℝ) * (c2 * A2 ^ m) :=
          mul_le_mul_of_nonneg_left (hq_lin m hm_ge_N0).2 (Nat.cast_nonneg u)
      _ = (u : ℝ) * c2 * A2 ^ m := by ring
      _ < 1 / 4 := hm_spec.2
  have hS_zero : S_int = 0 := by
    have habs : |(S_int : ℝ)| < 1 / 2 := by
      have htri : |(S_int : ℝ)| ≤ |(S_int : ℝ) - (u : ℝ) * L| + |(u : ℝ) * L| := by
        simpa [sub_add_cancel] using abs_add_le ((S_int : ℝ) - (u : ℝ) * L) ((u : ℝ) * L)
      linarith
    have hlt1 : |(S_int : ℝ)| < 1 := by linarith
    have hlt1Z : |S_int| < 1 := by exact_mod_cast hlt1
    exact Int.abs_lt_one_iff.mp hlt1Z
  -- Now lower bound |u * L| = |S_int - u * L| and derive contradiction!
  have hlow_uL : (c1 * A2 / (4 * c2)) * (A1 / A2) ^ m ≤ (d : ℝ) * C * B ^ m / (M : ℝ) := by
    have hA2_eq : A2 ^ m = A2 * A2 ^ (m - 1) := by
      have : m = (m - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have hu_low : 1 / (4 * c2 * A2 ^ (m - 1)) ≤ (u : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h1 : (c1 * A2 / (4 * c2)) * (A1 / A2) ^ m ≤ |(u : ℝ) * L| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg u)]
      calc (c1 * A2 / (4 * c2)) * (A1 / A2) ^ m
          = (1 / (4 * c2 * A2 ^ (m - 1))) * (c1 * A1 ^ m) := by
            rw [div_pow, hA2_eq]
            field_simp [hA2.ne', hc2.ne']
        _ ≤ (u : ℝ) * |L| :=
            mul_le_mul hu_low (hq_lin m hm_ge_N0).1 (by positivity) (Nat.cast_nonneg u)
    have h2 : |(u : ℝ) * L| = |(S_int : ℝ) - (u : ℝ) * L| := by
      simp [hS_zero]
    exact le_trans h1 (h2 ▸ hdiff_bound)
  have hlow_pow : K_low * ((A1 / A2) ^ (d - 1)) ^ m ≤ K_err * (B ^ (d - 1) * A2) ^ m := by
    have h1 := pow_le_pow_left₀ (by positivity) hlow_uL (d - 1)
    rw [mul_pow, ← pow_mul, mul_comm m (d - 1), pow_mul] at h1
    exact le_trans h1 herr_pow
  have hcontra := hM1b m (by omega)
  rw [div_pow, ← mul_div_assoc] at hcontra
  have hpos_pow : 0 < ((A1 / A2) ^ (d - 1)) ^ m := by positivity
  have hcontra' := (div_lt_iff₀ hpos_pow).mp hcontra
  linarith

/- Section 6: Finite-dimensional reduction and main theorem -/

lemma basis_starting_with_one {K : ℕ} {W : Submodule ℚ ℝ}
    (h1 : (1 : ℝ) ∈ W) (hdim_le : Module.finrank ℚ W ≤ K + 1)
    (hdim_ge : 2 ≤ Module.finrank ℚ W) :
    ∃ (d : ℕ) (hd2 : 2 ≤ d) (hdK : d ≤ K + 1) (ω : Fin d → ℝ),
      ω ⟨0, by omega⟩ = 1 ∧
      Irrational (ω ⟨1, by omega⟩) ∧
      ∀ w ∈ W, ∃ coeffs : Fin d → ℚ, w = ∑ i : Fin d, (coeffs i : ℝ) * ω i := by
  haveI : FiniteDimensional ℚ W := by
    by_cases hfin : FiniteDimensional ℚ W
    · exact hfin
    · exfalso
      have h0 : Module.finrank ℚ W = 0 := Module.finrank_of_infinite_dimensional hfin
      omega
  set d := Module.finrank ℚ W
  let v0 : W := ⟨1, h1⟩
  have hv0_ne : v0 ≠ 0 := by intro h; have := congr_arg Subtype.val h; norm_num at this
  let U : Submodule ℚ W := Submodule.span ℚ ({v0} : Set W)
  obtain ⟨U', hcompl⟩ := Submodule.exists_isCompl U
  have hU_dim : Module.finrank ℚ U = 1 := finrank_span_singleton hv0_ne
  have hU'_dim : Module.finrank ℚ U' = d - 1 := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  let bU' : Module.Basis (Fin (d - 1)) ℚ U' :=
    (Module.finBasis ℚ U').reindex (finCongr hU'_dim)
  let ω : Fin d → ℝ := fun i =>
    if hi : i.val = 0 then (1 : ℝ) else ((bU' ⟨i.val - 1, by omega⟩ : U') : W).val
  refine ⟨d, hdim_ge, hdim_le, ω, by simp [ω], ?_, ?_⟩
  · -- Show ω 1 is irrational
    intro ⟨q, hq⟩
    have hmemU : (q • v0 : W) ∈ U := Submodule.smul_mem U q (Submodule.subset_span rfl)
    have hmemU' : ((bU' ⟨0, by omega⟩ : U') : W) ∈ U' := (bU' ⟨0, by omega⟩).property
    have heq_W : ((bU' ⟨0, by omega⟩ : U') : W) = q • v0 := by
      apply Subtype.ext
      change (bU' ⟨0, by omega⟩ : W).val = q • (1 : ℝ)
      have hω1_eq : ω ⟨1, by omega⟩ = ((bU' ⟨0, by omega⟩ : U') : W).val := by simp [ω]
      rw [← hω1_eq, ← hq, Rat.smul_def, mul_one]
    have hzero_W : ((bU' ⟨0, by omega⟩ : U') : W) = 0 := by
      have hinf : ((bU' ⟨0, by omega⟩ : U') : W) ∈ U ⊓ U' := ⟨heq_W ▸ hmemU, hmemU'⟩
      rw [hcompl.inf_eq_bot] at hinf
      exact (Submodule.mem_bot ℚ).mp hinf
    have hzero_U' : bU' ⟨0, by omega⟩ = 0 := Subtype.ext hzero_W
    exact bU'.ne_zero ⟨0, by omega⟩ hzero_U'
  · -- Show every w ∈ W is a ℚ-linear combination of ω
    intro w hw
    have hmem_sup : (⟨w, hw⟩ : W) ∈ U ⊔ U' := by rw [hcompl.sup_eq_top]; trivial
    rcases Submodule.mem_sup.mp hmem_sup with ⟨u, hu, u', hu', huu'⟩
    rcases Submodule.mem_span_singleton.mp hu with ⟨c0, hc0⟩
    let c' : Fin (d - 1) → ℚ := bU'.repr ⟨u', hu'⟩
    let coeffs : Fin d → ℚ := fun i =>
      if hi : i.val = 0 then c0 else c' ⟨i.val - 1, by omega⟩
    refine ⟨coeffs, ?_⟩
    have hu'_eq : (⟨u', hu'⟩ : U') = ∑ j : Fin (d - 1), c' j • bU' j := (bU'.sum_repr _).symm
    have hw_val : w = (c0 : ℝ) * 1 + ∑ j : Fin (d - 1), (c' j : ℝ) * ((bU' j : U') : W).val := by
      have h1' := congr_arg Subtype.val huu'.symm
      dsimp at h1'
      rw [h1', ← hc0]
      have hu'_val : u'.val = ∑ j : Fin (d - 1), (c' j : ℝ) * ((bU' j : U') : W).val := by
        have h2 := congr_arg (fun x : U' => (x : W).val) hu'_eq
        simpa [AddSubmonoidClass.coe_finset_sum, Rat.smul_def] using h2
      rw [hu'_val]
      simp [v0, Rat.smul_def]
    rw [hw_val]
    have hsplit : ∑ i : Fin d, (coeffs i : ℝ) * ω i =
        (coeffs ⟨0, by omega⟩ : ℝ) * ω ⟨0, by omega⟩ +
        ∑ j : Fin (d - 1), (coeffs ⟨j.val + 1, by omega⟩ : ℝ) * ω ⟨j.val + 1, by omega⟩ := by
      have h0 : (Finset.univ : Finset (Fin d)) = insert (⟨0, by omega⟩ : Fin d)
          (Finset.univ.image (fun j : Fin (d - 1) => (⟨j.val + 1, by omega⟩ : Fin d))) := by
        ext i
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_iff]
        have hi_lt : i.val < d := i.isLt
        by_cases hi : i.val = 0
        · left; exact Fin.ext hi
        · right; exact ⟨⟨i.val - 1, by omega⟩, trivial,
            Fin.ext (show (i.val - 1) + 1 = i.val by omega)⟩
      have hnot : (⟨0, by omega⟩ : Fin d) ∉
          Finset.univ.image (fun j : Fin (d - 1) => (⟨j.val + 1, by omega⟩ : Fin d)) := by
        simp [Fin.ext_iff]
      conv_lhs => rw [h0, Finset.sum_insert hnot]
      congr 1
      rw [Finset.sum_image]
      intro j1 _ j2 _ h
      have hval : j1.val + 1 = j2.val + 1 := congr_arg Fin.val h
      exact Fin.ext (by omega)
    rw [hsplit]
    simp only [coeffs, ω, ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      Nat.add_sub_cancel]

lemma rivoal_aux (K r a : ℕ)
    (hrat_ge : ∀ k ≥ K, ∃ q : ℚ, (q : ℝ) = zetaReal (2 * k + 1))
    (hr_big : 64 * 17160 ^ K + 100 ≤ r)
    (ha_eq : a = 2 * r ^ 3 + 1) : False := by
  have hr64 : 64 ≤ r := by omega
  have hr1 : 1 ≤ r := by omega
  have ha_odd : Odd a := ⟨r ^ 3, ha_eq⟩
  have ha_ge : 2 * r + 2 ≤ a := by
    have h1 : r + 1 ≤ r ^ 3 := by
      calc r + 1 ≤ r * r := by nlinarith
        _ ≤ r * r * r := by nlinarith
        _ = r ^ 3 := by ring
    omega
  -- Define finite-dimensional ℚ-subspace W spanned by 1 and {zetaReal (2k+1) | k < K}
  let gens : Finset ℝ := insert (1 : ℝ) ((Finset.range K).image (fun k => zetaReal (2 * k + 1)))
  let W : Submodule ℚ ℝ := Submodule.span ℚ (gens : Set ℝ)
  have h1_mem : (1 : ℝ) ∈ W := Submodule.subset_span (by simp [gens])
  have hzeta_mem : ∀ j ∈ (Finset.Icc 3 a).filter Odd, zetaReal j ∈ W := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    rcases hj.2 with ⟨k, rfl⟩
    by_cases hk : k < K
    · apply Submodule.subset_span
      simp only [gens, Finset.coe_insert, Finset.coe_image, Finset.coe_range, Set.mem_insert_iff,
        Set.mem_image, Set.mem_Iio]
      right; exact ⟨k, hk, rfl⟩
    · obtain ⟨q, hq⟩ := hrat_ge k (by omega)
      rw [← hq]
      have : (q : ℝ) = q • (1 : ℝ) := by rw [Rat.smul_def, mul_one]
      rw [this]
      exact W.smul_mem q h1_mem
  have hW_fin : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ gens.finite_toSet
  have hdim_le : Module.finrank ℚ W ≤ K + 1 := by
    have h1 := finrank_span_le_card (R := ℚ) (M := ℝ) (gens : Set ℝ)
    have hcard : gens.card ≤ K + 1 := by
      calc gens.card ≤ ((Finset.range K).image (fun k => zetaReal (2 * k + 1))).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (Finset.range K).card + 1 := by gcongr; exact Finset.card_image_le
        _ = K + 1 := by rw [Finset.card_range]
    exact le_trans (by simpa [W] using h1) hcard
  have hdim_pos : 1 ≤ Module.finrank ℚ W := by
    have hne : Nontrivial W := ⟨⟨⟨1, h1_mem⟩, 0, by intro h; have := congr_arg Subtype.val h; norm_num at this⟩⟩
    exact Module.finrank_pos
  -- Define asymptotic constants A1, A2, B (for n = 2*m we square them!)
  set A1_step : ℝ := (r : ℝ) ^ (2 * r) / ((4 : ℝ) * ((r : ℝ) + 2)) ^ a
  set A2_step : ℝ := ((32 : ℝ) ^ a * (4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a
  set B_step : ℝ := (65 : ℝ) ^ a * (2 : ℝ) ^ (2 * r ^ 2 + 2 * r)
  have hA1_pos : 0 < A1_step := by positivity
  have hA2_pos : 0 < A2_step := by positivity
  have hB_pos : 0 < B_step := by positivity
  -- Verify A1_step ≤ A2_step and A2_step < 1 and key parameter inequalities
  have h2r_pow_le : ((2 : ℝ) * (r : ℝ)) ^ (2 * r) ≤ (2 : ℝ) ^ a := by
    have h2r_le : 2 * r ≤ 2 ^ r := by
      have : ∀ t : ℕ, 2 ≤ t → 2 * t ≤ 2 ^ t := by
        intro t ht
        induction t with
        | zero => omega
        | succ k ih =>
          cases k with
          | zero => omega
          | succ k' =>
            cases k' with
            | zero => norm_num
            | succ m =>
              have hm := ih (by omega)
              have hpow : 2 ^ (m + 2 + 1) = 2 * 2 ^ (m + 2) := by rw [pow_succ']
              have h2le : 2 ≤ 2 ^ (m + 2) := by
                have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 1 ≤ m + 2 by omega)
                simpa using this
              omega
      exact this r (by omega)
    have h1 : (2 * r) ^ (2 * r) ≤ (2 ^ r) ^ (2 * r) := Nat.pow_le_pow_left h2r_le _
    have h2 : (2 ^ r) ^ (2 * r) = 2 ^ (2 * r ^ 2) := by rw [← pow_mul]; congr 1; ring
    have h3 : 2 * r ^ 2 ≤ a := by
      have : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hnat : (2 * r) ^ (2 * r) ≤ 2 ^ a :=
      le_trans h1 (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
    exact_mod_cast hnat
  have hA2_le_simple : A2_step ≤ ((64 : ℝ) / (r : ℝ)) ^ a := by
    dsimp [A2_step]
    have h4r : (4 : ℝ) ^ r * (r : ℝ) ^ (2 * r) = ((2 : ℝ) * (r : ℝ)) ^ (2 * r) := by
      rw [mul_pow, pow_mul (2 : ℝ) 2 r]; norm_num
    rw [mul_assoc, h4r, div_pow]
    have h64 : (64 : ℝ) ^ a = (32 : ℝ) ^ a * (2 : ℝ) ^ a := by rw [← mul_pow]; norm_num
    rw [h64]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2r_pow_le (by positivity))
      (by positivity)
  have hA2_lt1 : A2_step < 1 := by
    refine lt_of_le_of_lt hA2_le_simple ?_
    have hlt : (64 : ℝ) / (r : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast (show 64 < r by omega))
    exact pow_lt_one₀ (by positivity) hlt (by omega)
  have hA1_le_A2 : A1_step ≤ A2_step := by
    dsimp [A1_step, A2_step]
    have hr_le : (r : ℝ) ≤ (4 : ℝ) * ((r : ℝ) + 2) := by linarith
    have hden : (r : ℝ) ^ a ≤ ((4 : ℝ) * ((r : ℝ) + 2)) ^ a := pow_le_pow_left₀ (by positivity) hr_le a
    have hnum : (r : ℝ) ^ (2 * r) ≤ (32 : ℝ) ^ a * (4 : ℝ) ^ r * (r : ℝ) ^ (2 * r) := by
      have h1 : (1 : ℝ) ≤ (32 : ℝ) ^ a * (4 : ℝ) ^ r :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 32))
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) r) (2 * r)]
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  -- Asymptotic threshold N_asymp for even n = 2*m ≥ N_asymp
  have hex_N1 : ∃ N1 : ℕ, ∀ n ≥ N1, (((r : ℝ) + 2) * (n : ℝ)) ^ a ≤ (4 / 3 : ℝ) ^ (a * n) := by
    have hlim : Filter.Tendsto (fun n : ℕ => (((r : ℝ) + 2) * (n : ℝ)) / (4 / 3 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (4 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) := by
        have := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4 / 3)
        simpa using this
      simpa [mul_div_assoc] using (tendsto_const_nhds (x := (r : ℝ) + 2)).mul h1
    have hev := hlim.eventually (gt_mem_nhds zero_lt_one)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N1, hN1⟩ := hev
    refine ⟨N1, fun n hn => ?_⟩
    have hlt := (div_lt_one (by positivity)).mp (hN1 n hn)
    calc (((r : ℝ) + 2) * (n : ℝ)) ^ a ≤ ((4 / 3 : ℝ) ^ n) ^ a :=
          pow_le_pow_left₀ (by positivity) hlt.le a
      _ = (4 / 3 : ℝ) ^ (a * n) := by rw [← pow_mul, mul_comm]
  have hex_N2 : ∃ N2 : ℕ, ∀ n ≥ N2,
      (a : ℝ) * ((n : ℝ) + 1) ^ 2 * (2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a ≤
      (65 / 64 : ℝ) ^ (a * n) := by
    have hlim : Filter.Tendsto
        (fun n : ℕ => ((a : ℝ) * ((n : ℝ) + 1) ^ 2 * (2 * (a : ℝ) * ((n : ℝ) + 1)) ^ a) /
          ((65 / 64 : ℝ) ^ a) ^ n)
        Filter.atTop (nhds 0) := by
      have hgt1 : (1 : ℝ) < (65 / 64 : ℝ) ^ a := one_lt_pow₀ (by norm_num) (by omega)
      have hpow := tendsto_pow_const_div_const_pow_of_one_lt (a + 2) hgt1
      have hshift : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (a + 2) / ((65 / 64 : ℝ) ^ a) ^ n)
          Filter.atTop (nhds 0) := by
        have h1 := hpow.comp (Filter.tendsto_add_atTop_nat 1)
        have h2 : Filter.Tendsto
            (fun n : ℕ => (((65 / 64 : ℝ) ^ a) * (((n + 1 : ℕ) : ℝ) ^ (a + 2) /
              ((65 / 64 : ℝ) ^ a) ^ (n + 1)))) Filter.atTop (nhds 0) := by
          simpa using (tendsto_const_nhds (x := (65 / 64 : ℝ) ^ a)).mul h1
        refine h2.congr fun n => ?_
        have hne : (65 / 64 : ℝ) ^ a ≠ 0 := by positivity
        rw [pow_succ' ((65 / 64 : ℝ) ^ a) n, Nat.cast_add, Nat.cast_one,
          ← mul_div_assoc, mul_div_mul_left _ _ hne]
      have hconst : Filter.Tendsto
          (fun n : ℕ => ((a : ℝ) * (2 * (a : ℝ)) ^ a) *
            (((n : ℝ) + 1) ^ (a + 2) / ((65 / 64 : ℝ) ^ a) ^ n))
          Filter.atTop (nhds 0) := by
        simpa using (tendsto_const_nhds (x := (a : ℝ) * (2 * (a : ℝ)) ^ a)).mul hshift
      refine hconst.congr fun n => ?_
      rw [mul_pow (2 * (a : ℝ)) ((n : ℝ) + 1) a, pow_add]
      ring
    have hev := hlim.eventually (gt_mem_nhds zero_lt_one)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N2, hN2⟩ := hev
    refine ⟨N2, fun n hn => ?_⟩
    have hlt := (div_lt_one (by positivity)).mp (hN2 n hn)
    rw [← pow_mul] at hlt
    exact hlt.le
  obtain ⟨N1, hN1⟩ := hex_N1
  obtain ⟨N2, hN2⟩ := hex_N2
  set N_big := max 2 (max N1 N2)
  -- Check cases: dim W = 1 vs dim W ≥ 2
  by_cases hdim2 : 2 ≤ Module.finrank ℚ W
  · -- Case d ≥ 2: use basis_starting_with_one and nesterenko_criterion
    obtain ⟨d, hd2, hdK, ω, hω0, hω1, hspan⟩ := basis_starting_with_one h1_mem hdim_le hdim2
    -- Express every zetaReal j (j ∈ Icc 3 a, odd) in basis ω
    have hcoeffs : ∀ j ∈ (Finset.Icc 3 a).filter Odd,
        ∃ coeffs : Fin d → ℚ, zetaReal j = ∑ i : Fin d, (coeffs i : ℝ) * ω i :=
      fun j hj => hspan _ (hzeta_mem j hj)
    classical
    let M_rat : ℕ → Fin d → ℚ := fun j =>
      if hj : j ∈ (Finset.Icc 3 a).filter Odd then (hcoeffs j hj).choose else 0
    have hM_spec : ∀ j ∈ (Finset.Icc 3 a).filter Odd,
        zetaReal j = ∑ i : Fin d, (M_rat j i : ℝ) * ω i := by
      intro j hj; simp only [M_rat, dif_pos hj]; exact (hcoeffs j hj).choose_spec
    -- Clear denominators of all M_rat j i
    let D_rat : ℕ := ∏ j ∈ (Finset.Icc 3 a).filter Odd, ∏ i : Fin d, (M_rat j i).den
    have hD_pos : 0 < D_rat := by
      apply Finset.prod_pos; intro j _; apply Finset.prod_pos; intro i _; exact (M_rat j i).pos
    have hM_int : ∀ j ∈ (Finset.Icc 3 a).filter Odd, ∀ i : Fin d,
        ∃ z : ℤ, (D_rat : ℚ) * M_rat j i = (z : ℚ) := by
      intro j hj i
      have hdvd : (M_rat j i).den ∣ D_rat :=
        dvd_trans (Finset.dvd_prod_of_mem (fun i' => (M_rat j i').den) (Finset.mem_univ i))
          (Finset.dvd_prod_of_mem (fun j' => ∏ i' : Fin d, (M_rat j' i').den) hj)
      rcases hdvd with ⟨q, hq⟩
      refine ⟨(q : ℤ) * (M_rat j i).num, ?_⟩
      have hqQ : (D_rat : ℚ) = ((M_rat j i).den : ℚ) * (q : ℚ) := by exact_mod_cast hq
      have hnum_den : ((M_rat j i).den : ℚ) * M_rat j i = ((M_rat j i).num : ℚ) := by
        set x := M_rat j i
        have hne : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
        conv_lhs => rhs; rw [← Rat.num_div_den x]
        exact mul_div_cancel₀ _ hne
      rw [hqQ]
      push_cast
      calc ((M_rat j i).den : ℚ) * (q : ℚ) * M_rat j i
          = (q : ℚ) * (((M_rat j i).den : ℚ) * M_rat j i) := by ring
        _ = (q : ℚ) * ((M_rat j i).num : ℚ) := by rw [hnum_den]
    let M_int : ℕ → Fin d → ℤ := fun j i =>
      if hj : j ∈ (Finset.Icc 3 a).filter Odd then (hM_int j hj i).choose else 0
    have hM_int_spec : ∀ j ∈ (Finset.Icc 3 a).filter Odd, ∀ i : Fin d,
        (M_int j i : ℝ) = (D_rat : ℝ) * (M_rat j i : ℝ) := by
      intro j hj i
      simp only [M_int, dif_pos hj]
      have h := congr_arg (Rat.cast (K := ℝ)) (hM_int j hj i).choose_spec
      push_cast at h; exact h.symm
    -- Upper bound constant C_mat for M_int
    set C_mat : ℝ := (D_rat : ℝ) + ∑ j ∈ (Finset.Icc 3 a).filter Odd, ∑ i : Fin d, |(M_int j i : ℝ)|
    have hC_mat_pos : 0 < C_mat := by
      have : (0 : ℝ) < (D_rat : ℝ) := by exact_mod_cast hD_pos
      have : (0 : ℝ) ≤ ∑ j ∈ (Finset.Icc 3 a).filter Odd, ∑ i : Fin d, |(M_int j i : ℝ)| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    -- Build sequence q : ℕ → Fin d → ℤ from n = 2 * m
    have hform : ∀ m : ℕ, ∃ qm : Fin d → ℤ,
        (D_rat : ℝ) * (((commonDenom (2 * m) : ℝ) ^ a) * S_BR a r (2 * m)) =
          ∑ i : Fin d, (qm i : ℝ) * ω i ∧
        (N_big ≤ 2 * m → ∀ i : Fin d, |(qm i : ℝ)| ≤ C_mat * (B_step ^ 2) ^ m) := by
      intro m
      obtain ⟨p0, p, heq, hp0_b, hp_b⟩ :=
        S_BR_integer_linear_form ha_ge ha_odd (even_two_mul m)
      let qm : Fin d → ℤ := fun i =>
        (if i.val = 0 then (D_rat : ℤ) * p0 else 0) +
        ∑ j ∈ (Finset.Icc 3 a).filter Odd, p j * M_int j i
      refine ⟨qm, ?_, ?_⟩
      · rw [heq, mul_add, Finset.mul_sum]
        have hsum_i : ∑ i : Fin d, (qm i : ℝ) * ω i =
            (D_rat : ℝ) * (p0 : ℝ) +
            ∑ j ∈ (Finset.Icc 3 a).filter Odd, (p j : ℝ) * ((D_rat : ℝ) * zetaReal j) := by
          simp only [qm, Int.cast_add, Int.cast_sum, Int.cast_mul, add_mul, Finset.sum_add_distrib]
          congr 1
          · rw [Finset.sum_eq_single ⟨0, by omega⟩]
            · simp [hω0]
            · intro i _ hi
              have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
              simp [hi0]
            · intro h; exact absurd (Finset.mem_univ _) h
          · simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [hM_spec j hj, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hM_int_spec j hj i]; ring
        rw [hsum_i]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring
      · intro hN i
        have h2m_bound : (commonDenom (2 * m) : ℝ) ^ a * (a : ℝ) * ((2 * m : ℕ) + 1 : ℝ) ^ 2 *
            ((2 * (a : ℝ) * (((2 * m : ℕ) : ℝ) + 1)) ^ a *
              (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m))) ≤ (B_step ^ 2) ^ m := by
          have hD_le : (commonDenom (2 * m) : ℝ) ^ a ≤ (32 : ℝ) ^ (a * (2 * m)) := by
            calc (commonDenom (2 * m) : ℝ) ^ a ≤ ((32 : ℝ) ^ (2 * m)) ^ a :=
                  pow_le_pow_left₀ (by positivity) (by exact_mod_cast commonDenom_le_pow (2 * m)) a
              _ = (32 : ℝ) ^ (a * (2 * m)) := by rw [← pow_mul, mul_comm]
          have hpoly := hN2 (2 * m) (by omega)
          have hstep : (commonDenom (2 * m) : ℝ) ^ a *
              ((a : ℝ) * (((2 * m : ℕ) : ℝ) + 1) ^ 2 * (2 * (a : ℝ) * (((2 * m : ℕ) : ℝ) + 1)) ^ a) *
              (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m)) ≤
              (32 : ℝ) ^ (a * (2 * m)) * (65 / 64 : ℝ) ^ (a * (2 * m)) *
              (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m)) := by
            gcongr
          refine le_trans (by linarith [show (commonDenom (2 * m) : ℝ) ^ a * (a : ℝ) *
              (((2 * m : ℕ) : ℝ) + 1) ^ 2 *
              ((2 * (a : ℝ) * (((2 * m : ℕ) : ℝ) + 1)) ^ a *
                (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m))) =
              (commonDenom (2 * m) : ℝ) ^ a *
              ((a : ℝ) * (((2 * m : ℕ) : ℝ) + 1) ^ 2 * (2 * (a : ℝ) * (((2 * m : ℕ) : ℝ) + 1)) ^ a) *
              (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m)) by ring]) (le_trans hstep (le_of_eq ?_))
          dsimp [B_step]
          rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
          have h2split : (2 : ℝ) ^ ((a + 2 * r ^ 2 + 2 * r) * (2 * m)) =
              (2 : ℝ) ^ (a * (2 * m)) * (2 : ℝ) ^ ((2 * r ^ 2 + 2 * r) * (2 * m)) := by
            rw [← pow_add]; congr 1; ring
          rw [h2split]
          have h65 : (32 : ℝ) ^ (a * (2 * m)) * (65 / 64 : ℝ) ^ (a * (2 * m)) *
              (2 : ℝ) ^ (a * (2 * m)) = (65 : ℝ) ^ (a * (2 * m)) := by
            rw [← mul_pow, ← mul_pow]; norm_num
          calc (32 : ℝ) ^ (a * (2 * m)) * (65 / 64 : ℝ) ^ (a * (2 * m)) *
                ((2 : ℝ) ^ (a * (2 * m)) * (2 : ℝ) ^ ((2 * r ^ 2 + 2 * r) * (2 * m)))
              = ((32 : ℝ) ^ (a * (2 * m)) * (65 / 64 : ℝ) ^ (a * (2 * m)) *
                  (2 : ℝ) ^ (a * (2 * m))) * (2 : ℝ) ^ ((2 * r ^ 2 + 2 * r) * (2 * m)) := by ring
            _ = (65 : ℝ) ^ (a * (2 * m)) * (2 : ℝ) ^ ((2 * r ^ 2 + 2 * r) * (2 * m)) := by rw [h65]
            _ = (65 : ℝ) ^ (a * (2 * m)) * (2 : ℝ) ^ ((2 * r ^ 2 + 2 * r) * (2 * m)) := rfl
        have hp0_le : |(p0 : ℝ)| ≤ (B_step ^ 2) ^ m := le_trans hp0_b (by simpa using h2m_bound)
        have hpj_le : ∀ j ∈ (Finset.Icc 3 a).filter Odd, |(p j : ℝ)| ≤ (B_step ^ 2) ^ m :=
          fun j hj => le_trans (hp_b j hj) (by simpa using h2m_bound)
        simp only [qm, Int.cast_add, Int.cast_sum, Int.cast_mul]
        refine le_trans (abs_add_le _ _) ?_
        have hpart1 : |((if i.val = 0 then (D_rat : ℤ) * p0 else 0 : ℤ) : ℝ)| ≤
            (D_rat : ℝ) * (B_step ^ 2) ^ m := by
          split_ifs
          · rw [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg D_rat)]
            exact mul_le_mul_of_nonneg_left hp0_le (Nat.cast_nonneg D_rat)
          · simp; positivity
        have hpart2 : |∑ j ∈ (Finset.Icc 3 a).filter Odd, (p j : ℝ) * (M_int j i : ℝ)| ≤
            (∑ j ∈ (Finset.Icc 3 a).filter Odd, ∑ i' : Fin d, |(M_int j i' : ℝ)|) *
              (B_step ^ 2) ^ m := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul]
          have hsingle : |(M_int j i : ℝ)| ≤ ∑ i' : Fin d, |(M_int j i' : ℝ)| :=
            Finset.single_le_sum (f := fun i' : Fin d => |(M_int j i' : ℝ)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          calc |(p j : ℝ)| * |(M_int j i : ℝ)|
              ≤ (B_step ^ 2) ^ m * (∑ i' : Fin d, |(M_int j i' : ℝ)|) :=
                mul_le_mul (hpj_le j hj) hsingle (abs_nonneg _) (by positivity)
            _ = (∑ i' : Fin d, |(M_int j i' : ℝ)|) * (B_step ^ 2) ^ m := mul_comm _ _
        calc _ ≤ (D_rat : ℝ) * (B_step ^ 2) ^ m +
              (∑ j ∈ (Finset.Icc 3 a).filter Odd, ∑ i' : Fin d, |(M_int j i' : ℝ)|) *
                (B_step ^ 2) ^ m := add_le_add hpart1 hpart2
          _ = C_mat * (B_step ^ 2) ^ m := by dsimp [C_mat]; ring
    choose q hq_eq hq_b using hform
    -- Verify Nesterenko criterion inequality: (B_step^2)^(d-1) * A2_step^2 < (A1_step^2 / A2_step^2)^(d-1)
    have hcrit_step : B_step ^ (d - 1) * A2_step < (A1_step / A2_step) ^ (d - 1) := by
      -- Equivalently (B_step * (A2_step / A1_step))^(d-1) * A2_step < 1
      have hA2_div_A1 : A2_step / A1_step ≤ (132 : ℝ) ^ a * (4 : ℝ) ^ r := by
        dsimp [A1_step, A2_step]
        have hrew : ((32 : ℝ) ^ a * (4 : ℝ) ^ r * (r : ℝ) ^ (2 * r) / (r : ℝ) ^ a) /
            ((r : ℝ) ^ (2 * r) / ((4 : ℝ) * ((r : ℝ) + 2)) ^ a) =
            ((128 : ℝ) * ((r : ℝ) + 2) / (r : ℝ)) ^ a * (4 : ℝ) ^ r := by
          have hne1 : (r : ℝ) ^ (2 * r) ≠ 0 := by positivity
          have hne2 : (r : ℝ) ^ a ≠ 0 := by positivity
          have h128 : (128 : ℝ) ^ a = (32 : ℝ) ^ a * (4 : ℝ) ^ a := by rw [← mul_pow]; norm_num
          rw [div_pow, mul_pow (128 : ℝ) ((r : ℝ) + 2) a, h128, mul_pow (4 : ℝ) ((r : ℝ) + 2) a]
          field_simp [hne1, hne2]
        rw [hrew]
        have hfrac_le : (128 : ℝ) * ((r : ℝ) + 2) / (r : ℝ) ≤ 132 := by
          rw [div_le_iff₀ (by positivity)]
          have : (64 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr64
          linarith
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfrac_le a) (by positivity)
      have hBA_le : B_step * (A2_step / A1_step) ≤ (17160 : ℝ) ^ a := by
        have h1 := mul_le_mul_of_nonneg_left hA2_div_A1 hB_pos.le
        refine le_trans h1 ?_
        dsimp [B_step]
        have h2pow : (2 : ℝ) ^ (2 * r ^ 2 + 2 * r) * (4 : ℝ) ^ r ≤ (2 : ℝ) ^ a := by
          have h4eq : (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) := by rw [pow_mul]; norm_num
          rw [h4eq, ← pow_add]
          apply pow_le_pow_right₀ (by norm_num)
          have hle : 2 * r ^ 2 + 4 * r ≤ 2 * r ^ 3 + 1 := by
            have : 4 ≤ r := by omega
            nlinarith
          omega
        calc (65 : ℝ) ^ a * (2 : ℝ) ^ (2 * r ^ 2 + 2 * r) * ((132 : ℝ) ^ a * (4 : ℝ) ^ r)
            = ((65 : ℝ) * 132) ^ a * ((2 : ℝ) ^ (2 * r ^ 2 + 2 * r) * (4 : ℝ) ^ r) := by
              rw [mul_pow]; ring
          _ ≤ ((65 : ℝ) * 132) ^ a * (2 : ℝ) ^ a :=
              mul_le_mul_of_nonneg_left h2pow (by positivity)
          _ = (17160 : ℝ) ^ a := by rw [← mul_pow]; norm_num
      have hpow_lt : (B_step * (A2_step / A1_step)) ^ (d - 1) * A2_step < 1 := by
        have h1 : (B_step * (A2_step / A1_step)) ^ (d - 1) * A2_step ≤
            ((17160 : ℝ) ^ a) ^ (d - 1) * ((64 : ℝ) / (r : ℝ)) ^ a :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hBA_le (d - 1)) hA2_le_simple
            hA2_pos.le (by positivity)
        refine lt_of_le_of_lt h1 ?_
        rw [← pow_mul, mul_comm a (d - 1), pow_mul, ← mul_pow]
        apply pow_lt_one₀ (by positivity) _ (by omega)
        rw [mul_div_assoc', div_lt_one (by positivity)]
        have hpow_le : 17160 ^ (d - 1) ≤ 17160 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hnat_lt : 17160 ^ (d - 1) * 64 < r := by
          calc 17160 ^ (d - 1) * 64 ≤ 17160 ^ K * 64 := Nat.mul_le_mul_right 64 hpow_le
            _ < 64 * 17160 ^ K + 100 := by omega
            _ ≤ r := hr_big
        exact_mod_cast hnat_lt
      have heq1 : (B_step * (A2_step / A1_step)) ^ (d - 1) * A2_step =
          (B_step ^ (d - 1) * A2_step) / (A1_step / A2_step) ^ (d - 1) := by
        generalize B_step = x
        generalize A1_step = y
        generalize A2_step = z
        rw [mul_pow, div_pow, div_pow, div_div_eq_mul_div]
        ring
      rw [heq1, div_lt_one (by positivity)] at hpow_lt
      exact hpow_lt
    have hcrit_sq : (B_step ^ 2) ^ (d - 1) * A2_step ^ 2 < (A1_step ^ 2 / A2_step ^ 2) ^ (d - 1) := by
      have hsq := mul_lt_mul'' hcrit_step hcrit_step (by positivity) (by positivity)
      have hL : (B_step ^ 2) ^ (d - 1) * A2_step ^ 2 =
          (B_step ^ (d - 1) * A2_step) * (B_step ^ (d - 1) * A2_step) := by
        rw [← pow_mul, mul_comm 2 (d - 1), pow_mul]; ring
      have hR : (A1_step ^ 2 / A2_step ^ 2) ^ (d - 1) =
          (A1_step / A2_step) ^ (d - 1) * (A1_step / A2_step) ^ (d - 1) := by
        rw [← div_pow, ← pow_mul, mul_comm 2 (d - 1), pow_mul]; ring
      rw [hL, hR]
      exact hsq
    -- Apply nesterenko_criterion with m ≥ N_big
    apply nesterenko_criterion hd2 ω hω0 hω1
      (A1 := A1_step ^ 2) (A2 := A2_step ^ 2) (B := B_step ^ 2)
      (c1 := (D_rat : ℝ)) (c2 := 2 * (D_rat : ℝ)) (C := C_mat)
      (by positivity) (by positivity) (pow_le_pow_left₀ hA1_pos.le hA1_le_A2 2)
      (pow_lt_one₀ hA2_pos.le hA2_lt1 (by norm_num))
      (by positivity) (by positivity) (by positivity) hC_mat_pos hcrit_sq N_big q
    · intro m hm i
      exact hq_b m (by omega) i
    · intro m hm
      rw [← hq_eq m]
      have hS_pos : 0 ≤ (D_rat : ℝ) * (((commonDenom (2 * m) : ℝ) ^ a) * S_BR a r (2 * m)) := by
        apply mul_nonneg (by positivity)
        apply mul_nonneg (by positivity)
        exact tsum_nonneg fun _ => R_rat_nonneg
      rw [abs_of_nonneg hS_pos]
      constructor
      · have hlow := S_BR_lower_bound hr1 ha_ge ha_odd (even_two_mul m) (by omega)
        have hD1 : (1 : ℝ) ≤ (commonDenom (2 * m) : ℝ) ^ a :=
          one_le_pow₀ (by exact_mod_cast commonDenom_pos (2 * m))
        have hpoly := hN1 (2 * m) (by omega)
        have hstep : A1_step ^ (2 * m) ≤ S_BR a r (2 * m) := by
          refine le_trans ?_ hlow
          dsimp [A1_step]
          rw [zpow_neg, zpow_natCast, div_pow, div_pow, mul_pow (4 : ℝ), mul_pow (3 : ℝ)]
          have h43 : (4 / 3 : ℝ) ^ (a * (2 * m)) = (4 : ℝ) ^ (a * (2 * m)) / (3 : ℝ) ^ (a * (2 * m)) :=
            div_pow _ _ _
          have hm_pos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < 2 * m by omega)
          have hinv_le : ((4 : ℝ) ^ (a * (2 * m)) / (3 : ℝ) ^ (a * (2 * m)))⁻¹ ≤
              ((((r : ℝ) + 2) * ((2 * m : ℕ) : ℝ)) ^ a)⁻¹ :=
            inv_anti₀ (by positivity) (h43 ▸ hpoly)
          have hrew : ((r : ℝ) ^ (2 * r)) ^ (2 * m) / ((4 : ℝ) ^ a * ((r : ℝ) + 2) ^ a) ^ (2 * m) =
              ((4 : ℝ) ^ (a * (2 * m)) / (3 : ℝ) ^ (a * (2 * m)))⁻¹ *
              (((r : ℝ) ^ (2 * r)) ^ (2 * m) / ((3 : ℝ) ^ a * ((r : ℝ) + 2) ^ a) ^ (2 * m)) := by
            simp_rw [mul_pow, ← pow_mul]
            field_simp
          rw [hrew]
          exact mul_le_mul_of_nonneg_right hinv_le (by positivity)
        have hsq : (A1_step ^ 2) ^ m = A1_step ^ (2 * m) := by rw [← pow_mul]
        rw [hsq]
        have h1 : A1_step ^ (2 * m) ≤ (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m) := by
          calc A1_step ^ (2 * m) = 1 * A1_step ^ (2 * m) := (one_mul _).symm
            _ ≤ (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m) :=
              mul_le_mul hD1 hstep (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · have hup := S_BR_upper_bound hr1 ha_ge ha_odd (even_two_mul m) (by omega)
        have hD_le : (commonDenom (2 * m) : ℝ) ^ a ≤ ((32 : ℝ) ^ a) ^ (2 * m) := by
          calc (commonDenom (2 * m) : ℝ) ^ a ≤ ((32 : ℝ) ^ (2 * m)) ^ a :=
                pow_le_pow_left₀ (by positivity) (by exact_mod_cast commonDenom_le_pow (2 * m)) a
            _ = ((32 : ℝ) ^ a) ^ (2 * m) := by rw [← pow_mul, ← pow_mul, mul_comm]
        have hprod : (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m) ≤
            2 * A2_step ^ (2 * m) := by
          calc (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m)
              ≤ ((32 : ℝ) ^ a) ^ (2 * m) *
                  (2 * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ (2 * m)) :=
                mul_le_mul hD_le hup (tsum_nonneg fun _ => R_rat_nonneg) (by positivity)
            _ = 2 * (((32 : ℝ) ^ a) * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a)) ^ (2 * m) := by
                rw [mul_pow]; ring
            _ = 2 * A2_step ^ (2 * m) := by dsimp [A2_step]; congr 2; ring
        have hsq : (A2_step ^ 2) ^ m = A2_step ^ (2 * m) := by rw [← pow_mul]
        rw [hsq]
        have := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ (D_rat : ℝ))
        linarith
  · -- Case dim W = 1: all zetaReal j (j ∈ Icc 3 a, odd) are rational, immediate contradiction!
    have hdim1 : Module.finrank ℚ W = 1 := by omega
    have hW_eq : W = Submodule.span ℚ ({(1 : ℝ)} : Set ℝ) := by
      have hsub : Submodule.span ℚ ({(1 : ℝ)} : Set ℝ) ≤ W :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h1_mem)
      have hfin1 : Module.finrank ℚ (Submodule.span ℚ ({(1 : ℝ)} : Set ℝ)) = 1 :=
        finrank_span_singleton (by norm_num)
      exact (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfin1, hdim1])).symm
    have hrat_all : ∀ j ∈ (Finset.Icc 3 a).filter Odd, ∃ q : ℚ, (q : ℝ) = zetaReal j := by
      intro j hj
      have hmem : zetaReal j ∈ Submodule.span ℚ ({(1 : ℝ)} : Set ℝ) := hW_eq ▸ hzeta_mem j hj
      rcases Submodule.mem_span_singleton.mp hmem with ⟨q, hq⟩
      exact ⟨q, by simpa [Rat.smul_def] using hq⟩
    classical
    let q_val : ℕ → ℚ := fun j =>
      if hj : j ∈ (Finset.Icc 3 a).filter Odd then (hrat_all j hj).choose else 0
    have hq_spec : ∀ j ∈ (Finset.Icc 3 a).filter Odd, (q_val j : ℝ) = zetaReal j := by
      intro j hj; simp only [q_val, dif_pos hj]; exact (hrat_all j hj).choose_spec
    let D_rat : ℕ := ∏ j ∈ (Finset.Icc 3 a).filter Odd, (q_val j).den
    have hD_pos : 0 < D_rat :=
      Finset.prod_pos fun j _ => (q_val j).pos
    -- Pick even n large enough that D_rat * 2 * A2_step ^ n < 1
    have hlim : Filter.Tendsto (fun m : ℕ => (D_rat : ℝ) * 2 * (A2_step ^ 2) ^ m)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (D_rat : ℝ) * 2)).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (pow_lt_one₀ hA2_pos.le hA2_lt1 (by norm_num)))
    have hev := hlim.eventually (gt_mem_nhds zero_lt_one)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨m0, hm0⟩ := hev
    set m := max 1 m0
    have hm_lt : (D_rat : ℝ) * 2 * (A2_step ^ 2) ^ m < 1 := hm0 m (le_max_right _ _)
    obtain ⟨p0, p, heq, _, _⟩ := S_BR_integer_linear_form ha_ge ha_odd (even_two_mul m)
    -- Show D_rat * ((commonDenom (2m))^a * S_BR a r (2m)) is an integer strictly between 0 and 1
    have hint : ∃ z : ℤ,
        (D_rat : ℝ) * ((commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m)) = (z : ℝ) := by
      have hterm : ∀ j ∈ (Finset.Icc 3 a).filter Odd,
          ∃ z : ℤ, (D_rat : ℚ) * (p j : ℚ) * q_val j = (z : ℚ) := by
        intro j hj
        rcases Finset.dvd_prod_of_mem (fun j => (q_val j).den) hj with ⟨q', hq'⟩
        refine ⟨(q' : ℤ) * p j * (q_val j).num, ?_⟩
        have hqQ : (D_rat : ℚ) = ((q_val j).den : ℚ) * (q' : ℚ) := by exact_mod_cast hq'
        have hnum_den : ((q_val j).den : ℚ) * q_val j = ((q_val j).num : ℚ) := by
          set x := q_val j
          have hne : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
          conv_lhs => rhs; rw [← Rat.num_div_den x]
          exact mul_div_cancel₀ _ hne
        rw [hqQ]
        push_cast
        calc ((q_val j).den : ℚ) * (q' : ℚ) * (p j : ℚ) * q_val j
            = (q' : ℚ) * (p j : ℚ) * (((q_val j).den : ℚ) * q_val j) := by ring
          _ = (q' : ℚ) * (p j : ℚ) * ((q_val j).num : ℚ) := by rw [hnum_den]
      obtain ⟨z_sum, hz_sum⟩ := exists_int_sum _ _ hterm
      refine ⟨(D_rat : ℤ) * p0 + z_sum, ?_⟩
      rw [heq, mul_add, Finset.mul_sum]
      have hcast := congr_arg (Rat.cast (K := ℝ)) hz_sum
      push_cast at hcast ⊢
      rw [← hcast]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← hq_spec j hj]; ring
    obtain ⟨z, hz⟩ := hint
    have hz_pos : (0 : ℝ) < (z : ℝ) := by
      rw [← hz]
      have hlow := S_BR_lower_bound hr1 ha_ge ha_odd (even_two_mul m) (by omega)
      have hS_pos : 0 < S_BR a r (2 * m) := lt_of_lt_of_le (by positivity) hlow
      have hD_pos' : (0 : ℝ) < (commonDenom (2 * m) : ℝ) ^ a :=
        pow_pos (by exact_mod_cast commonDenom_pos (2 * m)) a
      exact mul_pos (by exact_mod_cast hD_pos) (mul_pos hD_pos' hS_pos)
    have hz_lt1 : (z : ℝ) < 1 := by
      rw [← hz]
      have hup := S_BR_upper_bound hr1 ha_ge ha_odd (even_two_mul m) (by omega)
      have hD_le : (commonDenom (2 * m) : ℝ) ^ a ≤ ((32 : ℝ) ^ a) ^ (2 * m) := by
        calc (commonDenom (2 * m) : ℝ) ^ a ≤ ((32 : ℝ) ^ (2 * m)) ^ a :=
              pow_le_pow_left₀ (by positivity) (by exact_mod_cast commonDenom_le_pow (2 * m)) a
          _ = ((32 : ℝ) ^ a) ^ (2 * m) := by rw [← pow_mul, ← pow_mul, mul_comm]
      have hprod : (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m) ≤ 2 * (A2_step ^ 2) ^ m := by
        calc (commonDenom (2 * m) : ℝ) ^ a * S_BR a r (2 * m)
            ≤ ((32 : ℝ) ^ a) ^ (2 * m) *
                (2 * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a) ^ (2 * m)) :=
              mul_le_mul hD_le hup (tsum_nonneg fun _ => R_rat_nonneg) (by positivity)
          _ = 2 * (((32 : ℝ) ^ a) * (((4 : ℝ) ^ r * (r : ℝ) ^ (2 * r)) / (r : ℝ) ^ a)) ^ (2 * m) := by
              rw [mul_pow]; ring
          _ = 2 * A2_step ^ (2 * m) := by dsimp [A2_step]; congr 2; ring
          _ = 2 * (A2_step ^ 2) ^ m := by rw [← pow_mul]
      have := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ (D_rat : ℝ))
      linarith
    have hz_posZ : (0 : ℤ) < z := by exact_mod_cast hz_pos
    have hz_lt1Z : z < (1 : ℤ) := by exact_mod_cast hz_lt1
    omega

lemma rivoal_main :
    { n : ℕ | ∃ x, Irrational x ∧ riemannZeta (2 * n + 1) = x }.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  let S_fin : Finset ℕ := hfin.toFinset
  set K := S_fin.sup id + 1
  have hrat_ge : ∀ k ≥ K, ∃ q : ℚ, (q : ℝ) = zetaReal (2 * k + 1) := by
    intro k hk
    by_contra hnot
    have hirr : Irrational (zetaReal (2 * k + 1)) := hnot
    have hmem : k ∈ { n : ℕ | ∃ x, Irrational x ∧ riemannZeta (2 * n + 1) = x } := by
      refine ⟨zetaReal (2 * k + 1), hirr, ?_⟩
      have hcast : (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast]
      exact riemannZeta_nat_eq_zetaReal (by omega)
    have hmemS : k ∈ S_fin := hfin.mem_toFinset.mpr hmem
    have hle : k ≤ S_fin.sup id := Finset.le_sup (f := id) hmemS
    omega
  exact rivoal_aux K (64 * 17160 ^ K + 100) (2 * (64 * 17160 ^ K + 100) ^ 3 + 1)
    hrat_ge le_rfl rfl

end BallRivoalProof

theorem OMA.solution : type_of% @RiemannZetaValues.infinite_irrational_at_odd :=
  BallRivoalProof.rivoal_main
