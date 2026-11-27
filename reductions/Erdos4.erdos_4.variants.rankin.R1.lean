import FormalConjectures.ErdosProblems.«4»

-- Reduction Erdos4.erdos_4.variants.rankin.R1 of Erdős Problem 4 — rankin
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos4_erdos_4_variants_rankin_R1

open Real

/-- Rankin's covering (Jacobsthal-function lower bound): for some `c > 0` and every large `y`,
one residue `x` makes each of `x + 1, …, x + L(y)` divisible by a prime `≤ y`, where
`L(y) = c y log y log₃ y / (log₂ y)²` (Rankin 1938). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∃ x : ℕ, ∀ i : ℕ, 1 ≤ i →
    (i : ℝ) ≤ c * y * Real.log y * Real.log (Real.log (Real.log y)) /
      (Real.log (Real.log y)) ^ 2 →
    ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ p ∣ x + i

/-- A weak Chebyshev lower bound: `π(x)² ≥ x` for all large `x`. -/
def H2 : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x → x ≤ Nat.primeCounting x ^ 2

lemma key (y A : ℝ) (hy : 16 ≤ Real.log y) (hy0 : 0 < y) (hA1 : y / 4 ≤ A)
    (hA2 : A ≤ 3 * y) :
    A * Real.log A * (Real.log (Real.log (Real.log A)) / (Real.log (Real.log A)) ^ 2) ≤
      48 * (y * Real.log y * (Real.log (Real.log (Real.log y)) /
        (Real.log (Real.log y)) ^ 2)) := by
  have hA0 : 0 < A := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  set u := Real.log y with hu
  have hu0 : 0 < u := by linarith
  have hLA1 : u / 2 ≤ Real.log A := by
    have h1 : Real.log (y / 4) ≤ Real.log A := Real.log_le_log (by positivity) hA1
    rw [Real.log_div hy0.ne' (by norm_num)] at h1
    linarith
  have hLA2 : Real.log A ≤ 2 * u := by
    have h1 : Real.log A ≤ Real.log (3 * y) := Real.log_le_log hA0 hA2
    rw [Real.log_mul (by norm_num) hy0.ne'] at h1
    linarith
  set t := Real.log u with ht
  have ht2 : 2 ≤ t := by
    have h1 : Real.log 16 ≤ t := Real.log_le_log (by norm_num) hy
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  set s := Real.log (Real.log A) with hs
  have hs1 : t / 2 ≤ s := by
    have h1 : Real.log (u / 2) ≤ s := Real.log_le_log (by positivity) hLA1
    rw [Real.log_div hu0.ne' (by norm_num)] at h1
    linarith
  have hs2 : s ≤ 2 * t := by
    have h1 : s ≤ Real.log (2 * u) := Real.log_le_log (by linarith) hLA2
    rw [Real.log_mul (by norm_num) hu0.ne'] at h1
    linarith
  have hs0 : 1 ≤ s := by linarith
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg hs0
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
  have hlogs : Real.log s ≤ 2 * Real.log t := by
    have h1 : Real.log s ≤ Real.log (2 * t) := Real.log_le_log (by linarith) hs2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 ≤ Real.log t := by linarith
  have hfrac : Real.log s / s ^ 2 ≤ 8 * (Real.log t / t ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    have h5 : 8 * (Real.log t / t ^ 2) * (t ^ 2 / 4) = 2 * Real.log t := by
      field_simp; ring
    have h6 : 0 ≤ 8 * (Real.log t / t ^ 2) := by positivity
    calc Real.log s ≤ 2 * Real.log t := hlogs
      _ = 8 * (Real.log t / t ^ 2) * (t ^ 2 / 4) := h5.symm
      _ ≤ 8 * (Real.log t / t ^ 2) * s ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ h6; linarith
  have hAl : A * Real.log A ≤ 6 * (y * u) := by
    have := mul_le_mul hA2 hLA2 (by linarith) (by linarith)
    linarith
  have hfr0 : 0 ≤ Real.log s / s ^ 2 := by positivity
  have hyu : 0 ≤ 6 * (y * u) := by positivity
  calc A * Real.log A * (Real.log s / s ^ 2)
        ≤ (6 * (y * u)) * (8 * (Real.log t / t ^ 2)) := mul_le_mul hAl hfrac hfr0 hyu
    _ = 48 * (y * u * (Real.log t / t ^ 2)) := by ring

lemma gap (x M : ℕ) (hx : 2 ≤ x) (hc : ∀ i, 1 ≤ i → i ≤ M → ¬ (x + i).Prime) :
    Nat.nth Nat.Prime (Nat.primeCounting x - 1) ≤ x ∧
    x + M + 1 ≤ Nat.nth Nat.Prime (Nat.primeCounting x - 1 + 1) := by
  have hk : 1 ≤ Nat.primeCounting x := by
    have h2 : Nat.primeCounting 2 ≤ Nat.primeCounting x := Nat.monotone_primeCounting hx
    have : Nat.primeCounting 2 = 1 := by decide
    omega
  have hkk : Nat.primeCounting x - 1 + 1 = Nat.primeCounting x := by omega
  constructor
  · have : Nat.nth Nat.Prime (Nat.primeCounting x - 1) < x + 1 :=
      Nat.nth_lt_of_lt_count (by
        show Nat.primeCounting x - 1 < Nat.count Nat.Prime (x + 1)
        have : Nat.primeCounting x = Nat.count Nat.Prime (x + 1) := rfl
        omega)
    omega
  · rw [hkk]
    have h1 : x + 1 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (x + 1)) :=
      Nat.le_nth_count Nat.infinite_setOfPred_prime (x + 1)
    have hpr : (Nat.nth Nat.Prime (Nat.primeCounting x)).Prime := Nat.prime_nth_prime _
    by_contra hlt
    push_neg at hlt
    have h1' : x + 1 ≤ Nat.nth Nat.Prime (Nat.primeCounting x) := h1
    obtain ⟨i, hi⟩ : ∃ i, Nat.nth Nat.Prime (Nat.primeCounting x) = x + i :=
      ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
    exact hc i (by omega) (by omega) (hi ▸ hpr)

theorem main : H1 → H2 → type_of% @Erdos4.erdos_4.variants.rankin := by
  rintro ⟨c, hc, Y, hY⟩ ⟨N2, hN2⟩
  refine ⟨c / 48, by positivity, ?_⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨y, hyY, hyN2, hyN, hy24⟩ : ∃ y : ℕ, Y ≤ y ∧ N2 ≤ y ∧ 4 * N + 4 ≤ y ∧ 2 ^ 24 ≤ y :=
    ⟨max (max Y N2) (max (4 * N + 4) (2 ^ 24)), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨x0, hx0⟩ := hY y hyY
  set P := primorial y with hP
  have hP0 : 0 < P := primorial_pos y
  have hP4 : P ≤ 4 ^ y := primorial_le_four_pow y
  set x := x0 % P + P * 2 ^ y with hxdef
  set L : ℝ := c * y * Real.log y * Real.log (Real.log (Real.log y)) /
      (Real.log (Real.log y)) ^ 2 with hL
  set M := ⌊L⌋₊ with hM
  have hylt : y < 2 ^ y := Nat.lt_two_pow_self
  have hx2y : 2 ^ y ≤ x := by
    have : 2 ^ y ≤ P * 2 ^ y := Nat.le_mul_of_pos_left _ hP0
    omega
  have hcomp : ∀ i, 1 ≤ i → i ≤ M → ¬ (x + i).Prime := by
    intro i hi1 hiM hpr
    have hiL : (i : ℝ) ≤ L := by
      have hL0 : 0 ≤ L := by
        by_contra hneg
        push_neg at hneg
        have : M = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      exact le_trans (Nat.cast_le.mpr hiM) (Nat.floor_le hL0)
    obtain ⟨p, hp, hpy, hpd⟩ := hx0 i hi1 hiL
    have hpP : p ∣ P := by
      rw [hP, primorial]
      apply Finset.dvd_prod_of_mem
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    have hpx : p ∣ x + i := by
      have he : x0 + i = P * (x0 / P) + (x0 % P + i) := by
        have := Nat.div_add_mod x0 P; omega
      have h1 : p ∣ x0 % P + i := by
        rw [he] at hpd
        exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hpP _)).mp hpd
      have h2 : x + i = (x0 % P + i) + P * 2 ^ y := by rw [hxdef]; ring
      rw [h2]
      exact dvd_add h1 (dvd_mul_of_dvd_left hpP _)
    have := (Nat.prime_dvd_prime_iff_eq hp hpr).mp hpx
    omega
  obtain ⟨hlo, hhi⟩ := gap x M (by have : 2 ≤ 2 ^ y := Nat.le_self_pow (by omega) 2; omega) hcomp
  set n := Nat.primeCounting x - 1 with hn
  have hpc : x ≤ Nat.primeCounting x ^ 2 := hN2 x (by omega)
  have hn1 : x ≤ (n + 1) ^ 2 := by
    have : n + 1 = Nat.primeCounting x := by
      have : 1 ≤ Nat.primeCounting x := by
        by_contra h0; push_neg at h0
        have : Nat.primeCounting x = 0 := by omega
        rw [this] at hpc; omega
      omega
    rw [this]; exact hpc
  have hnx : n ≤ x := by
    have : Nat.primeCounting x ≤ x + 1 := Nat.count_le _
    omega
  have hn2 : 2 ≤ n := by
    by_contra h; push_neg at h
    have : (n + 1) ^ 2 ≤ 4 := by
      have : n + 1 ≤ 2 := by omega
      calc (n + 1) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 := by norm_num
    have : 2 ^ 24 ≤ 2 ^ y := le_trans hy24 hylt.le
    omega
  -- real bounds
  have hyR : (2:ℝ) ^ 24 ≤ (y:ℝ) := by exact_mod_cast hy24
  have hy0 : (0:ℝ) < y := by linarith [show (0:ℝ) < 2 ^ 24 by norm_num]
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hlogy : 16 ≤ Real.log y := by
    have : Real.log ((2:ℝ) ^ 24) ≤ Real.log y := Real.log_le_log (by norm_num) hyR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < n := by linarith
  set A := Real.log (n : ℝ) with hA
  have hA1 : (y:ℝ) / 4 ≤ A := by
    have h1 : (2:ℝ) ^ y ≤ ((n:ℝ) + 1) ^ 2 := by exact_mod_cast le_trans hx2y hn1
    have h2 : (n:ℝ) + 1 ≤ 2 * n := by linarith
    have h3 : ((n:ℝ) + 1) ^ 2 ≤ (2 * n) ^ 2 := by gcongr
    have h4 : Real.log ((2:ℝ) ^ y) ≤ Real.log ((2 * (n:ℝ)) ^ 2) :=
      Real.log_le_log (by positivity) (le_trans h1 h3)
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hn0.ne'] at h4
    push_cast at h4
    have hy8 : (8:ℝ) ≤ y := by linarith [show (8:ℝ) ≤ 2 ^ 24 by norm_num]
    nlinarith
  have hA2 : A ≤ 3 * y := by
    have hxlt : x < 2 ^ (3 * y + 1) := by
      have h1 : x0 % P < P := Nat.mod_lt _ hP0
      have h2 : x < P * (2 ^ y + 1) := by rw [hxdef]; nlinarith
      have h3 : P * (2 ^ y + 1) ≤ 4 ^ y * (2 ^ y + 2 ^ y) := by
        apply Nat.mul_le_mul hP4
        have : 1 ≤ 2 ^ y := Nat.one_le_two_pow
        omega
      have h4 : 4 ^ y * (2 ^ y + 2 ^ y) = 2 ^ (3 * y + 1) := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        rw [show 3 * y + 1 = 2 * y + y + 1 by ring, pow_succ, pow_add]
        ring
      omega
    have h1 : (n:ℝ) ≤ (2:ℝ) ^ (3 * y + 1) := by exact_mod_cast le_trans hnx hxlt.le
    have h2 : A ≤ Real.log ((2:ℝ) ^ (3 * y + 1)) := Real.log_le_log hn0 h1
    rw [Real.log_pow] at h2
    push_cast at h2
    have hy8 : (8:ℝ) ≤ y := by linarith [show (8:ℝ) ≤ 2 ^ 24 by norm_num]
    nlinarith
  have hk := key (y:ℝ) A hlogy hy0 hA1 hA2
  refine ⟨n, ?_, ?_⟩
  · show (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) > _
    have hg : ((x + M + 1 : ℕ) : ℝ) - (x : ℝ) ≤
        (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) := by
      have a1 : ((x + M + 1 : ℕ) : ℝ) ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by exact_mod_cast hhi
      have a2 : (Nat.nth Nat.Prime n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hlo
      linarith
    have hML : L < (M : ℝ) + 1 := Nat.lt_floor_add_one L
    push_cast at hg
    have hrw : c / 48 * Real.log (Real.log (n:ℝ)) * Real.log (Real.log (Real.log (Real.log (n:ℝ)))) /
        (Real.log (Real.log (Real.log (n:ℝ)))) ^ 2 * Real.log (n:ℝ) =
        c / 48 * (A * Real.log A * (Real.log (Real.log (Real.log A)) /
          (Real.log (Real.log A)) ^ 2)) := by
      rw [hA]; ring
    rw [gt_iff_lt, hrw]
    have hLeq : L = c * (y * Real.log y * (Real.log (Real.log (Real.log y)) /
        (Real.log (Real.log y)) ^ 2)) := by rw [hL]; ring
    have : c / 48 * (A * Real.log A * (Real.log (Real.log (Real.log A)) /
          (Real.log (Real.log A)) ^ 2)) ≤ L := by
      rw [hLeq]
      have := mul_le_mul_of_nonneg_left hk (le_of_lt (show 0 < c / 48 by positivity))
      linarith
    linarith
  · have hy4 : ((4 * N + 4 : ℕ) : ℝ) ≤ y := by exact_mod_cast hyN
    push_cast at hy4
    have he : A + 1 ≤ (n:ℝ) := by
      have := Real.add_one_le_exp A
      rw [hA, Real.exp_log hn0] at this
      exact this
    have : (N:ℝ) < n := by linarith
    exact_mod_cast this

end OMA.R_Erdos4_erdos_4_variants_rankin_R1
