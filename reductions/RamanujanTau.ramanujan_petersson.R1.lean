import FormalConjectures.Wikipedia.RamanujanTau
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Reduction of `RamanujanTau.ramanujan_petersson`

Following L. J. Mordell (*On Mr. Ramanujan's empirical expansions of modular functions*, Proc.
Cambridge Philos. Soc. 19 (1917), 117–124), E. Hecke (1937), and P. Deligne (*La conjecture de
Weil I*, Publ. Math. IHÉS 43 (1974), 273–307), we reduce the sharp Ramanujan–Petersson inequality
`|(τ p : ℝ)| ≤ 2 * (p : ℝ) ^ (11 / 2)` for every prime `p` to two independent pillars:
1. `H1`: **Mordell–Hecke prime-power recurrence** (1917/1937): for every prime `p` and every
   `k : ℕ`, `τ (p ^ (k + 2)) = τ p * τ (p ^ (k + 1)) - p ^ 11 * τ (p ^ k)`.
2. `H2`: **Deligne's sub-exponential prime-power growth bound** (1974): for every prime `p` and
   every `ε > 0`, there exists `C : ℝ` such that for all `k : ℕ`,
   `|(τ (p ^ k) : ℝ)| ≤ C * ((p ^ k : ℕ) : ℝ) ^ (11 / 2 + ε)`.

Inside `main`, we prove the **quadratic-root amplification argument** completely from scratch:
- Assuming for contradiction `|(τ p : ℝ)| > 2 * p ^ (11 / 2)`, set `x = τ p / p ^ (11 / 2)`
  (`|x| > 2`) and extract the real root `r` of `r + r⁻¹ = x` with `|r| > 1`.
- Prove by induction on `k` (using `RamanujanTau.τ_one` and `H1`) the exact closed form
  `(τ (p ^ k) : ℝ) * (r - r⁻¹) = (p ^ (11 / 2)) ^ k * (r ^ (k + 1) - (r⁻¹) ^ (k + 1))`.
- Choose `ε = log |r| / (2 * log p) > 0` so `p ^ ε = √|r| < |r|`, apply `H2`, and observe that
  `|r| * (√|r|) ^ k - 1 ≤ C * |r - r⁻¹|` for all `k : ℕ`, contradicting `(√|r|) ^ k → ∞`.

Credit: @tkaiman
-/

namespace OMA.R_RamanujanTau_ramanujan_petersson_R1

open Real RamanujanTau

/-- **Mordell–Hecke prime-power recurrence for the Ramanujan `τ`-function** (Mordell 1917 / Hecke
1937): for every prime `p` and every `k : ℕ`,
`τ (p ^ (k + 2)) = τ p * τ (p ^ (k + 1)) - (p : ℤ) ^ 11 * τ (p ^ k)`. -/
def H1 : Prop :=
  ∀ p : ℕ, Prime p → ∀ k : ℕ,
    RamanujanTau.τ (p ^ (k + 2)) =
      RamanujanTau.τ p * RamanujanTau.τ (p ^ (k + 1)) -
        (p : ℤ) ^ 11 * RamanujanTau.τ (p ^ k)

/-- **Deligne's asymptotic prime-power bound for the Ramanujan `τ`-function** (Deligne 1974):
for every prime `p` and every `ε > 0`, there exists `C : ℝ` such that for all `k : ℕ`,
`|(τ (p ^ k) : ℝ)| ≤ C * ((p ^ k : ℕ) : ℝ) ^ ((11 : ℝ) / 2 + ε)`. -/
def H2 : Prop :=
  ∀ p : ℕ, Prime p → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ k : ℕ,
      |(RamanujanTau.τ (p ^ k) : ℝ)| ≤ C * ((p ^ k : ℕ) : ℝ) ^ ((11 : ℝ) / 2 + ε)

theorem main : H1 → H2 → type_of% @RamanujanTau.ramanujan_petersson := by
  intro h1 h2 p hp
  have hp_nat : Nat.Prime p := Nat.prime_iff.mpr hp
  have hp2 : 2 ≤ p := hp_nat.two_le
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  set q : ℝ := (p : ℝ) ^ ((11 : ℝ) / 2)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hp_pos _
  have hq_sq : q ^ 2 = (p : ℝ) ^ 11 := by
    dsimp [q]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp_pos.le]
    have hexp : ((11 : ℝ) / 2) * (2 : ℕ) = (11 : ℕ) := by norm_num
    rw [hexp, Real.rpow_natCast]
  by_contra hgt
  push Not at hgt
  -- Set `x = τ p / q` with `|x| > 2` and construct real root `r` of `r + r⁻¹ = x` with `|r| > 1`
  set x : ℝ := (τ p : ℝ) / q
  have hx_gt2 : 2 < |x| := by
    dsimp [x]
    rw [abs_div, abs_of_pos hq_pos, lt_div_iff₀ hq_pos]
    simpa [Int.cast_abs] using hgt
  have hdisc : 0 < x ^ 2 - 4 := by
    have : 4 < |x| ^ 2 := by nlinarith
    rw [sq_abs] at this
    linarith
  set s : ℝ := if 0 ≤ x then 1 else -1
  have hs_sq : s ^ 2 = 1 := by dsimp [s]; split_ifs <;> norm_num
  have hsx : s * x = |x| := by
    dsimp [s]
    split_ifs with hx0
    · rw [one_mul, abs_of_nonneg hx0]
    · push Not at hx0
      rw [neg_one_mul, abs_of_neg hx0]
  set r : ℝ := (x + s * Real.sqrt (x ^ 2 - 4)) / 2
  have hsr_eq : s * r = (|x| + Real.sqrt (x ^ 2 - 4)) / 2 := by
    dsimp [r]
    calc s * ((x + s * Real.sqrt (x ^ 2 - 4)) / 2)
        = (s * x + s ^ 2 * Real.sqrt (x ^ 2 - 4)) / 2 := by ring
      _ = (|x| + Real.sqrt (x ^ 2 - 4)) / 2 := by rw [hsx, hs_sq, one_mul]
  have hr_abs : |r| = (|x| + Real.sqrt (x ^ 2 - 4)) / 2 := by
    have hpos : 0 < (|x| + Real.sqrt (x ^ 2 - 4)) / 2 := by
      have := Real.sqrt_pos.mpr hdisc
      linarith
    have habs_s : |s| = 1 := by dsimp [s]; split_ifs <;> norm_num
    calc |r| = |s| * |r| := by rw [habs_s, one_mul]
      _ = |s * r| := (abs_mul s r).symm
      _ = (|x| + Real.sqrt (x ^ 2 - 4)) / 2 := by rw [hsr_eq, abs_of_pos hpos]
  have hr_gt1 : 1 < |r| := by
    rw [hr_abs]
    have := Real.sqrt_pos.mpr hdisc
    linarith
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hr_gt1
    linarith
  have hr_quad : r ^ 2 - x * r + 1 = 0 := by
    dsimp [r]
    have hsq : Real.sqrt (x ^ 2 - 4) ^ 2 = x ^ 2 - 4 := Real.sq_sqrt hdisc.le
    calc ((x + s * Real.sqrt (x ^ 2 - 4)) / 2) ^ 2 - x * ((x + s * Real.sqrt (x ^ 2 - 4)) / 2) + 1
        = (s ^ 2 * Real.sqrt (x ^ 2 - 4) ^ 2 - (x ^ 2 - 4)) / 4 := by ring
      _ = 0 := by rw [hs_sq, hsq]; ring
  have hr_sum : r + r⁻¹ = x := by
    field_simp [hr_ne]
    linarith [hr_quad]
  have htau_p : (τ p : ℝ) = q * (r + r⁻¹) := by
    rw [hr_sum]
    dsimp [x]
    field_simp [hq_pos.ne']
  -- Exact closed form for `τ (p ^ k)` by strong induction using `H1` and `RamanujanTau.τ_one`
  have hclosed : ∀ k : ℕ,
      (τ (p ^ k) : ℝ) * (r - r⁻¹) = q ^ k * (r ^ (k + 1) - (r⁻¹) ^ (k + 1)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 =>
        simp [RamanujanTau.τ_one]
      | 1 =>
        simp only [pow_one, htau_p]
        ring
      | m + 2 =>
        have hrec : (τ (p ^ (m + 2)) : ℝ) =
            (τ p : ℝ) * (τ (p ^ (m + 1)) : ℝ) - (p : ℝ) ^ 11 * (τ (p ^ m) : ℝ) := by
          exact_mod_cast h1 p hp m
        have ihm1 := ih (m + 1) (by omega)
        have ihm := ih m (by omega)
        calc (τ (p ^ (m + 2)) : ℝ) * (r - r⁻¹)
            = (τ p : ℝ) * ((τ (p ^ (m + 1)) : ℝ) * (r - r⁻¹)) -
                (p : ℝ) ^ 11 * ((τ (p ^ m) : ℝ) * (r - r⁻¹)) := by rw [hrec]; ring
          _ = q * (r + r⁻¹) * (q ^ (m + 1) * (r ^ (m + 2) - (r⁻¹) ^ (m + 2))) -
                q ^ 2 * (q ^ m * (r ^ (m + 1) - (r⁻¹) ^ (m + 1))) := by
                  rw [htau_p, ← hq_sq, ihm1, ihm]
          _ = q ^ (m + 2) * ((r + r⁻¹) * (r ^ (m + 2) - (r⁻¹) ^ (m + 2)) -
                (r ^ (m + 1) - (r⁻¹) ^ (m + 1))) := by ring
          _ = q ^ (m + 2) * (r ^ (m + 3) - (r⁻¹) ^ (m + 3)) := by
                congr 1
                have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr_ne
                calc (r + r⁻¹) * (r ^ (m + 2) - (r⁻¹) ^ (m + 2)) - (r ^ (m + 1) - (r⁻¹) ^ (m + 1))
                    = r ^ (m + 3) - (r⁻¹) ^ (m + 3) +
                        (r * r⁻¹ - 1) * (r ^ (m + 1) - (r⁻¹) ^ (m + 1)) := by ring
                  _ = r ^ (m + 3) - (r⁻¹) ^ (m + 3) := by rw [hrr]; ring
  -- Choose `ε = log |r| / (2 * log p) > 0` so `p ^ ε = √|r| < |r|` and contradict `H2`
  have hlogr_pos : 0 < Real.log |r| := Real.log_pos hr_gt1
  have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
  set ε : ℝ := Real.log |r| / (2 * Real.log (p : ℝ))
  have hε_pos : 0 < ε := by positivity
  obtain ⟨C, hC⟩ := h2 p hp ε hε_pos
  have hp_eps : (p : ℝ) ^ ε = Real.sqrt |r| := by
    rw [Real.rpow_def_of_pos hp_pos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
    congr 1
    dsimp [ε]
    field_simp [hlogp_pos.ne']
  have hsqrt_gt1 : 1 < Real.sqrt |r| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hr_gt1
  have hbound_k : ∀ k : ℕ, |r| * (Real.sqrt |r|) ^ k ≤ C * |r - r⁻¹| + 1 := by
    intro k
    have hCk := hC k
    have hrpow_eq : ((p ^ k : ℕ) : ℝ) ^ ((11 : ℝ) / 2 + ε) = q ^ k * (Real.sqrt |r|) ^ k := by
      push_cast
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos.le, mul_add,
        Real.rpow_add hp_pos, mul_comm (k : ℝ), Real.rpow_mul hp_pos.le,
        mul_comm (k : ℝ) ε, Real.rpow_mul hp_pos.le, Real.rpow_natCast, Real.rpow_natCast,
        hp_eps]
    rw [hrpow_eq] at hCk
    have hdiff_ge : |r| ^ (k + 1) - 1 ≤ |r ^ (k + 1) - (r⁻¹) ^ (k + 1)| := by
      have htri := abs_sub_abs_le_abs_sub (r ^ (k + 1)) ((r⁻¹) ^ (k + 1))
      rw [abs_pow, abs_pow, abs_inv] at htri
      have hinv_le1 : |r|⁻¹ ^ (k + 1) ≤ 1 := by
        have hinv_le : |r|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr_gt1.le
        exact pow_le_one₀ (by positivity) hinv_le
      linarith
    have hcl_abs : |(τ (p ^ k) : ℝ)| * |r - r⁻¹| =
        q ^ k * |r ^ (k + 1) - (r⁻¹) ^ (k + 1)| := by
      have h := congrArg abs (hclosed k)
      rwa [abs_mul, abs_mul, abs_of_pos (pow_pos hq_pos k)] at h
    have hineq1 : q ^ k * (|r| ^ (k + 1) - 1) ≤
        C * q ^ k * (Real.sqrt |r|) ^ k * |r - r⁻¹| := by
      have h1 : q ^ k * (|r| ^ (k + 1) - 1) ≤ |(τ (p ^ k) : ℝ)| * |r - r⁻¹| := by
        rw [hcl_abs]
        exact mul_le_mul_of_nonneg_left hdiff_ge (pow_pos hq_pos k).le
      have h2 : |(τ (p ^ k) : ℝ)| * |r - r⁻¹| ≤ C * q ^ k * (Real.sqrt |r|) ^ k * |r - r⁻¹| := by
        have := mul_le_mul_of_nonneg_right hCk (abs_nonneg (r - r⁻¹))
        linarith
      linarith
    have hineq2 : |r| ^ (k + 1) - 1 ≤ C * |r - r⁻¹| * (Real.sqrt |r|) ^ k := by
      have hqk_pos : 0 < q ^ k := pow_pos hq_pos k
      nlinarith
    have hr_sq : |r| = (Real.sqrt |r|) ^ 2 := (Real.sq_sqrt (by linarith)).symm
    have hpow_eq : |r| ^ (k + 1) = |r| * (Real.sqrt |r|) ^ k * (Real.sqrt |r|) ^ k := by
      calc |r| ^ (k + 1) = |r| * |r| ^ k := pow_succ' _ _
        _ = |r| * ((Real.sqrt |r|) ^ 2) ^ k := by rw [← hr_sq]
        _ = |r| * (Real.sqrt |r|) ^ k * (Real.sqrt |r|) ^ k := by
          rw [sq, mul_pow]; ring
    have hsp_pos : 0 < (Real.sqrt |r|) ^ k := pow_pos (by linarith) k
    have hge1 : (1 : ℝ) ≤ (Real.sqrt |r|) ^ k := one_le_pow₀ hsqrt_gt1.le
    have hdiv : |r| * (Real.sqrt |r|) ^ k ≤ C * |r - r⁻¹| + 1 / (Real.sqrt |r|) ^ k := by
      have h1 : |r| * (Real.sqrt |r|) ^ k * (Real.sqrt |r|) ^ k ≤
          (C * |r - r⁻¹| + 1 / (Real.sqrt |r|) ^ k) * (Real.sqrt |r|) ^ k := by
        have hcancel : (1 / (Real.sqrt |r|) ^ k) * (Real.sqrt |r|) ^ k = 1 :=
          one_div_mul_cancel hsp_pos.ne'
        linarith [hpow_eq, hineq2]
      exact le_of_mul_le_mul_right h1 hsp_pos
    have hinv_le : 1 / (Real.sqrt |r|) ^ k ≤ 1 := by
      rw [div_le_one hsp_pos]
      exact hge1
    linarith
  -- Contradict `|r| * (√|r|) ^ k ≤ C * |r - r⁻¹| + 1` as `k → ∞`
  have htend : Filter.Tendsto (fun k : ℕ => (Real.sqrt |r|) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hsqrt_gt1
  rw [Filter.tendsto_atTop] at htend
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (htend ((C * |r - r⁻¹| + 2) / |r|))
  have hK' := hK K le_rfl
  have hmul := (div_le_iff₀ (by linarith : (0 : ℝ) < |r|)).mp hK'
  have hb := hbound_k K
  linarith

end OMA.R_RamanujanTau_ramanujan_petersson_R1
