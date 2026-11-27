import FormalConjectures.ErdosProblems.«408»

-- Port of FinalAssembly.lean by Jacob Parish (Plasma AI), Apache-2.0.
-- https://github.com/plasma-ai/erdos-408/tree/4ea44bf911f8
-- The additive height is expressed through the pinned iteration counts on primes.

open Erdos408 Filter
open scoped Topology

namespace OMA.R_Erdos408_erdos_408_parts_ii_R1

def H1 : Prop :=
  let F := fun n : ℕ => ∑ p ∈ n.primeFactors, n.factorization p * (if p = 2 then 1 else f p - 1)
  ∀ n : ℕ, 1 ≤ n → |(f n : ℝ) - F n| ≤ 1

def H2 : Prop :=
  let F := fun n : ℕ => ∑ p ∈ n.primeFactors, n.factorization p * (if p = 2 then 1 else f p - 1)
  ∃ α K : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((F n : ℝ) - α * Real.log x) ^ 2 ≤
        K * (x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 + x * Real.log x)

theorem tendsto_log_log_atTop : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
theorem sq_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ 16 * Real.exp (u / 2) := by
  have h := Real.add_one_le_exp (u / 4)
  have he : Real.exp (u / 2) = Real.exp (u / 4) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [he]
  nlinarith

/-- `∑_{n ≤ N} 1 / √n ≤ 2 √N`, since `1 / √(n + 1) ≤ 2 √(n + 1) - 2 √n`. -/
theorem sum_inv_sqrt_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, 1 / √(n : ℝ) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have ha := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N + 1)
    have hb₀ : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have : 1 / √((N : ℝ) + 1) ≤ 2 * √((N : ℝ) + 1) - 2 * √(N : ℝ) := by
      rw [div_le_iff₀ hb₀]
      nlinarith [sq_nonneg (√(N : ℝ) - √((N : ℝ) + 1))]
    linarith

/-- `∑_{n ≤ x} log² (x / n) ≤ 32 x`. -/
theorem sum_log_div_sq_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / n) ^ 2 ≤ 32 * x := by
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / n) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 16 * √x * (1 / √(n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp hn.2
        have hpos : 0 < x / n := div_pos (by linarith) (by linarith)
        have h := sq_le_exp_half (Real.log_nonneg ((one_le_div (by linarith)).mpr hnx))
        rw [Real.exp_half, Real.exp_log hpos, Real.sqrt_div' _ (by linarith)] at h
        exact h.trans_eq (by ring)
    _ = 16 * √x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 1 / √(n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 16 * √x * (2 * √x) := by
        gcongr
        exact (sum_inv_sqrt_le _).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hx)) (by norm_num))
    _ = 32 * x := by
        rw [show 16 * √x * (2 * √x) = 32 * (√x * √x) by ring, Real.mul_self_sqrt hx]

/-- The variance of `f` about `α log n`: `∑_{n ≤ x} (f n - α log n)² = O(x L² T⁻⁵)`. -/
theorem variance_f (F : ℕ → ℕ)
    (abs_f_sub_F_le_one : ∀ {n : ℕ}, 1 ≤ n → |(f n : ℝ) - F n| ≤ 1)
    (hv : ∃ α K : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((F n : ℝ) - α * Real.log x) ^ 2 ≤
        K * (x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 + x * Real.log x)) :
    ∃ α : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∃ K : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
        K * x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
  obtain ⟨α, K, hα₃, hα₂, hV⟩ := hv
  refine ⟨α, hα₃, hα₂, 8 * |K| + 514, ?_⟩
  -- `T⁵ ≤ L`, so `x L ≤ x L² T⁻⁵`
  have hTL : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 5 ≤ Real.log x := by
    filter_upwards [(Real.isLittleO_pow_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).def
      one_pos, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hL
    simp only [Real.norm_eq_abs, Function.comp_apply, id_eq, one_mul, abs_of_nonneg hL] at hx
    exact (le_abs_self _).trans hx
  filter_upwards [hV, hTL, tendsto_log_log_atTop.eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1] with x hVx hTLx hT hL hx
  set L := Real.log x
  set T := Real.log L
  set N := ⌊x⌋₊
  have hx₀ : 0 ≤ x := by linarith
  have hT5 : 0 < T ^ 5 := pow_pos hT 5
  have hα₀ : 0 ≤ α := le_trans (by positivity) hα₃
  have hα : α ≤ 2 := by
    refine hα₂.trans ?_
    rw [div_le_iff₀ (Real.log_pos one_lt_two)]
    linarith [Real.log_two_gt_d9]
  -- `(f n - α log n)² ≤ 4 (F n - α L)² + 16 log² (x / n) + 2`
  have hpt : ∀ n ∈ Finset.Icc 1 N, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
      4 * ((F n : ℝ) - α * L) ^ 2 + 16 * Real.log (x / n) ^ 2 + 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hfF := abs_le.mp (abs_f_sub_F_le_one hn.1)
    have hlog : Real.log n = L - Real.log (x / n) := by
      rw [Real.log_div (by linarith) (by linarith)]
      ring
    rw [hlog]
    have hα2 : α ^ 2 ≤ 4 := by nlinarith
    nlinarith [sq_nonneg ((f n : ℝ) - F n - ((F n : ℝ) - α * (L - Real.log (x / n)))),
      sq_nonneg ((F n : ℝ) - α * L - α * Real.log (x / n)),
      mul_le_mul_of_nonneg_right hα2 (sq_nonneg (Real.log (x / n)))]
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx₀
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum
  have hlog := sum_log_div_sq_le hx₀
  have hb : x * L ≤ x * L ^ 2 / T ^ 5 := by
    rw [le_div_iff₀ hT5]
    nlinarith [mul_le_mul_of_nonneg_left hTLx (mul_nonneg hx₀ (by linarith : (0 : ℝ) ≤ L))]
  have hxL : x ≤ x * L := le_mul_of_one_le_right hx₀ hL
  have hK : K * (x * L ^ 2 / T ^ 5 + x * L) ≤ |K| * (2 * (x * L ^ 2 / T ^ 5)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K))
  have : (8 * |K| + 514) * x * L ^ 2 / T ^ 5 =
      8 * |K| * (x * L ^ 2 / T ^ 5) + 514 * (x * L ^ 2 / T ^ 5) := by ring
  rw [this]
  linarith

/-- Chebyshev's inequality: if `c ≤ g` on `t ⊆ s` and `g ≥ 0` on `s`, then
`#t ≤ ∑_{n ∈ s} g n / c`. -/
theorem card_le_sum_div {s t : Finset ℕ} {g : ℕ → ℝ} {c : ℝ} (hts : t ⊆ s)
    (hg : ∀ n ∈ s, 0 ≤ g n) (hc : 0 < c) (ht : ∀ n ∈ t, c ≤ g n) :
    (t.card : ℝ) ≤ (∑ n ∈ s, g n) / c := by
  rw [le_div_iff₀ hc]
  calc (t.card : ℝ) * c = ∑ n ∈ t, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ t, g n := Finset.sum_le_sum ht
    _ ≤ ∑ n ∈ s, g n := Finset.sum_le_sum_of_subset_of_nonneg hts fun n hn _ => hg n hn

theorem ncard_setOf_inter_Iio (p : ℕ → Prop) [DecidablePred p] (b : ℕ) :
    ({n | p n} ∩ Set.Iio b).ncard = ((Finset.range b).filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

theorem main : H1 → H2 → type_of% @Erdos408.erdos_408.parts.ii := by
  intro h₁ h₂
  classical
  let F := fun n : ℕ => ∑ p ∈ n.primeFactors, n.factorization p * (if p = 2 then 1 else f p - 1)
  obtain ⟨α, -, -, K, hK⟩ := variance_f F (fun {n} hn => h₁ n hn) h₂
  refine ⟨α, fun ε hε => ?_⟩
  set P : ℕ → Prop := fun n => |(f n : ℝ) / Real.log n - α| < ε
  set c := 4 * |K| / ε ^ 2
  -- the proportion of exceptions below `b` is at most `g b`, and `g b → 0`
  set g : ℝ → ℝ := fun y => (√y)⁻¹ + y⁻¹ + c * (Real.log (Real.log y) ^ 5)⁻¹
  have hg : Tendsto g atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).add
      tendsto_inv_atTop_zero).add ((tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by norm_num : 5 ≠ 0)).comp tendsto_log_log_atTop)).const_mul c)
    simpa using this
  have hbad : ∀ᶠ b : ℕ in atTop,
      (((Finset.range b).filter fun n => ¬ P n).card : ℝ) ≤ b * g b := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hK,
      tendsto_natCast_atTop_atTop.eventually (tendsto_log_log_atTop.eventually_gt_atTop 0),
      tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_gt_atTop 0),
      eventually_ge_atTop 1] with b hKb hT hL hb
    rw [Nat.floor_natCast] at hKb
    set L := Real.log b
    set T := Real.log L
    have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
    have hsq := Real.sqrt_nonneg (b : ℝ)
    set s := (Finset.range b).filter fun n => ¬ P n
    rw [← Finset.card_filter_add_card_filter_not (fun n : ℕ => √(b : ℝ) < n) (s := s)]
    push_cast
    -- at most `√b + 1` exceptions up to `√b`
    have hlow : ((s.filter fun n : ℕ => ¬ √(b : ℝ) < n).card : ℝ) ≤ √b + 1 := by
      have : s.filter (fun n : ℕ => ¬ √(b : ℝ) < n) ⊆ Finset.range (⌊√(b : ℝ)⌋₊ + 1) := by
        intro n hn
        simp only [Finset.mem_filter, not_lt] at hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn.2))
      refine (Nat.cast_le.mpr (Finset.card_le_card this)).trans ?_
      rw [Finset.card_range]
      push_cast
      linarith [Nat.floor_le hsq]
    -- above `√b`, an exception has `(f n - α log n)² ≥ (ε L / 2)²`
    have hhigh : ((s.filter fun n : ℕ => √(b : ℝ) < n).card : ℝ) ≤
        b * (c * (T ^ 5)⁻¹) := by
      have hc : 0 < (ε * L / 2) ^ 2 := by positivity
      have hsub : s.filter (fun n : ℕ => √(b : ℝ) < n) ⊆ Finset.Icc 1 b := by
        intro n hn
        simp only [s, Finset.mem_filter, Finset.mem_range] at hn
        have : (0 : ℝ) < n := hsq.trans_lt hn.2
        exact Finset.mem_Icc.mpr ⟨by exact_mod_cast this, hn.1.1.le⟩
      refine (card_le_sum_div hsub (fun n _ => sq_nonneg ((f n : ℝ) - α * Real.log n)) hc
        ?_).trans ?_
      · intro n hn
        simp only [s, Finset.mem_filter, Finset.mem_range, P, not_lt] at hn
        obtain ⟨⟨-, hP⟩, hsn⟩ := hn
        have hlo : L / 2 < Real.log n := by
          rw [← Real.log_sqrt hb₀.le]
          exact Real.log_lt_log (Real.sqrt_pos.mpr hb₀) hsn
        have hlog₀ : 0 < Real.log n := by linarith
        -- `|f n - α log n| = |f n / log n - α| log n ≥ ε log n`
        have h₁ : ε * L / 2 ≤ |(f n : ℝ) - α * Real.log n| := by
          rw [show (f n : ℝ) - α * Real.log n = ((f n : ℝ) / Real.log n - α) * Real.log n by
            field_simp, abs_mul, abs_of_pos hlog₀]
          nlinarith
        have h₂ := pow_le_pow_left₀ (by positivity) h₁ 2
        rwa [sq_abs] at h₂
      · rw [div_le_iff₀ hc]
        calc ∑ n ∈ Finset.Icc 1 b, ((f n : ℝ) - α * Real.log n) ^ 2
            ≤ K * b * L ^ 2 / T ^ 5 := hKb
          _ ≤ |K| * b * L ^ 2 / T ^ 5 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self K) hb₀.le) (sq_nonneg _)) (pow_pos hT 5).le
          _ = b * (c * (T ^ 5)⁻¹) * (ε * L / 2) ^ 2 := by
            simp only [c]
            field_simp
            ring
    have : (b : ℝ) * g b = √b + 1 + b * (c * (T ^ 5)⁻¹) := by
      simp only [g, mul_add]
      rw [← div_eq_mul_inv, Real.div_sqrt, mul_inv_cancel₀ hb₀.ne']
    rw [this]
    linarith
  have hratio : ∀ᶠ b : ℕ in atTop,
      ((({n | P n} ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard) =
        1 - (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b := by
    filter_upwards [eventually_ge_atTop 1] with b hb
    have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
    have := Finset.card_filter_add_card_filter_not P (s := Finset.range b)
    rw [Finset.card_range] at this
    rw [ncard_setOf_inter_Iio, Set.ncard_Iio_nat, eq_sub_iff_add_eq, ← add_div,
      div_eq_one_iff_eq hb₀.ne']
    exact_mod_cast this
  have h₀ : Tendsto (fun b : ℕ => (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hg.comp tendsto_natCast_atTop_atTop) (Eventually.of_forall fun b => by positivity) ?_
    filter_upwards [hbad, eventually_ge_atTop 1] with b hb hb₁
    rw [Function.comp_apply, div_le_iff₀ (by exact_mod_cast hb₁), mul_comm]
    exact hb
  have : Tendsto (fun b : ℕ => 1 - (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h₀
  rw [sub_zero] at this
  simpa only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter] using
    this.congr' (hratio.mono fun b hb => hb.symm)

end OMA.R_Erdos408_erdos_408_parts_ii_R1
