import FormalConjectures.ErdosProblems.«437»
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Smooth-number reduction for Tao's bounds on square partial products

The lower and upper combinatorial estimates and the smooth-number asymptotic are separate
hypotheses. The proof combines them at the same smoothness cutoff and constructs the two
vanishing error terms.
-/

namespace OMA.R_Erdos437_erdos_437_variants_tao_R1

open Erdos437 Filter Real
open scoped Topology

/-- Partition the smooth numbers into blocks of at most the cutoff size. -/
def H1 : Prop :=
  ∀ x y : ℕ, 1 ≤ y →
    ((x.smoothNumbersUpTo y).card : ℝ) ≤ ((L x : ℝ) + 1) * (y : ℝ)

/-- Each square-producing block uses a smooth number, contains a multiple of a large
prime square, or spans a gap at least as wide as the smoothness cutoff. -/
def H2 : Prop :=
  ∀ x y : ℕ, 2 ≤ y →
    (L x : ℝ) ≤ (x.smoothNumbersUpTo y).card + 3 * (x : ℝ) / (y : ℝ)

/-- The smooth-number count at the cutoff used in Tao's proof. The cutoff is strict
on prime factors, following Mathlib's convention. -/
def H3 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let t := √(log (x : ℝ) * log (log (x : ℝ)))
    let c := (√(2 : ℝ))⁻¹
    let y := ⌈exp (c * t)⌉₊
    (x : ℝ) * exp (-(c + δ) * t) ≤ (x.smoothNumbersUpTo y).card ∧
      (x.smoothNumbersUpTo y).card ≤ (x : ℝ) * exp (-(c - δ) * t)

lemma one_le_L {x : ℕ} (hx : 1 ≤ x) : 1 ≤ L x := by
  unfold L
  apply le_csSup
  · refine ⟨x, ?_⟩
    rintro m ⟨a, ha, hax, rfl⟩
    have hsubset : a.toFinset ⊆ Finset.Icc 1 x := fun n hn ↦ hax n (List.mem_toFinset.mp hn)
    have hcard := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup (ha.imp fun h ↦ ne_of_lt h), Nat.card_Icc] at hcard
    unfold squarePartialProducts
    exact (Finset.card_filter_le _ _).trans (by simpa using hcard)
  · exact ⟨[1], by simp, by simpa, by decide⟩

lemma eventual_bounds (hLower : H1) (hUpper : H2) (hSmooth : H3) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      let t := √(log (x : ℝ) * log (log (x : ℝ)))
      (x : ℝ) * exp (-(√2 + δ) * t) ≤ L x ∧
        (L x : ℝ) ≤ (x : ℝ) * exp (-((√2)⁻¹ - δ) * t) := by
  let t (x : ℕ) := √(log (x : ℝ) * log (log (x : ℝ)))
  let c : ℝ := (√(2 : ℝ))⁻¹
  have hc : 0 < c := by positivity
  have hDouble : 2 * c = √(2 : ℝ) := by
    have hs : 0 < √(2 : ℝ) := by positivity
    dsimp [c]
    rw [← div_eq_mul_inv, div_eq_iff hs.ne']
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hLog : Tendsto (fun x : ℕ ↦ log (x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop atTop :=
    tendsto_sqrt_atTop.comp (hLog.atTop_mul_atTop₀ (tendsto_log_atTop.comp hLog))
  have hExtra : Tendsto (fun x ↦ exp (δ / 2 * t x)) atTop atTop :=
    tendsto_exp_atTop.comp (ht.const_mul_atTop (half_pos hδ))
  have hCutoff : Tendsto (fun x ↦ exp (c * t x)) atTop atTop :=
    tendsto_exp_atTop.comp (ht.const_mul_atTop hc)
  filter_upwards [hSmooth (δ / 2) (half_pos hδ),
    hExtra.eventually (eventually_ge_atTop (4 : ℝ)),
    hCutoff.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with x hΨ hFour hTwo hx
  let y : ℕ := ⌈exp (c * t x)⌉₊
  have hCeil : exp (c * t x) ≤ (y : ℝ) := Nat.le_ceil _
  have hy : 2 ≤ y := by exact_mod_cast hTwo.trans hCeil
  have hyUpper : (y : ℝ) ≤ 2 * exp (c * t x) := by
    have hlt := Nat.ceil_lt_add_one (exp_pos (c * t x)).le
    change (y : ℝ) < exp (c * t x) + 1 at hlt
    linarith
  have hL : 1 ≤ (L x : ℝ) := by exact_mod_cast one_le_L hx
  have hX : 0 ≤ (x : ℝ) := by positivity
  have htNonneg : 0 ≤ t x := sqrt_nonneg _
  change (x : ℝ) * exp (-(c + δ / 2) * t x) ≤ (x.smoothNumbersUpTo y).card ∧
    (x.smoothNumbersUpTo y).card ≤ (x : ℝ) * exp (-(c - δ / 2) * t x) at hΨ
  change (x : ℝ) * exp (-(√2 + δ) * t x) ≤ L x ∧
    (L x : ℝ) ≤ (x : ℝ) * exp (-(c - δ) * t x)
  constructor
  · have hProd : ((x : ℝ) * exp (-(√2 + δ) * t x) * exp (c * t x)) *
        exp (δ / 2 * t x) = (x : ℝ) * exp (-(c + δ / 2) * t x) := by
      rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add, ← hDouble]
      congr 2 <;> ring
    refine le_of_mul_le_mul_right (a := 4 * exp (c * t x)) ?_ (by positivity)
    calc
      (x : ℝ) * exp (-(√2 + δ) * t x) * (4 * exp (c * t x)) =
          ((x : ℝ) * exp (-(√2 + δ) * t x) * exp (c * t x)) * 4 := by ring
      _ ≤ ((x : ℝ) * exp (-(√2 + δ) * t x) * exp (c * t x)) *
          exp (δ / 2 * t x) := mul_le_mul_of_nonneg_left hFour (by positivity)
      _ = (x : ℝ) * exp (-(c + δ / 2) * t x) := hProd
      _ ≤ (x.smoothNumbersUpTo y).card := hΨ.1
      _ ≤ ((L x : ℝ) + 1) * (y : ℝ) := hLower x y (by omega)
      _ ≤ (L x : ℝ) * (4 * exp (c * t x)) := by
        calc
          ((L x : ℝ) + 1) * (y : ℝ) ≤ (2 * (L x : ℝ)) * (2 * exp (c * t x)) :=
            mul_le_mul (by linarith) hyUpper (by positivity) (by positivity)
          _ = _ := by ring
  · let bound := (x : ℝ) * exp (-(c - δ / 2) * t x)
    have hExp : exp (-(c * t x)) ≤ exp (-(c - δ / 2) * t x) :=
      exp_le_exp.mpr (by nlinarith)
    have hTail : 3 * (x : ℝ) / (y : ℝ) ≤ 3 * bound := by
      calc
        3 * (x : ℝ) / (y : ℝ) ≤ 3 * (x : ℝ) / exp (c * t x) :=
          div_le_div_of_nonneg_left (by positivity) (exp_pos _) hCeil
        _ = 3 * (x : ℝ) * exp (-(c * t x)) := by rw [exp_neg, div_eq_mul_inv]
        _ ≤ 3 * bound := by
          dsimp [bound]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hExp (by positivity)
    calc
      (L x : ℝ) ≤ (x.smoothNumbersUpTo y).card + 3 * (x : ℝ) / (y : ℝ) := hUpper x y hy
      _ ≤ bound + 3 * bound := add_le_add hΨ.2 hTail
      _ = bound * 4 := by ring
      _ ≤ bound * exp (δ / 2 * t x) := mul_le_mul_of_nonneg_left hFour (by positivity)
      _ = (x : ℝ) * exp (-(c - δ) * t x) := by
        dsimp [bound]
        rw [mul_assoc, ← exp_add]
        congr 2 <;> ring

lemma lower_iff {x y t a : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    x * exp (-a * t) ≤ y ↔ (log x - log y) / t ≤ a := by
  rw [← log_le_log_iff (mul_pos hx (exp_pos _)) hy, log_mul hx.ne' (exp_ne_zero _), log_exp,
    div_le_iff₀ ht]
  constructor <;> intro h <;> linarith

lemma upper_iff {x y t a : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    y ≤ x * exp (-a * t) ↔ a ≤ (log x - log y) / t := by
  rw [← log_le_log_iff hy (mul_pos hx (exp_pos _)), log_mul hx.ne' (exp_ne_zero _), log_exp,
    le_div_iff₀ ht]
  constructor <;> intro h <;> linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos437.erdos_437.variants.tao := by
  intro hLower hUpper hSmooth
  let t (x : ℕ) := √(log (x : ℝ) * log (log (x : ℝ)))
  let ratio (x : ℕ) := (log (x : ℝ) - log (L x : ℝ)) / t x
  let c : ℝ := (√(2 : ℝ))⁻¹
  let lo (x : ℕ) := max 0 (ratio x - √2)
  let hi (x : ℕ) := min 0 (ratio x - c)
  have hLog : Tendsto (fun x : ℕ ↦ log (x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPos : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) ∧ 0 < (L x : ℝ) ∧ 0 < t x := by
    filter_upwards [hLog.eventually (eventually_gt_atTop (1 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with x hLogx hx
    have hx' : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hx)
    have hL' : 0 < (L x : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_L hx))
    exact ⟨hx', hL', sqrt_pos.2 (mul_pos (zero_lt_one.trans hLogx) (log_pos hLogx))⟩
  have hRatio (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℕ in atTop,
      ratio x ≤ √2 + δ ∧ c - δ ≤ ratio x := by
    filter_upwards [hPos, eventual_bounds hLower hUpper hSmooth δ hδ] with x hp hb
    exact ⟨(lower_iff hp.1 hp.2.1 hp.2.2).mp hb.1, (upper_iff hp.1 hp.2.1 hp.2.2).mp hb.2⟩
  refine ⟨lo, hi, Metric.tendsto_nhds.mpr ?_, Metric.tendsto_nhds.mpr ?_, ?_⟩
  · intro δ hδ
    filter_upwards [hRatio (δ / 2) (half_pos hδ)] with x h
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
    exact max_lt hδ (by linarith [h.1])
  · intro δ hδ
    filter_upwards [hRatio (δ / 2) (half_pos hδ)] with x h
    rw [Real.dist_eq, sub_zero, abs_of_nonpos (min_le_left _ _), neg_lt]
    exact lt_min (by linarith) (by linarith [h.2])
  · filter_upwards [hPos] with x hp
    refine ⟨(lower_iff hp.1 hp.2.1 hp.2.2).mpr ?_, (upper_iff hp.1 hp.2.1 hp.2.2).mpr ?_⟩
    · have h := le_max_right (0 : ℝ) (ratio x - √2)
      dsimp [lo]
      linarith
    · have h := min_le_right (0 : ℝ) (ratio x - c)
      dsimp [hi]
      change c + min 0 (ratio x - c) ≤ ratio x
      linarith

end OMA.R_Erdos437_erdos_437_variants_tao_R1
