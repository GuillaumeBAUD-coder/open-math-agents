import FormalConjectures.ErdosProblems.«239»
import Mathlib

/-! The convergent prime series leads to a divisor sum whose mean is obtained
by dominated convergence. In the divergent case, doubling the phase excludes
every nonzero Archimedean twist in Halász's mean-value theorem. -/
-- Credit: @marcusbuffett
namespace OMA.R_Erdos239_erdos_239_R1
open Filter Finset Real
open scoped Topology

private lemma divisor_mean (f g : ℕ → ℝ) (hs : Summable (fun d : ℕ => |g d|/d))
    (hg : ∀ n ≥ 1, f n = ∑ d ∈ n.divisors, g d) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n) / N) atTop
      (𝓝 (∑' d : ℕ, g d / d)) := by
  classical
  let w (N d : ℕ) : ℝ := g d * ((N/d : ℕ) : ℝ) / N
  have hlim (d : ℕ) : Tendsto (fun N : ℕ => w N d) atTop (𝓝 (g d / d)) := by
    have h := (tendsto_nat_floor_mul_div_atTop
      (show 0 ≤ (d : ℝ)⁻¹ by positivity)).comp tendsto_natCast_atTop_atTop
    have hh : Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ) / N) atTop (𝓝 (d : ℝ)⁻¹) := by
      simpa [Function.comp_def, mul_comm (d : ℝ)⁻¹, ← div_eq_mul_inv, Nat.floor_div_eq_div] using h
    simpa [w, div_eq_mul_inv, mul_assoc] using hh.const_mul (g d)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, ‖w N d‖ ≤ |g d| / d := by
    filter_upwards [eventually_gt_atTop 0] with N hN d
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    change ‖g d * ((N/d : ℕ) : ℝ) / N‖ ≤ _
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
    rw [div_le_iff₀ hn]
    have hb := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := N) (n := d)) (abs_nonneg (g d))
    convert hb using 1 <;> ring
  have h := tendsto_tsum_of_dominated_convergence hs hlim hbound
  apply h.congr'
  filter_upwards with N
  change (∑' d, w N d) = _
  rw [tsum_eq_sum (s := range (N+1)) (fun d hd => by
    have hlt : N < d := by simpa using hd
    simp [w, Nat.div_eq_of_lt hlt])]
  simp only [w, ← sum_div]
  congr 1
  have hrewrite (n : ℕ) (hn : n ∈ Icc 1 N) :
      f n = ∑ d ∈ range (N+1), if d ∣ n then g d else 0 := by
    rw [hg n (mem_Icc.mp hn).1, ← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_range]
    obtain ⟨hp, hle⟩ := mem_Icc.mp hn
    exact ⟨fun h => ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd hp h.1).trans hle), h.1⟩,
      fun h => ⟨h.2, by omega⟩⟩
  rw [sum_congr rfl hrewrite, sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have he : (Icc 1 N).filter (d ∣ ·) = (range (N+1)).filter (fun k => k ≠ 0 ∧ d ∣ k) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [he, Nat.card_multiples']

/-- The absolutely convergent case of the Euler product for the convolution
of a sign-valued multiplicative function with the Möbius function. -/
def H1 : Prop :=
  ∀ f : ℕ → ℝ, (∀ n ≥ 1, f n = 1 ∨ f n = -1) →
    (∀ m n, m.Coprime n → f (m*n) = f m * f n) → f 1 = 1 →
    Summable (fun p : Nat.Primes => (1 - f p) / (p.val : ℝ)) →
    ∃ g : ℕ → ℝ, Summable (fun d : ℕ => |g d| / d) ∧
      ∀ n ≥ 1, f n = ∑ d ∈ n.divisors, g d

/-- Halász's mean-zero criterion for bounded real multiplicative functions. -/
def H2 : Prop :=
  ∀ f : ℕ → ℝ, (∀ n ≥ 1, |f n| ≤ 1) →
    (∀ m n, m.Coprime n → f (m*n) = f m * f n) → f 1 = 1 →
    (∀ t : ℝ, ¬ Summable (fun p : Nat.Primes =>
      (1 - f p * cos (t * log p.val)) / p.val)) →
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n) / N) atTop (𝓝 0)

/-- A nonconstant Archimedean character stays at divergent prime distance
from the constant character. -/
def H3 : Prop :=
  ∀ t : ℝ, t ≠ 0 → ¬ Summable (fun p : Nat.Primes =>
    (1 - cos (t * log p.val)) / p.val)

theorem main : H1 → H2 → H3 → type_of% @Erdos239.erdos_239 := by
  intro conv halasz oscill f ⟨hsign, hmul, h1⟩
  by_cases hs : Summable (fun p : Nat.Primes => (1 - f p) / (p.val : ℝ))
  · obtain ⟨g,hg,hfg⟩ := conv f hsign hmul h1 hs
    exact ⟨_, divisor_mean f g hg hfg⟩
  refine ⟨0, halasz f (fun n hn => ?_) hmul h1 ?_⟩
  · rcases hsign n hn with h|h <;> simp [h]
  intro t ht
  by_cases hzero : t = 0
  · subst t
    exact hs (by simpa using ht)
  apply oscill (2*t) (mul_ne_zero (by norm_num) hzero)
  apply Summable.of_nonneg_of_le (f := fun p : Nat.Primes =>
    4 * ((1 - f p * cos (t * log p.val)) / p.val))
  · intro p
    exact div_nonneg (sub_nonneg.mpr (cos_le_one _)) (Nat.cast_nonneg _)
  · intro p
    rw [mul_assoc 2 t, cos_two_mul, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rcases hsign p p.property.one_lt.le with hp|hp <;>
      rw [hp] <;> nlinarith [sq_nonneg (1 + cos (t * log p.val)),
        sq_nonneg (1 - cos (t * log p.val))]
  · exact ht.mul_left 4

end OMA.R_Erdos239_erdos_239_R1
