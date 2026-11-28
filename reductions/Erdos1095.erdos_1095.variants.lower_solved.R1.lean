import FormalConjectures.ErdosProblems.«1095»
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Konyagin’s lower bound for the Erdős–Selfridge function

The proof is reduced to a short-interval prime count and a specialized bound on
rational points close to a reciprocal curve. The window, denominator size,
counting functions and quantifier order are explicit. The same prime estimate
alone gives the preliminary lower bound of order k²/log k.

The method follows S. V. Konyagin, *Estimates of the least prime factor of a
binomial coefficient*, Mathematika 46 (1999), 41–55, and O. Trifonov,
*Integer points close to a smooth curve*, Theorems 6 and 9. The prime supply
is the classical short-interval theorem as used by Trifonov. The reciprocal
input is stated for the precise one-sided count used here. The elementary
small-offset argument follows E. F. Ecklund Jr., *On prime divisors of the
binomial coefficient* (1969). The composite-neighbour argument is from
P. Erdős, C. Lacampagne and J. Selfridge (1993), Theorem 2. The finite
certificates use the carry criterion from @desenyon’s reduction #1901.
-/

namespace OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1
/-- A uniform lower count for primes in (x,x+y] when x^(3/4) ≤ y ≤ x.
This is a classical short-interval prime theorem. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ X : ℕ, ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x →
    a * (y : ℝ) / Real.log x ≤ ((Finset.Ioc x (x+y)).filter Nat.Prime).card
end OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1

namespace RoughBinomial

/-- Shifting the top index by a multiple of `k! * m` preserves the binomial
coefficient modulo `m`.  We need only the shift from the diagonal. -/
theorem choose_shift_diagonal (k m t : ℕ) (shift : k.factorial * m ∣ t) :
    (t + k).choose k ≡ 1 [MOD m] := by
  have step : (t + 1) ≡ 1 [MOD k.factorial * m] := by
    simpa using shift.modEq_zero_nat.add_right 1
  have asc (j : ℕ) :
      (t + 1).ascFactorial j ≡ (1 : ℕ).ascFactorial j [MOD k.factorial * m] := by
    induction j with
    | zero => exact Nat.ModEq.rfl
    | succ j ih =>
      rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
      exact (step.add_right j).mul ih
  apply Nat.ModEq.mul_left_cancel' k.factorial_ne_zero
  have both := asc k
  rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.one_ascFactorial] at both
  simpa only [Nat.mul_one] using both

theorem factorial_square_witness {k : ℕ} (hk : 2 ≤ k) :
    k + 1 < k.factorial ^ 2 + k ∧ k < ((k.factorial ^ 2 + k).choose k).minFac := by
  have hf : 2 ≤ k.factorial := Nat.factorial_le (m := 2) hk
  have hsq : 4 ≤ k.factorial ^ 2 := by
    simpa only [Nat.reducePow] using Nat.pow_le_pow_left hf 2
  refine ⟨by omega, ?_⟩
  by_contra! hsmall
  let p := ((k.factorial ^ 2 + k).choose k).minFac
  have hp : p.Prime := Nat.minFac_prime (fun h => by
    rcases Nat.choose_eq_one_iff.mp h with h | h <;> omega)
  have hpk : p ≤ k := hsmall
  have hcong := (choose_shift_diagonal k k.factorial (k.factorial ^ 2)
    (by simpa only [pow_two] using dvd_refl (k.factorial * k.factorial))).of_dvd (Nat.dvd_factorial hp.pos hpk)
  have hdiv : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp
    (hcong.symm.trans (Nat.minFac_dvd _).modEq_zero_nat)
  exact hp.ne_one (Nat.dvd_one.mp hdiv)

theorem rough_infimum_spec {k : ℕ} (hk : 2 ≤ k) :
    let A := {m : ℕ | k + 1 < m ∧ k < (m.choose k).minFac}
    sInf A ∈ A ∧ sInf A ≤ k.factorial ^ 2 + k := by
  let A := {m : ℕ | k + 1 < m ∧ k < (m.choose k).minFac}
  have mem : k.factorial ^ 2 + k ∈ A := factorial_square_witness hk
  exact ⟨Nat.sInf_mem ⟨_, mem⟩, Nat.sInf_le mem⟩

end RoughBinomial

namespace RoughBinomial

theorem g_attained {k : ℕ} (hk : 2 ≤ k) :
    k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac :=
  (rough_infimum_spec hk).1

theorem g_le_factorial_square {k : ℕ} (hk : 2 ≤ k) :
    Erdos1095.g k ≤ k.factorial ^ 2 + k :=
  (rough_infimum_spec hk).2

theorem eventually_g_attained :
    ∀ᶠ k : ℕ in Filter.atTop,
      k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac :=
  Filter.eventually_atTop.2 ⟨2, fun _ hk => g_attained hk⟩

end RoughBinomial

namespace RoughBinomial

theorem units_digit_le {n k p : ℕ} (hp : p.Prime) (pk : p ≤ k)
    (rough : k < (n.choose k).minFac) : k % p ≤ n % p := by
  by_contra! h
  let : Fact p.Prime := ⟨hp⟩
  have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hc
  have hm := Nat.minFac_le_of_dvd hp.two_le (Nat.modEq_zero_iff_dvd.mp hc)
  omega

/-- If wp is the first multiple of p above k, the next multiple above n is
within wp-k of n. This is the integer numerator of the approximation to n/(wp). -/
theorem gap_to_next_multiple {n k p w : ℕ} (hp : p.Prime) (pk : p ≤ k)
    (rough : k < (n.choose k).minFac) (above : k < w * p) (nearby : w * p < k + p) :
    0 < p * (n / p + 1) - n ∧ p * (n / p + 1) - n ≤ w * p - k := by
  have hk := Nat.mod_add_div k p
  have hn := Nat.mod_add_div n p
  have kr := Nat.mod_lt k hp.pos
  have nr := Nat.mod_lt n hp.pos
  have digit := units_digit_le hp pk rough
  have next : w = k / p + 1 := by
    have lo : k / p < w := (Nat.div_lt_iff_lt_mul hp.pos).mpr above
    by_contra! h
    have far : k / p + 2 ≤ w := by omega
    have mul := Nat.mul_le_mul_left p far
    rw [Nat.mul_add] at mul
    rw [Nat.mul_comm w p] at nearby
    omega
  rw [next, Nat.mul_comm (k / p + 1) p, Nat.mul_add, Nat.mul_add]
  omega

/-- Konyagin's rational point has a numerator given by the next p-block.
Its error is positive and at most the relative displacement of wp from k. -/
theorem rational_approximation {n k p w : ℕ} (hp : p.Prime) (pk : p ≤ k)
    (rough : k < (n.choose k).minFac) (above : k < w * p) (nearby : w * p < k + p) :
    ∃ v : ℕ, 0 < (v : ℝ) / w - (n : ℝ) / (w * p) ∧
      (v : ℝ) / w - (n : ℝ) / (w * p) ≤ ((w * p : ℕ) - k : ℝ) / (w * p) := by
  obtain ⟨hpos, hle⟩ := gap_to_next_multiple hp pk rough above nearby
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at above)
  have pp : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have wp : 0 < (w : ℝ) := by exact_mod_cast hw
  have hwp : (0 : ℝ) < (w : ℝ) * p := by positivity
  have pos : n < p * (n / p + 1) := by omega
  have bound : p * (n / p + 1) + k ≤ w * p + n := by omega
  have realpos : (n : ℝ) < (p : ℝ) * ((n / p + 1 : ℕ) : ℝ) := by exact_mod_cast pos
  have realbound : (p : ℝ) * ((n / p + 1 : ℕ) : ℝ) + k ≤ (w : ℝ) * p + n := by exact_mod_cast bound
  refine ⟨n / p + 1, ?_⟩
  have identity : ((n / p + 1 : ℕ) : ℝ) / w - (n : ℝ) / (w * p) =
      ((p : ℝ) * ((n / p + 1 : ℕ) : ℝ) - n) / (w * p) := by
    field_simp [pp.ne', wp.ne']
  rw [identity]
  constructor
  · exact div_pos (sub_pos.mpr realpos) hwp
  · apply (div_le_div_iff_of_pos_right hwp).mpr
    rw [Nat.cast_mul]
    linarith only [realbound]

end RoughBinomial

namespace RoughBinomial
open Finset

theorem products_subset_nearPoints {k n H W : ℕ} (hk : 0 < k)
    (rough : k < (n.choose k).minFac) : (fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k H W ⊆ (fun (k n H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ v : ℕ, 0 < (v:ℝ)/w-(n:ℝ)/u ∧
    (v:ℝ)/w-(n:ℝ)/u ≤ (H:ℝ)/k)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k n H W := by
  classical
  intro u hu
  simp only [mem_filter] at hu
  simp only [mem_filter]
  obtain ⟨inside, w, hw, p, prime, pk, eq, close⟩ := hu
  have bounds := mem_Ioc.mp inside
  obtain ⟨v, pos, err⟩ := rational_approximation prime pk rough (eq ▸ bounds.1) (eq ▸ close)
  refine ⟨inside, w, hw, v, ?_⟩
  have up : (0 : ℝ) < u := by exact_mod_cast (lt_trans hk bounds.1)
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  have ku : (k : ℝ) ≤ u := by exact_mod_cast bounds.1.le
  have width : (u : ℝ) - k ≤ H := by
    have h : (u : ℝ) ≤ k + H := by exact_mod_cast bounds.2
    linarith
  have identity : (u : ℝ) = (w : ℝ)*p := by exact_mod_cast eq
  rw [← identity, ← eq] at err
  rw [← identity] at pos
  exact ⟨pos, err.trans ((div_le_div_of_nonneg_right width up.le).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg H) kp ku))⟩

theorem small_factor_of_count_gap {k n H W : ℕ} (hk : 0 < k)
    (gap : ((fun (k n H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ v : ℕ, 0 < (v:ℝ)/w-(n:ℝ)/u ∧
    (v:ℝ)/w-(n:ℝ)/u ≤ (H:ℝ)/k)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k n H W).card < ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k H W).card) :
    (n.choose k).minFac ≤ k := by
  by_contra! rough
  exact (Nat.not_le_of_lt gap) (Finset.card_le_card (products_subset_nearPoints hk rough))

end RoughBinomial

namespace RoughBinomial
open Filter Asymptotics Real

/-- A lower density of products and a smaller upper density of nearby rational
points, with the same H and W, rule out every small rough binomial. -/
theorem lower_of_density_bounds
    (g : ℕ → ℕ)
    (c lower upper : ℝ) (sep : upper < lower)
    (H W threshold : ℕ → ℕ)
    (attains : ∀ᶠ k in atTop, k + 1 < g k ∧ k < ((g k).choose k).minFac)
    (preliminary : ∀ᶠ k in atTop, threshold k ≤ g k)
    (products_many : ∀ᶠ k in atTop,
      0 < H k ∧ lower * (H k : ℝ) ≤ ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k (H k) (W k)).card)
    (points_few : ∀ᶠ k in atTop, ∀ n : ℕ, k+1 < n → threshold k ≤ n → (n : ℝ) < exp (c * log k ^ 2) →
      (((fun (k n H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ v : ℕ, 0 < (v:ℝ)/w-(n:ℝ)/u ∧
    (v:ℝ)/w-(n:ℝ)/u ≤ (H:ℝ)/k)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k n (H k) (W k)).card : ℝ) ≤ upper * (H k : ℝ)) :
    (fun k : ℕ ↦ exp (c * log k ^ 2)) =O[atTop] fun k ↦ (g k : ℝ) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [attains, preliminary, products_many, points_few, eventually_ge_atTop 1] with k atG prev many few hk
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Nat.abs_cast, one_mul]
  by_contra! small
  have gap : ((fun (k n H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ v : ℕ, 0 < (v:ℝ)/w-(n:ℝ)/u ∧
    (v:ℝ)/w-(n:ℝ)/u ≤ (H:ℝ)/k)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k (g k) (H k) (W k)).card < ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k (H k) (W k)).card := by
    have strict := mul_lt_mul_of_pos_right sep (show 0 < (H k : ℝ) by exact_mod_cast many.1)
    exact_mod_cast ((few (g k) atG.1 prev small).trans_lt (strict.trans_le many.2))
  exact (Nat.not_le_of_lt atG.2) (small_factor_of_count_gap (by omega) gap)

end RoughBinomial

namespace Erdos1095

/-- Rounding down loses at most half whenever the quotient is positive. -/
theorem floor_double (q t : ℕ) (qpos : 0 < q) (room : q≤ t) : t≤ 2*q*(t/q) := by
  have pos := Nat.div_pos room qpos
  have hq : q ≤ q*(t/q) := by simpa using Nat.mul_le_mul_left q pos
  have rem := Nat.mod_lt t qpos
  have total := Nat.mod_add_div t q
  rw [show 2*q*(t/q)=q*(t/q)+q*(t/q) by ring]
  omega

/-- The fourth-power inequality absorbs both integer roundings in the short interval. -/
theorem short_scale_aux {b k w : ℕ} (hb : 2≤ b) (hk : b^80≤ k) (hw : 2≤ w) (hwB : w≤ b) :
    let D := b^10*w
    let y := k/b^10/w
    D≤ k ∧ k ≤ 2*D*y ∧ 16*D^4≤ k ∧ k^3≤ y^4 := by
  intro D y
  have bp : 0 < b := by omega
  have dp : 0 < D := Nat.mul_pos (pow_pos bp _) (by omega)
  have cap : D ≤ b^11 := (Nat.mul_le_mul_left (b^10) hwB).trans_eq (pow_succ b 10).symm
  have room : D≤ k := cap.trans ((Nat.pow_le_pow_right bp (by decide : 11≤ 80)).trans hk)
  have len : y = k/D := Nat.div_div_eq_div_mul _ _ _
  have approx : k ≤ 2*D*y := by rw [len]; exact floor_double D k dp room
  have sixteen : 16 ≤ b^4 := Nat.pow_le_pow_left hb 4
  have absorb : 16*D^4 ≤ k := calc
    _ ≤ b^4*(b^11)^4 := Nat.mul_le_mul sixteen (Nat.pow_le_pow_left cap 4)
    _ = b^48 := by ring
    _ ≤ k := (Nat.pow_le_pow_right bp (by decide : 48≤ 80)).trans hk
  have kp : 0 < k := dp.trans_le room
  have combined : k*k^3 ≤ k*y^4 := calc
    _ = k^4 := by ring
    _ ≤ (2*D*y)^4 := Nat.pow_le_pow_left approx 4
    _ = 16*D^4*y^4 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ absorb
  exact ⟨room,approx,absorb,(Nat.le_of_mul_le_mul_left combined kp)⟩

theorem short_scale {b k w : ℕ} (hb : 2≤ b) (hk : b^80≤ k) (hw : 2≤ w) (hwB : w≤ b) :
    let H:=k/b^10
    let x:=k/w
    let y:=H/w
    x^3≤ y^4 ∧ y≤ x ∧ b≤ x ∧ H≤ 2*w*y ∧ b^2≤ k ∧ H*b≤ k ∧ H≤ k ∧ 0 < H := by
  intro H x y
  obtain ⟨room,_,_,power⟩ := short_scale_aux hb hk hw hwB
  have bp : 0 < b := by omega
  have wp : 0 < w := by omega
  have b10 : b≤ b^10 := by simpa using (Nat.pow_le_pow_right bp (by decide : 1≤ 10))
  have b2 : b^2≤ k := (Nat.pow_le_pow_right bp (by decide : 2≤ 80)).trans hk
  have Hle : H≤ k := Nat.div_le_self _ _
  have wH : w≤ H := (Nat.le_div_iff_mul_le (pow_pos bp 10)).mpr (by simpa only [Nat.mul_comm w] using room)
  have bw : b*w≤ k := (Nat.mul_le_mul_left b hwB).trans (by simpa only [sq] using b2)
  exact ⟨(Nat.pow_le_pow_left (Nat.div_le_self k w) 3).trans power,Nat.div_le_div_right Hle,
    (Nat.le_div_iff_mul_le wp).mpr bw, floor_double w H wp wH,b2,
    (Nat.mul_le_mul_left H b10).trans (Nat.div_mul_le_self k (b^10)),Hle,wp.trans_le wH⟩

end Erdos1095

namespace RoughBinomial

open Finset Filter

/-- Each complete dyadic interval contributes at least one half. -/
theorem dyadic_reciprocals (e : ℕ) :
    (e : ℝ) / 2 ≤ ∑ w ∈ Ioc 1 (2 ^ e : ℕ), 1 / (w : ℝ) := by
  have block (a : ℕ) (ha : 0 < a) :
      (1 : ℝ) / 2 ≤ ∑ w ∈ Ioc a (a + a), 1 / (w : ℝ) := by
    calc
      _ = ∑ _w ∈ Ioc a (a+a), (1 : ℝ) / ((a+a : ℕ) : ℝ) := by
        simp only [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add]
        have pos : (0 : ℝ) < a := by exact_mod_cast ha
        field_simp
        ring
      _ ≤ _ := Finset.sum_le_sum (fun w hw => by
        obtain ⟨lo, hi⟩ := Finset.mem_Ioc.mp hw
        exact one_div_le_one_div_of_le (by exact_mod_cast (ha.trans lo))
          (by exact_mod_cast hi))
  induction e with
  | zero => simp
  | succ e ih =>
    have pos : 0 < (2 : ℕ)^e := by positivity
    rw [pow_succ, Nat.mul_two, ← Finset.sum_Ioc_consecutive _
      (Nat.one_le_iff_ne_zero.mpr pos.ne') (Nat.le_add_right _ _)]
    have step := block (2 ^ e) pos
    push_cast
    linarith

theorem weight_power_le {k : ℕ} (hk : 0 < k) :
    (2 ^ (Nat.log 2 k / 80) : ℕ)^80 ≤ k := by
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : Nat.log 2 k / 80 * 80 ≤ Nat.log 2 k)).trans
    (Nat.pow_log_le_self 2 hk.ne')

theorem weight_tendsto :
    Tendsto (fun k : ℕ => 2 ^ (Nat.log 2 k / 80) : ℕ → ℕ) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (80*n) : ℕ)] with k hk
  have lo := Nat.le_log_of_pow_le (by decide : 1 < 2) hk
  calc
    n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ (Nat.log 2 k / 80) := Nat.pow_le_pow_right (by decide) (by omega)

theorem dyadic_weights_lower {k : ℕ} (hk : 2^80 ≤ k) :
    (1/320 : ℝ) * Real.log k ≤ ∑ w ∈ Icc 2 (2^(Nat.log 2 k/80) : ℕ), 1/(w:ℝ) := by
  let d := Nat.log 2 k
  let e := d/80
  have hd : 80 ≤ d := Nat.le_log_of_pow_le (by decide : 1 < 2) hk
  have cap : d + 1 ≤ 160*e := by dsimp [e]; omega
  have kp : 0 < k := lt_of_lt_of_le (by positivity) hk
  have logcap : Real.log k ≤ (d+1 : ℕ) := by
    calc
      _ ≤ Real.log ((2:ℝ)^(d+1)) := Real.log_le_log (by exact_mod_cast kp)
        (by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1< 2) k).le)
      _ = ((d+1 : ℕ):ℝ)*Real.log 2 := Real.log_pow _ _
      _ ≤ _ := mul_le_of_le_one_right (by positivity)
        (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)< 2)])
  have capR : ((d+1:ℕ):ℝ) ≤ 160*(e:ℝ) := by exact_mod_cast cap
  have sets : Icc 2 (2 ^ e : ℕ) = Ioc 1 (2^e) := by
    ext w
    simp only [mem_Icc, mem_Ioc]
    omega
  change _ ≤ ∑ w ∈ Icc 2 (2^e : ℕ), 1 / (w:ℝ)
  rw [sets]
  linarith [dyadic_reciprocals e]

end RoughBinomial

namespace RoughBinomial
open Finset

theorem primeRows_le_products {k H W : ℕ} (hsquare : W * W ≤ k)
    (hwidth : H * W ≤ k) (hsmall : H ≤ k) :
    (∑ w ∈ Icc 2 W, ((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w).card) ≤ ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k H W).card := by
  classical
  let rows := (Icc 2 W).sigma ((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H)
  let f : (Σ _w : ℕ, ℕ) → ℕ := fun a => a.1 * a.2
  have row {w p : ℕ} (hw : w ∈ Icc 2 W) (hp : p ∈ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w) :
      p.Prime ∧ k < w*p ∧ w*p ≤ k+H ∧ W < p ∧ H < p ∧ p ≤ k := by
    obtain ⟨wl, wu⟩ := mem_Icc.mp hw
    obtain ⟨inside, prime⟩ := mem_filter.mp hp
    obtain ⟨lo, hi⟩ := mem_Ioc.mp inside
    have wp : 0 < w := by omega
    have lb := (Nat.div_lt_iff_lt_mul wp).mp lo
    have ub := (Nat.le_div_iff_mul_le wp).mp hi
    have sepW : W < p := by
      by_contra! bad
      exact (not_lt_of_ge ((Nat.mul_le_mul bad wu).trans hsquare)) lb
    have sepH : H < p := by
      by_contra! bad
      exact (not_lt_of_ge ((Nat.mul_le_mul bad wu).trans hwidth)) lb
    have two : p*2 ≤ k+H := (Nat.mul_le_mul_left p wl).trans ub
    have pk := two.trans (Nat.add_le_add_left hsmall k)
    rw [Nat.mul_comm p w] at lb ub
    exact ⟨prime, lb, ub, sepW, sepH, by omega⟩
  have maps : Set.MapsTo f rows ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k H W) := by
    rintro ⟨w,p⟩ ha
    obtain ⟨hw,hp⟩ := mem_sigma.mp ha
    change w ∈ Icc 2 W at hw
    change p ∈ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w at hp
    obtain ⟨prime,lo,hi,_,far,pk⟩ := row hw hp
    simp only [mem_coe, mem_filter, mem_Ioc, f]
    exact ⟨⟨lo,hi⟩,w,hw,p,prime,pk,rfl,hi.trans_lt (Nat.add_lt_add_left far k)⟩
  have inj : Set.InjOn f rows := by
    rintro ⟨w,p⟩ ha ⟨v,q⟩ hb eq
    obtain ⟨hw, hp⟩ := mem_sigma.mp ha
    obtain ⟨hv, hq⟩ := mem_sigma.mp hb
    change w ∈ Icc 2 W at hw
    change v ∈ Icc 2 W at hv
    change p ∈ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w at hp
    change q ∈ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H v at hq
    obtain ⟨pp,_,_,pw,_,_⟩ := row hw hp
    have qp := (row hv hq).1
    change w*p = v*q at eq
    have divides : p ∣ v*q := eq ▸ dvd_mul_left p w
    have pq : p = q := by
      rcases pp.dvd_mul.mp divides with dv | dq
      · have vp := Nat.le_of_dvd (show 0 < v by have := (mem_Icc.mp hv).1; omega) dv
        have := (mem_Icc.mp hv).2
        omega
      · exact (Nat.prime_dvd_prime_iff_eq pp qp).mp dq
    subst q
    have wv := Nat.eq_of_mul_eq_mul_right pp.pos eq
    subst v
    rfl
  simpa [rows, Finset.card_sigma] using Finset.card_le_card_of_injOn f maps inj

end RoughBinomial

namespace RoughBinomial
open Finset Real

theorem one_prime_row {k H w X : ℕ} {a : ℝ} (ha : 0 < a)
    (estimate : ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x →
      a * (y : ℝ) / log x ≤ ((Ioc x (x+y)).filter Nat.Prime).card)
    (hw : 2 ≤ w) (reach : X ≤ k/w) (big : 2 ≤ k/w)
    (power : (k/w)^3 ≤ (H/w)^4) (width : H/w ≤ k/w) (cover : H ≤ 2*w*(H/w)) :
    (a * H / (2 * log k)) * (1 / (w : ℝ)) ≤ ((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w).card := by
  have wp : 0 < w := by omega
  have xk := Nat.div_le_self k w
  have xp : (1 : ℝ) < (k/w : ℕ) := by exact_mod_cast (show 1 < k/w by omega)
  have wpos : 0 < (w : ℝ) := by exact_mod_cast wp
  have xlog := log_pos xp
  have logs : log (k/w : ℕ) ≤ log (k : ℝ) :=
    log_le_log (by positivity) (by exact_mod_cast xk)
  have klog := lt_of_lt_of_le xlog logs
  have inc : (Ioc (k/w) (k/w+H/w)).filter Nat.Prime ⊆ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w := by
    intro p hp
    obtain ⟨inside,prime⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp inside).1, (mem_Ioc.mp inside).2.trans ?_⟩,prime⟩
    apply (Nat.le_div_iff_mul_le wp).mpr
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self k w) (Nat.div_mul_le_self H w)
  have prime : a*(H/w : ℕ)/log (k/w : ℕ) ≤ (((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w).card : ℝ) := (estimate _ _ reach power width).trans (by exact_mod_cast Finset.card_le_card inc)
  apply le_trans ?_ prime
  have main : (H : ℝ) ≤ 2*(w : ℝ)*(H/w : ℕ) := by exact_mod_cast cover
  calc
    _ = (a * H / (2*w)) / log k := by ring
    _ ≤ (a * (H/w : ℕ)) / log k := by
      apply div_le_div_of_nonneg_right _ klog.le
      apply (div_le_iff₀ (by positivity : 0 < 2*(w : ℝ))).mpr
      calc
        _ ≤ a * (2 * (w : ℝ) * (H/w : ℕ)) := mul_le_mul_of_nonneg_left main ha.le
        _ = _ := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) xlog logs

theorem sum_prime_rows {k H W : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (big : 1 < k) (square : W*W ≤ k) (hwidth : H*W ≤ k) (small : H ≤ k)
    (mass : (1/320 : ℝ)*log k ≤ ∑ w ∈ Icc 2 W, 1/(w:ℝ))
    (rows : ∀ w ∈ Icc 2 W, (a*H/(2*log k))*(1/(w:ℝ)) ≤ ((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w).card) :
    (a/640)*(H:ℝ) ≤ ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k H W).card := by
  have lg : 0 < log (k : ℝ) := log_pos (by exact_mod_cast big)
  calc
    _ = (a*H/(2*log k)) * ((1/320 : ℝ) * log k) := by field_simp; ring
    _ ≤ (a*H/(2*log k)) * (∑ w ∈ Icc 2 W, 1/(w:ℝ)) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ = _ := Finset.mul_sum _ _ _
    _ ≤ ∑ w ∈ Icc 2 W, (((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H w).card : ℝ) := Finset.sum_le_sum rows
    _ ≤ _ := by exact_mod_cast primeRows_le_products square hwidth small

end RoughBinomial

namespace RoughBinomial
open Finset Filter Real

theorem many_products (h : OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1.H1) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop, 0 < (fun k : ℕ => k / ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)^10 : ℕ → ℕ) k ∧
      A * ((fun k : ℕ => k / ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)^10 : ℕ → ℕ) k : ℝ) ≤ ((fun (k H W : ℕ) => @Finset.filter ℕ
  (fun u => ∃ w ∈ Finset.Icc 2 W, ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ u = w*p ∧ u < k+p)
  (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))) k ((fun k : ℕ => k / ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)^10 : ℕ → ℕ) k) ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)).card := by
  obtain ⟨a,ha,X,estimate⟩ := h
  refine ⟨a/640, by positivity, ?_⟩
  have grows := tendsto_atTop.mp weight_tendsto (max X 2)
  filter_upwards [grows, eventually_ge_atTop (2^80 : ℕ)] with k bk big
  let b := (fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k
  let H := (fun k : ℕ => k / ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)^10 : ℕ → ℕ) k
  change max X 2 ≤ b at bk
  have kb : 1 < k := lt_of_lt_of_le (by decide : 1 < 2^80) big
  have hb : 2 ≤ b := (le_max_right _ _).trans bk
  have hk : b^80 ≤ k := weight_power_le (by omega)
  obtain ⟨_,_,_,_,square,width,small,pos⟩ := Erdos1095.short_scale hb hk (le_refl 2) hb
  refine ⟨pos, sum_prime_rows ha.le kb (by simpa [sq] using square) width small
    (dyadic_weights_lower big) ?_⟩
  intro w inside
  obtain ⟨hw,wb⟩ := mem_Icc.mp inside
  obtain ⟨pow,ratio,large,cover,_⟩ := Erdos1095.short_scale hb hk hw wb
  exact one_prime_row ha estimate hw (((le_max_left X 2).trans bk).trans large)
    (hb.trans large) pow ratio cover

end RoughBinomial

namespace RoughBinomial
open Filter Real

theorem log_nat_tendsto : Tendsto (fun k : ℕ => log (k:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The logarithm is at most eighty times the dyadic denominator bound. -/
theorem log_le_weight {k : ℕ} (kp : 0< k) :
    log (k:ℝ) ≤ 80*((2^(Nat.log 2 k/80) : ℕ) : ℝ) := by
  let d := Nat.log 2 k
  let e := d/80
  have power := Nat.lt_pow_succ_log_self (by decide : 1< 2) k
  have room : d+1 ≤ 80*(e+1) := by dsimp [e]; omega
  have size := Nat.lt_two_pow_self (n:=e)
  have upper : d+1 ≤ 80*(2^e) := room.trans (Nat.mul_le_mul_left 80 size)
  calc
    log (k:ℝ) ≤ log ((2:ℝ)^(d+1)) := Real.log_le_log (by exact_mod_cast kp) (by exact_mod_cast power.le)
    _ = ((d+1 : ℕ):ℝ)*log 2 := Real.log_pow _ _
    _ ≤ ((d+1 : ℕ):ℝ)*1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [Real.log_le_sub_one_of_pos (by norm_num : 0< (2:ℝ))]
    _ ≤ _ := by rw [mul_one]; exact_mod_cast upper

theorem dyadic_errors (ε : ℝ) (hε : 0< ε) : ∀ᶠ k : ℕ in atTop,
    let b : ℕ := 2^(Nat.log 2 k/80)
    let H := k/b^10
    log (k:ℝ)/(H:ℝ)≤ ε ∧ ((H:ℝ)/(k:ℝ))*log (k:ℝ)≤ ε := by
  have weight : Tendsto (fun k : ℕ => ((2^(Nat.log 2 k/80) : ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp weight_tendsto
  filter_upwards [eventually_ge_atTop 1,weight.eventually_ge_atTop (80/ε)] with k kp large
  let b : ℕ := 2^(Nat.log 2 k/80)
  let H := k/b^10
  have bp : 0< b := pow_pos (by decide) _
  have kp' : 0< k := kp
  have pow80 : b^80≤ k := weight_power_le kp'
  have above : b^2≤ H := by
    apply (Nat.le_div_iff_mul_le (pow_pos bp 10)).mpr
    rw [←pow_add]
    exact (Nat.pow_le_pow_right bp (by decide : 2+10≤ 80)).trans pow80
  have below : H*b^2≤ k :=
    (Nat.mul_le_mul_left H (Nat.pow_le_pow_right bp (by decide : 2≤ 10))).trans (Nat.div_mul_le_self k _)
  have hp : 0< (H:ℝ) := by exact_mod_cast ((pow_pos bp 2).trans_le above)
  have ker : 0< (k:ℝ) := by exact_mod_cast kp'
  change 80/ε≤ (b:ℝ) at large
  have rate : (80:ℝ) ≤ (b:ℝ)*ε := (div_le_iff₀ hε).mp large
  have bound : log (k:ℝ)≤ ε*(b:ℝ)^2 := calc
    _ ≤ 80*(b:ℝ) := log_le_weight kp'
    _ ≤ ((b:ℝ)*ε)*b := mul_le_mul_of_nonneg_right rate (by positivity)
    _ = _ := by ring
  change log (k:ℝ)/(H:ℝ)≤ ε ∧ ((H:ℝ)/(k:ℝ))*log (k:ℝ)≤ ε
  constructor
  · exact (div_le_iff₀ hp).mpr (bound.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast above) hε.le))
  · rw [div_mul_eq_mul_div,div_le_iff₀ ker]
    calc
      (H:ℝ)*log (k:ℝ) ≤ H*(ε*(b:ℝ)^2) := mul_le_mul_of_nonneg_left bound hp.le
      _ = ε*((H:ℝ)*(b:ℝ)^2) := by ring
      _ ≤ ε*(k:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast below) hε.le

/-- Uniform bound for every denominator above the log-squared threshold. -/
theorem above_log_square (ε : ℝ) (hε : 0< ε) : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
    (k:ℝ)*(log (k:ℝ))^2 ≤ n → ((k:ℝ)*log (k:ℝ))/(n:ℝ)≤ ε := by
  filter_upwards [eventually_ge_atTop 1,log_nat_tendsto.eventually_ge_atTop (1/ε)] with k kp grow
  intro n hn
  have kh : 0< (k:ℝ) := by exact_mod_cast (show 0< k from kp)
  have lh : 0< log (k:ℝ) := (one_div_pos.mpr hε).trans_le grow
  have nh : 0< (n:ℝ) := (mul_pos kh (sq_pos_of_pos lh)).trans_le hn
  have ready : 1 ≤ log (k:ℝ)*ε := (div_le_iff₀ hε).mp grow
  apply (div_le_iff₀ nh).mpr
  calc
    (k:ℝ)*log (k:ℝ) = ((k:ℝ)*log (k:ℝ))*1 := by ring
    _ ≤ ((k:ℝ)*log (k:ℝ))*(log (k:ℝ)*ε) := mul_le_mul_of_nonneg_left ready (mul_pos kh lh).le
    _ = ε*((k:ℝ)*(log (k:ℝ))^2) := by ring
    _ ≤ ε*(n:ℝ) := mul_le_mul_of_nonneg_left hn hε.le

end RoughBinomial

namespace RoughBinomial
open Finset Real

private theorem card_from_span (S : Finset ℕ) (D : ℝ) (nonneg : 0 ≤ D)
    (span : ∀ x ∈ S, ∀ y ∈ S, (x : ℝ) - y ≤ D) : (S.card : ℝ) ≤ 1 + D := by
  by_cases ne : S.Nonempty
  · let l := S.min' ne
    let u := S.max' ne
    have sub : S ⊆ Icc l u := fun z hz => mem_Icc.mpr ⟨S.min'_le z hz, S.le_max' z hz⟩
    have ord : l ≤ u := S.min'_le _ (S.max'_mem ne)
    have bound := Finset.card_le_card sub
    rw [Nat.card_Icc] at bound
    have exactWidth : u + 1 - l + l = u + 1 := Nat.sub_add_cancel (by omega)
    have it := span u (S.max'_mem ne) l (S.min'_mem ne)
    have size : (S.card : ℝ) + l ≤ (u:ℝ)+1 := by exact_mod_cast (show S.card+l ≤ u+1 by omega)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp ne]
    simp [nonneg.trans (by linarith : D ≤ 1+D)]

private theorem interval_for_quotient {k n H p : ℕ} (width : H*2 ≤ k)
    (rough : k < (n.choose k).minFac) (inside : p ∈ (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H 2) :
    let q := n/p+1
    k < 2*p ∧ 2*p ≤ k+H ∧ p ≤ k ∧ n < q*p ∧ q*p ≤ n+H := by
  obtain ⟨bounds,hp⟩ := mem_filter.mp inside
  obtain ⟨x,y⟩ := mem_Ioc.mp bounds
  have lo := (Nat.div_lt_iff_lt_mul (by decide : 0< 2)).mp x
  have hi := (Nat.le_div_iff_mul_le (by decide : 0< 2)).mp y
  have pk : p ≤ k := by omega
  have hlt : 2*p < k+p := by omega
  have ⟨pos,small⟩ := gap_to_next_multiple hp pk rough (by omega : k < 2*p) hlt
  dsimp
  rw [Nat.mul_comm p (n/p+1)] at pos small
  omega

/-- A concrete upper bound for the number of double primes in the interval
when the binomial coefficient has no prime factor at most k. -/
theorem double_prime_row_upper {k n H : ℕ} (kpos : 0 < k) (large : k < n)
    (width : H*2 ≤ k) (rough : k < (n.choose k).minFac) :
    (((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H 2).card : ℝ) ≤
      (1+2*H*(n+k : ℝ)/(k:ℝ)^2) * (1+(H:ℝ)*k/n) := by
  classical
  let S := (fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H 2
  let J := fun p : ℕ => n/p+1
  let Q := S.image J
  let D := 2*(H:ℝ)*(n+k)/(k:ℝ)^2
  let E := (H:ℝ)*k/n
  have kp : (0:ℝ) < k := by exact_mod_cast kpos
  have np : (0:ℝ) < n := by exact_mod_cast kpos.trans large
  have G {p : ℕ} (hp : p ∈ S) :
      (k:ℝ) < 2*p ∧ (2:ℝ)*p ≤ k+H ∧ (p:ℝ) ≤ k ∧ (n:ℝ) < (J p:ℝ)*p ∧
        (J p:ℝ)*p ≤ n+H := by
    obtain ⟨lo,hi,pk,a,b⟩ := interval_for_quotient width rough hp
    exact ⟨by exact_mod_cast lo,by exact_mod_cast hi,by exact_mod_cast pk,by exact_mod_cast a,by exact_mod_cast b⟩
  have qr : (Q.card : ℝ) ≤ 1 + D := by
    apply card_from_span Q D (by dsimp [D]; positivity)
    intro u hu v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hv
    obtain ⟨lp,_,_,_,up⟩ := G hp
    obtain ⟨_,us,_,ls,_⟩ := G hs
    have rku : (J p:ℝ)*k ≤ 2*(n+H) := calc
      _ ≤ (J p:ℝ)*(2*p) := mul_le_mul_of_nonneg_left lp.le (by positivity)
      _ ≤ _ := by linarith only [up]
    have rkl : 2*(n:ℝ) ≤ (J s:ℝ)*(k+H) := calc
      _ ≤ (J s:ℝ)*(2*s) := by linarith only [ls]
      _ ≤ _ := mul_le_mul_of_nonneg_left us (by positivity)
    apply (le_div_iff₀ (by positivity : 0 < (k:ℝ)^2)).mpr
    -- Use the exact rational bounds before dropping the denominator k+H.
    have pkHi : (J p:ℝ) ≤ 2*(n+H)/(k:ℝ) := (le_div_iff₀ kp).mpr rku
    have skLo : 2*(n:ℝ)/((k:ℝ)+H) ≤ J s := (div_le_iff₀ (by positivity)).mpr rkl
    have thin := sub_le_sub pkHi skLo
    have envelope : (2*((n:ℝ)+H)/k - 2*(n:ℝ)/(k+H)) * (k:ℝ)^2 ≤ 2*(H:ℝ)*(n+k) := by
      field_simp
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg (H:ℝ))]
    exact (mul_le_mul_of_nonneg_right thin (sq_nonneg (k:ℝ))).trans envelope
  have fiber (q : ℕ) : ((S.filter fun p => J p = q).card : ℝ) ≤ 1 + E := by
    apply card_from_span _ E (by dsimp [E]; positivity)
    intro p hp s hs
    obtain ⟨hp,eqp⟩ := mem_filter.mp hp
    obtain ⟨hs,eqs⟩ := mem_filter.mp hs
    obtain ⟨_,_,_,_,pu⟩ := G hp
    obtain ⟨_,_,sk,sl,_⟩ := G hs
    rw [eqp] at pu
    rw [eqs] at sl
    by_cases order : p ≤ s
    · exact (sub_nonpos.mpr (by exact_mod_cast order)).trans (by dsimp [E]; positivity)
    have pos : 0 ≤ (p:ℝ)-s := sub_nonneg.mpr (by exact_mod_cast (le_of_not_ge order))
    have a : (q:ℝ)*((p:ℝ)-s) ≤ H := by linarith only [pu,sl]
    have b : (n:ℝ) ≤ q*k := sl.le.trans (mul_le_mul_of_nonneg_left sk (by positivity))
    apply (le_div_iff₀ np).mpr
    calc
      _ ≤ ((p:ℝ)-s)*(q*k) := mul_le_mul_of_nonneg_left b pos
      _ = ((q:ℝ)*((p:ℝ)-s))*k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right a kp.le
  have cover : ∑ q ∈ Q, (S.filter fun p => J p=q).card = S.card := (Finset.card_eq_sum_card_image (s := S) (f := J)).symm
  calc
    _ = ∑ q ∈ Q, ((S.filter fun p => J p=q).card : ℝ) := by exact_mod_cast cover.symm
    _ ≤ ∑ _q ∈ Q, (1+E) := Finset.sum_le_sum (fun q _ => fiber q)
    _ = (Q.card : ℝ)*(1+E) := by simp [mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right qr (by dsimp [E]; positivity)

end RoughBinomial

namespace RoughBinomial
open Filter Finset Real

theorem row_quadratic_bound {k n H a : ℝ} (sqrtk : 1 < k) (kn : k ≤ n)
    (hp : 0 < H) (ap : 0 < a)
    (compare : a*H/(4*log k) ≤ (1+2*H*(n+k)/k^2)*(1+H*k/n))
    (e0 : log k/H ≤ a/64) (e1 : k*log k/n ≤ a/64) (e2 : H/k*log k ≤ a/64) :
    (a/64)*k^2/log k ≤ n := by
  have kp : 0 < k := by linarith
  have np := kp.trans_le kn
  have lg := log_pos sqrtk
  have d : 2*H*(n+k)/k^2 ≤ 4*H*n/k^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg k)
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr kn)]
  have major := compare.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) d) (by positivity))
  have expanded : a/4 ≤ log k/H + 4*(n*log k/k^2) + k*log k/n + 4*(H/k*log k) := calc
    _ = a*H/(4*log k) * (log k/H) := by field_simp
    _ ≤ (1+4*H*n/k^2)*(1+H*k/n)*(log k/H) :=
      mul_le_mul_of_nonneg_right major (by positivity)
    _ = _ := by field_simp; ring
  have middle : a/64 ≤ n*log k/k^2 := by linarith [expanded,e0,e1,e2]
  have bound := (le_div_iff₀ (sq_pos_of_pos kp)).mp middle
  exact (div_le_iff₀ lg).mpr bound

/-- The earlier quadratic/log estimate follows from the same short-interval
prime theorem, given just a logarithmic-square preliminary lower bound. -/
theorem lift_preliminary (g : ℕ → ℕ) (h : OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1.H1)
    (attains : ∀ᶠ k in atTop, k+1 < g k ∧ k < ((g k).choose k).minFac)
    (prelim : ∀ᶠ k : ℕ in atTop, (k:ℝ) * (log k)^2 ≤ g k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k : ℕ in atTop, δ*(k:ℝ)^2/log k ≤ g k := by
  obtain ⟨a,ha,X,estimate⟩ := h
  refine ⟨a/64, by positivity, ?_⟩
  have grows := tendsto_atTop.mp weight_tendsto (max X 2)
  have eps : 0 < a/64 := by positivity
  filter_upwards [grows, dyadic_errors (a/64) eps, above_log_square (a/64) eps,
    attains, prelim, eventually_ge_atTop (2^80 : ℕ)] with k bk errors smallG atG lower huge
  let b := (fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k
  let H := (fun k : ℕ => k / ((fun k : ℕ => 2^(Nat.log 2 k / 80) : ℕ → ℕ) k)^10 : ℕ → ℕ) k
  change max X 2 ≤ b at bk
  have hb : 2 ≤ b := (le_max_right _ _).trans bk
  have kb : 1 < k := lt_of_lt_of_le (by decide : 1 < 2^80) huge
  have hk : b^80 ≤ k := weight_power_le (by omega)
  obtain ⟨power, ratio, large, cover, _, width, _, pos⟩ :=
    Erdos1095.short_scale hb hk (le_refl 2) hb
  have one := one_prime_row ha estimate (le_refl 2) (((le_max_left X 2).trans bk).trans large)
    (hb.trans large) power ratio cover
  have wd : H*2 ≤ k := (Nat.mul_le_mul_left H hb).trans width
  have bound := double_prime_row_upper (by omega : 0 < k) (by omega : k < g k) wd atG.2
  have scaled : a*(H:ℝ)/(4*log k) ≤ (((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H 2).card : ℝ) := by
    change a*(H:ℝ)/(2*log k)*(1/(2:ℝ)) ≤ (((fun (k H w : ℕ) =>
  (Finset.Ioc (k/w) ((k+H)/w)).filter Nat.Prime) k H 2).card : ℝ) at one
    calc
      _ = a*(H:ℝ)/(2*log k)*(1/(2:ℝ)) := by ring
      _ ≤ _ := one
  exact row_quadratic_bound (by exact_mod_cast kb) (by exact_mod_cast (show k ≤ g k by omega))
    (by exact_mod_cast pos) ha (scaled.trans bound) errors.1 (smallG (g k) lower) errors.2

end RoughBinomial

namespace RoughBinomial

/-- A single prime power between both summands and their sum certifies a carry. -/
theorem prime_power_obstruction {n k p a : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (ha : 0 < a) (hk : k < p^a) (hd : n-k < p^a) (total : p^a ≤ n) :
    (n.choose k).minFac ≤ k := by
  have kn : k ≤ n := by omega
  apply le_trans (Nat.minFac_le_of_dvd hp.two_le _) hpk
  apply Nat.dvd_of_factorization_pos
  let b := Nat.log p n + a + 1
  rw [Nat.factorization_choose hp kn (show Nat.log p n < b by dsimp [b]; omega)]
  apply Finset.card_ne_zero.mpr
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha,by dsimp [b]; omega⟩, ?_⟩⟩
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hd]
  omega

end RoughBinomial

namespace RoughBinomial

/-- A short interval prime near the square root forces a divisor of the binomial.
The same argument handles either order of the lower index and its complement. -/
theorem square_band {k n X : ℕ} (short : ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x+y)
    (kn : k ≤ n) (reach : max ((max X 2)^2) 4 ≤ max k (n-k))
    (width : 8^8 * (max k (n-k))^7 ≤ (min k (n-k))^8) :
    (n.choose k).minFac ≤ k := by
  let m := max k (n-k)
  let d := min k (n-k)
  let x := Nat.sqrt m
  let y := d/(4*x)
  have msum : m+d=n := by dsimp [m,d]; omega
  have dm : d≤ m := by dsimp [m,d]; omega
  have xx : x^2 ≤ m := Nat.sqrt_le' _
  have xg : max X 2 ≤ x := Nat.le_sqrt'.mpr <| (le_max_left _ _).trans reach
  have xp : 0 < x := by omega
  have high : m ≤ x*x+2*x := by simpa [two_mul, Nat.add_assoc] using Nat.sqrt_le_add m
  have powering : ((8:ℕ)^4*x^7)^2 ≤ (d^4)^2 := calc
    _ = 8^8*(x^2)^7 := by ring
    _ ≤ 8^8*m^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left xx 7)
    _ ≤ _ := by simpa [←Nat.pow_mul] using width
  have step : 8^4*x^7 ≤ d^4 := (Nat.pow_le_pow_iff_left (by decide)).mp powering
  have linear : 8*x ≤ d := by
    apply (Nat.pow_le_pow_iff_left (by decide : 4≠ 0)).mp
    calc
      (8*x)^4 = 8^4*x^4 := by ring
      _ ≤ 8^4*x^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right xp (by decide))
      _ ≤ _ := step
  have divisorPos : 0 < 4*x := by omega
  have yn : 1 ≤ y := Nat.div_pos (by omega) divisorPos
  have yprod : 4*x*y ≤ d := Nat.mul_div_le d (4*x)
  have rem := Nat.mod_lt d divisorPos
  have dec := Nat.mod_add_div d (4*x)
  change d%(4*x) + 4*x*y = d at dec
  have ybig : d ≤ 8*x*y := by nlinarith [Nat.mul_le_mul_left (4*x) yn]
  have accurate : x^3 ≤ y^4 := by
    apply Nat.le_of_mul_le_mul_left (c := (8*x)^4) _ (pow_pos (by omega) _)
    calc
      (8*x)^4*x^3 = 8^4*x^7 := by ring
      _ ≤ d^4 := step
      _ ≤ (8*x*y)^4 := Nat.pow_le_pow_left ybig 4
      _ = _ := by ring
  have yx : y ≤ x := by
    by_contra! bad
    have := Nat.mul_le_mul_left (4*x) (show x+1≤ y by omega)
    nlinarith
  obtain ⟨p,hp,px,pe⟩ := short x y (by omega) accurate yx
  have low : m < p^2 := (Nat.lt_succ_sqrt' m).trans_le (Nat.pow_le_pow_left px 2)
  have up : p^2 ≤ n := calc
    _ ≤ (x+y)^2 := Nat.pow_le_pow_left pe 2
    _ ≤ m+d := by nlinarith [Nat.mul_le_mul_right y yx]
    _ = n := msum
  have pk : p ≤ k := by dsimp [d] at linear; omega
  exact prime_power_obstruction hp pk (by decide : 0< 2)
    ((le_max_left k (n-k)).trans_lt low) ((le_max_right k (n-k)).trans_lt low) up

end RoughBinomial

namespace RoughBinomial
open Filter Finset Real

/-- Positivity of the short-interval prime count gives a prime in every such interval. -/
theorem short_interval_prime (h : OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1.H1) :
    ∃ X : ℕ, ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x+y := by
  obtain ⟨a,ha,X,estimate⟩ := h
  refine ⟨max X 2, fun x y hx power width => ?_⟩
  have large : 2 ≤ x := (le_max_right _ _).trans hx
  have yp : 0 < y := by
    by_contra! z
    have yz : y=0 := Nat.eq_zero_of_le_zero z
    simp [yz] at power
    omega
  have logpos := Real.log_pos (show (1 : ℝ)< x by exact_mod_cast (show 1< x by omega))
  have pos : 0 < a*(y:ℝ)/log x := div_pos (mul_pos ha (by exact_mod_cast yp)) logpos
  have card : 0 < ((Ioc x (x+y)).filter Nat.Prime).card := by
    exact_mod_cast pos.trans_le (estimate x y ((le_max_left _ _).trans hx) power width)
  obtain ⟨p,hp⟩ := card_pos.mp card
  obtain ⟨inside,prime⟩ := mem_filter.mp hp
  exact ⟨p,prime,mem_Ioc.mp inside⟩

/-- The square-root interval has sufficient relative width throughout the
logarithmic-square range, including where n-k is the smaller summand. -/
theorem eventual_square_width : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 3*k≤ 2*n →
    (n:ℝ) ≤ (k:ℝ)*(log (k:ℝ))^2 →
    8^8*(max k (n-k))^7 ≤ (min k (n-k))^8 := by
  filter_upwards [weight_tendsto.eventually_ge_atTop (16^8*6400^7),
    eventually_ge_atTop 1] with k large positive
  intro n lower upper
  let b : ℕ := 2^(Nat.log 2 k/80)
  change 16^8*6400^7 ≤ b at large
  have bp : 0< b := pow_pos (by decide) _
  have kp : 0< k := positive
  have logs := log_le_weight kp
  change log (k:ℝ) ≤ 80*(b:ℝ) at logs
  have lg := log_nonneg (show (1:ℝ)≤ k by exact_mod_cast positive)
  have cap : n ≤ k*(6400*b^2) := by
    have : (n:ℝ) ≤ k*(6400*(b:ℝ)^2) := calc
      _ ≤ _ := upper
      _ ≤ k*(80*(b:ℝ))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lg logs _) (by positivity)
      _ = _ := by ring
    exact_mod_cast this
  have small : 16^8*(6400*b^2)^7 ≤ k := calc
    _ = (16^8*6400^7)*b^14 := by ring
    _ ≤ b*b^14 := Nat.mul_le_mul_right _ large
    _ = b^15 := by ring
    _ ≤ b^80 := Nat.pow_le_pow_right bp (by decide)
    _ ≤ k := weight_power_le kp
  have budget : 16^8*n^7 ≤ k^8 := calc
    _ ≤ 16^8*(k*(6400*b^2))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 7)
    _ = k^7*(16^8*(6400*b^2)^7) := by ring
    _ ≤ k^7*k := Nat.mul_le_mul_left _ small
    _ = k^8 := by ring
  have kn : k≤ n := by omega
  have mx : max k (n-k) ≤ n := max_le kn (Nat.sub_le _ _)
  have half : k≤ 2*min k (n-k) := by omega
  apply Nat.le_of_mul_le_mul_left (c:=2^8) _ (by decide)
  calc
    2^8*(8^8*(max k (n-k))^7) = 16^8*(max k (n-k))^7 := by ring
    _ ≤ 16^8*n^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left mx 7)
    _ ≤ k^8 := budget
    _ ≤ (2*min k (n-k))^8 := Nat.pow_le_pow_left half 8
    _ = _ := by ring

/-- Beyond a fixed k the entire range from 3k/2 to k(log k)^2
contains a prime-square carry, ruling out a k-rough binomial. -/
theorem eventual_square_range (h : OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1.H1) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 3*k ≤ 2*n →
      (n:ℝ) ≤ (k:ℝ)*(log (k:ℝ))^2 → (n.choose k).minFac ≤ k := by
  obtain ⟨X,short⟩ := short_interval_prime h
  filter_upwards [eventual_square_width,eventually_ge_atTop (max ((max X 2)^2) 4)] with k widths large
  intro n band upper
  exact square_band short (by omega) (large.trans (le_max_left _ _)) (widths n band upper)

end RoughBinomial

namespace RoughBinomial
open Finset

/-- In a rough binomial with n=k+d≤ 2k, all composite factors in the upper
interval must cancel into d!, as in Ecklund's proof (Pacific J. Math., 1969). -/
theorem composites_cancel {k d : ℕ} (dk : d ≤ k)
    (rough : k < ((k+d).choose k).minFac) :
    let S := (range d).filter (fun i => ¬(k+1+i).Prime)
    k ^ S.card ≤ d.factorial := by
  intro S
  classical
  have cop : (∏ i ∈ S, (k+1+i)).Coprime ((k+d).choose k) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    obtain ⟨idhi,comp⟩ := mem_filter.mp hi
    have il := mem_range.mp idhi
    apply Nat.coprime_of_dvd
    intro p pp pm pc
    have hi := Nat.minFac_le_of_dvd pp.two_le pc
    obtain ⟨a,ha⟩ := pm
    have pa : p ≤ k+1+i := Nat.le_of_dvd (by omega) ⟨a,ha⟩
    have age : 2 ≤ a := by
      rcases a with _|a
      · simp at ha
      rcases a with _|a
      · simp at ha
        exact False.elim (comp (ha ▸ pp))
      · omega
    have bound := Nat.mul_le_mul_left p age
    omega
  have total : ∏ i ∈ range d,(k+1+i) = d.factorial*((k+d).choose k) := by
    rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose]
    congr 1
    simpa using (Nat.choose_symm (show k≤ k+d by omega))
  have dv : (∏ i ∈ S,(k+1+i)) ∣ d.factorial := by
    apply cop.dvd_of_dvd_mul_right
    rw [←total]
    exact prod_dvd_prod_of_subset S (range d) (fun i => k+1+i) (filter_subset _ _)
  have floor : (∏ _i ∈ S, k) ≤ ∏ i ∈ S,(k+1+i) := by
    apply prod_le_prod' ; intro i hi; omega
  simpa using floor.trans (Nat.le_of_dvd d.factorial_pos dv)

set_option maxRecDepth 6000 in
/-- A fixed wheel of period 210 certifies at least 162 cancelled factors per
complete block of offsets inside (k,k+d]. -/
theorem cancelled_count {k d : ℕ} (hk : 210 ≤ k) :
    162*(d/210-1) ≤ ((range d).filter fun i => ¬(k+1+i).Prime).card := by
  classical
  let R := (range 210).filter (fun r => 2∣ r ∨ 3∣ r ∨ 5∣ r ∨ 7∣ r)
  have card : R.card = 162 := by decide
  let pairs := Finset.product (range (d/210-1)) R
  let f (v : ℕ × ℕ) := (k/210+1+v.1)*210 + v.2 -(k+1)
  have val (j r : ℕ) : k+1+f (j,r)=(k/210+1+j)*210+r := by
    dsimp [f]; omega
  have maps : Set.MapsTo f pairs
        ((range d).filter fun i => ¬(k+1+i).Prime) := by
    rintro ⟨j,r⟩ h
    obtain ⟨jl,hr⟩ := mem_product.mp h
    obtain ⟨rl,dr⟩ := mem_filter.mp hr
    rw [mem_range] at jl rl
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by dsimp [f]; omega), ?_⟩
    rw [val]
    intro prime
    have nonprime {q : ℕ} (small : 2 ≤ q) (sq : q ≤ 210) (step : q∣ 210) (qr : q∣ r) : False := by
      have dv := dvd_add (dvd_mul_of_dvd_right step (k/210+1+j)) qr
      have eq := (Nat.dvd_prime prime).mp dv
      omega
    rcases dr with h|h|h|h
    · exact nonprime (q:=2) (by decide) (by decide) (by decide) h
    · exact nonprime (q:=3) (by decide) (by decide) (by decide) h
    · exact nonprime (q:=5) (by decide) (by decide) (by decide) h
    · exact nonprime (q:=7) (by decide) (by decide) (by decide) h
  have inj : Set.InjOn f pairs := by
    rintro ⟨j,r⟩ h ⟨j',r'⟩ h' e
    have rb := mem_range.mp (mem_filter.mp (mem_product.mp h).2).1
    have rb' := mem_range.mp (mem_filter.mp (mem_product.mp h').2).1
    have e' := congrArg (fun x => k+1+x) e
    rw [val,val] at e'
    congr 1 <;> omega
  simpa [pairs, card, Nat.mul_comm] using card_le_card_of_injOn f maps inj
end RoughBinomial

namespace RoughBinomial
open Finset

theorem long_offset {k d : ℕ} (large : 20000 < k) (huge : Nat.factorial 20000 < k)
    (room : 81^50 ≤ k) (dd : 2 ≤ d) (dk : d ≤ k)
    (rough : k < ((k+d).choose k).minFac) : 81*k^3 ≤ d^4 := by
  classical
  let S := (range d).filter fun i => ¬(k+1+i).Prime
  have prod : k^S.card ≤ d.factorial := composites_cancel dk rough
  have count : 162*(d/210-1) ≤ S.card := cancelled_count (le_trans (by decide : 210 ≤ 20000) large.le)
  have even_index : ∃ i< d, 2∣ k+1+i := by
    by_cases h : 2∣ k+1
    · exact ⟨0,by omega,by simpa using h⟩
    · exact ⟨1,by omega,by omega⟩
  obtain ⟨i,hi,even⟩ := even_index
  have el : i ∈ S := by
    refine mem_filter.mpr ⟨mem_range.mpr hi,fun h => ?_⟩
    have := (Nat.dvd_prime h).mp even
    omega
  have pos := Finset.card_pos.mpr (show S.Nonempty from ⟨i,el⟩)
  have kd := (le_self_pow (by omega : 1 ≤ k) (by omega : S.card≠ 0)).trans prod
  have dlarge : 20000 ≤ d := by
    by_contra! small
    exact (not_le_of_gt huge) (kd.trans (Nat.factorial_le small.le))
  have squeeze : 151*d ≤ 200*S.card := by omega
  apply (Nat.pow_le_pow_iff_left (show 50*d≠ 0 by omega)).mp
  calc
    (81*k^3)^(50*d) = (81^50*k^150)^d := by rw [pow_mul,mul_pow,←pow_mul]
    _ ≤ (k*k^150)^d := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ room) _
    _ = k^(151*d) := by rw [pow_mul]; congr 1; ring
    _ ≤ k^(200*S.card) := Nat.pow_le_pow_right (by omega) squeeze
    _ = (k^S.card)^200 := by rw [←pow_mul, Nat.mul_comm 200]
    _ ≤ (d.factorial)^200 := Nat.pow_le_pow_left prod _
    _ ≤ (d^d)^200 := Nat.pow_le_pow_left d.factorial_le_pow _
    _ = (d^4)^(50*d) := by rw [←pow_mul,←pow_mul]; congr 1; ring

theorem no_small_rough {k d X : ℕ} (large : 20000 < k) (huge : Nat.factorial 20000 < k)
    (room : 81^50 ≤ k) (reach : X ≤ k/2) (dd : 2 ≤ d) (small : 2*d < k)
    (short : ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x → ∃ p, Nat.Prime p ∧ x < p ∧ p ≤ x+y) :
    ((k+d).choose k).minFac ≤ k := by
  by_contra! rough
  have wide := long_offset large huge room dd (by omega) rough
  have dY : d ≤ 3*(d/2) := by omega
  have fourth : (k/2)^3 ≤ (d/2)^4 := by
    apply Nat.le_of_mul_le_mul_left (c:=81) _ (by decide)
    calc
      81*(k/2)^3 ≤ 81*k^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.div_le_self ..) 3)
      _ ≤ d^4 := wide
      _ ≤ (3*(d/2))^4 := Nat.pow_le_pow_left dY 4
      _ = _ := by ring
  obtain ⟨p,pp,lo,hi⟩ := short _ _ reach fourth (by omega)
  have i : 2*p-(k+1) ∈ range d := mem_range.mpr (by omega)
  have fac : (k+1+(2*p-(k+1))) ∣ ∏ i ∈ range d,(k+1+i) :=
    Finset.dvd_prod_of_mem (fun i => k+1+i) i
  have eq : k+1+(2*p-(k+1)) = 2*p := by omega
  rw [eq, ← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose] at fac
  rcases pp.dvd_mul.mp ((dvd_mul_left p 2).trans fac) with h|h
  · have := pp.dvd_factorial.mp h; omega
  · have eqb : (k+d).choose d=(k+d).choose k := by simpa using Nat.choose_symm (show k ≤ k+d by omega)
    rw [eqb] at h
    have := Nat.minFac_le_of_dvd pp.two_le h
    omega

end RoughBinomial

namespace RoughBinomial
open Filter

/-- Every good binomial eventually lies beyond the initial half-width interval. -/
theorem eventual_low_band (supply : ∃ X : ℕ, ∀ x y : ℕ, X ≤ x → x^3 ≤ y^4 → y ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x+y) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, k+1 < n → k < (n.choose k).minFac → 3*k ≤ 2*n := by
  obtain ⟨X,short⟩ := supply
  filter_upwards [eventually_ge_atTop (20001 : ℕ),
    eventually_ge_atTop (Nat.factorial 20000 + 1),
    eventually_ge_atTop (81^50 : ℕ), eventually_ge_atTop (2*X)] with k size huge room reach
  intro n large rough
  let d := n-k
  have nform : k+d=n := by dsimp [d]; omega
  by_contra! fail
  have small : 2*d< k := by omega
  have bound := no_small_rough (X:=X) (by omega : 20000< k) (by omega) room
    (by omega) (show 2≤ d by omega) small short
  rw [nform] at bound
  omega

end RoughBinomial

namespace RoughBinomial

/-- An elementary form of Erdős, Lacampagne and Selfridge (1993), Theorem 2. -/
theorem composite_neighbours {k n p a : ℕ} (large : k+1 < n)
    (rough : k < (n.choose k).minFac) (comp : ¬(k+1).Prime)
    (prime : p.Prime) (pk : p ≤ k) (dp : p^a ∣ k+2) :
    (k+1)*p^a ≤ n+1 := by
  have cop : (k+1).Coprime (n.choose k) := by
    apply Nat.coprime_of_dvd
    intro q hq hd he
    have b := Nat.le_of_dvd (Nat.succ_pos k) hd
    have s := Nat.minFac_le_of_dvd hq.two_le he
    have e : q = k+1 := by omega
    exact comp (e ▸ hq)
  have one : k+1 ∣ n+1 := cop.dvd_of_dvd_mul_right <| by
    rw [Nat.add_one_mul_choose_eq]
    exact dvd_mul_left _ _
  have cp : (p^a).Coprime (n.choose k) := by
    apply Nat.Coprime.pow_left a
    apply prime.coprime_iff_not_dvd.mpr
    intro bad
    have := Nat.minFac_le_of_dvd prime.two_le bad
    omega
  have two : p^a ∣ (n+1)*(n+2) := by
    apply cp.dvd_of_dvd_mul_right
    have ctx : (n+1)*(n+2)*n.choose k =
        (n+2).choose (k+2)*(k+1)*(k+2) := by
      calc
        _ = (n+2)*((n+1)*n.choose k) := by ac_rfl
        _ = (n+2)*((n+1).choose (k+1)*(k+1)) := by rw [Nat.add_one_mul_choose_eq]
        _ = ((n+2)*(n+1).choose (k+1))*(k+1) := by ac_rfl
        _ = _ := by rw [Nat.add_one_mul_choose_eq (n+1) (k+1)]; ac_rfl
    rw [ctx]
    exact dp.trans (dvd_mul_left _ _)
  have col : (k+1).Coprime (p^a) :=
    Nat.Coprime.of_dvd_right dp (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _))
  by_cases f : p ∣ n+1
  · have other : ¬p ∣ n+2 := by
      intro h
      have e := Nat.dvd_sub h f
      have : p ∣ 1 := by simpa using e
      exact prime.not_dvd_one this
    have c : (p^a).Coprime (n+2) := (prime.coprime_iff_not_dvd.mpr other).pow_left a
    exact Nat.le_of_dvd (Nat.succ_pos n) (col.mul_dvd_of_dvd_of_dvd one (c.dvd_of_dvd_mul_right two))
  · have c : (p^a).Coprime (n+1) := (prime.coprime_iff_not_dvd.mpr f).pow_left a
    have l := Nat.dvd_sub one (dvd_refl (k+1))
    have r := Nat.dvd_sub (c.dvd_of_dvd_mul_left two) dp
    have dl : k+1 ∣ n-k := by simpa using l
    have dr : p^a ∣ n-k := by simpa using r
    have lo := Nat.le_of_dvd (by omega : 0 < n-k) (col.mul_dvd_of_dvd_of_dvd dl dr)
    omega

end RoughBinomial

namespace RoughBinomial

/-- The first corollary of Erdős–Lacampagne–Selfridge Theorem 2, specialized
to the infinite sequence k = 3^a - 2. -/
theorem quadratic_on_threes {n k a : ℕ} (ha : 2 ≤ a) (kp : k+2 = 3^a)
    (large : k+1 < n) (rough : k < (n.choose k).minFac) :
    k^2 + 3*k + 1 ≤ n := by
  have ge : 3^2 ≤ 3^a := Nat.pow_le_pow_right (by decide) ha
  have hk : 7 ≤ k := by omega
  have comp : ¬(k+1).Prime := by
    intro h
    have residue : 3^a%2=1 := by rw [Nat.pow_mod]; simp
    have even : 2 ∣ k+1 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h).mp even
    omega
  have bd := composite_neighbours (p:=3) (a:=a) large rough comp Nat.prime_three
    (by omega) (kp ▸ dvd_refl _)
  rw [←kp] at bd
  nlinarith

end RoughBinomial

namespace RoughBinomial

theorem reciprocal_derivative_abs (n : ℝ) (hn : 0 ≤ n) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    |iteratedDeriv r (fun x : ℝ => n / x) u| =
      n * r.factorial / u^(r+1) := by
  simp only [div_eq_mul_inv] at *
  change |iteratedDeriv r (fun x : ℝ => n * Inv.inv x) u| = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (r : ℤ)) = -((r+1:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  simp [abs_mul, abs_of_nonneg hn, abs_of_pos hu, mul_assoc]

/-- If the logarithmic length times the order is at most log 2, the r-th
derivative varies by a factor of at most two over the interval. -/
theorem reciprocal_curvature {n k H u : ℝ} {r : ℕ}
    (hn : 0 ≤ n) (hk : 0 < k) (hu : k ≤ u) (hi : u ≤ k + H)
    (short : (r+1 : ℕ) * (H/k) ≤ Real.log 2) :
    let scale := n * r.factorial / k^(r+1)
    scale / 2 ≤ |iteratedDeriv r (fun x : ℝ => n/x) u| ∧
    |iteratedDeriv r (fun x : ℝ => n/x) u| ≤ scale := by
  intro scale
  have upos := hk.trans_le hu
  have ratio : 0 < u / k := div_pos upos hk
  have logRel : Real.log (u / k) ≤ H/k := by
    apply (Real.log_le_sub_one_of_pos ratio).trans
    apply (le_div_iff₀ hk).mpr
    rw [sub_mul, div_mul_cancel₀ _ hk.ne', one_mul]
    linarith
  have cap : Real.log ((u/k)^(r+1)) ≤ Real.log 2 := by
    rw [Real.log_pow]
    exact (mul_le_mul_of_nonneg_left logRel (by positivity)).trans short
  have pbound : u^(r+1) ≤ 2*k^(r+1) := by
    have h := (Real.log_le_log_iff (pow_pos ratio _) (by norm_num : (0:ℝ)< 2)).mp cap
    rwa [div_pow, div_le_iff₀ (pow_pos hk _)] at h
  rw [reciprocal_derivative_abs n hn r upos]
  dsimp [scale]
  constructor
  · rw [div_div]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos upos _) (by simpa [mul_comm] using pbound)
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos hk _) (pow_le_pow_left₀ hk.le hu _)

end RoughBinomial

namespace RoughBinomial

theorem dyadic_curvature_window {k r : ℕ} (hk : 2^80 ≤ k)
    (hr : r ≤ Nat.log 2 k) :
    let b : ℕ := 2^(Nat.log 2 k / 80)
    let H := k / b^10
    (((r+1 : ℕ):ℝ) * ((H:ℝ) / (k:ℝ))) ≤ Real.log 2 := by
  intro b H
  let e := Nat.log 2 k / 80
  have dlarge := Nat.le_log_of_pow_le (by decide : 1< 2) hk
  have epos : 1 ≤ e := by dsimp [e]; omega
  have eb : e < b := Nat.lt_two_pow_self
  have hb : 2 ≤ b := by omega
  have cap : r+1 ≤ 160*e := by dsimp [e]; omega
  have high : 512*b ≤ b^10 := by
    have e9 := Nat.pow_le_pow_left hb 9
    simpa only [Nat.reducePow, ← pow_succ] using Nat.mul_le_mul_right b e9
  have bound : 2*(r+1) ≤ b^10 := by omega
  have totals : 2*(r+1)*H ≤ k := calc
    _ ≤ b^10*H := Nat.mul_le_mul_right H bound
    _ ≤ k := by simpa only [Nat.mul_comm (b^10)] using Nat.div_mul_le_self k (b^10)
  have kp : 0 < k := lt_of_lt_of_le (by positivity) hk
  have kpos : (0:ℝ) < k := by exact_mod_cast kp
  have comparison : 2*((r+1:ℕ):ℝ)*(H:ℝ) ≤ (k:ℝ) := by exact_mod_cast totals
  calc
    _ ≤ (1:ℝ)/2 := by
      rw [← mul_div_assoc, div_le_iff₀ kpos]
      linarith
    _ ≤ _ := by
      have l := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)< 2)
      norm_num at l ⊢
      exact l

end RoughBinomial

open Finset

namespace Erdos1095

/-- Kummer's carry test in the form used by the published short-period reduction
by @desenyon (PR #1901), `Erdos1095.erdos_1095.variants.log_equivalent.R1`, lemma `prime_avoids_iff`. -/
theorem rough_digit {n k p : ℕ} (prime : p.Prime) (small : p ≤ k)
    (fits : k ≤ n) (rough : k < (n.choose k).minFac) (i : ℕ) :
    k%(p^i) ≤ n%(p^i) := by
  by_contra! bad
  have ip : 0 < i := by by_contra! zero; simp [show i=0 by omega,Nat.mod_one] at bad
  let q := p^i
  have carry : q ≤ k%q+(n-k)%q := by
    by_contra! lt
    have eq : n%q = k%q + (n-k)%q := calc
      _ = (k+(n-k))%q := by rw [Nat.add_sub_of_le fits]
      _ = _ := (Nat.add_mod k (n-k) q).trans (Nat.mod_eq_of_lt lt)
    change n%q < k%q at bad
    omega
  let b := max (Nat.log p n) i + 1
  have member : i∈(Ico 1 b).filter fun j => p^j ≤ k%(p^j)+(n-k)%(p^j) := by
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨ip,(le_max_right _ _).trans_lt (Nat.lt_succ_self _)⟩,carry⟩
  have pos : 0 < (n.choose k).factorization p := by
    rw [Nat.factorization_choose prime fits ((le_max_left _ _).trans_lt (Nat.lt_succ_self _) : Nat.log p n < b)]
    exact card_pos.mpr ⟨i,member⟩
  have dv : p∣ n.choose k := by
    by_contra h
    exact pos.ne' (Nat.factorization_eq_zero_of_not_dvd h)
  exact (not_lt_of_ge ((Nat.minFac_le_of_dvd prime.two_le dv).trans small)) rough

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1600000 in
theorem twenty_minimal {m : ℕ} (large : 21 < m) (rough : 20 < (m.choose 20).minFac) : 43196 ≤ m := by
  let tests : List (ℕ×ℕ) := [(2,3),(2,5),(3,1),(3,3),(5,2),(7,1),(7,2),(11,1),(11,2),(13,1),(13,2)]
  let passes (u : ℕ) := tests.all fun pe => decide (20%(pe.1^pe.2) ≤ u%(pe.1^pe.2))
  have check : ∀ a : Fin 65, (List.range 32).all (fun j =>
      let u := 21*(32*a.val+j)+20
      decide (u ≤ 21) || decide (43196 ≤ u) || !passes u) = true := by
    dsimp only [passes,tests]
    decide +kernel
  have allowed (x : ℕ×ℕ) (hx : x∈tests) : x.1.Prime ∧ x.1 ≤ 20 := by
    exact (show ∀ x∈tests, x.1.Prime ∧ x.1 ≤ 20 by decide) x hx
  have pp : passes m=true := List.all_eq_true.mpr fun pe hp =>
    decide_eq_true (rough_digit (allowed pe hp).1 (allowed pe hp).2 (by omega) rough pe.2)
  have residue : m%21=20 := by
    have rows : ∀ i : Fin 21, 2 ≤ i.val%3 → 6 ≤ i.val%7 → i.val=20 := by decide
    apply rows ⟨m%21,Nat.mod_lt _ (by decide)⟩
    · rw [Nat.mod_mod_of_dvd m (by decide : 3∣ 21)]
      exact rough_digit (by decide : Nat.Prime 3) (by decide) (by omega) rough 1
    · rw [Nat.mod_mod_of_dvd m (by decide : 7∣ 21)]
      exact rough_digit (by decide : Nat.Prime 7) (by decide) (by omega) rough 1
  by_contra! below
  have h := List.all_eq_true.mp (check ⟨m/21/32,by omega⟩) (m/21%32)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  dsimp only at h
  rw [Nat.div_add_mod,←residue,Nat.div_add_mod] at h
  simp [not_le.mpr large, not_le.mpr below,pp] at h

theorem twenty_witness : 20 < ((43196:ℕ).choose 20).minFac := by
  let c : ℕ := 209331929857689170816679759057273715075985521200063244466786956418042736271
  have value : (43196:ℕ).choose 20=c := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 20)
    rw [←Nat.descFactorial_eq_factorial_mul_choose]
    decide +kernel
  rw [value]
  exact (Nat.coprime_factorial_iff (show c≠ 1 by decide)).mp (by decide +kernel)

end Erdos1095

namespace Erdos1095

theorem g_twenty : g 20 = 43196 := by
  let S := {m : ℕ | 20+1 < m ∧ 20 < (m.choose 20).minFac}
  change sInf S = 43196
  have w : 43196∈S := ⟨by decide,twenty_witness⟩
  have mem : sInf S ∈ S := Nat.sInf_mem ⟨43196,w⟩
  exact le_antisymm (Nat.sInf_le w) (twenty_minimal mem.1 mem.2)

end Erdos1095

namespace Erdos1095
open Finset

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1800000 in
theorem table_specs (i : Fin 18) :
    let values : List ℕ := [6,7,7,23,62,143,44,159,46,47,174,2239,239,719,241,5849,2098,2099]
    let k := i.val+2
    let v := values[i.val]!
    (k+1 < v ∧ k < (v.choose k).minFac) ∧
      ∀ m : ℕ, k+1 < m → k < (m.choose k).minFac → v ≤ m := by
  intro values k v
  let periods : List (ℕ×ℕ) := [(2,0),(2,2),(3,0),(3,1),(5,0),(2,3),(3,2),(5,1),(7,0),
    (2,2),(11,0),(7,1),(5,1),(2,4),(13,0),(3,2),(17,0),(5,1)]
  let e := periods[i.val]!
  let q := e.1^e.2
  let tests : List (ℕ×ℕ) := [(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),
    (5,1),(5,2),(7,1),(7,2),(11,1),(11,2),(13,1),(13,2),(17,1),(17,2),(19,1),(19,2)]
  let passes (k m : ℕ) := tests.all fun pe =>
    decide (k < pe.1) || decide (k%(pe.1^pe.2) ≤ m%(pe.1^pe.2))
  have row : ∀ j : Fin 18,
      let k := j.val+2
      let v := values[j.val]!
      let e := periods[j.val]!
      let q := e.1^e.2
      (k+1 < v ∧ (v.descFactorial k/k.factorial).Coprime k.factorial) ∧
      e.1.Prime ∧ e.1 ≤ k ∧ k%q=q-1 ∧
      (List.range (v/q+1)).all (fun t =>
        let m := q*t+(q-1)
        decide (m ≤ k+1) || decide (v ≤ m) || !passes k m) = true := by
    dsimp only [values,periods,tests,passes]
    decide +kernel
  obtain ⟨⟨fit,coeff⟩,prime,small,last,block⟩ := row i
  change k+1 < v at fit
  have good : k < (v.choose k).minFac := by
    apply (Nat.coprime_factorial_iff (show v.choose k≠ 1 by
      intro one
      have clash := Nat.choose_eq_one_iff.mp one
      dsimp only [k] at fit clash
      omega)).mp
    change (v.descFactorial k/k.factorial).Coprime k.factorial at coeff
    simpa only [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.mul_div_cancel_left _ (Nat.factorial_pos k)] using coeff
  refine ⟨⟨fit,good⟩,?_⟩
  intro m hm rough
  by_contra! below
  have ep : e.1.Prime := prime
  have qp : 0 < q := pow_pos ep.pos _
  have low := rough_digit ep small (by omega : k ≤ m) rough e.2
  change k%q ≤ m%q at low
  change k%q=q-1 at last
  have rem := Nat.mod_lt m qp
  have residue : m%q=q-1 := by omega
  have testgood (pe : ℕ×ℕ) (hp : pe∈tests) : pe.1.Prime := by
    exact (show ∀ pe∈tests, pe.1.Prime by decide) pe hp
  have pass : passes k m = true := by
    apply List.all_eq_true.mpr
    intro pe hp
    by_cases big : k < pe.1
    · simp [big]
    · simp [big,rough_digit (testgood pe hp) (by omega) (by omega : k ≤ m) rough pe.2]
  have idx : m/q < v/q+1 := Nat.lt_succ_of_le (Nat.div_le_div_right below.le)
  have no := List.all_eq_true.mp block (m/q) (List.mem_range.mpr idx)
  change (decide (q*(m/q)+(q-1) ≤ k+1) || decide (v ≤ q*(m/q)+(q-1)) ||
    !passes k (q*(m/q)+(q-1))) = true at no
  rw [←residue,Nat.div_add_mod] at no
  simp [not_le.mpr hm,not_le.mpr below,pass] at no

end Erdos1095

namespace Erdos1095

theorem g_two_through_twenty :
    let values : List ℕ := [6,7,7,23,62,143,44,159,46,47,174,2239,239,719,241,5849,2098,2099,43196]
    ∀ i : Fin 19, g (i.val+2) = values[i.val]! := by
  intro values i
  by_cases small : i.val < 18
  · let early : List ℕ := [6,7,7,23,62,143,44,159,46,47,174,2239,239,719,241,5849,2098,2099]
    have agree : ∀ j : Fin 18, early[j.val]! = values[j.val]! := by decide
    let S := {m : ℕ | i.val+2+1 < m ∧ i.val+2 < (m.choose (i.val+2)).minFac}
    obtain ⟨good,minimum⟩ := table_specs ⟨i.val,small⟩
    have witness : early[i.val]! ∈ S := good
    have first : sInf S ∈ S := Nat.sInf_mem ⟨_,witness⟩
    change sInf S = values[i.val]!
    rw [←agree ⟨i.val,small⟩]
    exact le_antisymm (Nat.sInf_le witness) (minimum _ first.1 first.2)
  · have key : i.val=18 := by have := i.isLt; omega
    rw [key]
    exact g_twenty

end Erdos1095

namespace RoughBinomial
open Filter Real

/-- The earlier quadratic-over-log lower bound needs only the prime-counting input. -/
theorem quadratic_from_primes (primes : OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1.H1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k : ℕ in atTop, δ*(k:ℝ)^2/log k ≤ Erdos1095.g k := by
  apply lift_preliminary _ primes eventually_g_attained
  filter_upwards [eventually_g_attained, eventual_low_band (short_interval_prime primes),
    eventual_square_range primes] with k atG lo hi
  by_contra! bad
  exact (Nat.not_le_of_lt atG.2) (hi _ (lo _ atG.1 atG.2) bad.le)

end RoughBinomial

namespace OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1
open Filter Finset Real RoughBinomial

/-- The rational-point density estimate for the reciprocal curve on integer
windows. The coefficient c in the upper range for n may depend on δ and ε. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, k+1 < n → δ*(k:ℝ)^2/log k ≤ n →
      (n:ℝ) < exp (c * log k ^ 2) →
      let W : ℕ := 2^(Nat.log 2 k / 80)
      let H : ℕ := k/W^10
      let nearby := fun u : ℕ => ∃ w ∈ Finset.Icc 2 W, ∃ v : ℕ,
        0 < (v:ℝ)/w-(n:ℝ)/u ∧ (v:ℝ)/w-(n:ℝ)/u ≤ (H:ℝ)/k
      ((@Finset.filter ℕ nearby (fun _ => Classical.propDecidable _) (Finset.Ioc k (k+H))).card : ℝ) ≤ ε*(H:ℝ)

theorem main : H1 → H2 → type_of% @Erdos1095.erdos_1095.variants.lower_solved := by
  intro primes curves
  obtain ⟨A, ap, many⟩ := many_products primes
  obtain ⟨δ, dp, floor⟩ := quadratic_from_primes primes
  obtain ⟨c, cp, few⟩ := curves δ dp (A/2) (by positivity)
  refine ⟨c,cp,lower_of_density_bounds _ _ A (A/2) (by linarith) _ _
    (fun k => ⌈δ*(k:ℝ)^2/log k⌉₊) eventually_g_attained ?_ many ?_⟩
  · filter_upwards [floor] with k fk
    exact Nat.ceil_le.mpr fk
  · filter_upwards [few] with k fk n hn above top
    exact fk n hn (Nat.ceil_le.mp above) top

end OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1
