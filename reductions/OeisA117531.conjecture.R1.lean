import FormalConjectures.OEIS.«117531»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Reduction to Rabinowitsch's criterion and the Stark-Heegner discriminant
bound. The descent shortens the polynomial test from p-1 values to the
length of the OEIS row, using Chebyshev's prime-counting estimate.
See P. Ribenboim, Euler's famous prime generating polynomial and the class
number of imaginary quadratic fields (1988), section G. -/

namespace OMA.R_OeisA117531_conjecture_R1

open Polynomial

-- Rabinowitsch's criterion: a full prime row has fundamental discriminant
-- and its imaginary quadratic field has class number one.
def H1 : Prop := ∀ p : ℕ, p.Prime → 41 < p →
  (∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime) →
    let d : ℤ := 1 - 4 * p
    Squarefree d ∧ ∃ h : Irreducible (X ^ 2 - C (d : ℚ)),
      letI : Fact (Irreducible (X ^ 2 - C (d : ℚ))) := ⟨h⟩
      NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ))) = 1

-- The lower discriminant bound in the Stark-Heegner classification.
def H2 : Prop := ∀ d : ℤ, Squarefree d → d < 0 →
  ∀ h : Irreducible (X ^ 2 - C (d : ℚ)),
    letI : Fact (Irreducible (X ^ 2 - C (d : ℚ))) := ⟨h⟩
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ))) = 1 → -163 ≤ d

lemma prime_size (n : ℕ) (hn : 13 < n) : Nat.nth Nat.Prime (n - 1) ≤ 3 * n ^ 2 := by
  let m := 3 * n ^ 2
  have hn' : (14 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 1 < m := by dsimp [m]; nlinarith
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ((m : ℝ) + 1) ≤ n + 2 := by
    have harg : (m : ℝ) + 1 ≤ (2 * (n : ℝ)) ^ 2 := by
      dsimp [m]; push_cast; nlinarith
    have h := Real.log_le_log (by positivity) harg
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h
    have h₂ := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / 2 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h₂
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hlogm : Real.log m ≤ n + 2 := (Real.log_le_log (by positivity) (by linarith : (m : ℝ) ≤ m + 1)).trans hlog
  have hπ := (div_le_iff₀ (Real.log_pos hm')).mp (Chebyshev.pi_ge m)
  have hc : n ≤ Nat.primeCounting m := by
    by_contra! h
    have hh : (Nat.primeCounting m : ℝ) ≤ n := by exact_mod_cast h.le
    have hz := mul_le_mul hh hlogm (Real.log_pos hm').le (by positivity)
    have hl : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hw := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    dsimp only [m] at hw hπ hlog hz
    push_cast at hw hπ hlog hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg n)]
  have hlt : n - 1 < Nat.count Nat.Prime (m + 1) := by
    change n - 1 < Nat.primeCounting m
    omega
  exact Nat.le_of_lt_succ ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp hlt)

lemma shorten {p n : ℕ} (hp : 41 < p) (hpn : p ≤ 3 * n ^ 2)
    (hw : ∃ x : ℕ, x + 1 < p ∧ ¬ (x * (x + 1) + p).Prime) :
    ∃ t < n, ¬ (t * (t + 1) + p).Prime := by
  let t := Nat.find hw
  obtain ⟨htp, hbad⟩ := Nat.find_spec hw
  change t + 1 < p at htp
  change ¬ (t * (t + 1) + p).Prime at hbad
  let v := t * (t + 1) + p
  let q := v.minFac
  have hq2 : 2 ≤ q := (Nat.minFac_prime (show v ≠ 1 by dsimp [v]; omega)).two_le
  have hs : q ^ 2 ≤ v := Nat.minFac_sq_le_self (by dsimp [v]; omega) hbad
  have hqp : q < p := by
    dsimp only [v] at hs
    by_contra! hh
    nlinarith [Nat.mul_self_le_mul_self hh,
      Nat.mul_le_mul (show t ≤ p - 2 by omega) (show t + 1 ≤ p - 1 by omega),
      show p - 2 + 2 = p by omega, show p - 1 + 1 = p by omega]
  let r := t % q
  let s := q - 1 - r
  have hr : r < q := Nat.mod_lt _ (by omega)
  have hsum : s + 1 + r = q := by dsimp [s]; omega
  have hz : (t : ZMod q) * (t + 1) + p = 0 := by
    have hv := (ZMod.natCast_eq_zero_iff v q).mpr (Nat.minFac_dvd v)
    simpa [v] using hv
  have hrz : (r : ZMod q) = t := ZMod.natCast_mod t q
  have hsz : (s : ZMod q) + 1 + r = 0 := by
    exact_mod_cast (show ((s + 1 + r : ℕ) : ZMod q) = 0 by rw [hsum]; simp)
  have hsmall (b : ℕ) (hb : b < q) (hbz : (b : ZMod q) * (b + 1) + p = 0) : t ≤ b := by
    have hd : q ∣ b * (b + 1) + p := (ZMod.natCast_eq_zero_iff _ q).mp (by simpa using hbz)
    have hnp := Nat.not_prime_of_dvd_of_lt hd hq2 (show q < b * (b + 1) + p by omega)
    by_contra! h
    exact Nat.find_min hw h ⟨by omega, hnp⟩
  have htr := hsmall r hr (by rwa [hrz])
  have hts := hsmall s (by omega) (by
    rw [← hrz] at hz
    linear_combination hz + (s - (r : ZMod q)) * hsz)
  have hq : 2*t+1 ≤ q := by omega
  have hh := Nat.mul_self_le_mul_self hq
  refine ⟨t, ?_, hbad⟩
  by_contra! hn
  dsimp [v] at hs
  nlinarith [Nat.mul_self_le_mul_self hn]

theorem main : H1 → H2 → type_of% @OeisA117531.conjecture := by
  intro criterion classify n hn
  let p := Nat.nth Nat.Prime (n - 1)
  have h41 : Nat.nth Nat.Prime 12 = 41 := by
    have hc : Nat.count Nat.Prime 41 = 12 := by decide
    rw [← hc]
    exact Nat.nth_count (by decide)
  have hlarge : 41 < p := h41 ▸ Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 12 < n - 1 by omega)
  have hw : ∃ x : ℕ, x + 1 < p ∧ ¬ (x * (x + 1) + p).Prime := by
    by_contra! hall
    obtain ⟨hs, hi, hc⟩ := criterion p (Nat.prime_nth_prime _) hlarge hall
    have hh := classify (1 - 4 * (p : ℤ)) hs (by omega) hi hc
    omega
  obtain ⟨t, ht, hbad⟩ := shorten hlarge (prime_size n hn) hw
  have ht' : (t + 1)^2 - (t+1) = t*(t+1) := by
    rw [pow_two, Nat.add_mul, one_mul, Nat.add_sub_cancel]
  unfold OeisA117531.a
  change ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + p).Prime).card < n
  have hsub : ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + p).Prime) ⊂ Finset.Icc 1 n := by
    apply Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
    exact ⟨t+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp [ht', hbad]⟩
  simpa using Finset.card_lt_card hsub

end OMA.R_OeisA117531_conjecture_R1
