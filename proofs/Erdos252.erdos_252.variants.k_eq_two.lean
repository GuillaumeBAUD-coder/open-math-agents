import FormalConjectures.ErdosProblems.«252»
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Irrationality of the squared-divisor factorial series

Dirichlet's theorem gives large primes p for which the odd half-successor
has no small divisor. After scaling by (p-1)!, the finite prefix is integral
and the two leading terms put the remainder strictly between integers.

The proof follows the k = 2 argument of Friedlander, Luca and Stoiciu,
*On the irrationality of a divisor function series* (2007), Section 1.
-/

-- Credit: @ysanatomic

open ArithmeticFunction
open scoped Nat ArithmeticFunction.sigma BigOperators

private theorem factorial_at {p : ℕ} (hp : 0 < p) :
    p.factorial = p * (p-1).factorial := by
  have h : p-1+1 = p := by omega
  calc
    p.factorial = (p-1+1).factorial := congrArg Nat.factorial h.symm
    _ = p * (p-1).factorial := by rw [Nat.factorial_succ, h]

private theorem factorial_series_not_rational
    (hpick : ∀ B : ℕ, ∃ p : ℕ, p.Prime ∧ B ≤ p ∧
      5/4 ≤ (σ 2 (p+1):ℝ)/((p:ℝ)*(p+1)) ∧
      (σ 2 (p+1):ℝ)/((p:ℝ)*(p+1)) ≤ 3/2)
    (hs : Summable (fun n : ℕ ↦ (σ 2 n:ℝ)/(n.factorial:ℝ)))
    (ht : ∀ p ≥ 2,
      (∑' j : ℕ, ((p-1).factorial:ℝ) * (σ 2 (p+j+2):ℝ)/((p+j+2).factorial:ℝ)) ≤ 8/(p:ℝ)) :
    Irrational (Erdos252.erdos_252_sum 2) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp, hB, hlow, hhigh⟩ := hpick (max (q.den+1) 100)
  have hp100 : 100 ≤ p := (le_max_right _ _).trans hB
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hp100R : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp100
  let F := (p-1).factorial
  let f (n : ℕ) : ℝ := (σ 2 n:ℝ)/(n.factorial:ℝ)
  have hF : 0 < (F:ℝ) := by exact_mod_cast Nat.factorial_pos (p-1)
  have hqP : q.den + 1 ≤ p := (le_max_left _ _).trans hB
  have hqD : q.den ∣ F := Nat.dvd_factorial q.pos (by omega)
  let z : ℤ := q.num * (((F / q.den : ℕ) : ℤ))
  have hz : (z:ℝ) = (F:ℝ) * ∑' n : ℕ, f n := by
    have hq' : (q:ℝ) = ∑' n : ℕ, f n := hq
    rw [← hq', Rat.cast_def]
    dsimp only [z]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hqD (Nat.cast_ne_zero.mpr q.den_nz)]
    ring
  let A : ℕ := ∑ j ∈ Finset.range p, σ 2 j * (F / j.factorial)
  have hA : (F:ℝ) * (∑ j ∈ Finset.range p, f j) = (A:ℝ) := by
    dsimp only [A]
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjF : j.factorial ∣ F := Nat.factorial_dvd_factorial (by
      have hj' := Finset.mem_range.mp hj
      omega)
    rw [Nat.cast_mul, Nat.cast_div hjF (by positivity)]
    dsimp only [f]
    ring
  have hpFact : p.factorial = p * F := factorial_at hp.pos
  have hp1Fact : (p+1).factorial = (p+1)*p*F := by
    rw [Nat.factorial_succ, hpFact, mul_assoc]
  have hsig : σ 2 p = 1 + p^2 := by
    simpa [Finset.sum_range_succ] using
      (ArithmeticFunction.sigma_apply_prime_pow (k := 2) (i := 1) hp)
  have hpTerm : (F:ℝ)*f p = (p:ℝ) + 1/(p:ℝ) := by
    unfold f
    rw [hsig, hpFact]
    push_cast
    field_simp
    ring
  have hp1Term : (F:ℝ)*f (p+1) = (σ 2 (p+1):ℝ)/((p:ℝ)*(p+1)) := by
    unfold f
    rw [hp1Fact]
    push_cast
    field_simp
  let tail : ℝ := ∑' j : ℕ, (F:ℝ) * (σ 2 (p+j+2):ℝ)/((p+j+2).factorial:ℝ)
  have hscale : (F:ℝ) * (∑' j : ℕ, f (j + (p+2))) = tail := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [show j+(p+2) = p+j+2 by omega]
    simp only [f, mul_div_assoc]
  have hs' : Summable f := hs
  have hsplit : (z:ℝ) = (A:ℝ) + (p:ℝ) + (1/(p:ℝ)) +
      (σ 2 (p+1):ℝ)/((p:ℝ)*(p+1)) + tail := by
    rw [hz, ← hs'.sum_add_tsum_nat_add (p+2),
      Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, mul_add,
      hA, hpTerm, hp1Term, hscale]
    ring
  have htail : 0 ≤ tail := tsum_nonneg (fun _ ↦ by positivity)
  have htail' : tail ≤ 8/(p:ℝ) := ht p (by omega)
  have hfrac : 0 < 1/(p:ℝ) := by positivity
  have hsum : 1/(p:ℝ) + 8/(p:ℝ) ≤ 9/100 := by
    rw [← add_div]
    exact (div_le_div_iff₀ hpR (by norm_num)).2 (by linarith)
  let b : ℤ := (A:ℤ) + (p:ℤ)
  have hb₁ : (b:ℝ) + 1 < (z:ℝ) := by
    dsimp only [b]
    push_cast
    linarith
  have hb₂ : (z:ℝ) < (b:ℝ) + 2 := by
    dsimp only [b]
    push_cast
    linarith
  have hb₁' : b + 1 < z := by exact_mod_cast hb₁
  have hb₂' : z < b + 2 := by exact_mod_cast hb₂
  omega

namespace OMA.Erdos252

/-- Dirichlet's theorem supplies primes with no small prime divisor of their half-successor. -/
lemma exists_large_prime (N : ℕ) :
    ∃ p > N, p.Prime ∧ p ≡ 1 [MOD 4] ∧ ∀ d : ℕ, 2 ≤ d → d ≤ 10 → ¬ d ∣ (p + 1) / 2 := by
  obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 420) (a := 1) (by decide) (by simp)
  refine ⟨p, hpN, hp, hmod.of_dvd (by decide), ?_⟩
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' (show 1 ≤ p from hp.one_lt.le)).mp hmod.symm
  have hhalf : (p + 1) / 2 = 210 * t + 1 := by omega
  intro d hd₂ hd₁₀ hdiv
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hq₂ := hq.two_le
  have hq₁₀ := (Nat.le_of_dvd (show 0 < d by omega) hqd).trans hd₁₀
  have hq210 : q ∣ 210 := by
    interval_cases q <;> first | decide | (exfalso; exact (by decide : ¬ Nat.Prime _) hq)
  have hq_half := hqd.trans hdiv
  rw [hhalf] at hq_half
  exact hq.not_dvd_one ((Nat.dvd_add_iff_right (hq210.trans (dvd_mul_right 210 t))).mpr hq_half)

end OMA.Erdos252

namespace OMA

open Finset
open scoped ArithmeticFunction.sigma

private lemma erdos252_sigma_two_ratio_apply (x : ℕ) :
    (σ 2 x : ℝ) / (x : ℝ)^2 = ∑ d ∈ x.divisors, (1 : ℝ) / (d : ℝ)^2 := by
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro d hd
  have hpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hD : d ∣ x := Nat.dvd_of_mem_divisors hd
  have hx : 0 < x := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
  have hdq : 0 < x / d := Nat.div_pos (Nat.le_of_dvd hx hD) hpos
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hqne : ((x / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdq.ne'
  have hmul : ((x / d : ℕ) : ℝ) * (d : ℝ) = (x : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hD
  rw [Nat.cast_pow, ← hmul, mul_pow]
  field_simp

private lemma erdos252_inv_square_le_telescoping (i : ℕ) (hi : 0 < i) :
    (1 : ℝ) / ((i : ℝ) + 1)^2 ≤ 1 / (i : ℝ) - 1 / ((i : ℝ) + 1) := by
  have hiR : 0 < (i : ℝ) := by exact_mod_cast hi
  calc
    (1 : ℝ) / ((i : ℝ) + 1)^2 ≤ 1 / ((i : ℝ) * ((i : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = 1 / (i : ℝ) - 1 / ((i : ℝ) + 1) := by
      field_simp
      ring

private lemma erdos252_sum_inv_square_le (L x : ℕ) (hL : 0 < L) (hLx : L ≤ x) :
    ∑ d ∈ Ico (L + 1) (x + 1), (1 : ℝ) / (d : ℝ)^2 ≤ 1 / (L : ℝ) - 1 / (x : ℝ) := by
  induction x, hLx using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    rw [show i + 1 + 1 = (i + 1).succ from rfl,
      Finset.sum_Ico_succ_top (show L + 1 ≤ i + 1 by omega)]
    push_cast
    have hstep := erdos252_inv_square_le_telescoping i (hL.trans_le hi)
    linarith

private lemma erdos252_sigma_two_ratio_le (x L : ℕ) (hx : 0 < x) (hL : 0 < L)
    (hdiv : ∀ d : ℕ, 2 ≤ d → d ≤ L → ¬ d ∣ x) :
    1 ≤ (σ 2 x : ℝ) / (x : ℝ)^2 ∧
      (σ 2 x : ℝ) / (x : ℝ)^2 ≤ 1 + 1 / (L : ℝ) := by
  rw [erdos252_sigma_two_ratio_apply]
  have h1 : 1 ∈ x.divisors := Nat.one_mem_divisors.mpr hx.ne'
  rw [← Finset.sum_erase_add _ _ h1]
  norm_num only [Nat.cast_one, one_pow, div_one]
  have hnonneg : 0 ≤ ∑ d ∈ x.divisors.erase 1, (1 : ℝ) / (d : ℝ)^2 :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hsub : x.divisors.erase 1 ⊆ Ico (L + 1) (max L x + 1) := by
    intro d hd
    obtain ⟨hdne, hd⟩ := Finset.mem_erase.mp hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdx := Nat.divisor_le hd
    have hdL : L < d := by
      by_contra! hle
      exact hdiv d (by omega) hle (Nat.dvd_of_mem_divisors hd)
    exact Finset.mem_Ico.mpr ⟨by omega, by have := le_max_right L x; omega⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun d : ℕ ↦ (1 : ℝ) / (d : ℝ)^2) (fun _ _ _ ↦ by positivity)
  have htel := erdos252_sum_inv_square_le L (max L x) hL (le_max_left _ _)
  have htail : 0 ≤ (1 : ℝ) / ((max L x : ℕ) : ℝ) := by positivity
  exact ⟨by linarith, by linarith⟩

/-- An elementary uniform bound on the sum of the squares of the divisors. -/
lemma erdos252_sigma_two_le (x : ℕ) (hx : 0 < x) :
    (σ 2 x : ℝ) ≤ 2 * (x : ℝ)^2 := by
  have h := (erdos252_sigma_two_ratio_le x 1 hx (by decide) (by omega)).2
  norm_num at h
  exact (div_le_iff₀ (by positivity)).mp h

/-- If all nontrivial divisors exceed ten, the normalized sum is close to one. -/
lemma erdos252_sigma_two_rough (x : ℕ) (hx : 0 < x)
    (hdiv : ∀ d : ℕ, 2 ≤ d → d ≤ 10 → ¬ d ∣ x) :
    1 ≤ (σ 2 x : ℝ) / (x : ℝ)^2 ∧
      (σ 2 x : ℝ) / (x : ℝ)^2 ≤ 1 + 1 / 10 := by
  exact erdos252_sigma_two_ratio_le x 10 hx (by decide) hdiv

/-- For the chosen progression, normalize the contribution of the index just after the cut. -/
lemma erdos252_sigma_two_at_succ (p : ℕ) (hp : 11 ≤ p) (hpmod : p % 4 = 1)
    (hdiv : ∀ d : ℕ, 2 ≤ d → d ≤ 10 → ¬ d ∣ (p + 1) / 2) :
    (5 : ℝ) / 4 ≤ (σ 2 (p + 1) : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) ∧
      (σ 2 (p + 1) : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) ≤ 3 / 2 := by
  let x := (p + 1) / 2
  have hpx : p + 1 = 2 * x := by dsimp [x]; omega
  have hxodd : Odd x := by rw [Nat.odd_iff]; dsimp [x]; omega
  have hx : 0 < x := by omega
  have hS : σ 2 2 = 5 := by
    rw [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
    norm_num
  have hSmul : σ 2 (p + 1) = 5 * σ 2 x := by
    rw [hpx, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hxodd.coprime_two_left,
      hS]
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : 0 < (p : ℝ) := by linarith
  have hpxR : (p : ℝ) + 1 = 2 * (x : ℝ) := by exact_mod_cast hpx
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have h := erdos252_sigma_two_rough x hx hdiv
  have heq : (σ 2 (p + 1) : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) =
      (5 / 4 : ℝ) * (((p : ℝ) + 1) / (p : ℝ)) * ((σ 2 x : ℝ) / (x : ℝ)^2) := by
    rw [hSmul]
    push_cast
    rw [hpxR]
    field_simp
    ring
  have hpLo : (1 : ℝ) ≤ ((p : ℝ) + 1) / (p : ℝ) := (le_div_iff₀ hpp).mpr (by linarith)
  have hpHi : ((p : ℝ) + 1) / (p : ℝ) ≤ 12 / 11 := (div_le_iff₀ hpp).mpr (by linarith)
  rw [heq]
  constructor
  · calc
      (5 / 4 : ℝ) = (5 / 4 : ℝ) * 1 * 1 := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpLo (by norm_num)) h.1 (by norm_num)
        (by positivity)
  · calc
      _ ≤ (5 / 4 : ℝ) * (12 / 11) * (1 + 1 / 10) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpHi (by norm_num)) h.2
          (by positivity) (by norm_num)
      _ = 3 / 2 := by norm_num

end OMA

namespace OMA.ER252

private theorem geometric_term_bound (f : ℕ → ℕ)
    (hf : ∀ x > 0, (f x : ℝ) ≤ 2 * (x : ℝ) ^ 2)
    (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    ((n - 1).factorial : ℝ) * (f (n + j + 2) : ℝ) /
        ((n + j + 2).factorial : ℝ) ≤ (4 / (n : ℝ)) * (1 / 2 : ℝ) ^ j := by
  have hfactorial : (n : ℝ) * (2 : ℝ) ^ j * ((n - 1).factorial : ℝ) ≤
      ((n + j).factorial : ℝ) := by
    have hgrow : n.factorial * 2 ^ j ≤ (n + j).factorial :=
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2 ≤ n + 1) j)).trans
        Nat.factorial_mul_pow_le_factorial
    have hnfac : n.factorial = n * (n - 1).factorial := by
      have h : n = (n - 1) + 1 := by omega
      conv_lhs => rw [h, Nat.factorial_succ, ← h]
    rw [hnfac, mul_right_comm] at hgrow
    exact_mod_cast hgrow
  have hr : ((n - 1).factorial : ℝ) / ((n + j).factorial : ℝ) ≤
      1 / ((n : ℝ) * (2 : ℝ) ^ j) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm]
    exact hfactorial
  have hnum : (f (n + j + 2) : ℝ) ≤ 2 * ((n : ℝ) + j + 2) ^ 2 := by
    exact_mod_cast hf (n + j + 2) (by omega)
  have hratio : ((n : ℝ) + j + 2) / ((n : ℝ) + j + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j]
  calc
    _ ≤ ((n - 1).factorial : ℝ) * (2 * ((n : ℝ) + j + 2) ^ 2) /
        ((n + j + 2).factorial : ℝ) := by gcongr
    _ = 2 * (((n : ℝ) + j + 2) / ((n : ℝ) + j + 1)) *
        (((n - 1).factorial : ℝ) / ((n + j).factorial : ℝ)) := by
      rw [show (n + j + 2) = (n + j + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ (n + j)]
      push_cast
      field_simp
      ring
    _ ≤ 2 * 2 * (1 / ((n : ℝ) * (2 : ℝ) ^ j)) := by gcongr
    _ = _ := by rw [div_pow]; ring

private theorem summable_half_powers :
    Summable (fun j : ℕ ↦ (1 / 2 : ℝ) ^ j) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem summable_factorial_series (f : ℕ → ℕ)
    (hf : ∀ x > 0, (f x : ℝ) ≤ 2 * (x : ℝ) ^ 2) :
    Summable (fun x ↦ (f x : ℝ) / (x.factorial : ℝ)) := by
  apply (summable_nat_add_iff (k := 4)).mp
  refine Summable.of_nonneg_of_le (fun j ↦ by positivity) ?_
    (summable_half_powers.mul_left (4 / (2 : ℝ)))
  intro j
  have h := geometric_term_bound f hf 2 (by decide) j
  rw [show 2 + j + 2 = j + 4 by omega] at h
  simpa using h

theorem factorial_tail_le (f : ℕ → ℕ)
    (hf : ∀ x > 0, (f x : ℝ) ≤ 2 * (x : ℝ) ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑' j : ℕ, ((n - 1).factorial : ℝ) * (f (n + j + 2) : ℝ) /
      ((n + j + 2).factorial : ℝ)) ≤ 8 / (n : ℝ) := by
  have hgeom := summable_half_powers.mul_left (4 / (n : ℝ))
  have hterm := geometric_term_bound f hf n hn
  have htail := Summable.of_nonneg_of_le (fun j ↦ by positivity : ∀ j : ℕ,
    0 ≤ ((n - 1).factorial : ℝ) * (f (n + j + 2) : ℝ) /
      ((n + j + 2).factorial : ℝ)) hterm hgeom
  refine (htail.tsum_le_tsum hterm hgeom).trans_eq ?_
  rw [summable_half_powers.tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

end OMA.ER252

theorem OMA.solution : type_of% @Erdos252.erdos_252.variants.k_eq_two := by
  apply factorial_series_not_rational
  · intro B
    obtain ⟨p, hpB, hp, hpmod, hdiv⟩ := OMA.Erdos252.exists_large_prime (max B 11)
    have hpB' : B ≤ p := (le_max_left _ _).trans hpB.le
    have hp11 : 11 ≤ p := (le_max_right _ _).trans hpB.le
    have hpmod' : p % 4 = 1 := by simpa [Nat.ModEq] using hpmod
    exact ⟨p, hp, hpB', OMA.erdos252_sigma_two_at_succ p hp11 hpmod' hdiv⟩
  · exact OMA.ER252.summable_factorial_series (σ 2) OMA.erdos252_sigma_two_le
  · exact OMA.ER252.factorial_tail_le (σ 2) OMA.erdos252_sigma_two_le
