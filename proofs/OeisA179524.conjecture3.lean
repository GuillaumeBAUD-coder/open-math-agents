import FormalConjectures.OEIS.«179524»
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.FinCases
/-!
# The vanishing supercongruence for A179524

Reflection of the binomial factors reduces the double sum modulo $p^2$ to one sum.
The reversed summands satisfy a third-order recurrence. A quadratic change of
variable identifies their polynomial with a scalar multiple of a square.
The root reduces modulo $p$ to a coefficient of the power of a cubic, which
vanishes by a polynomial isogeny certificate and quadratic reciprocity.

The local selection notes supplied the square strategy and rational isogeny
certificate. The factorial cancellation uses the same Mathlib facts as the
merged A357513 supercongruence proof submitted by @rleshner.
-/

namespace OMA
open Finset Nat

private lemma convolution (m k N : ℕ) :
    ∑ i ∈ range (N + 1), (i + m).choose m * (N - i + k).choose k =
      (N + m + k + 1).choose (m + k + 1) := by
  induction k generalizing N with
  | zero => simpa using Nat.sum_range_add_choose N m
  | succ k ih =>
    induction N with
    | zero => simp [Nat.add_assoc]
    | succ N jh =>
      rw [sum_range_succ]
      have eq (i : ℕ) (hi : i ∈ range (N + 1)) :
          (N + 1 - i + (k + 1)).choose (k + 1) =
            (N - i + (k + 1)).choose (k + 1) + (N + 1 - i + k).choose k := by
        rw [show N + 1 - i + (k + 1) = (N + 1 - i + k) + 1 by omega,
          Nat.choose_succ_succ', add_comm]
        congr 2
        simp only [mem_range] at hi
        omega
      rw [sum_congr rfl (show ∀ i ∈ range (N + 1),
          (i + m).choose m * (N + 1 - i + (k + 1)).choose (k + 1) =
           (i + m).choose m * (N - i + (k + 1)).choose (k + 1) +
           (i + m).choose m * (N + 1 - i + k).choose k from fun i hi => by rw [eq i hi, mul_add])]
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one]
      rw [sum_add_distrib, jh, add_assoc]
      have hh := ih (N + 1)
      rw [sum_range_succ] at hh
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one] at hh
      -- The final index in the second convolution contributes its own boundary term.
      rw [hh]
      rw [show N + 1 + m + (k + 1) + 1 = (N + m + (k + 1) + 1) + 1 by omega,
        show m + (k + 1) + 1 = (m + k + 1) + 1 by omega, Nat.choose_succ_succ', add_comm]
      congr 1 <;> congr 1 <;> omega


private lemma choose_mul_factorial_prod {R : Type*} [CommRing R] {n m : ℕ} (hm : m ≤ n) :
    (m.factorial : R) * (n.choose m : R) = ∏ i ∈ range m, ((n : R) - (i : R)) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod]
  exact prod_congr rfl fun i hi => Nat.cast_sub (by have := mem_range.mp hi; omega)

private lemma choose_reflect (p m n : ℕ) (hp : p.Prime) (hm : m < p)
    (hn : n ∈ Ico m p) (he : Even m) :
    (n.choose m : ZMod p) = ((p + m - 1 - n).choose m : ZMod p) := by
  have hn' := mem_Ico.mp hn
  have hunit : IsUnit (m.factorial : ZMod p) := by
    have h := ZMod.coe_mul_inv_eq_one m.factorial (hp.coprime_factorial_of_lt hm).symm
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  apply hunit.mul_left_cancel
  rw [choose_mul_factorial_prod hn'.1, choose_mul_factorial_prod (by omega)]
  rw [← prod_range_reflect (fun i => ((n : ZMod p) - (i : ZMod p))) m]
  have hsign : (∏ i ∈ range m, -((n : ZMod p) - (↑(m - 1 - i) : ZMod p))) =
      ∏ i ∈ range m, ((n : ZMod p) - (↑(m - 1 - i) : ZMod p)) := by
    rw [prod_neg, card_range, he.neg_one_pow, one_mul]
  rw [← hsign]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  push_cast [show i ≤ m - 1 by omega, show 1 ≤ m by omega,
    show n ≤ p + m - 1 by omega, show 1 ≤ p + m by omega]
  rw [ZMod.natCast_self]
  ring

/-- Reflect the index over the interval on which both binomials are supported.
The difference between the square sum and the reflected convolution is half
the sum of squared differences. -/
private lemma choose_square_sum (p m : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hm : m < p)
    (he : Even m) :
    (∑ n ∈ range p, (n.choose m : ZMod (p ^ 2)) ^ 2) = ((p + m).choose (2 * m + 1) : ℕ) := by
  let R := ZMod (p ^ 2)
  let b (n : ℕ) : R := n.choose m
  let r (n : ℕ) := p + m - 1 - n
  have hr : ∀ n ∈ Ico m p, r n ∈ Ico m p := by
    intro n hn
    simp only [mem_Ico, r] at *
    omega
  have hr2 : ∀ n ∈ Ico m p, r (r n) = n := by
    intro n hn
    simp only [mem_Ico, r] at *
    omega
  have hsq (n : ℕ) (hn : n ∈ Ico m p) : (b n - b (r n)) ^ 2 = 0 := by
    have h := choose_reflect p m n hp hm hn he
    have hdvd : (p : ℤ) ∣ (n.choose m : ℤ) - ((r n).choose m : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr h
    obtain ⟨d, hd⟩ := hdvd
    have hx : (b n - b (r n)) = (p : R) * (d : R) := by
      dsimp [R, b]
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using
        congrArg (fun x : ℤ => (x : ZMod (p ^ 2))) hd
    rw [hx, mul_pow]
    rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hsum : (∑ n ∈ Ico m p, b (r n) ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 :=
    sum_nbij' r r hr hr hr2 hr2 (fun _ _ => rfl)
  have hb : (∑ n ∈ range p, b n ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 := by
    symm
    apply sum_subset
    · intro n hn
      exact mem_range.mpr (mem_Ico.mp hn).2
    · intro n hn hnm
      have h : n < m := by simpa [mem_Ico, mem_range.mp hn] using hnm
      simp [b, Nat.choose_eq_zero_of_lt h]
  have hc : (∑ n ∈ Ico m p, b n * b (r n)) = ((p + m).choose (2 * m + 1) : R) := by
    rw [sum_Ico_eq_sum_range]
    have hlen : p - m = (p - m - 1) + 1 := by omega
    rw [hlen]
    have eq (i : ℕ) (hi : i ∈ range (p - m - 1 + 1)) : r (m + i) = (p - m - 1) - i + m := by
      simp only [r, mem_range] at *
      omega
    rw [sum_congr rfl (fun i hi => show b (m+i) * b (r (m+i)) =
      ((m+i).choose m * (p-m-1-i+m).choose m : ℕ) by simp [R, b, eq i hi]), ← Nat.cast_sum]
    rw [show (∑ x ∈ range (p - m - 1 + 1), (m + x).choose m *
          (p - m - 1 - x + m).choose m) =
          ((p - m - 1) + m + m + 1).choose (m + m + 1) from by
      simpa only [add_comm m] using convolution m m (p - m - 1)]
    congr 2 <;> omega
  change (∑ n ∈ range p, b n ^ 2) = _
  rw [hb, ← hc]
  have ht := sum_congr rfl hsq
  simp only [sum_const_zero] at ht
  have exp (n : ℕ) : (b n - b (r n)) ^ 2 = b n ^ 2 + b (r n) ^ 2 - 2 * (b n * b (r n)) := by ring
  simp_rw [exp, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum, ← two_mul] at ht
  have hc2 : (2 : ℕ).Coprime (p ^ 2) := (Nat.coprime_of_lt_prime (by decide) hp2 hp).symm.pow_right 2
  have hu2 : IsUnit (2 : R) := by
    obtain h := ZMod.coe_mul_inv_eq_one 2 hc2
    exact ⟨⟨2, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  apply hu2.mul_left_cancel
  exact sub_eq_zero.mp ht

private lemma collapse (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (∑ n ∈ range p, (OeisA179524.a n : ZMod (p ^ 2))) =
      ∑ k ∈ range ((p - 1) / 2 + 1), (-4 : ZMod (p ^ 2)) ^ k *
        ((2 * k).choose k : ZMod (p ^ 2)) ^ 2 * ((p + 2 * k).choose (4 * k + 1) : ℕ) := by
  let R := ZMod (p ^ 2)
  let h := (p - 1) / 2 + 1
  have ha (n : ℕ) (hn : n < p) :
      (OeisA179524.a n : R) =
        ∑ k ∈ range h, (-4 : R) ^ k * ((2 * k).choose k : R) ^ 2 * (n.choose (2 * k) : R) ^ 2 := by
    dsimp [R]
    simp only [OeisA179524.a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, Int.cast_natCast]
    have he (k : ℕ) :
        (-4 : R) ^ k * (n.choose k : R) ^ 2 * ((n - k).choose k : R) ^ 2 =
          (-4 : R) ^ k * ((2 * k).choose k : R) ^ 2 * (n.choose (2 * k) : R) ^ 2 := by
      have hx := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      rw [show 2 * k - k = k by omega] at hx
      dsimp [R]
      have hx' := congrArg (fun x : ℕ => (x : ZMod (p ^ 2))) hx
      simp only [Nat.cast_mul] at hx'
      linear_combination ((-4 : R) ^ k * ((n.choose (2 * k) : R) * ((2 * k).choose k : R) +
        (n.choose k : R) * ((n-k).choose k : R))) * (-hx')
    simp_rw [he]
    rcases le_total (n + 1) h with hh | hh
    · apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
    · symm
      apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by dsimp [h] at hk'; simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
  rw [sum_congr rfl (fun n hn => ha n (mem_range.mp hn)), sum_comm]
  apply sum_congr rfl
  intro k hk
  change k ∈ range h at hk
  rw [← mul_sum, choose_square_sum p (2 * k) hp hp2 (by
    dsimp [h] at hk; simp only [mem_range] at hk; omega) ⟨k, by omega⟩]
  congr 3
  omega

end OMA

namespace OMA
open Nat Finset

private abbrev R2 (p : ℕ) := ZMod (p^2)

private def red (p : ℕ) : R2 p →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) _

private lemma p_sq_zero (p : ℕ) : (p : R2 p) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma unit_red {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x ≠ 0) : IsUnit x := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)]
  intro hd
  apply hx
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

private lemma red_kern {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x = 0) :
    ∃ d : R2 p, x = (p : R2 p) * d := by
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨d, hd⟩ := hx
  refine ⟨d, ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hd, Nat.cast_mul]

private lemma unit_small {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : R2 p) := by
  apply unit_red hp
  rw [map_natCast]
  intro hz
  exact Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)

private def half (p : ℕ) : R2 p := (2 : R2 p)⁻¹
private def pa (p : ℕ) : R2 p := (1-2*(p : R2 p)) * half p ^ 2
private def pb (p : ℕ) : R2 p := (3-2*(p : R2 p)) * half p ^ 2
private def pc (p : ℕ) : R2 p := 1-(p : R2 p) * half p

private lemma two_half {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : 2 * half p = 1 :=
  ZMod.mul_inv_of_unit _ (unit_small hp (by decide : 0 < 2) hp2)

private lemma param_sums {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    pa p + pb p = 2 * pc p - 1 ∧ 2 * (-(h : R2 p)) = 2 * pc p - 1 := by
  have hi := two_half hp hp2
  have hP : (p : R2 p) = 2 * (h : R2 p) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : R2 p)) hh
  constructor
  · unfold pa pb pc
    linear_combination ((1 - (p : R2 p)) * (2 * half p + 1) + (p : R2 p)) * hi
  · unfold pc
    linear_combination (p : R2 p) * hi + hP

private lemma choose_move (u w : ℕ) :
    (u+w+2).choose (u+2) * ((u+1)*(u+2)*(u+w+4)*(u+w+3)) =
      (u+w+4).choose u * ((w+4)*(w+3)*(w+2)*(w+1)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show u+2 ≤ u+w+2 by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show u ≤ u+w+4 by omega)
  rw [show u+w+2-(u+2)=w by omega, Nat.factorial_succ, Nat.factorial_succ u] at h1
  rw [show u+w+4-u=w+4 by omega, Nat.factorial_succ (w+3), Nat.factorial_succ (w+2),
    Nat.factorial_succ (w+1), Nat.factorial_succ w,
    Nat.factorial_succ (u+w+3), Nat.factorial_succ (u+w+2), ← h1] at h2
  have he : (u+w+2).choose (u+2) * ((u+1)*(u+2)*(u+w+4)*(u+w+3)) *
      (u.factorial*w.factorial) =
      (u+w+4).choose u * ((w+4)*(w+3)*(w+2)*(w+1)) * (u.factorial*w.factorial) := by
    push_cast at h2
    convert h2.symm using 1 <;> ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) he

private def weight (p h j : ℕ) : R2 p :=
  (-4)^(h-j) * ((2*(h-j)).choose (h-j) : ℕ)^2 * ((p+2*(h-j)).choose (2*j) : ℕ) * (-16)^j

/-- The reversed summand, multiplied by $(-16)^j$, satisfies the recurrence
at the polynomial argument $X(1-X)$. The cancellation uses
$(p-v)^2 = -v(2p-v)$ in the ring modulo $p^2$. -/
private lemma weight_recurrence {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1)
    (j : ℕ) (hj : j < h) :
    ((j : R2 p)+1)*((j : R2 p)+pc p)*((j : R2 p)+2*pc p-1)*weight p h (j+1) =
      4*((j : R2 p)+pa p)*((j : R2 p)+pb p)*((j : R2 p)-(h : R2 p))*weight p h j := by
  let J : R2 p := j
  let P : R2 p := p
  let v : R2 p := 2*J+1
  let w : R2 p := v+1
  let A : R2 p := (2*(h-j-1)).choose (h-j-1)
  let B : R2 p := (2*(h-j)).choose (h-j)
  let D : R2 p := (p+2*(h-j-1)).choose (2*(j+1))
  let E : R2 p := (p+2*(h-j)).choose (2*j)
  have hP : P = 2*(h : R2 p)+1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : R2 p)) hh
  have hC : 4*(P-w)*A = (P-v)*B := by
    have he := Nat.succ_mul_centralBinom_succ (h-j-1)
    rw [show h-j-1+1 = h-j by omega] at he
    have he' := congrArg (fun n : ℕ => (n : R2 p)) he
    simp only [Nat.centralBinom, Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : j ≤ h),
      Nat.cast_sub (by omega : 1 ≤ h-j), Nat.cast_one, Nat.cast_ofNat] at he'
    change ((h : R2 p) - J) * B = 2 * (2*((h : R2 p)-J-1)+1)*A at he'
    dsimp [w, v]
    linear_combination -2*he' + ((4*A)-B) * hP
  let z := p+2*(h-j)-2*j-4
  have hD : D * (v*w*(2*P-v)*(2*P-w)) =
      E * ((2*P-4*J-1)*(2*P-4*J-3)*4*(P-v)*(P-w)) := by
    have he := choose_move (2*j) z
    have hz : 2*j+z+2 = p+2*(h-j-1) := by dsimp [z]; omega
    have hz' : 2*j+z+4 = p+2*(h-j) := by dsimp [z]; omega
    have hz'' : 2*j+z+3 = p+2*(h-j)-1 := by dsimp [z]; omega
    rw [hz, hz', hz''] at he
    have he' := congrArg (fun n : ℕ => (n : R2 p)) he
    have hzcast : (z : R2 p) = P+2*((h : R2 p)-J)-2*J-4 := by
      dsimp [z, P, J]
      push_cast [show 2*j ≤ p+2*(h-j) by omega, show 4 ≤ p+2*(h-j)-2*j by omega,
        show j ≤ h by omega]
      ring
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show 2*j+2=2*(j+1) by omega, Nat.cast_sub (by omega : 1 ≤ p+2*(h-j)),
      Nat.cast_sub (by omega : j ≤ h), hzcast] at he'
    change D*( (2*J+1)*(2*(J+1))*(P+2*((h : R2 p)-J))*(P+2*((h : R2 p)-J)-1)) =
      E*((P+2*((h : R2 p)-J)-2*J-4+4)*(P+2*((h : R2 p)-J)-2*J-4+3)*
        (P+2*((h : R2 p)-J)-2*J-4+2)*(P+2*((h : R2 p)-J)-2*J-4+1)) at he'
    dsimp [w, v]
    have hr (X : R2 p) : 2*((h : R2 p)-X) = P-1-2*X := by linear_combination -hP
    rw [hr J] at he'
    linear_combination he'
  have hhj : h-j = h-j-1+1 := by omega
  let L : R2 p := (-4)^(h-j-1) * (-16)^j
  have hW1 : weight p h (j+1) = -16*L*A^2*D := by
    unfold weight
    simp only [show h-(j+1)=h-j-1 by omega, pow_succ (-16 : R2 p) j]
    dsimp [L, A, D]
    ring
  have hW0 : weight p h j = -4*L*B^2*E := by
    change (-4 : R2 p)^(h-j)*B^2*E*(-16)^j = _
    rw [show (-4 : R2 p)^(h-j) = (-4)^(h-j-1)*(-4) by rw [← pow_succ, ← hhj]]
    dsimp [L]
    ring
  letI : Fact p.Prime := ⟨hp⟩
  have hv : IsUnit v := by
    dsimp [v, J]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      unit_small hp (by omega : 0 < 2*j+1) (by omega : 2*j+1 < p)
  have hredP : red p P = 0 := (map_natCast (red p) p).trans (ZMod.natCast_self p)
  have hu : IsUnit (2*P-v) := by
    apply unit_red hp
    rw [map_sub, map_mul, hredP, mul_zero, zero_sub, neg_ne_zero]
    exact (hv.map (red p)).ne_zero
  have hw : IsUnit (P-w) := by
    apply unit_red hp
    have hww : IsUnit w := by
      dsimp [w,v,J]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        unit_small hp (by omega : 0 < 2*j+1+1) (by omega : 2*j+1+1 < p)
    rw [map_sub, hredP, zero_sub, neg_ne_zero]
    exact (hww.map (red p)).ne_zero
  have hpv : (P-v)^2 = -(v*(2*P-v)) := by
    have hz : P^2 = 0 := p_sq_zero p
    linear_combination hz
  have hrec : (P-w)*w*(2*P-w)*weight p h (j+1) =
      (v-P)*(2*P-4*J-1)*(2*P-4*J-3)*weight p h j := by
    rw [hW1, hW0]
    apply (hv.mul hu).mul_left_cancel
    apply hw.mul_left_cancel
    have hC2 : (4*(P-w)*A)^2 = ((P-v)*B)^2 := congrArg (fun x : R2 p => x^2) hC
    linear_combination (-16*L*A^2*(P-w)^2)*hD -
      (4*L*E*(2*P-4*J-1)*(2*P-4*J-3)*(P-v)*(P-w)) * (hC2+B^2*hpv)
  have hi := two_half hp hp2
  have k1 : 2*(J+1)=w := by dsimp [w,v]; ring
  have k2 : 2*(J+pc p)=w-P := by
    unfold pc
    linear_combination k1 - P*hi
  have k3 : 2*(J+2*pc p-1)=w-2*P := by
    unfold pc
    linear_combination k1 - 2*P*hi
  have k4 : 4*(J+pa p)=4*J+1-2*P := by
    unfold pa
    linear_combination (1-2*P)*(2*half p+1)*hi
  have k5 : 4*(J+pb p)=4*J+3-2*P := by
    unfold pb
    linear_combination (3-2*P)*(2*half p+1)*hi
  have k6 : 2*(J-(h : R2 p))=v-P := by
    dsimp [v]
    linear_combination hP
  apply ((unit_small hp (by decide : 0 < 2) hp2).pow 3).mul_left_cancel
  calc
    _ = (2*(J+1))*(2*(J+pc p))*(2*(J+2*pc p-1))*weight p h (j+1) := by ring
    _ = (4*(J+pa p))*(4*(J+pb p))*(2*(J-(h : R2 p)))*weight p h j := by
      rw [k1,k2,k3,k4,k5,k6]
      linear_combination hrec
    _ = _ := by ring

end OMA

namespace OMA
open Polynomial Finset

section Operators
variable {R : Type*} [CommRing R]

private noncomputable def theta (P : R[X]) : R[X] := X * derivative P
private noncomputable def step (a : R) (P : R[X]) : R[X] := theta P + C a * P
private noncomputable def delta : R[X] := X * (1 - X)
private noncomputable def ell : R[X] := 1 - 2 * X

private lemma theta_coeff (P : R[X]) (n : ℕ) :
    (theta P).coeff n = (n : R) * P.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n => rw [theta, coeff_X_mul, coeff_derivative, mul_comm, Nat.cast_add, Nat.cast_one]

private lemma step_coeff (a : R) (P : R[X]) (n : ℕ) :
    (step a P).coeff n = ((n : R) + a) * P.coeff n := by
  rw [step, coeff_add, theta_coeff, coeff_C_mul, add_mul]

private noncomputable def odeT (a b c : R) (T : R[X]) : R[X] :=
  theta (step (c - 1) T) - X * step a (step b T)

private noncomputable def odeY (a b c d : R) (Y : R[X]) : R[X] :=
  theta (step (c - 1) (step (2*c - 2) Y)) - C 4 * X * step a (step b (step d Y))

private noncomputable def odeS (q c : R) (S : R[X]) : R[X] :=
  (1-X)^2 * theta (step (-1) (step (-2) S)) +
    C (3*c) * (1-X) * ell * theta (step (-1) S) +
    (C (2*c^2-c) * ell^2 + C (-2*c-4*q) * delta) * theta S +
    C ((2-4*c)*q) * X * ell * S

private lemma odeT_deriv (a b c : R) (hab : a+b = 2*c-1) (T : R[X]) :
    odeT a b c T = X * (delta * derivative (derivative T) +
      C c * ell * derivative T - C (a*b) * T) := by
  simp [odeT, step, theta, delta, ell, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_ofNat, C_eq_natCast]
  have h := congrArg (C : R → R[X]) hab
  simp [map_add, map_sub, map_mul, map_ofNat] at h
  linear_combination -(X^2 * derivative T) * h

private lemma odeS_deriv (q c : R) (S : R[X]) :
    odeS q c S = X * (delta^2 * derivative (derivative (derivative S)) +
      C (3*c) * delta * ell * derivative (derivative S) +
      (C (2*c^2-c) * ell^2 + C (-2*c-4*q) * delta) * derivative S +
      C ((2-4*c)*q) * ell * S) := by
  simp [odeS, step, theta, delta, ell, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg, map_pow, map_ofNat, C_eq_natCast]
  ring

private lemma odeS_square (a b c : R) (hab : a+b = 2*c-1) (T : R[X]) :
    odeS (a*b) c (T^2) = 2*(1-X)*T*theta (odeT a b c T) +
      (6*(1-X)*theta T + 2*C (2*c-1)*ell*T - 2*(1-X)*T) * odeT a b c T := by
  rw [odeS_deriv, odeT_deriv a b c hab]
  simp only [pow_two T]
  simp [theta, delta, ell, derivative_add, derivative_sub, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg,
    map_pow, map_ofNat, C_eq_natCast]
  ring

private lemma odeY_deriv (a b c d : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1) (Y : R[X]) :
    odeY a b c d Y = X * (
      X^2*(1-4*X)*derivative (derivative (derivative Y)) +
      (C (3*c)*X*(1-4*X)-6*X^2)*derivative (derivative Y) +
      (C (2*c^2-c)*(1-4*X)-C (8*c+4*a*b)*X)*derivative Y +
      C ((2-4*c)*(a*b))*Y) := by
  simp [odeY, step, theta, derivative_add, derivative_mul,
    derivative_C, derivative_X, map_sub, map_add, map_one, map_neg, map_pow,
    map_ofNat, C_eq_natCast]
  have h1 := congrArg (C : R → R[X]) hab
  have h2 := congrArg (C : R → R[X]) hd
  simp [map_add, map_sub, map_one, map_mul, map_ofNat, C_eq_natCast] at h1 h2
  linear_combination
    (-4*X^3*derivative (derivative Y) - 4*C d*X^2*derivative Y - 4*X^2*derivative Y) * h1 +
    (-2*X^3*derivative (derivative Y) - 4*C c*X^2*derivative Y -
      2*C a*C b*X*Y) * h2

private lemma odeS_comp (a b c d : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1) (Y : R[X]) :
    (1-X)*odeS (a*b) c (Y.comp delta) = ell * (odeY a b c d Y).comp delta := by
  rw [odeS_deriv, odeY_deriv a b c d hab hd]
  simp [delta, ell, derivative_comp, derivative_mul, derivative_sub, derivative_add,
    derivative_X, derivative_one, derivative_C, mul_comp, add_comp, sub_comp, pow_comp,
    C_comp, X_comp, one_comp, map_ofNat]
  ring

private lemma coeff_mul_initial (P Q : R[X]) (n : ℕ) (hq : ∀ j < n, Q.coeff j = 0) :
    (P*Q).coeff n = P.coeff 0 * Q.coeff n := by
  rw [coeff_mul, sum_eq_single (0,n)]
  · rintro ⟨i,j⟩ hij hne
    simp only [HasAntidiagonal.mem_antidiagonal] at hij
    rw [hq j (by
      by_contra! hn
      exact hne (Prod.ext (by omega) (by omega))), mul_zero]
  · simp

private lemma odeS_initial (q c : R) (P : R[X]) (n : ℕ)
    (hp : ∀ j < n, P.coeff j = 0) :
    ((1-X)*odeS q c P).coeff n =
      ((n : R) * ((n : R)+c-1) * ((n : R)+2*c-2)) * P.coeff n := by
  have hz (k : ℕ) (hk : k ≤ n) (P0 : R[X])
      (hP0 : ∀ j < k, P0.coeff j = 0) :
      (odeS q c P0).coeff k =
        ((k : R) * ((k : R)+c-1) * ((k : R)+2*c-2)) * P0.coeff k := by
    have hs : ∀ a b (j : ℕ), j < k → (theta (step a (step b P0))).coeff j = 0 := by
      intro a b j hj
      simp [theta_coeff, step_coeff, hP0 j hj]
    have hs' : ∀ a (j : ℕ), j < k → (theta (step a P0)).coeff j = 0 := by
      intro a j hj
      simp [theta_coeff, step_coeff, hP0 j hj]
    have ht : ∀ j < k, (theta P0).coeff j = 0 := by
      intro j hj
      simp [theta_coeff, hP0 j hj]
    simp only [odeS, coeff_add]
    rw [coeff_mul_initial _ _ _ (hs _ _), coeff_mul_initial _ _ _ (hs' _),
      coeff_mul_initial _ _ _ ht, coeff_mul_initial _ _ _ hP0]
    simp [delta, ell, coeff_zero_eq_eval_zero, theta_coeff, step_coeff]
    ring
  rw [coeff_mul_initial _ _ _ (fun j hj => by
    rw [hz j (by omega) P (fun i hi => hp i (by omega)), hp j hj, mul_zero]), hz n le_rfl P hp]
  simp [coeff_zero_eq_eval_zero]

private lemma odeS_C_mul (q c k : R) (P : R[X]) :
    odeS q c (C k * P) = C k * odeS q c P := by
  simp [odeS, theta, step, derivative_mul, derivative_C]
  ring

private lemma odeS_sub (q c : R) (P Q : R[X]) :
    odeS q c (P-Q) = odeS q c P - odeS q c Q := by
  simp [odeS, theta, step, derivative_sub]
  ring

private lemma theta_dvd (P : R[X]) {p : ℕ} (hp : X^p ∣ P) : X^p ∣ theta P := by
  rw [X_pow_dvd_iff] at hp ⊢
  intro n hn
  rw [theta_coeff, hp n hn, mul_zero]

/-- The symmetric square and the quadratic substitution satisfy the same
coefficient recursion through degree $p-1$. This proves the finite form
of Clausen's square identity used here. -/
private lemma clausal_square (a b c d k : R) (hab : a+b = 2*c-1) (hd : 2*d = 2*c-1)
    (p : ℕ) (T Y : R[X]) (h0 : (Y.comp delta).coeff 0 = k * (T^2).coeff 0)
    (hu : ∀ n : ℕ, 0 < n → n < p → IsUnit (((n : R) * ((n : R)+c-1) * ((n : R)+2*c-2))))
    (ht : X^p ∣ odeT a b c T) (hy : odeY a b c d Y = 0)
    (htdeg : (T^2).natDegree < p) (hydeg : (Y.comp delta).natDegree < p) :
    Y.comp delta = C k * T^2 := by
  have hs : X^p ∣ (1-X)*odeS (a*b) c (T^2) := by
    rw [odeS_square a b c hab]
    exact dvd_mul_of_dvd_right (dvd_add
      (dvd_mul_of_dvd_right (theta_dvd _ ht) _)
      (dvd_mul_of_dvd_right ht _)) _
  have hy' : (1-X)*odeS (a*b) c (Y.comp delta) = 0 := by
    rw [odeS_comp a b c d hab hd, hy, zero_comp, mul_zero]
  let P := Y.comp delta - C k * T^2
  have hz : X^p ∣ (1-X)*odeS (a*b) c P := by
    change X^p ∣ (1-X)*odeS (a*b) c (Y.comp delta - C k * T^2)
    rw [odeS_sub, mul_sub, hy', zero_sub, odeS_C_mul,
      show (1-X)* (C k * odeS (a*b) c (T^2)) = C k * ((1-X)*odeS (a*b) c (T^2)) by ring]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hs _)
  rw [X_pow_dvd_iff] at hz
  have hall (n : ℕ) : P.coeff n = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < p
      · by_cases hn0 : n = 0
        · subst n
          simpa [P, coeff_sub, coeff_C_mul, h0]
        · have h := hz n hn
          rw [odeS_initial _ _ _ _ ih] at h
          exact (hu n (by omega) hn).mul_left_cancel (by simpa using h)
      · simp [P, coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (show (Y.comp delta).natDegree < n by omega),
          coeff_eq_zero_of_natDegree_lt (show (T^2).natDegree < n by omega)]
  exact sub_eq_zero.mp (Polynomial.ext fun n => by simpa [P] using hall n)

private noncomputable def polyOf (N : ℕ) (f : ℕ → R) : R[X] :=
  ∑ i ∈ range N, monomial i (f i)

private lemma polyOf_coeff (N : ℕ) (f : ℕ → R) (n : ℕ) :
    (polyOf N f).coeff n = if n < N then f n else 0 := by
  rw [polyOf, finsetSum_coeff]
  by_cases h : n < N
  · rw [if_pos h, sum_eq_single n, coeff_monomial_same]
    · intro b hb hbn
      simp [coeff_monomial, hbn, Ne.symm hbn]
    · simp [h]
  · rw [if_neg h]
    apply sum_eq_zero
    intro i hi
    have hni : i ≠ n := by have := mem_range.mp hi; omega
    simp [coeff_monomial, hni, Ne.symm hni]

private lemma polyOf_odeT (a b c : R) (p : ℕ) (f : ℕ → R)
    (hf : ∀ n, n+1 < p →
      ((n : R)+1)*((n : R)+c)*f (n+1) = ((n : R)+a)*((n : R)+b)*f n) :
    X^p ∣ odeT a b c (polyOf p f) := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [odeT, coeff_sub, theta_coeff]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, step_coeff, step_coeff, step_coeff, polyOf_coeff, polyOf_coeff,
      if_pos hn, if_pos (by omega : n < p), Nat.cast_add, Nat.cast_one]
    rw [show (n : R) + 1 + (c-1) = (n : R)+c by ring]
    linear_combination hf n hn

private lemma polyOf_odeY (a b c d : R) (h : ℕ) (f : ℕ → R) (hd : d = -(h : R))
    (hf : ∀ n < h, ((n : R)+1)*((n : R)+c)*((n : R)+2*c-1)*f (n+1) =
      4*((n : R)+a)*((n : R)+b)*((n : R)+d)*f n) :
    odeY a b c d (polyOf (h+1) f) = 0 := by
  ext n
  rw [odeY, coeff_sub, theta_coeff, coeff_zero, mul_assoc, coeff_C_mul]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, step_coeff, step_coeff, step_coeff, step_coeff, step_coeff,
      polyOf_coeff, polyOf_coeff, Nat.cast_add, Nat.cast_one]
    rcases lt_trichotomy n h with hn | rfl | hn
    · rw [if_pos (by omega : n+1 < h+1), if_pos (by omega : n < h+1)]
      linear_combination hf n hn
    · simp [hd]
    · rw [if_neg (by omega : ¬ n+1 < h+1), if_neg (by omega : ¬ n < h+1)]
      ring

end Operators
end OMA

namespace OMA
open Polynomial Finset

private lemma nat_unit {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {n : ℕ} (hn : 0 < n) (hnp : n < p) : IsUnit (n : K) := by
  rw [← map_natCast (ZMod.castHom (dvd_refl p) K)]
  exact (isUnit_iff_ne_zero.mpr fun hz => by
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p n).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hn hnp) hd).map _

private lemma coeff_mul_frobenius {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (P Q : K[X]) {n : ℕ} (hn : n < p) :
    (P * Q ^ p).coeff n = P.coeff n * Q.coeff 0 ^ p := by
  have hQ := X_mul_divX_add Q
  conv_lhs => rw [← hQ, add_pow_char _ _ p, mul_pow, ← C.map_pow, mul_add]
  rw [coeff_add, coeff_mul_C]
  have hz : (P * (X ^ p * Q.divX ^ p)).coeff n = 0 := by
    rw [show P * (X ^ p * Q.divX ^ p) = X ^ p * (P * Q.divX ^ p) by ring,
      coeff_X_pow_mul', if_neg (by omega)]
  rw [hz, zero_add]

private noncomputable def jac {K : Type*} [CommRing K] (A B : K[X]) : K[X] :=
  A * B + X * (A * derivative B - derivative A * B)

private lemma hom_coeff {K : Type*} [CommRing K] (P U V : K[X]) (n : ℕ) :
    MvPolynomial.eval₂ C ![U, V] (P.homogenize n) =
      ∑ d ∈ range (n + 1), C (P.coeff d) * U ^ d * V ^ (n - d) := by
  classical
  change (MvPolynomial.eval₂Hom C ![U, V]) (P.homogenize n) = _
  rw [Polynomial.homogenize, map_sum]
  exact Eq.trans (Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (MvPolynomial.eval₂Hom C ![U, V])
      (MvPolynomial.monomial (fun₀ | 0 => i | 1 => j) (P.coeff i))) n) (by
    apply sum_congr rfl
    intro d hd
    rw [MvPolynomial.eval₂Hom_monomial]
    simp [Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc])

private lemma hom_pow {K : Type*} [CommRing K] (P : K[X]) (h : ℕ) (hd : P.natDegree ≤ 3) :
    (P ^ h).homogenize (3 * h) = P.homogenize 3 ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 3 * (h + 1) = 3 * h + 3 by omega, pow_succ,
      Polynomial.homogenize_mul _ _ _ hd, ih, pow_succ]
    exact natDegree_pow_le.trans (by simpa [mul_comm] using Nat.mul_le_mul_left h hd)

/-- Transport the coefficient at infinity using reversed polynomials.
In the term of shift $d<h$, the coefficient of order $m=h-d$ vanishes
because $mQ-XQ'$ has zero coefficient in degree $m$. -/
private lemma residue_coeff {K : Type*} [CommRing K] {p h : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p = 2 * h + 1) (P A B : K[X]) :
    ((MvPolynomial.eval₂ C ![X * B, A] (P.homogenize (3 * h))) * B ^ h * jac A B).coeff h =
      (A.coeff 0 ^ p * B.coeff 0 ^ p) * P.coeff h := by
  rw [hom_coeff, sum_mul, sum_mul, finsetSum_coeff]
  rw [sum_eq_single h]
  · rw [mul_pow]
    rw [show C (P.coeff h) * (X ^ h * B ^ h) * A ^ (3 * h - h) * B ^ h * jac A B =
      X ^ h * (C (P.coeff h) * A ^ (3*h-h) * B ^ (h+h) * jac A B) by rw [pow_add]; ring]
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    simp only [jac, coeff_zero_eq_eval_zero, eval_mul, eval_C, eval_pow, eval_add, eval_X, zero_mul, add_zero]
    rw [ show 3 * h - h = 2 * h by omega, show h+h = 2*h by omega, hp]
    rw [pow_succ, pow_succ]
    ring
  · intro d hd hdh
    rw [mul_pow]
    rw [show C (P.coeff d) * (X ^ d * B ^ d) * A ^ (3*h-d) * B ^ h * jac A B =
      X ^ d * (C (P.coeff d) * (A ^ (3*h-d) * B ^ (h+d) * jac A B)) by rw [pow_add]; ring,
      coeff_X_pow_mul']
    split_ifs with hle
    · rw [coeff_C_mul]
      have hm : 0 < h - d := by omega
      let m := h - d
      have hm' : 0 < m := hm
      have hmp : m < p := by dsimp [m]; omega
      have hap : 3 * h - d = (m - 1) + p := by dsimp [m]; omega
      rw [hap, pow_add,
        show A ^ (m - 1) * A ^ p * B ^ (h + d) * jac A B =
          (A ^ (m - 1) * B ^ (h + d) * jac A B) * A ^ p by ring,
        coeff_mul_frobenius _ _ hmp]
      suffices hz : (A ^ (m - 1) * B ^ (h + d) * jac A B).coeff m = 0 by
        rw [hz, zero_mul, mul_zero]
      have hcast : ((h + d + 1 : ℕ) : K) = -(m : K) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, show h + d + 1 + m = p by dsimp [m]; omega,
          CharP.cast_eq_zero]
      let Q := A ^ m * B ^ (h + d + 1)
      have hq :
          C (m : K) * (A ^ (m - 1) * B ^ (h + d) * jac A B) =
            C (m : K) * Q - X * derivative Q := by
        simp only [Q, jac, derivative_mul, derivative_pow, hcast, map_neg, ← C_eq_natCast,
          Nat.add_sub_cancel]
        rw [show A ^ m = A ^ (m-1) * A from by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
          rw [pow_succ],
          pow_succ B (h+d)]
        ring
      have hq' := congrArg (fun f : K[X] => f.coeff m) hq
      rw [coeff_C_mul, coeff_sub, coeff_C_mul] at hq'
      have hxd : (X * derivative Q).coeff m = Q.coeff m * (m : K) := by
        obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m-1, by omega⟩
        rw [hi, coeff_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one]
      rw [hxd, mul_comm (Q.coeff m), sub_self] at hq'
      exact (nat_unit (K := K) hm' hmp).mul_left_cancel (by simpa using hq')
    · rfl
  · intro hh
    exact False.elim (hh (mem_range.mpr (by omega)))

private noncomputable def cubicRev {K : Type*} [CommRing K] (b c : K) : K[X] :=
  1 + C 4 * X + C b * X ^ 2 + C c * X ^ 3

private lemma cubicRev_degree {K : Type*} [CommRing K] (b c : K) :
    (cubicRev b c).natDegree ≤ 3 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [cubicRev, coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : (2 : ℕ) ≠ n := by omega
  have h3 : (3 : ℕ) ≠ n := by omega
  simp [h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

private lemma cubic_hom {K : Type*} [CommRing K] (b c : K) (A B : K[X]) :
    MvPolynomial.eval₂ C ![X * B, A] ((cubicRev b c).homogenize 3) =
      A ^ 3 + C 4 * (X * B) * A ^ 2 + C b * (X * B) ^ 2 * A + C c * (X * B) ^ 3 := by
  simp [cubicRev, homogenize_add, homogenize_C_mul, homogenize_X_pow, mul_assoc,
    show (2 : ℕ) ≤ 3 by decide]


-- Both reversed isogeny polynomials are scaled by 25 to clear the denominators.
private noncomputable def certB {K : Type*} [CommRing K] (s : K) : K[X] :=
  (C 5 + C (5-5*s)*X + C (5-2*s)*X^2)^2

private noncomputable def certA {K : Type*} [CommRing K] (s : K) : K[X] :=
  certB s + 5*X^2*(C (80+24*s) + C (-24*s)*X + C (-24+16*s)*X^2 + C (-72+32*s)*X^3)

private noncomputable def certG {K : Type*} [CommRing K] (s : K) : K[X] :=
  cubicRev (25*(2-s)-128) (200*(2-s)-768)

private noncomputable def certF {K : Type*} [CommRing K] (s : K) : K[X] :=
  cubicRev (2-s) 0

private lemma residue_isogeny {K : Type*} [CommRing K] {p h : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p = 2*h+1) {G F A B : K[X]} (hd : G.natDegree ≤ 3)
    (hunit : IsUnit ((jac A B).coeff 0))
    (he : MvPolynomial.eval₂ C ![X*B,A] (G.homogenize 3) * B = F * jac A B ^ 2) :
    (G ^ h).coeff h = (F ^ h).coeff h := by
  have hh := residue_coeff hp (G^h) A B
  have heval : MvPolynomial.eval₂ C ![X*B,A] ((G^h).homogenize (3*h)) * B^h * jac A B =
      F^h * jac A B ^ p := by
    rw [hom_pow _ _ hd, show MvPolynomial.eval₂ C ![X*B,A] (G.homogenize 3 ^ h) =
      (MvPolynomial.eval₂ C ![X*B,A] (G.homogenize 3)) ^ h from
        map_pow (MvPolynomial.eval₂Hom C ![X*B,A]) _ _]
    calc
      _ = (MvPolynomial.eval₂ C ![X*B,A] (G.homogenize 3) * B)^h * jac A B := by rw [mul_pow]
      _ = _ := by rw [he, mul_pow, ← pow_mul, mul_assoc, ← pow_succ, ← hp]
  rw [heval, coeff_mul_frobenius _ _ (by omega)] at hh
  have hc : (jac A B).coeff 0 = A.coeff 0 * B.coeff 0 := by simp [jac, coeff_zero_eq_eval_zero]
  have hu := hunit.pow p
  apply hu.mul_left_cancel
  rw [hc, mul_pow]
  rw [hc, mul_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

private lemma affine_coeff {K : Type*} [CommRing K] {p h : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p = 2*h+1) (s : K) (hu : IsUnit (-5 : K)) :
    (certG s ^ h).coeff h = (-5 : K)^h * (certF s ^ h).coeff h := by
  let A : K[X] := C (-5) - C 8 * X
  have hj : jac A 1 = C (-5) := by
    simp [A, jac, derivative_sub, derivative_mul, derivative_X, derivative_C]
  have he : MvPolynomial.eval₂ C ![X*(1 : K[X]), A] ((certG s).homogenize 3) * 1 =
      (C (-5) * certF s) * jac A 1 ^ 2 := by
    rw [certG, cubic_hom, hj]
    simp [certF, cubicRev, A, map_sub, map_add, map_mul, map_neg, map_ofNat, C_eq_natCast]
    ring
  have hJ : IsUnit ((jac A (1 : K[X])).coeff 0) := by simpa [hj] using hu
  have h := residue_isogeny hp (G := certG s) (cubicRev_degree _ _) hJ he
  rw [mul_pow, ← C.map_pow, coeff_C_mul] at h
  exact h

set_option maxHeartbeats 1500000 in
private lemma certificate {K : Type*} [CommRing K] (s : K) (hs : s^2=5) :
    MvPolynomial.eval₂ C ![X*certB s, certA s] ((certG s).homogenize 3) * certB s =
      certF s * jac (certA s) (certB s) ^ 2 := by
  rw [certG, cubic_hom]
  have H := congrArg (C : K → K[X]) hs
  simp only [map_pow, map_ofNat] at H
  have HB : certB s = (((25)) * X^0 +
      ((50) + (-50) * (C s)^1) * X^1 +
      ((200) + (-70) * (C s)^1) * X^2 +
      ((150) + (-70) * (C s)^1) * X^3 +
      ((45) + (-20) * (C s)^1) * X^4) := by
    simp only [certB, map_add, map_sub, map_mul, map_ofNat]
    linear_combination (((25)) * X^2 +
      ((20)) * X^3 +
      ((4)) * X^4) * H
  have HA : certA s = (((25)) * X^0 +
      ((50) + (-50) * (C s)^1) * X^1 +
      ((600) + (50) * (C s)^1) * X^2 +
      ((150) + (-190) * (C s)^1) * X^3 +
      ((-75) + (60) * (C s)^1) * X^4 +
      ((-360) + (160) * (C s)^1) * X^5) := by
    simp only [certA, certB, map_add, map_sub, map_mul, map_ofNat, map_neg]
    linear_combination (((25)) * X^2 +
      ((20)) * X^3 +
      ((4)) * X^4) * H
  have HJ : jac (certA s) (certB s) = (((625)) * X^0 +
      ((2500) + (-2500) * (C s)^1) * X^1 +
      ((15000) + (-11500) * (C s)^1) * X^2 +
      ((62500) + (-24500) * (C s)^1) * X^3 +
      ((133750) + (-55000) * (C s)^1) * X^4 +
      ((247500) + (-111500) * (C s)^1) * X^5 +
      ((365000) + (-163500) * (C s)^1) * X^6 +
      ((307500) + (-137500) * (C s)^1) * X^7 +
      ((100625) + (-45000) * (C s)^1) * X^8) := by
    rw [HA, HB]
    simp only [jac, derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_X, derivative_C, derivative_natCast,
      derivative_ofNat, derivative_zero, derivative_one, derivative_neg, neg_zero, C_eq_natCast,
      zero_mul, mul_zero, add_zero, zero_add]
    linear_combination (((2500)) * X^2 +
      ((7000)) * X^3 +
      ((-2500)) * X^4 +
      ((3000)) * X^5 +
      ((38500)) * X^6 +
      ((30000)) * X^7 +
      ((10000)) * X^8) * H
  rw [HJ, HA, HB]
  simp only [certF, cubicRev, map_add, map_sub, map_mul, map_ofNat, map_zero, zero_mul, add_zero]
  linear_combination (((3125000)) * X^2 +
      ((60000000) + (-12500000) * (C s)^1) * X^3 +
      ((537750000) + (-288125000) * (C s)^1 + (6250000) * (C s)^2) * X^4 +
      ((3274375000) + (-2617500000) * (C s)^1 + (327500000) * (C s)^2) * X^5 +
      ((15134375000) + (-14637125000) * (C s)^1 + (3480000000) * (C s)^2 + (-156250000) * (C s)^3) * X^6 +
      ((55340000000) + (-59570250000) * (C s)^1 + (19152500000) * (C s)^2 + (-1750000000) * (C s)^3) * X^7 +
      ((162405625000) + (-187349125000) * (C s)^1 + (69868750000) * (C s)^2 + (-8512500000) * (C s)^3) * X^8 +
      ((386211625000) + (-461058000000) * (C s)^1 + (184060000000) * (C s)^2 + (-24885000000) * (C s)^3) * X^9 +
      ((740116875000) + (-885858500000) * (C s)^1 + (360360000000) * (C s)^2 + (-50093750000) * (C s)^3) * X^10 +
      ((1119467500000) + (-1319821000000) * (C s)^1 + (532497500000) * (C s)^2 + (-73845000000) * (C s)^3) * X^11 +
      ((1309187500000) + (-1512875875000) * (C s)^1 + (598596250000) * (C s)^2 + (-81977500000) * (C s)^3) * X^12 +
      ((1169470625000) + (-1322334500000) * (C s)^1 + (512032500000) * (C s)^2 + (-69125000000) * (C s)^3) * X^13 +
      ((790606125000) + (-873109625000) * (C s)^1 + (330182500000) * (C s)^2 + (-43781250000) * (C s)^3) * X^14 +
      ((398402500000) + (-427561250000) * (C s)^1 + (156740000000) * (C s)^2 + (-20220000000) * (C s)^3) * X^15 +
      ((141461875000) + (-148636875000) * (C s)^1 + (52425000000) * (C s)^2 + (-6370000000) * (C s)^3) * X^16 +
      ((31259375000) + (-32800000000) * (C s)^1 + (11100000000) * (C s)^2 + (-1200000000) * (C s)^3) * X^17 +
      ((3025000000) + (-3312500000) * (C s)^1 + (1100000000) * (C s)^2 + (-100000000) * (C s)^3) * X^18) * H

private lemma hasse_vanish {K : Type*} [CommRing K] {p h : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p = 2*h+1) (hp5 : 5 < p) (s : K) (hs : s^2 = 5) (hi : (-5 : K)^h = -1) :
    (certF s ^ h).coeff h = 0 := by
  have h5 : IsUnit (5 : K) := nat_unit (p := p) (by decide : 0 < 5) hp5
  have hj : (jac (certA s) (certB s)).coeff 0 = (5 : K)^4 := by
    simp [jac, certA, certB, coeff_zero_eq_eval_zero, pow_succ, mul_assoc]
  have he := residue_isogeny hp (G := certG s) (cubicRev_degree _ _) (show IsUnit ((jac (certA s) (certB s)).coeff 0) by rw [hj]; exact h5.pow 4)
    (certificate s hs)
  have ha := affine_coeff hp s h5.neg
  rw [he, hi, neg_one_mul] at ha
  apply (nat_unit (p := p) (by decide : 0 < 2) (by omega : 2 < p)).mul_left_cancel
  linear_combination ha

end OMA

namespace OMA

open Finset Polynomial

private abbrev Quadr (R : Type*) [CommRing R] := QuadraticAlgebra R (5 : R) 0

private def quadMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Quadr R →+* Quadr S where
  toFun x := ⟨f x.re, f x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    simp [QuadraticAlgebra.mk_mul_mk, map_ofNat]

private lemma quad_omega_sq (R : Type*) [CommRing R] : (QuadraticAlgebra.omega : Quadr R)^2 = 5 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp [map_ofNat]

private lemma quad_kernel_sq {p : ℕ} (hp : p.Prime) (x : Quadr (R2 p))
    (hx : quadMap (red p) x = 0) : x^2 = 0 := by
  have hr : red p x.re = 0 := congrArg QuadraticAlgebra.re hx
  have hi : red p x.im = 0 := congrArg QuadraticAlgebra.im hx
  obtain ⟨r, hr⟩ := red_kern hp hr
  obtain ⟨i, hi⟩ := red_kern hp hi
  have he : x = (p : Quadr (R2 p))*⟨r,i⟩ := by
    ext
    · simpa [QuadraticAlgebra.re_mul] using hr
    · simpa [QuadraticAlgebra.im_mul] using hi
  rw [he, mul_pow]
  have hh : (p : Quadr (R2 p))^2 = 0 := by
    simpa only [map_pow, map_natCast, map_zero] using
      congrArg (algebraMap (R2 p) (Quadr (R2 p))) (p_sq_zero p)
  rw [hh, zero_mul]

private lemma inert_euler (p : ℕ) [Fact p.Prime] (hp5 : 5 < p)
    (hm : p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19) :
    (-5 : ZMod p)^(p/2) = -1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hqr : legendreSym p 5 = legendreSym 5 (p : ℤ) := by
    simpa using (legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
      (by decide) (by omega))
  have h2 : legendreSym 5 2 = -1 :=
    (legendreSym.eq_neg_one_iff 5).mpr (by decide +kernel)
  have h3 : legendreSym 5 3 = -1 :=
    (legendreSym.eq_neg_one_iff 5).mpr (by decide +kernel)
  have h4 : legendreSym 5 4 = 1 :=
    (legendreSym.eq_one_iff 5 (by decide : ((4 : ℤ) : ZMod 5) ≠ 0)).mpr ⟨2, by decide⟩
  have hl : legendreSym p (-5) = -1 := by
    rw [legendreSym.at_neg (by omega), hqr, legendreSym.mod 5 (p : ℤ), ZMod.χ₄_nat_mod_four]
    rcases hm with hm | hm | hm | hm
    · rw [show (p : ℤ) % (↑(5 : ℕ) : ℤ) = 1 by omega, show p % 4 = 3 by omega, legendreSym.at_one]
      decide
    · rw [show (p : ℤ) % (↑(5 : ℕ) : ℤ) = 3 by omega, show p % 4 = 1 by omega, h3]
      decide
    · rw [show (p : ℤ) % (↑(5 : ℕ) : ℤ) = 2 by omega, show p % 4 = 1 by omega, h2]
      decide
    · rw [show (p : ℤ) % (↑(5 : ℕ) : ℤ) = 4 by omega, show p % 4 = 3 by omega, h4]
      decide
  simpa [hl] using (legendreSym.eq_pow p (-5)).symm

private def tCoef (p n : ℕ) : R2 p :=
  ((∏ j ∈ range n, ((j : R2 p) + pa p)) *
    (∏ j ∈ range n, ((j : R2 p) + pb p))) *
    ∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹

private lemma pc_red (p : ℕ) : red p (pc p) = 1 := by
  simp [pc, map_sub, map_mul, map_natCast]

private lemma t_recurrence {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : n+1 < p) :
    ((n : R2 p)+1)*((n : R2 p)+pc p)*tCoef p (n+1) =
      ((n : R2 p)+pa p)*((n : R2 p)+pb p)*tCoef p n := by
  have h : IsUnit (((n : R2 p)+1)*((n : R2 p)+pc p)) := by
    apply unit_red hp
    rw [map_mul, map_add, map_add, map_natCast, map_one, pc_red]
    have h' : (n : ZMod p)+1 ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact fun hz => Nat.not_dvd_of_pos_of_lt (by omega) hn ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    letI : Fact p.Prime := ⟨hp⟩
    exact mul_ne_zero h' h'
  simp only [tCoef, prod_range_succ]
  rw [show ((n : R2 p)+1)*((n : R2 p)+pc p) *
      (((∏ j ∈ range n, ((j : R2 p) + pa p)) * ((n : R2 p) + pa p)) *
        ((∏ j ∈ range n, ((j : R2 p) + pb p)) * ((n : R2 p) + pb p)) *
        ((∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹) *
          ((((n : R2 p)+1)*((n : R2 p)+pc p)))⁻¹)) =
        ((((n : R2 p)+1)*((n : R2 p)+pc p)) *
          ((((n : R2 p)+1)*((n : R2 p)+pc p)))⁻¹) *
        (((n : R2 p)+pa p)*((n : R2 p)+pb p) *
          (((∏ j ∈ range n, ((j : R2 p) + pa p)) * (∏ j ∈ range n, ((j : R2 p) + pb p))) *
            (∏ j ∈ range n, (((j : R2 p)+1)*((j : R2 p)+pc p))⁻¹))) by ring,
      ZMod.mul_inv_of_unit _ h, one_mul]

private lemma recover_term {p : ℕ} (hp : p.Prime) (a : R2 p) (n : ℕ)
    (hn : (-(red p a)).val < n) :
    ∃ d : R2 p, (∏ j ∈ range n, ((j : R2 p) + a)) = (p : R2 p)*d := by
  apply red_kern hp
  rw [map_prod]
  apply Finset.prod_eq_zero (mem_range.mpr hn)
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [map_add, map_natCast, ZMod.natCast_zmod_val, neg_add_cancel]

/-- The two root offsets sum to $p-1$. A product of coefficients in
total degree at least $p$ therefore contains two factors of $p$. -/
private lemma high_t_mul {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1)
    (i j : ℕ) (hij : p ≤ i+j) : tCoef p i * tCoef p j = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let a := (-(red p (pa p))).val
  let b := (-(red p (pb p))).val
  have ha : a < p := ZMod.val_lt _
  have hb : b < p := ZMod.val_lt _
  have hs : (a : ZMod p) + (b : ZMod p) = -1 := by
    rw [show (a : ZMod p) = -(red p (pa p)) from ZMod.natCast_zmod_val _,
      show (b : ZMod p) = -(red p (pb p)) from ZMod.natCast_zmod_val _,
      ← neg_add, ← map_add, (param_sums hp hp2 hh).1]
    simp [pc_red, map_ofNat] <;> ring
  have hs' : a+b=p-1 := by
    have hcast : ((a+b+1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hs, neg_add_cancel]
    obtain ⟨r, hr⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hbound : p*r < p*2 := by omega
    have hr2 : r < 2 := Nat.lt_of_mul_lt_mul_left hbound
    interval_cases r <;> omega
  have bothA (hi : a < i) (hj : a < j) : tCoef p i * tCoef p j = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pa p) i hi
    obtain ⟨y, hy⟩ := recover_term hp (pa p) j hj
    simp only [tCoef, hx, hy] 
    linear_combination
      (x*y * (∏ k ∈ range i, ((k : R2 p)+pb p)) * (∏ k ∈ range j, ((k : R2 p)+pb p)) *
        (∏ k ∈ range i, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹) *
        (∏ k ∈ range j, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹)) * p_sq_zero p
  have bothB (hi : b < i) (hj : b < j) : tCoef p i * tCoef p j = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pb p) i hi
    obtain ⟨y, hy⟩ := recover_term hp (pb p) j hj
    simp only [tCoef, hx, hy]
    linear_combination
      (x*y * (∏ k ∈ range i, ((k : R2 p)+pa p)) * (∏ k ∈ range j, ((k : R2 p)+pa p)) *
        (∏ k ∈ range i, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹) *
        (∏ k ∈ range j, (((k : R2 p)+1)*((k : R2 p)+pc p))⁻¹)) * p_sq_zero p
  have single (n : ℕ) (ha : a < n) (hb : b < n) : tCoef p n = 0 := by
    obtain ⟨x, hx⟩ := recover_term hp (pa p) n ha
    obtain ⟨y, hy⟩ := recover_term hp (pb p) n hb
    rw [tCoef, hx, hy, show (p : R2 p)*x*((p : R2 p)*y)=(p : R2 p)^2*(x*y) by ring,
      p_sq_zero, zero_mul, zero_mul]
  by_cases hai : a < i <;> by_cases haj : a < j <;> by_cases hbi : b < i <;> by_cases hbj : b < j <;>
    first | exact bothA hai haj | exact bothB hbi hbj | rw [single i hai hbi, zero_mul] |
      rw [single j haj hbj, mul_zero] | omega


private lemma binomial_pair_prod {K : Type*} [CommRing K] (h j : ℕ) :
    (j.factorial : K)^2 * (h.choose j : K) * ((h-j).choose j : K) =
      ∏ i ∈ range (2*j), ((h : K) - (i : K)) := by
  by_cases hh : 2*j ≤ h
  · rw [pow_two]
    calc
      _ = ((j.factorial : K) * (h.choose j : K)) *
          ((j.factorial : K) * ((h-j).choose j : K)) := by ring
      _ = _ := by
        rw [choose_mul_factorial_prod (by omega : j ≤ h), choose_mul_factorial_prod (by omega : j ≤ h-j),
          show 2*j=j+j by omega, prod_range_add, Nat.cast_sub (by omega : j ≤ h)]
        congr 1
        apply prod_congr rfl
        intro i hi
        push_cast
        ring
  · have hzero : (∏ i ∈ range (2*j), ((h : K) - (i : K))) = 0 :=
      prod_eq_zero (mem_range.mpr (by omega : h < 2*j)) (sub_self _)
    rw [hzero]
    by_cases hj : j ≤ h
    · simp [Nat.choose_eq_zero_of_lt (by omega : h-j < j)]
    · simp [Nat.choose_eq_zero_of_lt (by omega : h < j)]

private def pairCoef {K : Type*} [CommRing K] (h n : ℕ) : K :=
  (h.choose n : K) * ((h-n).choose n : K)

private lemma pair_recurrence {K : Type*} [CommRing K] (h n : ℕ)
    (hu : IsUnit (n.factorial : K)) :
    ((n : K)+1)^2 * pairCoef h (n+1) =
      ((h : K)-2*(n : K))*((h : K)-2*(n : K)-1)*pairCoef h n := by
  have h0 := binomial_pair_prod (K := K) h n
  have h1 := binomial_pair_prod (K := K) h (n+1)
  rw [show 2*(n+1)=2*n+1+1 by omega, prod_range_succ, prod_range_succ,
    Nat.factorial_succ] at h1
  push_cast at h1
  apply (hu.pow 2).mul_left_cancel
  unfold pairCoef
  linear_combination h1 - ((h : K)-2*(n : K))*((h : K)-2*(n : K)-1)*h0

private lemma t_mod_p {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1) {n : ℕ} (hn : n < p) :
    red p (tCoef p n) = pairCoef h n * (red p (half p))^(2*n) := by
  let i := red p (half p)
  have hi : (2 : ZMod p) * i = 1 := by
    simpa only [i, map_mul, map_one, map_ofNat] using congrArg (red p) (two_half hp hp2)
  have hp' : (p : ZMod p) = 2*(h : ZMod p)+1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod p)) hh
  rw [ZMod.natCast_self] at hp'
  have ha : red p (pa p) = - (h : ZMod p)*i := by
    simp [pa, i, map_ofNat]
    change i^2 = _
    linear_combination -(h : ZMod p)*i*hi - i^2*hp'
  have hb : red p (pb p) = (1-(h : ZMod p))*i := by
    simp [pb, i, map_ofNat]
    change 3*i^2 = _
    linear_combination -((h : ZMod p)-1)*i*hi - i^2*hp'
  induction n with
  | zero => simp [tCoef, pairCoef]
  | succ n ih =>
    have H := congrArg (red p) (t_recurrence hp n hn)
    simp only [map_mul, map_add, map_one, map_natCast, pc_red, ha, hb] at H
    rw [ih (by omega)] at H
    have hU : IsUnit (n.factorial : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_factorial_of_lt (by omega)).symm
    have hnum : IsUnit (((n : ZMod p)+1)) := by
      rw [← Nat.cast_one, ← Nat.cast_add, ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_of_lt_prime (by omega) hn hp).symm
    apply (hnum.pow 2).mul_left_cancel
    have hR := pair_recurrence h n hU
    have hv : (((n : ZMod p) - (h : ZMod p)*i) * ((n : ZMod p)+(1-(h : ZMod p))*i)) =
        ((h : ZMod p)-2*(n : ZMod p))*((h : ZMod p)-2*(n : ZMod p)-1)*i^2 := by
      linear_combination
        ((n : ZMod p)*((h : ZMod p)*i) + (n : ZMod p)*((h : ZMod p)*i-i) -
          (n : ZMod p)^2*(2*i+1))*hi
    rw [show 2*(n+1)=2*n+2 by omega, pow_add]
    linear_combination H + pairCoef h n * i^(2*n) * hv - i^(2*n)*i^2*hR

private lemma hasse_expansion {K : Type*} [CommRing K] (s i : K) (hi : 2*i=1) (h : ℕ) :
    (certF s ^ h).coeff h =
      (4 : K)^h * ∑ j ∈ range (h+1), pairCoef h j * i^(2*j) * ((2-s)*i^2)^j := by
  have hq : (4 : K)*i^2 = 1 := by linear_combination (2*i+1)*hi
  have hF : certF s = C (2-s) * X^2 + (1 + C 4 * X) := by simp [certF, cubicRev]; ring
  rw [hF, add_pow, finsetSum_coeff, mul_sum]
  apply sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  have htrans : ((1 : K[X]) + C 4 * X)^(h-j) = ((1+X)^(h-j)).comp (C 4 * X) := by
    simp
  rw [mul_pow, ← C.map_pow, ← pow_mul]
  -- Isolate the monomial factor of degree 2j before taking the coefficient.
  rw [show C ((2-s)^j) * X^(2*j) * ((1 + C 4 * X)^(h-j)) * ((h.choose j : ℕ) : K[X]) =
    (C ((2-s)^j * (h.choose j : K)) * ((1 + C 4 * X)^(h-j))) * X^(2*j) by
    rw [C.map_mul, C_eq_natCast]; ring]
  rw [coeff_mul_X_pow']
  by_cases hjh : 2*j ≤ h
  · rw [if_pos hjh, coeff_C_mul, htrans, comp_C_mul_X_coeff, coeff_one_add_X_pow,
      show h-2*j=h-j-j by omega, Nat.choose_symm (show j ≤ h-j by omega)]
    rw [show h-j-j=h-2*j by omega, pow_mul i 2 j, mul_pow (2-s) (i^2) j]
    unfold pairCoef
    have hpow : (4 : K)^h * (i^2)^j * (i^2)^j = (4 : K)^(h-2*j) := by
      have hpw : (4 : K)^h = (4 : K)^(h-2*j) * ((4 : K)^2)^j := by
        rw [← pow_mul, ← pow_add, show h-2*j+2*j=h by omega]
      have hz : (4 : K)^2*i^2*i^2 = 1 := by linear_combination ((4 : K)*i^2+1)*hq
      calc
        _ = (4 : K)^(h-2*j) * (((4 : K)^2*i^2*i^2)^j) := by
          rw [hpw, mul_pow, mul_pow]; ring
        _ = _ := by rw [hz, one_pow, mul_one]
    linear_combination -(h.choose j : K)*((h-j).choose j : K)*(2-s)^j*hpow
  · rw [if_neg hjh]
    simp [pairCoef, Nat.choose_eq_zero_of_lt (show h-j<j by omega)]


private lemma polyOf_eval₂ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : S) (n : ℕ) (c : ℕ → R) :
    (polyOf n c).eval₂ f x = ∑ j ∈ range n, f (c j) * x^j := by
  simp [polyOf, eval₂_finsetSum, eval₂_monomial]

private lemma t_square_degree {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1) :
    ((polyOf p (tCoef p))^2).natDegree < p := by
  apply lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr _) (show p-1 < p by omega)
  intro n hn
  rw [pow_two (polyOf p (tCoef p)), coeff_mul]
  apply sum_eq_zero
  rintro ⟨i,j⟩ hij
  simp only [HasAntidiagonal.mem_antidiagonal] at hij
  simp only [polyOf_coeff]
  by_cases hi : i < p <;> by_cases hj : j < p <;>
    simp [hi, hj, high_t_mul hp hp2 hh i j (by omega)]

private lemma t_vanishing {p h : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hh : p=2*h+1)
    (hm : p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19) :
    let k := algebraMap (R2 p) (Quadr (R2 p))
    let u := (2 - QuadraticAlgebra.omega) * (k (half p))^2
    ((polyOf p (tCoef p)).eval₂ k u)^2 = 0 := by
  dsimp only
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (Quadr (ZMod p)) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  let K := Quadr (ZMod p)
  let s : K := QuadraticAlgebra.omega
  let f := algebraMap (ZMod p) (Quadr (ZMod p))
  let i := f (red p (half p))
  let x := (2-s)*i^2
  have hi : (2 : K)*i = 1 := by
    have h := congrArg (f.comp (red p)) (two_half hp (by omega))
    simpa only [i, RingHom.comp_apply, map_ofNat, map_mul, map_one] using h
  have hLeg : (-5 : K)^h = -1 := by
    have hh' : p/2=h := by omega
    have hp' := inert_euler p hp5 hm
    rw [hh'] at hp'
    change (-5 : Quadr (ZMod p))^h = -1
    simpa only [map_pow, map_neg, map_ofNat, map_one] using congrArg f hp'
  have H := hasse_vanish hh hp5 s (quad_omega_sq _) hLeg
  rw [hasse_expansion s i hi] at H
  have h4 : IsUnit (4 : K) := nat_unit (K := K) (p := p) (n := 4) (by decide) (by omega)
  have hzero : (∑ j ∈ range (h+1), pairCoef h j * i^(2*j) * x^j) = 0 :=
    (h4.pow h).mul_left_cancel (by simpa [x] using H)
  apply quad_kernel_sq hp
  rw [polyOf_eval₂, map_sum]
  have hf (a : R2 p) : quadMap (red p) (algebraMap (R2 p) (Quadr (R2 p)) a) = f (red p a) := by
    ext <;> simp [quadMap, f]
  have hsmap : quadMap (red p) (QuadraticAlgebra.omega : Quadr (R2 p)) = s := by
    ext <;> simp [quadMap, s]
  have hu : quadMap (red p) (((2 - QuadraticAlgebra.omega) *
      (algebraMap (R2 p) (Quadr (R2 p)) (half p))^2) : Quadr (R2 p)) = x := by
    simp only [map_mul, map_sub, map_pow, map_ofNat, x, i, hsmap, hf]
  simp_rw [map_mul, map_pow, hu, hf]
  have hcoeff (j : ℕ) (hj : j ∈ range p) :
      f (red p (tCoef p j)) = pairCoef h j * i^(2*j) := by
    rw [t_mod_p hp (by omega) hh (mem_range.mp hj), map_mul, map_pow]
    simp [pairCoef, i, f]
  rw [sum_congr rfl (fun j hj => by rw [hcoeff j hj])]
  calc
    _ = ∑ j ∈ range (h+1), pairCoef h j * i^(2*j) * x^j := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      have hhj : h<j := by simp only [mem_range, not_lt] at hj; omega
      simp [pairCoef, Nat.choose_eq_zero_of_lt hhj]
    _ = 0 := hzero

private lemma total_eq_eval {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p=2*h+1) :
    let f := algebraMap (R2 p) (Quadr (R2 p))
    let u := (2 - QuadraticAlgebra.omega)*(f (half p))^2
    f (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
      ((polyOf (h+1) (weight p h)).comp delta).eval₂ f u := by
  dsimp only
  let f := algebraMap (R2 p) (Quadr (R2 p))
  let i := f (half p)
  let s : Quadr (R2 p) := QuadraticAlgebra.omega
  let u := (2-s)*i^2
  let y := delta.eval₂ f u
  change f _ = _
  have h2 : (2 : Quadr (R2 p))*i = 1 := by
    simpa only [i, map_mul, map_ofNat, map_one] using congrArg f (two_half hp hp2)
  have hs : s^2 = 5 := quad_omega_sq _
  have h4 : (4 : Quadr (R2 p))*i^2=1 := by linear_combination (2*i+1)*h2
  have h16 : (16 : Quadr (R2 p))*i^4=1 := by linear_combination (4*i^2+1)*h4
  have hy : (-16 : Quadr (R2 p))*y = 1 := by
    have hy' : y = u*(1-u) := by simp [y, delta]
    rw [hy']
    dsimp [u]
    linear_combination hs + (s^2 - 4*s + 4)*h16 - 4*(2-s)*h4
  rw [collapse p hp hp2, show (p-1)/2=h by omega, map_sum, eval₂_comp]
  change _ = (polyOf (h+1) (weight p h)).eval₂ f y
  rw [polyOf_eval₂, ← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hjh : j ≤ h := by have := mem_range.mp hj; omega
  rw [show h+1-1-j=h-j by omega,
    ← Nat.choose_symm (show 4*(h-j)+1 ≤ p+2*(h-j) by omega),
    show p+2*(h-j)-(4*(h-j)+1)=2*j by omega]
  simp only [weight, map_mul, map_pow, map_natCast, map_neg, map_ofNat]
  rw [mul_assoc _ ((-16 : Quadr (R2 p))^j) (y^j), ← mul_pow, hy, one_pow, mul_one]

private lemma polynomial_square {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2*h+1) :
    (polyOf (h+1) (weight p h)).comp delta = C (weight p h 0)*(polyOf p (tCoef p))^2 := by
  have hs := param_sums hp hp2 hh
  apply clausal_square (pa p) (pb p) (pc p) (-(h : R2 p)) _ hs.1 hs.2 p
  · have hd0 : (delta : (R2 p)[X]).eval 0 = 0 := by simp [delta]
    rw [coeff_zero_eq_eval_zero, eval_comp, hd0, ← coeff_zero_eq_eval_zero, polyOf_coeff, if_pos (by omega)]
    have H : ((polyOf p (tCoef p)).coeff 0) = 1 := by
      rw [polyOf_coeff, if_pos (by omega)]
      simp [tCoef]
    simp only [pow_two (polyOf p (tCoef p)), mul_coeff_zero, H, mul_one]
  · intro n hn hnp
    apply unit_red hp
    rw [map_mul, map_mul, map_sub, map_sub, map_add, map_add, map_mul, map_natCast, pc_red,
      map_one, map_ofNat, mul_one, add_sub_cancel_right, add_sub_cancel_right]
    have h0 : (n : ZMod p) ≠ 0 :=
      fun hz => Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)
    letI : Fact p.Prime := ⟨hp⟩
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  · exact polyOf_odeT _ _ _ _ _ (t_recurrence hp)
  · apply polyOf_odeY _ _ _ _ _ _ rfl
    intro j hj
    simpa only [sub_eq_add_neg] using weight_recurrence hp hp2 hh j hj
  · exact t_square_degree hp hp2 hh
  · have hy : (polyOf (h+1) (weight p h)).natDegree ≤ h :=
      natDegree_le_iff_coeff_eq_zero.mpr (fun n hn => by rw [polyOf_coeff, if_neg (by omega)])
    have hd : (delta : (R2 p)[X]).natDegree ≤ 2 := by
      have h' : (1-X : (R2 p)[X]).natDegree ≤ 1 :=
        (natDegree_sub_le (p := (1 : (R2 p)[X])) (q := X)).trans (max_le (by simp) natDegree_X_le)
      exact natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le h')
    exact natDegree_comp_le.trans_lt ((Nat.mul_le_mul hy hd).trans_lt (by omega))

end OMA

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @OeisA179524.conjecture3 := by
  intro p hp hmod
  have hm : p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19 := by
    rcases hmod with h | h | h | h <;> unfold Int.ModEq at h <;> omega
  have hp5 : 5 < p := by omega
  let h := (p-1)/2
  have hh : p = 2*h+1 := by dsimp [h]; omega
  have H := OMA.total_eq_eval hp (by omega) hh
  dsimp only at H
  rw [OMA.polynomial_square hp (by omega) hh, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, OMA.t_vanishing hp hp5 hh hm, mul_zero] at H
  have Hz : (∑ n ∈ Finset.range p, (OeisA179524.a n : OMA.R2 p)) = 0 :=
    QuadraticAlgebra.algebraMap_injective (H.trans (map_zero _).symm)
  have Hz' : ((∑ n ∈ Finset.range p, OeisA179524.a n : ℤ) : ZMod (p^2)) = ((0 : ℤ) : ZMod (p^2)) := by
    simpa only [Int.cast_sum, Int.cast_zero] using Hz
  simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ _).mp Hz'
