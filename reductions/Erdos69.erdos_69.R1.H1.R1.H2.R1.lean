import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1
import Mathlib

/-! The near-shift nonconcentration estimate in the elementary part of Erdős 69
splits into a comparison with an independent model for prime divisibilities
and decay of the explicit product in that model. We remove the frozen primes
on the progression and deduce the positive proportion from the first Fourier
coefficient. The progression, growth, cube-weight and modulus bounds below
adapt the merged Erdős 69 variance reduction and scale estimates by @marcusbuffett. -/

open Filter Finset Real
namespace Numeric69
lemma prog_card (x Q b : ℕ) (hx : 256 ≤ x) (hQ : 0 < Q) (hQr : (Q:ℝ) ≤ √(x:ℝ)) :
    √(x:ℝ) ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card:ℝ) := by
  let u := x.sqrt
  have hQn : Q ≤ u := by
    change Q ≤ x.sqrt
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.le_floor hQr
  have hu : 16 ≤ u := by
    exact Nat.le_sqrt.mpr hx
  let f (i : ℕ) := x/2/Q*Q + (i+1)*Q + b%Q
  have hi : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    have he : (i+1)*Q=(j+1)*Q := by omega
    have := Nat.eq_of_mul_eq_mul_right hQ he
    omega
  have him : (range (u/4)).image f ⊆ (Icc (x/2) x).filter fun n => n%Q=b%Q := by
    rintro _ hi'
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hi'
    have hir := mem_range.mp hi
    have hdiv := Nat.div_mul_le_self (x/2) Q
    have hmod := Nat.mod_add_div (x/2) Q
    rw [Nat.mul_comm Q] at hmod
    have hm := Nat.mod_lt (x/2) hQ
    have hb := Nat.mod_lt b hQ
    have hsu := Nat.sqrt_le x
    change u*u ≤ x at hsu
    have hsum : (i+2)*Q ≤ x/2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
      calc
        (i+2)*Q*2 = (2*(i+2))*Q := by ring
        _ ≤ u*u := Nat.mul_le_mul (by omega) hQn
        _ ≤ x := hsu
    have hbase : Q ≤ (i+1)*Q := by exact Nat.le_mul_of_pos_left Q (by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · dsimp [f]; omega
    · dsimp [f]; rw [show i+2=i+1+1 by omega, Nat.add_mul, one_mul] at hsum; omega
    · simp [f,Nat.add_mod]
  have hcard := card_le_card him
  rw [card_image_of_injective _ hi,card_range] at hcard
  have hf := Nat.lt_floor_add_one (√(x:ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hf
  change √(x:ℝ) < (u:ℝ)+1 at hf
  have hbound : u+1 ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card) := by omega
  exact hf.le.trans (by exact_mod_cast hbound)
lemma floor_power (l : ℝ) (hl : 100 ≤ l) :
    let K := ⌊2*log l/log 2⌋₊
    0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ l^2 ≤ 2*(2:ℝ)^K := by
  let t := 2*log l/log 2
  let K := ⌊t⌋₊
  have hl0 : 0 < l := by linarith
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hlog).2
    have := log_le_log (by norm_num : (0:ℝ)<2) (show 2≤l by linarith)
    linarith
  have heq : (2:ℝ)^t=l^2 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hh : log 2 * t = 2*log l := by dsimp [t]; field_simp
    rw [hh, show 2 * log l = log (l^2) by simp [Real.log_pow], Real.exp_log (by positivity)]
  have h1 : (K:ℝ) ≤ t := Nat.floor_le (by linarith)
  have h2 : t ≤ (K:ℝ)+1 := (Nat.lt_floor_add_one t).le
  have hK : 1 ≤ K := Nat.le_floor (by simpa using ht)
  refine ⟨hK, ?_, ?_⟩
  · calc (2:ℝ)^K = 2^(K:ℝ) := (Real.rpow_natCast ..).symm
         _ ≤ 2^t := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
         _ = _ := heq
  · calc l^2 = (2:ℝ)^t := heq.symm
         _ ≤ 2^((K:ℝ)+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
         _ = _ := by rw [Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_one]; ring
end Numeric69

open Filter Real
namespace Numeric69
lemma growth (A : ℝ) : ∀ᶠ x : ℕ in atTop,
    let w := log (log x)
    let l := log w
    let D := exp (4*l^11)
    let R := (x:ℝ)^(1/w^2)
    256 ≤ x ∧ A ≤ l ∧ 100 ≤ l ∧ 2*D < R ∧ D < √(x:ℝ) ∧ D < (x/2:ℕ) ∧
      A ≤ R ∧ R ≤ x ∧ log (log R) = w - 2*l := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hwtop := tendsto_log_atTop.comp hlog
  have hltop := tendsto_log_atTop.comp hwtop
  have he := (tendsto_exp_div_pow_atTop 13).comp hwtop
  filter_upwards [eventually_ge_atTop 256,hlog.eventually_ge_atTop 1,hwtop.eventually_ge_atTop 2,
    hltop.eventually_ge_atTop (max A 100),he.eventually_ge_atTop 16] with x hx hxlog hw0 hl0 hexp
  let w := log (log (x:ℝ))
  let l := log w
  let R := (x:ℝ)^(1/w^2)
  have hxR : 1 < (x:ℝ) := by exact_mod_cast (show 1<x by omega)
  change 1 ≤ log (x:ℝ) at hxlog
  change 2 ≤ w at hw0
  change max A 100 ≤ l at hl0
  change 16 ≤ exp w / w^13 at hexp
  have hw : 0 < w := by linarith
  have hA := (le_max_left A 100).trans hl0
  have hl := (le_max_right A 100).trans hl0
  have hlw : l ≤ w := (log_le_sub_one_of_pos hw).trans (by linarith)
  have hwp : 16*w^13 ≤ log (x:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<w^13)).mp hexp
    simpa [w,Real.exp_log (by linarith : 0<log (x:ℝ))] using hh
  have h11 := pow_le_pow_left₀ (show 0 ≤ l by linarith) hlw 11
  have h13 : w^11 ≤ w^13 := pow_le_pow_right₀ (by linarith) (by decide)
  have hl11 : l ≤ l^11 := le_self_pow₀ (by linarith) (by decide)
  have hlogR : log R = log (x:ℝ) / w^2 := by dsimp [R]; rw [log_rpow (by linarith)]; ring
  have hratio : 16*w^11 ≤ log R := by
    rw [hlogR,le_div_iff₀ (by positivity)]
    calc 16 * w^11 * w^2 = 16*w^13 := by ring
         _ ≤ _ := hwp
  have hlR : 0 < log R := by linarith [show 0 < w^11 by positivity]
  have hR0 : 0 < R := rpow_pos_of_pos (by linarith) _
  have heR : 2*exp (4*l^11) < R := by
    rw [← exp_log (by norm_num : (0:ℝ)<2), ← exp_add, ← exp_log hR0]
    apply exp_lt_exp.mpr
    nlinarith only [hratio,h11,hl11,hl,log_two_lt_d9]
  have hD : exp (4*l^11) < √(x:ℝ) := by
    rw [← exp_log (Real.sqrt_pos.2 (by linarith : 0<(x:ℝ))), log_sqrt (by positivity)]
    apply exp_lt_exp.mpr
    linarith only [h11,h13,hwp,hl11,hl]
  have hs : √(x:ℝ) < (x/2:ℕ) := by
    have hs16 : 16 ≤ √(x:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by
      have h : (256:ℝ)≤ x := by exact_mod_cast hx
      norm_num; linarith)
    have hdiv : (x:ℝ) ≤ 2*((x/2:ℕ):ℝ)+1 := by exact_mod_cast (show x≤2*(x/2)+1 by omega)
    nlinarith [sq_sqrt (by positivity : (0:ℝ) ≤ x),sq_nonneg (√(x:ℝ)-8)]
  refine ⟨hx,hA,hl,heR,hD,hD.trans hs,?_,?_,?_⟩
  · have := add_one_le_exp (log R)
    rw [exp_log hR0] at this
    linarith only [this,hratio,hl11,h11,hA,hl]
  · calc R ≤ (x:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hxR.le
          ((div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (w-2)]))
         _ = _ := rpow_one _
  · change log (log R) = w - 2*l
    rw [hlogR,log_div (by linarith) (by positivity),log_pow]; norm_num [w,l]
end Numeric69

namespace Tail69
open Finset
open scoped Classical
lemma finite_bounds (l : ℝ) (hl : 100 ≤ l) (K H : ℕ)
    (hC : (2:ℝ)^K ≤ l^2) (hK : (K:ℝ) ≤ l^2) (hH : (H:ℝ) ≤ l^2)
    (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (hp : ∀ E ∈ (range K).powerset, (p E:ℝ) ≤ Real.exp (l^3) ∧
      |s E| ≤ 8*(K:ℤ)^2*p E) :
    let C := (range K).powerset
    let S := C ×ˢ Ico (K+1) (K+H+1)
    let r (a : Finset ℕ × ℕ) : ℤ := (p a.1:ℤ)*a.2-s a.1
    let W := ∏ a ∈ S.offDiag, (r a.1-r a.2).natAbs
    W ≠ 0 →
      (((∏ E ∈ C, p E) * (∏ q ∈ W.primeFactors \ C.image p, q^W.factorization q) : ℕ):ℝ) ≤
        Real.exp (4*l^11) ∧
      (∀ E ∈ C, |(s E:ℝ)| ≤ Real.exp (4*l^11)) ∧
      ∀ a ∈ S, |(r a:ℝ)| ≤ Real.exp (4*l^11) := by
  classical
  intro C S r W hW
  have hl0 : 0 ≤ l := by linarith
  have grow {i j : ℕ} (hij : i ≤ j) : l^i ≤ l^j := pow_le_pow_right₀ (by linarith) hij
  have hP := Real.pow_div_factorial_le_exp (l^3) (pow_nonneg hl0 3) 2
  norm_num at hP
  have hl4 : 100*l^4 ≤ l^6 := by
    have hl2 : 100 ≤ l^2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hl2 (pow_nonneg hl0 4)]
  have hlocal : 2*l^2+8*l^4 ≤ Real.exp (l^3) := by
    nlinarith only [hP,hl4,grow (i:=2) (j:=4) (by decide),pow_nonneg hl0 4]
  have h2P : 2 ≤ Real.exp (l^3) := by
    nlinarith [Real.add_one_le_exp (l^3),grow (i:=1) (j:=3) (by decide)]
  have hK2 : (K:ℝ)^2 ≤ l^4 := by
    calc
      _ ≤ (l^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      _ = _ := by ring
  have hss (E) (he : E ∈ C) : |(s E:ℝ)| ≤ (8*l^4)*Real.exp (l^3) := by
    have orig : |(s E:ℝ)| ≤ 8*(K:ℝ)^2*(p E:ℝ) := by exact_mod_cast (hp E he).2
    exact orig.trans (mul_le_mul (by linarith : 8*(K:ℝ)^2 ≤ 8*l^4) (hp E he).1
      (Nat.cast_nonneg _) (by positivity))
  have hr (a) (ha : a ∈ S) : |(r a:ℝ)| ≤ Real.exp (2*l^3) := by
    obtain ⟨he,hh⟩ := mem_product.mp ha
    have hval : (a.2:ℝ) ≤ 2*l^2 := by
      have ha' : a.2 ≤ K+H := by have := (mem_Ico.mp hh).2; omega
      have h' : (a.2:ℝ) ≤ K+(H:ℝ) := by exact_mod_cast ha'
      linarith
    have hv := mul_le_mul hval (hp a.1 he).1 (Nat.cast_nonneg _) (by positivity)
    change |(((p a.1:ℤ)*(a.2:ℤ)-s a.1:ℤ):ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(p a.1:ℝ)*a.2| + |(s a.1:ℝ)| := abs_sub _ _
      _ ≤ (2*l^2+8*l^4)*Real.exp (l^3) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (p a.1:ℝ)*a.2)]
        nlinarith only [hv,hss a.1 he]
      _ ≤ Real.exp (l^3)*Real.exp (l^3) :=
        mul_le_mul_of_nonneg_right hlocal (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hc : (C.card:ℝ) ≤ l^2 := by simpa [C] using hC
  have hS : (S.card:ℝ) ≤ l^4 := by
    have z : S.card = C.card * H := by simp [S]
    rw [z,Nat.cast_mul]
    calc
      _ ≤ l^2*l^2 := mul_le_mul hc hH (Nat.cast_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hoff : (S.offDiag.card:ℝ) ≤ l^8 := by
    have hsub : S.offDiag ⊆ S ×ˢ S := fun a ha =>
      mem_product.mpr ⟨(mem_offDiag.mp ha).1,(mem_offDiag.mp ha).2.1⟩
    have h' : S.offDiag.card ≤ S.card*S.card := by simpa using card_le_card hsub
    have hh : (S.offDiag.card:ℝ) ≤ (S.card:ℝ)*S.card := by exact_mod_cast h'
    calc
      _ ≤ _ := hh
      _ ≤ l^4*l^4 := mul_le_mul hS hS (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hWle : (W:ℝ) ≤ Real.exp (3*l^11) := by
    dsimp only [W]
    push_cast
    calc
      _ ≤ ∏ _ ∈ S.offDiag, Real.exp (3*l^3) := by
        apply Finset.prod_le_prod
        · intros; positivity
        · intro a ha
          obtain ⟨h1,h2,_⟩ := mem_offDiag.mp ha
          have h' : |(r a.1:ℝ)-(r a.2:ℝ)| ≤ Real.exp (2*l^3)+Real.exp (2*l^3) :=
            (abs_sub _ _).trans (add_le_add (hr _ h1) (hr _ h2))
          have he : Real.exp (3*l^3) = Real.exp (l^3)*Real.exp (2*l^3) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [he]
          have := mul_le_mul_of_nonneg_right h2P (Real.exp_pos (2*l^3)).le
          simp only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] 
          linarith
      _ = Real.exp ((S.offDiag.card:ℝ)*(3*l^3)) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hoff (show 0 ≤ 3*l^3 by positivity)])
  have hPle : ((∏ E ∈ C, p E : ℕ):ℝ) ≤ Real.exp (l^11) := by
    push_cast
    calc
      _ ≤ ∏ _ ∈ C, Real.exp (l^3) := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun E he => (hp E he).1)
      _ = Real.exp ((C.card:ℝ)*l^3) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hl0 3),grow (i:=5) (j:=11) (by decide)])
  have hD : (∏ q ∈ W.primeFactors \ C.image p, q ^ W.factorization q) ≤ W := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hW)
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hW]
    exact prod_dvd_prod_of_subset _ _ _ sdiff_subset
  have hex : Real.exp (2*l^3) ≤ Real.exp (4*l^11) := Real.exp_le_exp.mpr (by
    nlinarith [grow (i:=3) (j:=11) (by decide),pow_nonneg hl0 11])
  refine ⟨?_,?_,fun a ha => (hr a ha).trans hex⟩
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (l^11) * Real.exp (3*l^11) := mul_le_mul hPle
        (le_trans (by exact_mod_cast hD) hWle) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro E he
    apply (hss E he).trans
    apply le_trans _ hex
    rw [show 2*l^3 = l^3+l^3 by ring,Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith [sq_nonneg l]




end Tail69

open Finset Filter
open scoped Classical
namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

/-- Compare the Fourier average of shifted prime-divisibility counts with the product of
their one-prime means. This is uniform over distinct residue classes and bounded total
weight. One can truncate the product expansion after a constant multiple of log log x
terms and count each resulting intersection by the Chinese remainder theorem. -/
def H1 : Prop :=
  let phase (t : ℝ) := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)
  ∀ q : ℕ, 0 < q → ∀ᶠ x : ℕ in atTop,
    let R := (x:ℝ)^(1/Real.log (Real.log x)^2)
    ∀ (Q b : ℕ) (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ)
      (w : Finset ℕ × ℕ → ℝ) (P : Finset ℕ),
      let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
      0 < Q → Real.sqrt x ≤ 8*(N.card:ℝ) →
      (∀ p ∈ P, p.Prime ∧ ¬p ∣ Q ∧ (p:ℝ) ≤ R) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ p ∈ P, ¬(p:ℤ) ∣ r a - r b) →
      (∑ a ∈ S, |w a|) ≤ 1 →
      ‖∑ n ∈ N, phase (q * ∑ a ∈ S, w a *
        ((P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r a).card : ℝ))‖ <
        (N.card:ℝ) * (‖∏ p ∈ P, (1 + (∑ a ∈ S, (phase (q * w a) - 1)) / (p:ℂ))‖ + 1/8)

/-- Decay of the independent product. The cube signs pair by parity, and the first
height already contributes a cosine deficit of order q²/2^K. Mertens' theorem supplies
enough reciprocal prime mass even after removing the primes dividing Q. -/
def H2 : Prop :=
  let phase (t : ℝ) := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)
  ∀ q : ℕ, 0 < q → ∀ᶠ x : ℕ in atTop,
    let l := Real.log (Real.log (Real.log x))
    let K := ⌊2*Real.log l / Real.log 2⌋₊
    let H := ⌊l^2⌋₊
    let R := (x:ℝ)^(1/Real.log (Real.log x)^2)
    let S := (range K).powerset ×ˢ Ico (K+1) (K+H+1)
    let w (a : Finset ℕ × ℕ) := (-1:ℝ)^a.1.card/2^a.2
    ∀ Q : ℕ, 0 < Q → (Q:ℝ) ≤ Real.exp (4*l^11) →
      let P := (range (⌊R⌋₊+1)).filter fun (p:ℕ) => p.Prime ∧ ¬p ∣ Q ∧ (p:ℝ) ≤ R
      ‖∏ p ∈ P, (1 + (∑ a ∈ S, (phase (q * w a) - 1)) / (p:ℂ))‖ ≤ 1/8

lemma phase_add (a b : ℝ) :
    Complex.exp ((2*Real.pi*(a+b) : ℝ)*Complex.I) =
      Complex.exp ((2*Real.pi*a : ℝ)*Complex.I) * Complex.exp ((2*Real.pi*b : ℝ)*Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_norm (a : ℝ) : ‖Complex.exp ((2*Real.pi*a : ℝ)*Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma phase_re (a : ℝ) : (Complex.exp ((2*Real.pi*a : ℝ)*Complex.I)).re = Real.cos (2*Real.pi*a) := by
  simp [Complex.exp_re]

lemma cos_near {t : ℝ} {z : ℤ} (h : |t-z| < 1/10) : 1/2 ≤ Real.cos (2*Real.pi*t) := by
  rw [← Real.cos_sub_int_mul_two_pi (2*Real.pi*t) z,
    show 2*Real.pi*t-z*(2*Real.pi)=2*Real.pi*(t-z) by ring,← Real.cos_abs,
    ← Real.cos_pi_div_three]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  nlinarith [mul_lt_mul_of_pos_left h Real.pi_pos,Real.pi_pos]

lemma far_set (N : Finset ℕ) (t : ℕ → ℝ)
    (h : ‖∑ n ∈ N, Complex.exp ((2*Real.pi*t n : ℝ)*Complex.I)‖ < (N.card:ℝ)/4) :
    ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ N ∧ (N.card:ℝ) ≤ 10*A.card ∧
      ∀ n ∈ A, ∀ z : ℤ, 1/10 ≤ |t n-z| := by
  classical
  let A := N.filter fun n => ∀ z : ℤ, 1/10 ≤ |t n-z|
  have sub : A ⊆ N := filter_subset _ _
  have lo (n) (hn : n ∈ N) : (if n ∈ A then (-1:ℝ) else 1/2) ≤ (Complex.exp ((2*Real.pi*t n : ℝ)*Complex.I)).re := by
    rw [phase_re]
    split_ifs with ha
    · exact Real.neg_one_le_cos _
    · have hn' : ¬∀ z : ℤ, 1/10 ≤ |t n-z| := fun hh => ha (mem_filter.mpr ⟨hn,hh⟩)
      push_neg at hn'
      obtain ⟨z,hz⟩ := hn'
      exact cos_near hz
  have hb := (sum_le_sum lo).trans (show (∑ n ∈ N, (Complex.exp ((2*Real.pi*t n : ℝ)*Complex.I)).re) ≤
    ‖∑ n ∈ N, Complex.exp ((2*Real.pi*t n : ℝ)*Complex.I)‖ by rw [← Complex.re_sum]; exact Complex.re_le_norm _)
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    show N.filter (fun n => n ∈ A) = A from filter_mem_eq_inter .. |>.trans
      (inter_eq_right.mpr sub),
    show N.filter (fun n => n ∉ A) = N \ A by ext; simp] at hb
  rw [card_sdiff_of_subset sub,Nat.cast_sub (card_le_card sub)] at hb
  have hcard : 0 < (A.card:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) N.card]
  exact ⟨A,card_pos.mp (by exact_mod_cast hcard),sub,by linarith,
    fun n hn => (mem_filter.mp hn).2⟩

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

open Finset
open scoped Classical
namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

lemma dvd_modulus {C : Finset (Finset ℕ)} {p : Finset ℕ → ℕ} {W Q u : ℕ} (hu : u.Prime)
    (hW : W ≠ 0) (hd : u ∣ W)
    (hQ : Q = (∏ E ∈ C, p E) * ∏ v ∈ W.primeFactors \ C.image p, v^W.factorization v) :
    u ∣ Q := by
  rw [hQ]
  by_cases hc : u ∈ C.image p
  · obtain ⟨E,hE,rfl⟩ := mem_image.mp hc
    exact dvd_mul_of_dvd_left (dvd_prod_of_mem p hE) _
  · have hv : u ∈ W.primeFactors \ C.image p := mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hu,hd,hW⟩,hc⟩
    exact dvd_mul_of_dvd_right ((dvd_pow_self _ (hu.factorization_pos_of_dvd hW hd).ne').trans
      (dvd_prod_of_mem (fun v => v^W.factorization v) hv)) _

lemma count_split (R : ℝ) (n b Q : ℕ) (r : ℤ) (hn : n ≡ b [MOD Q]) (hpos : (n:ℤ)+r ≠ 0) :
    let P := (range (⌊R⌋₊+1)).filter fun (p:ℕ) => p.Prime ∧ ¬p ∣ Q ∧ (p:ℝ) ≤ R
    let B := (range (⌊R⌋₊+1)).filter fun (p:ℕ) => p.Prime ∧ p ∣ Q ∧ (p:ℝ) ≤ R
    (((n:ℤ)+r).natAbs.primeFactors.filter fun (p:ℕ) => (p:ℝ) ≤ R).card =
      (B.filter fun (p:ℕ) => (p:ℤ) ∣ (b:ℤ)+r).card + (P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r).card := by
  classical
  intro P B
  let F := (((n:ℤ)+r).natAbs.primeFactors.filter fun (p:ℕ) => (p:ℝ) ≤ R)
  have memF (p : ℕ) : p ∈ F ↔ p.Prime ∧ (p:ℤ) ∣ (n:ℤ)+r ∧ (p:ℝ) ≤ R := by
    simp only [F,mem_filter,Nat.mem_primeFactors,Int.natCast_dvd,and_assoc]
    have hh : ((n:ℤ)+r).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hpos
    tauto
  have hB : F.filter (fun (p:ℕ) => p ∣ Q) = B.filter (fun (p:ℕ) => (p:ℤ) ∣ (b:ℤ)+r) := by
    ext p
    simp only [B,mem_filter,mem_range,memF]
    constructor
    · rintro ⟨⟨hp,hd,hR⟩,hQ⟩
      have he : (n:ℤ) ≡ b [ZMOD p] := Int.natCast_modEq_iff.mpr (hn.of_dvd hQ)
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hR),hp,hQ,hR⟩,(he.add_right r).dvd_iff.mp hd⟩
    · rintro ⟨⟨_,hp,hQ,hR⟩,hd⟩
      have he : (n:ℤ) ≡ b [ZMOD p] := Int.natCast_modEq_iff.mpr (hn.of_dvd hQ)
      exact ⟨⟨hp,(he.add_right r).dvd_iff.mpr hd,hR⟩,hQ⟩
  have hP : F.filter (fun (p:ℕ) => ¬p ∣ Q) = P.filter (fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r) := by
    ext p
    simp only [P,mem_filter,mem_range,memF]
    constructor
    · rintro ⟨⟨hp,hd,hR⟩,hQ⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hR),hp,hQ,hR⟩,hd⟩
    · rintro ⟨⟨_,hp,hQ,hR⟩,hd⟩
      exact ⟨⟨hp,hd,hR⟩,hQ⟩
  rw [← hB,← hP,card_filter_add_card_filter_not]

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

open Finset Filter
open scoped Classical
namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1
open OMA.R_Erdos69_erdos_69_R1_H1_R1 (geom_one geom_two sign_sum)

lemma weights (K H : ℕ) (hk : 0<K) :
    let S := (range K).powerset ×ˢ Ico (K+1) (K+H+1)
    let w (a : Finset ℕ × ℕ) := (-1:ℝ)^a.1.card/2^a.2
    (∑ i ∈ S, w i) = 0 ∧ (∑ i ∈ S, |w i|) ≤ 1 ∧
      (∑ i ∈ S, (w i)^2) ≤ 1/(3*2^K) := by
  classical
  dsimp only
  simp only [sum_product]
  constructor
  · rw [sum_comm]
    apply sum_eq_zero
    intro h _
    rw [← sum_div,sign_sum K hk,zero_div]
  constructor
  · rw [sum_comm]
    simp only [abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    simp only [sum_const,card_powerset,card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one_div]
    rw [geom_one]
    linarith [show (0:ℝ) ≤ 1/2^H by positivity]
  · rw [sum_comm]
    simp only [div_pow,← pow_mul,show ∀ c : ℕ, (-1:ℝ)^(c*2)=1 by
      intro c; rw [mul_comm,pow_mul]; norm_num]
    simp only [sum_const,card_powerset,card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one_div]
    simp_rw [pow_mul (2:ℝ) _ 2]
    rw [geom_two]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [show (0:ℝ) ≤ 1/(2^H:ℝ)^2 by positivity]



set_option maxHeartbeats 1400000 in
theorem main : H1 → H2 → OMA.R_Erdos69_erdos_69_R1_H1_R1.H2 := by
  classical
  let phase (v : ℝ) := Complex.exp ((2*Real.pi*v : ℝ)*Complex.I)
  intro compare decay q hq
  apply eventually_atTop.mp
  filter_upwards [compare q hq,decay q hq,Numeric69.growth 1] with x hcmp hdec hg
  let l := Real.log (Real.log (Real.log x))
  let D := Real.exp (4*l^11)
  let R := (x:ℝ)^(1/Real.log (Real.log x)^2)
  intro K H Q b p s
  dsimp only
  intro hK hH hs _ hW hQ _
  obtain ⟨hx,_,hl,_,hDx,hDh,_⟩ := hg
  have hpow := Numeric69.floor_power l hl
  dsimp only at hpow hdec hcmp
  rw [← hK] at hpow hdec
  rw [← hH] at hdec
  let C := (range K).powerset
  let S := C ×ˢ Ico (K+1) (K+H+1)
  let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
  let P := (range (⌊R⌋₊+1)).filter fun (u:ℕ) => u.Prime ∧ ¬u ∣ Q ∧ (u:ℝ) ≤ R
  let B := (range (⌊R⌋₊+1)).filter fun (u:ℕ) => u.Prime ∧ u ∣ Q ∧ (u:ℝ) ≤ R
  let r (a : Finset ℕ × ℕ) : ℤ := (p a.1:ℤ)*a.2 - s a.1
  let w (a : Finset ℕ × ℕ) := (-1:ℝ)^a.1.card/2^a.2
  let M := ∏ u ∈ P, (1 + (∑ a ∈ S, (phase (q * w a) - 1)) / (u:ℂ))
  let W := ∏ a ∈ S.offDiag, (r a.1-r a.2).natAbs
  change W ≠ 0 at hW
  have hQp : 0 < Q := by
    rw [hQ]
    exact Nat.mul_pos (prod_pos fun E he => (hs E he).1.pos)
      (prod_pos fun u hu => pow_pos (Nat.pos_of_mem_primeFactors (mem_sdiff.mp hu).1) _)
  have hKs : (K:ℝ) ≤ l^2 := le_trans (by exact_mod_cast K.lt_two_pow_self.le) hpow.2.1
  obtain ⟨hQD,_,hshift⟩ := Tail69.finite_bounds l hl K H hpow.2.1 hKs
    (show (H:ℝ) ≤ l^2 from hH ▸ Nat.floor_le (sq_nonneg l))
    p s (fun E he => ⟨(hs E he).2.2.1,(hs E he).2.2.2.1⟩) hW
  rw [← hQ] at hQD
  have hcard := Numeric69.prog_card x Q b hx hQp (hQD.trans hDx.le)
  have hdiff (i) (hi : i ∈ S) (j) (hj : j ∈ S) (hn : i ≠ j) (u) (hu : u ∈ P) :
      ¬ (u:ℤ) ∣ r i - r j := by
    obtain ⟨hprime,havoid,_⟩ := (mem_filter.mp hu).2
    intro hd
    have huW : u ∣ W := (Int.natCast_dvd.mp hd).trans
      (dvd_prod_of_mem (fun a : (Finset ℕ × ℕ) × (Finset ℕ × ℕ) =>
        (r a.1-r a.2).natAbs) (show (i,j) ∈ S.offDiag from mem_offDiag.mpr ⟨hi,hj,hn⟩))
    exact havoid (dvd_modulus hprime hW huW hQ)
  let t (n : ℕ) := (q:ℝ)*∑ a ∈ S, w a *
    ((((n:ℤ)+r a).natAbs.primeFactors.filter (fun u : ℕ => (u:ℝ) ≤ R)).card:ℝ)
  let f (n : ℕ) := (q:ℝ)*∑ a ∈ S, w a * ((P.filter fun (u:ℕ) => (u:ℤ) ∣ (n:ℤ)+r a).card:ℝ)
  let c := (q:ℝ)*∑ a ∈ S, w a * ((B.filter fun (u:ℕ) => (u:ℤ) ∣ (b:ℤ)+r a).card:ℝ)
  have hsplit (n : ℕ) (hn : n ∈ N) : t n = c + f n := by
    dsimp only [t,c,f]
    rw [← mul_add,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro a ha
    have hn' : ((x/2:ℕ):ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
    have hr : |(r a:ℝ)| ≤ D := hshift a ha
    have hpos : 0 < (n:ℝ)+(r a:ℝ) := by
      change D < ((x/2:ℕ):ℝ) at hDh
      linarith [neg_abs_le (r a:ℝ)]
    have hnz : (n:ℤ)+r a ≠ 0 := by exact_mod_cast hpos.ne'
    have hh := count_split R n b Q (r a) (mem_filter.mp hn).2 hnz
    rw [← mul_add,hh,Nat.cast_add]
  apply far_set N t
  have he : (∑ n ∈ N, phase (t n)) = phase c * ∑ n ∈ N, phase (f n) := by
    rw [mul_sum]
    exact sum_congr rfl fun n hn => by rw [hsplit n hn]; exact phase_add c (f n)
  change ‖∑ n ∈ N, phase (t n)‖ < _
  rw [he,norm_mul,show ‖phase c‖ = 1 from phase_norm c,one_mul]
  have hcomp := hcmp Q b S r w P hQp hcard (fun u hu => (mem_filter.mp hu).2)
    hdiff (weights K H hpow.1).2.1
  have hm : ‖M‖ ≤ 1/8 := hdec Q hQp hQD
  change ‖∑ n ∈ N, phase (f n)‖ < (N.card:ℝ)*(‖M‖+1/8) at hcomp
  exact hcomp.trans_le (by nlinarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α:=ℝ) N.card)])

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1

