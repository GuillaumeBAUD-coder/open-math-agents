import OMAReductions.R_Erdos345_erdos_345_R1
import Mathlib

/-! A finite averaging reduction following the mathematical argument of Kai
(Steve) Fan and Paul Pollack, arXiv:2510.14167, Theorem 1.1, Section 3.
For an admissible triple (d,a,p), the label a(p−1)/d gives a multiple
of k containing the shifted prime. Coprimality makes the count exact
within a label. The two inputs isolate the progression estimate and
rounding in the coprime multiplier count. -/

namespace OMA.R_Erdos345_erdos_345_R1_H1_R1

open Finset Filter

theorem recover_cofactor {s d a : ℕ} (hd : d ∣ s) (ha : a.Coprime d) :
    (a * (s / d)).gcd s = s / d := by
  have h : d * (s/d) = s := by rw [mul_comm, Nat.div_mul_cancel hd]
  calc
    _ = (a * (s/d)).gcd (d * (s/d)) := by rw [h]
    _ = _ := by simp [Nat.gcd_mul_right, ha.gcd_eq_one]

theorem equal_labels {s a b d e : ℕ} (hs : 0 < s)
    (hd : d ∣ s) (he : e ∣ s) (ha : a.Coprime d) (hb : b.Coprime e)
    (hab : a*(s/d) = b*(s/e)) : d = e ∧ a = b := by
  have hq : s/d = s/e := by
    rw [← recover_cofactor hd ha, ← recover_cofactor he hb, hab]
  have pos := Nat.div_pos (Nat.le_of_dvd hs hd) (Nat.pos_of_dvd_of_pos hd hs)
  have hdq : d * (s/d) = s := by rw [mul_comm, Nat.div_mul_cancel hd]
  have heq : e * (s/e) = s := by rw [mul_comm, Nat.div_mul_cancel he]
  rw [← hq] at heq hab
  exact ⟨Nat.eq_of_mul_eq_mul_right pos (hdq.trans heq.symm),
    Nat.eq_of_mul_eq_mul_right pos hab⟩

/-- Count the primes by the multiplier t=a(p−1)/d. With gcd(a,d)=1,
    a prime occurs at most once in each bucket, even across different moduli. -/
theorem prime_fibers (k T m : ℕ) (D : Finset ℕ) (C P : ℕ → Finset ℕ)
    (hd : ∀ d ∈ D, d ∣ k)
    (hc : ∀ d ∈ D, ∀ a ∈ C d, 0 < a ∧ a.Coprime d)
    (hp : ∀ d ∈ D, ∀ p ∈ P d, Nat.Prime p ∧ d ∣ p-1)
    (bound : ∀ d ∈ D, ∀ a ∈ C d, ∀ p ∈ P d, a*((p-1)/d) ≤ T)
    (mass : T*m < ∑ d ∈ D, (C d).card * (P d).card) :
    ∃ t ∈ Icc 1 T, ∃ S : Finset ℕ,
      (∀ p ∈ S, Nat.Prime p ∧ p-1 ∣ k*t) ∧ m < S.card := by
  classical
  let W := D.sigma (fun d => (C d) ×ˢ (P d))
  let bucket : (Σ _ : ℕ, ℕ × ℕ) → ℕ := fun v => v.2.1*((v.2.2-1)/v.1)
  let prime : (Σ _ : ℕ, ℕ × ℕ) → ℕ := fun v => v.2.2
  have unpack {d a p : ℕ} (h : ⟨d,(a,p)⟩ ∈ W) : d ∈ D ∧ a ∈ C d ∧ p ∈ P d :=
    ⟨(mem_sigma.mp h).1, mem_product.mp (mem_sigma.mp h).2⟩
  have maps : ∀ v ∈ W, bucket v ∈ Icc 1 T := by
    rintro ⟨d,a,p⟩ h
    obtain ⟨hD,hA,hP⟩ := unpack h
    obtain ⟨hpr,dv⟩ := hp d hD p hP
    have hs : 0 < p-1 := by have := hpr.two_le; omega
    have hq := Nat.div_pos (Nat.le_of_dvd hs dv) (Nat.pos_of_dvd_of_pos dv hs)
    exact mem_Icc.mpr ⟨Nat.mul_pos (hc d hD a hA).1 hq, bound d hD a hA p hP⟩
  have count : (Icc 1 T).card * m < W.card := by
    simpa [W, card_sigma, Nat.card_Icc] using mass
  obtain ⟨t, ht, htcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps count
  let F := W.filter (fun v => bucket v = t)
  have injective : Set.InjOn prime F := by
    rintro ⟨d,a,p⟩ hx ⟨e,b,q⟩ hy heq
    change p = q at heq
    subst q
    obtain ⟨hx,hxt⟩ := mem_filter.mp hx
    obtain ⟨hy,hyt⟩ := mem_filter.mp hy
    obtain ⟨hD,hA,hP⟩ := unpack hx
    obtain ⟨hE,hB,hQ⟩ := unpack hy
    obtain ⟨hpr,dv⟩ := hp d hD p hP
    have hs : 0 < p-1 := by have := hpr.two_le; omega
    obtain ⟨rfl,rfl⟩ := equal_labels hs dv (hp e hE p hQ).2
      (hc d hD a hA).2 (hc e hE b hB).2 (hxt.trans hyt.symm)
    rfl
  refine ⟨t,ht,F.image prime,?_,by simpa [card_image_of_injOn injective] using htcard⟩
  intro p h
  obtain ⟨⟨d,a,p⟩,hv,rfl⟩ := mem_image.mp h
  obtain ⟨hv,htv⟩ := mem_filter.mp hv
  obtain ⟨hD,hA,hP⟩ := unpack hv
  obtain ⟨hpr,dv⟩ := hp d hD p hP
  refine ⟨hpr,?_⟩
  change p-1 ∣ k*t
  obtain ⟨u, hku⟩ := hd d hD
  refine ⟨u*a, ?_⟩
  have hmul := Nat.div_mul_cancel dv
  change a*((p-1)/d) = t at htv
  calc
    k*t = ((p-1)/d*d)*(u*a) := by rw [hku, ← htv]; ring
    _ = (p-1)*(u*a) := by rw [hmul]


theorem large_log_ratio : ∀ᶠ n : ℕ in atTop,
    (128 : ℝ) ≤ Real.log n / Real.log (Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1/128))
  filter_upwards [hlog.eventually_ge_atTop 2, hlog.eventually hsmall] with n hn hs
  have hpos : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
  change ‖Real.log (Real.log n)‖ ≤ (1 / 128 : ℝ) * ‖Real.log n‖ at hs
  rw [Real.norm_eq_abs, abs_of_pos hpos, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hs
  exact (le_div_iff₀ hpos).mpr (by linarith)

theorem round_bound (t : ℝ) (ht : 128 ≤ t) :
    ((8 * (1 + ⌊Real.exp ((17 / 40 : ℝ) * t)⌋₊) : ℕ) : ℝ) ≤
      Real.exp ((9 / 20 : ℝ) * t) := by
  let a : ℝ := 17 / 40
  let c : ℝ := 9 / 20
  have hgap : 1 / 40 ≤ c - a := by
    norm_num [a, c]
  have hlog : Real.log 16 ≤ (c - a) * t := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num1
    have hmul := mul_le_mul_of_nonneg_right hgap (by linarith : 0 ≤ t)
    linarith only [Real.log_two_lt_d9, ht, hmul]
  have hg : (16 : ℝ) ≤ Real.exp ((c-a)*t) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 16)]
    exact Real.exp_le_exp.mpr hlog
  have hzero : 0 ≤ a*t := by dsimp [a]; linarith
  have hone : 1 ≤ Real.exp (a*t) := Real.one_le_exp hzero
  have hfloor := Nat.floor_le (Real.exp_pos (a*t)).le
  change ((8 * (1 + ⌊Real.exp (a*t)⌋₊) : ℕ) : ℝ) ≤ Real.exp (c*t)
  push_cast
  calc
    _ ≤ 16 * Real.exp (a*t) := by linarith
    _ ≤ Real.exp ((c-a)*t) * Real.exp (a*t) :=
      mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
    _ = Real.exp (c*t) := by rw [← Real.exp_add]; ring_nf

/-- A weighted prime-counting estimate on divisors of a common modulus.
For d in D, the loss of one per divisor accounts for rounding the coprime
multiplier count. The progression has residue 1 modulo d. Fan and Pollack,
Theorem 1.1 and its proof in Section 3, give an exponent exceeding 9/20. -/
def H1 : Prop :=
  ∀ B : ℕ, ∃ k x T m : ℕ, ∃ D : Finset ℕ, ∃ A : ℕ → ℕ,
    B ≤ k ∧ (∀ d ∈ D, 0 < d ∧ d ∣ k ∧ A d * x ≤ T * d) ∧
    Real.exp ((9/20 : ℝ) * Real.log (k*T : ℕ) / Real.log (Real.log k)) ≤ (m : ℝ) ∧
    T*m < ∑ d ∈ D, (A d * d.totient / d - d.divisors.card) *
      ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card

/-- The interval count of positive integers coprime to d has absolute
error at most the number of divisors of d. Only the lower side is needed. -/
def H2 : Prop :=
  ∀ d M : ℕ, 0 < d → M * d.totient / d - d.divisors.card ≤
    ((Icc 1 M).filter (fun a => a.Coprime d)).card

theorem main : H1 → H2 → OMA.R_Erdos345_erdos_345_R1.H1 := by
  intro hmass hcop B
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (large_log_ratio.and (hlog.eventually_ge_atTop 2))
  obtain ⟨k,x,T,m,D,A,hk,hd,hex,hm⟩ := hmass (max 1 (max B N))
  have hk1 : 1 ≤ k := (le_max_left ..).trans hk
  have hkB : B ≤ k := (le_max_left B N).trans ((le_max_right ..).trans hk)
  have hkN : N ≤ k := (le_max_right B N).trans ((le_max_right ..).trans hk)
  let C := fun d => (Icc 1 (A d)).filter (fun a => a.Coprime d)
  let P := fun d => (Nat.primesLE x).filter (fun p => d ∣ p-1)
  have prog (d p : ℕ) (h : p ∈ P d) : Nat.Prime p ∧ p ≤ x ∧ d ∣ p-1 := by
    obtain ⟨hp, hdiv⟩ := mem_filter.mp h
    obtain ⟨hle, hpr⟩ := mem_filter.mp hp
    exact ⟨hpr, Nat.le_of_lt_succ (mem_range.mp hle), hdiv⟩
  have cap (d : ℕ) (hD : d ∈ D) (a : ℕ) (hA : a ∈ C d) (p : ℕ) (hP : p ∈ P d) :
      a * ((p-1)/d) ≤ T := by
    have ha := (mem_Icc.mp (mem_filter.mp hA).1).2
    obtain ⟨_,hpx,hdiv⟩ := prog d p hP
    apply Nat.le_of_mul_le_mul_right _ (hd d hD).1
    calc
      a * ((p-1)/d) * d = a * (p-1) := by rw [Nat.mul_assoc, Nat.div_mul_cancel hdiv]
      _ ≤ A d * x := Nat.mul_le_mul ha (by omega)
      _ ≤ T*d := (hd d hD).2.2
  have mass : T*m < ∑ d ∈ D, (C d).card * (P d).card :=
    hm.trans_le (sum_le_sum fun d hD =>
      Nat.mul_le_mul_right (P d).card (hcop d (A d) (hd d hD).1))
  obtain ⟨t,ht,S,hS,hcard⟩ := prime_fibers k T m D C P (fun d hD => (hd d hD).2.1)
    (fun _ _ _ hA => ⟨(mem_Icc.mp (mem_filter.mp hA).1).1, (mem_filter.mp hA).2⟩)
    (fun d _ p hp => ⟨(prog d p hp).1, (prog d p hp).2.2⟩) cap mass
  obtain ⟨ht1,htT⟩ := mem_Icc.mp ht
  have lower : k ≤ k*t := by simpa using Nat.mul_le_mul_left k ht1
  have upper : k*t ≤ k*T := Nat.mul_le_mul_left k htT
  have lpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have lower' : (k : ℝ) ≤ (k*t : ℕ) := by exact_mod_cast lower
  have upper' : ((k*t : ℕ) : ℝ) ≤ (k*T : ℕ) := by exact_mod_cast upper
  have hklog := (hN k hkN).2
  have hloglo := Real.log_le_log lpos lower'
  have hloghi := Real.log_le_log (lt_of_lt_of_le lpos lower') upper'
  have hll := Real.log_le_log (show 0 < Real.log k by linarith) hloglo
  have hllp : 0 < Real.log (Real.log k) := Real.log_pos (by linarith)
  have ratio : Real.log (k*t : ℕ) / Real.log (Real.log (k*t : ℕ)) ≤
      Real.log (k*T : ℕ) / Real.log (Real.log k) :=
    (div_le_div_of_nonneg_left (by linarith) hllp hll).trans
      (div_le_div_of_nonneg_right hloghi hllp.le)
  refine ⟨k*t, hkB.trans lower, S, hS, ?_⟩
  have hr := round_bound _ (hN (k*t) (hkN.trans lower)).1
  have step := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ratio (by norm_num : (0 : ℝ) ≤ 9/20))
  simp only [mul_div_assoc] at hex ⊢
  exact_mod_cast ((hr.trans step).trans hex).trans (by exact_mod_cast hcard.le : (m : ℝ) ≤ S.card)

end OMA.R_Erdos345_erdos_345_R1_H1_R1
