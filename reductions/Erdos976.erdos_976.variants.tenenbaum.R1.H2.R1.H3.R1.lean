import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
import Mathlib

/-! The polynomial-value sieve for Erdős 976. For weights with divisor-bounded
growth, a dyadic short-sum estimate on polynomials with no fixed prime divisor
is enough. Affine residue classes handle fixed divisors, an upper bound on the
prime product supplies one inverse logarithm, and a prefix-sum estimate gives
the result on the full interval.

The analytic short-sum input follows Nair and Tenenbaum, “Short sums of certain
arithmetic functions”, Acta Math. 180 (1998), Corollary 3. The affine
normalization is also formalized by Jason Davies in nair-tenenbaum-short-sums
at 9c3c9236a66f9ba1e04a237089ff836adde0cd6c. -/

open Polynomial Finset

namespace Erdos976Sieve

/-- Passing to the polynomial left after extracting the content on a residue class
costs at most the modulus of that class in each root count. -/
theorem affine_root_count (R Q : ℤ[X]) {M a : ℕ} (ha : a < M)
    (divides : ∀ u : ℕ, R.eval (u : ℤ) ∣ Q.eval ((a + M*u : ℕ) : ℤ)) (d : ℕ) :
    Nat.count (fun u : ℕ => (d : ℤ) ∣ R.eval (u : ℤ)) d ≤
      M * Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  have hdpos := Nat.pos_of_ne_zero hd
  simp only [Nat.count_eq_card_filter_range]
  rw [← card_range M, ← card_product]
  let key (u : ℕ) := ((a + M*u)/d, (a + M*u)%d)
  apply card_le_card_of_injOn key
  · intro u hu
    obtain ⟨hu, hr⟩ := mem_filter.mp hu
    have hul := mem_range.mp hu
    have hLt : a + M*u < M*d := calc
      a + M*u < M + M*u := by omega
      _ = M*(u+1) := by ring
      _ ≤ M*d := Nat.mul_le_mul_left _ hul
    let v := a + M*u
    have hmod : v % d ≡ v [MOD d] := Nat.mod_modEq _ _
    have hdiff := (Int.natCast_modEq_iff.mpr hmod).dvd
    have hEval := Int.modEq_of_dvd (hdiff.trans (sub_dvd_eval_sub (v:ℤ) (↑(v%d):ℤ) Q))
    exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hdpos).mpr hLt),
      mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hdpos), hEval.dvd_iff.mpr (hr.trans (divides u))⟩⟩
  · intro u _ v _ huv
    have quot : (a+M*u)/d = (a+M*v)/d := congrArg Prod.fst huv
    have rem : (a+M*u)%d = (a+M*v)%d := congrArg Prod.snd huv
    have eqv : a+M*u = a+M*v := by
      calc
        _ = (a+M*u)%d+d*((a+M*u)/d) := (Nat.mod_add_div _ _).symm
        _ = (a+M*v)%d+d*((a+M*v)/d) := by rw [quot, rem]
        _ = _ := Nat.mod_add_div _ _
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) (Nat.add_left_cancel eqv)

theorem affine_root_sum (R Q : ℤ[X]) {M a : ℕ} (ha : a < M)
    (divides : ∀ u : ℕ, R.eval (u : ℤ) ∣ Q.eval ((a + M*u : ℕ) : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    (∑ d ∈ Icc 1 N, (Nat.count (fun u : ℕ => (d : ℤ) ∣ R.eval (u : ℤ)) d : ℝ)*w d/d) ≤
      M * (∑ d ∈ Icc 1 N, (Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d : ℝ)*w d/d) := by
  rw [mul_sum]
  apply sum_le_sum
  intro d _
  have h := affine_root_count R Q ha divides d
  push_cast at *
  calc
    _ ≤ (((M:ℝ) * Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d) * w d / d) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (hw d)) (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos976Sieve

open Polynomial Finset Real Filter
namespace Erdos976Sieve

/-- Count each positive integer once in its affine residue class. The constant
term covers the initial quotient zero in each class. -/
theorem affine_prefix (f : ℤ[X]) {M : ℕ} (hM : 0 < M) (R : Fin M → ℤ[X]) (c : Fin M → ℤ)
    (affine : ∀ a : Fin M, ∀ u : ℕ, f.eval ((a.val + M*u : ℕ) : ℤ) = c a * (R a).eval (u : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {t : ℝ}
    (growth : ∀ a b : ℕ, w (a*b) ≤ w a * (b.divisors.card : ℝ)^t) (n : ℕ) :
    (∑ m ∈ Icc 1 n, w (f.eval (m:ℤ)).natAbs) ≤
      ∑ a : Fin M, (((c a).natAbs.divisors.card:ℝ)^t *
        (w ((R a).eval 0).natAbs + ∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs)) := by
  classical
  let index (m : ℕ) : Fin M × ℕ := (⟨m%M, Nat.mod_lt _ hM⟩, m/M)
  have hinj : Function.Injective index := by
    intro m k eqv
    have h₁ : m%M = k%M := congrArg (fun z : Fin M × ℕ => z.1.val) eqv
    have h₂ : m/M=k/M := congrArg Prod.snd eqv
    simpa only [h₁, h₂, Nat.mod_add_div] using (Nat.mod_add_div m M).symm
  let weight (p : Fin M × ℕ) := ((c p.1).natAbs.divisors.card:ℝ)^t *
    w ((R p.1).eval (p.2:ℤ)).natAbs
  let T := (univ : Finset (Fin M)) ×ˢ insert 0 (Icc 1 n)
  have hsub : (Icc 1 n).image index ⊆ T := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have hle : m/M ≤ n := (Nat.div_le_self ..).trans (mem_Icc.mp hm).2
    exact mem_product.mpr ⟨mem_univ _,mem_insert.mpr (by
      change m/M = 0 ∨ m/M ∈ Icc 1 n
      by_cases h : m/M = 0
      · exact Or.inl h
      · exact Or.inr (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, hle⟩))⟩
  calc
    _ ≤ ∑ m ∈ Icc 1 n, weight (index m) := by
      apply sum_le_sum
      intro m _
      have h := affine (index m).1 (m/M)
      simp only [index, Nat.mod_add_div] at h
      rw [h, Int.natAbs_mul, Nat.mul_comm]
      simpa only [weight, mul_comm] using (growth ((R (index m).1).eval (↑(m/M):ℤ)).natAbs (c (index m).1).natAbs)
    _ = ∑ p ∈ (Icc 1 n).image index, weight p := (sum_image (fun _ _ _ _ e => hinj e)).symm
    _ ≤ ∑ p ∈ T, weight p := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hw _))
    _ = _ := by
      rw [show T = _ from rfl, sum_product]
      apply sum_congr rfl
      intro a _
      rw [sum_insert (by simp), mul_add, mul_sum]
      rfl

end Erdos976Sieve

open Polynomial Finset Real Filter
namespace Erdos976Sieve

/-- Long-prefix estimates for primitive parts on finitely many progressions
give the original estimate, even when the weight vanishes on some integers. -/
theorem affine_long (f : ℤ[X]) {M : ℕ} (hM : 0 < M) (R : Fin M → ℤ[X]) (c : Fin M → ℤ)
    (affine : ∀ a : Fin M, ∀ u : ℕ, f.eval ((a.val + M*u : ℕ) : ℤ) = c a * (R a).eval (u : ℤ))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {t : ℝ}
    (growth : ∀ a b : ℕ, w (a*b) ≤ w a * (b.divisors.card : ℝ)^t) :
    let H (Q : ℤ[X]) (n : ℕ) := ∑ d ∈ Icc 1 n,
      (Nat.count (fun u : ℕ => (d : ℤ) ∣ Q.eval (u : ℤ)) d : ℝ)*w d/d
    (∀ a : Fin M, ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs) ≤ B*((n:ℝ)/log n)*H (R a) n) →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Icc 1 n, w (f.eval (u:ℤ)).natAbs) ≤ B*((n:ℝ)/log n)*H f n := by
  intro H rows
  classical
  choose B Bpos bounds using rows
  let s (a : Fin M) := ((c a).natAbs.divisors.card:ℝ)^t
  let z (a : Fin M) := (((R a).eval 0).natAbs.divisors.card:ℝ)^t
  let K := ∑ a : Fin M, s a * (z a + B a * M)
  have hs a : 0 ≤ s a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz a : 0 ≤ z a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK : 0 ≤ K := sum_nonneg (fun a _ => mul_nonneg (hs a) (add_nonneg (hz a)
    (mul_nonneg (Bpos a).le (Nat.cast_nonneg M))))
  refine ⟨K+1, by linarith, ?_⟩
  filter_upwards [eventually_all.mpr bounds, eventually_ge_atTop 2] with n hrow hn
  have logpos : 0 < log n := Real.log_pos (by exact_mod_cast (show 1< n by omega))
  let x : ℝ := n / log n
  have hx : 1 ≤ x := (one_le_div logpos).mpr (Real.log_le_self (Nat.cast_nonneg _))
  have Hnonneg : 0 ≤ H f n := by dsimp only [H]; exact sum_nonneg (fun i _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  have Hbase : w 1 ≤ H f n := by
    have h1 : (1:ℕ) ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl,by omega⟩
    have h := single_le_sum (f := fun d : ℕ =>
      (Nat.count (fun u : ℕ => (d:ℤ) ∣ f.eval (u:ℤ)) d : ℝ)*w d/d)
      (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _)) h1
    simpa [Nat.count_succ, H] using h
  have hscale : H f n ≤ x*H f n := le_mul_of_one_le_left Hnonneg hx
  have zeroTerm (a : Fin M) : w ((R a).eval 0).natAbs ≤ z a*(x*H f n) := by
    have hzero : w ((R a).eval 0).natAbs ≤ w 1*z a := by
      simpa [z] using (growth 1 ((R a).eval 0).natAbs)
    refine hzero.trans ?_
    rw [mul_comm (w 1)]
    exact mul_le_mul_of_nonneg_left (Hbase.trans hscale) (hz a)
  have term (a : Fin M) : w ((R a).eval 0).natAbs + (∑ u ∈ Icc 1 n, w ((R a).eval (u:ℤ)).natAbs)
        ≤ (z a+B a*M)*(x*H f n) := by
    have root : H (R a) n ≤ (M:ℝ)*H f n := affine_root_sum _ _ a.isLt (fun u =>
      (affine a u).symm ▸ dvd_mul_left _ _) w hw n
    have rest := (hrow a).trans (mul_le_mul_of_nonneg_left root (mul_nonneg (Bpos a).le (le_trans zero_le_one hx)))
    calc
      _ ≤ z a*(x*H f n)+ B a*x*((M:ℝ)*H f n) := add_le_add (zeroTerm a) rest
      _ = _ := by ring
  calc
    _ ≤ _ := affine_prefix f hM R c affine w hw growth n
    _ ≤ ∑ a : Fin M, s a * ((z a+B a*M)*(x*H f n)) :=
      sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (term a) (hs a))
    _ = K*(x*H f n) := by simp only [K, sum_mul, mul_assoc]
    _ ≤ (K+1)*(x*H f n) := mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (le_trans zero_le_one hx) Hnonneg)
    _ = _ := by ring

end Erdos976Sieve

namespace TenenbaumDirect
open Finset Real Filter

/-- A half-interval estimate with the factor n / log n sums with uniform
constant on a prefix, for any nondecreasing positive cumulative weight. -/
theorem log_prefix (F H : ℕ → ℝ) (mono : Monotone H) (pos : 0 < H 1)
    (band : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      F n - F (n/2) ≤ c * ((n:ℝ)/log n) * H n) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      F n ≤ B * ((n:ℝ)/log n) * H n := by
  obtain ⟨c,cp,localbound⟩ := band
  obtain ⟨N,hN⟩ := eventually_atTop.mp localbound
  let T := N+24
  let D := ∑ i ∈ range (T+1),max (F i) 0
  have D0 : 0 ≤ D := sum_nonneg (fun i _ => le_max_right _ _)
  have start (n : ℕ) (small : n ≤ T) : F n ≤ D :=
    (le_max_left _ _).trans (single_le_sum (f:=fun i => max (F i) 0)
      (fun i _ => le_max_right _ _) (mem_range.mpr (by omega : n< T+1)))
  have bound (n : ℕ) (two : 2≤ n) : F n ≤ D+4*c*((n:ℝ)/log n)*H n := by
    induction n using Nat.strong_induction_on with | h n ih =>
    have hn : 0 < H n := pos.trans_le (mono (by omega))
    have logpos : 0< log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1< n))
    by_cases small : n≤ T
    · exact (start n small).trans (le_add_of_nonneg_right (by positivity))
    let m := n/2
    have large : N+24< n := Nat.lt_of_not_ge small
    have data : 9≤ m ∧ m< n ∧ 2*m≤ n ∧ n≤3*m := by dsimp [m];omega
    obtain ⟨m9,mn,mhalf,nt⟩ := data
    have mh : 0< H m := pos.trans_le (mono (by omega))
    have ml : 0< log (m:ℝ) := log_pos (by exact_mod_cast (by omega : 1< m))
    have three_le : log (9:ℝ) ≤ log (m:ℝ) := log_le_log (by norm_num) (by exact_mod_cast m9)
    have twice : log (9:ℝ) = 2*log (3:ℝ) := by rw [show (9:ℝ)=3*3 by norm_num,log_mul (by norm_num) (by norm_num)]; ring
    have high := log_le_log (show 0<(n:ℝ) by positivity) (show (n:ℝ)≤3*(m:ℝ) by exact_mod_cast nt)
    rw [log_mul (by norm_num) (ne_of_gt (show 0<(m:ℝ) by positivity))] at high
    have qlog : 2*log (n:ℝ) ≤ 3*log (m:ℝ) := by linarith
    have half : 2*(m:ℝ) ≤ n := by exact_mod_cast mhalf
    have ratio : 4*((m:ℝ)/log m) ≤ 3*((n:ℝ)/log n) := by
      field_simp [ml.ne',logpos.ne']
      nlinarith [mul_le_mul_of_nonneg_left qlog (show 0≤2*(m:ℝ) by positivity),
        mul_le_mul_of_nonneg_right half ml.le]
    have lt := mul_le_mul_of_nonneg_right ratio mh.le
    have hi := mul_le_mul_of_nonneg_left (mono mn.le) (show 0≤3*((n:ℝ)/log n) by positivity)
    have fine := mul_le_mul_of_nonneg_left (lt.trans hi) cp.le
    have prev := ih m mn (by omega)
    have lastBand := hN n (by omega)
    change F n - F m ≤ _ at lastBand
    linarith
  refine ⟨D/H 1+4*c,by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n n2
  have logpos : 0< log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1< n))
  have nb : 1 ≤ (n:ℝ)/log n := (one_le_div logpos).mpr (by linarith [log_le_sub_one_of_pos (show 0<(n:ℝ) by positivity)])
  have HH := mono (show 1≤ n by omega)
  have bb := mul_le_mul_of_nonneg_left ((show H 1≤((n:ℝ)/log n)*H n from
    HH.trans (le_mul_of_one_le_left (pos.le.trans HH) nb))) (show 0≤ D/H 1 by positivity)
  have e : D/H 1 * H 1 = D := div_mul_cancel₀ _ pos.ne'
  linarith [bound n n2]

end TenenbaumDirect

namespace OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1_H3_R1
open Finset Real Filter Polynomial

/-- The single-polynomial short-sum sieve on a half interval, for polynomials
with no fixed prime divisor (Nair–Tenenbaum, Corollary 3, with k=1). -/
def H1 : Prop :=
  let roots (Q : ℤ[X]) (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  ∀ Q : ℤ[X], Irreducible Q → 2 ≤ Q.natDegree → (∀ p : ℕ, p.Prime → roots Q p < p) →
    ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) →
    (∀ a b : ℕ, w (a*b) ≤ w a*(b.divisors.card:ℝ)^(3/2:ℝ)) →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ Ioc (n/2) n, w (Q.eval (u:ℤ)).natAbs) ≤
        C*n*(∏ p ∈ (Icc 1 (n/2)).filter Nat.Prime, (1-(roots Q p:ℝ)/p))*
          (∑ d ∈ Icc 1 n, (roots Q d:ℝ)*w d/d)

/-- Finitely many affine residue classes remove every fixed prime divisor while
preserving the degree and irreducibility of each primitive part. -/
def H2 : Prop :=
  let roots (Q : ℤ[X]) (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  ∀ f : ℤ[X], Irreducible f → 2 ≤ f.natDegree →
    ∃ M : ℕ, 0 < M ∧ ∃ R : Fin M → ℤ[X], ∃ c : Fin M → ℤ, ∀ a : Fin M,
      Irreducible (R a) ∧ 2 ≤ (R a).natDegree ∧ (∀ p : ℕ, p.Prime → roots (R a) p < p) ∧
      ∀ u : ℕ, f.eval ((a.val+M*u:ℕ):ℤ) = c a*(R a).eval (u:ℤ)

/-- For an irreducible polynomial, its polynomial root densities remove one
logarithm from the prime product. -/
def H3 : Prop :=
  let roots (Q : ℤ[X]) (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  ∀ Q : ℤ[X], Irreducible Q → 2 ≤ Q.natDegree →
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      (∏ p ∈ (Icc 1 (n/2)).filter Nat.Prime, (1-(roots Q p:ℝ)/p)) ≤ A/log n

theorem main : H1 → H2 → H3 → OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1.H3 := by
  intro short normalize product f hirr hdeg w hw growth
  classical
  obtain ⟨M,hM,R,c,good⟩ := normalize f hirr hdeg
  apply Erdos976Sieve.affine_long f hM R c (fun a => (good a).2.2.2) w hw growth
  intro a
  obtain ⟨hR,hdegR,hfix,_⟩ := good a
  let Q := R a
  let ρ (d : ℕ) := Nat.count (fun u : ℕ => (d:ℤ) ∣ Q.eval (u:ℤ)) d
  let H (n : ℕ) := ∑ d ∈ Icc 1 n, (ρ d:ℝ)*w d/d
  let F (n : ℕ) := ∑ u ∈ Icc 1 n, w (Q.eval (u:ℤ)).natAbs
  change ∃ B : ℝ, 0< B ∧ ∀ᶠ n : ℕ in atTop, F n ≤ B*((n:ℝ)/log n)*H n
  by_cases h0 : w 1 = 0
  · have hz (b : ℕ) : w b = 0 := le_antisymm (by simpa [h0] using growth 1 b) (hw b)
    exact ⟨1,zero_lt_one,Eventually.of_forall (by simp [F,H,hz])⟩
  apply TenenbaumDirect.log_prefix F H
  · intro n k hnk
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hnk) (fun d _ _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  · simpa [H,ρ,Nat.count_succ] using lt_of_le_of_ne (hw 1) (Ne.symm h0)
  obtain ⟨C,hC,hshort⟩ := short Q hR hdegR hfix w hw growth
  obtain ⟨A,hA,hprod⟩ := product Q hR hdegR
  refine ⟨C*A,mul_pos hC hA,?_⟩
  filter_upwards [hshort,hprod] with n hS hP
  have hpart : Icc 1 n = Icc 1 (n/2) ∪ Ioc (n/2) n := by
    ext i
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have hdis : Disjoint (Icc 1 (n/2)) (Ioc (n/2) n) := disjoint_left.mpr (by
    intro i hi hj
    exact (not_lt_of_ge (mem_Icc.mp hi).2) (mem_Ioc.mp hj).1)
  have hex : F n-F (n/2) = ∑ u ∈ Ioc (n/2) n, w (Q.eval (u:ℤ)).natAbs := by
    dsimp only [F]
    rw [hpart, sum_union hdis, add_sub_cancel_left]
  have hnn : 0 ≤ H n := sum_nonneg (fun d _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _)) (Nat.cast_nonneg _))
  rw [hex]
  apply hS.trans
  calc
    _ ≤ (C*n*(A/log n))*H n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (mul_nonneg hC.le (Nat.cast_nonneg _))) hnn
    _ = _ := by ring

end OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1_H3_R1
