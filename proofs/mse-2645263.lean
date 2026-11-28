import OMAStatements.S_mse_2645263

/-!
At `n = 3` the exponent is `223092870 / 29`. We enclose
`exp (223092870 / 58)` strictly between `N + 1/2` and `N + 1`
for an integer `N ≥ 2`. The floor of its square lies between
consecutive squares.

The enclosure starts with a Taylor sum evaluated by binary splitting
at an argument less than one. Twenty-two outward-rounded squarings
then give the desired interval. The endpoint computations use exact
natural-number arithmetic with a fixed power-of-two denominator.
-/

namespace OMA.S_mse_2645263
open Nat

private def exponentNum : ℕ := 223092870

private def smallDen : ℕ := 243269632

private structure Segment where
  ratioNum : ℕ
  denom : ℕ
  sumNum : ℕ

private def combine (a b : Segment) : Segment :=
  ⟨a.ratioNum * b.ratioNum, a.denom * b.denom,
   a.sumNum * b.denom + a.ratioNum * b.sumNum⟩

private def segment : ℕ → ℕ → Segment
  | 0, start =>
      let den := smallDen * (start + 1)
      ⟨exponentNum, den, den⟩
  | depth + 1, start => combine (segment depth start) (segment depth (start + 2^depth))

private def powTwoDigits : List ℕ → ℕ
  | [] => 1
  | d :: ds =>
      let q := powTwoDigits ds
      2^d * (q*q)

private def precisionBits : ℕ := 5750000

private def scale : ℕ := powTwoDigits (Nat.digits 2 precisionBits)

private def initBoundsFrom (d : ℕ) (t : Segment) : ℕ × ℕ :=
  let lower := d * t.sumNum / t.denom
  (lower, lower+2)

private def baseInterval : ℕ × ℕ := initBoundsFrom scale (segment 19 0)

private def oneSquare (d : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1*p.1/d, p.2*p.2/d+1)

private def squareIntervalFrom (d : ℕ) (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => p
  | s+1 => oneSquare d (squareIntervalFrom d p s)

private def squareInterval : ℕ → ℕ × ℕ := squareIntervalFrom scale baseInterval

private def numericalCertificate : Prop :=
  let pair := squareInterval 22
  let lower := pair.1
  let upper := pair.2
  lower / scale = upper / scale ∧
  2 ≤ lower / scale ∧
  scale < 2 * (lower % scale)

private instance : Decidable numericalCertificate := inferInstanceAs
  (Decidable ((squareInterval 22).1 / scale = (squareInterval 22).2 / scale ∧
   2 ≤ (squareInterval 22).1 / scale ∧
   scale < 2 * ((squareInterval 22).1 % scale)))

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 1000000 in
private theorem numerical_result : numericalCertificate := by decide +kernel


open Finset

private noncomputable def u : ℝ := (exponentNum : ℝ) / smallDen

private noncomputable def term (start i : ℕ) : ℝ := u / ((start + i + 1 : ℕ) : ℝ)

private noncomputable def weight (start length : ℕ) : ℝ := ∏ i ∈ range length, term start i

private noncomputable def sumTerms (start length : ℕ) : ℝ := ∑ i ∈ range length, weight start i

private theorem weight_split (start a b : ℕ) :
    weight start (a+b) = weight start a * weight (start+a) b := by
  simp only [weight, prod_range_add, term, Nat.add_assoc]

private theorem sumTerms_split (start a b : ℕ) :
    sumTerms start (a+b) = sumTerms start a + weight start a * sumTerms (start+a) b := by
  simp only [sumTerms, sum_range_add, mul_sum, weight_split]

private theorem weight_start (k : ℕ) : weight 0 k = u^k / (k.factorial : ℝ) := by
  induction k with
  | zero => simp [weight]
  | succ k ih =>
      simp only [weight, prod_range_succ] at ⊢
      change weight 0 k * term 0 k = _
      rw [ih, term, Nat.zero_add, Nat.factorial_succ, Nat.cast_mul, pow_succ, _root_.div_mul_div_comm]
      rw [mul_comm (k.factorial : ℝ)]

private theorem segment_denom_pos (depth start : ℕ) : 0 < (segment depth start).denom := by
  induction depth generalizing start with
  | zero => simpa [segment] using Nat.mul_pos (show 0 < smallDen by decide) (Nat.succ_pos start)
  | succ depth ih => exact Nat.mul_pos (ih start) (ih (start+2^depth))

private theorem segment_eval (depth start : ℕ) :
    ((segment depth start).ratioNum : ℝ) / (segment depth start).denom =
        weight start (2^depth) ∧
    ((segment depth start).sumNum : ℝ) / (segment depth start).denom =
        sumTerms start (2^depth) := by
  induction depth generalizing start with
  | zero =>
      have hden : 0 < (smallDen : ℝ) := by exact_mod_cast (show 0 < smallDen by decide)
      have hnext : (start : ℝ) + 1 ≠ 0 := by positivity
      constructor
      · simp [segment, weight, term, u, div_div]
      · simp [segment, sumTerms, weight, hden.ne', hnext]
  | succ depth ih =>
      let left := segment depth start
      let right := segment depth (start+2^depth)
      have hl : (left.denom : ℝ) ≠ 0 := by exact_mod_cast (segment_denom_pos depth start).ne'
      have hr : (right.denom : ℝ) ≠ 0 := by
        exact_mod_cast (segment_denom_pos depth (start+2^depth)).ne'
      have he : 2^(depth+1) = 2^depth+2^depth := by rw [pow_succ, Nat.mul_two]
      simp only [segment, he, weight_split, sumTerms_split]
      rw [← (ih start).1, ← (ih (start+2^depth)).1,
          ← (ih start).2, ← (ih (start+2^depth)).2]
      change ((combine left right).ratioNum : ℝ) / (combine left right).denom =
             (left.ratioNum / (left.denom : ℝ)) * (right.ratioNum / (right.denom : ℝ)) ∧
             ((combine left right).sumNum : ℝ) / (combine left right).denom =
             left.sumNum / (left.denom : ℝ) +
               (left.ratioNum / (left.denom : ℝ)) * (right.sumNum / (right.denom : ℝ))
      simp only [combine, Nat.cast_mul, Nat.cast_add]
      constructor
      · rw [_root_.div_mul_div_comm]
      · field_simp [hl, hr]

private theorem powTwoDigits_eq (ds : List ℕ) : powTwoDigits ds = 2^(Nat.ofDigits 2 ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [powTwoDigits, ih, Nat.ofDigits_cons, pow_add]
      rw [Nat.mul_comm 2 (Nat.ofDigits 2 ds), pow_mul, pow_two]

private theorem scale_eq : scale = 2^precisionBits := by
  simp only [scale, powTwoDigits_eq, Nat.ofDigits_digits]

private theorem scale_pos : 0 < (scale : ℝ) := by
  have hn : 0 < scale := scale_eq.symm ▸ Nat.two_pow_pos _
  exact Nat.cast_pos.mpr hn

private theorem floor_cast_bounds (v d : ℕ) (hd : 0<d) :
    (((v/d : ℕ) : ℝ) ≤ (v : ℝ)/d) ∧ (v : ℝ)/d < ((v/d : ℕ) : ℝ)+1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (div_lt_iff₀ hdr).2
  exact_mod_cast (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (v/d))

private theorem scaled_floor (v d : ℕ) (hd : 0 < (d : ℝ)) :
    ((v/d : ℕ) : ℝ)/(d : ℝ) ≤ (v : ℝ)/(d : ℝ)^2 ∧
      (v : ℝ)/(d : ℝ)^2 < (((v/d : ℕ) : ℝ)+1)/(d : ℝ) := by
  have h := floor_cast_bounds v d (by exact_mod_cast hd)
  rw [pow_two, ← div_div]
  exact ⟨div_le_div_of_nonneg_right h.1 hd.le, div_lt_div_of_pos_right h.2 hd⟩

private def seriesLength : ℕ := 2^19

private theorem length_pos : 0 < seriesLength := by exact Nat.two_pow_pos _

private theorem factorial_bound : 2*scale ≤ seriesLength.factorial := by
  have hm : (131071 : ℕ) + 393217 = seriesLength := by decide
  have ha : (131072 : ℕ)^393217 ≤ (131071+1).ascFactorial 393217 := by
    calc
      _ = ∏ _ ∈ range 393217, (131072 : ℕ) := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := by
        rw [Nat.ascFactorial_eq_prod_range]
        exact Finset.prod_le_prod' (fun i _ => Nat.le_add_right 131072 i)
  have hb : (2 : ℕ)^(precisionBits+1) ≤ (2 : ℕ)^(17*393217) := by
    exact Nat.pow_le_pow_right (by decide) (by decide)
  calc
    2*scale = 2*2^precisionBits := congrArg (2*·) scale_eq
    _ = 2^(precisionBits+1) := (pow_succ' 2 precisionBits).symm
    _ ≤ 2^(17*393217) := hb
    _ = 131072^393217 := pow_mul 2 17 393217
    _ ≤ (131071+1).ascFactorial 393217 := ha
    _ ≤ (131071 : ℕ).factorial * (131071+1).ascFactorial 393217 :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ = seriesLength.factorial := by rw [Nat.factorial_mul_ascFactorial, hm]

private theorem series_bound :
    sumTerms 0 seriesLength ≤ Real.exp u ∧
      Real.exp u ≤ sumTerms 0 seriesLength + 1/(scale : ℝ) := by
  have h0 : 0 ≤ u := by norm_num [u, exponentNum, smallDen]
  have h1 : u ≤ 1 := by norm_num [u, exponentNum, smallDen]
  simp only [sumTerms, weight_start]
  refine ⟨Real.sum_le_exp_of_nonneg h0 _, ?_⟩
  refine (Real.exp_bound' h0 h1 length_pos).trans (add_le_add_right ?_ _)
  have hw : u^seriesLength ≤ 1 := pow_le_one₀ h0 h1
  have hm : 1 ≤ (seriesLength : ℝ) := by exact_mod_cast length_pos
  have hf : 0 < (seriesLength.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfd : 2*(scale : ℝ) ≤ (seriesLength.factorial : ℝ) := by exact_mod_cast factorial_bound
  calc
    _ ≤ 2/(seriesLength.factorial : ℝ) := by
      rw [div_le_div_iff₀ (mul_pos hf (zero_lt_one.trans_le hm)) hf]
      have hs : u^seriesLength * ((seriesLength : ℝ) + 1) ≤ 2*(seriesLength : ℝ) := by
        calc
          _ ≤ 1 * ((seriesLength : ℝ) + 1) := by gcongr
          _ ≤ _ := by linarith
      calc
        _ ≤ (2*(seriesLength : ℝ)) * (seriesLength.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hs hf.le
        _ = _ := by ring
    _ ≤ _ := (div_le_div_iff₀ hf scale_pos).2 (by simpa only [one_mul] using hfd)

private theorem initial_bounds {d : ℕ} {t : Segment} {v e : ℝ}
    (hd : 0 < (d : ℝ)) (hq : 0 < t.denom) (hv : (t.sumNum : ℝ)/t.denom = v)
    (he : v ≤ e ∧ e ≤ v + 1/(d : ℝ)) :
    ((initBoundsFrom d t).1 : ℝ)/d ≤ e ∧ e < ((initBoundsFrom d t).2 : ℝ)/d := by
  let l := d*t.sumNum/t.denom
  have hdiv := floor_cast_bounds (d*t.sumNum) t.denom hq
  rw [Nat.cast_mul, mul_div_assoc, hv] at hdiv
  change (l : ℝ) ≤ (d : ℝ)*v ∧ (d : ℝ)*v < (l : ℝ)+1 at hdiv
  refine ⟨((div_le_iff₀ hd).2 ?_).trans he.1, he.2.trans_lt ?_⟩
  · rw [mul_comm]
    exact hdiv.1
  · change v + 1/(d : ℝ) < ((l+2 : ℕ) : ℝ)/(d : ℝ)
    rw [Nat.cast_add, Nat.cast_ofNat]
    apply (lt_div_iff₀ hd).2
    rw [add_mul, div_mul_cancel₀ _ hd.ne', mul_comm v]
    calc
      _ < ((l : ℝ)+1)+1 := add_lt_add_left hdiv.2 1
      _ = _ := by ring

private theorem base_bound :
    ((baseInterval.1 : ℕ) : ℝ)/(scale : ℝ) ≤ Real.exp u ∧
    Real.exp u < ((baseInterval.2 : ℕ) : ℝ)/(scale : ℝ) := by
  unfold baseInterval
  exact initial_bounds (d := scale) (t := segment 19 0) (v := sumTerms 0 seriesLength)
    (e := Real.exp u) scale_pos (segment_denom_pos 19 0) (segment_eval 19 0).2 series_bound

private theorem interval_invariant (d : ℕ) (p : ℕ × ℕ) (x : ℝ) (hd : 0 < (d : ℝ))
    (hp : (p.1 : ℝ)/d ≤ Real.exp x ∧ Real.exp x < (p.2 : ℝ)/d) (k : ℕ) :
    ((squareIntervalFrom d p k).1 : ℝ)/d ≤ Real.exp ((2:ℝ)^k*x) ∧
      Real.exp ((2:ℝ)^k*x) < ((squareIntervalFrom d p k).2 : ℝ)/d := by
  induction k with
  | zero => simpa only [pow_zero, one_mul, squareIntervalFrom] using hp
  | succ k ih =>
      let l := (squareIntervalFrom d p k).1
      let h := (squareIntervalFrom d p k).2
      let e := Real.exp ((2:ℝ)^k*x)
      have he : Real.exp ((2:ℝ)^(k+1)*x) = e^2 := by
        rw [pow_succ, show (2:ℝ)^k*2*x=(2:ℝ)^k*x+(2:ℝ)^k*x by ring, Real.exp_add, pow_two]
      have hlsq : ((l : ℝ)/(d : ℝ))^2 ≤ e^2 :=
        pow_le_pow_left₀ (by positivity) ih.1 2
      have hhsq : e^2 < ((h : ℝ)/(d : ℝ))^2 :=
        pow_lt_pow_left₀ ih.2 (Real.exp_nonneg _) (by decide)
      rw [he]
      constructor
      · exact (scaled_floor (l*l) d hd).1.trans (by
          simpa only [Nat.cast_mul, ← pow_two (l : ℝ), ← div_pow] using hlsq)
      · have hmid : e^2 < ((h*h : ℕ) : ℝ)/(d : ℝ)^2 := by
          simpa only [Nat.cast_mul, ← pow_two (h : ℝ), ← div_pow] using hhsq
        change e^2 < ((h*h/d+1 : ℕ) : ℝ)/(d : ℝ)
        rw [Nat.cast_add, Nat.cast_one]
        exact hmid.trans (scaled_floor (h*h) d hd).2

private theorem squaring_invariant (k : ℕ) :
    ((squareInterval k).1 : ℝ)/(scale : ℝ) ≤ Real.exp ((2:ℝ)^k*u) ∧
      Real.exp ((2:ℝ)^k*u) < ((squareInterval k).2 : ℝ)/(scale : ℝ) :=
  interval_invariant scale baseInterval u scale_pos base_bound k

private theorem nonsquare_between {e : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hl : (n : ℝ)+1/2 < e) (hu : e < (n : ℝ)+1) : ¬ IsSquare ⌊e^2⌋ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnI : (0 : ℤ) ≤ (n : ℤ) := by positivity
  have he : 0 ≤ e := by linarith
  have hlowR : (n : ℝ)^2+1 ≤ e^2 := by
    have hsq := pow_lt_pow_left₀ hl (by positivity) (show 2 ≠ (0 : ℕ) by decide)
    nlinarith
  have hhighR : e^2 < ((n : ℝ)+1)^2 := pow_lt_pow_left₀ hu he (by decide)
  have hlowI : (n : ℤ)^2+1 ≤ ⌊e^2⌋ := Int.le_floor.mpr (by exact_mod_cast hlowR)
  have hhighI : ⌊e^2⌋ < ((n : ℤ)+1)^2 := Int.floor_lt.mpr (by exact_mod_cast hhighR)
  rintro ⟨a,ha⟩
  have heq : |a|^2 = ⌊e^2⌋ := by rw [sq_abs, pow_two]; exact ha.symm
  by_cases h : |a| ≤ (n : ℤ)
  · have hh := pow_le_pow_left₀ (abs_nonneg a) h 2
    omega
  · have h' : (n : ℤ)+1 ≤ |a| := by omega
    have hh := pow_le_pow_left₀ (show (0 : ℤ) ≤ (n : ℤ)+1 by omega) h' 2
    omega

private theorem interval_forces_nonsquare {e : ℝ} {l h d : ℕ}
    (hd : 0 < (d : ℝ)) (hl : (l : ℝ)/d ≤ e) (hu : e < (h : ℝ)/d)
    (hsame : l/d = h/d) (hn : 2 ≤ l/d) (hrem : d < 2*(l%d)) :
    ¬ IsSquare ⌊e^2⌋ := by
  let n := l/d
  have hadd := Nat.mod_add_div l d
  have hcast : ((l%d : ℕ) : ℝ) + (d : ℝ)*(n : ℝ) = (l : ℝ) := by
    exact_mod_cast hadd
  have hhalf : (d : ℝ) < 2*((l%d : ℕ) : ℝ) := by exact_mod_cast hrem
  apply nonsquare_between hn
  · apply lt_of_lt_of_le _ hl
    change (n : ℝ)+1/2 < (l : ℝ)/(d : ℝ)
    apply (lt_div_iff₀ hd).2
    nlinarith
  · apply hu.trans
    change (h : ℝ)/(d : ℝ) < (n : ℝ)+1
    change n = h/d at hsame
    rw [hsame]
    exact (floor_cast_bounds h d (by exact_mod_cast hd)).2

private theorem certificate_gap (hc : numericalCertificate) :
    ¬ IsSquare ⌊(Real.exp ((2:ℝ)^22*u))^2⌋ :=
  interval_forces_nonsquare scale_pos (squaring_invariant 22).1 (squaring_invariant 22).2
    hc.1 hc.2.1 hc.2.2

private theorem p_of_count (i q : ℕ) (hq : q.Prime)
    (hcount : Nat.count Nat.Prime q = i-1) : p i = q := by
  simpa only [p, ← hcount] using Nat.nth_count (p := Nat.Prime) hq

private theorem primorial_nine : primorial 9 = 223092870 := by
  have p1 : p 1 = 2 := p_of_count _ _ (by decide) (by decide)
  have p2 : p 2 = 3 := p_of_count _ _ (by decide) (by decide)
  have p3 : p 3 = 5 := p_of_count _ _ (by decide) (by decide)
  have p4 : p 4 = 7 := p_of_count _ _ (by decide) (by decide)
  have p5 : p 5 = 11 := p_of_count _ _ (by decide) (by decide)
  have p6 : p 6 = 13 := p_of_count _ _ (by decide) (by decide)
  have p7 : p 7 = 17 := p_of_count _ _ (by decide) (by decide)
  have p8 : p 8 = 19 := p_of_count _ _ (by decide) (by decide)
  have p9 : p 9 = 23 := p_of_count _ _ (by decide) (by decide)
  have hset : Finset.Icc (1 : ℕ) 9 = {1,2,3,4,5,6,7,8,9} := by decide
  rw [primorial, hset]
  norm_num [Finset.prod_insert, p1, p2, p3, p4, p5, p6, p7, p8, p9]

private theorem exp_witness :
    Real.exp ((primorial (3^2) : ℝ) / p (3^2+1)) = (Real.exp ((2:ℝ)^22*u))^2 := by
  have hp : p 10 = 29 := p_of_count _ _ (by decide) (by decide)
  change Real.exp ((primorial 9 : ℝ) / p 10) = _
  rw [primorial_nine, hp, pow_two, ← Real.exp_add]
  congr 1
  norm_num [u, exponentNum, smallDen]

private theorem disproof_of_certificate (hc : numericalCertificate) :
    ¬ (type_of% @OMA.S_mse_2645263.main) := by
  intro h
  have hx := h 3 (by decide)
  rw [exp_witness] at hx
  exact certificate_gap hc hx

end OMA.S_mse_2645263

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2645263.main) :=
  OMA.S_mse_2645263.disproof_of_certificate OMA.S_mse_2645263.numerical_result
