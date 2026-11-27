import FormalConjectures.OEIS.«218585»
import Mathlib

/-! First moments of coordinates in the fundamental Eisenstein sector.
The split norm representation proof below is adapted from @PanPapag (#1308).
Summation by parts transfers unweighted sector averages to square-root weights. -/

namespace OMA.SplitPrime

lemma cubicRoot (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ r : ZMod p, r ^ 2 + r + 1 = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hd
  have hc : (u : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
    rfl
  have hne : (u : ZMod p) ≠ 1 := by
    intro h
    have h' : u = 1 := Units.ext h
    simp [h'] at hu
  refine ⟨u, (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)⟩
  linear_combination hc

/-- Pigeonholing a square modulo p gives a nonzero vector with small coordinates. -/
lemma smallVector (p : ℕ) (hp : p.Prime) (r : ZMod p) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ p.sqrt ∧ |b| ≤ p.sqrt ∧
      (a : ZMod p) = r * (b : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := Fin (p.sqrt + 1)
  let f (v : B × B) : ZMod p := (v.1.val : ZMod p) - r * v.2.val
  obtain ⟨v, w, hvw, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simpa [B, ZMod.card] using Nat.lt_succ_sqrt p)
  let a : ℤ := (v.1.val : ℤ) - w.1.val
  let b : ℤ := (v.2.val : ℤ) - w.2.val
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · by_contra! hz
    apply hvw
    apply Prod.ext <;> apply Fin.ext
    · dsimp [a] at hz
      omega
    · dsimp [b] at hz
      omega
  · have hv := v.1.isLt
    have hw := w.1.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [a]
    omega
  · have hv := v.2.isLt
    have hw := w.2.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [b]
    omega
  · dsimp [a, b]
    push_cast
    dsimp [f] at heq
    linear_combination heq

/-- The small norm is a positive multiple of p strictly below 3p.
The residue 2 modulo 3 is impossible for the norm form. -/
lemma integralRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : ℤ, a ^ 2 + a * b + b ^ 2 = p := by
  obtain ⟨r, hr⟩ := cubicRoot p hp hmod
  obtain ⟨a, b, hab, ha, hb, heq⟩ := smallVector p hp r
  let q := a ^ 2 + a * b + b ^ 2
  have hd : (p : ℤ) ∣ q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [q]
    push_cast
    rw [heq]
    linear_combination (b : ZMod p) ^ 2 * hr
  have hpos : 0 < q := by
    dsimp [q]
    rcases hab with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg b, sq_nonneg (a + b)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a, sq_nonneg (a + b)]
  have hs : p.sqrt * p.sqrt < p :=
    lt_of_le_of_ne (Nat.sqrt_le _) (fun h => hp.prime.not_isSquare ⟨_, h.symm⟩)
  have hbound : q < 3 * p := by
    have hs' : (p.sqrt : ℤ) * p.sqrt < p := by exact_mod_cast hs
    have ha' := mul_self_le_mul_self (abs_nonneg a) ha
    have hb' := mul_self_le_mul_self (abs_nonneg b) hb
    rw [abs_mul_abs_self] at ha' hb'
    dsimp [q]
    nlinarith [sq_nonneg (a - b)]
  obtain ⟨k, hk⟩ := hd
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hkpos : 0 < k := pos_of_mul_pos_right (hk ▸ hpos) hp'.le
  have hksmall : k < 3 := by
    rw [hk, mul_comm (3 : ℤ)] at hbound
    exact (mul_lt_mul_iff_right₀ hp').mp hbound
  have hk1 : k = 1 := by
    by_contra h
    have hk2 : k = 2 := by omega
    have hq : a ^ 2 + a * b + b ^ 2 = (p : ℤ) * 2 := by simpa [q, hk2] using hk
    have h3 : (p : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, hmod]
      rfl
    have hbad := congrArg (fun z : ℤ => (z : ZMod 3)) hq
    push_cast at hbad
    rw [h3, one_mul] at hbad
    exact (show ∀ x y : ZMod 3, x ^ 2 + x * y + y ^ 2 ≠ 2 by decide) _ _ hbad
  exact ⟨a, b, by simpa [q, hk1] using hk⟩

/-- Among a, b, and -a-b, two share a weak sign. Each pair has the same norm. -/
lemma nonnegativeRepresentation (p : ℕ) (a b : ℤ) (h : a ^ 2 + a * b + b ^ 2 = p) :
    ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
  have liftPair (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v)
      (hn : u ^ 2 + u * v + v ^ 2 = p) : ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
    refine ⟨u.toNat, v.toNat, ?_⟩
    have he : (u.toNat : ℤ) ^ 2 + (u.toNat : ℤ) * v.toNat + (v.toNat : ℤ) ^ 2 = p := by
      simpa [Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv] using hn
    exact_mod_cast he
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · exact liftPair a b ha hb h
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair a (-a-b) ha hs (by linear_combination h)
    · exact liftPair (-b) (a+b) (by omega) (by omega) (by linear_combination h)
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair b (-a-b) hb hs (by linear_combination h)
    · exact liftPair (-a) (a+b) (by omega) (by omega) (by linear_combination h)
  · exact liftPair (-a) (-b) (by omega) (by omega) (by linear_combination h)

lemma orderedRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ x y : ℕ, 0 < y ∧ y < x ∧ x < p ∧ x ^ 2 + x * y + y ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := integralRepresentation p hp hmod
  obtain ⟨u, v, huv⟩ := nonnegativeRepresentation p a b hab
  obtain ⟨x, y, hle, hn⟩ : ∃ x y : ℕ, y ≤ x ∧ x ^ 2 + x * y + y ^ 2 = p := by
    rcases le_total v u with h | h
    · exact ⟨u, v, h, huv⟩
    · exact ⟨v, u, h, by linarith⟩
  have hy : 0 < y := by
    by_contra! hz
    have he : y = 0 := by omega
    exact hp.prime.not_isSquare ⟨x, by simpa [he, pow_two] using hn.symm⟩
  have hne : y ≠ x := by
    rintro rfl
    have hd : 3 ∣ p := ⟨y ^ 2, by nlinarith⟩
    omega
  refine ⟨x, y, hy, lt_of_le_of_ne hle hne, ?_, hn⟩
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) x, Nat.pow_pos hy (n := 2)]

/-- Swapping the coordinates interchanges the two roots of the norm form modulo p.
In the ordered sector only one cross product can vanish. -/
lemma uniqueSecond (p : ℕ) (hp : p.Prime) (a b c d : ℕ)
    (hb : 0 < b) (hab : b < a) (hd : 0 < d) (hcd : d < c)
    (h₁ : a ^ 2 + a * b + b ^ 2 = p) (h₂ : c ^ 2 + c * d + d ^ 2 = p) : b = d := by
  let : Fact p.Prime := ⟨hp⟩
  have h₁' : (a : ZMod p) ^ 2 + a * b + b ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₁
  have h₂' : (c : ZMod p) ^ 2 + c * d + d ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₂
  have hf : ((a : ZMod p) * d - b * c) * (a * c - b * d) = 0 := by
    linear_combination (c : ZMod p) * d * h₁' - (a : ZMod p) * b * h₂'
  have hac : a * c < p := by
    rcases le_total a c with h | h
    · have hsq := Nat.mul_le_mul_right c h
      nlinarith [Nat.mul_pos (hd.trans hcd) hd]
    · have hsq := Nat.mul_le_mul_left a h
      nlinarith [Nat.mul_pos (hb.trans hab) hb]
  have hbc := Nat.mul_lt_mul_of_pos_right hab (by omega : 0 < c)
  have had := Nat.mul_lt_mul_of_pos_left hcd (by omega : 0 < a)
  have hbd := Nat.mul_lt_mul_of_pos_right hab hd
  have liftEq (u v : ℕ) (hu : u < p) (hv : v < p) (h : (u : ZMod p) = v) : u = v := by
    simpa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using
      (ZMod.natCast_eq_natCast_iff' u v p).mp h
  have hcross : a * d = b * c := by
    rcases mul_eq_zero.mp hf with h | h
    · exact liftEq _ _ (had.trans hac) (hbc.trans hac) (by simpa using sub_eq_zero.mp h)
    · have he := liftEq (a*c) (b*d) hac (hbd.trans (had.trans hac)) (by simpa using sub_eq_zero.mp h)
      omega
  have he : p * d ^ 2 = p * b ^ 2 := calc
    p * d ^ 2 = (a*d) ^ 2 + (a*d)*(b*d) + (b*d) ^ 2 := by rw [← h₁]; ring
    _ = p * b ^ 2 := by rw [hcross, ← h₂]; ring
  have := Nat.eq_of_mul_eq_mul_left hp.pos he
  nlinarith

lemma findWitness (l : List ℕ) (f : ℕ → Bool) (w : ℕ) (hw : w ∈ l) (hf : f w) :
    f ((l.find? f).getD 0) := by
  cases h : l.find? f with
  | none => exact False.elim ((List.find?_eq_none.mp h w hw) hf)
  | some z => exact List.find?_some h

end OMA.SplitPrime

open OeisA218585 OMA.SplitPrime

private theorem splitNorm : ∀ p : ℕ, p.Prime → p % 3 = 1 → xp p ^ 2 + xp p * yp p + yp p ^ 2 = p := by
  intro p hp hmod
  obtain ⟨x, y, hy, hyx, hxp, hn⟩ := orderedRepresentation p hp hmod
  let X (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let Y (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  have specX (u : ℕ) : X u ↔ ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [X]
  have specY (v : ℕ) : Y v ↔ 0 < v ∧ ∃ u, (v + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [Y]
  have hx' : X (xp p) := findWitness (List.range p) X x (List.mem_range.mpr hxp)
    ((specX x).mpr ⟨y, hyx, hy, hn⟩)
  have hy' : Y (yp p) := findWitness (List.range p) Y y (List.mem_range.mpr (hyx.trans hxp))
    ((specY y).mpr ⟨hy, x, ⟨hyx, hxp⟩, hn⟩)
  obtain ⟨v, hvx, hv, h₁⟩ := (specX _).mp hx'
  obtain ⟨hy₀, u, ⟨hyu, _⟩, h₂⟩ := (specY _).mp hy'
  rwa [← uniqueSecond p hp (xp p) v u (yp p) hv hvx hy₀ hyu h₁ h₂]

namespace OMA.R_OeisA218585_conjecture_3_R1

open OeisA218585 Real Filter MeasureTheory Finset
open scoped Topology

-- Hecke's sector theorem for the unweighted counting measure.
def H1 : Prop :=
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun n => (∑ p ∈ splitPrimes n, f (angle p)) / (splitPrimes n).card)
    atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t))

-- A positive fraction of the split primes lie in the upper dyadic interval.
def H2 : Prop :=
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  ∀ᶠ n in atTop,
    (splitPrimes n).card ≤ 3 * ((splitPrimes n).filter fun p => n ≤ 2 * p).card

lemma countsGrow :
    Tendsto (fun n => ((((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card : ℝ)) atTop atTop := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let P (p : ℕ) := p.Prime ∧ p % 3 = 1
  have hi : (Set.ofPred P).Infinite :=
    Nat.infinite_setOfPred_prime_modEq_one (k := 3) (by decide)
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_atTop.mpr
  intro k
  refine ⟨Nat.nth P k, fun n hn => ?_⟩
  change k ≤ ((range n).filter P).card
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_nth_of_infinite hi k]
  exact Nat.count_monotone P hn

private theorem uniformPrefix {A count : ℕ → ℝ} (hn : ∀ j, 0 ≤ count j)
    (hz : ∀ j, count j = 0 → A j = 0) (hm : Monotone count)
    (hg : Tendsto count atTop atTop) (h : Tendsto (fun j => A j / count j) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, |A j| ≤ δ * count n := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp h) δ hδ)
  let C := ∑ j ∈ range K, |A j|
  filter_upwards [hg.eventually_ge_atTop (C / δ)] with n hn' j hj
  by_cases hk : j < K
  · exact (single_le_sum (f := fun j => |A j|) (fun i _ => abs_nonneg (A i))
      (mem_range.mpr hk)).trans (by simpa [mul_comm] using (div_le_iff₀ hδ).mp hn')
  by_cases hc : count j = 0
  · simp [hz j hc, mul_nonneg hδ.le (hn n)]
  have hpos := lt_of_le_of_ne (hn j) (Ne.symm hc)
  have hsmall := hK j (Nat.le_of_not_gt hk)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at hsmall
  exact hsmall.le.trans (mul_le_mul_of_nonneg_left (hm hj) hδ.le)

private theorem weightBound (hd : H2) : ∀ᶠ n : ℕ in atTop,
    √(n : ℝ) * (((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card ≤ 6 * ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  filter_upwards [hd] with n h
  let U := (splitPrimes n).filter fun p => n ≤ 2 * p
  have hc : ((splitPrimes n).card : ℝ) ≤ 3 * (U.card : ℝ) := by exact_mod_cast h
  have hb : √(n : ℝ) * U.card ≤ 2 * ∑ p ∈ splitPrimes n, √(p : ℝ) := calc
    _ = ∑ _p ∈ U, √(n : ℝ) := by simp [mul_comm]
    _ ≤ ∑ p ∈ U, 2 * √(p : ℝ) := sum_le_sum fun p hp => by
      have hv : (n : ℝ) ≤ 2 * p := by exact_mod_cast (mem_filter.mp hp).2
      nlinarith [sq_sqrt (Nat.cast_nonneg p), sq_sqrt (Nat.cast_nonneg n),
        sqrt_nonneg (p : ℝ), sqrt_nonneg (n : ℝ)]
    _ ≤ ∑ p ∈ splitPrimes n, 2 * √(p : ℝ) := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => by positivity
    _ = _ := (mul_sum ..).symm
  linarith [mul_le_mul_of_nonneg_left hc (sqrt_nonneg (n : ℝ))]

private theorem transfer (hd : H2) (f : ℕ → ℝ)
    (cancel : Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), f p) / (((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card)
      atTop (𝓝 0)) :
    Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) * f p) /
      ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ)) atTop (𝓝 0) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let A (n : ℕ) := ∑ p ∈ splitPrimes n, f p
  let count (n : ℕ) : ℝ := (splitPrimes n).card
  let w (j : ℕ) := √(j : ℝ)
  let mass (n : ℕ) := ∑ p ∈ splitPrimes n, w p
  have hw : Monotone w := fun _ _ hj => sqrt_le_sqrt (by exact_mod_cast hj)
  have hc : Monotone count := fun m n h => by
    dsimp [count,splitPrimes]
    exact_mod_cast Finset.card_le_card (filter_subset_filter (fun p : ℕ => p.Prime ∧ p % 3 = 1) (range_mono h))
  have hz (j : ℕ) (h : count j = 0) : A j = 0 := by
    dsimp [count] at h
    have h' : (splitPrimes j).card = 0 := by exact_mod_cast h
    simp [A, card_eq_zero.mp h']
  have abel (n : ℕ) : (∑ p ∈ splitPrimes n, w p * f p) =
      w (n-1) * A n - ∑ j ∈ range (n-1), (w (j+1) - w j) * A (j+1) := by
    simpa [A, splitPrimes, sum_filter, mul_ite] using
      sum_range_by_parts w (fun p => if p.Prime ∧ p % 3 = 1 then f p else 0) n
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let δ := ε / 24
  have hd' : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [uniformPrefix (A := A) (count := count) (fun n => Nat.cast_nonneg _) hz hc
    countsGrow cancel hd', weightBound hd, countsGrow.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hsmall hweight hcount hn
  change w n * count n ≤ 6 * mass n at hweight
  change (1 : ℝ) ≤ count n at hcount
  have hmass : 0 < mass n := by
    have hn' : 0 < w n := sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    nlinarith [mul_pos hn' (show 0 < count n by linarith)]
  have sumBound : |∑ j ∈ range (n-1), (w (j+1) - w j) * A (j+1)| ≤
      w (n-1) * (δ * count n) := calc
    _ ≤ ∑ j ∈ range (n-1), |(w (j+1) - w j) * A (j+1)| := abs_sum_le_sum_abs .. 
    _ ≤ ∑ j ∈ range (n-1), (w (j+1) - w j) * (δ * count n) := sum_le_sum fun j hj => by
      have hdif := sub_nonneg.mpr (hw (Nat.le_succ j))
      rw [abs_mul, abs_of_nonneg hdif]
      exact mul_le_mul_of_nonneg_left (hsmall _ (by have := mem_range.mp hj; omega)) hdif
    _ = _ := by rw [← sum_mul, sum_range_sub]; simp [w]
  have hlast := mul_le_mul_of_nonneg_left (hsmall n le_rfl) (sqrt_nonneg ((n-1 : ℕ) : ℝ))
  have hbig := mul_le_mul_of_nonneg_right (hw (Nat.sub_le n 1)) (mul_nonneg hd'.le (Nat.cast_nonneg _ : 0 ≤ count n))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hmass, div_lt_iff₀ hmass, abel]
  refine (abs_sub _ _).trans_lt ?_
  rw [abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  change w (n-1) * |A n| + _ < ε * mass n
  dsimp only [w] at hlast ⊢
  dsimp only [w] at hbig hweight sumBound
  dsimp [δ] at hbig hlast sumBound
  nlinarith [mul_le_mul_of_nonneg_left hweight he.le, mul_pos he hmass]


private theorem weightedLimit (sieve : H1) (hd : H2) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) * g ((⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg)) /
      ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ)) atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, g t)) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  let L := (6 / π) * ∫ t in 0..π / 6, g t
  have hc : ∀ᶠ n : ℕ in atTop, (splitPrimes n).Nonempty := by
    filter_upwards [eventually_ge_atTop 8] with n hn
    exact ⟨7,mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩⟩
  have cancel : Tendsto (fun n => (∑ p ∈ splitPrimes n, (g (angle p) - L)) /
      (splitPrimes n).card) atTop (𝓝 0) := by
    have h := (sieve g hg).sub_const L
    rw [show (6 / π) * (∫ t in 0..π / 6, g t) - L = 0 from sub_self L] at h
    apply h.congr'
    filter_upwards [hc] with n hn
    have hn' : ((splitPrimes n).card : ℝ) ≠ 0 := by exact_mod_cast hn.card_pos.ne'
    change (∑ p ∈ splitPrimes n, g (angle p)) / (splitPrimes n).card - L = _
    rw [sum_sub_distrib]
    simp [sub_div, hn', nsmul_eq_mul]
  have h := (transfer hd (fun p => g (angle p) - L) cancel).add_const L
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  have h7 : 7 ∈ splitPrimes n := mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩
  have hm : 0 < ∑ p ∈ splitPrimes n, √(p : ℝ) :=
    (by norm_num : (0:ℝ) < √(7 : ℕ)).trans_le (single_le_sum (f := fun p : ℕ => √(p : ℝ)) (fun p _ => sqrt_nonneg (p:ℝ)) h7)
  change (∑ p ∈ splitPrimes n, √(p:ℝ) * (g (angle p) - L)) / (∑ p ∈ splitPrimes n, √(p:ℝ)) + L = (∑ p ∈ splitPrimes n, √(p:ℝ) * g (angle p)) / (∑ p ∈ splitPrimes n, √(p:ℝ))
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
  field_simp <;> ring

theorem main : H1 → H2 → type_of% @OeisA218585.conjecture_3 := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  intro sieve hd
  let g (a b t : ℝ) := a * cos t + b * sin t
  have integral (a b : ℝ) :
      (∫ t in 0..π / 6, g a b t) = a / 2 + b * (1 - √3 / 2) := by
    dsimp [g]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos, integral_sin]
    · simp [sin_pi_div_six, cos_pi_div_six]; ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  have limits (a b : ℝ) : Tendsto (fun n => (∑ p ∈ splitPrimes n, √(p:ℝ) * g a b (angle p)) / ∑ p ∈ splitPrimes n, √(p:ℝ)) atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, g a b t)) := weightedLimit sieve hd (g a b) (by dsimp [g]; fun_prop)
  have hx := limits 1 (-(√3) / 3)
  have hy := limits 0 (2 * √3 / 3)
  rw [integral] at hx hy
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have points (p : ℕ) (hp : p.Prime ∧ p % 3 = 1) :
      √(p : ℝ) * g 1 (-(√3) / 3) (angle p) = xp p ∧
      √(p : ℝ) * g 0 (2 * √3 / 3) (angle p) = yp p := by
    let x : ℝ := xp p
    let y : ℝ := yp p
    let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
    have hn : x^2 + x*y + y^2 = (p : ℝ) := by dsimp [x,y]; exact_mod_cast splitNorm p hp.1 hp.2
    have hz : ‖z‖ ^ 2 = (p : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [z]
      linear_combination hn + (y^2/4)*hs
    have hnorm : ‖z‖ = √(p : ℝ) := by rw [← hz, sqrt_sq (norm_nonneg _)]
    have hc := Complex.norm_mul_cos_arg z
    have hi := Complex.norm_mul_sin_arg z
    rw [hnorm] at hc hi
    change √(p : ℝ) * cos z.arg = x + y / 2 at hc
    change √(p : ℝ) * sin z.arg = √3 * y / 2 at hi
    change √(p : ℝ) * (1 * cos z.arg + -(√3) / 3 * sin z.arg) = x ∧
      √(p : ℝ) * (0 * cos z.arg + 2 * √3 / 3 * sin z.arg) = y
    constructor
    · linear_combination hc - (√3/3)*hi - (y/6)*hs
    · linear_combination (2*√3/3)*hi + (y/3)*hs
  have sx (n : ℕ) : (∑ p ∈ splitPrimes n, √(p : ℝ) * g 1 (-(√3)/3) (angle p)) =
      ∑ p ∈ splitPrimes n, (xp p : ℝ) :=
    sum_congr rfl fun p hp => (points p (mem_filter.mp hp).2).1
  have sy (n : ℕ) : (∑ p ∈ splitPrimes n, √(p : ℝ) * g 0 (2*√3/3) (angle p)) =
      ∑ p ∈ splitPrimes n, (yp p : ℝ) :=
    sum_congr rfl fun p hp => (points p (mem_filter.mp hp).2).2
  simp_rw [sx] at hx
  simp_rw [sy] at hy
  have hpos : 0 < (6 / π) * (0 / 2 + 2 * √3 / 3 * (1 - √3 / 2)) := by
    have : 0 < 1 - √3 / 2 := by nlinarith [sqrt_nonneg (3:ℝ)]
    positivity
  have heq : (6 / π * (1 / 2 + -√3 / 3 * (1 - √3 / 2))) /
      (6 / π * (0 / 2 + 2 * √3 / 3 * (1 - √3 / 2))) = 1 + √3 := by
    apply (div_eq_iff hpos.ne').mpr
    ring_nf
    field_simp
    linear_combination (norm := ring_nf) (2 * √3 - 1) * hs
  have h := hx.div hy hpos.ne'
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  have h7 : 7 ∈ splitPrimes n := mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩
  have hm : 0 < ∑ p ∈ splitPrimes n, √(p : ℝ) :=
    (by norm_num : (0:ℝ) < √(7 : ℕ)).trans_le (single_le_sum (f := fun p : ℕ => √(p : ℝ)) (fun p _ => sqrt_nonneg (p:ℝ)) h7)
  exact div_div_div_cancel_right₀ hm.ne' _ _

end OMA.R_OeisA218585_conjecture_3_R1
