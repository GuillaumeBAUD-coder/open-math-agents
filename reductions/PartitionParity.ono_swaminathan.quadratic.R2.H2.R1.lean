import OMAReductions.R_PartitionParity_ono_swaminathan_quadratic_R2
import Mathlib

/-!
# Nonperiodicity of the complementary partition Lambert series

Ono and Swaminathan's level-six Eisenstein comparison, including the oldform
sum at level 6D, gives the unweighted Lambert transform. Its difference from
the Borcherds Lambert series has a nonzero positive coefficient as soon as one
admissible even partition value exists. This difference generates a field over
which the inverse modular invariant is algebraic. If the Lambert coefficients
were periodic, Christol's necessary direction would force the odd-square
sequence to have finite binary kernel.

The three inputs are the two modular algebraicity statements and an even value
from the ordinary CM pole comparison. The arithmetic Eisenstein coefficient
identities, the field exchange, and the binary Christol implication are proved
below.

## References
* Ono and Swaminathan, <https://arxiv.org/html/2509.09553v4#S4.SS2>.
* Christol, Kamae, Mendès France and Rauzy,
  <https://www.numdam.org/articles/10.24033/bsmf.1926/>.
-/

open scoped BigOperators LaurentSeries RatFunc

namespace PartitionPeriodicSeries

open PowerSeries

/-- A positive period on the positive coefficients makes the generating
series rational, with polynomial denominator `1-X^P`. The constant
coefficient may be arbitrary. -/
private theorem polynomial_mul_of_periodic_positive {R : Type*} [CommRing R]
    (f : ℕ → R) {P : ℕ}
    (hperiod : ∀ n : ℕ, 0 < n → f (n + P) = f n) :
    ∃ A : Polynomial R,
      (1 - (X : PowerSeries R)^P) * PowerSeries.mk f = (A : PowerSeries R) := by
  let c (i : ℕ) : R := f i - if i = P then f 0 else 0
  refine ⟨∑ i ∈ Finset.range (P + 1), Polynomial.monomial i (c i), ?_⟩
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul', Polynomial.coeff_coe,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hlt : n < P
  · have hnP : n ≠ P := hlt.ne
    simp [c, hnP, not_le.mpr hlt, hlt.trans (Nat.lt_succ_self P)]
  · have hle : P ≤ n := le_of_not_gt hlt
    rcases eq_or_lt_of_le hle with hEq | hgt
    · subst n
      simp [c]
    · have hpos : 0 < n-P := by omega
      have heq := hperiod (n-P) hpos
      rw [Nat.sub_add_cancel hle] at heq
      have hout : ¬ n < P + 1 := by omega
      simp [hle, hout, heq]

/-- The Laurent series of a positively indexed periodic sequence lies in the
rational function subfield. -/
private theorem ratFunc_of_periodic_positive {K : Type*} [Field K] (f : ℕ → K) {P : ℕ}
    (hP : 0 < P) (hperiod : ∀ n : ℕ, 0 < n → f (n + P) = f n) :
    ∃ F : RatFunc K, (F : K⸨X⸩) = (PowerSeries.mk f : K⸨X⸩) := by
  obtain ⟨A, hA⟩ := polynomial_mul_of_periodic_positive f hperiod
  let B : Polynomial K := 1 - Polynomial.X^P
  have hB : (B : PowerSeries K) = 1 - (X : PowerSeries K)^P := by simp [B]
  have hBne : (B : PowerSeries K) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff (R := K)) hz
    simp [hB, zero_pow hP.ne'] at hc
  have hLaurentB : ((B : PowerSeries K) : K⸨X⸩) ≠ 0 := by
    have hf : Function.Injective (HahnSeries.ofPowerSeries ℤ K) :=
      HahnSeries.ofPowerSeries_injective
    simpa only [map_zero] using hf.ne hBne
  have heq : ((B : PowerSeries K) : K⸨X⸩) * (PowerSeries.mk f : K⸨X⸩) =
      ((A : PowerSeries K) : K⸨X⸩) := by
    rw [← PowerSeries.coe_mul, hB, hA]
  refine ⟨(A : RatFunc K) / (B : RatFunc K), ?_⟩
  change algebraMap (RatFunc K) K⸨X⸩ ((A : RatFunc K) / (B : RatFunc K)) =
    (PowerSeries.mk f : K⸨X⸩)
  rw [map_div₀]
  change ((A : RatFunc K) : K⸨X⸩) / ((B : RatFunc K) : K⸨X⸩) =
    (PowerSeries.mk f : K⸨X⸩)
  rw [← RatFunc.coe_coe, ← RatFunc.coe_coe, div_eq_iff hLaurentB, mul_comm]
  exact heq.symm


end PartitionPeriodicSeries

namespace PartitionSquareKernel

/-- The binary kernel of a sequence consists of all its dyadic subsequences. -/
private def binaryKernel {α : Type*} (f : ℕ → α) : Set (ℕ → α) :=
  {g | ∃ e r : ℕ, r < 2^e ∧ g = fun n => f (2^e*n+r)}

/-- The mod-two series supported on odd squares. -/
private noncomputable def oddSquareSequence (n : ℕ) : ZMod 2 := by
  classical
  exact if Odd n ∧ IsSquare n then 1 else 0

private theorem dyadic_odd (e n : ℕ) : Odd (2^(e+3)*n+1 : ℕ) := by
  apply Even.add_odd _ odd_one
  apply even_iff_two_dvd.mpr
  exact dvd_mul_of_dvd_left (by rw [pow_succ']; exact dvd_mul_right _ _) _

/-- Every nonzero index in the residue-one subsequence that gives a square is
at least the first index shown below. -/
private theorem first_square_lower_bound {e n : ℕ} (hn : 0 < n)
    (hs : IsSquare (2^(e+3)*n+1 : ℕ)) : 2^(e+1) - 1 ≤ n := by
  let q : ℕ := 2^(e+1)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hscale : (2 : ℕ)^(e+3) = 4*q := by
    dsimp [q]
    rw [show e+3 = 2+(e+1) by omega, pow_add]
    rfl
  obtain ⟨a, ha⟩ := hs
  have hodd : Odd a := (Nat.odd_mul.mp (ha ▸ dyadic_odd e n)).1
  obtain ⟨t, rfl⟩ := hodd.exists_bit1
  rw [hscale] at ha
  have htEq : t*(t+1) = q*n := by nlinarith only [ha]
  have ht : 0 < t := by
    by_contra! h
    have hzero : t = 0 := Nat.eq_zero_of_le_zero h
    rw [hzero, zero_mul] at htEq
    exact (Nat.mul_pos hqpos hn).ne' htEq.symm
  have hdiv : q ∣ t*(t+1) := ⟨n, htEq⟩
  have hbound : q ≤ t+1 := by
    by_cases h : 2 ∣ t
    · have hn : ¬ 2 ∣ t+1 := by omega
      have hc : Nat.Coprime q (t+1) :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr hn).pow_left _
      exact (Nat.le_of_dvd ht (hc.dvd_of_dvd_mul_right hdiv)).trans (by omega)
    · have hc : Nat.Coprime q t :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr h).pow_left _
      exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left hdiv)
  have hmul : q*(q-1) ≤ q*n := by
    rw [← htEq, mul_comm q]
    exact Nat.mul_le_mul (by omega) hbound
  exact Nat.le_of_mul_le_mul_left hmul hqpos

/-- The lower bound for the first positive square is attained. -/
private theorem first_square (e : ℕ) :
    IsSquare (2^(e+3)*(2^(e+1)-1)+1 : ℕ) := by
  let q : ℕ := 2^(e+1) - 1
  have hq : 2^(e+1) = q+1 := by
    have hpos : 0 < (2 : ℕ)^(e+1) := by positivity
    dsimp [q]
    omega
  have hscale : (2 : ℕ)^(e+3) = 4*(q+1) := by
    rw [show e+3 = 2+(e+1) by omega, pow_add, hq]
    rfl
  change IsSquare (2^(e+3)*q+1 : ℕ)
  refine ⟨2*q+1, ?_⟩
  rw [hscale]
  ring

private theorem oddSquareSequence_binaryKernel_infinite :
    (binaryKernel oddSquareSequence).Infinite := by
  classical
  let g (e n : ℕ) := oddSquareSequence (2^(e+3)*n+1)
  have hne {e d : ℕ} (hed : e < d) : g e ≠ g d := by
    intro heq
    let n := (2 : ℕ)^(e+1)-1
    have hlt₁ : (1 : ℕ) < 2^(e+1) := one_lt_pow₀ (by decide) (by omega)
    have hn : 0 < n := by dsimp [n]; omega
    have h₁ : g e n = 1 := by
      have hs : Odd (2^(e+3)*n+1) ∧ IsSquare (2^(e+3)*n+1) :=
        ⟨dyadic_odd e n, first_square e⟩
      simp only [g, oddSquareSequence, if_pos hs]
    have h₂ : g d n = 0 := by
      unfold g oddSquareSequence
      apply if_neg
      intro hs
      have hb := first_square_lower_bound hn hs.2
      have hpow : (2 : ℕ)^(e+1) < 2^(d+1) :=
        (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)
      dsimp [n] at hb
      omega
    rw [heq, h₂] at h₁
    exact zero_ne_one h₁
  have hg : Function.Injective g := by
    intro e d h
    by_contra h'
    rcases lt_or_gt_of_ne h' with hlt | hgt
    · exact hne hlt h
    · exact hne hgt h.symm
  refine (Set.infinite_range_of_injective hg).mono ?_
  rintro f ⟨e, rfl⟩
  exact ⟨e+3, 1, one_lt_pow₀ (by decide) (by omega), rfl⟩


end PartitionSquareKernel


namespace PartitionOddSquareExpansion

open PowerSeries

open PartitionSquareKernel

/-- The series with one coefficient at each triangular number. -/
private noncomputable def triangleSeries : PowerSeries (ZMod 2) := by
  classical
  exact PowerSeries.mk (fun n => if ∃ m : ℕ, n = m*(m+1)/2 then 1 else 0)

private theorem frobenius_iterate_eq_id (r : ℕ) :
    iterateFrobenius (ZMod 2) 2 r = RingHom.id (ZMod 2) := by
  ext x
  exact ZMod.pow_card_pow x

private theorem expand_eq_pow_eight (A : PowerSeries (ZMod 2)) :
    A.expand 8 (by decide) = A^8 := by
  have h := MvPowerSeries.map_iterateFrobenius_expand 2 (by decide) A 3
  rw [frobenius_iterate_eq_id, MvPowerSeries.map_id] at h
  exact h

private theorem square_of_odd (m : ℕ) :
    (2*m+1)*(2*m+1) = 8*(m*(m+1)/2)+1 := by
  have h := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self m))
  nlinarith only [h]

private theorem square_iff_triangle (n : ℕ) :
    Odd (n+1) ∧ IsSquare (n+1) ↔
      8 ∣ n ∧ ∃ m : ℕ, n/8 = m*(m+1)/2 := by
  constructor
  · rintro ⟨hodd, a, ha⟩
    have haodd : Odd a := (Nat.odd_mul.mp (ha ▸ hodd)).1
    obtain ⟨m, rfl⟩ := haodd.exists_bit1
    rw [square_of_odd] at ha
    have hn : n = 8*(m*(m+1)/2) := by omega
    rw [hn]
    exact ⟨dvd_mul_right _ _, m, Nat.mul_div_cancel_left _ (by decide)⟩
  · rintro ⟨hdiv, m, hm⟩
    have hn := Nat.div_mul_cancel hdiv
    rw [hm, mul_comm] at hn
    rw [← hn, ← square_of_odd]
    exact ⟨Nat.odd_mul.mpr ⟨⟨m, by omega⟩, ⟨m, by omega⟩⟩, 2*m+1, rfl⟩

private theorem oddSquareSeries_eq_X_mul_triangle_pow :
    PowerSeries.mk oddSquareSequence = (X : PowerSeries (ZMod 2)) * triangleSeries^8 := by
  classical
  rw [← expand_eq_pow_eight]
  ext n
  cases n with
  | zero =>
      rw [coeff_zero_eq_constantCoeff_apply (X * _), map_mul, constantCoeff_X, zero_mul]
      simp [oddSquareSequence]
  | succ n =>
      rw [PowerSeries.coeff_mk, show (X : PowerSeries (ZMod 2)) = X^1 by simp,
        PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.succ_sub_one,
        PowerSeries.coeff_expand, triangleSeries, PowerSeries.coeff_mk, oddSquareSequence]
      by_cases h : 8 ∣ n
      · simp [h, square_iff_triangle]
      · rw [if_neg h, if_neg (fun h' => h ((square_iff_triangle n).mp h').1)]


end PartitionOddSquareExpansion

namespace PartitionChristolWindow

private abbrev Coefficients := ℤ → ZMod 2

/-- The two operators which select the coefficients at even and odd indices. -/
private def cartier (r : Fin 2) : Coefficients →ₗ[ZMod 2] Coefficients where
  toFun f n := f (2*n + (r.val : ℤ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of a coefficient sequence by a monomial of degree `d`. -/
private def shift (d : ℕ) : Coefficients →ₗ[ZMod 2] Coefficients where
  toFun f n := f (n - (d : ℤ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Insert zero coefficients at odd indices. Over the field of two elements
this is the coefficient operation of squaring a Laurent series. -/
private def double (f : Coefficients) : Coefficients :=
  fun n => if n % 2 = 0 then f (n / 2) else 0

private def inflate (f : Coefficients) : ℕ → Coefficients
  | 0 => f
  | j+1 => double (inflate f j)

private theorem shift_shift (d e : ℕ) (f : Coefficients) :
    shift d (shift e f) = shift (d+e) f := by
  funext n
  change f (n - (d : ℤ) - (e : ℤ)) = f (n - ((d+e : ℕ) : ℤ))
  congr 1
  push_cast
  ring

/-- Decimation halves a monomial exponent when its parity is selected. -/
private theorem cartier_shift_double (r : Fin 2) (d : ℕ) (f : Coefficients) :
    cartier r (shift d (double f)) =
      if d % 2 = r.val then shift (d / 2) f else 0 := by
  have hr : r.val < 2 := r.isLt
  by_cases h : d % 2 = r.val
  · rw [if_pos h]
    funext n
    change (if (2*n+(r.val : ℤ)-(d : ℤ))%2=0
      then f ((2*n+(r.val : ℤ)-(d : ℤ))/2) else 0) =
        f (n - ((d / 2 : ℕ) : ℤ))
    have hm : (2*n+(r.val : ℤ)-(d : ℤ))%2=0 := by omega
    have hd : (2*n+(r.val : ℤ)-(d : ℤ))/2 = n - ((d / 2 : ℕ) : ℤ) := by omega
    rw [if_pos hm, hd]
  · rw [if_neg h]
    funext n
    change (if (2*n+(r.val : ℤ)-(d : ℤ))%2=0
      then f ((2*n+(r.val : ℤ)-(d : ℤ))/2) else 0) = 0
    have hm : (2*n+(r.val : ℤ)-(d : ℤ))%2 ≠ 0 := by omega
    rw [if_neg hm]

/-- The coefficient span of monomials of degree at most `B` times the first
`k` Frobenius powers. -/
private def window (g : Coefficients) (k B : ℕ) : Submodule (ZMod 2) Coefficients :=
  Submodule.span _ (Set.range fun i : Fin k × Fin (B+1) =>
    shift i.2.val (inflate g i.1.val))

private theorem generator_mem (g : Coefficients) {k B j d : ℕ} (hj : j < k) (hd : d ≤ B) :
    shift d (inflate g j) ∈ window g k B :=
  Submodule.subset_span ⟨(⟨j, hj⟩, ⟨d, by omega⟩), rfl⟩

private theorem cartier_shift_successor_mem (g : Coefficients)
    {k B j d : ℕ} (hj : j < k) (hd : d ≤ 2*B) (r : Fin 2) :
    cartier r (shift d (inflate g (j+1))) ∈ window g k B := by
  rw [inflate, cartier_shift_double]
  split_ifs
  · exact generator_mem g hj (by omega)
  · exact (window g k B).zero_mem

/-- If the base series is a polynomial combination of its positive Frobenius
powers with coefficient degrees at most `B`, the window of degree `B` is
stable under both Cartier operators. -/
private theorem window_stable (g : Coefficients) (k B : ℕ) (c : Fin k → Fin (B+1) → ZMod 2)
    (hrel : g = ∑ j : Fin k, ∑ d : Fin (B+1), c j d • shift d.val (inflate g (j.val+1)))
    (r : Fin 2) {f : Coefficients} (hf : f ∈ window g k B) :
    cartier r f ∈ window g k B := by
  classical
  let W := window g k B
  change f ∈ W at hf
  change cartier r f ∈ W
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨j, d⟩, rfl⟩ := hf
    change cartier r (shift d.val (inflate g j.val)) ∈ W
    have hd : d.val ≤ B := by omega
    rcases he : j.val with _ | j'
    · change cartier r (shift d.val g) ∈ W
      have ht := congrArg ((cartier r).comp (shift d.val)) hrel
      simp only [LinearMap.comp_apply, map_sum, map_smul, shift_shift] at ht
      rw [ht]
      refine W.sum_mem fun j _ => W.sum_mem fun e _ => W.smul_mem _ ?_
      exact cartier_shift_successor_mem g j.isLt (by have := e.isLt; omega) r
    · have hj' : j'<k := by have := j.isLt; omega
      exact cartier_shift_successor_mem g hj' (by omega) r
  | zero => simpa only [map_zero] using W.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ => simpa only [map_add] using W.add_mem h₁ h₂
  | smul a f _ hf => simpa only [map_smul] using W.smul_mem a hf

private theorem window_finite (g : Coefficients) (k B : ℕ) :
    (window g k B : Set Coefficients).Finite := by
  rw [window, ← Finsupp.range_linearCombination]
  exact Set.finite_range _

private theorem affine_mem_of_stable (W : Submodule (ZMod 2) Coefficients)
    (hW : ∀ (r : Fin 2) (f : Coefficients), f ∈ W → cartier r f ∈ W)
    (e r : ℕ) (hr : r < 2^e) (f : Coefficients) (hf : f ∈ W) :
    (fun n : ℤ => f ((2 : ℤ)^e*n+(r : ℤ))) ∈ W := by
  induction e generalizing r f with
  | zero =>
    have h0 : r = 0 := by simpa using hr
    simpa [h0] using hf
  | succ e ih =>
    have hr' : r / 2 < 2^e := by rw [pow_succ] at hr; omega
    let d : Fin 2 := ⟨r % 2, Nat.mod_lt _ (by decide)⟩
    have hm := ih (r / 2) hr' (cartier d f) (hW d f hf)
    convert hm using 1
    funext n
    change f ((2 : ℤ)^(e+1)*n+(r : ℤ)) =
      f (2*((2 : ℤ)^e*n+((r / 2 : ℕ) : ℤ))+(d.val : ℤ))
    congr 1
    have hpair : (2 : ℤ)*((r / 2 : ℕ) : ℤ) + ((r % 2 : ℕ) : ℤ) = (r : ℤ) := by
      exact_mod_cast (by omega : 2*(r / 2)+r % 2 = r)
    rw [pow_succ]
    change (2 : ℤ)^e*2*n+r = 2*(2^e*n+((r / 2 : ℕ) : ℤ))+((r % 2 : ℕ) : ℤ)
    linear_combination -hpair

/-- Every binary decimation of a sequence in a finite Cartier-stable space is
the natural-index restriction of a member of this same space. -/
private theorem binaryKernel_finite_of_stable (W : Submodule (ZMod 2) Coefficients)
    (hfinite : (W : Set Coefficients).Finite)
    (hW : ∀ (r : Fin 2) (f : Coefficients), f ∈ W → cartier r f ∈ W)
    (f : Coefficients) (hf : f ∈ W) :
    {g : ℕ → ZMod 2 | ∃ e r : ℕ, r < 2^e ∧ g = fun n => f ((2^e*n+r : ℕ) : ℤ)}.Finite := by
  refine (hfinite.image (fun (g : Coefficients) (n : ℕ) => g (n : ℤ))).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  refine ⟨_, affine_mem_of_stable W hW e r hr f hf, ?_⟩
  funext n
  push_cast
  rfl

private theorem binaryKernel_finite_of_relation (g : Coefficients) (k B : ℕ)
    (c : Fin k → Fin (B+1) → ZMod 2)
    (hrel : g = ∑ j : Fin k, ∑ d : Fin (B+1), c j d • shift d.val (inflate g (j.val+1)))
    (f : Coefficients) (hf : f ∈ window g k B) :
    {a : ℕ → ZMod 2 | ∃ e r : ℕ, r < 2^e ∧ a = fun n => f ((2^e*n+r : ℕ) : ℤ)}.Finite :=
  binaryKernel_finite_of_stable _ (window_finite g k B)
    (fun r _ h => window_stable g k B c hrel r h) f hf


end PartitionChristolWindow

open scoped LaurentSeries PowerSeries

namespace PartitionChristolLaurent

open PartitionChristolWindow

private abbrev K := ZMod 2
private abbrev L := LaurentSeries K

private theorem powerSeries_square (f : PowerSeries K) :
    f^2 = f.expand 2 (by decide) := by
  have h := MvPowerSeries.map_frobenius_expand 2 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

private theorem embedded_square_even (f : PowerSeries K) (n : ℤ) :
    ((f^2 : PowerSeries K) : L).coeff (2*n) = (f : L).coeff n := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [show (2 : ℤ)*(n : ℤ) = ((2*n : ℕ) : ℤ) by push_cast; rfl]
    change (HahnSeries.ofPowerSeries ℤ K (f^2)).coeff ((2*n : ℕ) : ℤ) =
      (HahnSeries.ofPowerSeries ℤ K f).coeff (n : ℤ)
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      powerSeries_square, PowerSeries.coeff_expand_mul]
  · have hn' : n < 0 := lt_of_not_ge hn
    rw [PowerSeries.coeff_coe, if_pos (show 2*n < 0 by omega),
      PowerSeries.coeff_coe, if_pos hn']

private theorem embedded_square_odd (f : PowerSeries K) (n : ℤ) :
    ((f^2 : PowerSeries K) : L).coeff (2*n+1) = 0 := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [show (2 : ℤ)*(n : ℤ)+1 = ((2*n+1 : ℕ) : ℤ) by push_cast; rfl]
    have hnot : ¬ 2 ∣ 2*n+1 := by omega
    change (HahnSeries.ofPowerSeries ℤ K (f^2)).coeff ((2*n+1 : ℕ) : ℤ) = 0
    rw [HahnSeries.ofPowerSeries_apply_coeff, powerSeries_square,
      PowerSeries.coeff_expand_of_not_dvd _ _ _ hnot]
  · have hn' : n < 0 := lt_of_not_ge hn
    rw [PowerSeries.coeff_coe, if_pos (show 2*n+1 < 0 by omega)]

/-- Squaring a Laurent series over F₂ doubles exponents and inserts zero
coefficients at odd indices, including negative indices. -/
private theorem coeff_square (f : L) : (f^2).coeff = double f.coeff := by
  let a := f.order
  let p := f.powerSeriesPart
  have hf : f = HahnSeries.single a 1 * (p : L) :=
    (LaurentSeries.single_order_mul_powerSeriesPart f).symm
  have hsq : f^2 = HahnSeries.single (2*a) 1 * ((p^2 : PowerSeries K) : L) := by
    calc
      f^2 = (HahnSeries.single a 1 * (p : L))^2 := congrArg (· ^ 2) hf
      _ = _ := by
        rw [mul_pow, pow_two (HahnSeries.single a (1 : K)), HahnSeries.single_mul_single,
          one_mul, two_mul, PowerSeries.coe_pow]
  funext n
  by_cases hn : n%2=0
  · rw [hsq, HahnSeries.coeff_single_mul, one_mul, double, if_pos hn]
    rw [show n-2*a=2*(n/2-a) by omega, embedded_square_even]
    conv_rhs => rw [hf, HahnSeries.coeff_single_mul, one_mul]
  · rw [hsq, HahnSeries.coeff_single_mul, one_mul, double, if_neg hn]
    rw [show n-2*a=2*(n/2-a)+1 by omega, embedded_square_odd]

private theorem coeff_frobenius_iterate (f : L) (j : ℕ) :
    (f^(2^j : ℕ)).coeff = inflate f.coeff j := by
  induction j with
  | zero => simp [inflate]
  | succ j ih => rw [pow_succ (2 : ℕ), pow_mul, coeff_square, ih, inflate]

private theorem polynomial_monomial_laurent (n : ℕ) (c : K) :
    algebraMap (Polynomial K) L (Polynomial.monomial n c) =
      HahnSeries.single (n : ℤ) c := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  simp [HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]

/-- The coefficients of multiplication by a polynomial are a finite sum of
shifted sequences over its degree window. -/
private theorem coeff_polynomial_mul (P : Polynomial K) (f : L) {B : ℕ}
    (hB : P.natDegree ≤ B) :
    (algebraMap (Polynomial K) L P * f).coeff =
      ∑ d : Fin (B+1), P.coeff d.val • shift d.val f.coeff := by
  have hP : P = ∑ d : Fin (B+1), Polynomial.monomial d.val (P.coeff d.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (P.coeff n))]
    exact P.as_sum_range' _ (by omega)
  funext n
  nth_rw 1 [hP]
  simp only [map_sum, Finset.sum_mul, HahnSeries.coeff_sum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [polynomial_monomial_laurent, HahnSeries.coeff_single_mul]
  rfl

/-- A polynomial relation (f=sum_j P_j f^{2^{j+1}}), together with an
initial polynomial multiple, is sufficient for a finite binary kernel. -/
private theorem finite_kernel_of_normalized_relation (g : L) {k : ℕ} (hk : 0 < k)
    (P : Fin k → Polynomial K) (D : Polynomial K)
    (hrel : g = ∑ j : Fin k, algebraMap (Polynomial K) L (P j) * g^(2^(j.val+1) : ℕ)) :
    {a : ℕ → K | ∃ e r : ℕ, r < 2^e ∧
      a = fun n => (algebraMap (Polynomial K) L D * g).coeff ((2^e*n+r : ℕ) : ℤ)}.Finite := by
  classical
  let B := max D.natDegree (Finset.univ.sup fun j => (P j).natDegree)
  have hD : D.natDegree ≤ B := le_max_left _ _
  have hPi (j : Fin k) : (P j).natDegree ≤ B :=
    (Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j)).trans (le_max_right _ _)
  have hcoeff : g.coeff = ∑ j : Fin k, ∑ d : Fin (B+1),
      (P j).coeff d.val • shift d.val (inflate g.coeff (j.val+1)) := by
    have h := congrArg HahnSeries.coeff hrel
    have hsum : (∑ j : Fin k, algebraMap (Polynomial K) L (P j) * g^(2^(j.val+1) : ℕ)).coeff =
        ∑ j : Fin k, (algebraMap (Polynomial K) L (P j) * g^(2^(j.val+1) : ℕ)).coeff := by
      funext n
      simp [HahnSeries.coeff_sum]
    rw [hsum] at h
    simpa only [fun j => coeff_polynomial_mul (P j) (g^(2^(j.val+1) : ℕ)) (hPi j),
      coeff_frobenius_iterate] using h
  have hstart : (algebraMap (Polynomial K) L D * g).coeff ∈ window g.coeff k B := by
    rw [coeff_polynomial_mul D g hD]
    refine (window g.coeff k B).sum_mem fun d _ => (window g.coeff k B).smul_mem _ ?_
    exact Submodule.subset_span ⟨(⟨0, hk⟩, d), rfl⟩
  exact binaryKernel_finite_of_relation _ k B (fun j d => (P j).coeff d.val)
    hcoeff _ hstart

/-- Divide by a nonzero polynomial on the left of a Frobenius relation to
obtain a polynomial relation for the quotient with leading coefficient one. -/
private theorem finite_kernel_of_polynomial_relation (f : L) {k : ℕ} (hk : 0 < k)
    (D : Polynomial K) (hD : D ≠ 0) (P : Fin k → Polynomial K)
    (hrel : algebraMap (Polynomial K) L D * f =
       ∑ j : Fin k, algebraMap (Polynomial K) L (P j) * f^(2^(j.val+1) : ℕ)) :
    {a : ℕ → K | ∃ e r : ℕ, r < 2^e ∧
      a = fun n => f.coeff ((2^e*n+r : ℕ) : ℤ)}.Finite := by
  let d := algebraMap (Polynomial K) L D
  have hd : d ≠ 0 := by
    intro hzero
    apply hD
    apply Polynomial.algebraMap_hahnSeries_injective ℤ
    simpa only [map_zero] using hzero
  let g := f / d
  have hfg : d * g = f := by
    dsimp [g]
    rw [mul_comm d, div_mul_cancel₀ _ hd]
  let Q : Fin k → Polynomial K := fun j => P j * D^(2^(j.val+1)-2 : ℕ)
  have hnorm : g = ∑ j : Fin k, algebraMap (Polynomial K) L (Q j) * g^(2^(j.val+1) : ℕ) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d^2 * g = d * f := by rw [pow_two, mul_assoc, hfg]
      _ = ∑ j : Fin k, algebraMap (Polynomial K) L (P j) * f^(2^(j.val+1) : ℕ) := hrel
      _ = ∑ j : Fin k, d^2 * (algebraMap (Polynomial K) L (Q j) * g^(2^(j.val+1) : ℕ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        let E : ℕ := 2^(j.val+1)
        have hE : 2 ≤ E := by
          dsimp [E]
          rw [pow_succ]
          have h : 0 < (2:ℕ)^j.val := by positivity
          omega
        have hsplit : d^E = d^2 * d^(E-2) := by
          rw [← pow_add, show 2+(E-2) = E by omega]
        change algebraMap (Polynomial K) L (P j) * f^E =
          d^2 * (algebraMap (Polynomial K) L (P j * D^(E-2)) * g^E)
        rw [map_mul, map_pow, ← hfg, mul_pow]
        change algebraMap (Polynomial K) L (P j) * (d^E * g^E) =
          d^2 * (algebraMap (Polynomial K) L (P j) * d^(E-2) * g^E)
        rw [hsplit]
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hfin := finite_kernel_of_normalized_relation g hk Q D hnorm
  change {a : ℕ → K | ∃ e r : ℕ, r < 2^e ∧
      a = fun n => (d*g).coeff ((2^e*n+r : ℕ) : ℤ)}.Finite at hfin
  simpa only [hfg] using hfin


end PartitionChristolLaurent

namespace PartitionChristolPolynomialSplit

private abbrev K := ZMod 2

open Polynomial

/-- In characteristic two, the even and odd exponents of a polynomial provide
a unique expression as one square plus the variable times another square. -/
private theorem square_split (P : Polynomial K) :
    P = (P.contract 2)^2 + X*((P.divX).contract 2)^2 := by
  ext n
  rw [coeff_add]
  have hfirst : ((P.contract 2)^2).coeff n = if 2 ∣ n then P.coeff n else 0 := by
    rw [← ZMod.expand_card, coeff_expand (by decide : 0 < 2)]
    split_ifs with hn
    · rw [coeff_contract (by decide : 2 ≠ 0), Nat.div_mul_cancel hn]
    · rfl
  have hsecond : (X*((P.divX).contract 2)^2).coeff n =
      if 2 ∣ n then 0 else P.coeff n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_X_mul, ← ZMod.expand_card, coeff_expand (by decide : 0 < 2)]
      by_cases hn : 2 ∣ n
      · rw [if_pos hn, if_neg (show ¬ 2 ∣ n+1 by omega),
          coeff_contract (by decide : 2 ≠ 0), Nat.div_mul_cancel hn, coeff_divX]
      · rw [if_neg hn, if_pos (show 2 ∣ n+1 by omega)]
  rw [hfirst, hsecond]
  split_ifs <;> simp


end PartitionChristolPolynomialSplit

open scoped LaurentSeries RatFunc PowerSeries

namespace PartitionChristolLinearRelation

private abbrev K := ZMod 2
private abbrev L := LaurentSeries K
private abbrev Q := RatFunc K

/-- Algebraicity provides a finite linear dependence among Frobenius powers,
with polynomial coefficients after clearing denominators. -/
private theorem exists_polynomial_dependence (f : L) (hf : IsAlgebraic Q f) :
    ∃ n : ℕ, ∃ C : Fin n → Polynomial K,
      (∃ i, C i ≠ 0) ∧
      ∑ i : Fin n, algebraMap (Polynomial K) L (C i) * f^(2^i.val : ℕ) = 0 := by
  classical
  let E := IntermediateField.adjoin Q {f}
  let : FiniteDimensional Q E := IntermediateField.adjoin.finiteDimensional hf.isIntegral
  let θ : E := ⟨f, IntermediateField.subset_adjoin Q {f} (by simp)⟩
  let n := Module.finrank Q E + 1
  let v (i : Fin n) : E := θ^(2^i.val : ℕ)
  have hnli : ¬ LinearIndependent Q v := by
    intro h
    have hcard := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    dsimp [n] at hcard
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
  have hlin : ∑ j : Fin n, algebraMap Q L (c j) * f^(2^j.val : ℕ) = 0 := by
    let incl : E →ₗ[Q] L := E.val.toLinearMap
    have h := congrArg incl hc
    rw [map_sum, map_zero] at h
    have hval (j : Fin n) : incl (c j • v j) =
        algebraMap Q L (c j) * f^(2^j.val : ℕ) := by
      rw [incl.map_smul, Algebra.smul_def]
      change algebraMap Q L (c j) * E.val (θ^(2^j.val : ℕ)) = _
      rw [map_pow]
      rfl
    simpa only [hval] using h
  let D : Polynomial K := ∏ j : Fin n, (c j).denom
  let C (j : Fin n) : Polynomial K :=
    (c j).num * ∏ t ∈ Finset.univ.erase j, (c t).denom
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => RatFunc.denom_ne_zero (c j))
  have hfactor (j : Fin n) :
      D = (c j).denom * ∏ t ∈ Finset.univ.erase j, (c t).denom :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have hcQ (j : Fin n) : algebraMap (Polynomial K) Q (C j) =
      algebraMap (Polynomial K) Q D * c j := by
    have hmul : algebraMap (Polynomial K) Q (c j).denom * c j =
        algebraMap (Polynomial K) Q (c j).num := by
      have hd := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (c j))
      conv_lhs =>
        arg 2
        rw [← RatFunc.num_div_denom (c j)]
      rw [mul_comm, div_mul_cancel₀ _ hd]
    dsimp [C]
    rw [hfactor j, map_mul, map_mul]
    linear_combination -(algebraMap (Polynomial K) Q
      (∏ t ∈ Finset.univ.erase j, (c t).denom)) * hmul
  have hiC : C i ≠ 0 := by
    intro hz
    have h := hcQ i
    rw [hz, map_zero] at h
    exact (mul_ne_zero (RatFunc.algebraMap_ne_zero hD) hi) h.symm
  refine ⟨n, C, ⟨i, hiC⟩, ?_⟩
  have hcL (j : Fin n) : algebraMap (Polynomial K) L (C j) =
      algebraMap (Polynomial K) L D * algebraMap Q L (c j) := by
    have h := congrArg (algebraMap Q L) (hcQ j)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply (Polynomial K) Q L] using h
  simp_rw [hcL, mul_assoc, ← Finset.mul_sum, hlin, mul_zero]


end PartitionChristolLinearRelation

open scoped LaurentSeries RatFunc PowerSeries

namespace PartitionChristolNecessity

open PartitionChristolLaurent
open PartitionChristolWindow

private abbrev Q := RatFunc K

private theorem two_square_components_zero (A B : L)
    (h : A^2 + HahnSeries.single (1 : ℤ) 1 * B^2 = 0) :
    A = 0 ∧ B = 0 := by
  constructor
  · apply HahnSeries.ext
    funext n
    have hc := congrArg (fun f : L => f.coeff (2*n)) h
    change (A^2 + HahnSeries.single (1 : ℤ) 1 * B^2).coeff (2*n) = 0 at hc
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_mul, one_mul, coeff_square A,
      coeff_square B, double, double, if_pos (show (2*n)%2=0 by omega),
      if_neg (show (2*n-1)%2≠0 by omega), add_zero,
      show (2*n)/2=n by omega] at hc
    exact hc
  · apply HahnSeries.ext
    funext n
    have hc := congrArg (fun f : L => f.coeff (2*n+1)) h
    change (A^2 + HahnSeries.single (1 : ℤ) 1 * B^2).coeff (2*n+1) = 0 at hc
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_mul, one_mul, coeff_square A,
      coeff_square B, double, double, if_neg (show (2*n+1)%2≠0 by omega),
      show 2*n+1-1=2*n by omega, if_pos (show (2*n)%2=0 by omega),
      zero_add, show (2*n)/2=n by omega] at hc
    exact hc

private def HasDependence (f : L) (n : ℕ) : Prop :=
  ∃ C : Fin n → Polynomial K,
    (∃ i, C i ≠ 0) ∧
    ∑ i : Fin n, algebraMap (Polynomial K) L (C i) * f^(2^i.val : ℕ) = 0

private theorem smaller_dependence (f : L) {n : ℕ} (C : Fin (n+1) → Polynomial K)
    (hnz : ∃ i, C i ≠ 0) (hzero : C 0 = 0)
    (hrel : ∑ i : Fin (n+1), algebraMap (Polynomial K) L (C i) * f^(2^i.val : ℕ) = 0) :
    HasDependence f n := by
  classical
  let E (i : Fin n) := (C i.succ).contract 2
  let O (i : Fin n) := (C i.succ).divX.contract 2
  let a (i : Fin n) : L := algebraMap (Polynomial K) L (E i) * f^(2^i.val : ℕ)
  let b (i : Fin n) : L := algebraMap (Polynomial K) L (O i) * f^(2^i.val : ℕ)
  have htail : ∑ i : Fin n, algebraMap (Polynomial K) L (C i.succ) *
      f^(2^(i.val+1) : ℕ) = 0 := by
    simpa only [Fin.sum_univ_succ, hzero, map_zero, zero_mul, zero_add, Fin.val_succ] using hrel
  have hterm (i : Fin n) : algebraMap (Polynomial K) L (C i.succ) *
      f^(2^(i.val+1) : ℕ) =
      (a i)^2 + HahnSeries.single (1 : ℤ) 1 * (b i)^2 := by
    have hs := congrArg (algebraMap (Polynomial K) L)
      (PartitionChristolPolynomialSplit.square_split (C i.succ))
    rw [map_add, map_mul, map_pow, map_pow, Polynomial.algebraMap_hahnSeries_apply
      (Γ := ℤ) (Polynomial.X : Polynomial K), Polynomial.coe_X, HahnSeries.ofPowerSeries_X] at hs
    change algebraMap (Polynomial K) L (C i.succ) =
      (algebraMap (Polynomial K) L (E i))^2 +
        HahnSeries.single (1 : ℤ) 1 * (algebraMap (Polynomial K) L (O i))^2 at hs
    rw [hs, pow_succ (2 : ℕ), pow_mul]
    dsimp [a, b]
    rw [mul_pow, mul_pow]
    ring
  have hs : (∑ i : Fin n, a i)^2 +
      HahnSeries.single (1 : ℤ) 1 * (∑ i : Fin n, b i)^2 = 0 := by
    let : ExpChar L 2 := expChar_of_injective_ringHom (algebraMap K L).injective 2
    rw [sum_pow_char 2, sum_pow_char 2, Finset.mul_sum, ← Finset.sum_add_distrib]
    simpa only [← hterm] using htail
  obtain ⟨he, ho⟩ := two_square_components_zero _ _ hs
  by_cases hE : ∃ i, E i ≠ 0
  · exact ⟨E, hE, he⟩
  by_cases hO : ∃ i, O i ≠ 0
  · exact ⟨O, hO, ho⟩
  exfalso
  obtain ⟨i, hi⟩ := hnz
  cases i using Fin.cases with
  | zero => exact hi hzero
  | succ i =>
    have hs := PartitionChristolPolynomialSplit.square_split (C i.succ)
    change C i.succ = (E i)^2 + Polynomial.X*(O i)^2 at hs
    rw [show E i = 0 from not_not.mp (fun hn => hE ⟨i, hn⟩),
      show O i = 0 from not_not.mp (fun hn => hO ⟨i, hn⟩)] at hs
    exact hi (by simpa using hs)

/-- A shortest nonzero dependence has a nonzero coefficient at the first
Frobenius level. Otherwise the even and odd polynomial parts each descend
one level, and at least one remains a nonzero dependence. -/
private theorem polynomial_frobenius_relation (f : L) (hf : IsAlgebraic Q f) :
    ∃ k : ℕ, 0 < k ∧ ∃ D : Polynomial K, D ≠ 0 ∧ ∃ P : Fin k → Polynomial K,
      algebraMap (Polynomial K) L D * f =
        ∑ i : Fin k, algebraMap (Polynomial K) L (P i) * f^(2^(i.val+1) : ℕ) := by
  classical
  by_cases h0 : f = 0
  · exact ⟨1, by decide, 1, one_ne_zero, fun _ => 0, by simp [h0]⟩
  have hex : ∃ n, HasDependence f n :=
    PartitionChristolLinearRelation.exists_polynomial_dependence f hf
  obtain ⟨m, hm, hmin⟩ : ∃ m, HasDependence f m ∧
      ∀ n < m, ¬ HasDependence f n :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩
  obtain ⟨C, hC, hsum⟩ := hm
  cases m with
  | zero =>
    obtain ⟨i, _⟩ := hC
    exact Fin.elim0 i
  | succ k =>
    have hC0 : C 0 ≠ 0 := by
      intro hz
      exact hmin k (by omega) (smaller_dependence f C hC hz hsum)
    have hk : 0 < k := by
      by_contra! h
      have hk0 : k = 0 := by omega
      subst k
      have hz : algebraMap (Polynomial K) L (C 0) * f = 0 := by simpa using hsum
      have hn : algebraMap (Polynomial K) L (C 0) ≠ 0 := by
        intro hz
        apply hC0
        apply Polynomial.algebraMap_hahnSeries_injective ℤ
        simpa only [map_zero] using hz
      exact (mul_ne_zero hn h0) hz
    refine ⟨k, hk, C 0, hC0, fun i => -C i.succ, ?_⟩
    rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, pow_one] at hsum
    simp only [map_neg, neg_mul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hsum

/-- Christol's necessary direction, specialized to the binary coefficients
of a formal power series viewed in the Laurent series field. -/
private theorem finite_binary_kernel (a : ℕ → K)
    (ha : IsAlgebraic Q ((PowerSeries.mk a : PowerSeries K) : L)) :
    {g : ℕ → K | ∃ e r : ℕ, r < 2^e ∧ g = fun n => a (2^e*n+r)}.Finite := by
  let f : L := (PowerSeries.mk a : PowerSeries K)
  obtain ⟨k, hk, D, hD, P, hP⟩ := polynomial_frobenius_relation f ha
  have h := finite_kernel_of_polynomial_relation f hk D hD P hP
  have hcoeff (n : ℕ) : f.coeff (n : ℤ) = a n :=
    (HahnSeries.ofPowerSeries_apply_coeff (PowerSeries.mk a) n).trans (PowerSeries.coeff_mk n a)
  simpa only [hcoeff] using h


end PartitionChristolNecessity

open Finset

private def quadraticLambert (D : ℕ) (a : ℕ → ZMod 2) (k : ℕ) : ZMod 2 :=
  ∑ m ∈ k.divisors, if m.Coprime 6 ∧ (k / m).Coprime D then a m else 0

private theorem quadraticLambert_identifies_admissible {D : ℕ} {a b : ℕ → ZMod 2}
    (h : quadraticLambert D a = quadraticLambert D b) :
    ∀ m : ℕ, m.Coprime 6 → a m = b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    have hmpos : 0 < m := by
      by_contra! hm0
      have hmzero : m = 0 := by omega
      subst m
      exact (by decide : ¬ Nat.Coprime 0 6) hm
    have hd : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hmpos.ne'⟩
    let f (c : ℕ → ZMod 2) (k : ℕ) :=
      if k.Coprime 6 ∧ (m / k).Coprime D then c k else 0
    have hsum : ∑ k ∈ m.divisors.erase m, f a k = ∑ k ∈ m.divisors.erase m, f b k := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hne, hk'⟩ := mem_erase.mp hk
      have hlt := lt_of_le_of_ne (Nat.le_of_dvd hmpos (Nat.mem_divisors.mp hk').1) hne
      by_cases hc : k.Coprime 6 ∧ (m / k).Coprime D
      · simp only [f, if_pos hc]
        exact ih k hlt hc.1
      · simp only [f, if_neg hc]
    have hself (c : ℕ → ZMod 2) : f c m = c m := by
      have hcond : m.Coprime 6 ∧ (m / m).Coprime D :=
        ⟨hm, by rw [Nat.div_self hmpos]; exact Nat.coprime_one_left D⟩
      simp only [f, if_pos hcond]
    have atIndex : ∑ k ∈ m.divisors, f a k = ∑ k ∈ m.divisors, f b k :=
      congrFun h m
    rw [← sum_erase_add _ _ hd, ← sum_erase_add _ _ hd, hsum, hself, hself] at atIndex
    exact add_left_cancel atIndex

open scoped LaurentSeries PowerSeries IntermediateField.algebraAdjoinAdjoin

namespace PartitionQuadraticExchange

private theorem exchange {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}
    (hx : ¬ IsAlgebraic K x) (h : IsAlgebraic (IntermediateField.adjoin K {y}) x) :
    IsAlgebraic (IntermediateField.adjoin K {x}) y := by
  let M := AlgebraicIndependent.matroid K L
  have hnot : x ∉ M.closure ∅ := by
    change x ∉ (AlgebraicIndependent.matroid K L).closure ∅
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe,
      Subalgebra.mem_algebraicClosure, Algebra.adjoin_empty,
      Subalgebra.isAlgebraic_bot_iff (FaithfulSMul.algebraMap_injective K L)]
    exact hx
  have hmem : x ∈ M.closure (insert y ∅) := by
    simpa [M, AlgebraicIndependent.matroid_closure_eq, Subalgebra.mem_algebraicClosure] using
      (IsFractionRing.isAlgebraic_iff (Algebra.adjoin K {y})
        (IntermediateField.adjoin K {y}) L).mpr h
  have hy := Matroid.mem_closure_insert hnot hmem
  exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin K {x})
    (IntermediateField.adjoin K {x}) L).mp (by
      simpa [M, AlgebraicIndependent.matroid_closure_eq, Subalgebra.mem_algebraicClosure] using hy)

private theorem not_algebraic_of_order_pos {K : Type*} [Field K] [Finite K] {x : K⸨X⸩}
    (hx : x ≠ 0) (horder : 0 < x.order) : ¬ IsAlgebraic K x := by
  classical
  intro h
  let E := IntermediateField.adjoin K {x}
  let : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional h.isIntegral
  let : Finite E := Module.finite_of_finite K
  let : Fintype E := Fintype.ofFinite E
  let y : E := ⟨x, IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
  have hy : y ≠ 0 := by
    intro hy
    exact hx (congrArg Subtype.val hy)
  have hpow : x ^ (Fintype.card E - 1) = 1 := by
    simpa [y] using congrArg (algebraMap E K⸨X⸩) (FiniteField.pow_card_sub_one_eq_one y hy)
  have hcard : 1 < Fintype.card E := Fintype.one_lt_card
  have e := congrArg HahnSeries.order hpow
  rw [HahnSeries.order_pow, HahnSeries.order_one, nsmul_eq_mul] at e
  have hpos : (0 : ℤ) < (Fintype.card E - 1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hcard
  exact (ne_of_gt (mul_pos hpos horder)) e

private theorem of_mk_ne_zero_and_const_zero {K : Type*} [Field K] [Finite K] {a : ℕ → K}
    (h0 : a 0 = 0) (ha : ∃ n, a n ≠ 0) : ¬ IsAlgebraic K (PowerSeries.mk a : K⸨X⸩) := by
  let x : K⸨X⸩ := PowerSeries.mk a
  obtain ⟨n, hn⟩ := ha
  have hx : x ≠ 0 := by
    intro he
    apply hn
    have ht := congrArg (fun z : K⸨X⸩ => z.coeff n) he
    simpa [x] using ht
  refine not_algebraic_of_order_pos hx ?_
  have hcoe : ∀ i : ℤ, i ≤ 0 → x.coeff i = 0 := by
    intro i hi
    obtain rfl | hi := hi.eq_or_lt'
    · simpa [x, PowerSeries.coeff_coe] using h0
    · simp [x, PowerSeries.coeff_coe, hi]
  by_contra! hi
  exact hx (HahnSeries.coeff_order_eq_zero.mp (hcoe x.order hi))

end PartitionQuadraticExchange

open Finset

namespace PartitionEisensteinComparison

private def levelSix (n : ℕ) : ZMod 2 :=
  ∑ m ∈ n.divisors, if m.Coprime 6 then 1 else 0

private def levelSixD (D n : ℕ) : ZMod 2 :=
  ∑ d ∈ D.divisors, if d ∣ n then levelSix (n / d) else 0

private theorem cast_divisors_card {g : ℕ} (hg : Squarefree g) :
    (g.divisors.card : ZMod 2) = if g = 1 then 1 else 0 := by
  by_cases h : g = 1
  · simp [h]
  · simp only [h, if_false]
    rw [Nat.card_divisors hg.ne_zero, Nat.cast_prod]
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
    have hp' : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, hg.ne_zero⟩
    apply Finset.prod_eq_zero hp'
    rw [Nat.factorization_eq_one_of_squarefree hg hp hd]
    decide

/-- Oldform filtering gives the coprime second-index restriction in (4.4). -/
private theorem levelSixD_eq {D : ℕ} (hD : Squarefree D) (n : ℕ) :
    levelSixD D n =
      ∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n / m).Coprime D then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn, levelSixD, levelSix]
  unfold levelSixD
  calc
    _ = ∑ d ∈ D.divisors, ∑ m ∈ n.divisors,
          if m.Coprime 6 ∧ d ∣ n / m then (1 : ZMod 2) else 0 := by
      refine sum_congr rfl fun d hd ↦ ?_
      by_cases h : d ∣ n
      · rw [if_pos h]
        have hquot : n / d ≠ 0 := ne_of_gt
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) (Nat.pos_of_mem_divisors hd))
        have hs : n.divisors.filter (fun m => d ∣ n / m) = (n / d).divisors := by
          ext m
          simp only [mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨hm, hm'⟩
            refine ⟨(Nat.dvd_div_iff_mul_dvd h).mpr ?_, hquot⟩
            simpa [mul_comm] using (Nat.dvd_div_iff_mul_dvd hm.1).mp hm'
          · intro hm
            have hh := (Nat.dvd_div_iff_mul_dvd h).mp hm.1
            have hmn : m ∣ n := dvd_trans (dvd_mul_left m d) hh
            exact ⟨⟨hmn, hn⟩, (Nat.dvd_div_iff_mul_dvd hmn).mpr
                (by simpa [mul_comm] using hh)⟩
        rw [levelSix, ← hs, sum_filter]
        refine sum_congr rfl fun m hm ↦ ?_
        by_cases h₁ : m.Coprime 6 <;> by_cases h₂ : d ∣ n / m <;> simp [h₁, h₂]
      · rw [if_neg h]
        symm
        refine sum_eq_zero fun m hm ↦ if_neg fun h' ↦ h ?_
        exact dvd_trans h'.2 (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hm))
    _ = ∑ m ∈ n.divisors, ∑ d ∈ D.divisors,
          if m.Coprime 6 ∧ d ∣ n / m then (1 : ZMod 2) else 0 := sum_comm
    _ = ∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n / m).Coprime D then (1 : ZMod 2) else 0 := by
      refine sum_congr rfl fun m hm ↦ ?_
      by_cases hc : m.Coprime 6
      · have he (q : Prop) : (m.Coprime 6 ∧ q) ↔ q := and_iff_right hc
        simp_rw [he]
        let g := Nat.gcd D (n / m)
        have hg : Squarefree g := hD.squarefree_of_dvd (Nat.gcd_dvd_left ..)
        have hfilter : D.divisors.filter (fun d => d ∣ n / m) = g.divisors := by
          rw [← Nat.divisors_filter_dvd_of_dvd hD.ne_zero (Nat.gcd_dvd_left D (n / m))]
          ext d
          simp only [mem_filter, Nat.dvd_gcd_iff]
          constructor
          · rintro ⟨hd, hd'⟩
            exact ⟨hd, Nat.dvd_of_mem_divisors hd, hd'⟩
          · rintro ⟨hd, _, hd'⟩
            exact ⟨hd, hd'⟩
        rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul, mul_one,
          cast_divisors_card hg]
        exact if_congr (show D.Coprime (n / m) ↔ (n / m).Coprime D from Nat.coprime_comm)
          rfl rfl
      · rw [if_neg (fun h => hc h.1)]
        exact sum_eq_zero fun d hd => if_neg (fun h => hc h.1)

end PartitionEisensteinComparison

open Finset

namespace PartitionEisensteinComparison

private theorem cast_divisor_sum (n : ℕ) :
    (∑ m ∈ n.divisors, (m : ZMod 2)) =
      ((n.divisors.filter (fun m => ¬ 2 ∣ m)).card : ZMod 2) := by
  calc
    _ = ∑ m ∈ n.divisors, if ¬ 2 ∣ m then (1 : ZMod 2) else 0 := by
      refine sum_congr rfl fun m hm ↦ ?_
      by_cases h : 2 ∣ m
      · have he : Even m := even_iff_two_dvd.mpr h
        rw [if_neg (not_not_intro h), he.natCast_zmod_two]
      · have ho : Odd m := Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp h)
        rw [if_pos h, ho.natCast_zmod_two]
    _ = _ := by rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

private theorem odd_multiple_three_count (n : ℕ) (hn : n ≠ 0) (h3 : 3 ∣ n) :
    ((n / 3).divisors.filter (fun m => ¬ 2 ∣ m)).card =
      (n.divisors.filter (fun m => ¬ 2 ∣ m ∧ 3 ∣ m)).card := by
  refine card_bij (fun m _ ↦ 3 * m) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm, hodd⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, ?_, dvd_mul_right 3 m⟩
    · exact (Nat.dvd_div_iff_mul_dvd h3).mp (Nat.dvd_of_mem_divisors hm)
    · exact fun he ↦ hodd ((Nat.prime_two.dvd_mul.mp he).resolve_left (by decide))
  · intro a _ b _ he
    omega
  · intro k hk
    obtain ⟨hk, hk2, hk3⟩ := mem_filter.mp hk
    obtain ⟨m, rfl⟩ := hk3
    have hquot : n / 3 ≠ 0 :=
      ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h3) (by decide))
    refine ⟨m, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hquot⟩, ?_⟩, rfl⟩
    · exact (Nat.dvd_div_iff_mul_dvd h3).mpr (Nat.dvd_of_mem_divisors hk)
    · exact fun he ↦ hk2 (dvd_trans he (dvd_mul_left m 3))

/-- The reduction of the level-six Eisenstein coefficient in (4.1) is (4.2).
The terms involving (4σ_1(n/2)) vanish in characteristic two. -/
private theorem levelSix_sigma (n : ℕ) :
    (∑ m ∈ n.divisors, (m : ZMod 2)) +
      (if 3 ∣ n then ∑ m ∈ (n / 3).divisors, (m : ZMod 2) else 0) =
        ∑ m ∈ n.divisors, if m.Coprime 6 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hcop (m : ℕ) : m.Coprime 6 ↔ ¬ 2 ∣ m ∧ ¬ 3 ∣ m := by
    rw [show 6 = 2 * 3 by decide, Nat.coprime_mul_iff_right,
      show m.Coprime 2 ↔ Nat.Coprime 2 m from Nat.coprime_comm,
      show m.Coprime 3 ↔ Nat.Coprime 3 m from Nat.coprime_comm,
      Nat.prime_two.coprime_iff_not_dvd, Nat.prime_three.coprime_iff_not_dvd]
  have hlevel :
      (∑ m ∈ n.divisors, if m.Coprime 6 then (1 : ZMod 2) else 0) =
      ((n.divisors.filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m)).card : ZMod 2) := by
    simp only [hcop, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsplit :
      (n.divisors.filter (fun m => ¬ 2 ∣ m ∧ 3 ∣ m)).card +
        (n.divisors.filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m)).card =
      (n.divisors.filter (fun m => ¬ 2 ∣ m)).card := by
    simpa only [filter_filter] using
      (card_filter_add_card_filter_not (s := n.divisors.filter (fun m => ¬ 2 ∣ m))
        (p := fun m => 3 ∣ m))
  have ht :
      (if 3 ∣ n then ∑ m ∈ (n / 3).divisors, (m : ZMod 2) else 0) =
        ((n.divisors.filter (fun m => ¬ 2 ∣ m ∧ 3 ∣ m)).card : ZMod 2) := by
    by_cases h3 : 3 ∣ n
    · rw [if_pos h3, cast_divisor_sum, odd_multiple_three_count n hn h3]
    · rw [if_neg h3]
      have he : n.divisors.filter (fun m => ¬ 2 ∣ m ∧ 3 ∣ m) = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun m hm ↦ h3 ?_
        obtain ⟨hm, _, hm3⟩ := mem_filter.mp hm
        exact dvd_trans hm3 (Nat.dvd_of_mem_divisors hm)
      rw [he, card_empty, Nat.cast_zero]
  rw [cast_divisor_sum, ht, hlevel, ← hsplit, Nat.cast_add, add_right_comm]
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

end PartitionEisensteinComparison

open scoped LaurentSeries RatFunc PowerSeries

namespace PartitionComplementRational

/-- Algebraicity over the field generated by one element transfers to the
rational function field whenever that element is itself rational. -/
private theorem algebraic_over_ratfunc_of_rational_generator {K : Type*} [Field K]
    {x y : K⸨X⸩} {f : RatFunc K} (hf : (f : K⸨X⸩) = x)
    (h : IsAlgebraic (IntermediateField.adjoin K {x}) y) :
    IsAlgebraic (RatFunc K) y := by
  let ι : RatFunc K →ₐ[K] K⸨X⸩ :=
    { toRingHom := algebraMap (RatFunc K) K⸨X⸩
      commutes' := fun a => by
        symm
        calc
          algebraMap K K⸨X⸩ a = algebraMap (Polynomial K) K⸨X⸩
              (algebraMap K (Polynomial K) a) := by
                simp [HahnSeries.algebraMap_apply' ℤ, PowerSeries.algebraMap_apply']
          _ = algebraMap (RatFunc K) K⸨X⸩ (algebraMap (Polynomial K) (RatFunc K)
              (algebraMap K (Polynomial K) a)) :=
                IsScalarTower.algebraMap_apply (Polynomial K) _ _ _
          _ = _ := by
            rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
            rfl }
  let S := IntermediateField.adjoin K {x}
  have hs : S ≤ ι.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨f, hf⟩)
  let e : S →+* RatFunc K :=
    ι.equivFieldRange.symm.toRingHom.comp (IntermediateField.inclusion hs).toRingHom
  have he : (algebraMap (RatFunc K) K⸨X⸩).comp e =
      (RingHom.id K⸨X⸩).comp (algebraMap S K⸨X⸩) := by
    ext1 s
    change ι (ι.equivFieldRange.symm (IntermediateField.inclusion hs s)) = (s : K⸨X⸩)
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  exact h.ringHom_of_comp_eq e (RingHom.id K⸨X⸩) e.injective he

end PartitionComplementRational

/- The modular algebraicity inputs imply nonperiodicity of the complementary Lambert series. -/

open scoped LaurentSeries RatFunc PowerSeries

namespace OMA.R_PartitionParity_ono_swaminathan_quadratic_R2_H2_R1

open Nat Finset PartitionSquareKernel

/-- Algebraicity of the mod-two Borcherds Lambert series over the field
generated by the inverse modular invariant. -/
def H1 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
  let A : PowerSeries (ZMod 2) := PowerSeries.mk fun n =>
    ∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n / m).Coprime D then
      (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2) else 0
  let J : PowerSeries (ZMod 2) := by
    classical
    exact PowerSeries.mk fun n => if Odd n ∧ IsSquare n then 1 else 0
  IsAlgebraic (IntermediateField.adjoin (ZMod 2) {(J : (ZMod 2)⸨X⸩)})
    (A : (ZMod 2)⸨X⸩)

/-- Algebraicity of Ono and Swaminathan's level-six Eisenstein oldform sum
over the same inverse-invariant field. The inner coefficient is the
reduction of equation (4.1), and the outer sum is (4.3). -/
def H2 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
  let E : PowerSeries (ZMod 2) := PowerSeries.mk fun n =>
    ∑ d ∈ D.divisors, if d ∣ n then
      (∑ m ∈ (n / d).divisors, (m : ZMod 2)) +
        (if 3 ∣ n / d then ∑ m ∈ (n / d / 3).divisors, (m : ZMod 2) else 0)
    else 0
  let J : PowerSeries (ZMod 2) := by
    classical
    exact PowerSeries.mk fun n => if Odd n ∧ IsSquare n then 1 else 0
  IsAlgebraic (IntermediateField.adjoin (ZMod 2) {(J : (ZMod 2)⸨X⸩)})
    (E : (ZMod 2)⸨X⸩)

/-- An even value supplied by the surviving CM pole and regularity of the
Eisenstein comparison in Ono and Swaminathan, §4.2. -/
def H3 : Prop := ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
  ∃ m : ℕ, m.Coprime 6 ∧ Even (partitionNumber ((D * m ^ 2 + 1) / 24))

/-- The inverse invariant trivializes the differential $dq/q$ at the cusp. -/
theorem inverseInvariant_derivative :
    (PowerSeries.X : PowerSeries (ZMod 2)) *
      PowerSeries.derivative (ZMod 2) (PowerSeries.mk oddSquareSequence) =
      PowerSeries.mk oddSquareSequence := by
  rw [PartitionOddSquareExpansion.oddSquareSeries_eq_X_mul_triangle_pow,
    Derivation.leibniz, PowerSeries.derivative_X, PowerSeries.derivative_pow,
    show ((8 : ℕ) : PowerSeries (ZMod 2)) = 0 by
      simpa only [map_natCast, map_zero] using
        congrArg PowerSeries.C (show ((8 : ℕ) : ZMod 2) = 0 by decide)]
  simp [smul_eq_mul, mul_comm]

private theorem complement_coeff {D : ℕ} (hD : Squarefree D) (a : ℕ → ZMod 2) (n : ℕ) :
    quadraticLambert D (fun m => 1 - a m) n =
      PartitionEisensteinComparison.levelSixD D n - quadraticLambert D a n := by
  rw [PartitionEisensteinComparison.levelSixD_eq hD]
  simp only [quadraticLambert, ← sum_sub_distrib]
  exact sum_congr rfl fun m _ ↦ by
    by_cases hm : m.Coprime 6 ∧ (n / m).Coprime D
    · simp only [if_pos hm]
    · simp only [if_neg hm, sub_zero]

private theorem complement_nonzero {D : ℕ} {a : ℕ → ZMod 2}
    {m : ℕ} (hm : m.Coprime 6) (ha : a m = 0) :
    ∃ n : ℕ, quadraticLambert D (fun j => 1 - a j) n ≠ 0 := by
  by_contra! hz
  have he : quadraticLambert D (fun j => 1 - a j) =
      quadraticLambert D (fun _ => 0) := by
    funext n
    rw [hz]
    simp [quadraticLambert]
  have ht := quadraticLambert_identifies_admissible he m hm
  simp [ha] at ht

theorem main : H1 → H2 → H3 → OMA.R_PartitionParity_ono_swaminathan_quadratic_R2.H2 := by
  intro hB hE hEven D hD hsf h23 P hP
  by_contra! hperiod
  let a : ℕ → ZMod 2 := fun m => (partitionNumber ((D * m ^ 2 + 1) / 24) : ZMod 2)
  let f : ℕ → ZMod 2 := quadraticLambert D (fun m => 1 - a m)
  let J : (ZMod 2)⸨X⸩ := PowerSeries.mk oddSquareSequence
  let L := IntermediateField.adjoin (ZMod 2) {J}
  obtain ⟨R, hR⟩ := PartitionPeriodicSeries.ratFunc_of_periodic_positive f hP hperiod
  obtain ⟨m, hm, hEvenm⟩ := hEven D hD hsf h23
  have hnonalg : ¬ IsAlgebraic (ZMod 2) (PowerSeries.mk f : (ZMod 2)⸨X⸩) :=
    PartitionQuadraticExchange.of_mk_ne_zero_and_const_zero (by simp [f, quadraticLambert])
      (complement_nonzero hm hEvenm.natCast_zmod_two)
  have hcomplement : (PowerSeries.mk f : (ZMod 2)⸨X⸩) =
      (PowerSeries.mk (PartitionEisensteinComparison.levelSixD D) : (ZMod 2)⸨X⸩) -
        (PowerSeries.mk (quadraticLambert D a) : (ZMod 2)⸨X⸩) := by
    rw [← PowerSeries.coe_sub]
    congr 1
    apply PowerSeries.ext
    intro n
    simp only [map_sub, PowerSeries.coeff_mk]
    exact complement_coeff hsf a n
  have halg : IsAlgebraic L (PowerSeries.mk f : (ZMod 2)⸨X⸩) := by
    rw [hcomplement]
    have hE' : IsAlgebraic L
        (PowerSeries.mk (PartitionEisensteinComparison.levelSixD D) : (ZMod 2)⸨X⸩) := by
      change IsAlgebraic L ((PowerSeries.mk fun n =>
        ∑ d ∈ D.divisors, if d ∣ n then
          ∑ m ∈ (n / d).divisors, if m.Coprime 6 then (1 : ZMod 2) else 0
        else 0) : (ZMod 2)⸨X⸩)
      have h := hE D hD hsf h23
      simp only [PartitionEisensteinComparison.levelSix_sigma] at h
      exact h
    have hB' : IsAlgebraic L (PowerSeries.mk (quadraticLambert D a) : (ZMod 2)⸨X⸩) :=
      hB D hD hsf h23
    exact (hE'.isIntegral.sub hB'.isIntegral).isAlgebraic
  have hJ := PartitionQuadraticExchange.exchange hnonalg halg
  have hrational := PartitionComplementRational.algebraic_over_ratfunc_of_rational_generator hR hJ
  exact oddSquareSequence_binaryKernel_infinite
    (PartitionChristolNecessity.finite_binary_kernel oddSquareSequence hrational)

end OMA.R_PartitionParity_ono_swaminathan_quadratic_R2_H2_R1
