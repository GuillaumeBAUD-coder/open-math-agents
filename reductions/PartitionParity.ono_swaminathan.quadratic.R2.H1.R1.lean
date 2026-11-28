import OMAReductions.R_PartitionParity_ono_swaminathan_quadratic_R2
import Mathlib

/-!
# Nonperiodicity of the odd partition Lambert series

The modular input uses Ono and Swaminathan's surviving pole in §4.1 of
<https://arxiv.org/html/2509.09553v4>. The arithmetic input is the necessary
direction of Christol's theorem.
-/

open PowerSeries
open scoped BigOperators LaurentSeries RatFunc

namespace PartitionPeriodicSeries

/-- A positive period on the positive coefficients makes the generating
series rational, with polynomial denominator `1-X^P`. The constant
coefficient may be arbitrary. -/
theorem polynomial_mul_of_periodic_positive {R : Type*} [CommRing R]
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
theorem ratFunc_of_periodic_positive {K : Type*} [Field K] (f : ℕ → K) {P : ℕ}
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
theorem first_square_lower_bound {e n : ℕ} (hn : 0 < n)
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
theorem first_square (e : ℕ) :
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

theorem oddSquareSequence_binaryKernel_infinite :
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

open PowerSeries

namespace PartitionOddSquareExpansion

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

theorem oddSquareSeries_eq_X_mul_triangle_pow :
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

open scoped LaurentSeries RatFunc PowerSeries

namespace OMA.R_PartitionParity_ono_swaminathan_quadratic_R2_H1_R1

open Nat PartitionSquareKernel

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

/-- The inverse modular invariant is algebraic over the field generated by the
nonconstant mod-two function represented by the odd Lambert series. The
displayed expansion is the discriminant modulo two in triangular form. -/
def H1 : Prop := by
  classical
  exact ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    let A : (ZMod 2)⸨X⸩ := PowerSeries.mk fun n =>
      ∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n/m).Coprime D then
        (partitionNumber ((D*m^2+1)/24) : ZMod 2) else 0
    let T : PowerSeries (ZMod 2) := PowerSeries.mk fun n =>
      if ∃ m : ℕ, n = m*(m+1)/2 then 1 else 0
    IsAlgebraic (IntermediateField.adjoin (ZMod 2) {A})
      ((PowerSeries.X * T^8 : PowerSeries (ZMod 2)) : (ZMod 2)⸨X⸩)

/-- The necessary direction of Christol's theorem over the field of two
elements, in the Laurent series field. -/
def H2 : Prop := ∀ a : ℕ → ZMod 2,
    IsAlgebraic (RatFunc (ZMod 2)) ((PowerSeries.mk a) : (ZMod 2)⸨X⸩) →
    {g : ℕ → ZMod 2 | ∃ e r : ℕ, r < 2^e ∧ g = fun n => a (2^e*n+r)}.Finite

theorem main : H1 → H2 → OMA.R_PartitionParity_ono_swaminathan_quadratic_R2.H1 := by
  classical
  intro hmod hchristol D hD hsf h23 P hP
  by_contra! hperiod
  let f : ℕ → ZMod 2 := fun n =>
      ∑ m ∈ n.divisors, if m.Coprime 6 ∧ (n/m).Coprime D then
        (partitionNumber ((D*m^2+1)/24) : ZMod 2) else 0
  obtain ⟨F, hF⟩ := PartitionPeriodicSeries.ratFunc_of_periodic_positive f hP hperiod
  have hmod' : IsAlgebraic (IntermediateField.adjoin (ZMod 2)
      {(PowerSeries.mk f : (ZMod 2)⸨X⸩)})
      ((PowerSeries.mk oddSquareSequence) : (ZMod 2)⸨X⸩) := by
    rw [PartitionOddSquareExpansion.oddSquareSeries_eq_X_mul_triangle_pow]
    exact hmod D hD hsf h23
  have h := algebraic_over_ratfunc_of_rational_generator hF hmod'
  exact oddSquareSequence_binaryKernel_infinite (hchristol oddSquareSequence h)

end OMA.R_PartitionParity_ono_swaminathan_quadratic_R2_H1_R1
