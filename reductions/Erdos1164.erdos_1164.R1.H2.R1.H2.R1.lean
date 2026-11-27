import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Stop the walk at the earlier of time n and an independent geometric lifetime.
The two steps are a last-site hitting estimate and a fixed-time counting identity.
The cardinal induction and the cost of returning to deterministic time are proved below. -/

open MeasureTheory Filter
open scoped ProbabilityTheory Real ENNReal
open Erdos1164 Erdos1165 Finset

namespace OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1



-- A fractional power pays for one deletion at size m.
private lemma factor (m r q : ℝ) (hm : 0 < m) (hr : 0≤r) (r1 : r≤1) (rq : r≤q) :
    m*(m+1)^r ≤ (m+q)*m^r := by
  have ir : 0≤ m⁻¹ := inv_nonneg.mpr hm.le
  have one := rpow_one_add_le_one_add_mul_self (by linarith : -1≤ m⁻¹) hr r1
  have eq : m+1=(1+m⁻¹)*m := by field_simp
  rw [eq,Real.mul_rpow (by positivity) hm.le]
  calc
    _ ≤ m*((1+r*m⁻¹)*m^r) := by gcongr
    _ = (m+r)*m^r := by field_simp
    _ ≤ _ := by gcongr

private theorem deletion {α : Type*} [DecidableEq α] (S : Finset α) (q : ℝ)
    (hq : 0≤q) (q1 : q≤1) (F : Finset α → ℝ)
    (nonneg : ∀ U ⊆ S, 0≤F U) (empty : F ∅≤1)
    (rec : ∀ U ⊆ S, U.Nonempty → (U.card+q)*F U ≤ ∑ x ∈ U, F (U.erase x))
    (pos : S.Nonempty) : F S ≤ Real.exp (-(q/2)*Real.log S.card) := by
  classical
  let r := q/2
  have hr : 0≤r := by dsimp [r]; linarith
  have r1 : r≤1 := by dsimp [r]; linarith
  have rq : r≤q := by dsimp [r]; linarith
  have claim (U : Finset α) (inside : U⊆S) : ((U.card : ℝ)+1)^r * F U ≤ 1 := by
    induction U using Finset.strongInduction with
    | H U ih =>
      rcases U.eq_empty_or_nonempty with rfl|hu
      · simpa using empty
      have hm : (0:ℝ)<U.card := by exact_mod_cast card_pos.mpr hu
      have each (x : α) (hx : x∈U) : (U.card : ℝ)^r * F (U.erase x) ≤ 1 := by
        have h := ih (U.erase x) (erase_ssubset hx) ((erase_subset x U).trans inside)
        have e : ((U.erase x).card : ℝ)+1=U.card := by exact_mod_cast card_erase_add_one hx
        rwa [e] at h
      have sum : (U.card : ℝ)^r*(∑ x ∈ U, F (U.erase x)) ≤ U.card := by
        rw [mul_sum]
        calc _ ≤ ∑ _ ∈ U, (1:ℝ) := sum_le_sum each
             _ = _ := by simp
      have w := mul_le_mul_of_nonneg_left (rec U inside hu) (Real.rpow_nonneg hm.le r)
      have f := mul_le_mul_of_nonneg_right (factor U.card r q hm hr r1 rq) (nonneg U inside)
      exact (le_of_mul_le_mul_left (a:= (U.card : ℝ)) (by nlinarith only [w,sum,f]) hm)
  have h := claim S (Subset.rfl)
  have hp : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr pos
  change F S ≤ Real.exp (-r * Real.log S.card)
  rw [neg_mul,Real.exp_neg]
  rw [mul_comm r,←Real.rpow_def_of_pos hp,←one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mpr
  have p := Real.rpow_le_rpow hp.le (show (S.card:ℝ)≤S.card+1 by linarith) hr
  nlinarith only [h,mul_le_mul_of_nonneg_right p (nonneg S (Subset.rfl))]

private lemma survival (n : ℕ) (hn : 2≤n) : 1 ≤ 4*(1-(1:ℝ)/n)^n := by
  have h : (2:ℝ)≤n := by exact_mod_cast hn
  have hp : 0<(n:ℝ) := by linarith
  have t := rpow_one_add_le_one_add_mul_self (s:=-(1/2:ℝ)) (p:=2/(n:ℝ))
    (by norm_num) (by positivity) ((div_le_one hp).mpr h)
  have single : (1/2 : ℝ)^(2/(n:ℝ)) ≤ 1-1/(n:ℝ) := by
    convert t using 1 <;> ring_nf
  have powBound := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0:ℝ)≤1/2) _) single n
  have eq : ((1/2:ℝ)^(2/(n:ℝ)))^n = 1/4 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),div_mul_cancel₀ 2 hp.ne']
    norm_num
  rw [eq] at powBound
  linarith


-- Compare complete coverage with the event that just one site remains.
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ (n : ℕ), 2 ≤ n → ∀ (S : Finset (ℤ × ℤ)), S.Nonempty → (0 : ℤ × ℤ) ∉ S →
    ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      (∀ z ∈ S, ∀ w ∈ insert (0 : ℤ × ℤ) S, w ≠ z →
        q ≤ 1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
          (ℙ {ω | position X (k + 1) ω = z - w ∧
            ∀ j < k + 1, position X j ω ≠ z - w}).toReal) →
    let A (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∀ x ∈ U, ∃ j ≤ k, position X j ω = x}).toReal
    let B (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∃! x : ℤ × ℤ, x ∈ U ∧ ¬ ∃ j ≤ k, position X j ω = x}).toReal
    let t : ℝ := 1 - 1 / (n : ℝ)
    let T (a : ℕ → ℝ) := t^n * a n + (1-t) * ∑ k ∈ Finset.range n, t^k * a k
    q * T (A S) ≤ T (B S)

-- Deleting one target counts a completely covered set once for each of its sites.
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ (U : Finset (ℤ × ℤ)) (k : ℕ),
    let A (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∀ x ∈ U, ∃ j ≤ k, position X j ω = x}).toReal
    let B (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∃! x : ℤ × ℤ, x ∈ U ∧ ¬ ∃ j ≤ k, position X j ω = x}).toReal
    ∑ x ∈ U, A (U.erase x) k = U.card * A U k + B U k

theorem main : H1 → H2 → OMA.R_Erdos1164_erdos_1164_R1_H2_R1.H2 := by
  intro lastSite counting Ω _ _ X hX n hn S hS hzero q hq hq1 pairs
  classical
  let A (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∀ x ∈ U, ∃ j ≤ k, position X j ω = x}).toReal
  let B (U : Finset (ℤ × ℤ)) (k : ℕ) := (ℙ {ω | ∃! x : ℤ × ℤ, x ∈ U ∧ ¬ ∃ j ≤ k, position X j ω = x}).toReal
  let t : ℝ := 1 - 1 / (n : ℝ)
  let T (a : ℕ → ℝ) := t^n * a n + (1-t) * ∑ k ∈ Finset.range n, t^k * a k
  have npos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have tn : 0 ≤ t := by dsimp [t]; have := (div_le_one npos).mpr (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega)); linarith
  have t1 : 0 ≤ 1-t := by simp [t]
  have An (U : Finset (ℤ × ℤ)) (k : ℕ) : 0 ≤ A U k := ENNReal.toReal_nonneg
  have weighted (U : Finset (ℤ × ℤ)) : t^n * A U n ≤ T (A U) := by
    dsimp only [T]
    exact le_add_of_nonneg_right (mul_nonneg t1 (sum_nonneg fun k _ ↦ mul_nonneg (pow_nonneg tn k) (An U k)))
  have nonneg (U : Finset (ℤ × ℤ)) (_ : U⊆S) : 0≤T (A U) :=
    (mul_nonneg (pow_nonneg tn n) (An U n)).trans (weighted U)
  have mass (m : ℕ) : t^m + (1-t) * ∑ k ∈ range m, t^k = 1 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, pow_succ]; nlinarith only [ih]
  have empty : T (A ∅) ≤ 1 := by
    have ae (k : ℕ) : A ∅ k = 1 := by simp [A]
    simp only [T, ae, mul_one]
    exact (mass n).le
  have descend (U : Finset (ℤ × ℤ)) (hu : U⊆S) (hp : U.Nonempty) :
      (U.card+q) * T (A U) ≤ (∑ x ∈ U, T (A (U.erase x))) := by
    have pairU : ∀ z ∈ U, ∀ w ∈ insert (0 : ℤ × ℤ) U, w ≠ z →
        q ≤ 1 - ∑' k : ℕ, (1 - (1:ℝ)/n)^(k+1) *
          (ℙ {ω | position X (k+1) ω = z-w ∧ ∀ j < k+1, position X j ω ≠ z-w}).toReal := by
      intro z hz w hw hwz
      exact pairs z (hu hz) w (insert_subset_insert _ hu hw) hwz
    have missing : q*T (A U) ≤ T (B U) := lastSite hX n hn U hp (fun h => hzero (hu h)) q hq hq1 pairU
    have count (k : ℕ) : ∑ x ∈ U, A (U.erase x) k = U.card * A U k + B U k := counting hX U k
    have total : (∑ x ∈ U, T (A (U.erase x))) = U.card * T (A U) + T (B U) := by
      dsimp only [T]
      rw [sum_add_distrib, ←mul_sum, ←mul_sum, sum_comm (s:=U) (t:=range n)]
      simp_rw [←mul_sum, count, mul_add, sum_add_distrib]
      have exchange : ∑ k ∈ range n, t^k * (U.card * A U k) =
          U.card * ∑ k ∈ range n, t^k * A U k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        ring
      rw [exchange]
      ring
    rw [total]
    linarith only [missing]
  have upper := deletion S q hq hq1 (fun U => T (A U)) nonneg empty descend hS
  have lower : 1 ≤ 4*t^n := survival n hn
  change A S n ≤ _
  calc
    A S n ≤ 4 * (t^n * A S n) := by nlinarith only [mul_le_mul_of_nonneg_right lower (An S n)]
    _ ≤ 4 * T (A S) := by linarith only [weighted S]
    _ ≤ _ := by linarith only [upper]

end OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1
