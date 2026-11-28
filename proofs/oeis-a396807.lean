import OMAStatements.S_oeis_a396807
import Mathlib

namespace R396807
open OMA.S_oeis_a396807

noncomputable def compR {R : Type*} [CommRing R] (F G : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

noncomputable def iterR {R : Type*} [CommRing R] (A : PowerSeries R) : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | k + 1 => compR A (iterR A k)

theorem coeff_compR {R : Type*} [CommRing R] (F G : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (compR F G) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k) := by
  first
    | exact PowerSeries.coeff_mk _ _
    | simp only [compR, PowerSeries.coeff_mk]

theorem iterR_zero {R : Type*} [CommRing R] (A : PowerSeries R) :
    iterR A 0 = PowerSeries.X := rfl

theorem iterR_succ {R : Type*} [CommRing R] (A : PowerSeries R) (k : ℕ) :
    iterR A (k + 1) = compR A (iterR A k) := rfl

theorem psIter_zero' (A : PowerSeries ℤ) : psIter A 0 = PowerSeries.X := rfl

theorem psIter_succ' (A : PowerSeries ℤ) (k : ℕ) :
    psIter A (k + 1) = psComp A (psIter A k) := rfl

theorem map_psComp {S : Type*} [CommRing S] (f : ℤ →+* S) (F G : PowerSeries ℤ) :
    PowerSeries.map f (psComp F G) = compR (PowerSeries.map f F) (PowerSeries.map f G) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, coeff_compR]
  simp only [psComp, PowerSeries.coeff_mk, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow (PowerSeries.map f) G k]
  simp only [PowerSeries.coeff_map]

theorem map_psIter {S : Type*} [CommRing S] (f : ℤ →+* S) (A : PowerSeries ℤ) (k : ℕ) :
    PowerSeries.map f (psIter A k) = iterR (PowerSeries.map f A) k := by
  induction k with
  | zero => rw [psIter_zero', iterR_zero, PowerSeries.map_X]
  | succ k ih => rw [psIter_succ', iterR_succ, map_psComp, ih]

noncomputable def Cm {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.mk (fun n => a ^ n)

theorem geoS {R : Type*} [CommRing R] (a : R) :
    PowerSeries.mk (fun n => a ^ n) =
      1 + PowerSeries.C a * (PowerSeries.X * PowerSeries.mk (fun n => a ^ n)) := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp
  · simp [pow_succ, mul_comm]

theorem geoS_mul {R : Type*} [CommRing R] (a : R) :
    PowerSeries.mk (fun n => a ^ n) * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  linear_combination geoS a

theorem Cm_eq {R : Type*} [CommRing R] (a : R) :
    Cm a = PowerSeries.X + PowerSeries.C a * (PowerSeries.X * Cm a) := by
  have h := geoS a
  unfold Cm
  linear_combination PowerSeries.X * h

theorem Cm_mul {R : Type*} [CommRing R] (a : R) :
    Cm a * (1 - PowerSeries.C a * PowerSeries.X) = PowerSeries.X := by
  linear_combination Cm_eq a

theorem coeff_Cm_zero {R : Type*} [CommRing R] (a : R) : PowerSeries.coeff 0 (Cm a) = 0 := by
  unfold Cm
  exact PowerSeries.coeff_zero_X_mul _

theorem coeff_Cm_succ {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (Cm a) = a ^ n := by
  unfold Cm
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

theorem Cm_rec {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (Cm a) =
      (if n = 0 then 1 else 0) + a * PowerSeries.coeff n (Cm a) := by
  rcases n with _ | k
  · rw [coeff_Cm_succ, coeff_Cm_zero, if_pos rfl, pow_zero, mul_zero, add_zero]
  · rw [coeff_Cm_succ, coeff_Cm_succ, if_neg (show k + 1 ≠ 0 by omega), zero_add, pow_succ']

theorem powLow {R : Type*} [CommRing R] (G : PowerSeries R) (hG : PowerSeries.coeff 0 G = 0)
    (k n : ℕ) (h : n < k) : PowerSeries.coeff n (G ^ k) = 0 := by
  have h1 : PowerSeries.X ∣ G := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hG
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd h1 k) n h

theorem powRec {R : Type*} [CommRing R] (m : R) (k n : ℕ) :
    PowerSeries.coeff (n + 1) (Cm m ^ (k + 1)) =
      PowerSeries.coeff n (Cm m ^ k) + m * PowerSeries.coeff n (Cm m ^ (k + 1)) := by
  have e := Cm_eq m
  have h : Cm m ^ (k + 1) =
      PowerSeries.X * Cm m ^ k + PowerSeries.C m * (PowerSeries.X * Cm m ^ (k + 1)) := by
    linear_combination (Cm m ^ k) * e
  have h2 := congrArg (fun F => PowerSeries.coeff (n + 1) F) h
  simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul] at h2
  exact h2

theorem sumForm {R : Type*} [CommRing R] (m : R) (N : ℕ) :
    PowerSeries.coeff N (compR (Cm 1) (Cm m)) =
      ∑ k ∈ Finset.range N, PowerSeries.coeff N (Cm m ^ (k + 1)) := by
  rw [coeff_compR, Finset.sum_range_succ', coeff_Cm_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_Cm_succ, one_pow, one_mul]

theorem sRec {R : Type*} [CommRing R] (m : R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (compR (Cm 1) (Cm m)) =
      (if n = 0 then 1 else 0) + (m + 1) * PowerSeries.coeff n (compR (Cm 1) (Cm m)) := by
  rw [sumForm m (n + 1), sumForm m n]
  have A1 : ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (Cm m ^ k) =
      ∑ k ∈ Finset.range n, PowerSeries.coeff n (Cm m ^ (k + 1)) +
        PowerSeries.coeff n (Cm m ^ 0) :=
    Finset.sum_range_succ' (fun k => PowerSeries.coeff n (Cm m ^ k)) n
  have A2 : ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (Cm m ^ (k + 1)) =
      ∑ k ∈ Finset.range n, PowerSeries.coeff n (Cm m ^ (k + 1)) +
        PowerSeries.coeff n (Cm m ^ (n + 1)) :=
    Finset.sum_range_succ (fun k => PowerSeries.coeff n (Cm m ^ (k + 1))) n
  have A3 : ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff n (Cm m ^ k) + m * PowerSeries.coeff n (Cm m ^ (k + 1))) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (Cm m ^ k) +
        m * ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (Cm m ^ (k + 1)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have A4 : ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (n + 1) (Cm m ^ (k + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff n (Cm m ^ k) + m * PowerSeries.coeff n (Cm m ^ (k + 1))) :=
    Finset.sum_congr rfl (fun k _ => powRec m k n)
  have A5 : PowerSeries.coeff n (Cm m ^ (n + 1)) = 0 :=
    powLow (Cm m) (coeff_Cm_zero m) (n + 1) n (Nat.lt_succ_self n)
  have A6 : PowerSeries.coeff n (Cm m ^ 0) = if n = 0 then 1 else 0 := by
    rw [pow_zero, PowerSeries.coeff_one]
  linear_combination A4 + A3 + A1 + m * A2 + m * A5 + A6

theorem compCm {R : Type*} [CommRing R] (m : R) : compR (Cm 1) (Cm m) = Cm (m + 1) := by
  refine PowerSeries.ext fun n => ?_
  induction n with
  | zero =>
    rw [coeff_compR, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      coeff_Cm_zero (1 : R), coeff_Cm_zero (m + 1), zero_mul]
  | succ n ih => rw [sRec, Cm_rec, ih]

theorem CmZero {R : Type*} [CommRing R] : Cm (0 : R) = PowerSeries.X := by
  have h := Cm_eq (0 : R)
  rw [map_zero, zero_mul, add_zero] at h
  exact h

theorem iterCm {R : Type*} [CommRing R] (k : ℕ) : iterR (Cm (1 : R)) k = Cm (k : R) := by
  induction k with
  | zero => rw [Nat.cast_zero, CmZero, iterR_zero]
  | succ k ih => rw [iterR_succ, ih, compCm, Nat.cast_succ]

theorem fixId {R : Type*} [CommRing R] (u v : R) (huv : u + v = 1) (huv0 : u * v = 0) :
    PowerSeries.X + Cm u * Cm v = Cm 1 := by
  have hu := Cm_mul u
  have hv := Cm_mul v
  have hs : PowerSeries.C u + PowerSeries.C v = (1 : PowerSeries R) := by
    rw [← map_add, huv, map_one]
  have hp : PowerSeries.C u * PowerSeries.C v = (0 : PowerSeries R) := by
    rw [← map_mul, huv0, map_zero]
  have key : (PowerSeries.X + Cm u * Cm v) * (1 - PowerSeries.X) = PowerSeries.X := by
    linear_combination (Cm v * (1 - PowerSeries.C v * PowerSeries.X)) * hu + PowerSeries.X * hv +
      (Cm u * Cm v * PowerSeries.X) * hs - (Cm u * Cm v * PowerSeries.X ^ 2) * hp
  have g1 := geoS_mul (1 : R)
  have hc1 : PowerSeries.C (1 : R) = 1 := map_one _
  have e : Cm (1 : R) = PowerSeries.X * PowerSeries.mk (fun n => (1 : R) ^ n) := rfl
  linear_combination (-(PowerSeries.X + Cm u * Cm v)) * g1 -
    ((PowerSeries.X + Cm u * Cm v) * PowerSeries.mk (fun n => (1 : R) ^ n) * PowerSeries.X) * hc1 +
    PowerSeries.mk (fun n => (1 : R) ^ n) * key - e

def Agree {R : Type*} [CommRing R] (N : ℕ) (F G : PowerSeries R) : Prop :=
  ∀ j ≤ N, PowerSeries.coeff j F = PowerSeries.coeff j G

theorem agree_mul {R : Type*} [CommRing R] {N : ℕ} {F F' G G' : PowerSeries R}
    (hF : Agree N F F') (hG : Agree N G G') : Agree N (F * G) (F' * G') := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = j := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | simpa using hp
  rw [hF p.1 (by omega), hG p.2 (by omega)]

theorem agree_pow {R : Type*} [CommRing R] {N : ℕ} {F F' : PowerSeries R}
    (hF : Agree N F F') (k : ℕ) : Agree N (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro j _; simp only [pow_zero]
  | succ k ih => rw [pow_succ, pow_succ]; exact agree_mul ih hF

theorem agree_comp {R : Type*} [CommRing R] {N : ℕ} {F F' G G' : PowerSeries R}
    (hF : Agree N F F') (hG : Agree N G G') : Agree N (compR F G) (compR F' G') := by
  intro j hj
  rw [coeff_compR, coeff_compR]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [hF k (by omega), agree_pow hG k j hj]

theorem agree_iter {R : Type*} [CommRing R] {N : ℕ} {a b : PowerSeries R}
    (h : Agree N a b) (k : ℕ) : Agree N (iterR a k) (iterR b k) := by
  induction k with
  | zero =>
    intro j _
    rfl
  | succ k ih => rw [iterR_succ, iterR_succ]; exact agree_comp h ih

theorem coeff0_iter {R : Type*} [CommRing R] {a : PowerSeries R}
    (ha : PowerSeries.coeff 0 a = 0) (k : ℕ) : PowerSeries.coeff 0 (iterR a k) = 0 := by
  cases k with
  | zero => rw [iterR_zero]; exact PowerSeries.coeff_zero_X
  | succ k =>
    rw [iterR_succ, coeff_compR, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ha,
      zero_mul]

theorem agree_mul_succ {R : Type*} [CommRing R] {N : ℕ} {F F' G G' : PowerSeries R}
    (hF0 : PowerSeries.coeff 0 F = 0) (hF0' : PowerSeries.coeff 0 F' = 0)
    (hG0 : PowerSeries.coeff 0 G = 0) (hG0' : PowerSeries.coeff 0 G' = 0)
    (hF : Agree N F F') (hG : Agree N G G') : Agree (N + 1) (F * G) (F' * G') := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = j := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | simpa using hp
  rcases Nat.eq_zero_or_pos p.1 with h1 | h1
  · rw [h1, hF0, hF0', zero_mul, zero_mul]
  rcases Nat.eq_zero_or_pos p.2 with h2 | h2
  · rw [h2, hG0, hG0', mul_zero, mul_zero]
  rw [hF p.1 (by omega), hG p.2 (by omega)]

theorem uniqFix {R : Type*} [CommRing R] (a b : PowerSeries R)
    (ha0 : PowerSeries.coeff 0 a = 0) (hb0 : PowerSeries.coeff 0 b = 0)
    (ha : a = PowerSeries.X + iterR a 5 * iterR a 6)
    (hb : b = PowerSeries.X + iterR b 5 * iterR b 6) : a = b := by
  have key : ∀ N, Agree N a b := by
    intro N
    induction N with
    | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [ha0, hb0]
    | succ N ih =>
      have hm := agree_mul_succ (coeff0_iter ha0 5) (coeff0_iter hb0 5) (coeff0_iter ha0 6)
        (coeff0_iter hb0 6) (agree_iter ih 5) (agree_iter ih 6)
      intro j hj
      have e1 : PowerSeries.coeff j a =
          PowerSeries.coeff j (PowerSeries.X + iterR a 5 * iterR a 6) := by
        exact congrArg (fun F => PowerSeries.coeff j F) ha
      have e2 : PowerSeries.coeff j b =
          PowerSeries.coeff j (PowerSeries.X + iterR b 5 * iterR b 6) := by
        exact congrArg (fun F => PowerSeries.coeff j F) hb
      rw [e1, e2, map_add, map_add, hm j hj]
  exact PowerSeries.ext fun n => key n n le_rfl

theorem mapA (A : PowerSeries ℤ) (hA0 : PowerSeries.coeff 0 A = 0)
    (hA1 : A = PowerSeries.X + psIter A 5 * psIter A 6) :
    PowerSeries.map (Int.castRingHom (ZMod 10)) A = Cm (1 : ZMod 10) := by
  have h56 : ((5 : ℕ) : ZMod 10) + ((6 : ℕ) : ZMod 10) = 1 := by
    decide
  have h56' : ((5 : ℕ) : ZMod 10) * ((6 : ℕ) : ZMod 10) = 0 := by
    decide
  apply uniqFix
  · rw [PowerSeries.coeff_map, hA0, map_zero]
  · exact coeff_Cm_zero 1
  · conv_lhs => rw [hA1]
    rw [map_add, map_mul, PowerSeries.map_X, map_psIter, map_psIter]
  · rw [iterCm, iterCm]
    exact (fixId _ _ h56 h56').symm

end R396807

theorem OMA.solution : type_of% @OMA.S_oeis_a396807.main := by
  intro A hA
  have hm := R396807.mapA A hA.1 hA.2
  have hk : ∀ k : ℕ, PowerSeries.map (Int.castRingHom (ZMod 10)) (OMA.S_oeis_a396807.psIter A k) =
      R396807.Cm ((k : ℕ) : ZMod 10) := by
    intro k
    rw [R396807.map_psIter, hm, R396807.iterCm]
  refine ⟨fun n hn => ?_, fun k n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e := congrArg (fun F => PowerSeries.coeff (m + 1) F) hm
    simp only [PowerSeries.coeff_map, R396807.coeff_Cm_succ, one_pow, eq_intCast] at e
    have e2 : ((PowerSeries.coeff (m + 1) A : ℤ) : ZMod 10) = ((1 : ℤ) : ZMod 10) := by
      rw [e, Int.cast_one]
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ 10).mp e2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e := congrArg (fun F => PowerSeries.coeff (m + 1) F) (hk k)
    simp only [PowerSeries.coeff_map, R396807.coeff_Cm_succ, eq_intCast] at e
    rw [Nat.add_sub_cancel]
    have e2 : ((PowerSeries.coeff (m + 1) (OMA.S_oeis_a396807.psIter A k) : ℤ) : ZMod 10) =
        (((k : ℤ) ^ m : ℤ) : ZMod 10) := by
      rw [e, Int.cast_pow, Int.cast_natCast]
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ 10).mp e2
