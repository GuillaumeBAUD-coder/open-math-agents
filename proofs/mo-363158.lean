import OMAStatements.S_mo_363158
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Field.ULift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
Counterexample to `OMA.S_mo_363158.main` in characteristic 2 over an imperfect field
`K = F_2(u)(v)` with `[K : K^2] >= 3`.

For `n = 3`, coordinate projections are linearly independent, while
`P 0 = X_0^2 + u * X_1^2 + v * X_2^2`, `P 1 = 0`, `P 2 = 0`
has `totalDegree` sum `2 < 3` and defines an injective map `F : K^3 -> K^3`
(since `1, u, v` are linearly independent over `K^2` and squaring is injective
in characteristic 2), so `F '' X` and `F '' Xᶜ` are disjoint.
-/

namespace MO363158Disproof

open Polynomial

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev R0 := Polynomial (ZMod 2)
private abbrev F1 := FractionRing R0
private abbrev R1 := Polynomial F1
private abbrev K := FractionRing R1

private lemma two_eq_zero_ZMod2 : (2 : ZMod 2) = 0 := rfl

private lemma two_eq_zero_R0 : (2 : R0) = 0 := by
  rw [← map_ofNat (Polynomial.C : ZMod 2 →+* R0) 2, two_eq_zero_ZMod2, map_zero]

private lemma two_eq_zero_F1 : (2 : F1) = 0 := by
  rw [← map_ofNat (algebraMap R0 F1) 2, two_eq_zero_R0, map_zero]

private lemma two_eq_zero_R1 : (2 : R1) = 0 := by
  rw [← map_ofNat (Polynomial.C : F1 →+* R1) 2, two_eq_zero_F1, map_zero]

private lemma two_eq_zero_K : (2 : K) = 0 := by
  rw [← map_ofNat (algebraMap R1 K) 2, two_eq_zero_R1, map_zero]

private lemma sq_add_X_mul_sq_eq_zero {F : Type*} [Field F] (P Q : Polynomial F)
    (h : P ^ 2 + Polynomial.X * Q ^ 2 = 0) : P = 0 ∧ Q = 0 := by
  by_cases hQ : Q = 0
  · subst hQ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      sq_eq_zero_iff] at h
    exact ⟨h, rfl⟩
  · have hP : P ≠ 0 := by
      intro hP0
      rw [hP0, zero_pow (by norm_num), zero_add] at h
      have hmul := mul_eq_zero.mp h
      rcases hmul with hX | hQ2
      · exact Polynomial.X_ne_zero hX
      · exact hQ (sq_eq_zero_iff.mp hQ2)
    have hdeg : (P ^ 2).natDegree = (-(Polynomial.X * Q ^ 2)).natDegree :=
      congr_arg Polynomial.natDegree (eq_neg_of_add_eq_zero_left h)
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg,
      Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 2 hQ),
      Polynomial.natDegree_X, Polynomial.natDegree_pow] at hdeg
    omega

private noncomputable def uF1 : F1 := algebraMap R0 F1 Polynomial.X

private lemma F1_sq_indep (a b : F1) (h : a ^ 2 + uF1 * b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨A, D1, hD1, rfl⟩ := IsFractionRing.div_surjective (A := R0) a
  obtain ⟨B, D2, hD2, rfl⟩ := IsFractionRing.div_surjective (A := R0) b
  have hD10 : D1 ≠ 0 := nonZeroDivisors.ne_zero hD1
  have hD20 : D2 ≠ 0 := nonZeroDivisors.ne_zero hD2
  have hmD1 : algebraMap R0 F1 D1 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R0 F1)).mpr hD10
  have hmD2 : algebraMap R0 F1 D2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R0 F1)).mpr hD20
  have hclear : (algebraMap R0 F1 (D1 * D2)) ^ 2 *
      ((algebraMap R0 F1 A / algebraMap R0 F1 D1) ^ 2 +
        uF1 * (algebraMap R0 F1 B / algebraMap R0 F1 D2) ^ 2) = 0 := by
    rw [h, mul_zero]
  have hid : (algebraMap R0 F1 (D1 * D2)) ^ 2 *
      ((algebraMap R0 F1 A / algebraMap R0 F1 D1) ^ 2 +
        uF1 * (algebraMap R0 F1 B / algebraMap R0 F1 D2) ^ 2) =
      algebraMap R0 F1 ((A * D2) ^ 2 + Polynomial.X * (B * D1) ^ 2) := by
    simp only [uF1, map_add, map_mul, map_pow]
    field_simp [hmD1, hmD2]
  rw [hid] at hclear
  have hpoly : (A * D2) ^ 2 + Polynomial.X * (B * D1) ^ 2 = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective R0 F1)).mp hclear
  obtain ⟨hA, hB⟩ := sq_add_X_mul_sq_eq_zero (A * D2) (B * D1) hpoly
  have hA0 : A = 0 := (mul_eq_zero.mp hA).resolve_right hD20
  have hB0 : B = 0 := (mul_eq_zero.mp hB).resolve_right hD10
  subst hA0 hB0
  simp

private lemma coeff_sq_R1 (P : R1) :
    ∀ k : ℕ, (P ^ 2).coeff (2 * k + 1) = 0 ∧ (P ^ 2).coeff (2 * k) = (P.coeff k) ^ 2 := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro p q hp hq k
    have hsq : (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
      have h2 : (2 : R1) = 0 := two_eq_zero_R1
      calc
        (p + q) ^ 2 = p ^ 2 + 2 * p * q + q ^ 2 := by ring
        _ = p ^ 2 + q ^ 2 := by rw [h2]; ring
    rw [hsq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
    obtain ⟨hp1, hp0⟩ := hp k
    obtain ⟨hq1, hq0⟩ := hq k
    refine ⟨by rw [hp1, hq1, add_zero], ?_⟩
    rw [hp0, hq0]
    have h2 : (2 : F1) = 0 := two_eq_zero_F1
    calc
      (p.coeff k) ^ 2 + (q.coeff k) ^ 2 =
          (p.coeff k + q.coeff k) ^ 2 - 2 * p.coeff k * q.coeff k := by ring
      _ = (p.coeff k + q.coeff k) ^ 2 := by rw [h2]; ring
  · intro n a k
    rw [Polynomial.monomial_pow, mul_comm n 2, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    constructor
    · split_ifs with h
      · omega
      · rfl
    · split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · simp

private lemma R1_sq_indep (A B C : R1)
    (h : A ^ 2 + Polynomial.C uF1 * B ^ 2 + Polynomial.X * C ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hC : C = 0 := by
    ext k
    have hc := congr_arg (fun p : R1 => p.coeff (2 * k + 1)) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      Polynomial.coeff_zero] at hc
    rw [(coeff_sq_R1 A k).1, (coeff_sq_R1 B k).1, (coeff_sq_R1 C k).2] at hc
    simp only [zero_add, mul_zero] at hc
    exact sq_eq_zero_iff.mp hc
  subst hC
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  have hAB : A = 0 ∧ B = 0 := by
    have hall : ∀ k : ℕ, A.coeff k = 0 ∧ B.coeff k = 0 := by
      intro k
      have hc := congr_arg (fun p : R1 => p.coeff (2 * k)) h
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_zero] at hc
      rw [(coeff_sq_R1 A k).2, (coeff_sq_R1 B k).2] at hc
      exact F1_sq_indep (A.coeff k) (B.coeff k) hc
    exact ⟨Polynomial.ext fun k => (hall k).1, Polynomial.ext fun k => (hall k).2⟩
  exact ⟨hAB.1, hAB.2, rfl⟩

private noncomputable def uK : K := algebraMap R1 K (Polynomial.C uF1)
private noncomputable def vK : K := algebraMap R1 K Polynomial.X

private lemma K_sq_indep (a b c : K) (h : a ^ 2 + uK * b ^ 2 + vK * c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨A, D1, hD1, rfl⟩ := IsFractionRing.div_surjective (A := R1) a
  obtain ⟨B, D2, hD2, rfl⟩ := IsFractionRing.div_surjective (A := R1) b
  obtain ⟨C, D3, hD3, rfl⟩ := IsFractionRing.div_surjective (A := R1) c
  have hD10 : D1 ≠ 0 := nonZeroDivisors.ne_zero hD1
  have hD20 : D2 ≠ 0 := nonZeroDivisors.ne_zero hD2
  have hD30 : D3 ≠ 0 := nonZeroDivisors.ne_zero hD3
  have hmD1 : algebraMap R1 K D1 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R1 K)).mpr hD10
  have hmD2 : algebraMap R1 K D2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R1 K)).mpr hD20
  have hmD3 : algebraMap R1 K D3 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R1 K)).mpr hD30
  have hclear : (algebraMap R1 K (D1 * D2 * D3)) ^ 2 *
      ((algebraMap R1 K A / algebraMap R1 K D1) ^ 2 +
        uK * (algebraMap R1 K B / algebraMap R1 K D2) ^ 2 +
        vK * (algebraMap R1 K C / algebraMap R1 K D3) ^ 2) = 0 := by
    rw [h, mul_zero]
  have hid : (algebraMap R1 K (D1 * D2 * D3)) ^ 2 *
      ((algebraMap R1 K A / algebraMap R1 K D1) ^ 2 +
        uK * (algebraMap R1 K B / algebraMap R1 K D2) ^ 2 +
        vK * (algebraMap R1 K C / algebraMap R1 K D3) ^ 2) =
      algebraMap R1 K ((A * (D2 * D3)) ^ 2 +
        Polynomial.C uF1 * (B * (D1 * D3)) ^ 2 +
        Polynomial.X * (C * (D1 * D2)) ^ 2) := by
    simp only [uK, vK, map_add, map_mul, map_pow]
    field_simp [hmD1, hmD2, hmD3]
  rw [hid] at hclear
  have hpoly : (A * (D2 * D3)) ^ 2 + Polynomial.C uF1 * (B * (D1 * D3)) ^ 2 +
      Polynomial.X * (C * (D1 * D2)) ^ 2 = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective R1 K)).mp hclear
  obtain ⟨hA, hB, hC⟩ := R1_sq_indep (A * (D2 * D3)) (B * (D1 * D3)) (C * (D1 * D2)) hpoly
  have hA0 : A = 0 := (mul_eq_zero.mp hA).resolve_right (mul_ne_zero hD20 hD30)
  have hB0 : B = 0 := (mul_eq_zero.mp hB).resolve_right (mul_ne_zero hD10 hD30)
  have hC0 : C = 0 := (mul_eq_zero.mp hC).resolve_right (mul_ne_zero hD10 hD20)
  subst hA0 hB0 hC0
  simp

private lemma K_sq_add_sq (x y : K) : (x - y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  calc
    (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by ring
    _ = x ^ 2 + y ^ 2 := by rw [h2]; ring

private lemma K_add_eq_zero_iff (x y : K) : x + y = 0 ↔ x = y := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  constructor
  · intro h
    calc
      x = x + (y + y) := by rw [← two_mul, h2, zero_mul, add_zero]
      _ = (x + y) + y := by ring
      _ = y := by rw [h, zero_add]
  · intro h
    subst h
    rw [← two_mul, h2, zero_mul]

end MO363158Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_363158.main) := by
  intro hmain
  let K := ULift MO363158Disproof.K
  let u : K := ULift.up MO363158Disproof.uK
  let v : K := ULift.up MO363158Disproof.vK
  let forms : Fin 3 → (Fin 3 → K) →ₗ[K] K := fun i =>
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hli : LinearIndependent K forms := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congr_arg (fun f => f (fun j : Fin 3 => if j = i then (1 : K) else 0)) hg
    simp only [forms, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h
    exact h
  let p0 : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 0 ^ 2 + MvPolynomial.C u * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C v * MvPolynomial.X 2 ^ 2
  let P : Fin 3 → MvPolynomial (Fin 3) K := fun i => if i = 0 then p0 else 0
  let X : Set (Fin 3 → K) := {x | ∃ i : Fin 3, forms i x = 0}
  let F : (Fin 3 → K) → (Fin 3 → K) := fun x i => MvPolynomial.eval x (P i)
  have hdisj : Disjoint (F '' X) (F '' Xᶜ) := by
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
    have h0 : F y 0 = F x 0 := congr_fun hyx 0
    have heval : ∀ z : Fin 3 → K,
        F z 0 = z 0 ^ 2 + u * z 1 ^ 2 + v * z 2 ^ 2 := by
      intro z
      simp [F, P, p0]
    rw [heval y, heval x] at h0
    have h0' : (y 0).down ^ 2 + MO363158Disproof.uK * (y 1).down ^ 2 +
        MO363158Disproof.vK * (y 2).down ^ 2 =
        (x 0).down ^ 2 + MO363158Disproof.uK * (x 1).down ^ 2 +
        MO363158Disproof.vK * (x 2).down ^ 2 :=
      congr_arg ULift.down h0
    have hdiff : ((x 0).down - (y 0).down) ^ 2 +
        MO363158Disproof.uK * ((x 1).down - (y 1).down) ^ 2 +
        MO363158Disproof.vK * ((x 2).down - (y 2).down) ^ 2 = 0 := by
      rw [MO363158Disproof.K_sq_add_sq, MO363158Disproof.K_sq_add_sq,
        MO363158Disproof.K_sq_add_sq]
      have hadd := (MO363158Disproof.K_add_eq_zero_iff _ _).mpr h0'.symm
      calc
        (x 0).down ^ 2 + (y 0).down ^ 2 +
            MO363158Disproof.uK * ((x 1).down ^ 2 + (y 1).down ^ 2) +
            MO363158Disproof.vK * ((x 2).down ^ 2 + (y 2).down ^ 2) =
            ((x 0).down ^ 2 + MO363158Disproof.uK * (x 1).down ^ 2 +
              MO363158Disproof.vK * (x 2).down ^ 2) +
            ((y 0).down ^ 2 + MO363158Disproof.uK * (y 1).down ^ 2 +
              MO363158Disproof.vK * (y 2).down ^ 2) := by ring
        _ = 0 := hadd
    obtain ⟨h00, h11, h22⟩ := MO363158Disproof.K_sq_indep _ _ _ hdiff
    have hxy : x = y := by
      funext i
      fin_cases i
      · exact ULift.down_injective (sub_eq_zero.mp h00)
      · exact ULift.down_injective (sub_eq_zero.mp h11)
      · exact ULift.down_injective (sub_eq_zero.mp h22)
    rw [← hxy] at hy
    exact hy hx
  have hle : 3 ≤ ∑ i : Fin 3, (P i).totalDegree := hmain K 3 forms hli P hdisj
  have hp0 : p0.totalDegree ≤ 2 := by
    have hX0 : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_X (0 : Fin 3)).le
    have hX1 : (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) K).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_X (1 : Fin 3)).le
    have hX2 : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_X (2 : Fin 3)).le
    have hd0 : ((MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_pow _ _).trans (by omega)
    have hpow1 : ((MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_pow _ _).trans (by omega)
    have hpow2 : ((MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_pow _ _).trans (by omega)
    have hd1 : (MvPolynomial.C u *
        (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2).totalDegree ≤ 2 := by
      have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C u : MvPolynomial (Fin 3) K)
        ((MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2)
      rw [MvPolynomial.totalDegree_C] at hmul
      omega
    have hd2 : (MvPolynomial.C v *
        (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2).totalDegree ≤ 2 := by
      have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C v : MvPolynomial (Fin 3) K)
        ((MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ^ 2)
      rw [MvPolynomial.totalDegree_C] at hmul
      omega
    have ha1 : (MvPolynomial.X (0 : Fin 3) ^ 2 + MvPolynomial.C u *
        MvPolynomial.X (1 : Fin 3) ^ 2).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_add _ _).trans (max_le hd0 hd1)
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le ha1 hd2)
  have hsum : ∑ i : Fin 3, (P i).totalDegree = p0.totalDegree := by
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · simp [P]
    · intro i _ hi
      simp [P, hi]
    · intro hmem
      exact (hmem (Finset.mem_univ 0)).elim
  omega
