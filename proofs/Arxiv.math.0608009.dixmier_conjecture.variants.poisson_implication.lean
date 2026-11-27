import FormalConjectures.Arxiv.«math.0608009».DixmierConjecture
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.Separable

/-!
# Proof of `Arxiv.math.0608009.dixmier_conjecture.variants.poisson_implication`

We prove that if the Poisson conjecture in dimension `n` holds over every field of characteristic
zero, then the Dixmier conjecture in dimension `n` holds over every field of characteristic zero
(Adjamagbo–van den Essen, Theorem 7; Tsuchimoto; Belov-Kanel–Kontsevich).
-/

namespace DixmierPoissonProof

open MvPolynomial WeylAlgebra Arxiv.«math.0608009»
open scoped Pointwise

abbrev W (R : Type*) [CommRing R] (n : ℕ) := WeylAlgebra R (Fin n)
abbrev P (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) R

noncomputable def wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) : W R n :=
  WeylAlgebra.of R (Sum.inl i)

noncomputable def wy (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) : W R n :=
  WeylAlgebra.of R (Sum.inr i)

/-- Universal property of `WeylAlgebra R σ`. -/
noncomputable def weylLift {R σ A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (f : σ ⊕ σ → A)
    (h1 : ∀ i j, f (Sum.inl i) * f (Sum.inl j) = f (Sum.inl j) * f (Sum.inl i))
    (h2 : ∀ i j, f (Sum.inr i) * f (Sum.inr j) = f (Sum.inr j) * f (Sum.inr i))
    (h3 : ∀ i j, i ≠ j → f (Sum.inl i) * f (Sum.inr j) = f (Sum.inr j) * f (Sum.inl i))
    (h4 : ∀ i, f (Sum.inl i) * f (Sum.inr i) = f (Sum.inr i) * f (Sum.inl i) + 1) :
    WeylAlgebra R σ →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R f, by
    rintro x y hrel
    cases hrel with
    | inl_mul_comm i j => simp [h1 i j]
    | inr_mul_comm i j => simp [h2 i j]
    | inl_mul_inr_of_ne hij => simp [h3 _ _ hij]
    | inl_mul_inr_self i => simp [h4 i]⟩

@[simp]
lemma weylLift_of {R σ A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (f : σ ⊕ σ → A) (h1 h2 h3 h4) (v : σ ⊕ σ) :
    weylLift f h1 h2 h3 h4 (WeylAlgebra.of R v) = f v := by
  exact (RingQuot.liftAlgHom_mkAlgHom_apply R (FreeAlgebra.lift R f) _ (FreeAlgebra.ι R v)).trans
    (FreeAlgebra.lift_ι_apply f v)

/-- Base change for `WeylAlgebra`. -/
noncomputable def weylMap {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) : W R n →+* W S n :=
  letI : Algebra R (W S n) := Algebra.compHom (W S n) g
  (weylLift (R := R) (σ := Fin n) (A := W S n) (WeylAlgebra.of S)
    (fun i j => WeylAlgebra.of_inl_mul_comm S i j)
    (fun i j => WeylAlgebra.of_inr_mul_comm S i j)
    (fun _ _ h => WeylAlgebra.of_inl_mul_of_inr_of_ne S h)
    (fun i => WeylAlgebra.of_inl_mul_of_inr_self S i)).toRingHom

@[simp]
lemma weylMap_of {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (v : Fin n ⊕ Fin n) :
    weylMap g (WeylAlgebra.of R v) = WeylAlgebra.of S v := by
  dsimp only [weylMap]
  let _ : Algebra R (W S n) := Algebra.compHom (W S n) g
  exact weylLift_of _ _ _ _ _ v

@[simp]
lemma weylMap_algebraMap {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (r : R) :
    weylMap g (algebraMap R (W R n) r) = algebraMap S (W S n) (g r) := by
  dsimp only [weylMap]
  let _ : Algebra R (W S n) := Algebra.compHom (W S n) g
  exact AlgHom.commutes _ r

lemma pderiv_comm_local {R σ : Type*} [CommRing R] [DecidableEq σ] (u v : σ)
    (f : MvPolynomial σ R) : pderiv u (pderiv v f) = pderiv v (pderiv u f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    simp only [pderiv_monomial]
    by_cases huv : u = v
    · subst huv; rfl
    · simp only [Finsupp.tsub_apply, Finsupp.single_eq_of_ne huv,
        Finsupp.single_eq_of_ne (Ne.symm huv), Nat.sub_zero]
      rw [tsub_right_comm]
      congr 1; ring
  | add p q hp hq => simp [hp, hq]

/-- Standard differential-operator action of `W R n` on `P R n = MvPolynomial (Fin n ⊕ Fin n) R`:
`x_i` acts by multiplication by `X (inl i)`, and `y_i` acts by `X (inr i) - ∂_{x_i}`. -/
noncomputable def toEnd (R : Type*) [CommRing R] (n : ℕ) :
    W R n →ₐ[R] Module.End R (P R n) :=
  weylLift
    (fun v => match v with
      | Sum.inl i => LinearMap.mulLeft R (X (Sum.inl i))
      | Sum.inr i => LinearMap.mulLeft R (X (Sum.inr i)) - (pderiv (Sum.inl i)).toLinearMap)
    (by
      intro i j; refine LinearMap.ext fun f => ?_
      change X (Sum.inl i) * (X (Sum.inl j) * f) = X (Sum.inl j) * (X (Sum.inl i) * f)
      ring)
    (by
      intro i j; refine LinearMap.ext fun f => ?_
      change X (Sum.inr i) * (X (Sum.inr j) * f - pderiv (Sum.inl j) f) -
          pderiv (Sum.inl i) (X (Sum.inr j) * f - pderiv (Sum.inl j) f) =
        X (Sum.inr j) * (X (Sum.inr i) * f - pderiv (Sum.inl i) f) -
          pderiv (Sum.inl j) (X (Sum.inr i) * f - pderiv (Sum.inl i) f)
      rw [map_sub, map_sub, Derivation.leibniz, Derivation.leibniz,
        pderiv_X_of_ne (by simp), pderiv_X_of_ne (by simp),
        pderiv_comm_local (Sum.inl i) (Sum.inl j) f]
      simp only [smul_eq_mul, mul_zero, add_zero]
      ring)
    (by
      intro i j hij; refine LinearMap.ext fun f => ?_
      change X (Sum.inl i) * (X (Sum.inr j) * f - pderiv (Sum.inl j) f) =
        X (Sum.inr j) * (X (Sum.inl i) * f) - pderiv (Sum.inl j) (X (Sum.inl i) * f)
      rw [Derivation.leibniz, pderiv_X_of_ne (by simpa using hij)]
      simp only [smul_eq_mul, mul_zero, add_zero]
      ring)
    (by
      intro i; refine LinearMap.ext fun f => ?_
      change X (Sum.inl i) * (X (Sum.inr i) * f - pderiv (Sum.inl i) f) =
        X (Sum.inr i) * (X (Sum.inl i) * f) - pderiv (Sum.inl i) (X (Sum.inl i) * f) + f
      rw [Derivation.leibniz, pderiv_X_self]
      simp only [smul_eq_mul, mul_one]
      ring)

/-- Normal-form map `W R n →ₗ[R] P R n` sending `a` to `toEnd a 1`. -/
noncomputable def toMvPoly (R : Type*) [CommRing R] (n : ℕ) : W R n →ₗ[R] P R n where
  toFun a := toEnd R n a 1
  map_add' a b := by simp
  map_smul' r a := by simp

/-- Ordered product of `x_i^{α_i}` and `y_i^{β_i}` in `W R n`. -/
noncomputable def wxProd (R : Type*) [CommRing R] {n : ℕ} (e : Fin n → ℕ) : W R n :=
  ((List.finRange n).map (fun i => wx R i ^ e i)).prod

noncomputable def wyProd (R : Type*) [CommRing R] {n : ℕ} (e : Fin n → ℕ) : W R n :=
  ((List.finRange n).map (fun i => wy R i ^ e i)).prod

noncomputable def weylMonom (R : Type*) [CommRing R] {n : ℕ} (d : (Fin n ⊕ Fin n) →₀ ℕ) : W R n :=
  wxProd R (fun i => d (Sum.inl i)) * wyProd R (fun i => d (Sum.inr i))

/-- Inverse PBW map `P R n →ₗ[R] W R n` sending `∑ c_d X^d` to `∑ c_d x^α y^β`. -/
noncomputable def ofMvPoly (R : Type*) [CommRing R] (n : ℕ) : P R n →ₗ[R] W R n where
  toFun f := ∑ d ∈ f.support, f.coeff d • weylMonom R d
  map_add' f g := by
    have hf : f.support ⊆ f.support ∪ g.support := Finset.subset_union_left
    have hg : g.support ⊆ f.support ∪ g.support := Finset.subset_union_right
    have hfg : (f + g).support ⊆ f.support ∪ g.support := MvPolynomial.support_add
    rw [Finset.sum_subset hfg (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.mp hd]),
      Finset.sum_subset hf (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.mp hd]),
      Finset.sum_subset hg (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.mp hd]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.coeff_add, add_smul]
  map_smul' r f := by
    simp only [RingHom.id_apply]
    have hrf : (r • f).support ⊆ f.support := MvPolynomial.support_smul
    rw [Finset.sum_subset hrf (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.mp hd]),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

@[simp]
lemma ofMvPoly_monomial (R : Type*) [CommRing R] {n : ℕ} (d : (Fin n ⊕ Fin n) →₀ ℕ) (r : R) :
    ofMvPoly R n (monomial d r) = r • weylMonom R d := by
  classical
  change ∑ d' ∈ (monomial d r).support, (monomial d r).coeff d' • weylMonom R d' = _
  by_cases hr : r = 0
  · subst hr; simp
  · rw [MvPolynomial.support_monomial, if_neg hr, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl]

lemma toEnd_wx_pow (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) (f : P R n) :
    toEnd R n (wx R i ^ k) f = X (Sum.inl i) ^ k * f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply, ih]
    simp [wx, toEnd, pow_succ', mul_assoc]

lemma toEnd_list_wx (R : Type*) [CommRing R] {n : ℕ} (l : List (Fin n))
    (e : Fin n → ℕ) (f : P R n) :
    toEnd R n ((l.map (fun i => wx R i ^ e i)).prod) f =
      (l.map (fun i => (X (Sum.inl i) : P R n) ^ e i)).prod * f := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih,
      toEnd_wx_pow, mul_assoc]

lemma pderiv_inl_list_inr (R : Type*) [CommRing R] {n : ℕ} (j : Fin n)
    (l : List (Fin n)) (e : Fin n → ℕ) :
    pderiv (Sum.inl j) ((l.map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Derivation.leibniz, ih, smul_zero, zero_add]
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp)]
    simp

lemma toEnd_wy_pow_list_inr (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ)
    (l : List (Fin n)) (e : Fin n → ℕ) :
    toEnd R n (wy R i ^ k) ((l.map (fun j => (X (Sum.inr j) : P R n) ^ e j)).prod) =
      X (Sum.inr i) ^ k * (l.map (fun j => (X (Sum.inr j) : P R n) ^ e j)).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply, ih]
    have hkill : pderiv (Sum.inl i)
        ((X (Sum.inr i) : P R n) ^ k * (l.map (fun j => (X (Sum.inr j) : P R n) ^ e j)).prod) = 0 := by
      rw [Derivation.leibniz, pderiv_inl_list_inr, smul_zero, zero_add,
        Derivation.leibniz_pow, pderiv_X_of_ne (by simp)]
      simp
    simp only [wy, toEnd, weylLift_of, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      pow_succ', mul_assoc]
    change _ - pderiv (Sum.inl i) _ = _
    rw [hkill, sub_zero]

lemma toEnd_list_wy_one (R : Type*) [CommRing R] {n : ℕ} (l : List (Fin n)) (e : Fin n → ℕ) :
    toEnd R n ((l.map (fun i => wy R i ^ e i)).prod) 1 =
      (l.map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih,
      toEnd_wy_pow_list_inr]

lemma list_finRange_prod_eq {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ((List.finRange n).map f).prod = ∏ i : Fin n, f i := by
  have h : (Finset.univ : Finset (Fin n)).val = ↑(List.finRange n) := rfl
  rw [Finset.prod_eq_multiset_prod, h, Multiset.map_coe, Multiset.prod_coe]

lemma toMvPoly_weylMonom (R : Type*) [CommRing R] {n : ℕ} (d : (Fin n ⊕ Fin n) →₀ ℕ) :
    toMvPoly R n (weylMonom R d) = monomial d 1 := by
  rw [toMvPoly, weylMonom, wxProd, wyProd, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
    Module.End.mul_apply, toEnd_list_wy_one, toEnd_list_wx,
    list_finRange_prod_eq, list_finRange_prod_eq]
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type]

lemma toMvPoly_ofMvPoly (R : Type*) [CommRing R] (n : ℕ) (f : P R n) :
    toMvPoly R n (ofMvPoly R n f) = f := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [ofMvPoly_monomial, map_smul, toMvPoly_weylMonom, smul_monomial, smul_eq_mul, mul_one]
  | add p q hp hq =>
    simp [hp, hq]

lemma wy_mul_wx_pow (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) :
    wy R i * wx R i ^ k = wx R i ^ k * wy R i - (k : W R n) * wx R i ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcomm : wy R i * wx R i = wx R i * wy R i - 1 := by
      have h := WeylAlgebra.of_inl_mul_of_inr_self R i
      change wx R i * wy R i = wy R i * wx R i + 1 at h
      calc wy R i * wx R i = (wy R i * wx R i + 1) - 1 := by abel
        _ = wx R i * wy R i - 1 := by rw [← h]
    cases k with
    | zero => simpa using hcomm
    | succ k =>
      have ih' : wy R i * wx R i ^ (k + 1) =
          wx R i ^ (k + 1) * wy R i - ((k + 1 : ℕ) : W R n) * wx R i ^ k := by
        simpa using ih
      calc wy R i * wx R i ^ (k + 2)
          = (wy R i * wx R i ^ (k + 1)) * wx R i := by rw [pow_succ, mul_assoc]
        _ = (wx R i ^ (k + 1) * wy R i - ((k + 1 : ℕ) : W R n) * wx R i ^ k) * wx R i := by
            rw [ih']
        _ = wx R i ^ (k + 1) * (wy R i * wx R i) - ((k + 1 : ℕ) : W R n) * wx R i ^ (k + 1) := by
            rw [sub_mul, mul_assoc, mul_assoc, ← pow_succ]
        _ = wx R i ^ (k + 1) * (wx R i * wy R i - 1) - ((k + 1 : ℕ) : W R n) * wx R i ^ (k + 1) := by
            rw [hcomm]
        _ = wx R i ^ (k + 2) * wy R i - ((k + 2 : ℕ) : W R n) * wx R i ^ (k + 1) := by
            rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ]
            push_cast
            noncomm_ring

/- Left multiplication of `weylMonom` by `wx i` and `wy i`, giving surjectivity of `ofMvPoly`. -/

lemma wx_mul_wxProd (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wx R i * wxProd R e = wxProd R (Function.update e i (e i + 1)) := by
  have haux : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      wx R i * (l.map (fun j => wx R j ^ e j)).prod =
        (l.map (fun j => wx R j ^ Function.update e i (e i + 1) j)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with rfl | hl
      · have hmap : l.map (fun j => wx R j ^ Function.update e i (e i + 1) j) =
            l.map (fun j => wx R j ^ e j) := by
          refine List.map_congr_left fun j hj => ?_
          have hne : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update, hne]
        simp only [List.map_cons, List.prod_cons, Function.update_self, hmap, pow_succ', mul_assoc]
      · have hne : a ≠ i := fun h => hnd.1 (h ▸ hl)
        have hcomm : wx R i * wx R a ^ e a = wx R a ^ e a * wx R i := by
          exact Commute.pow_right (WeylAlgebra.of_inl_mul_comm R i a) (e a)
        simp only [List.map_cons, List.prod_cons, Function.update_of_ne hne]
        rw [← mul_assoc, hcomm, mul_assoc, ih hnd.2 hl]
  exact haux (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i)

lemma wy_mul_wyProd (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wy R i * wyProd R e = wyProd R (Function.update e i (e i + 1)) := by
  have haux : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      wy R i * (l.map (fun j => wy R j ^ e j)).prod =
        (l.map (fun j => wy R j ^ Function.update e i (e i + 1) j)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with rfl | hl
      · have hmap : l.map (fun j => wy R j ^ Function.update e i (e i + 1) j) =
            l.map (fun j => wy R j ^ e j) := by
          refine List.map_congr_left fun j hj => ?_
          have hne : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update, hne]
        simp only [List.map_cons, List.prod_cons, Function.update_self, hmap, pow_succ', mul_assoc]
      · have hne : a ≠ i := fun h => hnd.1 (h ▸ hl)
        have hcomm : wy R i * wy R a ^ e a = wy R a ^ e a * wy R i := by
          exact Commute.pow_right (WeylAlgebra.of_inr_mul_comm R i a) (e a)
        simp only [List.map_cons, List.prod_cons, Function.update_of_ne hne]
        rw [← mul_assoc, hcomm, mul_assoc, ih hnd.2 hl]
  exact haux (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i)

lemma wy_mul_wxProd (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wy R i * wxProd R e =
      wxProd R e * wy R i - (e i : W R n) * wxProd R (Function.update e i (e i - 1)) := by
  have haux : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      wy R i * (l.map (fun j => wx R j ^ e j)).prod =
        (l.map (fun j => wx R j ^ e j)).prod * wy R i -
          (e i : W R n) * (l.map (fun j => wx R j ^ Function.update e i (e i - 1) j)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with rfl | hl
      · have hmap : l.map (fun j => wx R j ^ Function.update e i (e i - 1) j) =
            l.map (fun j => wx R j ^ e j) := by
          refine List.map_congr_left fun j hj => ?_
          have hne : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update, hne]
        have hcomm_l : wy R i * (l.map (fun j => wx R j ^ e j)).prod =
            (l.map (fun j => wx R j ^ e j)).prod * wy R i := by
          have hmem_ne : ∀ j ∈ l, j ≠ i := fun j hj h => hnd.1 (h ▸ hj)
          clear ih hnd hmem hmap
          induction l with
          | nil => simp
          | cons b l' ihl =>
            simp only [List.map_cons, List.prod_cons]
            have hne : b ≠ i := hmem_ne b (by simp)
            have hc : wy R i * wx R b ^ e b = wx R b ^ e b * wy R i :=
              Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hne).symm (e b)
            rw [← mul_assoc, hc, mul_assoc, ihl (fun j hj => hmem_ne j (by simp [hj])), ← mul_assoc]
        simp only [List.map_cons, List.prod_cons, Function.update_self, hmap]
        rw [← mul_assoc, wy_mul_wx_pow, sub_mul, mul_assoc, hcomm_l, ← mul_assoc, mul_assoc]
        noncomm_ring
      · have hne : a ≠ i := fun h => hnd.1 (h ▸ hl)
        have hcomm : wy R i * wx R a ^ e a = wx R a ^ e a * wy R i :=
          Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hne).symm (e a)
        simp only [List.map_cons, List.prod_cons, Function.update_of_ne hne]
        rw [← mul_assoc, hcomm, mul_assoc, ih hnd.2 hl, mul_sub, ← mul_assoc]
        have hnat : wx R a ^ e a * ((e i : W R n) *
            (l.map (fun j => wx R j ^ Function.update e i (e i - 1) j)).prod) =
            (e i : W R n) * (wx R a ^ e a *
              (l.map (fun j => wx R j ^ Function.update e i (e i - 1) j)).prod) := by
          rw [← mul_assoc, ← Nat.cast_comm, mul_assoc]
        rw [hnat, ← mul_assoc]
  exact haux (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i)

lemma ofMvPoly_surjective (R : Type*) [CommRing R] (n : ℕ) :
    Function.Surjective (ofMvPoly R n) := by
  let S : Submodule R (W R n) := LinearMap.range (ofMvPoly R n)
  have hmon : ∀ d, weylMonom R (n := n) d ∈ S := fun d =>
    ⟨monomial d 1, by simp⟩
  have hone : (1 : W R n) ∈ S := by
    have h0 : weylMonom R (n := n) 0 = 1 := by
      simp [weylMonom, wxProd, wyProd]
    rw [← h0]; exact hmon 0
  have hwx : ∀ i (a : W R n), a ∈ S → wx R i * a ∈ S := by
    intro i a ha
    obtain ⟨f, rfl⟩ := ha
    induction f using MvPolynomial.induction_on' with
    | monomial d r =>
      have hupd : wx R i * weylMonom R d = weylMonom R (d + Finsupp.single (Sum.inl i) 1) := by
        simp only [weylMonom, ← mul_assoc, wx_mul_wxProd]
        congr 1
        · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
        · congr 1; funext j; simp
      rw [ofMvPoly_monomial, mul_smul_comm, hupd]
      exact S.smul_mem r (hmon _)
    | add p q hp hq =>
      rw [map_add, mul_add]; exact S.add_mem hp hq
  have hwy : ∀ i (a : W R n), a ∈ S → wy R i * a ∈ S := by
    intro i a ha
    obtain ⟨f, rfl⟩ := ha
    induction f using MvPolynomial.induction_on' with
    | monomial d r =>
      have hupd : wy R i * weylMonom R d =
          weylMonom R (d + Finsupp.single (Sum.inr i) 1) -
            (d (Sum.inl i) : R) • weylMonom R (d - Finsupp.single (Sum.inl i) 1) := by
        rw [weylMonom, weylMonom, weylMonom, ← mul_assoc, wy_mul_wxProd, sub_mul, mul_assoc,
          wy_mul_wyProd, mul_assoc, Algebra.smul_def, map_natCast]
        congr 1
        · congr 1
          · congr 1; funext j; simp
          · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
        · congr 1
          congr 1
          · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
          · congr 1; funext j; simp
      rw [ofMvPoly_monomial, mul_smul_comm, hupd]
      exact S.smul_mem r (S.sub_mem (hmon _) (S.smul_mem _ (hmon _)))
    | add p q hp hq =>
      rw [map_add, mul_add]; exact S.add_mem hp hq
  have hmul : ∀ a : W R n, ∀ b ∈ S, a * b ∈ S := by
    intro a
    obtain ⟨x, rfl⟩ : ∃ x : FreeAlgebra R (Fin n ⊕ Fin n), WeylAlgebra.mkAlgHom R (Fin n) x = a :=
      RingQuot.mkAlgHom_surjective R (WeylAlgebra.Rel R (Fin n)) a
    induction x using FreeAlgebra.induction with
    | grade0 r =>
      intro b hb
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact S.smul_mem r hb
    | grade1 v =>
      intro b hb
      rcases v with i | i
      · exact hwx i b hb
      · exact hwy i b hb
    | add x y hx hy =>
      intro b hb
      rw [map_add, add_mul]; exact S.add_mem (hx b hb) (hy b hb)
    | mul x y hx hy =>
      intro b hb
      rw [map_mul, mul_assoc]; exact hx _ (hy b hb)
  intro a
  have ha : a ∈ S := by simpa using hmul a 1 hone
  exact ha

/-- PBW linear equivalence `W R n ≃ₗ[R] P R n`. -/
noncomputable def weylEquiv (R : Type*) [CommRing R] (n : ℕ) : W R n ≃ₗ[R] P R n :=
  LinearEquiv.ofLinearMap (toMvPoly R n) (ofMvPoly R n)
    (LinearMap.ext (toMvPoly_ofMvPoly R n))
    (LinearMap.ext fun a => by
      obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
      simp [toMvPoly_ofMvPoly])

@[simp]
lemma ofMvPoly_toMvPoly (R : Type*) [CommRing R] (n : ℕ) (a : W R n) :
    ofMvPoly R n (toMvPoly R n a) = a :=
  (weylEquiv R n).symm_apply_apply a

lemma toMvPoly_injective (R : Type*) [CommRing R] (n : ℕ) :
    Function.Injective (toMvPoly R n) :=
  (weylEquiv R n).injective

lemma toMvPoly_weylMap {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (a : W R n) :
    toMvPoly S n (weylMap g a) = MvPolynomial.map g (toMvPoly R n a) := by
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
  rw [toMvPoly_ofMvPoly]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    have hmon : weylMap g (weylMonom R d) = weylMonom S d := by
      have hl : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
          weylMap g ((l.map (fun i => wx R i ^ e i)).prod) =
            (l.map (fun i => wx S i ^ e i)).prod := by
        intro l e; induction l with
        | nil => simp
        | cons i l ih =>
          rw [List.map_cons, List.prod_cons, map_mul, map_pow, ih, List.map_cons, List.prod_cons]
          simp [wx]
      have hr : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
          weylMap g ((l.map (fun i => wy R i ^ e i)).prod) =
            (l.map (fun i => wy S i ^ e i)).prod := by
        intro l e; induction l with
        | nil => simp
        | cons i l ih =>
          rw [List.map_cons, List.prod_cons, map_mul, map_pow, ih, List.map_cons, List.prod_cons]
          simp [wy]
      simp only [weylMonom, wxProd, wyProd, map_mul, hl, hr]
    rw [ofMvPoly_monomial, Algebra.smul_def, map_mul,
      weylMap_algebraMap, ← Algebra.smul_def, hmon, map_smul, toMvPoly_weylMonom,
      smul_monomial, smul_eq_mul, mul_one, map_monomial]
  | add p q hp hq =>
    simp [hp, hq]

/- Module 2: Commutator formulas, Char 0 injectivity, degree of products, and Char p center. -/

lemma toMvPoly_wx_mul (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (wx R i * a) = X (Sum.inl i) * toMvPoly R n a := by
  change toEnd R n (wx R i * a) 1 = _
  rw [map_mul, Module.End.mul_apply]
  simp [wx, toEnd, toMvPoly]

lemma toMvPoly_wy_mul (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (wy R i * a) =
      X (Sum.inr i) * toMvPoly R n a - pderiv (Sum.inl i) (toMvPoly R n a) := by
  change toEnd R n (wy R i * a) 1 = _
  rw [map_mul, Module.End.mul_apply]
  simp [wy, toEnd, toMvPoly]

lemma wy_pow_mul_wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) :
    wy R i ^ k * wx R i = wx R i * wy R i ^ k - (k : W R n) * wy R i ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcomm : wy R i * wx R i = wx R i * wy R i - 1 := by
      have h := WeylAlgebra.of_inl_mul_of_inr_self R i
      change wx R i * wy R i = wy R i * wx R i + 1 at h
      calc wy R i * wx R i = (wy R i * wx R i + 1) - 1 := by abel
        _ = wx R i * wy R i - 1 := by rw [← h]
    cases k with
    | zero => simpa using hcomm
    | succ k =>
      have ih' : wy R i ^ (k + 1) * wx R i =
          wx R i * wy R i ^ (k + 1) - ((k + 1 : ℕ) : W R n) * wy R i ^ k := by
        simpa using ih
      calc wy R i ^ (k + 2) * wx R i
          = wy R i * (wy R i ^ (k + 1) * wx R i) := by rw [pow_succ', mul_assoc]
        _ = wy R i * (wx R i * wy R i ^ (k + 1) - ((k + 1 : ℕ) : W R n) * wy R i ^ k) := by
            rw [ih']
        _ = (wy R i * wx R i) * wy R i ^ (k + 1) - ((k + 1 : ℕ) : W R n) * wy R i ^ (k + 1) := by
            rw [mul_sub, ← mul_assoc, ← mul_assoc, ← Nat.cast_comm, mul_assoc, mul_assoc, ← pow_succ']
        _ = (wx R i * wy R i - 1) * wy R i ^ (k + 1) - ((k + 1 : ℕ) : W R n) * wy R i ^ (k + 1) := by
            rw [hcomm]
        _ = wx R i * wy R i ^ (k + 2) - ((k + 2 : ℕ) : W R n) * wy R i ^ (k + 1) := by
            rw [sub_mul, one_mul, mul_assoc, ← pow_succ']
            push_cast
            noncomm_ring

lemma wyProd_mul_wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wyProd R e * wx R i =
      wx R i * wyProd R e - (e i : W R n) * wyProd R (Function.update e i (e i - 1)) := by
  have haux : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      (l.map (fun j => wy R j ^ e j)).prod * wx R i =
        wx R i * (l.map (fun j => wy R j ^ e j)).prod -
          (e i : W R n) * (l.map (fun j => wy R j ^ Function.update e i (e i - 1) j)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with rfl | hl
      · have hmap : l.map (fun j => wy R j ^ Function.update e i (e i - 1) j) =
            l.map (fun j => wy R j ^ e j) := by
          refine List.map_congr_left fun j hj => ?_
          have hne : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update, hne]
        have hcomm_l : (l.map (fun j => wy R j ^ e j)).prod * wx R i =
            wx R i * (l.map (fun j => wy R j ^ e j)).prod := by
          have hmem_ne : ∀ j ∈ l, j ≠ i := fun j hj h => hnd.1 (h ▸ hj)
          clear ih hnd hmem hmap
          induction l with
          | nil => simp
          | cons b l' ihl =>
            simp only [List.map_cons, List.prod_cons]
            have hne : b ≠ i := hmem_ne b (by simp)
            have hc : wy R b ^ e b * wx R i = wx R i * wy R b ^ e b :=
              (Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hne.symm) (e b)).symm
            rw [mul_assoc, ihl (fun j hj => hmem_ne j (by simp [hj])), ← mul_assoc, hc, mul_assoc]
        simp only [List.map_cons, List.prod_cons, Function.update_self, hmap]
        rw [mul_assoc, hcomm_l, ← mul_assoc, wy_pow_mul_wx, sub_mul]
        noncomm_ring
      · have hne : a ≠ i := fun h => hnd.1 (h ▸ hl)
        have hcomm : wy R a ^ e a * wx R i = wx R i * wy R a ^ e a :=
          (Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hne.symm) (e a)).symm
        simp only [List.map_cons, List.prod_cons, Function.update_of_ne hne]
        rw [mul_assoc, ih hnd.2 hl, mul_sub, ← mul_assoc, hcomm, mul_assoc]
        have hnat : wy R a ^ e a * ((e i : W R n) *
            (l.map (fun j => wy R j ^ Function.update e i (e i - 1) j)).prod) =
            (e i : W R n) * (wy R a ^ e a *
              (l.map (fun j => wy R j ^ Function.update e i (e i - 1) j)).prod) := by
          rw [← mul_assoc, ← Nat.cast_comm, mul_assoc]
        rw [hnat]
  exact haux (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i)

lemma wxProd_comm_wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wxProd R e * wx R i = wx R i * wxProd R e := by
  have haux : ∀ (l : List (Fin n)),
      (l.map (fun j => wx R j ^ e j)).prod * wx R i =
        wx R i * (l.map (fun j => wx R j ^ e j)).prod := by
    intro l; induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hc : wx R b ^ e b * wx R i = wx R i * wx R b ^ e b :=
        (Commute.pow_right (WeylAlgebra.of_inl_mul_comm R i b) (e b)).symm
      rw [mul_assoc, ih, ← mul_assoc, hc, mul_assoc]
  exact haux (List.finRange n)

lemma wyProd_mul_wy (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (e : Fin n → ℕ) :
    wyProd R e * wy R i = wyProd R (Function.update e i (e i + 1)) := by
  have haux : ∀ (l : List (Fin n)),
      (l.map (fun j => wy R j ^ e j)).prod * wy R i =
        wy R i * (l.map (fun j => wy R j ^ e j)).prod := by
    intro l; induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hc : wy R b ^ e b * wy R i = wy R i * wy R b ^ e b :=
        (Commute.pow_right (WeylAlgebra.of_inr_mul_comm R i b) (e b)).symm
      rw [mul_assoc, ih, ← mul_assoc, hc, mul_assoc]
  rw [wyProd, haux, ← wyProd, wy_mul_wyProd]

lemma toMvPoly_mul_wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (a * wx R i) =
      X (Sum.inl i) * toMvPoly R n a - pderiv (Sum.inr i) (toMvPoly R n a) := by
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
  rw [toMvPoly_ofMvPoly]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    have hupd : weylMonom R d * wx R i =
        weylMonom R (d + Finsupp.single (Sum.inl i) 1) -
          (d (Sum.inr i) : R) • weylMonom R (d - Finsupp.single (Sum.inr i) 1) := by
      rw [weylMonom, weylMonom, weylMonom, mul_assoc, wyProd_mul_wx, mul_sub, ← mul_assoc,
        wxProd_comm_wx, wx_mul_wxProd, Algebra.smul_def, map_natCast]
      have hnat : wxProd R (fun j => d (Sum.inl j)) *
          ((d (Sum.inr i) : W R n) * wyProd R (Function.update (fun j => d (Sum.inr j)) i (d (Sum.inr i) - 1))) =
          (d (Sum.inr i) : W R n) * (wxProd R (fun j => d (Sum.inl j)) *
            wyProd R (Function.update (fun j => d (Sum.inr j)) i (d (Sum.inr i) - 1))) := by
        rw [← mul_assoc, ← Nat.cast_comm, mul_assoc]
      rw [hnat]
      congr 1
      · congr 1
        · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
        · congr 1; funext j; simp
      · congr 1
        congr 1
        · congr 1; funext j; simp
        · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
    rw [ofMvPoly_monomial, smul_mul_assoc, hupd, map_smul, map_sub, map_smul,
      toMvPoly_weylMonom, toMvPoly_weylMonom, pderiv_monomial]
    rw [show (X (Sum.inl i) : P R n) * monomial d r = monomial (d + Finsupp.single (Sum.inl i) 1) r by
      rw [X, monomial_mul, one_mul, add_comm]]
    simp only [smul_sub, smul_monomial, smul_eq_mul, mul_one]
  | add p q hp hq =>
    simp only [map_add, add_mul, hp, hq, mul_add]; ring

lemma toMvPoly_mul_wy (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (a * wy R i) = X (Sum.inr i) * toMvPoly R n a := by
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
  rw [toMvPoly_ofMvPoly]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    have hupd : weylMonom R d * wy R i = weylMonom R (d + Finsupp.single (Sum.inr i) 1) := by
      rw [weylMonom, weylMonom, mul_assoc, wyProd_mul_wy]
      congr 1
      · congr 1; funext j; simp
      · congr 1; funext j; by_cases h : j = i <;> simp [Function.update, h]
    rw [ofMvPoly_monomial, smul_mul_assoc, hupd, map_smul, toMvPoly_weylMonom, smul_monomial,
      smul_eq_mul, mul_one, X, monomial_mul, one_mul, add_comm]
  | add p q hp hq =>
    simp only [map_add, add_mul, hp, hq, mul_add]

lemma toMvPoly_comm_wx (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (wx R i * a - a * wx R i) = pderiv (Sum.inr i) (toMvPoly R n a) := by
  rw [map_sub, toMvPoly_wx_mul, toMvPoly_mul_wx]; ring

lemma toMvPoly_comm_wy (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) (a : W R n) :
    toMvPoly R n (wy R i * a - a * wy R i) = - pderiv (Sum.inl i) (toMvPoly R n a) := by
  rw [map_sub, toMvPoly_wy_mul, toMvPoly_mul_wy]; ring

/- Characteristic 0 simplicity -> every endomorphism of `W L n` is injective. -/

lemma totalDegree_pderiv_lt {R σ : Type*} [CommRing R] [DecidableEq σ] (v : σ)
    (f : MvPolynomial σ R) (hf : 0 < f.totalDegree) :
    (pderiv v f).totalDegree < f.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hf]
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hd
  have hmem : d + Finsupp.single v 1 ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0; simp [h0] at hd
  have hle : (d + Finsupp.single v 1).sum (fun _ k => k) ≤ f.totalDegree :=
    Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ k => k) hmem
  have hsum : (d + Finsupp.single v 1).sum (fun _ k => k) = d.sum (fun _ k => k) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

lemma weylAlgHom_injective {L : Type*} [Field L] [CharZero L] {n : ℕ}
    (φ : W L n →ₐ[L] W L n) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  have haux : ∀ k : ℕ, ∀ a : W L n, (toMvPoly L n a).totalDegree ≤ k → φ a = 0 → a = 0 := by
    intro k
    induction k with
    | zero =>
      intro a hdeg hfa
      have hconst : toMvPoly L n a = C ((toMvPoly L n a).coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
      have ha : a = algebraMap L (W L n) ((toMvPoly L n a).coeff 0) := by
        apply toMvPoly_injective L n
        rw [Algebra.algebraMap_eq_smul_one, map_smul]
        have h1 : toMvPoly L n 1 = 1 := by
          change toEnd L n 1 1 = 1; simp
        rw [h1, smul_eq_C_mul, mul_one, ← hconst]
      rw [ha, AlgHom.commutes] at hfa
      by_cases hc : (toMvPoly L n a).coeff 0 = 0
      · rw [ha, hc, map_zero]
      · have h10 : (1 : W L n) = 0 := by
          have := congrArg (fun x => ((toMvPoly L n a).coeff 0)⁻¹ • x) hfa
          simp only [smul_zero] at this
          rw [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
          exact this
        have h11 : toMvPoly L n (1 : W L n) = 1 := by change toEnd L n 1 1 = 1; simp
        have h00 : toMvPoly L n (0 : W L n) = 0 := map_zero _
        rw [h10, h00] at h11
        exact absurd h11.symm one_ne_zero
    | succ k ih =>
      intro a hdeg hfa
      by_cases h0 : (toMvPoly L n a).totalDegree = 0
      · exact ih a (by omega) hfa
      · have hpos : 0 < (toMvPoly L n a).totalDegree := Nat.pos_of_ne_zero h0
        -- Every partial derivative of `toMvPoly L n a` is 0
        have hpderiv_zero : ∀ v : Fin n ⊕ Fin n, pderiv v (toMvPoly L n a) = 0 := by
          intro v
          rcases v with i | i
          · have hcomm_ker : φ (wy L i * a - a * wy L i) = 0 := by
              simp [map_sub, map_mul, hfa]
            have hdeg' : (toMvPoly L n (wy L i * a - a * wy L i)).totalDegree ≤ k := by
              rw [toMvPoly_comm_wy, MvPolynomial.totalDegree_neg]
              have := totalDegree_pderiv_lt (Sum.inl i) (toMvPoly L n a) hpos
              omega
            have hz := ih _ hdeg' hcomm_ker
            have := congrArg (toMvPoly L n) hz
            rw [toMvPoly_comm_wy, map_zero, neg_eq_zero] at this
            exact this
          · have hcomm_ker : φ (wx L i * a - a * wx L i) = 0 := by
              simp [map_sub, map_mul, hfa]
            have hdeg' : (toMvPoly L n (wx L i * a - a * wx L i)).totalDegree ≤ k := by
              rw [toMvPoly_comm_wx]
              have := totalDegree_pderiv_lt (Sum.inr i) (toMvPoly L n a) hpos
              omega
            have hz := ih _ hdeg' hcomm_ker
            have := congrArg (toMvPoly L n) hz
            rw [toMvPoly_comm_wx, map_zero] at this
            exact this
        -- Since `totalDegree > 0`, some monomial has a variable with exponent > 0, contradiction!
        have hne : (toMvPoly L n a).support.Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have : (toMvPoly L n a).totalDegree = 0 := by simp [MvPolynomial.totalDegree, hemp]
          omega
        obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hne (fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m)
        have hdpos : 0 < d.sum (fun _ m => m) := by
          rw [← hdeq]; exact hpos
        obtain ⟨v, hv⟩ : ∃ v, 0 < d v := by
          by_contra hall
          push Not at hall
          have hdz : d.sum (fun _ m => m) = 0 := Finset.sum_eq_zero fun v _ => Nat.le_zero.mp (hall v)
          omega
        have hcoeff := congrArg (fun p => p.coeff (d - Finsupp.single v 1)) (hpderiv_zero v)
        rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero] at hcoeff
        have hadd : (d - Finsupp.single v 1) + Finsupp.single v 1 = d := by
          ext w; by_cases h : w = v
          · subst h; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
          · simp [Finsupp.single_eq_of_ne h]
        rw [hadd] at hcoeff
        have hcoeff_ne : (toMvPoly L n a).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have hdv_ne : (((d - Finsupp.single v (1 : ℕ)) v : L) + 1) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero ((d - Finsupp.single v (1 : ℕ)) v)
        exact absurd hcoeff (mul_ne_zero hcoeff_ne hdv_ne)
  intro a hfa
  exact haux _ a le_rfl hfa

/- Module 2b: Degree of products over a domain and characteristic p center embedding. -/

lemma totalDegree_X_pow_le_local {R σ : Type*} [CommRing R] (v : σ) (k : ℕ) :
    ((X v : MvPolynomial σ R) ^ k).totalDegree ≤ k := by
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  have hX : (X v : MvPolynomial σ R).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd
    have hsub : (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} := by
      rw [X]; exact MvPolynomial.support_monomial_subset
    rw [Finset.mem_singleton.mp (hsub hd), Finsupp.sum_single_index rfl]
  nlinarith

lemma support_pderiv_deg_add_one_le {R σ : Type*} [CommRing R] [DecidableEq σ] (v : σ)
    (g : MvPolynomial σ R) {d : σ →₀ ℕ} (hd : d ∈ (pderiv v g).support) :
    d.sum (fun _ k => k) + 1 ≤ g.totalDegree := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hd
  have hmem : d + Finsupp.single v 1 ∈ g.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0; simp [h0] at hd
  have hle : (d + Finsupp.single v 1).sum (fun _ k => k) ≤ g.totalDegree :=
    Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ k => k) hmem
  have hsum : (d + Finsupp.single v 1).sum (fun _ k => k) = d.sum (fun _ k => k) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

lemma support_add_deg_le {R σ : Type*} [CommRing R] [DecidableEq σ] {f g : MvPolynomial σ R} {m : ℕ}
    (hf : ∀ d ∈ f.support, d.sum (fun _ k => k) ≤ m)
    (hg : ∀ d ∈ g.support, d.sum (fun _ k => k) ≤ m) :
    ∀ d ∈ (f + g).support, d.sum (fun _ k => k) ≤ m := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hf d h
  · exact hg d h

lemma support_sub_deg_le {R σ : Type*} [CommRing R] [DecidableEq σ] {f g : MvPolynomial σ R} {m : ℕ}
    (hf : ∀ d ∈ f.support, d.sum (fun _ k => k) ≤ m)
    (hg : ∀ d ∈ g.support, d.sum (fun _ k => k) ≤ m) :
    ∀ d ∈ (f - g).support, d.sum (fun _ k => k) ≤ m := by
  rw [sub_eq_add_neg]
  exact support_add_deg_le hf (fun d hd => hg d (by rwa [MvPolynomial.support_neg] at hd))

lemma toEnd_wy_pow_sub_deg {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) (g : P R n) :
    ∀ d ∈ (toEnd R n (wy R i ^ k) g - X (Sum.inr i) ^ k * g).support,
      d.sum (fun _ m => m) + 1 ≤ k + g.totalDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro d hd
    have hsplit : toEnd R n (wy R i ^ (k + 1)) g - X (Sum.inr i) ^ (k + 1) * g =
        (X (Sum.inr i) * (toEnd R n (wy R i ^ k) g - X (Sum.inr i) ^ k * g)) -
          pderiv (Sum.inl i) (toEnd R n (wy R i ^ k) g) := by
      have hwy_app : ∀ h : P R n, toEnd R n (wy R i) h = X (Sum.inr i) * h - pderiv (Sum.inl i) h := by
        intro h; simp [wy, toEnd]
      rw [pow_succ', map_mul, Module.End.mul_apply, hwy_app, pow_succ']; ring
    rw [hsplit] at hd
    have h1 : ∀ d' ∈ (X (Sum.inr i) * (toEnd R n (wy R i ^ k) g - X (Sum.inr i) ^ k * g)).support,
        d'.sum (fun _ m => m) + 1 ≤ (k + 1) + g.totalDegree := by
      intro d' hd'
      have hmem : d' ∈ (X (Sum.inr i) : P R n).support +
          (toEnd R n (wy R i ^ k) g - X (Sum.inr i) ^ k * g).support :=
        MvPolynomial.support_mul _ _ hd'
      rcases Finset.mem_add.mp hmem with ⟨d1, hd1, d2, hd2, rfl⟩
      have hd1' : d1 = Finsupp.single (Sum.inr i) 1 := by
        have hsub : (X (Sum.inr i) : P R n).support ⊆ {Finsupp.single (Sum.inr i) 1} := by
          rw [X]; exact MvPolynomial.support_monomial_subset
        exact Finset.mem_singleton.mp (hsub hd1)
      subst hd1'
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      have := ih d2 hd2
      omega
    have hdeg_end : (toEnd R n (wy R i ^ k) g).totalDegree ≤ k + g.totalDegree := by
      have heq : toEnd R n (wy R i ^ k) g =
          (toEnd R n (wy R i ^ k) g - X (Sum.inr i) ^ k * g) + X (Sum.inr i) ^ k * g := by ring
      rw [heq]
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
        intro d' hd'; have := ih d' hd'; omega
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have hX := totalDegree_X_pow_le_local (R := R) (Sum.inr i : Fin n ⊕ Fin n) k
        omega
    have h2 : ∀ d' ∈ (pderiv (Sum.inl i) (toEnd R n (wy R i ^ k) g)).support,
        d'.sum (fun _ m => m) + 1 ≤ (k + 1) + g.totalDegree := by
      intro d' hd'
      have := support_pderiv_deg_add_one_le (Sum.inl i) _ hd'
      omega
    have := support_sub_deg_le
      (fun d' hd' => show d'.sum (fun _ m => m) ≤ (k + 1) + g.totalDegree - 1 by
        have := h1 d' hd'; omega)
      (fun d' hd' => show d'.sum (fun _ m => m) ≤ (k + 1) + g.totalDegree - 1 by
        have := h2 d' hd'; omega)
      d hd
    omega

lemma toEnd_list_wy_sub_deg {R : Type*} [CommRing R] {n : ℕ} (l : List (Fin n)) (e : Fin n → ℕ)
    (g : P R n) :
    ∀ d ∈ (toEnd R n ((l.map (fun i => wy R i ^ e i)).prod) g -
        (l.map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod * g).support,
      d.sum (fun _ m => m) + 1 ≤ (l.map e).sum + g.totalDegree := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro d hd
    set Q := toEnd R n ((l.map (fun i => wy R i ^ e i)).prod) g
    set P0 := (l.map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod * g
    have hsplit : toEnd R n (((a :: l).map (fun i => wy R i ^ e i)).prod) g -
        ((a :: l).map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod * g =
        (toEnd R n (wy R a ^ e a) Q - X (Sum.inr a) ^ e a * Q) +
          X (Sum.inr a) ^ e a * (Q - P0) := by
      simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, Q, P0]
      ring
    rw [hsplit] at hd
    have hP0_deg : ((l.map (fun i => (X (Sum.inr i) : P R n) ^ e i)).prod).totalDegree ≤ (l.map e).sum := by
      clear ih Q P0 hsplit hd d
      induction l with
      | nil => simp
      | cons b l' ihl =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have hXb := totalDegree_X_pow_le_local (R := R) (Sum.inr b : Fin n ⊕ Fin n) (e b)
        omega
    have hdegQ : Q.totalDegree ≤ (l.map e).sum + g.totalDegree := by
      have heq : Q = (Q - P0) + P0 := by ring
      rw [heq]
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
        intro d' hd'; have := ih d' hd'; omega
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        omega
    have h1 : ∀ d' ∈ (toEnd R n (wy R a ^ e a) Q - X (Sum.inr a) ^ e a * Q).support,
        d'.sum (fun _ m => m) + 1 ≤ ((a :: l).map e).sum + g.totalDegree := by
      intro d' hd'
      have := toEnd_wy_pow_sub_deg a (e a) Q d' hd'
      simp only [List.map_cons, List.sum_cons]
      omega
    have h2 : ∀ d' ∈ (X (Sum.inr a) ^ e a * (Q - P0)).support,
        d'.sum (fun _ m => m) + 1 ≤ ((a :: l).map e).sum + g.totalDegree := by
      intro d' hd'
      have hmem : d' ∈ ((X (Sum.inr a) : P R n) ^ e a).support + (Q - P0).support :=
        MvPolynomial.support_mul _ _ hd'
      rcases Finset.mem_add.mp hmem with ⟨d1, hd1, d2, hd2, rfl⟩
      have hd1_le : d1.sum (fun _ m => m) ≤ e a := by
        have h1' : d1.sum (fun _ m => m) ≤ ((X (Sum.inr a) : P R n) ^ e a).totalDegree :=
          Finset.le_sup (f := fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m) hd1
        have h2' := totalDegree_X_pow_le_local (R := R) (Sum.inr a : Fin n ⊕ Fin n) (e a)
        omega
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      have := ih d2 hd2
      simp only [List.map_cons, List.sum_cons]
      omega
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact h1 d h
    · exact h2 d h

lemma list_finRange_sum_eq {n : ℕ} (f : Fin n → ℕ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  have h : (Finset.univ : Finset (Fin n)).val = ↑(List.finRange n) := rfl
  rw [Finset.sum_eq_multiset_sum, h, Multiset.map_coe, Multiset.sum_coe]

lemma toMvPoly_mul_sub_deg {R : Type*} [CommRing R] {n : ℕ} (a b : W R n) :
    ∀ d ∈ (toMvPoly R n (a * b) - toMvPoly R n a * toMvPoly R n b).support,
      d.sum (fun _ m => m) + 1 ≤ (toMvPoly R n a).totalDegree + (toMvPoly R n b).totalDegree := by
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
  rw [toMvPoly_ofMvPoly]
  have hmon : ∀ (d0 : Fin n ⊕ Fin n →₀ ℕ) (r : R),
      ∀ d ∈ (toMvPoly R n (ofMvPoly R n (monomial d0 r) * b) -
          monomial d0 r * toMvPoly R n b).support,
        d.sum (fun _ m => m) + 1 ≤ d0.sum (fun _ m => m) + (toMvPoly R n b).totalDegree := by
    intro d0 r d hd
    have heq : toMvPoly R n (ofMvPoly R n (monomial d0 r) * b) - monomial d0 r * toMvPoly R n b =
        r • ((∏ i : Fin n, (X (Sum.inl i) : P R n) ^ d0 (Sum.inl i)) *
          (toEnd R n (wyProd R (fun i => d0 (Sum.inr i))) (toMvPoly R n b) -
            (((List.finRange n).map (fun i => (X (Sum.inr i) : P R n) ^ d0 (Sum.inr i))).prod) *
              toMvPoly R n b)) := by
      rw [ofMvPoly_monomial, smul_mul_assoc, map_smul]
      have h1 : toMvPoly R n (weylMonom R d0 * b) =
          (∏ i : Fin n, (X (Sum.inl i) : P R n) ^ d0 (Sum.inl i)) *
            toEnd R n (wyProd R (fun i => d0 (Sum.inr i))) (toMvPoly R n b) := by
        change toEnd R n (wxProd R _ * wyProd R _ * b) 1 = _
        rw [mul_assoc, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
          wxProd, toEnd_list_wx, list_finRange_prod_eq]
        rfl
      have h2 : monomial d0 r = r • ((∏ i : Fin n, (X (Sum.inl i) : P R n) ^ d0 (Sum.inl i)) *
          ((List.finRange n).map (fun i => (X (Sum.inr i) : P R n) ^ d0 (Sum.inr i))).prod) := by
        rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type,
          list_finRange_prod_eq, smul_eq_C_mul]
      rw [h1, h2, smul_mul_assoc, ← smul_sub, mul_assoc, ← mul_sub]
    rw [heq] at hd
    have hd' := MvPolynomial.support_smul hd
    have hmem := MvPolynomial.support_mul _ _ hd'
    rcases Finset.mem_add.mp hmem with ⟨d1, hd1, d2, hd2, rfl⟩
    have hd1_le : d1.sum (fun _ m => m) ≤ ∑ i : Fin n, d0 (Sum.inl i) := by
      have h1' : d1.sum (fun _ m => m) ≤
          (∏ i : Fin n, (X (Sum.inl i) : P R n) ^ d0 (Sum.inl i)).totalDegree :=
        Finset.le_sup (f := fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m) hd1
      have h2' : (∏ i : Fin n, (X (Sum.inl i) : P R n) ^ d0 (Sum.inl i)).totalDegree ≤
          ∑ i : Fin n, d0 (Sum.inl i) := by
        refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
        refine Finset.sum_le_sum fun i _ => ?_
        exact totalDegree_X_pow_le_local (R := R) (Sum.inl i : Fin n ⊕ Fin n) (d0 (Sum.inl i))
      omega
    have hd2_le := toEnd_list_wy_sub_deg (List.finRange n) (fun i => d0 (Sum.inr i))
      (toMvPoly R n b) d2 hd2
    rw [list_finRange_sum_eq] at hd2_le
    have hd0_sum : d0.sum (fun _ m => m) =
        (∑ i : Fin n, d0 (Sum.inl i)) + (∑ i : Fin n, d0 (Sum.inr i)) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    omega
  have hf_eq : f = ∑ d0 ∈ f.support, monomial d0 (f.coeff d0) := f.as_sum
  have hdiff : toMvPoly R n (ofMvPoly R n f * b) - f * toMvPoly R n b =
      ∑ d0 ∈ f.support, (toMvPoly R n (ofMvPoly R n (monomial d0 (f.coeff d0)) * b) -
        monomial d0 (f.coeff d0) * toMvPoly R n b) := by
    conv_lhs => rw [hf_eq]
    rw [map_sum, Finset.sum_mul, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  intro d hd
  rw [hdiff] at hd
  have hsub := MvPolynomial.support_sum hd
  rcases Finset.mem_biUnion.mp hsub with ⟨d0, hd0, hdd0⟩
  have h1 := hmon d0 (f.coeff d0) d hdd0
  have h2 : d0.sum (fun _ m => m) ≤ f.totalDegree :=
    Finset.le_sup (f := fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m) hd0
  omega

lemma mvPoly_totalDegree_mul_of_isDomain {R σ : Type*} [CommRing R] [IsDomain R]
    {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).totalDegree = f.totalDegree + g.totalDegree := by
  classical
  refine le_antisymm (MvPolynomial.totalDegree_mul f g) ?_
  have hfa : MvPolynomial.homogeneousComponent f.totalDegree f ≠ 0 := by
    intro h0
    have hne : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
    obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ m => m)
    have hdeg : Finsupp.degree d = f.totalDegree := hdeq.symm
    have hc := congrArg (fun p => p.coeff d) h0
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg, MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  have hgb : MvPolynomial.homogeneousComponent g.totalDegree g ≠ 0 := by
    intro h0
    have hne : g.support.Nonempty := MvPolynomial.support_nonempty.mpr hg
    obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ m => m)
    have hdeg : Finsupp.degree d = g.totalDegree := hdeq.symm
    have hc := congrArg (fun p => p.coeff d) h0
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg, MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  have hprod_ne : MvPolynomial.homogeneousComponent f.totalDegree f *
      MvPolynomial.homogeneousComponent g.totalDegree g ≠ 0 := mul_ne_zero hfa hgb
  have hhom : MvPolynomial.homogeneousComponent (f.totalDegree + g.totalDegree) (f * g) =
      MvPolynomial.homogeneousComponent f.totalDegree f *
        MvPolynomial.homogeneousComponent g.totalDegree g := by
    ext d
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    by_cases hd : Finsupp.degree d = f.totalDegree + g.totalDegree
    · rw [if_pos hd]
      refine Finset.sum_congr rfl fun ⟨a, b⟩ hab => ?_
      have hab' : a + b = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
      have hdeg_add : Finsupp.degree a + Finsupp.degree b = f.totalDegree + g.totalDegree := by
        rw [← map_add, hab', hd]
      by_cases ha : Finsupp.degree a = f.totalDegree
      · have hb : Finsupp.degree b = g.totalDegree := by omega
        rw [if_pos ha, if_pos hb]
      · rw [if_neg ha, zero_mul]
        by_cases hfa' : a ∈ f.support
        · have hale : Finsupp.degree a ≤ f.totalDegree :=
            Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ m => m) hfa'
          have hblt : g.totalDegree < Finsupp.degree b := by omega
          have hbg : b ∉ g.support := fun hgb' => by
            have hble : Finsupp.degree b ≤ g.totalDegree :=
              Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ m => m) hgb'
            omega
          rw [MvPolynomial.notMem_support_iff.mp hbg, mul_zero]
        · rw [MvPolynomial.notMem_support_iff.mp hfa', zero_mul]
    · rw [if_neg hd]
      symm
      refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
      have hab' : a + b = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
      split_ifs with ha hb
      · exfalso; apply hd; rw [← hab', map_add, ha, hb]
      · simp
      · simp
      · simp
  have hfg_hom_ne : MvPolynomial.homogeneousComponent (f.totalDegree + g.totalDegree) (f * g) ≠ 0 :=
    hhom.symm ▸ hprod_ne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hfg_hom_ne
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_homogeneousComponent] at hd
  split_ifs at hd with hdeg
  · rw [← hdeg]
    exact Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ m => m)
      (MvPolynomial.mem_support_iff.mpr hd)
  · exact absurd rfl hd

lemma toMvPoly_mul_totalDegree {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {a b : W R n} (ha : a ≠ 0) (hb : b ≠ 0) :
    (toMvPoly R n (a * b)).totalDegree =
      (toMvPoly R n a).totalDegree + (toMvPoly R n b).totalDegree := by
  have hfa : toMvPoly R n a ≠ 0 := fun h => ha (toMvPoly_injective R n (by simpa using h))
  have hfb : toMvPoly R n b ≠ 0 := fun h => hb (toMvPoly_injective R n (by simpa using h))
  have hprod := mvPoly_totalDegree_mul_of_isDomain hfa hfb
  have hdiff := toMvPoly_mul_sub_deg a b
  refine le_antisymm ?_ ?_
  · have heq : toMvPoly R n (a * b) =
        (toMvPoly R n (a * b) - toMvPoly R n a * toMvPoly R n b) +
          toMvPoly R n a * toMvPoly R n b := by ring
    rw [heq]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ (by rw [hprod]))
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd; have := hdiff d hd; omega
  · have hne : (toMvPoly R n a * toMvPoly R n b).support.Nonempty :=
      MvPolynomial.support_nonempty.mpr (mul_ne_zero hfa hfb)
    obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hne
      (fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m)
    have hdsum : d.sum (fun _ m => m) =
        (toMvPoly R n a).totalDegree + (toMvPoly R n b).totalDegree := by
      change (toMvPoly R n a * toMvPoly R n b).totalDegree = _ at hdeq
      rw [← hdeq, hprod]
    have hd_not_diff : d ∉ (toMvPoly R n (a * b) - toMvPoly R n a * toMvPoly R n b).support := by
      intro hmem; have := hdiff d hmem; omega
    have hcoeff_eq : (toMvPoly R n (a * b)).coeff d =
        (toMvPoly R n a * toMvPoly R n b).coeff d := by
      have h0 := MvPolynomial.notMem_support_iff.mp hd_not_diff
      rw [MvPolynomial.coeff_sub] at h0
      exact sub_eq_zero.mp h0
    have hd_ab : d ∈ (toMvPoly R n (a * b)).support := by
      rw [MvPolynomial.mem_support_iff, hcoeff_eq]
      exact MvPolynomial.mem_support_iff.mp hd
    rw [← hdsum]
    exact Finset.le_sup (f := fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m) hd_ab

lemma toMvPoly_pow_totalDegree {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {a : W R n} (ha : a ≠ 0) (k : ℕ) :
    (toMvPoly R n (a ^ k)).totalDegree = k * (toMvPoly R n a).totalDegree := by
  induction k with
  | zero =>
    have h1 : toMvPoly R n (1 : W R n) = 1 := by change toEnd R n 1 1 = 1; simp
    simp [h1]
  | succ k ih =>
    have hne : a ^ k ≠ 0 := by
      clear ih
      induction k with
      | zero =>
        intro h10
        rw [pow_zero] at h10
        have h1 : toMvPoly R n (1 : W R n) = 1 := by change toEnd R n 1 1 = 1; simp
        rw [h10, map_zero] at h1
        exact one_ne_zero h1.symm
      | succ k ihk =>
        intro h0
        have hfa : toMvPoly R n (a ^ k) ≠ 0 := fun h => ihk (toMvPoly_injective R n (by simpa using h))
        have hfb : toMvPoly R n a ≠ 0 := fun h => ha (toMvPoly_injective R n (by simpa using h))
        have hdiff := toMvPoly_mul_sub_deg (a ^ k) a
        rw [pow_succ] at h0
        rw [h0, map_zero, zero_sub, MvPolynomial.support_neg] at hdiff
        have hne' := MvPolynomial.support_nonempty.mpr (mul_ne_zero hfa hfb)
        obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hne'
          (fun s : Fin n ⊕ Fin n →₀ ℕ => s.sum fun _ m => m)
        have h1 := hdiff d hd
        have h2 := mvPoly_totalDegree_mul_of_isDomain hfa hfb
        have hdeq' : (toMvPoly R n (a ^ k) * toMvPoly R n a).totalDegree = d.sum (fun _ m => m) := hdeq
        omega
    rw [pow_succ, toMvPoly_mul_totalDegree hne ha, ih, add_mul, one_mul]

/- Module 3a: Characteristic p center embedding `centerEmb` and `p^n`-dim lower bound. -/

lemma wx_pow_p_mem_center (R : Type*) [CommRing R] {n p : ℕ} [CharP R p] (i : Fin n) :
    wx R i ^ p ∈ Subalgebra.center R (W R n) := by
  rw [Subalgebra.mem_center_iff]
  have hcomm_gen : ∀ v : Fin n ⊕ Fin n, WeylAlgebra.of R v * wx R i ^ p = wx R i ^ p * WeylAlgebra.of R v := by
    intro v
    rcases v with j | j
    · exact (Commute.pow_right (WeylAlgebra.of_inl_mul_comm R j i) p).eq
    · by_cases hij : i = j
      · subst hij
        change wy R i * wx R i ^ p = wx R i ^ p * wy R i
        rw [wy_mul_wx_pow]
        have hp0 : (p : W R n) = 0 := by
          rw [← map_natCast (algebraMap R (W R n)), CharP.cast_eq_zero, map_zero]
        rw [hp0, zero_mul, sub_zero]
      · exact (Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij).symm p).eq
  intro a
  obtain ⟨x, rfl⟩ : ∃ x : FreeAlgebra R (Fin n ⊕ Fin n), WeylAlgebra.mkAlgHom R (Fin n) x = a :=
    RingQuot.mkAlgHom_surjective R (WeylAlgebra.Rel R (Fin n)) a
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.commutes]
  | grade1 v =>
    exact hcomm_gen v
  | add x y hx hy =>
    rw [map_add, add_mul, mul_add, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

lemma wy_pow_p_mem_center (R : Type*) [CommRing R] {n p : ℕ} [CharP R p] (i : Fin n) :
    wy R i ^ p ∈ Subalgebra.center R (W R n) := by
  rw [Subalgebra.mem_center_iff]
  have hcomm_gen : ∀ v : Fin n ⊕ Fin n, WeylAlgebra.of R v * wy R i ^ p = wy R i ^ p * WeylAlgebra.of R v := by
    intro v
    rcases v with j | j
    · by_cases hij : j = i
      · subst hij
        change wx R j * wy R j ^ p = wy R j ^ p * wx R j
        rw [wy_pow_mul_wx]
        have hp0 : (p : W R n) = 0 := by
          rw [← map_natCast (algebraMap R (W R n)), CharP.cast_eq_zero, map_zero]
        rw [hp0, zero_mul, sub_zero]
      · exact (Commute.pow_right (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij) p).eq
    · exact (Commute.pow_right (WeylAlgebra.of_inr_mul_comm R j i) p).eq
  intro a
  obtain ⟨x, rfl⟩ : ∃ x : FreeAlgebra R (Fin n ⊕ Fin n), WeylAlgebra.mkAlgHom R (Fin n) x = a :=
    RingQuot.mkAlgHom_surjective R (WeylAlgebra.Rel R (Fin n)) a
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.commutes]
  | grade1 v =>
    exact hcomm_gen v
  | add x y hx hy =>
    rw [map_add, add_mul, mul_add, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

/-- Center embedding `P R n →ₐ[R] W R n` in characteristic `p`, sending `X v ↦ (of R v)^p`. -/
noncomputable def centerEmb (R : Type*) [CommRing R] (n p : ℕ) [CharP R p] :
    P R n →ₐ[R] W R n :=
  (Subalgebra.val (Subalgebra.center R (W R n))).comp
    (MvPolynomial.aeval (fun v : Fin n ⊕ Fin n =>
      (⟨(WeylAlgebra.of R v) ^ p, by
        rcases v with i | i
        · exact wx_pow_p_mem_center R i
        · exact wy_pow_p_mem_center R i⟩ : Subalgebra.center R (W R n))))

@[simp]
lemma centerEmb_X (R : Type*) [CommRing R] (n p : ℕ) [CharP R p] (v : Fin n ⊕ Fin n) :
    centerEmb R n p (X v) = (WeylAlgebra.of R v) ^ p := by
  simp [centerEmb]

lemma centerEmb_mem_center (R : Type*) [CommRing R] (n p : ℕ) [CharP R p] (f : P R n) :
    centerEmb R n p f ∈ Subalgebra.center R (W R n) := by
  unfold centerEmb
  exact Subtype.prop _

lemma toMvPoly_centerEmb (R : Type*) [CommRing R] (n p : ℕ) [CharP R p] (f : P R n) :
    toMvPoly R n (centerEmb R n p f) = MvPolynomial.expand p f := by
  let g : P R n →ₐ[R] Subalgebra.center R (W R n) :=
    MvPolynomial.aeval (fun v : Fin n ⊕ Fin n =>
      (⟨(WeylAlgebra.of R v) ^ p, by
        rcases v with i | i
        · exact wx_pow_p_mem_center R i
        · exact wy_pow_p_mem_center R i⟩ : Subalgebra.center R (W R n)))
  have hmon : ∀ (d : Fin n ⊕ Fin n →₀ ℕ),
      centerEmb R n p (monomial d 1) = weylMonom R (p • d) := by
    intro d
    change (g (monomial d 1)).val = weylMonom R (p • d)
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fintype.prod_sum_type, map_mul, map_prod, map_prod, Subalgebra.coe_mul]
    simp only [map_pow, g, aeval_X, weylMonom, wxProd, wyProd]
    congr 1
    · rw [← list_finRange_prod_eq]
      have hl : ∀ (l : List (Fin n)),
          (l.map (fun i => (⟨wx R i ^ p, wx_pow_p_mem_center R i⟩ : Subalgebra.center R (W R n)) ^ d (Sum.inl i))).prod.val =
            (l.map (fun i => wx R i ^ (p * d (Sum.inl i)))).prod := by
        intro l; induction l with
        | nil => simp
        | cons a l ih =>
          rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, List.map_cons, List.prod_cons]
          simp [pow_mul]
      exact hl (List.finRange n)
    · rw [← list_finRange_prod_eq]
      have hl : ∀ (l : List (Fin n)),
          (l.map (fun i => (⟨wy R i ^ p, wy_pow_p_mem_center R i⟩ : Subalgebra.center R (W R n)) ^ d (Sum.inr i))).prod.val =
            (l.map (fun i => wy R i ^ (p * d (Sum.inr i)))).prod := by
        intro l; induction l with
        | nil => simp
        | cons a l ih =>
          rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, List.map_cons, List.prod_cons]
          simp [pow_mul]
      exact hl (List.finRange n)
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    have hmr : monomial d r = r • monomial d (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmr, map_smul, map_smul, hmon, toMvPoly_weylMonom, map_smul, MvPolynomial.expand_monomial,
      smul_monomial]
  | add f g hf hg =>
    simp [hf, hg]

lemma centerEmb_injective (R : Type*) [CommRing R] (n p : ℕ) [CharP R p] (hp : 0 < p) :
    Function.Injective (centerEmb R n p) := by
  intro f g hfg
  have h1 := congrArg (toMvPoly R n) hfg
  rw [toMvPoly_centerEmb, toMvPoly_centerEmb] at h1
  ext d
  have hc := congrArg (fun q => q.coeff (p • d)) h1
  rw [MvPolynomial.coeff_expand_smul p hp.ne' f d, MvPolynomial.coeff_expand_smul p hp.ne' g d] at hc
  exact hc

/- Every nonzero finite-dimensional `W F n`-module over an algebraically closed field `F`
of prime characteristic `p` has dimension at least `p ^ n`. -/

lemma dim_ge_pow_of_module {F M : Type*} [Field F] [IsAlgClosed F] {n p : ℕ}
    [CharP F p] (hp : p.Prime)
    [AddCommGroup M] [Module F M] [FiniteDimensional F M] [Nontrivial M]
    (ρ : W F n →ₐ[F] Module.End F M) :
    p ^ n ≤ Module.finrank F M := by
  -- Step 1: Common nonzero eigenvector `v₀` for `ρ (wx F 0), ..., ρ (wx F (n-1))`
  have hex_eig : ∀ k ≤ n, ∃ (c : Fin n → F) (v₀ : M), v₀ ≠ 0 ∧
      ∀ i : Fin n, i.val < k → ρ (wx F i) v₀ = c i • v₀ := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨v₀, hv₀⟩ := exists_ne (0 : M)
      exact ⟨0, v₀, hv₀, fun i hi => by omega⟩
    | succ k ih =>
      intro hkn
      obtain ⟨c, v₀, hv₀, hc⟩ := ih (by omega)
      let E : Submodule F M := ⨅ (i : {i : Fin n // i.val < k}),
        LinearMap.ker (ρ (wx F i.1) - c i.1 • LinearMap.id)
      have hv₀E : v₀ ∈ E := by
        rw [Submodule.mem_iInf]
        rintro ⟨i, hi⟩
        simp [LinearMap.mem_ker, hc i hi]
      have : Nontrivial E := ⟨⟨⟨v₀, hv₀E⟩, 0, fun h => hv₀ (congrArg Subtype.val h)⟩⟩
      let fk : Fin n := ⟨k, hkn⟩
      have hinv : ∀ u ∈ E, ρ (wx F fk) u ∈ E := by
        intro u hu
        rw [Submodule.mem_iInf] at hu ⊢
        rintro ⟨i, hi⟩
        have hui := hu ⟨i, hi⟩
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_eq_zero] at hui ⊢
        have hcomm : ρ (wx F i) (ρ (wx F fk) u) = ρ (wx F fk) (ρ (wx F i) u) := by
          rw [← Module.End.mul_apply, ← map_mul]
          rw [show wx F i * wx F fk = wx F fk * wx F i from WeylAlgebra.of_inl_mul_comm F i fk]
          rw [map_mul, Module.End.mul_apply]
        rw [hcomm, hui, map_smul]
      let T : Module.End F E := LinearMap.restrict (ρ (wx F fk)) hinv
      obtain ⟨lamk, hlamk⟩ := Module.End.exists_eigenvalue T
      obtain ⟨⟨w, hwE⟩, hweq, hwne⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hlamk
      have hw0 : w ≠ 0 := fun h => hwne (Subtype.ext h)
      refine ⟨Function.update c fk lamk, w, hw0, fun i hi => ?_⟩
      by_cases hik : i.val < k
      · have hne : i ≠ fk := fun h => by subst h; dsimp only [fk] at hik; omega
        rw [Function.update_of_ne hne]
        have hwi := (Submodule.mem_iInf _).mp hwE ⟨i, hik⟩
        simpa [LinearMap.mem_ker, sub_eq_zero] using hwi
      · have heq : i = fk := Fin.ext (by dsimp only [fk]; omega)
        subst heq
        rw [Function.update_self]
        have hweq' : T ⟨w, hwE⟩ = lamk • ⟨w, hwE⟩ := Module.End.mem_eigenspace_iff.mp hweq
        exact congrArg Subtype.val hweq'
  obtain ⟨c, v₀, hv₀, hc⟩ := hex_eig n le_rfl
  have hc' : ∀ i : Fin n, ρ (wx F i) v₀ = c i • v₀ := fun i => hc i i.isLt
  -- Step 2: `T i := ρ (wx F i) - c i • id` satisfies `T i v₀ = 0` and lowers `wy i ^ k` by `k`!
  let T : Fin n → Module.End F M := fun i => ρ (wx F i) - c i • LinearMap.id
  have hT_v0 : ∀ i, T i v₀ = 0 := fun i => by simp [T, hc' i]
  have hT_comm : ∀ i j, T i * T j = T j * T i := by
    intro i j; refine LinearMap.ext fun u => ?_
    simp only [T, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul]
    have h1 : ρ (wx F i) (ρ (wx F j) u) = ρ (wx F j) (ρ (wx F i) u) := by
      rw [← Module.End.mul_apply, ← map_mul]
      rw [show wx F i * wx F j = wx F j * wx F i from WeylAlgebra.of_inl_mul_comm F i j]
      rw [map_mul, Module.End.mul_apply]
    rw [h1, smul_sub, smul_sub, smul_comm]; abel
  have hT_wyProd : ∀ (i : Fin n) (e : Fin n → ℕ),
      T i (ρ (wyProd F e) v₀) =
        ((e i : ℕ) : F) • ρ (wyProd F (Function.update e i (e i - 1))) v₀ := by
    intro i e
    have hrel : wx F i * wyProd F e =
        wyProd F e * wx F i + (e i : W F n) * wyProd F (Function.update e i (e i - 1)) := by
      have h := wyProd_mul_wx F i e
      rw [h]; abel
    simp only [T, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Module.End.mul_apply, ← map_mul, hrel, map_add, map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hc' i, map_smul,
      add_sub_cancel_left]
    have hnat : ρ ((e i : ℕ) : W F n) = ((e i : ℕ) : F) • (1 : Module.End F M) := by
      rw [← map_natCast (algebraMap F (W F n)), AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rw [hnat]; simp
  have hT_pow_wyProd : ∀ (i : Fin n) (k : ℕ) (e : Fin n → ℕ),
      (T i ^ k) (ρ (wyProd F e) v₀) =
        if k ≤ e i then
          ((Nat.descFactorial (e i) k : ℕ) : F) • ρ (wyProd F (Function.update e i (e i - k))) v₀
        else 0 := by
    intro i k
    induction k with
    | zero =>
      intro e
      simp only [pow_zero, Module.End.one_apply, Nat.zero_le, ↓reduceIte, Nat.descFactorial_zero,
        Nat.cast_one, one_smul, Nat.sub_zero]
      congr 3; funext j; by_cases h : j = i <;> simp [Function.update, h]
    | succ k ih =>
      intro e
      rw [pow_succ', Module.End.mul_apply, ih]
      split_ifs with hk hle
      · rw [map_smul, hT_wyProd, smul_smul, Function.update_self, Function.update_idem]
        have heq : (e i - k) - 1 = e i - (k + 1) := by omega
        rw [heq, Nat.descFactorial_succ]
        push_cast; rw [mul_comm]
      · rw [map_smul, hT_wyProd, Function.update_self]
        have h0 : e i - k = 0 := by omega
        rw [h0]; simp
      · exfalso; omega
      · simp
  have hT_list : ∀ (l : List (Fin n)), l.Nodup → ∀ (a e : Fin n → ℕ),
      ((l.map (fun i => T i ^ a i)).prod) (ρ (wyProd F e) v₀) =
        if ∀ i ∈ l, a i ≤ e i then
          ((l.map (fun i => Nat.descFactorial (e i) (a i))).prod : F) •
            ρ (wyProd F (fun i => if i ∈ l then e i - a i else e i)) v₀
        else 0 := by
    intro l
    induction l with
    | nil => intro _ a e; simp
    | cons j l ih =>
      intro hnd a e
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hnd.2]
      by_cases hl : ∀ i ∈ l, a i ≤ e i
      · rw [if_pos hl, map_smul, hT_pow_wyProd]
        have hje : (if j ∈ l then e j - a j else e j) = e j := if_neg hnd.1
        rw [hje]
        by_cases hj : a j ≤ e j
        · have hall : ∀ i ∈ j :: l, a i ≤ e i := by
            intro i hi; rcases List.mem_cons.mp hi with rfl | hil; exact hj; exact hl i hil
          rw [if_pos hj, if_pos hall, smul_smul, Nat.cast_mul, mul_comm]
          congr 4
          funext i
          by_cases hij : i = j
          · subst hij; simp [Function.update, hnd.1]
          · simp [Function.update, hij]
        · have hnot : ¬ ∀ i ∈ j :: l, a i ≤ e i := fun hall => hj (hall j (by simp))
          rw [if_neg hj, if_neg hnot, smul_zero]
      · have hnot : ¬ ∀ i ∈ j :: l, a i ≤ e i := fun hall => hl (fun i hi => hall i (by simp [hi]))
        rw [if_neg hl, if_neg hnot, map_zero]
  -- Step 3: Linear independence of `v β := ρ (wyProd F (fun i => (β i).val)) v₀`
  let v : (Fin n → Fin p) → M := fun β => ρ (wyProd F (fun i => (β i).val)) v₀
  have hlin : LinearIndependent F v := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    have hsupp : (Finset.univ.filter (fun β : Fin n → Fin p => g β ≠ 0)).Nonempty := by
      obtain ⟨β, hβ⟩ := hne
      exact ⟨β, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ⟩⟩
    obtain ⟨β₀, hβ₀_mem, hβ₀_max⟩ := Finset.exists_max_image _
      (fun β : Fin n → Fin p => ∑ i : Fin n, (β i).val) hsupp
    have hgβ₀ : g β₀ ≠ 0 := (Finset.mem_filter.mp hβ₀_mem).2
    let op : Module.End F M := ((List.finRange n).map (fun i => T i ^ (β₀ i).val)).prod
    have hop_zero : op (∑ β : Fin n → Fin p, g β • v β) = 0 := by rw [hg, map_zero]
    rw [map_sum] at hop_zero
    have hterm : ∀ β : Fin n → Fin p, β ≠ β₀ → op (g β • v β) = 0 := by
      intro β hne_β
      by_cases hgβ : g β = 0
      · simp [hgβ]
      · have hle_sum : ∑ i : Fin n, (β i).val ≤ ∑ i : Fin n, (β₀ i).val :=
          hβ₀_max β (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgβ⟩)
        have hnot_all : ¬ ∀ i ∈ List.finRange n, (β₀ i).val ≤ (β i).val := by
          intro hall
          have heq : β = β₀ := by
            funext i
            apply Fin.ext
            by_contra hne_i
            have hlt : (β₀ i).val < (β i).val := lt_of_le_of_ne (hall i (List.mem_finRange i)) (Ne.symm hne_i)
            have hlt_sum : ∑ j : Fin n, (β₀ j).val < ∑ j : Fin n, (β j).val :=
              Finset.sum_lt_sum (fun j _ => hall j (List.mem_finRange j)) ⟨i, Finset.mem_univ i, hlt⟩
            omega
          exact hne_β heq
        rw [map_smul, hT_list (List.finRange n) (List.nodup_finRange n), if_neg hnot_all, smul_zero]
    rw [Finset.sum_eq_single β₀ (fun β _ hne => hterm β hne) (by simp)] at hop_zero
    rw [map_smul, hT_list (List.finRange n) (List.nodup_finRange n),
      if_pos (fun i _ => le_rfl), smul_smul] at hop_zero
    have hwy0 : wyProd F (fun i => if i ∈ List.finRange n then (β₀ i).val - (β₀ i).val else (β₀ i).val) = 1 := by
      simp [wyProd]
    rw [hwy0, map_one, Module.End.one_apply] at hop_zero
    have hfact_ne : (((List.finRange n).map (fun i => Nat.descFactorial (β₀ i).val (β₀ i).val)).prod : F) ≠ 0 := by
      have hndvd : ¬ p ∣ ((List.finRange n).map (fun i => Nat.descFactorial (β₀ i).val (β₀ i).val)).prod := by
        intro hdvd
        clear hop_zero hterm hβ₀_max hβ₀_mem hsupp hne hg hgβ₀
        have : ∀ l : List (Fin n), p ∣ (l.map (fun i => (β₀ i).val.descFactorial (β₀ i).val)).prod → False := by
          intro l; induction l with
          | nil => intro h; simp at h; exact hp.ne_one h
          | cons j l' ih =>
            simp only [List.map_cons, List.prod_cons]
            intro h
            rcases hp.dvd_mul.mp h with h1 | h2
            · rw [Nat.descFactorial_self] at h1
              exact absurd (hp.dvd_factorial.mp h1) (not_le_of_gt (β₀ j).isLt)
            · exact ih h2
        exact this (List.finRange n) hdvd
      intro h0
      exact hndvd ((CharP.cast_eq_zero_iff F p _).mp h0)
    have hcoeff_ne : g β₀ * (((List.finRange n).map (fun i => Nat.descFactorial (β₀ i).val (β₀ i).val)).prod : F) ≠ 0 :=
      mul_ne_zero hgβ₀ hfact_ne
    exact hv₀ ((smul_eq_zero.mp hop_zero).resolve_left hcoeff_ne)
  have hcard : Fintype.card (Fin n → Fin p) ≤ Module.finrank F M := hlin.fintype_card_le_finrank
  simpa [Fintype.card_fun, Fintype.card_fin] using hcard

/-- Schur's lemma for `p^n`-dimensional `W F n`-modules over an algebraically closed field `F`. -/
lemma central_acts_as_scalar {F M : Type*} [Field F] [IsAlgClosed F] {n p : ℕ}
    [CharP F p] (hp : p.Prime)
    [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (hdim : Module.finrank F M = p ^ n)
    (ρ : W F n →ₐ[F] Module.End F M)
    (z : Module.End F M) (hz : ∀ a : W F n, z * ρ a = ρ a * z) :
    ∃ c : F, z = c • 1 := by
  have : Nontrivial M := by
    rw [← Module.finrank_pos_iff (R := F)]
    rw [hdim]; exact pow_pos hp.pos n
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue z
  let K : Submodule F M := LinearMap.ker (z - c • LinearMap.id)
  have hK_nt : Nontrivial K := by
    obtain ⟨v, hv, hv0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
    have hv' : z v = c • v := Module.End.mem_eigenspace_iff.mp hv
    exact ⟨⟨⟨v, by simp [K, LinearMap.mem_ker, hv']⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hK_inv : ∀ a : W F n, ∀ u ∈ K, ρ a u ∈ K := by
    intro a u hu
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hu ⊢
    have := congrArg (fun f : Module.End F M => f u) (hz a)
    simp only [Module.End.mul_apply] at this
    rw [this, hu, map_smul]
  let ρK : W F n →ₐ[F] Module.End F K :=
    { toFun := fun a => LinearMap.restrict (ρ a) (hK_inv a)
      map_one' := by ext ⟨u, hu⟩; simp
      map_mul' := fun a b => by ext ⟨u, hu⟩; simp
      map_zero' := by ext ⟨u, hu⟩; simp
      map_add' := fun a b => by ext ⟨u, hu⟩; simp
      commutes' := fun r => by ext ⟨u, hu⟩; simp }
  have hge : p ^ n ≤ Module.finrank F K := dim_ge_pow_of_module hp ρK
  have htop : K = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le K) (hdim ▸ hge))
  refine ⟨c, LinearMap.ext fun u => ?_⟩
  have hu : u ∈ K := htop.symm ▸ Submodule.mem_top
  simpa [K, LinearMap.mem_ker, sub_eq_zero] using hu

/- Module 3b: Explicit `p^n`-dimensional irreducible representations `rep α β` in char `p`. -/

abbrev Idx (n p : ℕ) := Fin n → Fin p
abbrev RepSpace (F : Type*) (n p : ℕ) := Idx n p → F

noncomputable def repD (F : Type*) [Field F] (n p : ℕ) (i : Fin n) :
    Module.End F (RepSpace F n p) where
  toFun f γ :=
    if h : (γ i).val + 1 < p then
      (((γ i).val + 1 : ℕ) : F) * f (Function.update γ i ⟨(γ i).val + 1, h⟩)
    else 0
  map_add' f g := by
    funext γ; simp only [Pi.add_apply]; split_ifs <;> simp [mul_add]
  map_smul' r f := by
    funext γ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

noncomputable def repX {F : Type*} [Field F] {n p : ℕ} (α : Fin n → F) (i : Fin n) :
    Module.End F (RepSpace F n p) :=
  α i • 1 + repD F n p i

noncomputable def repY {F : Type*} [Field F] {n p : ℕ} (β : Fin n → F) (hp : p.Prime) (i : Fin n) :
    Module.End F (RepSpace F n p) where
  toFun f γ :=
    if h : (γ i).val = 0 then
      β i * f (Function.update γ i ⟨p - 1, Nat.sub_lt hp.pos zero_lt_one⟩)
    else
      f (Function.update γ i ⟨(γ i).val - 1, by omega⟩)
  map_add' f g := by
    funext γ; simp only [Pi.add_apply]; split_ifs <;> simp [mul_add]
  map_smul' r f := by
    funext γ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma repD_comm {F : Type*} [Field F] {n p : ℕ} (i j : Fin n) :
    repD F n p i * repD F n p j = repD F n p j * repD F n p i := by
  by_cases hij : i = j
  · subst hij; rfl
  · refine LinearMap.ext fun f => funext fun γ => ?_
    simp only [Module.End.mul_apply, repD, LinearMap.coe_mk, AddHom.coe_mk,
      Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    split_ifs with h1 h2 h3
    · rw [Function.update_comm hij]; ring
    · simp
    · simp
    · simp

lemma repX_comm {F : Type*} [Field F] {n p : ℕ} (α : Fin n → F) (i j : Fin n) :
    repX (p := p) α i * repX (p := p) α j = repX (p := p) α j * repX (p := p) α i := by
  simp only [repX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_add, smul_smul, repD_comm i j, mul_comm (α i) (α j)]
  abel

lemma repY_comm {F : Type*} [Field F] {n p : ℕ} (β : Fin n → F) (hp : p.Prime) (i j : Fin n) :
    repY β hp i * repY β hp j = repY β hp j * repY β hp i := by
  by_cases hij : i = j
  · subst hij; rfl
  · refine LinearMap.ext fun f => funext fun γ => ?_
    simp only [Module.End.mul_apply, repY, LinearMap.coe_mk, AddHom.coe_mk,
      Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    split_ifs <;> (rw [Function.update_comm hij]; try ring)

lemma repX_repY_comm_ne {F : Type*} [Field F] {n p : ℕ} (α β : Fin n → F) (hp : p.Prime)
    {i j : Fin n} (hij : i ≠ j) :
    repX (p := p) α i * repY β hp j = repY β hp j * repX (p := p) α i := by
  have hD : repD F n p i * repY β hp j = repY β hp j * repD F n p i := by
    refine LinearMap.ext fun f => funext fun γ => ?_
    simp only [Module.End.mul_apply, repD, repY, LinearMap.coe_mk, AddHom.coe_mk,
      Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    split_ifs <;> try rw [Function.update_comm hij]
    all_goals ring
  simp only [repX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hD]

lemma repX_repY_self {F : Type*} [Field F] {n p : ℕ} [CharP F p] (α β : Fin n → F)
    (hp : p.Prime) (i : Fin n) :
    repX (p := p) α i * repY β hp i = repY β hp i * repX (p := p) α i + 1 := by
  have hD : repD F n p i * repY β hp i = repY β hp i * repD F n p i + 1 := by
    refine LinearMap.ext fun f => funext fun γ => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, Pi.add_apply, Module.End.one_apply,
      repD, repY, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h0 : (γ i).val = 0
    · have h1 : (γ i).val + 1 < p := by have := hp.two_le; omega
      have hne0 : (⟨(γ i).val + 1, h1⟩ : Fin p).val ≠ 0 := by simp
      have hnot : ¬ (⟨p - 1, Nat.sub_lt hp.pos zero_lt_one⟩ : Fin p).val + 1 < p := by
        dsimp only; omega
      rw [dif_pos h1, dif_pos h0]
      simp only [Function.update_self, dif_neg hne0, dif_neg hnot, mul_zero, zero_add]
      have hupd : Function.update (Function.update γ i ⟨(γ i).val + 1, h1⟩) i ⟨(γ i).val + 1 - 1, by omega⟩ = γ := by
        funext j; by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; apply Fin.ext; simp
        · simp [Function.update_of_ne hj]
      rw [hupd, h0]; simp
    · by_cases htop : (γ i).val + 1 < p
      · have hne0 : (⟨(γ i).val + 1, htop⟩ : Fin p).val ≠ 0 := by simp
        have hlt' : (⟨(γ i).val - 1, by omega⟩ : Fin p).val + 1 < p := by dsimp only; omega
        rw [dif_pos htop, dif_neg h0]
        simp only [Function.update_self, dif_neg hne0, dif_pos hlt']
        have hupd1 : Function.update (Function.update γ i ⟨(γ i).val + 1, htop⟩) i ⟨(γ i).val + 1 - 1, by omega⟩ = γ := by
          funext j; by_cases hj : j = i
          · subst hj; simp only [Function.update_self]; apply Fin.ext; simp
          · simp [Function.update_of_ne hj]
        have hupd2 : Function.update (Function.update γ i ⟨(γ i).val - 1, by omega⟩) i ⟨(γ i).val - 1 + 1, hlt'⟩ = γ := by
          funext j; by_cases hj : j = i
          · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
          · simp [Function.update_of_ne hj]
        rw [hupd1, hupd2]
        have hsub : ((γ i).val - 1 + 1 : ℕ) = (γ i).val := by omega
        rw [hsub]; push_cast; ring
      · have hval : (γ i).val = p - 1 := by have := (γ i).isLt; omega
        have hlt' : (⟨(γ i).val - 1, by omega⟩ : Fin p).val + 1 < p := by dsimp only; omega
        rw [dif_neg htop, dif_neg h0]
        simp only [Function.update_self, dif_pos hlt']
        have hupd2 : Function.update (Function.update γ i ⟨(γ i).val - 1, by omega⟩) i ⟨(γ i).val - 1 + 1, hlt'⟩ = γ := by
          funext j; by_cases hj : j = i
          · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
          · simp [Function.update_of_ne hj]
        rw [hupd2]
        have hsub : ((γ i).val - 1 + 1 : ℕ) = p - 1 := by omega
        rw [hsub]
        have hp0 : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
        have hp1 : (((p - 1 : ℕ) : F)) + 1 = 0 := by
          rw [← Nat.cast_one (R := F), ← Nat.cast_add, Nat.sub_add_cancel hp.pos, hp0]
        linear_combination -f γ * hp1
  simp only [repX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hD]
  abel

/-- Explicit `p^n`-dimensional representation of `W F n` in characteristic `p`. -/
noncomputable def rep {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) : W F n →ₐ[F] Module.End F (RepSpace F n p) :=
  weylLift
    (fun v => match v with
      | Sum.inl i => repX (p := p) α i
      | Sum.inr i => repY β hp i)
    (repX_comm α)
    (repY_comm β hp)
    (fun _ _ h => repX_repY_comm_ne α β hp h)
    (repX_repY_self α β hp)

lemma repD_pow {F : Type*} [Field F] {n p : ℕ} (i : Fin n) (k : ℕ) (f : RepSpace F n p)
    (γ : Idx n p) :
    ((repD F n p i ^ k) f) γ =
      if h : (γ i).val + k < p then
        ((Nat.descFactorial ((γ i).val + k) k : ℕ) : F) *
          f (Function.update γ i ⟨(γ i).val + k, h⟩)
      else 0 := by
  induction k generalizing γ with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.add_zero, Fin.is_lt, ↓reduceDIte,
      Nat.descFactorial_zero, Nat.cast_one, one_mul, Fin.eta, Function.update_eq_self]
  | succ k ih =>
    have hstep : ∀ g γ', (repD F n p i) g γ' =
        if h : (γ' i).val + 1 < p then
          (((γ' i).val + 1 : ℕ) : F) * g (Function.update γ' i ⟨(γ' i).val + 1, h⟩)
        else 0 := fun _ _ => rfl
    rw [pow_succ', Module.End.mul_apply, hstep]
    by_cases h1 : (γ i).val + 1 < p
    · rw [dif_pos h1, ih]
      simp only [Function.update_self]
      by_cases h2 : (γ i).val + (k + 1) < p
      · have h2' : (γ i).val + 1 + k < p := by omega
        rw [dif_pos h2', dif_pos h2, Function.update_idem]
        have harg : (⟨(γ i).val + 1 + k, h2'⟩ : Fin p) = ⟨(γ i).val + (k + 1), h2⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [harg, ← mul_assoc]
        congr 1
        have hdf : ((γ i).val + 1) * Nat.descFactorial ((γ i).val + 1 + k) k =
            Nat.descFactorial ((γ i).val + (k + 1)) (k + 1) := by
          have heq : (γ i).val + (k + 1) = (γ i).val + 1 + k := by omega
          rw [heq, Nat.descFactorial_succ]
          have hsub : (γ i).val + 1 + k - k = (γ i).val + 1 := by omega
          rw [hsub, mul_comm]
        rw [← Nat.cast_mul, hdf]
      · have h2' : ¬ (γ i).val + 1 + k < p := by omega
        rw [dif_neg h2', dif_neg h2, mul_zero]
    · have h2 : ¬ (γ i).val + (k + 1) < p := by omega
      rw [dif_neg h1, dif_neg h2]

lemma repD_pow_p {F : Type*} [Field F] {n p : ℕ} (i : Fin n) :
    repD F n p i ^ p = 0 := by
  refine LinearMap.ext fun f => funext fun γ => ?_
  rw [repD_pow]
  have hnot : ¬ (γ i).val + p < p := by omega
  rw [dif_neg hnot]; rfl

lemma rep_wx_pow_p {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) (i : Fin n) :
    rep hp α β (wx F i ^ p) = (α i ^ p) • 1 := by
  have hrep : rep hp α β (wx F i) = repX (p := p) α i := by simp [rep, wx]
  rw [map_pow, hrep, repX]
  have hcomm : Commute (α i • (1 : Module.End F (RepSpace F n p))) (repD F n p i) := by
    simp [Commute, SemiconjBy]
  have hp0 : (p : Module.End F (RepSpace F n p)) = 0 := by
    rw [← map_natCast (algebraMap F (Module.End F (RepSpace F n p))), CharP.cast_eq_zero, map_zero]
  rw [hcomm.add_pow_prime_eq hp, smul_pow, one_pow, repD_pow_p, hp0]
  simp

lemma repY_pow_val {F : Type*} [Field F] {n p : ℕ} (β : Fin n → F) (hp : p.Prime)
    (i : Fin n) (k : ℕ) (hk : k ≤ p) (f : RepSpace F n p) (γ : Idx n p) :
    ((repY β hp i ^ k) f) γ =
      if h : k ≤ (γ i).val then
        f (Function.update γ i ⟨(γ i).val - k, by omega⟩)
      else
        β i * f (Function.update γ i ⟨(γ i).val + p - k, by have := (γ i).isLt; omega⟩) := by
  induction k generalizing γ with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.zero_le, ↓reduceDIte, Nat.sub_zero, Fin.eta,
      Function.update_eq_self]
  | succ k ih =>
    have hstep : ∀ g γ', (repY β hp i) g γ' =
        if h : (γ' i).val = 0 then
          β i * g (Function.update γ' i ⟨p - 1, Nat.sub_lt hp.pos zero_lt_one⟩)
        else
          g (Function.update γ' i ⟨(γ' i).val - 1, by omega⟩) := fun _ _ => rfl
    rw [pow_succ', Module.End.mul_apply, hstep]
    by_cases h0 : (γ i).val = 0
    · rw [dif_pos h0, ih (by omega)]
      simp only [Function.update_self]
      have hle : k ≤ p - 1 := by omega
      have hnot : ¬ k + 1 ≤ (γ i).val := by omega
      rw [dif_pos hle, dif_neg hnot, Function.update_idem]
      congr 2; funext j; by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
      · simp [Function.update_of_ne hj]
    · rw [dif_neg h0, ih (by omega)]
      simp only [Function.update_self]
      by_cases hle : k + 1 ≤ (γ i).val
      · have hle' : k ≤ (γ i).val - 1 := by omega
        rw [dif_pos hle', dif_pos hle, Function.update_idem]
        congr 1; funext j; by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
        · simp [Function.update_of_ne hj]
      · have hle' : ¬ k ≤ (γ i).val - 1 := by omega
        rw [dif_neg hle', dif_neg hle, Function.update_idem]
        congr 2; funext j; by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
        · simp [Function.update_of_ne hj]

lemma rep_wy_pow_p {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) (i : Fin n) :
    rep hp α β (wy F i ^ p) = (β i) • 1 := by
  have hrep : rep hp α β (wy F i) = repY β hp i := by simp [rep, wy]
  rw [map_pow, hrep]
  refine LinearMap.ext fun f => funext fun γ => ?_
  change ((repY β hp i ^ p) f) γ = β i * f γ
  rw [repY_pow_val β hp i p le_rfl]
  have hnot : ¬ p ≤ (γ i).val := not_le_of_gt (γ i).isLt
  rw [dif_neg hnot]
  congr 2; funext j; by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; apply Fin.ext; dsimp only; omega
  · simp [Function.update_of_ne hj]

lemma rep_centerEmb {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) (f : P F n) :
    rep hp α β (centerEmb F n p f) = MvPolynomial.eval (Sum.elim (fun i => α i ^ p) β) f • 1 := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [centerEmb, AlgHom.comp_apply, aeval_C, Subalgebra.val_apply, Subalgebra.coe_algebraMap,
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, eval_C]
  | add q₁ q₂ h1 h2 =>
    rw [map_add, map_add, h1, h2, map_add, add_smul]
  | mul_X q v hq =>
    rw [map_mul, map_mul, hq, centerEmb_X, eval_mul, eval_X, mul_smul]
    rcases v with i | i
    · rw [show WeylAlgebra.of F (Sum.inl i) ^ p = wx F i ^ p from rfl, rep_wx_pow_p hp α β i]
      simp [mul_comm, smul_smul]
    · rw [show WeylAlgebra.of F (Sum.inr i) ^ p = wy F i ^ p from rfl, rep_wy_pow_p hp α β i]
      simp [mul_comm, smul_smul]

/- Module 3c: Surjectivity of `rep`, `p`-adic PBW decomposition, `exists_centerMap`,
   and `bijective_of_centerMap_bijective`. -/

lemma rep_surjective {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) : Function.Surjective (rep hp α β) := by
  let topIdx : Idx n p := fun _ => ⟨p - 1, Nat.sub_lt hp.pos zero_lt_one⟩
  let zeroIdx : Idx n p := fun _ => ⟨0, hp.pos⟩
  have hfact_ne : (((p - 1).factorial : ℕ) : F) ≠ 0 := by
    intro h0
    have hdvd : p ∣ (p - 1).factorial := (CharP.cast_eq_zero_iff F p _).mp h0
    have hle : p ≤ p - 1 := hp.dvd_factorial.mp hdvd
    have := hp.pos; omega
  let cInv : F := (((p - 1).factorial : ℕ) : F)⁻¹
  -- `E0` maps `f` to `fun γ => if γ = zeroIdx then f topIdx else 0`
  let E0_list : List (Fin n) → Module.End F (RepSpace F n p) := fun l =>
    (l.map (fun i => cInv • (repD F n p i ^ (p - 1)))).prod
  have hE0_mem : ∀ l : List (Fin n), E0_list l ∈ Set.range (rep hp α β) := by
    intro l; induction l with
    | nil => exact ⟨1, map_one _⟩
    | cons i l ih =>
      obtain ⟨b, hb⟩ := ih
      have hD_mem : repD F n p i ∈ Set.range (rep hp α β) :=
        ⟨wx F i - algebraMap F (W F n) (α i), by
          simp [rep, wx, repX, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]⟩
      obtain ⟨d, hd⟩ := hD_mem
      refine ⟨cInv • d ^ (p - 1) * b, ?_⟩
      simp only [E0_list, List.map_cons, List.prod_cons, map_mul, map_smul, map_pow, hd, hb]
  have hE0_apply : ∀ (l : List (Fin n)), l.Nodup → ∀ (f : RepSpace F n p) (γ : Idx n p),
      (E0_list l f) γ =
        if ∀ i ∈ l, (γ i).val = 0 then
          f (fun i => if i ∈ l then ⟨p - 1, Nat.sub_lt hp.pos zero_lt_one⟩ else γ i)
        else 0 := by
    intro l; induction l with
    | nil => intro _ f γ; simp [E0_list]
    | cons j l ih =>
      intro hnd f γ
      rw [List.nodup_cons] at hnd
      simp only [E0_list, List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [repD_pow]
      by_cases hj : (γ j).val = 0
      · have hlt : (γ j).val + (p - 1) < p := by have := hp.pos; omega
        rw [dif_pos hlt, ih hnd.2]
        have hfact_eq : Nat.descFactorial ((γ j).val + (p - 1)) (p - 1) = (p - 1).factorial := by
          rw [hj, zero_add, Nat.descFactorial_self]
        rw [hfact_eq, ← mul_assoc, inv_mul_cancel₀ hfact_ne, one_mul]
        have hcond : (∀ i ∈ l, (Function.update γ j ⟨(γ j).val + (p - 1), hlt⟩ i).val = 0) ↔
            (∀ i ∈ j :: l, (γ i).val = 0) := by
          constructor
          · intro hl i hi
            rcases List.mem_cons.mp hi with rfl | hil
            · exact hj
            · have hne : i ≠ j := fun h => hnd.1 (h ▸ hil)
              simpa [Function.update_of_ne hne] using hl i hil
          · intro hall i hil
            have hne : i ≠ j := fun h => hnd.1 (h ▸ hil)
            simpa [Function.update_of_ne hne] using hall i (by simp [hil])
        by_cases hl : ∀ i ∈ j :: l, (γ i).val = 0
        · rw [if_pos (hcond.mpr hl), if_pos hl]
          congr 1; funext i
          by_cases hij : i = j
          · subst hij; simp only [List.mem_cons, true_or, ↓reduceIte, hnd.1, Function.update_self]
            apply Fin.ext; dsimp only; omega
          · by_cases hil : i ∈ l <;> simp [hij, hil, Function.update_of_ne hij]
        · rw [if_neg (mt hcond.mp hl), if_neg hl]
      · have hnot : ¬ (γ j).val + (p - 1) < p := by have := (γ j).isLt; omega
        have hnot_all : ¬ ∀ i ∈ j :: l, (γ i).val = 0 := fun h => hj (h j (by simp))
        rw [dif_neg hnot, mul_zero, if_neg hnot_all]
  let E0 := E0_list (List.finRange n)
  have hE0_val : ∀ (f : RepSpace F n p) (γ : Idx n p),
      (E0 f) γ = if γ = zeroIdx then f topIdx else 0 := by
    intro f γ
    rw [hE0_apply (List.finRange n) (List.nodup_finRange n)]
    have hiff : (∀ i ∈ List.finRange n, (γ i).val = 0) ↔ γ = zeroIdx := by
      constructor
      · intro h; funext i; exact Fin.ext (h i (List.mem_finRange i))
      · intro h i _; rw [h]
    by_cases hγ : γ = zeroIdx
    · rw [if_pos (hiff.mpr hγ), if_pos hγ]
      congr 1; funext i; simp [topIdx]
    · rw [if_neg (mt hiff.mp hγ), if_neg hγ]
  -- Left and right shift operators via `repY`
  let shiftY : List (Fin n) → (Fin n → ℕ) → Module.End F (RepSpace F n p) := fun l a =>
    (l.map (fun i => repY β hp i ^ a i)).prod
  have hshiftY_mem : ∀ l a, shiftY l a ∈ Set.range (rep hp α β) := by
    intro l a; induction l with
    | nil => exact ⟨1, map_one _⟩
    | cons i l ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨wy F i ^ a i * b, ?_⟩
      rw [map_mul, map_pow, hb]
      simp [shiftY, rep, wy]
  have hshiftY_top : ∀ (l : List (Fin n)), l.Nodup → ∀ (a : Fin n → ℕ), (∀ i ∈ l, a i < p) →
      ∀ (f : RepSpace F n p) (γ : Idx n p), (∀ i ∈ l, (γ i).val = p - 1) →
      (shiftY l a f) γ = f (fun i => if h : i ∈ l then ⟨p - 1 - a i, by have := hp.pos; omega⟩ else γ i) := by
    intro l; induction l with
    | nil => intro _ a _ f γ _; simp [shiftY]
    | cons j l ih =>
      intro hnd a ha f γ hγ
      rw [List.nodup_cons] at hnd
      simp only [shiftY, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [repY_pow_val β hp j (a j) (le_of_lt (ha j (by simp)))]
      have hj : (γ j).val = p - 1 := hγ j (by simp)
      have hle : a j ≤ (γ j).val := by have := ha j (by simp); omega
      rw [dif_pos hle, ih hnd.2 a (fun i hi => ha i (by simp [hi]))]
      · congr 1; funext i
        by_cases hij : i = j
        · subst hij; simp only [List.mem_cons, true_or, ↓reduceDIte, hnd.1, Function.update_self]
          apply Fin.ext; dsimp only; omega
        · by_cases hil : i ∈ l <;> simp [hij, hil, Function.update_of_ne hij]
      · intro i hil
        have hne : i ≠ j := fun h => hnd.1 (h ▸ hil)
        rw [Function.update_of_ne hne]; exact hγ i (by simp [hil])
  have hshiftY_zero : ∀ (l : List (Fin n)), l.Nodup → ∀ (a : Fin n → ℕ), (∀ i ∈ l, a i < p) →
      ∀ (g : RepSpace F n p) (γ : Idx n p),
      (∀ δ, (∃ i ∈ l, (δ i).val ≠ 0) → g δ = 0) →
      (shiftY l a g) γ = if ∀ i ∈ l, (γ i).val = a i then
        g (fun i => if i ∈ l then ⟨0, hp.pos⟩ else γ i) else 0 := by
    intro l; induction l with
    | nil => intro _ a _ g γ _; simp [shiftY]
    | cons j l ih =>
      intro hnd a ha g γ hg
      rw [List.nodup_cons] at hnd
      simp only [shiftY, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [repY_pow_val β hp j (a j) (le_of_lt (ha j (by simp)))]
      have hgl : ∀ δ, (∃ i ∈ l, (δ i).val ≠ 0) → g δ = 0 :=
        fun δ ⟨i, hil, hi⟩ => hg δ ⟨i, by simp [hil], hi⟩
      by_cases hj : (γ j).val = a j
      · have hle : a j ≤ (γ j).val := le_of_eq hj.symm
        rw [dif_pos hle, ih hnd.2 a (fun i hi => ha i (by simp [hi])) g _ hgl]
        have hcond : (∀ i ∈ l, (Function.update γ j ⟨(γ j).val - a j, by omega⟩ i).val = a i) ↔
            (∀ i ∈ j :: l, (γ i).val = a i) := by
          constructor
          · intro hl i hi; rcases List.mem_cons.mp hi with rfl | hil
            · exact hj
            · have hne : i ≠ j := fun h => hnd.1 (h ▸ hil)
              simpa [Function.update_of_ne hne] using hl i hil
          · intro hall i hil
            have hne : i ≠ j := fun h => hnd.1 (h ▸ hil)
            simpa [Function.update_of_ne hne] using hall i (by simp [hil])
        by_cases hall : ∀ i ∈ j :: l, (γ i).val = a i
        · rw [if_pos (hcond.mpr hall), if_pos hall]
          congr 1; funext i
          by_cases hij : i = j
          · subst hij; simp only [List.mem_cons, true_or, ↓reduceIte, hnd.1, Function.update_self]
            apply Fin.ext; dsimp only; omega
          · by_cases hil : i ∈ l <;> simp [hij, hil, Function.update_of_ne hij]
        · rw [if_neg (mt hcond.mp hall), if_neg hall]
      · have hnot : ¬ ∀ i ∈ j :: l, (γ i).val = a i := fun h => hj (h j (by simp))
        rw [if_neg hnot]
        split_ifs with hle
        · rw [ih hnd.2 a (fun i hi => ha i (by simp [hi])) g _ hgl]
          split_ifs with hl
          · apply hg; refine ⟨j, by simp, ?_⟩
            simp only [hnd.1, ↓reduceIte, Function.update_self]; omega
          · rfl
        · rw [ih hnd.2 a (fun i hi => ha i (by simp [hi])) g _ hgl]
          split_ifs with hl
          · have : g (fun i => if i ∈ l then ⟨0, hp.pos⟩ else
                Function.update γ j ⟨(γ j).val + p - a j, by have := (γ j).isLt; omega⟩ i) = 0 := by
              apply hg; refine ⟨j, by simp, ?_⟩
              simp only [hnd.1, ↓reduceIte, Function.update_self]
              have := ha j (by simp); omega
            rw [this, mul_zero]
          · rw [mul_zero]
  -- Every matrix unit `E_{γ₀, δ₀}` is in `range (rep hp α β)`
  have hunit : ∀ γ₀ δ₀ : Idx n p,
      ∃ e : W F n, ∀ (f : RepSpace F n p) (γ : Idx n p),
        rep hp α β e f γ = if γ = γ₀ then f δ₀ else 0 := by
    intro γ₀ δ₀
    obtain ⟨u₁, hu₁⟩ := hshiftY_mem (List.finRange n) (fun i => (γ₀ i).val)
    obtain ⟨u₀, hu₀⟩ := hE0_mem (List.finRange n)
    obtain ⟨u₂, hu₂⟩ := hshiftY_mem (List.finRange n) (fun i => p - 1 - (δ₀ i).val)
    refine ⟨u₁ * u₀ * u₂, fun f γ => ?_⟩
    rw [map_mul, map_mul, hu₁, hu₀, hu₂, Module.End.mul_apply, Module.End.mul_apply]
    have hg0 : ∀ δ, (∃ i ∈ List.finRange n, (δ i).val ≠ 0) → (E0 (shiftY (List.finRange n) (fun i => p - 1 - (δ₀ i).val) f)) δ = 0 := by
      intro δ ⟨i, _, hi⟩
      rw [hE0_val, if_neg]
      intro h; rw [h] at hi; exact hi rfl
    rw [hshiftY_zero (List.finRange n) (List.nodup_finRange n) (fun i => (γ₀ i).val)
      (fun i _ => (γ₀ i).isLt) _ γ hg0]
    have hiff : (∀ i ∈ List.finRange n, (γ i).val = (γ₀ i).val) ↔ γ = γ₀ := by
      constructor
      · intro h; funext i; exact Fin.ext (h i (List.mem_finRange i))
      · intro h i _; rw [h]
    by_cases hγ : γ = γ₀
    · rw [if_pos (hiff.mpr hγ), if_pos hγ]
      have harg : (fun i => if i ∈ List.finRange n then (⟨0, hp.pos⟩ : Fin p) else γ i) = zeroIdx := by
        funext i; simp [zeroIdx]
      rw [harg, hE0_val, if_pos rfl]
      rw [hshiftY_top (List.finRange n) (List.nodup_finRange n) (fun i => p - 1 - (δ₀ i).val)
        (fun i _ => by have := hp.pos; omega) f topIdx (fun i _ => rfl)]
      congr 1; funext i
      simp only [List.mem_finRange, ↓reduceDIte]
      apply Fin.ext; dsimp only; have := (δ₀ i).isLt; omega
    · rw [if_neg (mt hiff.mp hγ), if_neg hγ]
  -- Now express any `T : Module.End F (RepSpace F n p)` as a linear combination of matrix units
  intro T
  choose e he using hunit
  refine ⟨∑ γ₀ : Idx n p, ∑ δ₀ : Idx n p, T (Pi.single δ₀ 1) γ₀ • e γ₀ δ₀, ?_⟩
  refine LinearMap.ext fun f => funext fun γ => ?_
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, he]
  rw [Finset.sum_eq_single γ (fun γ₀ _ hne => Finset.sum_eq_zero fun δ₀ _ => by simp [Ne.symm hne]) (by simp)]
  simp only [↓reduceIte]
  have hf_eq : f = ∑ δ₀ : Idx n p, f δ₀ • Pi.single δ₀ (1 : F) := by
    funext δ; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hf_eq]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun δ₀ _ => mul_comm _ _

/- `p`-adic PBW decomposition over the center `P R n`, `exists_centerMap`, and surjectivity criterion. -/

abbrev Rem (n p : ℕ) := (Fin n ⊕ Fin n) → Fin p

noncomputable def remToFinsupp {n p : ℕ} (r : Rem n p) : (Fin n ⊕ Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => (r v).val)

noncomputable def weylRem (R : Type*) [CommRing R] {n p : ℕ} (r : Rem n p) : W R n :=
  weylMonom R (remToFinsupp r)

lemma weylMonom_center_mul (R : Type*) [CommRing R] {n p : ℕ} [CharP R p]
    (q r : (Fin n ⊕ Fin n) →₀ ℕ) :
    centerEmb R n p (monomial q 1) * weylMonom R r = weylMonom R (p • q + r) := by
  have h1 : toMvPoly R n (centerEmb R n p (monomial q 1) * weylMonom R r) =
      monomial (p • q + r) (1 : R) := by
    have hce : centerEmb R n p (monomial q 1) = weylMonom R (p • q) := by
      apply toMvPoly_injective R n
      rw [toMvPoly_centerEmb, MvPolynomial.expand_monomial, toMvPoly_weylMonom]
    rw [hce, weylMonom, weylMonom, mul_assoc]
    -- `wyProd (p • q)` is central, so it commutes past `wxProd r`!
    have hwy_cent : wyProd R (fun i => (p • q) (Sum.inr i)) ∈ Subalgebra.center R (W R n) := by
      have hl : ∀ (l : List (Fin n)),
          (l.map (fun i => wy R i ^ (p * q (Sum.inr i)))).prod ∈ Subalgebra.center R (W R n) := by
        intro l; induction l with
        | nil => exact Subalgebra.one_mem _
        | cons i l ih =>
          rw [List.map_cons, List.prod_cons, pow_mul]
          exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (wy_pow_p_mem_center R i) _) ih
      exact hl (List.finRange n)
    have hcomm : wyProd R (fun i => (p • q) (Sum.inr i)) * wxProd R (fun i => r (Sum.inl i)) =
        wxProd R (fun i => r (Sum.inl i)) * wyProd R (fun i => (p • q) (Sum.inr i)) :=
      ((Subalgebra.mem_center_iff.mp hwy_cent) _).symm
    rw [← mul_assoc (wyProd R _), hcomm, mul_assoc, ← mul_assoc (wxProd R _)]
    have hwx_mul : ∀ (e₁ e₂ : Fin n → ℕ), wxProd R e₁ * wxProd R e₂ = wxProd R (fun i => e₁ i + e₂ i) := by
      intro e₁ e₂
      have haux : ∀ (l : List (Fin n)), l.Nodup →
          (l.map (fun i => wx R i ^ e₁ i)).prod * (l.map (fun i => wx R i ^ e₂ i)).prod =
            (l.map (fun i => wx R i ^ (e₁ i + e₂ i))).prod := by
        intro l; induction l with
        | nil => simp
        | cons i l ih =>
          intro hnd; rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.prod_cons]
          have hc : (l.map (fun j => wx R j ^ e₁ j)).prod * wx R i ^ e₂ i =
              wx R i ^ e₂ i * (l.map (fun j => wx R j ^ e₁ j)).prod := by
            clear ih hnd; induction l with
            | nil => simp
            | cons j l' ihl =>
              simp only [List.map_cons, List.prod_cons]
              have h1 : wx R j ^ e₁ j * wx R i ^ e₂ i = wx R i ^ e₂ i * wx R j ^ e₁ j :=
                (Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inl_mul_comm R j i) _) _).eq
              rw [mul_assoc, ihl, ← mul_assoc, h1, mul_assoc]
          rw [mul_assoc, ← mul_assoc (l.map _).prod, hc, mul_assoc, ih hnd.2, ← mul_assoc, ← pow_add]
      exact haux (List.finRange n) (List.nodup_finRange n)
    have hwy_mul : ∀ (e₁ e₂ : Fin n → ℕ), wyProd R e₁ * wyProd R e₂ = wyProd R (fun i => e₁ i + e₂ i) := by
      intro e₁ e₂
      have haux : ∀ (l : List (Fin n)), l.Nodup →
          (l.map (fun i => wy R i ^ e₁ i)).prod * (l.map (fun i => wy R i ^ e₂ i)).prod =
            (l.map (fun i => wy R i ^ (e₁ i + e₂ i))).prod := by
        intro l; induction l with
        | nil => simp
        | cons i l ih =>
          intro hnd; rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.prod_cons]
          have hc : (l.map (fun j => wy R j ^ e₁ j)).prod * wy R i ^ e₂ i =
              wy R i ^ e₂ i * (l.map (fun j => wy R j ^ e₁ j)).prod := by
            clear ih hnd; induction l with
            | nil => simp
            | cons j l' ihl =>
              simp only [List.map_cons, List.prod_cons]
              have h1 : wy R j ^ e₁ j * wy R i ^ e₂ i = wy R i ^ e₂ i * wy R j ^ e₁ j :=
                (Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inr_mul_comm R j i) _) _).eq
              rw [mul_assoc, ihl, ← mul_assoc, h1, mul_assoc]
          rw [mul_assoc, ← mul_assoc (l.map _).prod, hc, mul_assoc, ih hnd.2, ← mul_assoc, ← pow_add]
      exact haux (List.finRange n) (List.nodup_finRange n)
    rw [hwx_mul, hwy_mul]
    exact toMvPoly_weylMonom R (p • q + r)
  apply toMvPoly_injective R n
  rw [h1, toMvPoly_weylMonom]

lemma weyl_p_decomp {R : Type*} [CommRing R] {n p : ℕ} [CharP R p] (hp : 0 < p) (a : W R n) :
    ∃ c : Rem n p → P R n, a = ∑ r : Rem n p, centerEmb R n p (c r) * weylRem R r := by
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n a
  induction f using MvPolynomial.induction_on' with
  | monomial d s =>
    let q : (Fin n ⊕ Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => d v / p)
    let r : Rem n p := fun v => ⟨d v % p, Nat.mod_lt _ hp⟩
    have hd_eq : p • q + remToFinsupp r = d := by
      ext v
      change p * (d v / p) + d v % p = d v
      exact Nat.div_add_mod (d v) p
    refine ⟨fun r' => if r' = r then monomial q s else 0, ?_⟩
    rw [Finset.sum_eq_single r (fun r' _ hne => by simp [hne]) (by simp)]
    simp only [↓reduceIte, ofMvPoly_monomial]
    have hms : monomial q s = s • monomial q (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hms, map_smul, smul_mul_assoc, weylRem, weylMonom_center_mul, hd_eq]
  | add f g hf hg =>
    obtain ⟨cf, hcf⟩ := hf
    obtain ⟨cg, hcg⟩ := hg
    refine ⟨fun r => cf r + cg r, ?_⟩
    rw [map_add, hcf, hcg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => by rw [map_add, add_mul]

lemma weyl_p_decomp_unique {R : Type*} [CommRing R] {n p : ℕ} [CharP R p] (hp : 0 < p)
    (c : Rem n p → P R n) (h0 : ∑ r : Rem n p, centerEmb R n p (c r) * weylRem R r = 0) :
    ∀ r : Rem n p, c r = 0 := by
  have hpoly : ∀ (r : Rem n p) (g : P R n),
      toMvPoly R n (centerEmb R n p g * weylRem R r) =
        ∑ q ∈ g.support, monomial (p • q + remToFinsupp r) (g.coeff q) := by
    intro r g
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hmq : monomial q (g.coeff q) = g.coeff q • monomial q (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmq, map_smul, smul_mul_assoc, map_smul, weylRem, weylMonom_center_mul,
      toMvPoly_weylMonom, smul_monomial, smul_eq_mul, mul_one]
  have hsum := congrArg (toMvPoly R n) h0
  rw [map_sum, map_zero] at hsum
  intro r
  ext q
  rw [MvPolynomial.coeff_zero]
  have hc := congrArg (fun f => f.coeff (p • q + remToFinsupp r)) hsum
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hc
  have hterm : ∀ r' : Rem n p,
      (toMvPoly R n (centerEmb R n p (c r') * weylRem R r')).coeff (p • q + remToFinsupp r) =
        if r' = r then (c r).coeff q else 0 := by
    intro r'
    rw [hpoly r' (c r'), MvPolynomial.coeff_sum]
    by_cases hrr' : r' = r
    · subst hrr'
      rw [if_pos rfl]
      by_cases hq : q ∈ (c r').support
      · rw [Finset.sum_eq_single q]
        · rw [MvPolynomial.coeff_monomial, if_pos rfl]
        · intro q' _ hne
          rw [MvPolynomial.coeff_monomial, if_neg]
          intro heq
          apply hne
          ext v
          have hv := congrArg (fun s : (Fin n ⊕ Fin n) →₀ ℕ => s v) heq
          simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hv
          exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_right_cancel hv)
        · intro h; exact absurd hq h
      · rw [MvPolynomial.notMem_support_iff.mp hq]
        refine Finset.sum_eq_zero fun q' hq' => ?_
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro heq
        apply hq
        have : q' = q := by
          ext v
          have hv := congrArg (fun s : (Fin n ⊕ Fin n) →₀ ℕ => s v) heq
          simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hv
          exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_right_cancel hv)
        rwa [← this]
    · rw [if_neg hrr']
      refine Finset.sum_eq_zero fun q' _ => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hrr'
      funext v
      apply Fin.ext
      have hv := congrArg (fun s : (Fin n ⊕ Fin n) →₀ ℕ => s v) heq
      change p * q' v + (r' v).val = p * q v + (r v).val at hv
      have hmod := congrArg (fun k => k % p) hv
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt (r' v).isLt, Nat.mod_eq_of_lt (r v).isLt] at hmod
      exact hmod
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hc
  exact hc

lemma rep_monom_linIndep {F : Type*} [Field F] {n p : ℕ} [CharP F p] (hp : p.Prime)
    (α β : Fin n → F) :
    LinearIndependent F (fun r : Rem n p => rep hp α β (weylRem F r)) := by
  have hspan : Submodule.span F (Set.range (fun r : Rem n p => rep hp α β (weylRem F r))) = ⊤ := by
    rw [eq_top_iff]
    intro T _
    obtain ⟨a, rfl⟩ := rep_surjective hp α β T
    obtain ⟨c, rfl⟩ := weyl_p_decomp hp.pos a
    rw [map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [map_mul, rep_centerEmb, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have hcard : Fintype.card (Rem n p) = Module.finrank F (Module.End F (RepSpace F n p)) := by
    rw [Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card]
    simp only [Rem, Idx, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, pow_add]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard

lemma weylRem_zero (R : Type*) [CommRing R] {n p : ℕ} (hp : 0 < p) :
    weylRem R (fun _ : Fin n ⊕ Fin n => (⟨0, hp⟩ : Fin p)) = 1 := by
  have h0 : remToFinsupp (fun _ : Fin n ⊕ Fin n => (⟨0, hp⟩ : Fin p)) = 0 := by
    ext v; rfl
  rw [weylRem, h0]
  apply toMvPoly_injective R n
  rw [toMvPoly_weylMonom, MvPolynomial.monomial_zero', map_one]
  simp [toMvPoly, toEnd]

/-- Base-change of a Weyl algebra endomorphism along a ring homomorphism `g : R →+* S`. -/
noncomputable def weylAlgHom_baseChange {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (φ : W R n →ₐ[R] W R n) : W S n →ₐ[S] W S n :=
  weylLift (fun v => weylMap g (φ (WeylAlgebra.of R v)))
    (fun i j => by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, WeylAlgebra.of_inl_mul_comm])
    (fun i j => by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, WeylAlgebra.of_inr_mul_comm])
    (fun i j hij => by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, WeylAlgebra.of_inl_mul_of_inr_of_ne R hij])
    (fun i => by
      rw [← map_mul, ← map_mul, WeylAlgebra.of_inl_mul_of_inr_self, map_add, map_mul, map_one,
        map_add, map_mul, map_one])

lemma weylRingHom_ext {R A : Type*} [CommRing R] [Ring A] {n : ℕ} {f g : W R n →+* A}
    (hC : ∀ r : R, f (algebraMap R (W R n) r) = g (algebraMap R (W R n) r))
    (hgen : ∀ v : Fin n ⊕ Fin n, f (WeylAlgebra.of R v) = g (WeylAlgebra.of R v)) : f = g := by
  ext a
  obtain ⟨p, rfl⟩ := ofMvPoly_surjective R n a
  induction p using MvPolynomial.induction_on' with
  | monomial d s =>
    rw [ofMvPoly_monomial, Algebra.smul_def, map_mul, map_mul, hC s]
    congr 1
    have hwx : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
        f (l.map (fun i => wx R i ^ e i)).prod = g (l.map (fun i => wx R i ^ e i)).prod := by
      intro l e; induction l with
      | nil => simp
      | cons i l ih =>
        rw [List.map_cons, List.prod_cons, map_mul, map_mul, map_pow, map_pow, wx, hgen (Sum.inl i), ih]
    have hwy : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
        f (l.map (fun i => wy R i ^ e i)).prod = g (l.map (fun i => wy R i ^ e i)).prod := by
      intro l e; induction l with
      | nil => simp
      | cons i l ih =>
        rw [List.map_cons, List.prod_cons, map_mul, map_mul, map_pow, map_pow, wy, hgen (Sum.inr i), ih]
    rw [weylMonom, wxProd, wyProd, map_mul, map_mul, hwx, hwy]
  | add p q hp hq => simp [map_add, hp, hq]

lemma weylAlgHom_baseChange_weylMap {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (φ : W R n →ₐ[R] W R n) (a : W R n) :
    weylAlgHom_baseChange g φ (weylMap g a) = weylMap g (φ a) := by
  let lhs : W R n →+* W S n := (weylAlgHom_baseChange g φ).toRingHom.comp (weylMap g)
  let rhs : W R n →+* W S n := (weylMap g).comp φ.toRingHom
  change lhs a = rhs a
  have h1 : ∀ r : R, lhs (algebraMap R (W R n) r) = rhs (algebraMap R (W R n) r) := by
    intro r
    simp only [lhs, rhs, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      weylMap_algebraMap, AlgHom.commutes]
  have h2 : ∀ v : Fin n ⊕ Fin n, lhs (WeylAlgebra.of R v) = rhs (WeylAlgebra.of R v) := by
    intro v
    simp only [lhs, rhs, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      weylMap_of, weylAlgHom_baseChange, weylLift_of]
  exact congrFun (congrArg DFunLike.coe (weylRingHom_ext h1 h2)) a

lemma weylMap_centerEmb {R S : Type*} [CommRing R] [CommRing S] {n p : ℕ}
    [CharP R p] [CharP S p] (g : R →+* S) (f : P R n) :
    weylMap g (centerEmb R n p f) = centerEmb S n p (MvPolynomial.map g f) := by
  apply toMvPoly_injective S n
  rw [toMvPoly_weylMap, toMvPoly_centerEmb, toMvPoly_centerEmb]
  -- `MvPolynomial.map g (expand p f) = expand p (MvPolynomial.map g f)`
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | mul_X f v ih => simp [map_mul, ih, MvPolynomial.expand_X]

lemma weylMap_weylRem {R S : Type*} [CommRing R] [CommRing S] {n p : ℕ}
    (g : R →+* S) (r : Rem n p) :
    weylMap g (weylRem R r) = weylRem S r := by
  apply toMvPoly_injective S n
  rw [toMvPoly_weylMap, weylRem, weylRem, toMvPoly_weylMonom, toMvPoly_weylMonom,
    MvPolynomial.map_monomial, map_one]

lemma exists_pth_root_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ}
    (hp : p.Prime) (x : F) : ∃ a : F, a ^ p = x := by
  have hdeg : (Polynomial.X ^ p - Polynomial.C x : Polynomial F).degree ≠ 0 := by
    have h1 : (Polynomial.X ^ p - Polynomial.C x : Polynomial F).natDegree = p := by
      rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_eq_natDegree (by
      intro h0; rw [h0, Polynomial.natDegree_zero] at h1; exact hp.ne_zero h1.symm)]
    rw [h1]; exact Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C x) hdeg
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at ha
  exact ⟨a, ha⟩

lemma exists_centerMap_of_algClosed {F : Type*} [Field F] [IsAlgClosed F] {n p : ℕ}
    [CharP F p] (hp : p.Prime) (φ : W F n →ₐ[F] W F n) :
    ∃ φ₀ : P F n →ₐ[F] P F n, ∀ f : P F n, φ (centerEmb F n p f) = centerEmb F n p (φ₀ f) := by
  have hgen : ∀ v : Fin n ⊕ Fin n, ∃ g : P F n, φ (centerEmb F n p (X v)) = centerEmb F n p g := by
    intro v
    obtain ⟨c, hc⟩ := weyl_p_decomp hp.pos (φ (centerEmb F n p (X v)))
    let r0 : Rem n p := fun _ => ⟨0, hp.pos⟩
    have hc_zero : ∀ r : Rem n p, r ≠ r0 → c r = 0 := by
      intro r hr
      -- Show `eval x (c r) = 0` for all `x : (Fin n ⊕ Fin n) → F`
      have heval : ∀ x : (Fin n ⊕ Fin n) → F, MvPolynomial.eval x (c r) = 0 := by
        intro x
        choose α hα using fun i => exists_pth_root_of_isAlgClosed hp (x (Sum.inl i))
        let β : Fin n → F := fun i => x (Sum.inr i)
        have hx : Sum.elim (fun i => α i ^ p) β = x := by
          funext w; rcases w with i | i <;> simp [hα, β]
        let ρ : W F n →ₐ[F] Module.End F (RepSpace F n p) := (rep hp α β).comp φ
        have hcent : centerEmb F n p (X v) ∈ Subalgebra.center F (W F n) := by
          rcases v with i | i
          · simpa [centerEmb, wx] using wx_pow_p_mem_center F i
          · simpa [centerEmb, wy] using wy_pow_p_mem_center F i
        have hdim : Module.finrank F (RepSpace F n p) = p ^ n := by
          rw [Module.finrank_fintype_fun_eq_card]
          simp [Idx]
        have hcomm : ∀ a : W F n, ρ (centerEmb F n p (X v)) * ρ a = ρ a * ρ (centerEmb F n p (X v)) :=
          fun a => by rw [← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp hcent a).symm]
        obtain ⟨lam, hlam⟩ := central_acts_as_scalar hp hdim ρ (ρ (centerEmb F n p (X v))) hcomm
        have hsum : ∑ r' : Rem n p,
            (MvPolynomial.eval x (c r') - if r' = r0 then lam else 0) •
              rep hp α β (weylRem F r') = 0 := by
          have h1 : rep hp α β (φ (centerEmb F n p (X v))) =
              ∑ r' : Rem n p, MvPolynomial.eval x (c r') • rep hp α β (weylRem F r') := by
            conv_lhs => rw [hc]
            rw [map_sum]
            refine Finset.sum_congr rfl fun r' _ => ?_
            rw [map_mul, rep_centerEmb, hx, smul_mul_assoc, one_mul]
          have h2 : lam • (1 : Module.End F (RepSpace F n p)) =
              ∑ r' : Rem n p, (if r' = r0 then lam else 0) • rep hp α β (weylRem F r') := by
            rw [Finset.sum_eq_single r0 (fun r' _ hne => by simp [hne]) (by simp)]
            simp only [↓reduceIte, r0, weylRem_zero F hp.pos, map_one]
          calc ∑ r' : Rem n p, (MvPolynomial.eval x (c r') - if r' = r0 then lam else 0) •
                rep hp α β (weylRem F r')
              = (∑ r' : Rem n p, MvPolynomial.eval x (c r') • rep hp α β (weylRem F r')) -
                (∑ r' : Rem n p, (if r' = r0 then lam else 0) • rep hp α β (weylRem F r')) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun r' _ =>
                  LinearMap.ext fun f => funext fun γ => by by_cases h : r' = r0 <;> simp [h, sub_mul]
            _ = rep hp α β (φ (centerEmb F n p (X v))) - lam • 1 := by rw [← h1, ← h2]
            _ = 0 := sub_eq_zero.mpr hlam
        have hlin := Fintype.linearIndependent_iff.mp (rep_monom_linIndep hp α β) _ hsum r
        simpa [hr] using hlin
      exact MvPolynomial.funext fun x => by rw [heval x, map_zero]
    refine ⟨c r0, ?_⟩
    rw [hc, Finset.sum_eq_single r0 (fun r _ hne => by rw [hc_zero r hne, map_zero, zero_mul]) (by simp),
      weylRem_zero F hp.pos, mul_one]
  choose g hg using hgen
  refine ⟨MvPolynomial.aeval g, fun f => ?_⟩
  induction f using MvPolynomial.induction_on with
  | C r => simp [centerEmb]
  | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | mul_X f v ih => rw [map_mul, map_mul, ih, map_mul, hg v, MvPolynomial.aeval_X, map_mul]

lemma exists_centerMap {K : Type*} [Field K] {n p : ℕ} [CharP K p] (hp : p.Prime)
    (φ : W K n →ₐ[K] W K n) :
    ∃ φ₀ : P K n →ₐ[K] P K n, ∀ f : P K n, φ (centerEmb K n p f) = centerEmb K n p (φ₀ f) := by
  let F := AlgebraicClosure K
  let ι : K →+* F := algebraMap K F
  haveI : CharP F p := charP_of_injective_ringHom ι.injective p
  let φ_F := weylAlgHom_baseChange ι φ
  obtain ⟨φ₀_F, hφ₀_F⟩ := exists_centerMap_of_algClosed hp φ_F
  have hgen : ∀ v : Fin n ⊕ Fin n, ∃ g : P K n, φ (centerEmb K n p (X v)) = centerEmb K n p g := by
    intro v
    obtain ⟨c, hc⟩ := weyl_p_decomp hp.pos (φ (centerEmb K n p (X v)))
    let r0 : Rem n p := fun _ => ⟨0, hp.pos⟩
    have hmap : ∑ r : Rem n p, centerEmb F n p (MvPolynomial.map ι (c r) -
        if r = r0 then φ₀_F (X v) else 0) * weylRem F r = 0 := by
      have h1 : weylMap ι (φ (centerEmb K n p (X v))) =
          ∑ r : Rem n p, centerEmb F n p (MvPolynomial.map ι (c r)) * weylRem F r := by
        conv_lhs => rw [hc]
        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => by
          rw [map_mul, weylMap_centerEmb, weylMap_weylRem]
      have h2 : weylMap ι (φ (centerEmb K n p (X v))) =
          centerEmb F n p (φ₀_F (X v)) * weylRem F r0 := by
        rw [weylRem_zero F hp.pos, mul_one, ← hφ₀_F (X v), ← weylAlgHom_baseChange_weylMap]
        congr 1
        rw [weylMap_centerEmb, MvPolynomial.map_X]
      calc ∑ r : Rem n p, centerEmb F n p (MvPolynomial.map ι (c r) -
              if r = r0 then φ₀_F (X v) else 0) * weylRem F r
          = (∑ r : Rem n p, centerEmb F n p (MvPolynomial.map ι (c r)) * weylRem F r) -
            (∑ r : Rem n p, centerEmb F n p (if r = r0 then φ₀_F (X v) else 0) * weylRem F r) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun r _ => by rw [map_sub, sub_mul]
        _ = weylMap ι (φ (centerEmb K n p (X v))) -
            centerEmb F n p (φ₀_F (X v)) * weylRem F r0 := by
            rw [← h1]
            congr 1
            rw [Finset.sum_eq_single r0 (fun r _ hne => by simp [hne]) (by simp)]
            simp
        _ = 0 := sub_eq_zero.mpr h2
    have huniq := weyl_p_decomp_unique hp.pos _ hmap
    have hc_zero : ∀ r : Rem n p, r ≠ r0 → c r = 0 := by
      intro r hr
      have h0 := huniq r
      rw [if_neg hr, sub_zero] at h0
      exact MvPolynomial.map_injective ι ι.injective (by rw [h0, map_zero])
    refine ⟨c r0, ?_⟩
    rw [hc, Finset.sum_eq_single r0 (fun r _ hne => by rw [hc_zero r hne, map_zero, zero_mul]) (by simp),
      weylRem_zero K hp.pos, mul_one]
  choose g hg using hgen
  refine ⟨MvPolynomial.aeval g, fun f => ?_⟩
  induction f using MvPolynomial.induction_on with
  | C r => simp [centerEmb]
  | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | mul_X f v ih => rw [map_mul, map_mul, ih, map_mul, hg v, MvPolynomial.aeval_X, map_mul]

lemma totalDegree_expand {R : Type*} [CommRing R] [IsDomain R] {σ : Type*} [DecidableEq σ] {p : ℕ}
    (hp : 0 < p) (f : MvPolynomial σ R) :
    (MvPolynomial.expand p f).totalDegree = p * f.totalDegree := by
  have hexp : MvPolynomial.expand p f = ∑ e ∈ f.support, monomial (p • e) (f.coeff e) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ => MvPolynomial.expand_monomial p e (f.coeff e)
  have hsum_smul : ∀ e : σ →₀ ℕ, (p • e).sum (fun _ k => k) = p * e.sum (fun _ k => k) := by
    intro e
    rw [Finsupp.sum_smul_index' (fun _ => rfl)]
    simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
  by_cases hf : f = 0
  · subst hf; simp
  · apply le_antisymm
    · refine Finset.sup_le fun d hd => ?_
      rw [MvPolynomial.mem_support_iff, hexp, MvPolynomial.coeff_sum] at hd
      obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
      rw [MvPolynomial.coeff_monomial] at hne
      split_ifs at hne with hpe
      · rw [← hpe, hsum_smul]
        exact Nat.mul_le_mul_left p (MvPolynomial.le_totalDegree he)
      · exact absurd rfl hne
    · obtain ⟨e, he, hdeg⟩ := Finset.exists_mem_eq_sup f.support
        (MvPolynomial.support_nonempty.mpr hf) (fun d => d.sum (fun _ k => k))
      have hpe_mem : p • e ∈ (MvPolynomial.expand p f).support := by
        rw [MvPolynomial.mem_support_iff, hexp, MvPolynomial.coeff_sum]
        rw [Finset.sum_eq_single e]
        · rw [MvPolynomial.coeff_monomial, if_pos rfl]
          exact MvPolynomial.mem_support_iff.mp he
        · intro e' _ hne
          rw [MvPolynomial.coeff_monomial, if_neg]
          intro h; apply hne
          ext v; exact Nat.eq_of_mul_eq_mul_left hp (congrArg (fun s : σ →₀ ℕ => s v) h)
        · intro h; exact absurd he h
      have hle := MvPolynomial.le_totalDegree hpe_mem
      rw [hsum_smul, ← hdeg] at hle
      exact hle

lemma centerMap_totalDegree_eq {K : Type*} [Field K] {n p : ℕ} [CharP K p] (hp : p.Prime)
    (φ : W K n →ₐ[K] W K n) (φ₀ : P K n →ₐ[K] P K n)
    (hφ₀ : ∀ f : P K n, φ (centerEmb K n p f) = centerEmb K n p (φ₀ f))
    (v : Fin n ⊕ Fin n) :
    (φ₀ (X v)).totalDegree = (toMvPoly K n (φ (WeylAlgebra.of K v))).totalDegree := by
  have hne : φ (WeylAlgebra.of K v) ≠ 0 := by
    intro h0
    have h01 : (0 : W K n) ≠ 1 := fun h => by
      have := congrArg (toMvPoly K n) h
      simp [toMvPoly, toEnd] at this
    rcases v with i | i
    · have hrel := congrArg φ (WeylAlgebra.of_inl_mul_of_inr_self K i)
      simp only [map_mul, map_add, map_one, h0, zero_mul, mul_zero, zero_add] at hrel
      exact h01 hrel
    · have hrel := congrArg φ (WeylAlgebra.of_inl_mul_of_inr_self K i)
      simp only [map_mul, map_add, map_one, h0, zero_mul, mul_zero, zero_add] at hrel
      exact h01 hrel
  have h1 : toMvPoly K n (φ (centerEmb K n p (X v))) = MvPolynomial.expand p (φ₀ (X v)) := by
    rw [hφ₀, toMvPoly_centerEmb]
  have h2 : φ (centerEmb K n p (X v)) = φ (WeylAlgebra.of K v) ^ p := by
    rw [← map_pow]
    congr 1
    simp only [centerEmb, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]
  have h3 := congrArg MvPolynomial.totalDegree h1
  rw [h2, toMvPoly_pow_totalDegree hne, totalDegree_expand hp.pos] at h3
  exact Nat.eq_of_mul_eq_mul_left hp.pos h3.symm

lemma bijective_of_centerMap_bijective {K : Type*} [Field K] {n p : ℕ} [CharP K p] (hp : p.Prime)
    (φ : W K n →ₐ[K] W K n) (φ₀ : P K n →ₐ[K] P K n)
    (hφ₀ : ∀ f : P K n, φ (centerEmb K n p f) = centerEmb K n p (φ₀ f))
    (hbij : Function.Bijective φ₀) : Function.Bijective φ := by
  -- Express `φ (weylRem K r) = ∑ r', centerEmb K n p (M r' r) * weylRem K r'`
  have hdecomp : ∀ r : Rem n p, ∃ c : Rem n p → P K n,
      φ (weylRem K r) = ∑ r' : Rem n p, centerEmb K n p (c r') * weylRem K r' :=
    fun r => weyl_p_decomp hp.pos (φ (weylRem K r))
  choose c hc using hdecomp
  let M : Matrix (Rem n p) (Rem n p) (P K n) := fun r' r => c r r'
  -- Step 1: Show `IsUnit M.det` in `P K n` using Nullstellensatz over `F := AlgebraicClosure K`
  have hdet_unit : IsUnit M.det := by
    let F := AlgebraicClosure K
    let ι : K →+* F := algebraMap K F
    haveI : CharP F p := charP_of_injective_ringHom ι.injective p
    let φ_F := weylAlgHom_baseChange ι φ
    let φ₀_F : P F n →ₐ[F] P F n := MvPolynomial.aeval (fun v => MvPolynomial.map ι (φ₀ (X v)))
    have hφ₀_F_map : ∀ f : P K n, φ₀_F (MvPolynomial.map ι f) = MvPolynomial.map ι (φ₀ f) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C r => simp [φ₀_F]
      | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | mul_X f v ih => rw [map_mul, map_mul, ih, map_mul, MvPolynomial.map_X, map_mul]; simp [φ₀_F]
    have hφ₀_F : ∀ f : P F n, φ_F (centerEmb F n p f) = centerEmb F n p (φ₀_F f) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C r => simp [centerEmb]
      | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | mul_X f v ih =>
        rw [map_mul, map_mul, ih, map_mul, map_mul]
        congr 1
        have hXv : centerEmb F n p (X v) = weylMap ι (centerEmb K n p (X v)) := by
          rw [weylMap_centerEmb, MvPolynomial.map_X]
        rw [hXv, weylAlgHom_baseChange_weylMap, hφ₀, weylMap_centerEmb]
        simp [φ₀_F]
    have hM_F : ∀ r : Rem n p, φ_F (weylRem F r) =
        ∑ r' : Rem n p, centerEmb F n p (MvPolynomial.map ι (M r' r)) * weylRem F r' := by
      intro r
      rw [← weylMap_weylRem ι r, weylAlgHom_baseChange_weylMap, hc r, map_sum]
      refine Finset.sum_congr rfl fun r' _ => by
        rw [map_mul, weylMap_centerEmb, weylMap_weylRem]
    -- Show `eval x (map ι M.det) ≠ 0` for every `x : (Fin n ⊕ Fin n) → F`
    have hno_root : ∀ x : (Fin n ⊕ Fin n) → F, MvPolynomial.eval x (MvPolynomial.map ι M.det) ≠ 0 := by
      intro x
      let ev : P K n →+* F := (MvPolynomial.eval x).comp (MvPolynomial.map ι)
      change ev M.det ≠ 0
      rw [RingHom.map_det]
      let A : Matrix (Rem n p) (Rem n p) F := M.map ev
      change A.det ≠ 0
      intro hdet0
      obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      -- Lift `x` and `y := fun w => eval x (φ₀_F (X w))`
      choose α hα using fun i => exists_pth_root_of_isAlgClosed hp (x (Sum.inl i))
      let β : Fin n → F := fun i => x (Sum.inr i)
      have hx : Sum.elim (fun i => α i ^ p) β = x := by
        funext w; rcases w with i | i <;> simp [hα, β]
      let y : (Fin n ⊕ Fin n) → F := fun w => MvPolynomial.eval x (φ₀_F (X w))
      choose α' hα' using fun i => exists_pth_root_of_isAlgClosed hp (y (Sum.inl i))
      let β' : Fin n → F := fun i => y (Sum.inr i)
      have hy : Sum.elim (fun i => α' i ^ p) β' = y := by
        funext w; rcases w with i | i <;> simp [hα', β']
      let ρ : W F n →ₐ[F] Module.End F (RepSpace F n p) := (rep hp α β).comp φ_F
      have hρ_cent : ∀ f : P F n, ρ (centerEmb F n p f) = MvPolynomial.eval y f • 1 := by
        intro f
        change rep hp α β (φ_F (centerEmb F n p f)) = _
        rw [hφ₀_F, rep_centerEmb, hx]
        congr 1
        induction f using MvPolynomial.induction_on with
        | C r => simp
        | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
        | mul_X f w ih => simp [map_mul, ih, y]
      have hker_le : ∀ a : W F n, rep hp α' β' a = 0 → ρ a = 0 := by
        intro a ha
        obtain ⟨d, rfl⟩ := weyl_p_decomp hp.pos a
        have ha' : ∑ r : Rem n p, MvPolynomial.eval y (d r) • rep hp α' β' (weylRem F r) = 0 := by
          rw [map_sum] at ha
          refine Eq.trans ?_ ha
          refine Finset.sum_congr rfl fun r _ => by
            rw [map_mul, rep_centerEmb, hy, smul_mul_assoc, one_mul]
        have hd0 := Fintype.linearIndependent_iff.mp (rep_monom_linIndep hp α' β') _ ha'
        rw [map_sum]
        refine Finset.sum_eq_zero fun r _ => ?_
        rw [map_mul, hρ_cent, hd0 r, zero_smul, zero_mul]
      -- Now let `b := ∑ r, v r • weylRem F r`
      let b : W F n := ∑ r : Rem n p, v r • weylRem F r
      have hρb : ρ b = 0 := by
        change rep hp α β (φ_F b) = 0
        simp only [b, map_sum, map_smul, hM_F]
        calc ∑ r : Rem n p, v r • ∑ r' : Rem n p,
              rep hp α β (centerEmb F n p (MvPolynomial.map ι (M r' r)) * weylRem F r')
            = ∑ r : Rem n p, ∑ r' : Rem n p,
              (A r' r * v r) • rep hp α β (weylRem F r') := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun r' _ => ?_
              rw [map_mul, rep_centerEmb, hx, smul_mul_assoc, one_mul, smul_smul, mul_comm]
              rfl
          _ = ∑ r' : Rem n p, (A.mulVec v r') • rep hp α β (weylRem F r') := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r' _ => ?_
              rw [← Finset.sum_smul]
              rfl
          _ = 0 := by simp [hv0]
      have hT0_ne : rep hp α' β' b ≠ 0 := by
        intro h0
        apply hv_ne
        funext r
        rw [map_sum] at h0
        have h0' : ∑ r' : Rem n p, v r' • rep hp α' β' (weylRem F r') = 0 := by
          simpa [map_smul] using h0
        exact Fintype.linearIndependent_iff.mp (rep_monom_linIndep hp α' β') v h0' r
      -- Since `rep hp α' β' b ≠ 0`, pick nonzero matrix entry `(γ₁, δ₁)`
      have hex : ∃ γ₁ δ₁ : Idx n p, rep hp α' β' b (Pi.single δ₁ 1) γ₁ ≠ 0 := by
        by_contra hall; push_neg at hall
        apply hT0_ne
        refine LinearMap.ext fun f => funext fun γ => ?_
        have hf : f = ∑ δ : Idx n p, f δ • Pi.single δ (1 : F) := by
          funext δ'; simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hf]
        simp [map_sum, map_smul, Finset.sum_apply, hall]
      obtain ⟨γ₁, δ₁, hentry⟩ := hex
      -- Matrix units `E_{γ, γ₁}` and `E_{δ₁, γ}` are in `range (rep hp α' β')`
      have hE : ∀ γ δ : Idx n p, ∃ u : W F n, ∀ (f : RepSpace F n p) (η : Idx n p),
          rep hp α' β' u f η = if η = γ then f δ else 0 := by
        intro γ δ
        let T : Module.End F (RepSpace F n p) :=
          { toFun := fun f η => if η = γ then f δ else 0
            map_add' := fun f g => funext fun η => by by_cases h : η = γ <;> simp [h]
            map_smul' := fun s f => funext fun η => by by_cases h : η = γ <;> simp [h] }
        obtain ⟨u, hu⟩ := rep_surjective hp α' β' T
        exact ⟨u, fun f η => congrFun (congrArg (fun L => L f) hu) η⟩
      choose uL huL using fun γ => hE γ γ₁
      choose uR huR using fun γ => hE δ₁ γ
      let s0 : F := rep hp α' β' b (Pi.single δ₁ 1) γ₁
      let w : W F n := 1 - s0⁻¹ • ∑ γ : Idx n p, uL γ * b * uR γ
      have hw_ker : rep hp α' β' w = 0 := by
        refine LinearMap.ext fun f => funext fun η => ?_
        simp only [w, map_sub, map_one, map_smul, map_sum, map_mul, LinearMap.sub_apply,
          Module.End.one_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.zero_apply, Pi.zero_apply,
          Module.End.mul_apply, huL]
        rw [Finset.sum_eq_single η (fun γ _ hne => by simp [Ne.symm hne]) (by simp)]
        simp only [↓reduceIte]
        have harg : (rep hp α' β' (uR η)) f = f η • Pi.single δ₁ (1 : F) := by
          funext η'; rw [huR]; by_cases h : η' = δ₁ <;> simp [h]
        rw [harg, map_smul, Pi.smul_apply, smul_eq_mul]
        change f η - s0⁻¹ * (f η * s0) = 0
        rw [mul_comm (f η) s0, ← mul_assoc, inv_mul_cancel₀ hentry, one_mul, sub_self]
      have hρw := hker_le w hw_ker
      have hρ1 : (1 : Module.End F (RepSpace F n p)) = 0 := by
        simp only [w, map_sub, map_one, map_smul, map_sum, map_mul, hρb, mul_zero, zero_mul,
          Finset.sum_const_zero, smul_zero, sub_zero] at hρw
        exact hρw
      have h10 : (1 : Module.End F (RepSpace F n p)) (fun _ => 1) (fun _ => ⟨0, hp.pos⟩) = 0 := by
        rw [hρ1]; rfl
      exact one_ne_zero h10
    -- Apply Nullstellensatz over `F`: `MvPolynomial.map ι M.det` is a unit in `P F n`
    haveI : IsAlgClosed F := AlgebraicClosure.isAlgClosed K
    have hzeroLocus : MvPolynomial.zeroLocus F (Ideal.span ({MvPolynomial.map ι M.det} : Set (P F n))) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hno_root x (hx (MvPolynomial.map ι M.det) (Ideal.subset_span rfl))
    have h1_rad : (1 : P F n) ∈ (Ideal.span ({MvPolynomial.map ι M.det} : Set (P F n))).radical := by
      have hrad := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := F)
        (Ideal.span ({MvPolynomial.map ι M.det} : Set (P F n)))
      rw [← hrad, hzeroLocus, MvPolynomial.vanishingIdeal_empty]
      trivial
    obtain ⟨k, hk⟩ := h1_rad
    rw [one_pow, Ideal.mem_span_singleton] at hk
    obtain ⟨q, hq⟩ := hk
    have hdeg0 : (MvPolynomial.map ι M.det).totalDegree = 0 := by
      have h0 : (MvPolynomial.map ι M.det * q).totalDegree = 0 := by
        rw [← hq]; exact MvPolynomial.totalDegree_one
      have hne1 : MvPolynomial.map ι M.det ≠ 0 := fun h => by rw [h, zero_mul] at hq; exact one_ne_zero hq
      have hne2 : q ≠ 0 := fun h => by rw [h, mul_zero] at hq; exact one_ne_zero hq
      rw [mvPoly_totalDegree_mul_of_isDomain hne1 hne2] at h0
      omega
    have hdet_deg0 : M.det.totalDegree = 0 := by
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg0
      have hC : M.det = MvPolynomial.C (M.det.coeff 0) := by
        ext d
        apply ι.injective
        rw [← MvPolynomial.coeff_map, hdeg0, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
        split_ifs with h
        · rw [MvPolynomial.coeff_map]
        · simp
      rw [hC]; exact MvPolynomial.totalDegree_C _
    have hdet_C : M.det = MvPolynomial.C (M.det.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdet_deg0
    have hdet_ne : M.det.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdet_C
      rw [hdet_C, map_zero, zero_mul] at hq
      exact one_ne_zero hq
    rw [hdet_C]
    exact (IsUnit.mk0 (M.det.coeff 0) hdet_ne).map MvPolynomial.C
  -- Step 2: `M` is invertible over `P K n`, so `φ` is bijective!
  let Minv : Matrix (Rem n p) (Rem n p) (P K n) := M⁻¹
  have hM_mul : M * Minv = 1 := Matrix.mul_nonsing_inv M hdet_unit
  have hMinv_mul : Minv * M = 1 := Matrix.nonsing_inv_mul M hdet_unit
  have hφ_decomp : ∀ c : Rem n p → P K n,
      φ (∑ r : Rem n p, centerEmb K n p (c r) * weylRem K r) =
        ∑ r' : Rem n p, centerEmb K n p (∑ r : Rem n p, M r' r * φ₀ (c r)) * weylRem K r' := by
    intro c
    rw [map_sum]
    calc ∑ r : Rem n p, φ (centerEmb K n p (c r) * weylRem K r)
        = ∑ r : Rem n p, ∑ r' : Rem n p,
            centerEmb K n p (M r' r * φ₀ (c r)) * weylRem K r' := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_mul, hφ₀, hc r, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r' _ => ?_
          rw [← mul_assoc, ← map_mul, mul_comm (φ₀ (c r)) (M r' r)]
      _ = ∑ r' : Rem n p, centerEmb K n p (∑ r : Rem n p, M r' r * φ₀ (c r)) * weylRem K r' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r' _ => by rw [map_sum, Finset.sum_mul]
  constructor
  · -- Injectivity
    intro a₁ a₂ ha
    rw [← sub_eq_zero]
    have h0 : φ (a₁ - a₂) = 0 := by rw [map_sub, ha, sub_self]
    obtain ⟨c, hc_eq⟩ := weyl_p_decomp hp.pos (a₁ - a₂)
    rw [hc_eq] at h0 ⊢
    rw [hφ_decomp] at h0
    have hmv : M.mulVec (fun r => φ₀ (c r)) = 0 := funext fun r' =>
      weyl_p_decomp_unique hp.pos _ h0 r'
    have hφc0 : (fun r => φ₀ (c r)) = 0 := by
      have := congrArg (Minv.mulVec) hmv
      rwa [Matrix.mulVec_mulVec, hMinv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    refine Finset.sum_eq_zero fun r _ => ?_
    have hcr : c r = 0 := hbij.1 (by simpa [map_zero] using congrFun hφc0 r)
    rw [hcr, map_zero, zero_mul]
  · -- Surjectivity
    intro b
    obtain ⟨d, rfl⟩ := weyl_p_decomp hp.pos b
    let e : Rem n p → P K n := Minv.mulVec d
    choose c hc_eq using fun r => hbij.2 (e r)
    refine ⟨∑ r : Rem n p, centerEmb K n p (c r) * weylRem K r, ?_⟩
    rw [hφ_decomp]
    refine Finset.sum_congr rfl fun r' _ => ?_
    congr 2
    have h1 : (∑ r : Rem n p, M r' r * φ₀ (c r)) = (M.mulVec e) r' := by
      simp only [Matrix.mulVec, dotProduct, hc_eq]
    rw [h1, show M.mulVec e = d from by rw [Matrix.mulVec_mulVec, hM_mul, Matrix.one_mulVec]]

/- Module 4: Mod `p^2` commutator and Poisson bracket preservation -/

section PoissonModP2

/-- Congruence modulo `m` in `W R n`: `a - b = (m : R) • t`. -/
def ModW {R : Type*} [CommRing R] {n : ℕ} (m : ℕ) (a b : W R n) : Prop :=
  ∃ t : W R n, a - b = (m : R) • t

lemma ModW.refl {R : Type*} [CommRing R] {n : ℕ} (m : ℕ) (a : W R n) : ModW m a a :=
  ⟨0, by simp⟩

lemma ModW.symm {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} {a b : W R n} (h : ModW m a b) :
    ModW m b a := by
  obtain ⟨t, ht⟩ := h
  exact ⟨-t, by rw [smul_neg, ← ht, neg_sub]⟩

lemma ModW.trans {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} {a b c : W R n}
    (h1 : ModW m a b) (h2 : ModW m b c) : ModW m a c := by
  obtain ⟨t1, ht1⟩ := h1; obtain ⟨t2, ht2⟩ := h2
  exact ⟨t1 + t2, by rw [smul_add, ← ht1, ← ht2]; abel⟩

lemma ModW.add {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} {a₁ a₂ b₁ b₂ : W R n}
    (h1 : ModW m a₁ b₁) (h2 : ModW m a₂ b₂) : ModW m (a₁ + a₂) (b₁ + b₂) := by
  obtain ⟨t1, ht1⟩ := h1; obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 + t2, ?_⟩
  rw [smul_add, ← ht1, ← ht2]; abel

lemma ModW.sub {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} {a₁ a₂ b₁ b₂ : W R n}
    (h1 : ModW m a₁ b₁) (h2 : ModW m a₂ b₂) : ModW m (a₁ - a₂) (b₁ - b₂) := by
  obtain ⟨t1, ht1⟩ := h1; obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 - t2, ?_⟩
  rw [smul_sub, ← ht1, ← ht2]; abel

lemma ModW.mul_left {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} (c : W R n) {a b : W R n}
    (h : ModW m a b) : ModW m (c * a) (c * b) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨c * t, by rw [← mul_sub, ht, mul_smul_comm]⟩

lemma ModW.mul_right {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} (c : W R n) {a b : W R n}
    (h : ModW m a b) : ModW m (a * c) (b * c) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t * c, by rw [← sub_mul, ht, smul_mul_assoc]⟩

lemma ModW.mul {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} {a₁ a₂ b₁ b₂ : W R n}
    (h1 : ModW m a₁ b₁) (h2 : ModW m a₂ b₂) : ModW m (a₁ * a₂) (b₁ * b₂) :=
  (h1.mul_right a₂).trans (h2.mul_left b₁)

lemma ModW.smul_scale {R : Type*} [CommRing R] {n : ℕ} {m : ℕ} (r : R) {a b : W R n}
    (h : ModW m a b) : ModW m (r • a) (r • b) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨r • t, by rw [← smul_sub, ht, smul_comm]⟩

lemma ModW.mul_p {R : Type*} [CommRing R] {n : ℕ} {p : ℕ} {a b : W R n}
    (h : ModW p a b) : ModW (p * p) ((p : R) • a) ((p : R) • b) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [← smul_sub, ht, smul_smul, Nat.cast_mul]

lemma ModW.map_weylMap {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} {m : ℕ} (g : R →+* S)
    {a b : W R n} (h : ModW m a b) : ModW m (weylMap g a) (weylMap g b) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨weylMap g t, ?_⟩
  rw [← map_sub, ht, Algebra.smul_def, map_mul, weylMap_algebraMap, map_natCast, ← Algebra.smul_def]

lemma wx_pow_mul_wy {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) :
    wx R i ^ k * wy R i = wy R i * wx R i ^ k + (k : R) • wx R i ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, show wx R i * wy R i = wy R i * wx R i + 1 from
      WeylAlgebra.of_inl_mul_of_inr_self R i, mul_add, mul_one, ← mul_assoc, ih]
    rcases k with _ | k
    · simp
    · rw [add_mul, smul_mul_assoc, Nat.add_sub_cancel, ← pow_succ]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      rw [mul_assoc]
      abel

lemma wx_mul_wy_pow {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) (k : ℕ) :
    wx R i * wy R i ^ k = wy R i ^ k * wx R i + (k : R) • wy R i ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mul_assoc, show wx R i * wy R i = wy R i * wx R i + 1 from
      WeylAlgebra.of_inl_mul_of_inr_self R i, add_mul, one_mul, mul_assoc, ih]
    rcases k with _ | k
    · simp
    · rw [mul_add, mul_smul_comm, Nat.add_sub_cancel, ← pow_succ']
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      rw [mul_assoc]
      abel

/-- Key congruence mod `p^2`: for any prime `p`, `[x_i^p, y_i^p] ≡ -p (mod p^2)` in `W R n`. -/
lemma wx_pow_p_comm_wy_pow_p_mod_p_sq {R : Type*} [CommRing R] {n p : ℕ} (hp : p.Prime)
    (i : Fin n) :
    ModW (p * p) (wx R i ^ p * wy R i ^ p - wy R i ^ p * wx R i ^ p) (-((p : R) • (1 : W R n))) := by
  -- Prove over `ℤ`, then push forward via `weylMap (Int.castRingHom R)`
  suffices hZ : ModW (p * p) (wx ℤ i ^ p * wy ℤ i ^ p - wy ℤ i ^ p * wx ℤ i ^ p)
      (-((p : ℤ) • (1 : W ℤ n))) by
    have h := hZ.map_weylMap (Int.castRingHom R)
    simpa [wx, wy, Algebra.smul_def] using h
  -- Induct on `b ≤ p`: `x^p * y^b ≡ y^b * x^p + p • ∑_{k=1}^b c(b, k) • y^{b-k} * x^{p-k} (mod p^2)`
  -- where `c(b, k) = (-1)^(k-1) * (k-1)! * C(b, k)`
  let c : ℕ → ℕ → ℤ := fun b k => (-1 : ℤ) ^ (k - 1) * ((k - 1).factorial : ℤ) * (Nat.choose b k : ℤ)
  have hstep : ∀ b : ℕ, b ≤ p →
      ModW (p * p) (wx ℤ i ^ p * wy ℤ i ^ b)
        (wy ℤ i ^ b * wx ℤ i ^ p + (p : ℤ) • ∑ k ∈ Finset.Icc 1 b,
          c b k • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - k))) := by
    intro b
    induction b with
    | zero => intro _; simp; exact ModW.refl _ _
    | succ b ih =>
      intro hbp
      have ihb := ih (Nat.le_of_succ_le hbp)
      have hmul : ModW (p * p) (wx ℤ i ^ p * wy ℤ i ^ (b + 1))
          ((wy ℤ i ^ b * wx ℤ i ^ p + (p : ℤ) • ∑ k ∈ Finset.Icc 1 b,
            c b k • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - k))) * wy ℤ i) := by
        rw [pow_succ, ← mul_assoc]
        exact ihb.mul_right (wy ℤ i)
      refine hmul.trans ?_
      rw [add_mul, mul_assoc, wx_pow_mul_wy, mul_add, ← mul_assoc, ← pow_succ,
        mul_smul_comm, smul_mul_assoc, Finset.sum_mul]
      -- Simplify each term `(y^{b-k} * x^{p-k}) * y` mod `p`
      have hterm_mod : ∀ k ∈ Finset.Icc 1 b,
          ModW p (c b k • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - k)) * wy ℤ i)
            (c b k • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) +
             (-((k : ℤ) * c b k)) • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1)))) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [smul_mul_assoc, mul_assoc, wx_pow_mul_wy, mul_add, ← mul_assoc, ← pow_succ,
          mul_smul_comm, smul_add]
        have hbk : b - k + 1 = b + 1 - k := by omega
        have hpk : p - k - 1 = p - (k + 1) := by omega
        rw [hbk, hpk]
        refine (ModW.refl p _).add ?_
        refine ⟨c b k • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1))), ?_⟩
        have h1 : c b k * ((p - k : ℕ) : ℤ) - -((k : ℤ) * c b k) = (p : ℤ) * c b k := by
          rw [Nat.cast_sub (by omega)]; ring
        have h1' := congrArg (fun z : ℤ => z • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1)))) h1
        simpa [sub_smul, mul_smul, Algebra.smul_def, zsmul_eq_mul, add_mul, mul_assoc] using h1'
      have hsum_mod : ModW p
          (∑ k ∈ Finset.Icc 1 b, c b k • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - k)) * wy ℤ i)
          (∑ k ∈ Finset.Icc 1 b, (c b k • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) +
            (-((k : ℤ) * c b k)) • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1))))) := by
        -- Sum of `ModW p` terms
        have haux : ∀ (s : Finset ℕ) (f g : ℕ → W ℤ n),
            (∀ k ∈ s, ModW p (f k) (g k)) → ModW p (∑ k ∈ s, f k) (∑ k ∈ s, g k) := by
          intro s f g hfg
          induction s using Finset.cons_induction with
          | empty => simp; exact ModW.refl _ _
          | cons a s ha ihs =>
            rw [Finset.sum_cons, Finset.sum_cons]
            exact (hfg a (Finset.mem_cons_self a s)).add
              (ihs fun k hk => hfg k (Finset.mem_cons_of_mem hk))
        exact haux _ _ _ hterm_mod
      have hRHS_mod := (ModW.refl (p * p) (wy ℤ i ^ (b + 1) * wx ℤ i ^ p)).add
        ((ModW.refl (p * p) ((p : ℤ) • (wy ℤ i ^ b * wx ℤ i ^ (p - 1)))).add hsum_mod.mul_p)
      rw [add_assoc]
      refine hRHS_mod.trans ?_
      -- Now match the exact algebraic identity on the `p • (...)` sum!
      have hid : (p : ℤ) • (wy ℤ i ^ b * wx ℤ i ^ (p - 1)) +
          (p : ℤ) • ∑ k ∈ Finset.Icc 1 b, (c b k • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) +
            (-((k : ℤ) * c b k)) • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1)))) =
          (p : ℤ) • ∑ k ∈ Finset.Icc 1 (b + 1), c (b + 1) k • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) := by
        rw [← smul_add]
        congr 1
        rw [Finset.sum_add_distrib]
        -- Shift the second sum from `k ∈ Icc 1 b` to `j = k + 1 ∈ Icc 2 (b + 1)`
        have hshift : ∑ k ∈ Finset.Icc 1 b, (-((k : ℤ) * c b k)) • (wy ℤ i ^ (b - k) * wx ℤ i ^ (p - (k + 1))) =
            ∑ j ∈ Finset.Icc 2 (b + 1), (-(((j - 1 : ℕ) : ℤ) * c b (j - 1))) • (wy ℤ i ^ (b + 1 - j) * wx ℤ i ^ (p - j)) := by
          refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
          · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
          · intro k₁ _ k₂ _ h; omega
          · intro j hj; rw [Finset.mem_Icc] at hj
            exact ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k hk
            rw [Nat.add_sub_cancel, Nat.add_sub_add_right]
        rw [hshift]
        -- Write all three parts over `Finset.Icc 1 (b + 1)` using `if`
        have h1 : wy ℤ i ^ b * wx ℤ i ^ (p - 1) =
            ∑ k ∈ Finset.Icc 1 (b + 1), (if k = 1 then (1 : ℤ) else 0) • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) := by
          rw [Finset.sum_eq_single 1 (fun k _ hne => by simp [hne]) (fun h => absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h)]
          simp
        have h2 : ∑ k ∈ Finset.Icc 1 b, c b k • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) =
            ∑ k ∈ Finset.Icc 1 (b + 1), (if k ≤ b then c b k else 0) • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) := by
          simp only [ite_smul, zero_smul]
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun k _ => rfl
          ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        have h3 : ∑ j ∈ Finset.Icc 2 (b + 1), (-(((j - 1 : ℕ) : ℤ) * c b (j - 1))) • (wy ℤ i ^ (b + 1 - j) * wx ℤ i ^ (p - j)) =
            ∑ k ∈ Finset.Icc 1 (b + 1), (if 2 ≤ k then -(((k - 1 : ℕ) : ℤ) * c b (k - 1)) else 0) • (wy ℤ i ^ (b + 1 - k) * wx ℤ i ^ (p - k)) := by
          simp only [ite_smul, zero_smul]
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun k _ => rfl
          ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        rw [← add_smul, ← add_smul]
        congr 1
        by_cases hk1 : k = 1
        · subst hk1
          by_cases hb0 : b = 0
          · subst hb0; simp [c]
          · have h1b : 1 ≤ b := by omega
            simp only [↓reduceIte, h1b, Nat.not_ofNat_le_one, add_zero, c]
            simp [Nat.choose_one_right]; ring
        · have h2k : 2 ≤ k := by omega
          simp only [hk1, ↓reduceIte, h2k, zero_add]
          rcases k with _ | _ | m
          · omega
          · omega
          · by_cases hkb : m + 2 ≤ b
            · simp only [hkb, ↓reduceIte, c, Nat.add_sub_cancel]
              rw [Nat.choose_succ_succ b (m + 1), Nat.factorial_succ]
              push_cast
              rw [pow_succ (-1 : ℤ) m]
              ring
            · have heq : m + 2 = b + 1 := by omega
              have hmb : m + 1 = b := by omega
              rw [if_neg hkb, zero_add]
              simp only [c, Nat.add_sub_cancel, ← hmb, Nat.choose_self, Nat.factorial_succ]
              push_cast
              rw [pow_succ (-1 : ℤ) m]
              ring
      exact (congrArg (fun x => wy ℤ i ^ (b + 1) * wx ℤ i ^ p + x) hid) ▸ ModW.refl _ _
  -- Specialize `hstep` to `b = p`
  have hp_step := hstep p le_rfl
  have hcomm_p : ModW (p * p) (wx ℤ i ^ p * wy ℤ i ^ p - wy ℤ i ^ p * wx ℤ i ^ p)
      ((p : ℤ) • ∑ k ∈ Finset.Icc 1 p, c p k • (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k))) := by
    obtain ⟨t, ht⟩ := hp_step
    exact ⟨t, by rw [← ht]; abel⟩
  refine hcomm_p.trans ?_
  -- Every term with `1 ≤ k < p` has `p ∣ C(p, k)`, and the `k = p` term is `(-1)^(p-1) * (p-1)! ≡ -1 (mod p)`
  have hsum_p : ModW p (∑ k ∈ Finset.Icc 1 p, c p k • (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k))) (-1) := by
    have hset : Finset.Icc 1 p = insert p (Finset.Ico 1 p) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; have := hp.pos; omega
    rw [hset, Finset.sum_insert (by simp), add_comm]
    simp only [Nat.sub_self, pow_zero, mul_one]
    have hfirst : ModW p (∑ k ∈ Finset.Ico 1 p, c p k • (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k))) 0 := by
      have haux : ∀ (s : Finset ℕ), (∀ k ∈ s, 1 ≤ k ∧ k < p) →
          ModW p (∑ k ∈ s, c p k • (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k))) 0 := by
        intro s hs
        induction s using Finset.cons_induction with
        | empty => simp; exact ModW.refl _ _
        | cons k s hk ihs =>
          rw [Finset.sum_cons, ← zero_add (0 : W ℤ n)]
          refine ModW.add ?_ (ihs fun j hj => hs j (Finset.mem_cons_of_mem hj))
          obtain ⟨hk1, hkp⟩ := hs k (Finset.mem_cons_self k s)
          obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega) hkp
          refine ⟨((-1 : ℤ) ^ (k - 1) * ((k - 1).factorial : ℤ) * (m : ℤ)) •
            (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k)), ?_⟩
          rw [sub_zero]
          have h1 : c p k = (p : ℤ) * ((-1 : ℤ) ^ (k - 1) * ((k - 1).factorial : ℤ) * (m : ℤ)) := by
            simp only [c, hm, Nat.cast_mul]; ring
          have h1' := congrArg (fun z : ℤ => z • (wy ℤ i ^ (p - k) * wx ℤ i ^ (p - k))) h1
          simpa [mul_smul, Algebra.smul_def, zsmul_eq_mul] using h1'
      exact haux _ fun k hk => Finset.mem_Ico.mp hk
    have hlast : ModW p (c p p • (1 : W ℤ n)) (-1) := by
      have : Fact p.Prime := ⟨hp⟩
      have hwilson : (((p - 1).factorial : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
      have hsign : (((-1 : ℤ) ^ (p - 1) * ((p - 1).factorial : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [hwilson]
        rcases hp.eq_two_or_odd with rfl | hodd
        · rw [show (-1 : ZMod 2) ^ (2 - 1) * -1 + 1 = ((2 : ℕ) : ZMod 2) by ring, CharP.cast_eq_zero]
        · have heven : Even (p - 1) := by
            obtain ⟨m, hm⟩ := Nat.odd_iff.mpr hodd
            exact ⟨m, by omega⟩
          rw [heven.neg_one_pow]
          ring
      have hdvd : (p : ℤ) ∣ (-1 : ℤ) ^ (p - 1) * ((p - 1).factorial : ℤ) + 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsign
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨m • (1 : W ℤ n), ?_⟩
      rw [sub_neg_eq_add]
      have hcpp : c p p = (-1 : ℤ) ^ (p - 1) * ((p - 1).factorial : ℤ) := by
        simp [c]
      rw [hcpp]
      have hm' := congrArg (Int.cast (R := W ℤ n)) hm
      simp only [zsmul_eq_mul, mul_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] at hm' ⊢
      exact hm'
    simpa using hfirst.add hlast
  obtain ⟨t, ht⟩ := hsum_p.mul_p
  refine ⟨t, ?_⟩
  simpa [Algebra.smul_def, zsmul_eq_mul] using ht

/-- Non-central lift of `P R n` into `W R n` via `expand p` and `ofMvPoly`. -/
noncomputable def centerLift (R : Type*) [CommRing R] (n p : ℕ) (f : P R n) : W R n :=
  ofMvPoly R n (MvPolynomial.expand p f)

lemma centerLift_C {R : Type*} [CommRing R] {n p : ℕ} (r : R) :
    centerLift R n p (MvPolynomial.C r) = algebraMap R (W R n) r := by
  simp only [centerLift, MvPolynomial.C_eq_smul_one, map_smul, Algebra.algebraMap_eq_smul_one]
  congr 1
  apply toMvPoly_injective R n
  rw [toMvPoly_ofMvPoly]
  simp [toMvPoly, toEnd]

lemma centerLift_X {R : Type*} [CommRing R] {n p : ℕ} (v : Fin n ⊕ Fin n) :
    centerLift R n p (X v) = WeylAlgebra.of R v ^ p := by
  apply toMvPoly_injective R n
  rw [centerLift, toMvPoly_ofMvPoly, MvPolynomial.expand_X]
  rcases v with i | i
  · have : toMvPoly R n (wx R i ^ p) = X (Sum.inl i) ^ p := by
      induction p with
      | zero => simp [toMvPoly, toEnd]
      | succ k ih =>
        rw [pow_succ', pow_succ']
        change toEnd R n (wx R i * wx R i ^ k) 1 = _
        rw [map_mul, Module.End.mul_apply]
        have hih : toEnd R n (wx R i ^ k) 1 = X (Sum.inl i) ^ k := ih
        rw [hih]
        simp [wx, toEnd]
    exact this.symm
  · have : toMvPoly R n (wy R i ^ p) = X (Sum.inr i) ^ p := by
      induction p with
      | zero => simp [toMvPoly, toEnd]
      | succ k ih =>
        rw [pow_succ', pow_succ']
        change toEnd R n (wy R i * wy R i ^ k) 1 = _
        rw [map_mul, Module.End.mul_apply]
        have hih : toEnd R n (wy R i ^ k) 1 = X (Sum.inr i) ^ k := ih
        rw [hih]
        simp only [wy, toEnd, weylLift_of, LinearMap.sub_apply, LinearMap.mulLeft_apply]
        have hp0 : pderiv (Sum.inl i) (X (Sum.inr i) ^ k : P R n) = 0 := by
          rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp), smul_zero, smul_zero]
        change X (Sum.inr i) * X (Sum.inr i) ^ k - pderiv (Sum.inl i) (X (Sum.inr i) ^ k) = _
        rw [hp0, sub_zero]
    exact this.symm

lemma centerLift_add {R : Type*} [CommRing R] {n p : ℕ} (f g : P R n) :
    centerLift R n p (f + g) = centerLift R n p f + centerLift R n p g := by
  simp [centerLift, map_add]

lemma centerLift_sub {R : Type*} [CommRing R] {n p : ℕ} (f g : P R n) :
    centerLift R n p (f - g) = centerLift R n p f - centerLift R n p g := by
  simp [centerLift, map_sub]

lemma centerLift_smul {R : Type*} [CommRing R] {n p : ℕ} (r : R) (f : P R n) :
    centerLift R n p (r • f) = r • centerLift R n p f := by
  simp [centerLift, map_smul]

lemma weylMap_centerLift {R S : Type*} [CommRing R] [CommRing S] {n p : ℕ}
    (g : R →+* S) (f : P R n) :
    weylMap g (centerLift R n p f) = centerLift S n p (MvPolynomial.map g f) := by
  apply toMvPoly_injective S n
  rw [toMvPoly_weylMap, centerLift, centerLift, toMvPoly_ofMvPoly, toMvPoly_ofMvPoly]
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | mul_X f v ih => simp [map_mul, ih, MvPolynomial.expand_X]

lemma centerLift_eq_centerEmb {K : Type*} [CommRing K] {n p : ℕ} [CharP K p] (f : P K n) :
    centerLift K n p f = centerEmb K n p f := by
  apply toMvPoly_injective K n
  rw [centerLift, toMvPoly_ofMvPoly, toMvPoly_centerEmb]

lemma wx_pow_p_central_mod_p {R : Type*} [CommRing R] {n p : ℕ} (i : Fin n) (w : W R n) :
    ModW p (wx R i ^ p * w) (w * wx R i ^ p) := by
  have hgen : ∀ v : Fin n ⊕ Fin n,
      ModW p (wx R i ^ p * WeylAlgebra.of R v) (WeylAlgebra.of R v * wx R i ^ p) := by
    intro v; rcases v with j | j
    · simp only [wx]
      rw [(Commute.pow_left (WeylAlgebra.of_inl_mul_comm R i j) p).eq]
      exact ModW.refl p _
    · by_cases hij : i = j
      · subst hij
        refine ⟨wx R i ^ (p - 1), ?_⟩
        change wx R i ^ p * wy R i - wy R i * wx R i ^ p = (p : R) • wx R i ^ (p - 1)
        rw [wx_pow_mul_wy]; abel
      · simp only [wx]
        rw [(Commute.pow_left (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij) p).eq]
        exact ModW.refl p _
  have hmul : ∀ a b : W R n, ModW p (wx R i ^ p * a) (a * wx R i ^ p) →
      ModW p (wx R i ^ p * b) (b * wx R i ^ p) →
      ModW p (wx R i ^ p * (a * b)) (a * b * wx R i ^ p) := by
    intro a b ha hb
    rw [← mul_assoc]
    exact (ha.mul_right b).trans (by rw [mul_assoc, mul_assoc]; exact hb.mul_left a)
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n w
  induction f using MvPolynomial.induction_on' with
  | monomial d s =>
    rw [ofMvPoly_monomial, mul_smul_comm, smul_mul_assoc]
    refine ModW.smul_scale s ?_
    have hpow : ∀ v k, ModW p (wx R i ^ p * WeylAlgebra.of R v ^ k) (WeylAlgebra.of R v ^ k * wx R i ^ p) := by
      intro v k; induction k with
      | zero => simp; exact ModW.refl p _
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hgen v)
    have hlist : ∀ (l : List (Fin n)) (v : Fin n → Fin n ⊕ Fin n) (e : Fin n → ℕ),
        ModW p (wx R i ^ p * (l.map (fun j => WeylAlgebra.of R (v j) ^ e j)).prod)
          ((l.map (fun j => WeylAlgebra.of R (v j) ^ e j)).prod * wx R i ^ p) := by
      intro l v e; induction l with
      | nil => simp; exact ModW.refl p _
      | cons j l ih => rw [List.map_cons, List.prod_cons]; exact hmul _ _ (hpow (v j) (e j)) ih
    exact hmul _ _ (hlist _ Sum.inl _) (hlist _ Sum.inr _)
  | add f g hf hg =>
    rw [map_add, mul_add, add_mul]
    exact hf.add hg

lemma wy_pow_p_central_mod_p {R : Type*} [CommRing R] {n p : ℕ} (i : Fin n) (w : W R n) :
    ModW p (wy R i ^ p * w) (w * wy R i ^ p) := by
  have hgen : ∀ v : Fin n ⊕ Fin n,
      ModW p (wy R i ^ p * WeylAlgebra.of R v) (WeylAlgebra.of R v * wy R i ^ p) := by
    intro v; rcases v with j | j
    · by_cases hij : j = i
      · subst hij
        refine ⟨-wy R j ^ (p - 1), ?_⟩
        change wy R j ^ p * wx R j - wx R j * wy R j ^ p = (p : R) • (-wy R j ^ (p - 1))
        rw [wx_mul_wy_pow, smul_neg]; abel
      · simp only [wy]
        rw [(Commute.pow_left (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij).symm p).eq]
        exact ModW.refl p _
    · simp only [wy]
      rw [(Commute.pow_left (WeylAlgebra.of_inr_mul_comm R i j) p).eq]
      exact ModW.refl p _
  have hmul : ∀ a b : W R n, ModW p (wy R i ^ p * a) (a * wy R i ^ p) →
      ModW p (wy R i ^ p * b) (b * wy R i ^ p) →
      ModW p (wy R i ^ p * (a * b)) (a * b * wy R i ^ p) := by
    intro a b ha hb
    rw [← mul_assoc]
    exact (ha.mul_right b).trans (by rw [mul_assoc, mul_assoc]; exact hb.mul_left a)
  obtain ⟨f, rfl⟩ := ofMvPoly_surjective R n w
  induction f using MvPolynomial.induction_on' with
  | monomial d s =>
    rw [ofMvPoly_monomial, mul_smul_comm, smul_mul_assoc]
    refine ModW.smul_scale s ?_
    have hpow : ∀ v k, ModW p (wy R i ^ p * WeylAlgebra.of R v ^ k) (WeylAlgebra.of R v ^ k * wy R i ^ p) := by
      intro v k; induction k with
      | zero => simp; exact ModW.refl p _
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hgen v)
    have hlist : ∀ (l : List (Fin n)) (v : Fin n → Fin n ⊕ Fin n) (e : Fin n → ℕ),
        ModW p (wy R i ^ p * (l.map (fun j => WeylAlgebra.of R (v j) ^ e j)).prod)
          ((l.map (fun j => WeylAlgebra.of R (v j) ^ e j)).prod * wy R i ^ p) := by
      intro l v e; induction l with
      | nil => simp; exact ModW.refl p _
      | cons j l ih => rw [List.map_cons, List.prod_cons]; exact hmul _ _ (hpow (v j) (e j)) ih
    exact hmul _ _ (hlist _ Sum.inl _) (hlist _ Sum.inr _)
  | add f g hf hg =>
    rw [map_add, mul_add, add_mul]
    exact hf.add hg

lemma centerLift_central_mod_p {R : Type*} [CommRing R] {n p : ℕ} (f : P R n) (w : W R n) :
    ModW p (centerLift R n p f * w) (w * centerLift R n p f) := by
  have hmul : ∀ a b : W R n, ModW p (a * w) (w * a) → ModW p (b * w) (w * b) →
      ModW p ((a * b) * w) (w * (a * b)) := by
    intro a b ha hb
    rw [mul_assoc]
    exact (hb.mul_left a).trans (by rw [← mul_assoc, ← mul_assoc]; exact ha.mul_right b)
  induction f using MvPolynomial.induction_on' with
  | monomial d s =>
    rw [centerLift, MvPolynomial.expand_monomial, ofMvPoly_monomial, smul_mul_assoc, mul_smul_comm]
    refine ModW.smul_scale s ?_
    have hpow_x : ∀ i k, ModW p ((wx R i ^ p) ^ k * w) (w * (wx R i ^ p) ^ k) := by
      intro i k; induction k with
      | zero => simp; exact ModW.refl p _
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih (wx_pow_p_central_mod_p i w)
    have hpow_y : ∀ i k, ModW p ((wy R i ^ p) ^ k * w) (w * (wy R i ^ p) ^ k) := by
      intro i k; induction k with
      | zero => simp; exact ModW.refl p _
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih (wy_pow_p_central_mod_p i w)
    have hlx : ∀ (l : List (Fin n)),
        ModW p ((l.map (fun i => wx R i ^ (p * d (Sum.inl i)))).prod * w)
          (w * (l.map (fun i => wx R i ^ (p * d (Sum.inl i)))).prod) := by
      intro l; induction l with
      | nil => simp; exact ModW.refl p _
      | cons i l ih => rw [List.map_cons, List.prod_cons, pow_mul]; exact hmul _ _ (hpow_x i _) ih
    have hly : ∀ (l : List (Fin n)),
        ModW p ((l.map (fun i => wy R i ^ (p * d (Sum.inr i)))).prod * w)
          (w * (l.map (fun i => wy R i ^ (p * d (Sum.inr i)))).prod) := by
      intro l; induction l with
      | nil => simp; exact ModW.refl p _
      | cons i l ih => rw [List.map_cons, List.prod_cons, pow_mul]; exact hmul _ _ (hpow_y i _) ih
    exact hmul _ _ (hlx (List.finRange n)) (hly (List.finRange n))
  | add f g hf hg =>
    rw [centerLift_add, add_mul, mul_add]
    exact hf.add hg

lemma centerLift_mul_mod_p {R : Type*} [CommRing R] {n p : ℕ} (f g : P R n) :
    ModW p (centerLift R n p (f * g)) (centerLift R n p f * centerLift R n p g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d₁ s₁ =>
    induction g using MvPolynomial.induction_on' with
    | monomial d₂ s₂ =>
      rw [MvPolynomial.monomial_mul, centerLift, centerLift, centerLift,
        MvPolynomial.expand_monomial, MvPolynomial.expand_monomial, MvPolynomial.expand_monomial,
        ofMvPoly_monomial, ofMvPoly_monomial, ofMvPoly_monomial,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      refine ModW.smul_scale (s₁ * s₂) ?_
      rw [weylMonom, weylMonom, weylMonom, mul_assoc]
      -- Commute `wyProd (p • d₁)` past `wxProd (p • d₂)` mod `p`
      have hwy_cent : ModW p (wyProd R (fun i => (p • d₁) (Sum.inr i)) * wxProd R (fun i => (p • d₂) (Sum.inl i)))
          (wxProd R (fun i => (p • d₂) (Sum.inl i)) * wyProd R (fun i => (p • d₁) (Sum.inr i))) := by
        let e₁ : (Fin n ⊕ Fin n) →₀ ℕ :=
          Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ => 0) (fun i => d₁ (Sum.inr i)))
        have h := centerLift_central_mod_p (R := R) (p := p)
          (monomial e₁ (1 : R)) (wxProd R (fun i => (p • d₂) (Sum.inl i)))
        have heq : centerLift R n p (monomial e₁ (1 : R)) =
            wyProd R (fun i => (p • d₁) (Sum.inr i)) := by
          rw [centerLift, MvPolynomial.expand_monomial, ofMvPoly_monomial, one_smul, weylMonom]
          have hx1 : wxProd R (fun i => (p • e₁) (Sum.inl i)) = 1 := by
            have h0 : ∀ (l : List (Fin n)), (l.map (fun i => wx R i ^ 0)).prod = 1 := by
              intro l; induction l with | nil => rfl | cons i l ih => simp [ih]
            exact h0 (List.finRange n)
          rw [hx1, one_mul]; rfl
        rwa [heq] at h
      have hwx_mul : ∀ (e₁ e₂ : Fin n → ℕ), wxProd R e₁ * wxProd R e₂ = wxProd R (fun i => e₁ i + e₂ i) := by
        intro e₁ e₂
        have haux : ∀ (l : List (Fin n)), l.Nodup →
            (l.map (fun i => wx R i ^ e₁ i)).prod * (l.map (fun i => wx R i ^ e₂ i)).prod =
              (l.map (fun i => wx R i ^ (e₁ i + e₂ i))).prod := by
          intro l; induction l with
          | nil => simp
          | cons i l ih =>
            intro hnd; rw [List.nodup_cons] at hnd
            simp only [List.map_cons, List.prod_cons]
            have hc : (l.map (fun j => wx R j ^ e₁ j)).prod * wx R i ^ e₂ i =
                wx R i ^ e₂ i * (l.map (fun j => wx R j ^ e₁ j)).prod := by
              clear ih hnd; induction l with
              | nil => simp
              | cons j l' ihl =>
                simp only [List.map_cons, List.prod_cons]
                have h1 : wx R j ^ e₁ j * wx R i ^ e₂ i = wx R i ^ e₂ i * wx R j ^ e₁ j :=
                  (Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inl_mul_comm R j i) _) _).eq
                rw [mul_assoc, ihl, ← mul_assoc, h1, mul_assoc]
            rw [mul_assoc, ← mul_assoc (l.map _).prod, hc, mul_assoc, ih hnd.2, ← mul_assoc, ← pow_add]
        exact haux (List.finRange n) (List.nodup_finRange n)
      have hwy_mul : ∀ (e₁ e₂ : Fin n → ℕ), wyProd R e₁ * wyProd R e₂ = wyProd R (fun i => e₁ i + e₂ i) := by
        intro e₁ e₂
        have haux : ∀ (l : List (Fin n)), l.Nodup →
            (l.map (fun i => wy R i ^ e₁ i)).prod * (l.map (fun i => wy R i ^ e₂ i)).prod =
              (l.map (fun i => wy R i ^ (e₁ i + e₂ i))).prod := by
          intro l; induction l with
          | nil => simp
          | cons i l ih =>
            intro hnd; rw [List.nodup_cons] at hnd
            simp only [List.map_cons, List.prod_cons]
            have hc : (l.map (fun j => wy R j ^ e₁ j)).prod * wy R i ^ e₂ i =
                wy R i ^ e₂ i * (l.map (fun j => wy R j ^ e₁ j)).prod := by
              clear ih hnd; induction l with
              | nil => simp
              | cons j l' ihl =>
                simp only [List.map_cons, List.prod_cons]
                have h1 : wy R j ^ e₁ j * wy R i ^ e₂ i = wy R i ^ e₂ i * wy R j ^ e₁ j :=
                  (Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inr_mul_comm R j i) _) _).eq
                rw [mul_assoc, ihl, ← mul_assoc, h1, mul_assoc]
            rw [mul_assoc, ← mul_assoc (l.map _).prod, hc, mul_assoc, ih hnd.2, ← mul_assoc, ← pow_add]
        exact haux (List.finRange n) (List.nodup_finRange n)
      have hstep1 : ModW p
          (wxProd R (fun i => (p • d₁) (Sum.inl i)) * (wyProd R (fun i => (p • d₁) (Sum.inr i)) *
            (wxProd R (fun i => (p • d₂) (Sum.inl i)) * wyProd R (fun i => (p • d₂) (Sum.inr i)))))
          (wxProd R (fun i => (p • d₁) (Sum.inl i)) * ((wxProd R (fun i => (p • d₂) (Sum.inl i)) *
            wyProd R (fun i => (p • d₁) (Sum.inr i))) * wyProd R (fun i => (p • d₂) (Sum.inr i)))) := by
        rw [← mul_assoc (wyProd R _)]
        exact (hwy_cent.mul_right _).mul_left _
      have hstep2 : wxProd R (fun i => (p • d₁) (Sum.inl i)) *
          ((wxProd R (fun i => (p • d₂) (Sum.inl i)) * wyProd R (fun i => (p • d₁) (Sum.inr i))) *
            wyProd R (fun i => (p • d₂) (Sum.inr i))) =
          wxProd R (fun i => (p • (d₁ + d₂)) (Sum.inl i)) * wyProd R (fun i => (p • (d₁ + d₂)) (Sum.inr i)) := by
        rw [← mul_assoc, ← mul_assoc, mul_assoc (wxProd R _ * wxProd R _), hwx_mul, hwy_mul]
        congr 1 <;> congr 1 <;> funext i <;> simp [mul_add]
      rw [hstep2] at hstep1
      exact hstep1.symm
    | add g₁ g₂ hg₁ hg₂ =>
      rw [mul_add, centerLift_add, centerLift_add, mul_add]
      exact hg₁.add hg₂
  | add f₁ f₂ hf₁ hf₂ =>
    rw [add_mul, centerLift_add, centerLift_add, add_mul]
    exact hf₁.add hf₂

/-- Commutator invariance mod `p^2` under mod-`p` perturbations of mod-`p`-central elements. -/
lemma comm_mod_p_sq_of_mod_p {R : Type*} [CommRing R] {n p : ℕ} {a a' b b' : W R n}
    (ha : ModW p a' a) (hb : ModW p b' b)
    (hac : ∀ w, ModW p (a * w) (w * a)) (hbc : ∀ w, ModW p (b * w) (w * b)) :
    ModW (p * p) (a' * b' - b' * a') (a * b - b * a) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have ha' : a' = a + (p : R) • u := eq_add_of_sub_eq' hu
  have hb' : b' = b + (p : R) • v := eq_add_of_sub_eq' hv
  obtain ⟨t1, ht1⟩ := hac v
  obtain ⟨t2, ht2⟩ := (hbc u).symm
  refine ⟨t1 + t2 + (u * v - v * u), ?_⟩
  rw [ha', hb']
  have hexpand : (a + (p : R) • u) * (b + (p : R) • v) - (b + (p : R) • v) * (a + (p : R) • u) -
      (a * b - b * a) =
      (p : R) • (a * v - v * a) + (p : R) • (u * b - b * u) +
        ((p * p : ℕ) : R) • (u * v - v * u) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, smul_sub,
      Nat.cast_mul]
    abel
  rw [hexpand, ht1, ht2, smul_smul, smul_smul, ← Nat.cast_mul, smul_add, smul_add]

lemma pb_C_right {R : Type*} [CommRing R] {n : ℕ} (f : P R n) (r : R) :
    MvPolynomial.poissonBracket f (MvPolynomial.C r) = 0 := by
  simp [MvPolynomial.poissonBracket]

lemma pb_C_left {R : Type*} [CommRing R] {n : ℕ} (r : R) (g : P R n) :
    MvPolynomial.poissonBracket (MvPolynomial.C r) g = 0 := by
  simp [MvPolynomial.poissonBracket]

lemma pb_add_right {R : Type*} [CommRing R] {n : ℕ} (f g₁ g₂ : P R n) :
    MvPolynomial.poissonBracket f (g₁ + g₂) =
      MvPolynomial.poissonBracket f g₁ + MvPolynomial.poissonBracket f g₂ := by
  simp only [MvPolynomial.poissonBracket, map_add, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma pb_add_left {R : Type*} [CommRing R] {n : ℕ} (f₁ f₂ g : P R n) :
    MvPolynomial.poissonBracket (f₁ + f₂) g =
      MvPolynomial.poissonBracket f₁ g + MvPolynomial.poissonBracket f₂ g := by
  simp only [MvPolynomial.poissonBracket, map_add, add_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma pb_mul_right {R : Type*} [CommRing R] {n : ℕ} (f g₁ g₂ : P R n) :
    MvPolynomial.poissonBracket f (g₁ * g₂) =
      g₁ * MvPolynomial.poissonBracket f g₂ + MvPolynomial.poissonBracket f g₁ * g₂ := by
  simp only [MvPolynomial.poissonBracket, Derivation.leibniz, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma pb_mul_left {R : Type*} [CommRing R] {n : ℕ} (f₁ f₂ g : P R n) :
    MvPolynomial.poissonBracket (f₁ * f₂) g =
      f₁ * MvPolynomial.poissonBracket f₂ g + MvPolynomial.poissonBracket f₁ g * f₂ := by
  simp only [MvPolynomial.poissonBracket, Derivation.leibniz, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Master mod-`p^2` bracket identity: `[centerLift F, centerLift G] ≡ -p • centerLift {F, G} (mod p^2)`. -/
lemma centerLift_comm_mod_p_sq {R : Type*} [CommRing R] {n p : ℕ} (hp : p.Prime)
    (F G : P R n) :
    ModW (p * p) (centerLift R n p F * centerLift R n p G - centerLift R n p G * centerLift R n p F)
      (-((p : R) • centerLift R n p (MvPolynomial.poissonBracket F G))) := by
  -- First prove for `F = X v` and `G = X w`
  have hgen : ∀ v w : Fin n ⊕ Fin n,
      ModW (p * p) (centerLift R n p (X v) * centerLift R n p (X w) -
          centerLift R n p (X w) * centerLift R n p (X v))
        (-((p : R) • centerLift R n p (MvPolynomial.poissonBracket (X v) (X w)))) := by
    intro v w
    rw [centerLift_X, centerLift_X]
    rcases v with i | i <;> rcases w with j | j
    · rw [MvPolynomial.poissonBracket_X_inl_inl]
      have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
      rw [this, smul_zero, neg_zero]
      rw [(Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inl_mul_comm R i j) p) p).eq, sub_self]
      exact ModW.refl _ _
    · by_cases hij : i = j
      · subst hij
        rw [MvPolynomial.poissonBracket_X_inl_inr, if_pos rfl]
        have h1 : centerLift R n p (1 : P R n) = 1 := by
          rw [← map_one MvPolynomial.C, centerLift_C, map_one]
        rw [h1]
        exact wx_pow_p_comm_wy_pow_p_mod_p_sq hp i
      · rw [MvPolynomial.poissonBracket_X_inl_inr, if_neg hij]
        have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
        rw [this, smul_zero, neg_zero]
        rw [(Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij) p) p).eq, sub_self]
        exact ModW.refl _ _
    · rw [MvPolynomial.poissonBracket_swap, MvPolynomial.poissonBracket_X_inl_inr]
      by_cases hij : j = i
      · subst hij
        rw [if_pos rfl]
        have h1 : centerLift R n p (-1 : P R n) = -1 := by
          rw [← map_one MvPolynomial.C, ← map_neg, centerLift_C, map_neg, map_one]
        rw [h1, smul_neg, neg_neg]
        obtain ⟨t, ht⟩ := wx_pow_p_comm_wy_pow_p_mod_p_sq (R := R) hp j
        refine ⟨-t, ?_⟩
        rw [smul_neg, ← ht]
        simp only [wx, wy]; abel
      · rw [if_neg hij, neg_zero]
        have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
        rw [this, smul_zero, neg_zero]
        rw [(Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inl_mul_of_inr_of_ne R hij).symm p) p).eq, sub_self]
        exact ModW.refl _ _
    · rw [MvPolynomial.poissonBracket_X_inr_inr]
      have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
      rw [this, smul_zero, neg_zero]
      rw [(Commute.pow_right (Commute.pow_left (WeylAlgebra.of_inr_mul_comm R i j) p) p).eq, sub_self]
      exact ModW.refl _ _
  -- Step 2: Fix `v`, induct on `G`
  have hX : ∀ (v : Fin n ⊕ Fin n) (G : P R n),
      ModW (p * p) (centerLift R n p (X v) * centerLift R n p G -
          centerLift R n p G * centerLift R n p (X v))
        (-((p : R) • centerLift R n p (MvPolynomial.poissonBracket (X v) G))) := by
    intro v G
    induction G using MvPolynomial.induction_on with
    | C r =>
      rw [centerLift_C, Algebra.commutes, sub_self, pb_C_right]
      have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
      rw [this, smul_zero, neg_zero]; exact ModW.refl _ _
    | add G₁ G₂ h₁ h₂ =>
      rw [centerLift_add, mul_add, add_mul, pb_add_right, centerLift_add,
        smul_add, neg_add]
      have : centerLift R n p (X v) * centerLift R n p G₁ + centerLift R n p (X v) * centerLift R n p G₂ -
          (centerLift R n p G₁ * centerLift R n p (X v) + centerLift R n p G₂ * centerLift R n p (X v)) =
          (centerLift R n p (X v) * centerLift R n p G₁ - centerLift R n p G₁ * centerLift R n p (X v)) +
          (centerLift R n p (X v) * centerLift R n p G₂ - centerLift R n p G₂ * centerLift R n p (X v)) := by abel
      rw [this]; exact h₁.add h₂
    | mul_X G w ih =>
      have hcent_prod : ∀ u, ModW p ((centerLift R n p G * centerLift R n p (X w)) * u)
          (u * (centerLift R n p G * centerLift R n p (X w))) := fun u => by
        rw [mul_assoc]
        exact ((centerLift_central_mod_p (X w) u).mul_left _).trans
          (by rw [← mul_assoc, ← mul_assoc]; exact (centerLift_central_mod_p G u).mul_right _)
      have h1' := comm_mod_p_sq_of_mod_p (ModW.refl p (centerLift R n p (X v)))
        (centerLift_mul_mod_p G (X w))
        (centerLift_central_mod_p (X v)) hcent_prod
      refine h1'.trans ?_
      have hleib : centerLift R n p (X v) * (centerLift R n p G * centerLift R n p (X w)) -
          centerLift R n p G * centerLift R n p (X w) * centerLift R n p (X v) =
          centerLift R n p G * (centerLift R n p (X v) * centerLift R n p (X w) -
            centerLift R n p (X w) * centerLift R n p (X v)) +
          (centerLift R n p (X v) * centerLift R n p G -
            centerLift R n p G * centerLift R n p (X v)) * centerLift R n p (X w) := by
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
      rw [hleib]
      have h2 := ((hgen v w).mul_left (centerLift R n p G)).add (ih.mul_right (centerLift R n p (X w)))
      refine h2.trans ?_
      rw [pb_mul_right, centerLift_add, smul_add, neg_add,
        mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
      have h3 := (centerLift_mul_mod_p (p := p) G (MvPolynomial.poissonBracket (X v) (X w))).symm.mul_p
      have h4 := (centerLift_mul_mod_p (p := p) (MvPolynomial.poissonBracket (X v) G) (X w)).symm.mul_p
      have h3' : ModW (p * p) (-((p : R) • (centerLift R n p G * centerLift R n p (MvPolynomial.poissonBracket (X v) (X w)))))
          (-((p : R) • centerLift R n p (G * MvPolynomial.poissonBracket (X v) (X w)))) := by
        obtain ⟨t, ht⟩ := h3
        exact ⟨-t, by rw [smul_neg, ← ht]; abel⟩
      have h4' : ModW (p * p) (-((p : R) • (centerLift R n p (MvPolynomial.poissonBracket (X v) G) * centerLift R n p (X w))))
          (-((p : R) • centerLift R n p (MvPolynomial.poissonBracket (X v) G * X w))) := by
        obtain ⟨t, ht⟩ := h4
        exact ⟨-t, by rw [smul_neg, ← ht]; abel⟩
      exact h3'.add h4'
  -- Step 3: Induct on `F` for fixed `G`
  induction F using MvPolynomial.induction_on with
  | C r =>
    rw [centerLift_C, Algebra.commutes, sub_self, pb_C_left]
    have : centerLift R n p (0 : P R n) = 0 := by simp [centerLift]
    rw [this, smul_zero, neg_zero]; exact ModW.refl _ _
  | add F₁ F₂ h₁ h₂ =>
    rw [centerLift_add, add_mul, mul_add, pb_add_left, centerLift_add,
      smul_add, neg_add]
    have : (centerLift R n p F₁ * centerLift R n p G + centerLift R n p F₂ * centerLift R n p G) -
        (centerLift R n p G * centerLift R n p F₁ + centerLift R n p G * centerLift R n p F₂) =
        (centerLift R n p F₁ * centerLift R n p G - centerLift R n p G * centerLift R n p F₁) +
        (centerLift R n p F₂ * centerLift R n p G - centerLift R n p G * centerLift R n p F₂) := by abel
    rw [this]; exact h₁.add h₂
  | mul_X F v ih =>
    have hcent_prod : ∀ u, ModW p ((centerLift R n p F * centerLift R n p (X v)) * u)
        (u * (centerLift R n p F * centerLift R n p (X v))) := fun u => by
      rw [mul_assoc]
      exact ((centerLift_central_mod_p (X v) u).mul_left _).trans
        (by rw [← mul_assoc, ← mul_assoc]; exact (centerLift_central_mod_p F u).mul_right _)
    have h1 := comm_mod_p_sq_of_mod_p (centerLift_mul_mod_p F (X v))
      (ModW.refl p (centerLift R n p G)) hcent_prod (centerLift_central_mod_p G)
    refine h1.trans ?_
    have hleib : centerLift R n p F * centerLift R n p (X v) * centerLift R n p G -
        centerLift R n p G * (centerLift R n p F * centerLift R n p (X v)) =
        centerLift R n p F * (centerLift R n p (X v) * centerLift R n p G -
          centerLift R n p G * centerLift R n p (X v)) +
        (centerLift R n p F * centerLift R n p G -
          centerLift R n p G * centerLift R n p F) * centerLift R n p (X v) := by
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    rw [hleib]
    have h2 := ((hX v G).mul_left (centerLift R n p F)).add (ih.mul_right (centerLift R n p (X v)))
    refine h2.trans ?_
    rw [pb_mul_left, centerLift_add, smul_add, neg_add,
      mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
    have h3 := (centerLift_mul_mod_p (p := p) F (MvPolynomial.poissonBracket (X v) G)).symm.mul_p
    have h4 := (centerLift_mul_mod_p (p := p) (MvPolynomial.poissonBracket F G) (X v)).symm.mul_p
    have h3' : ModW (p * p) (-((p : R) • (centerLift R n p F * centerLift R n p (MvPolynomial.poissonBracket (X v) G))))
        (-((p : R) • centerLift R n p (F * MvPolynomial.poissonBracket (X v) G))) := by
      obtain ⟨t, ht⟩ := h3
      exact ⟨-t, by rw [smul_neg, ← ht]; abel⟩
    have h4' : ModW (p * p) (-((p : R) • (centerLift R n p (MvPolynomial.poissonBracket F G) * centerLift R n p (X v))))
        (-((p : R) • centerLift R n p (MvPolynomial.poissonBracket F G * X v))) := by
      obtain ⟨t, ht⟩ := h4
      exact ⟨-t, by rw [smul_neg, ← ht]; abel⟩
    exact h3'.add h4'

lemma map_poissonBracket {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (f₁ f₂ : P R n) :
    MvPolynomial.map g (MvPolynomial.poissonBracket f₁ f₂) =
      MvPolynomial.poissonBracket (MvPolynomial.map g f₁) (MvPolynomial.map g f₂) := by
  simp only [MvPolynomial.poissonBracket, map_sum, map_sub, map_mul, MvPolynomial.pderiv_map]

/-- If `φ_S : W S n →ₐ[S] W S n` lifts `φ₀` modulo `p` over a `p`-torsion-free ring `S`,
then the induced polynomial endomorphism `φ₀` over any char-`p` field quotient `π : S →+* K`
is a Poisson endomorphism! -/
lemma isPoissonEndomorphism_of_lift {S K : Type*} [CommRing S] [Field K] {n p : ℕ}
    [CharP K p] (hp : p.Prime)
    (hp_nt : ∀ s : S, (p : S) * s = 0 → s = 0)
    (φ_S : W S n →ₐ[S] W S n) (π : S →+* K)
    (F : (Fin n ⊕ Fin n) → P S n)
    (hlift : ∀ v : Fin n ⊕ Fin n, ModW p (φ_S (WeylAlgebra.of S v ^ p)) (centerLift S n p (F v))) :
    IsPoissonEndomorphism (MvPolynomial.aeval (fun v => MvPolynomial.map π (F v)) : P K n →ₐ[K] P K n) := by
  intro v w
  simp only [MvPolynomial.aeval_X]
  -- Step 1: `φ_S ([X_v^p, X_w^p]) ≡ -p • centerLift {X_v, X_w} (mod p^2)`
  have h1 : ModW (p * p) (φ_S (WeylAlgebra.of S v ^ p) * φ_S (WeylAlgebra.of S w ^ p) -
      φ_S (WeylAlgebra.of S w ^ p) * φ_S (WeylAlgebra.of S v ^ p))
      (-((p : S) • centerLift S n p (MvPolynomial.poissonBracket (X v) (X w)))) := by
    have hvw := centerLift_comm_mod_p_sq (R := S) hp (X v) (X w)
    rw [centerLift_X, centerLift_X] at hvw
    obtain ⟨t, ht⟩ := hvw
    refine ⟨φ_S t, ?_⟩
    have hφ := congrArg φ_S ht
    simp only [map_sub, map_mul, map_neg, map_smul] at hφ
    have hfix : φ_S (centerLift S n p (MvPolynomial.poissonBracket (X v) (X w))) =
        centerLift S n p (MvPolynomial.poissonBracket (X v) (X w)) := by
      rcases v with i | i <;> rcases w with j | j
      · simp [MvPolynomial.poissonBracket_X_inl_inl, centerLift]
      · rw [MvPolynomial.poissonBracket_X_inl_inr]
        split_ifs
        · rw [← map_one MvPolynomial.C, centerLift_C, AlgHom.commutes]
        · simp [centerLift]
      · rw [MvPolynomial.poissonBracket_swap, MvPolynomial.poissonBracket_X_inl_inr]
        split_ifs
        · rw [← map_one MvPolynomial.C, ← map_neg, centerLift_C, AlgHom.commutes]
        · simp [centerLift]
      · simp [MvPolynomial.poissonBracket_X_inr_inr, centerLift]
    rwa [hfix] at hφ
  -- Step 2: `[φ_S (X_v^p), φ_S (X_w^p)] ≡ -p • centerLift {F v, F w} (mod p^2)`
  have h2 : ModW (p * p) (φ_S (WeylAlgebra.of S v ^ p) * φ_S (WeylAlgebra.of S w ^ p) -
      φ_S (WeylAlgebra.of S w ^ p) * φ_S (WeylAlgebra.of S v ^ p))
      (-((p : S) • centerLift S n p (MvPolynomial.poissonBracket (F v) (F w)))) :=
    (comm_mod_p_sq_of_mod_p (hlift v) (hlift w)
      (centerLift_central_mod_p (F v)) (centerLift_central_mod_p (F w))).trans
      (centerLift_comm_mod_p_sq hp (F v) (F w))
  -- Step 3: Subtract, cancel `p` using `hp_nt`, and apply `weylMap π`
  have hdiff : ModW (p * p) ((p : S) • centerLift S n p (MvPolynomial.poissonBracket (F v) (F w)))
      ((p : S) • centerLift S n p (MvPolynomial.poissonBracket (X v) (X w))) := by
    obtain ⟨t, ht⟩ := h1.symm.trans h2
    exact ⟨t, by rw [← ht]; abel⟩
  obtain ⟨t, ht⟩ := hdiff
  have hcancel : centerLift S n p (MvPolynomial.poissonBracket (F v) (F w) -
      MvPolynomial.poissonBracket (X v) (X w)) = (p : S) • t := by
    apply toMvPoly_injective S n
    ext d
    have hmul : (p : S) * (toMvPoly S n (centerLift S n p (MvPolynomial.poissonBracket (F v) (F w) -
        MvPolynomial.poissonBracket (X v) (X w)) - (p : S) • t)).coeff d = 0 := by
      rw [← smul_eq_mul, ← MvPolynomial.coeff_smul, ← map_smul, smul_sub, smul_smul, ← Nat.cast_mul,
        centerLift_sub, smul_sub, ht, sub_self, map_zero, MvPolynomial.coeff_zero]
    have h0 := hp_nt _ hmul
    rw [map_sub, MvPolynomial.coeff_sub, sub_eq_zero] at h0
    exact h0
  have hmap := congrArg (weylMap π) hcancel
  rw [weylMap_centerLift, centerLift_eq_centerEmb, Algebra.smul_def, map_mul, weylMap_algebraMap,
    map_natCast, CharP.cast_eq_zero, map_zero, zero_mul] at hmap
  have hpoly : MvPolynomial.map π (MvPolynomial.poissonBracket (F v) (F w) -
      MvPolynomial.poissonBracket (X v) (X w)) = 0 :=
    centerEmb_injective K n p hp.pos (by rwa [map_zero])
  rw [map_sub, sub_eq_zero, map_poissonBracket, map_poissonBracket, MvPolynomial.map_X,
    MvPolynomial.map_X] at hpoly
  exact hpoly

end PoissonModP2

/- Module 5: Number-field specialization, ultraproduct, and proof of `poisson_implication` -/

section UltraproductProof

/-- Finset of all multi-indices in `Fin n ⊕ Fin n` of total degree `≤ D`. -/
noncomputable def monLeFinset (n D : ℕ) : Finset ((Fin n ⊕ Fin n) →₀ ℕ) :=
  ((Fintype.piFinset (fun _ : Fin n ⊕ Fin n => Finset.range (D + 1))).image
    Finsupp.equivFunOnFinite.symm).filter (fun e => e.sum (fun _ m => m) ≤ D)

lemma mem_monLeFinset_iff {n D : ℕ} {e : (Fin n ⊕ Fin n) →₀ ℕ} :
    e ∈ monLeFinset n D ↔ e.sum (fun _ m => m) ≤ D := by
  simp only [monLeFinset, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro hle
  refine ⟨fun v => e v, fun v => ?_, ?_⟩
  · have hv : e v ≤ e.sum (fun _ m => m) := by
      by_cases hmem : v ∈ e.support
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      · rw [Finsupp.notMem_support_iff.mp hmem]; exact Nat.zero_le _
    exact Nat.lt_succ_of_le (le_trans hv hle)
  · ext v; rfl

lemma support_subset_monLeFinset {R : Type*} [CommRing R] {n D : ℕ} {f : P R n}
    (hdeg : f.totalDegree ≤ D) : f.support ⊆ monLeFinset n D := by
  intro e he
  rw [mem_monLeFinset_iff]
  exact le_trans (MvPolynomial.le_totalDegree he) hdeg

/-- Every polynomial `f` of total degree `≤ D` is a sum over `monLeFinset n D`. -/
lemma poly_eq_sum_monLeFinset {R : Type*} [CommRing R] {n D : ℕ} {f : P R n}
    (hdeg : f.totalDegree ≤ D) :
    f = ∑ e ∈ monLeFinset n D, monomial e (f.coeff e) := by
  conv_lhs => rw [f.as_sum]
  exact Finset.sum_subset (support_subset_monLeFinset hdeg) fun e _ hne => by
    rw [MvPolynomial.notMem_support_iff.mp hne, map_zero]

/-- If `v₀` is not in the range of `φ : W L n →ₐ[L] W L n` (lifted to `φ_R : W R n →ₐ[R] W R n`
for a subring `R ⊆ L`), then for each degree `D` there is a nonzero witness `w ∈ R` such that
under ANY ring hom `π : R →+* F` into a field `F` with `π w ≠ 0`, `of F v₀` is not in the
image of elements of degree `≤ D` under `weylAlgHom_baseChange π φ_R`. -/
lemma exists_nonSurj_witness {L : Type*} [Field L] {n : ℕ} (R : Subring L)
    (φ_R : W R n →ₐ[R] W R n) (v₀ : Fin n ⊕ Fin n)
    (hnot : WeylAlgebra.of L v₀ ∉ Set.range (weylAlgHom_baseChange R.subtype φ_R)) (D : ℕ) :
    ∃ w : R, w ≠ 0 ∧ ∀ (F : Type*) [Field F] (π : R →+* F) (_ : π w ≠ 0) (a : W F n),
      (toMvPoly F n a).totalDegree ≤ D →
      weylAlgHom_baseChange π φ_R a ≠ WeylAlgebra.of F v₀ := by
  let E : Finset ((Fin n ⊕ Fin n) →₀ ℕ) :=
    insert (Finsupp.single v₀ 1)
      ((monLeFinset n D).biUnion fun e => (toMvPoly R n (φ_R (weylMonom R e))).support)
  let A : Matrix E (monLeFinset n D) R :=
    fun m e => (toMvPoly R n (φ_R (weylMonom R e.val))).coeff m.val
  let m₀ : E := ⟨Finsupp.single v₀ 1, Finset.mem_insert_self _ _⟩
  let b : E → R := fun m => if m = m₀ then 1 else 0
  -- Over `K₀ := FractionRing R`, `b_{K₀}` is not in the range of `A_{K₀}.mulVecLin`
  let K₀ := FractionRing R
  let ιK : R →+* K₀ := algebraMap R K₀
  let embL : K₀ →+* L := IsFractionRing.lift (g := R.subtype) Subtype.val_injective
  have hemb_comp : ∀ r : R, embL (ιK r) = (r : L) := fun r =>
    IsFractionRing.lift_algebraMap Subtype.val_injective r
  let AK : Matrix E (monLeFinset n D) K₀ := A.map ιK
  let bK : E → K₀ := fun m => ιK (b m)
  have hbK_not_mem : bK ∉ LinearMap.range AK.mulVecLin := by
    rintro ⟨x, hx⟩
    apply hnot
    let a : W L n := ∑ e : monLeFinset n D, (embL (x e)) • weylMonom L e.val
    refine ⟨a, ?_⟩
    apply toMvPoly_injective L n
    have hLHS : toMvPoly L n (weylAlgHom_baseChange R.subtype φ_R a) =
        ∑ e : monLeFinset n D, (embL (x e)) •
          MvPolynomial.map R.subtype (toMvPoly R n (φ_R (weylMonom R e.val))) := by
      simp only [a, map_sum, map_smul]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      have hw : weylMonom L e.val = weylMap R.subtype (weylMonom R e.val) := by
        apply toMvPoly_injective L n
        rw [toMvPoly_weylMap, toMvPoly_weylMonom, toMvPoly_weylMonom, MvPolynomial.map_monomial,
          RingHom.map_one]
      rw [hw, weylAlgHom_baseChange_weylMap, toMvPoly_weylMap]
    have hRHS : toMvPoly L n (WeylAlgebra.of L v₀) = monomial (Finsupp.single v₀ 1) (1 : L) := by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
      rcases v₀ with i | i
      · simp [toMvPoly, toEnd]
      · simp [toMvPoly, toEnd]
    rw [hLHS, hRHS]
    ext d
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    by_cases hd : d ∈ E
    · have hdm : (∑ e : monLeFinset n D, (embL (x e) • MvPolynomial.map R.subtype
          (toMvPoly R n (φ_R (weylMonom R e.val)))).coeff d) =
          embL ((AK.mulVecLin x) ⟨d, hd⟩) := by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, AK,
          Matrix.map_apply, A, MvPolynomial.coeff_smul, MvPolynomial.coeff_map,
          smul_eq_mul, Subring.coe_subtype]
        refine Finset.sum_congr rfl fun e _ => ?_
        change embL (x e) * (A ⟨d, hd⟩ e : L) = embL (ιK (A ⟨d, hd⟩ e)) * embL (x e)
        rw [hemb_comp, mul_comm]
      rw [hdm, hx]
      simp only [bK, hemb_comp, b, Subtype.mk.injEq, m₀]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    · rw [if_neg (fun h : Finsupp.single v₀ 1 = d => hd (h ▸ Finset.mem_insert_self _ _))]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
      have hnot_supp : d ∉ (toMvPoly R n (φ_R (weylMonom R e.val))).support := fun hs =>
        hd (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨e.val, e.prop, hs⟩))
      rw [MvPolynomial.notMem_support_iff.mp hnot_supp, map_zero, smul_zero]
  -- Pick a linear functional `uK : (E → K₀) →ₗ[K₀] K₀` vanishing on `range AK.mulVecLin` with `uK bK ≠ 0`
  obtain ⟨uK, huK_b, huK_ker⟩ := Submodule.exists_le_ker_of_notMem hbK_not_mem
  let vK : E → K₀ := fun m => uK (Pi.single m 1)
  have hvK_orth : ∀ e : monLeFinset n D, ∑ m : E, vK m * AK m e = 0 := by
    intro e
    have hmem : AK.mulVecLin (Pi.single e 1) ∈ LinearMap.range AK.mulVecLin := ⟨Pi.single e 1, rfl⟩
    have h0 := huK_ker hmem
    rw [LinearMap.mem_ker] at h0
    have hvec : AK.mulVecLin (Pi.single e 1) = ∑ m : E, AK m e • Pi.single m (1 : K₀) := by
      funext m
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
    rw [hvec, map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    convert h0 using 1
    refine Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hvK_m0 : vK m₀ ≠ 0 := by
    have hb_eq : bK = Pi.single m₀ (1 : K₀) := by
      funext m; by_cases h : m = m₀ <;> simp [bK, b, h, Pi.single_apply]
    rwa [hb_eq] at huK_b
  -- Clear denominators of `vK : E → K₀` in `R`
  have hclear : ∀ m : E, ∃ (num : R) (den : R), den ≠ 0 ∧ ιK num = vK m * ιK den := by
    intro m
    obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) (vK m)
    refine ⟨num, den.val, nonZeroDivisors.ne_zero den.prop, hnd.symm⟩
  choose num den hden_ne hden_eq using hclear
  let denom : R := ∏ m : E, den m
  have hdenom_ne : denom ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hden_ne m
  let uR : E → R := fun m => num m * ∏ m' ∈ Finset.univ.erase m, den m'
  have huR_eq : ∀ m : E, ιK (uR m) = vK m * ιK denom := by
    intro m
    simp only [uR, denom, map_mul, hden_eq m]
    rw [mul_assoc, ← map_mul, Finset.mul_prod_erase Finset.univ den (Finset.mem_univ m)]
  have huR_orth : ∀ e : monLeFinset n D, ∑ m : E, uR m * A m e = 0 := by
    intro e
    apply IsFractionRing.injective R K₀
    rw [map_sum, map_zero]
    calc ∑ m : E, ιK (uR m * A m e)
        = ∑ m : E, (vK m * ιK denom) * AK m e := by
          refine Finset.sum_congr rfl fun m _ => by rw [map_mul, huR_eq m]; rfl
      _ = ιK denom * ∑ m : E, vK m * AK m e := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by rw [hvK_orth e, mul_zero]
  have hw_ne : uR m₀ ≠ 0 := by
    intro h0
    have h1 := huR_eq m₀
    rw [h0, map_zero] at h1
    rcases mul_eq_zero.mp h1.symm with hv0 | hd0
    · exact hvK_m0 hv0
    · exact hdenom_ne (IsFractionRing.injective R K₀ (by rwa [map_zero]))
  refine ⟨uR m₀, hw_ne, fun F _ π hπw a hdeg hfa => ?_⟩
  -- `a` has degree `≤ D`, so `x e := (toMvPoly F n a).coeff e` solves `A_F * x = b_F`
  have ha_eq : a = ∑ e : monLeFinset n D, ((toMvPoly F n a).coeff e.val) • weylMonom F e.val := by
    apply toMvPoly_injective F n
    rw [map_sum]
    conv_lhs => rw [poly_eq_sum_monLeFinset hdeg]
    rw [← Finset.sum_attach (monLeFinset n D)]
    refine Finset.sum_congr rfl fun e _ => by
      rw [map_smul, toMvPoly_weylMonom, smul_monomial, smul_eq_mul, mul_one]
  have hsys : ∀ m : E, ∑ e : monLeFinset n D, ((toMvPoly F n a).coeff e.val) * π (A m e) =
      π (b m) := by
    intro m
    have hcoeff := congrArg (fun z => (toMvPoly F n z).coeff m.val) hfa
    rw [ha_eq, map_sum, map_sum, MvPolynomial.coeff_sum] at hcoeff
    have hLHS : ∑ e : monLeFinset n D, (toMvPoly F n (weylAlgHom_baseChange π φ_R
        ((toMvPoly F n a).coeff e.val • weylMonom F e.val))).coeff m.val =
        ∑ e : monLeFinset n D, (toMvPoly F n a).coeff e.val * π (A m e) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 1
      have hw : weylMonom F e.val = weylMap π (weylMonom R e.val) := by
        apply toMvPoly_injective F n
        rw [toMvPoly_weylMap, toMvPoly_weylMonom, toMvPoly_weylMonom, MvPolynomial.map_monomial,
          RingHom.map_one]
      rw [hw, weylAlgHom_baseChange_weylMap, toMvPoly_weylMap, MvPolynomial.coeff_map]
    rw [hLHS] at hcoeff
    rw [hcoeff]
    have hRHS : toMvPoly F n (WeylAlgebra.of F v₀) = monomial (Finsupp.single v₀ 1) (1 : F) := by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
      rcases v₀ with i | i
      · simp [toMvPoly, toEnd]
      · change (toEnd F n (WeylAlgebra.of F (Sum.inr i))) 1 = X (Sum.inr i)
        simp only [toEnd, weylLift_of, LinearMap.sub_apply, LinearMap.mulLeft_apply, mul_one]
        simp
    rw [hRHS, MvPolynomial.coeff_monomial]
    simp only [b]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (Subtype.ext h1.symm) h2
    · exact absurd (congrArg Subtype.val h2).symm h1
    · simp
  have hcontra : π (uR m₀) = 0 := by
    calc π (uR m₀)
        = ∑ m : E, π (uR m) * π (b m) := by
          rw [Finset.sum_eq_single m₀ (fun m _ hne => by simp [b, hne]) (by simp)]
          simp [b]
      _ = ∑ m : E, π (uR m) * ∑ e : monLeFinset n D, (toMvPoly F n a).coeff e.val * π (A m e) := by
          refine Finset.sum_congr rfl fun m _ => by rw [hsys m]
      _ = ∑ m : E, ∑ e : monLeFinset n D, π (uR m) * ((toMvPoly F n a).coeff e.val * π (A m e)) := by
          refine Finset.sum_congr rfl fun m _ => Finset.mul_sum _ _ _
      _ = ∑ e : monLeFinset n D, ∑ m : E, π (uR m) * ((toMvPoly F n a).coeff e.val * π (A m e)) :=
          Finset.sum_comm
      _ = ∑ e : monLeFinset n D, (toMvPoly F n a).coeff e.val * π (∑ m : E, uR m * A m e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => by
            rw [map_mul π (uR m) (A m e), mul_left_comm]
      _ = 0 := by
          refine Finset.sum_eq_zero fun e _ => by rw [huR_orth e, map_zero, mul_zero]
  exact hπw hcontra

/-- Step 1–4 of specialization: given `a : Fin k → L` generating `R ⊆ L` and `W0 ∈ R \ {0}`,
produce a monic polynomial `g ∈ ℤ[T]` irreducible over `ℚ` with a root `α ∈ AlgebraicClosure ℚ`,
polynomials `fZ j, qZ, uZ, vZ ∈ ℤ[T]`, and a denominator `M > 0` certifying Bezout coprimality
of `(g, g')`, expressions for `x j`, and invertibility of `P0(x)`. -/
lemma exists_numfield_model {L : Type*} [Field L] [CharZero L] {k : ℕ}
    (a : Fin k → L) (R : Subring L)
    (hR : R = (MvPolynomial.eval₂Hom (Int.castRingHom L) a).range)
    (W0 : R) (hW0 : W0 ≠ 0) :
    ∃ (P0 : MvPolynomial (Fin k) ℤ) (x : Fin k → AlgebraicClosure ℚ) (α : AlgebraicClosure ℚ)
      (g uZ vZ qZ : Polynomial ℤ) (fZ : Fin k → Polynomial ℤ)
      (Du Dv Dq : ℕ) (Df : Fin k → ℕ),
      MvPolynomial.eval₂Hom (Int.castRingHom L) a P0 = (W0 : L) ∧
      (∀ f : MvPolynomial (Fin k) ℤ,
        MvPolynomial.eval₂Hom (Int.castRingHom L) a f = 0 →
          MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) f) = 0) ∧
      g.Monic ∧ 1 ≤ g.natDegree ∧
      Irreducible (g.map (Int.castRingHom ℚ)) ∧
      Polynomial.aeval α (g.map (Int.castRingHom ℚ)) = 0 ∧
      0 < Du ∧ 0 < Dv ∧ 0 < Dq ∧ (∀ j, 0 < Df j) ∧
      Polynomial.C (Dv : ℤ) * uZ * g + Polynomial.C (Du : ℤ) * vZ * g.derivative =
        Polynomial.C ((Du * Dv : ℕ) : ℤ) ∧
      (∀ j, Polynomial.aeval α ((fZ j).map (Int.castRingHom ℚ)) = (Df j : AlgebraicClosure ℚ) * x j) ∧
      Polynomial.aeval α (qZ.map (Int.castRingHom ℚ)) *
        MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) P0) =
          (Dq : AlgebraicClosure ℚ) := by
  have hW0_mem : (W0 : L) ∈ (MvPolynomial.eval₂Hom (Int.castRingHom L) a).range := by
    rw [← hR]; exact W0.prop
  obtain ⟨P0, hP0⟩ := hW0_mem
  let Qbar := AlgebraicClosure ℚ
  let evQ : MvPolynomial (Fin k) ℚ →+* L := MvPolynomial.eval₂Hom (algebraMap ℚ L) a
  let I : Ideal (MvPolynomial (Fin k) ℚ) := RingHom.ker evQ
  have hev_all : ∀ Q : MvPolynomial (Fin k) ℤ,
      evQ (MvPolynomial.map (Int.castRingHom ℚ) Q) = MvPolynomial.eval₂Hom (Int.castRingHom L) a Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C z => simp [evQ]
    | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
    | mul_X f j ih => rw [map_mul, map_mul, map_mul, ih]; simp [evQ]
  have hP0Q_not_rad : MvPolynomial.map (Int.castRingHom ℚ) P0 ∉ I.radical := by
    rintro ⟨r, hr⟩
    rw [RingHom.mem_ker, map_pow] at hr
    have h0 : evQ (MvPolynomial.map (Int.castRingHom ℚ) P0) = 0 := eq_zero_of_pow_eq_zero hr
    rw [hev_all P0, hP0] at h0
    exact hW0 (Subtype.ext h0)
  have hnot_van : MvPolynomial.map (Int.castRingHom ℚ) P0 ∉
      MvPolynomial.vanishingIdeal ℚ (MvPolynomial.zeroLocus Qbar I) := by
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Qbar) I]
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hnot_van
  push Not at hnot_van
  obtain ⟨x, hx_locus, hx_P0⟩ := hnot_van
  have hQbar_int : ∀ y : Qbar, IsIntegral ℚ y := fun y =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  let E : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ (Set.range x)
  have hfin : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun y _ => hQbar_int y)
  have : FiniteDimensional ℚ E := hfin
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element ℚ E
  let p_min : Polynomial ℚ := minpoly ℚ α₀.val
  have hp_min_monic : p_min.Monic := minpoly.monic (hQbar_int α₀.val)
  have hp_min_irred : Irreducible p_min := minpoly.irreducible (hQbar_int α₀.val)
  have hp_min_deg : 1 ≤ p_min.natDegree := by
    have := hp_min_irred.natDegree_pos; omega
  let N : ℕ := ∏ i ∈ Finset.range (p_min.natDegree + 1), (p_min.coeff i).den
  have hN_pos : 0 < N := Finset.prod_pos fun i _ => (p_min.coeff i).pos
  have hN_ne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN_pos)
  let α : Qbar := (N : Qbar) * α₀.val
  let d_min : ℕ := p_min.natDegree
  have hp_min_lc : p_min.coeff d_min = 1 := hp_min_monic.leadingCoeff
  have hcoeff_int : ∀ i : ℕ, ∃ z : ℤ, (z : ℚ) = (N : ℚ) ^ (d_min - i) * p_min.coeff i := by
    intro i
    by_cases hi : i ≤ d_min
    · have hdvd : ((p_min.coeff i).den : ℕ) ∣ N :=
        Finset.dvd_prod_of_mem (fun j => (p_min.coeff j).den)
          (Finset.mem_range.mpr (by dsimp only [d_min] at hi; omega))
      obtain ⟨q, hq⟩ := hdvd
      by_cases hid : i = d_min
      · subst hid
        refine ⟨1, ?_⟩
        simp [hp_min_lc]
      · have hpos_exp : 1 ≤ d_min - i := by omega
        refine ⟨(N : ℤ) ^ (d_min - i - 1) * (q : ℤ) * (p_min.coeff i).num, ?_⟩
        have hN_split : (N : ℚ) ^ (d_min - i) = (N : ℚ) ^ (d_min - i - 1) * (N : ℚ) := by
          rw [← pow_succ, Nat.sub_add_cancel hpos_exp]
        have hNq : (N : ℚ) = (q : ℚ) * ((p_min.coeff i).den : ℚ) := by
          have := congrArg (Nat.cast (R := ℚ)) hq
          simpa [Nat.cast_mul, mul_comm] using this
        have hprod : (N : ℚ) * p_min.coeff i = (q : ℚ) * ((p_min.coeff i).num : ℚ) := by
          rw [hNq, mul_assoc, Rat.den_mul_eq_num]
        rw [hN_split, mul_assoc ((N : ℚ) ^ _), hprod]
        push_cast; ring
    · refine ⟨0, ?_⟩
      have hlt : p_min.natDegree < i := by dsimp only [d_min] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp
  choose g_coeff hg_coeff using hcoeff_int
  let g : Polynomial ℤ := ∑ i ∈ Finset.range (d_min + 1), Polynomial.monomial i (g_coeff i)
  have hg_coeff_eq : ∀ i, g.coeff i = if i ≤ d_min then g_coeff i else 0 := by
    intro i
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ≤ d_min
    · rw [if_pos hi, Finset.sum_eq_single i (fun j _ hne => if_neg hne)
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl]
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega)
  have hg_natDeg : g.natDegree = d_min := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi; rw [hg_coeff_eq i, if_neg (by omega)]
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hg_coeff_eq d_min, if_pos le_rfl]
      intro h0
      have h1 := hg_coeff d_min
      rw [h0, Int.cast_zero, Nat.sub_self, pow_zero, one_mul, hp_min_lc] at h1
      exact zero_ne_one h1
  have hg_monic : g.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hg_natDeg, hg_coeff_eq d_min, if_pos le_rfl]
    have h1 := hg_coeff d_min
    rw [Nat.sub_self, pow_zero, one_mul, hp_min_lc] at h1
    exact Int.cast_injective (by rw [h1]; rfl)
  let gQ : Polynomial ℚ := g.map (Int.castRingHom ℚ)
  have hgQ_eval : Polynomial.aeval α gQ = 0 := by
    have heq : Polynomial.aeval α gQ = (N : Qbar) ^ d_min * Polynomial.aeval α₀.val p_min := by
      simp only [gQ, g, Polynomial.map_sum, Polynomial.map_monomial, map_sum,
        Polynomial.aeval_monomial, eq_intCast, hg_coeff]
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [α, mul_pow, map_mul, map_pow, map_natCast]
      have hexp : (N : Qbar) ^ (d_min - i) * (N : Qbar) ^ i = (N : Qbar) ^ d_min := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      calc (N : Qbar) ^ (d_min - i) * algebraMap ℚ Qbar (p_min.coeff i) * ((N : Qbar) ^ i * α₀.val ^ i)
          = ((N : Qbar) ^ (d_min - i) * (N : Qbar) ^ i) * (algebraMap ℚ Qbar (p_min.coeff i) * α₀.val ^ i) := by ring
        _ = (N : Qbar) ^ d_min * (algebraMap ℚ Qbar (p_min.coeff i) * α₀.val ^ i) := by rw [hexp]
    rw [heq, minpoly.aeval, mul_zero]
  have hgQ_irred : Irreducible gQ := by
    have hmin_dvd : minpoly ℚ α ∣ gQ := minpoly.dvd ℚ α hgQ_eval
    have hmin_deg : (minpoly ℚ α).natDegree = d_min := by
      have h1 : (minpoly ℚ α).natDegree ≤ d_min := by
        have hle := Polynomial.natDegree_le_of_dvd hmin_dvd (hg_monic.map (Int.castRingHom ℚ)).ne_zero
        rwa [hg_monic.natDegree_map, hg_natDeg] at hle
      have h2 : d_min ≤ (minpoly ℚ α).natDegree := by
        let q : Polynomial ℚ := (minpoly ℚ α).comp (Polynomial.C (N : ℚ) * Polynomial.X)
        have hq_eval : Polynomial.aeval α₀.val q = 0 := by
          simp only [q, Polynomial.aeval_comp, map_mul, Polynomial.aeval_X, map_natCast]
          exact minpoly.aeval ℚ α
        have hq_ne : q ≠ 0 := by
          intro hq0
          have h := congrArg (fun f : Polynomial ℚ => f.comp (Polynomial.C ((N : ℚ)⁻¹) * Polynomial.X)) hq0
          rw [Polynomial.zero_comp, Polynomial.comp_assoc] at h
          have hid : (Polynomial.C (N : ℚ) * Polynomial.X).comp (Polynomial.C ((N : ℚ)⁻¹) * Polynomial.X) =
              Polynomial.X := by
            rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
              ← Polynomial.C_mul, mul_inv_cancel₀ hN_ne, map_one, one_mul]
          rw [hid, Polynomial.comp_X] at h
          exact minpoly.ne_zero (hQbar_int α) h
        have hdvd := minpoly.dvd ℚ α₀.val hq_eval
        have hle := Polynomial.natDegree_le_of_dvd hdvd hq_ne
        have hq_deg : q.natDegree ≤ (minpoly ℚ α).natDegree := by
          calc q.natDegree ≤ (minpoly ℚ α).natDegree * (Polynomial.C (N : ℚ) * Polynomial.X).natDegree :=
                Polynomial.natDegree_comp_le
            _ ≤ (minpoly ℚ α).natDegree * 1 := by
                apply Nat.mul_le_mul_left
                exact le_trans Polynomial.natDegree_mul_le (by simp)
            _ = (minpoly ℚ α).natDegree := mul_one _
        exact le_trans hle hq_deg
      omega
    have hmon_min : (minpoly ℚ α).Monic := minpoly.monic (hQbar_int α)
    have hmon_gQ : gQ.Monic := hg_monic.map (Int.castRingHom ℚ)
    have heq_min : gQ = minpoly ℚ α := by
      obtain ⟨c, hc⟩ := hmin_dvd
      have hc_ne : c ≠ 0 := fun h0 => by rw [h0, mul_zero] at hc; exact hmon_gQ.ne_zero hc
      have hc_deg : c.natDegree = 0 := by
        have hdeg := congrArg Polynomial.natDegree hc
        rw [Polynomial.natDegree_mul hmon_min.ne_zero hc_ne, hmin_deg] at hdeg
        have hgQ_deg : gQ.natDegree = d_min := by rw [hg_monic.natDegree_map, hg_natDeg]
        omega
      have hc_monic : c.Monic := by
        have hlc := congrArg Polynomial.leadingCoeff hc
        rw [Polynomial.leadingCoeff_mul, hmon_min.leadingCoeff, one_mul, hmon_gQ.leadingCoeff] at hlc
        exact hlc.symm
      rw [hc, Polynomial.eq_one_of_monic_natDegree_zero hc_monic hc_deg, mul_one]
    rw [heq_min]
    exact minpoly.irreducible (hQbar_int α)
  have hsep : Polynomial.Separable gQ := hgQ_irred.separable
  obtain ⟨uQ, vQ, huvQ⟩ := hsep
  have hE_poly : ∀ y : E, ∃ f : Polynomial ℚ, Polynomial.aeval α f = y.val := by
    intro y
    let Sα : Subalgebra ℚ E := Algebra.adjoin ℚ ({α₀} : Set E)
    have hSα_inv : ∀ z ∈ Sα, z⁻¹ ∈ Sα := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0; simp [Sα.zero_mem]
      · have hz_int : IsIntegral ℚ z := by
          obtain ⟨p, hp_mon, hp_eval⟩ := hQbar_int z.val
          refine ⟨p, hp_mon, ?_⟩
          apply Subtype.ext
          rw [← Polynomial.aeval_def]
          change E.val (Polynomial.aeval z p) = 0
          rw [← Polynomial.aeval_algHom_apply E.val z p]
          exact hp_eval
        let q := minpoly ℚ z
        have hq_irred : Irreducible q := minpoly.irreducible hz_int
        have hq0 : q.coeff 0 ≠ 0 := by
          intro hc0
          have hX : Polynomial.X ∣ q := Polynomial.X_dvd_iff.mpr hc0
          rcases hq_irred.dvd_iff.mp hX with hu | hassoc
          · exact Polynomial.not_isUnit_X hu
          · have hz_zero : Polynomial.aeval z (Polynomial.X : Polynomial ℚ) = 0 := by
              obtain ⟨u, hu⟩ := hassoc
              have := congrArg (Polynomial.aeval z) hu
              rw [map_mul] at this
              have hqz : Polynomial.aeval z q = 0 := minpoly.aeval ℚ z
              rw [hqz, zero_mul] at this
              exact this.symm
            rw [Polynomial.aeval_X] at hz_zero
            exact hz0 hz_zero
        have hq_split : q = Polynomial.C (q.coeff 0) + Polynomial.X * q.divX := by
          rw [add_comm, Polynomial.X_mul_divX_add]
        have heval0 : algebraMap ℚ E (q.coeff 0) + z * Polynomial.aeval z q.divX = 0 := by
          have h0 : Polynomial.aeval z q = 0 := minpoly.aeval ℚ z
          rw [hq_split, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at h0
          exact h0
        have hinv_eq : z⁻¹ = (-(q.coeff 0)⁻¹) • Polynomial.aeval z q.divX := by
          apply mul_left_cancel₀ hz0
          rw [mul_inv_cancel₀ hz0, mul_smul_comm]
          have h1 : z * Polynomial.aeval z q.divX = -algebraMap ℚ E (q.coeff 0) :=
            eq_neg_of_add_eq_zero_right heval0
          rw [h1, Algebra.smul_def, mul_neg, map_neg, neg_mul, neg_neg, ← map_mul,
            inv_mul_cancel₀ hq0, map_one]
        rw [hinv_eq]
        refine Sα.smul_mem ?_ _
        have haeval_mem : ∀ f : Polynomial ℚ, Polynomial.aeval z f ∈ Sα := by
          intro f
          induction f using Polynomial.induction_on' with
          | add f₁ f₂ h₁ h₂ => rw [map_add]; exact Sα.add_mem h₁ h₂
          | monomial m c =>
            rw [Polynomial.aeval_monomial]
            exact Sα.mul_mem (Sα.algebraMap_mem c) (Sα.pow_mem hz m)
        exact haeval_mem q.divX
    let Fα : IntermediateField ℚ E := { Sα with inv_mem' := hSα_inv }
    have hle : IntermediateField.adjoin ℚ ({α₀} : Set E) ≤ Fα := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      exact Algebra.subset_adjoin hz
    have hmem : y ∈ Algebra.adjoin ℚ ({α₀} : Set E) := hle (by rw [hα₀]; trivial)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f.comp (Polynomial.C ((N : ℚ)⁻¹) * Polynomial.X), ?_⟩
    have hf' := congrArg Subtype.val hf
    simp only [Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, α]
    have hinv : algebraMap ℚ Qbar (N : ℚ)⁻¹ * ((N : Qbar) * α₀.val) = α₀.val := by
      rw [← mul_assoc, show (N : Qbar) = algebraMap ℚ Qbar (N : ℚ) by simp, ← map_mul,
        inv_mul_cancel₀ hN_ne, map_one, one_mul]
    rw [hinv]
    change Polynomial.aeval (E.val α₀) f = E.val y
    rw [Polynomial.aeval_algHom_apply E.val α₀ f]
    exact hf'
  have hx_poly : ∀ j : Fin k, ∃ f : Polynomial ℚ, Polynomial.aeval α f = x j := fun j =>
    hE_poly ⟨x j, IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩⟩
  choose fxQ hfxQ using hx_poly
  have hinv_poly : ∃ qQ : Polynomial ℚ,
      Polynomial.aeval α qQ * MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) P0) = 1 := by
    have hmemE_all : ∀ Q : MvPolynomial (Fin k) ℤ,
        MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) Q) ∈ E := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C z => rw [MvPolynomial.map_C, MvPolynomial.aeval_C]; exact E.algebraMap_mem (z : ℚ)
      | add f₁ f₂ h₁ h₂ => simp only [map_add]; exact E.add_mem h₁ h₂
      | mul_X f j ih =>
        simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
        exact E.mul_mem ih (IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩)
    have hinvE : (MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) P0))⁻¹ ∈ E :=
      E.inv_mem (hmemE_all P0)
    obtain ⟨qQ, hqQ⟩ := hE_poly ⟨_, hinvE⟩
    exact ⟨qQ, by rw [hqQ, inv_mul_cancel₀ hx_P0]⟩
  obtain ⟨qQ, hqQ⟩ := hinv_poly
  have hclear_poly : ∀ f : Polynomial ℚ, ∃ (D : ℕ) (_ : 0 < D) (fZ : Polynomial ℤ),
      fZ.map (Int.castRingHom ℚ) = Polynomial.C (D : ℚ) * f := by
    intro f
    let D : ℕ := ∏ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).den
    have hD_pos : 0 < D := Finset.prod_pos fun i _ => (f.coeff i).pos
    have hci : ∀ i, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * f.coeff i := by
      intro i
      by_cases hi : i ≤ f.natDegree
      · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j => (f.coeff j).den)
          (Finset.mem_range.mpr (by omega : i < f.natDegree + 1))
        refine ⟨(q : ℤ) * (f.coeff i).num, ?_⟩
        have hDq : D = (f.coeff i).den * q := hq
        rw [hDq, Nat.cast_mul, mul_comm ((f.coeff i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
        push_cast; ring
      · refine ⟨0, ?_⟩; rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    choose z hz using hci
    refine ⟨D, hD_pos, ∑ i ∈ Finset.range (f.natDegree + 1), Polynomial.monomial i (z i), ?_⟩
    ext i
    simp only [Polynomial.map_sum, Polynomial.map_monomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Polynomial.coeff_C_mul, eq_intCast]
    by_cases hi : i ≤ f.natDegree
    · rw [Finset.sum_eq_single i (fun j _ hne => if_neg hne)
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl, hz i]
    · rw [Finset.sum_eq_zero (fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  obtain ⟨Du, hDu, uZ, huZ⟩ := hclear_poly uQ
  obtain ⟨Dv, hDv, vZ, hvZ⟩ := hclear_poly vQ
  obtain ⟨Dq, hDq, qZ, hqZ⟩ := hclear_poly qQ
  choose Df hDf fZ hfZ using fun j => hclear_poly (fxQ j)
  refine ⟨P0, x, α, g, uZ, vZ, qZ, fZ, Du, Dv, Dq, Df, hP0, ?_, hg_monic, ?_, hgQ_irred, hgQ_eval,
    hDu, hDv, hDq, hDf, ?_, ?_, ?_⟩
  · intro f hf
    exact hx_locus _ (by rw [RingHom.mem_ker, hev_all f, hf])
  · rw [hg_natDeg]; exact hp_min_deg
  · apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, huZ, hvZ,
      Int.coe_castRingHom, Int.cast_natCast]
    rw [← Polynomial.derivative_map]
    have h1 := congrArg (fun r => Polynomial.C ((Du : ℚ) * (Dv : ℚ)) * r) huvQ
    simp only [mul_one, mul_add] at h1
    rw [Nat.cast_mul, ← h1]
    change Polynomial.C (Dv : ℚ) * (Polynomial.C (Du : ℚ) * uQ) * gQ +
        Polynomial.C (Du : ℚ) * (Polynomial.C (Dv : ℚ) * vQ) * gQ.derivative =
      Polynomial.C ((Du : ℚ) * (Dv : ℚ)) * (uQ * gQ) +
        Polynomial.C ((Du : ℚ) * (Dv : ℚ)) * (vQ * gQ.derivative)
    rw [Polynomial.C_mul]; ring
  · intro j
    rw [hfZ j, map_mul, Polynomial.aeval_C, hfxQ j]; simp
  · rw [hqZ, map_mul, Polynomial.aeval_C, mul_assoc, hqQ, mul_one]; simp

/-- Over a field `K`, a squarefree nonzero polynomial `gp` divides `h` whenever every irreducible
factor of `gp` divides `h`. -/
lemma squarefree_dvd_of_irred_dvd {K : Type*} [Field K] {gp h : Polynomial K}
    (hgp_ne : gp ≠ 0) (hgp_sqf : Squarefree gp)
    (hdiv : ∀ q : Polynomial K, Irreducible q → q ∣ gp → q ∣ h) : gp ∣ h := by
  have haux : ∀ (N : ℕ) (r : Polynomial K), r.natDegree ≤ N →
      r ≠ 0 → Squarefree r → (∀ q, Irreducible q → q ∣ r → q ∣ h) → r ∣ h := by
    intro N
    induction N with
    | zero =>
      intro r hr_deg hr_ne _ _
      have hu : IsUnit r := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hr_deg)]
        exact (isUnit_iff_ne_zero.mpr fun h0 => hr_ne (by
          rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hr_deg), h0, map_zero])).map Polynomial.C
      exact hu.dvd
    | succ N ih =>
      intro r hr_deg hr_ne hr_sqf hr_div
      by_cases hu : IsUnit r
      · exact hu.dvd
      · obtain ⟨q, hq_irred, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hr_ne
        obtain ⟨r', rfl⟩ := hq_dvd
        have hr'_ne : r' ≠ 0 := right_ne_zero_of_mul hr_ne
        have hq_ne : q ≠ 0 := left_ne_zero_of_mul hr_ne
        have hq_deg : 1 ≤ q.natDegree := by
          by_contra h0
          have hq0 : q.natDegree = 0 := by omega
          apply hq_irred.not_isUnit
          rw [Polynomial.eq_C_of_natDegree_eq_zero hq0]
          exact (isUnit_iff_ne_zero.mpr fun hc => hq_ne (by
            rw [Polynomial.eq_C_of_natDegree_eq_zero hq0, hc, map_zero])).map Polynomial.C
        have hr'_deg : r'.natDegree ≤ N := by
          rw [Polynomial.natDegree_mul hq_ne hr'_ne] at hr_deg; omega
        have hr'_sqf : Squarefree r' := hr_sqf.of_mul_right
        have hr'_dvd : r' ∣ h := ih r' hr'_deg hr'_ne hr'_sqf
          (fun s hs hsr' => hr_div s hs (dvd_mul_of_dvd_right hsr' q))
        have hq_dvd_h : q ∣ h := hr_div q hq_irred (dvd_mul_right q r')
        have hndvd_qr' : ¬ q ∣ r' := fun hd =>
          hq_irred.not_isUnit (hr_sqf q (mul_dvd_mul_left q hd))
        have hcop : IsCoprime q r' :=
          EuclideanDomain.isCoprime_of_dvd (fun ⟨h1, _⟩ => hq_ne h1) fun d hd_nu _ hdq hdr' => by
            rcases hq_irred.dvd_iff.mp hdq with hdu | hassoc
            · exact hd_nu hdu
            · exact hndvd_qr' (hassoc.dvd.trans hdr')
        exact hcop.mul_dvd hq_dvd_h hr'_dvd
  exact haux gp.natDegree gp le_rfl hgp_ne hgp_sqf hdiv

/-- For a squarefree nonzero polynomial `gp ∈ (ZMod p)[T]` and a quotient `mkB : (ZMod p)[T] →+* B`
with `ker mkB = (gp)`, every `φ_B` on `W B n` sends `of B v ^ p` into `range (centerLift B n p)`. -/
lemma weyl_centerLift_of_squarefree_quot {n p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (gp : Polynomial (ZMod p)) (hgp_ne : gp ≠ 0) (hgp_sqf : Squarefree gp)
    {B : Type} [CommRing B] (mkB : Polynomial (ZMod p) →+* B)
    (hmkB_surj : Function.Surjective mkB) (hmkB_ker : ∀ f, mkB f = 0 ↔ gp ∣ f)
    (φ_B : W B n →ₐ[B] W B n) (v : Fin n ⊕ Fin n) :
    ∃ fB : P B n, φ_B (WeylAlgebra.of B v ^ p) = centerLift B n p fB := by
  let P_v : P B n := toMvPoly B n (φ_B (WeylAlgebra.of B v ^ p))
  have hcoeff_zero : ∀ d : (Fin n ⊕ Fin n) →₀ ℕ, (∃ w, ¬ p ∣ d w) → P_v.coeff d = 0 := by
    intro d ⟨w, hndvd⟩
    obtain ⟨h_poly, hh_poly⟩ := hmkB_surj (P_v.coeff d)
    rw [← hh_poly, hmkB_ker]
    refine squarefree_dvd_of_irred_dvd hgp_ne hgp_sqf fun q hq_irred hq_dvd => ?_
    have : (Ideal.span ({q} : Set (Polynomial (ZMod p)))).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hq_irred
    let Iq : Ideal (Polynomial (ZMod p)) := Ideal.span ({q} : Set (Polynomial (ZMod p)))
    let Fq := Polynomial (ZMod p) ⧸ Iq
    let _ : Field Fq := Ideal.Quotient.field Iq
    let mkq : Polynomial (ZMod p) →+* Fq := Ideal.Quotient.mk Iq
    have : CharP Fq p :=
      charP_of_injective_ringHom (mkq.comp Polynomial.C).injective p
    -- Factor `mkq` through `mkB : (ZMod p)[T] →+* B`
    choose liftB hliftB using hmkB_surj
    have hker_sub : ∀ r : Polynomial (ZMod p), mkB r = 0 → mkq r = 0 := fun r hr => by
      rw [hmkB_ker] at hr
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change r ∈ Ideal.span ({q} : Set (Polynomial (ZMod p)))
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hq_dvd hr
    let πq : B →+* Fq :=
      { toFun := fun b => mkq (liftB b)
        map_one' := by
          rw [← map_one mkq, ← sub_eq_zero, ← map_sub]
          exact hker_sub _ (by rw [map_sub, hliftB 1, map_one, sub_self])
        map_mul' := fun b₁ b₂ => by
          rw [← map_mul, ← sub_eq_zero, ← map_sub]
          exact hker_sub _ (by rw [map_sub, map_mul, hliftB, hliftB, hliftB, sub_self])
        map_zero' := by
          rw [← map_zero mkq, ← sub_eq_zero, ← map_sub]
          exact hker_sub _ (by rw [map_sub, hliftB 0, map_zero, sub_self])
        map_add' := fun b₁ b₂ => by
          rw [← map_add, ← sub_eq_zero, ← map_sub]
          exact hker_sub _ (by rw [map_sub, map_add, hliftB, hliftB, hliftB, sub_self]) }
    have hπq_mkB : ∀ r : Polynomial (ZMod p), πq (mkB r) = mkq r := fun r => by
      rw [← sub_eq_zero]
      change mkq (liftB (mkB r)) - mkq r = 0
      rw [← map_sub]
      exact hker_sub _ (by rw [map_sub, hliftB, sub_self])
    let φ_Fq : W Fq n →ₐ[Fq] W Fq n := weylAlgHom_baseChange πq φ_B
    obtain ⟨φ₀_q, hφ₀_q⟩ := exists_centerMap hp φ_Fq
    have heq_Fq : toMvPoly Fq n (φ_Fq (WeylAlgebra.of Fq v ^ p)) = MvPolynomial.expand p (φ₀_q (X v)) := by
      have hXv : WeylAlgebra.of Fq v ^ p = centerEmb Fq n p (X v) := by
        simp only [centerEmb, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]
      rw [hXv, hφ₀_q, toMvPoly_centerEmb]
    have hmap_Pv : MvPolynomial.map πq P_v = MvPolynomial.expand p (φ₀_q (X v)) := by
      rw [← heq_Fq]
      simp only [P_v]
      rw [← toMvPoly_weylMap, ← weylAlgHom_baseChange_weylMap, map_pow, weylMap_of]
    have hcd0 : πq (P_v.coeff d) = 0 := by
      rw [← MvPolynomial.coeff_map, hmap_Pv]
      have hexp : MvPolynomial.expand p (φ₀_q (X v)) =
          ∑ e ∈ (φ₀_q (X v)).support, monomial (p • e) ((φ₀_q (X v)).coeff e) := by
        conv_lhs => rw [(φ₀_q (X v)).as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun e _ => MvPolynomial.expand_monomial p e _
      rw [hexp, MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hpe
      apply hndvd
      have hw := congrArg (fun s : (Fin n ⊕ Fin n) →₀ ℕ => s w) hpe
      exact ⟨e w, hw.symm⟩
    rw [← hh_poly, hπq_mkB] at hcd0
    rw [Ideal.Quotient.eq_zero_iff_mem] at hcd0
    change h_poly ∈ Ideal.span ({q} : Set (Polynomial (ZMod p))) at hcd0
    exact Ideal.mem_span_singleton.mp hcd0
  let fB : P B n := ∑ d ∈ P_v.support,
    monomial (Finsupp.equivFunOnFinite.symm (fun w => d w / p)) (P_v.coeff d)
  refine ⟨fB, ?_⟩
  apply toMvPoly_injective B n
  rw [centerLift, toMvPoly_ofMvPoly]
  change P_v = MvPolynomial.expand p fB
  simp only [fB, map_sum, MvPolynomial.expand_monomial]
  conv_lhs => rw [P_v.as_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  congr 2
  ext w
  have hdvd : p ∣ d w := by
    by_contra hnd
    exact MvPolynomial.mem_support_iff.mp hd (hcoeff_zero d ⟨w, hnd⟩)
  change d w = p * (d w / p)
  exact (Nat.mul_div_cancel' hdvd).symm

/-- Specialize a finitely generated `ℤ`-subalgebra `R ⊆ L` (with `CharZero L`) and a nonzero
element `W ∈ R` to a prime `p > m`, a `p`-torsion-free ring `S` with a ring hom `ψ : R →+* S`,
a char-`p` field `F : Type` with a quotient `π : S →+* F`, and a Poisson endomorphism `φ₀` on `P F n`
compatible with `weylAlgHom_baseChange (π.comp ψ) φ_R`, such that `π (ψ W) ≠ 0`! -/
lemma exists_charP_specialization {L : Type*} [Field L] [CharZero L] {n k : ℕ}
    (a : Fin k → L) (R : Subring L)
    (hR : R = (MvPolynomial.eval₂Hom (Int.castRingHom L) a).range)
    (φ_R : W R n →ₐ[R] W R n) (W0 : R) (hW0 : W0 ≠ 0) (m : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime) (_ : m < p) (F : Type) (_ : Field F) (_ : CharP F p)
      (π : R →+* F) (φ₀ : P F n →ₐ[F] P F n),
      π W0 ≠ 0 ∧
      IsPoissonEndomorphism φ₀ ∧
      (∀ f : P F n, weylAlgHom_baseChange π φ_R (centerEmb F n p f) = centerEmb F n p (φ₀ f)) := by
  obtain ⟨P0, x, α, g, uZ, vZ, qZ, fZ, Du, Dv, Dq, Df, hP0, hx_ker, hg_monic, hg_deg,
    hgQ_irred, hgQ_eval, hDu, hDv, hDq, hDf, hbez, hfZ_eval, hqZ_eval⟩ :=
    exists_numfield_model a R hR W0 hW0
  let Qbar := AlgebraicClosure ℚ
  let gQ : Polynomial ℚ := g.map (Int.castRingHom ℚ)
  have hQbar_int : ∀ y : Qbar, IsIntegral ℚ y := fun y =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  let M : ℕ := Du * Dv * Dq * ∏ j : Fin k, Df j
  have hM_pos : 0 < M := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hDu hDv) hDq)
    (Finset.prod_pos fun j _ => hDf j)
  obtain ⟨p, hp_gt, hp⟩ := Nat.exists_infinite_primes (max m M + 1)
  have hmp : m < p := by omega
  have hMp : M < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hM_ndvd : ¬ p ∣ M := Nat.not_dvd_of_pos_of_lt hM_pos hMp
  have hM_unit_ZMod : IsUnit (Int.castRingHom (ZMod p) (M : ℤ)) := by
    rw [isUnit_iff_ne_zero]
    change ((M : ℤ) : ZMod p) ≠ 0
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact hM_ndvd
  let A := Localization.Away (M : ℤ)
  have hM_unit_Q : IsUnit (Int.castRingHom ℚ (M : ℤ)) :=
    isUnit_iff_ne_zero.mpr (by simp [hM_pos.ne'])
  let embA : A →+* ℚ := IsLocalization.Away.lift (M : ℤ) hM_unit_Q
  have hembA_inj : Function.Injective embA := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro y hy
    obtain ⟨⟨z, ⟨_, ⟨e, rfl⟩⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (M : ℤ)) y
    have h1 := congrArg embA hz
    rw [map_mul, hy, zero_mul] at h1
    have hz0 : z = 0 := by
      have : embA (algebraMap ℤ A z) = (z : ℚ) := IsLocalization.Away.lift_eq _ _ z
      rw [this] at h1
      exact Int.cast_injective (by rw [← h1]; rfl)
    rw [hz0, map_zero] at hz
    have hu : IsUnit (algebraMap ℤ A ((M : ℤ) ^ e)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (M : ℤ)).pow e
    exact hu.mul_left_eq_zero.mp hz
  have : Nontrivial A := ⟨⟨0, 1, fun h => zero_ne_one (α := ℚ) (by simpa using congrArg embA h)⟩⟩
  let redA : A →+* ZMod p := IsLocalization.Away.lift (M : ℤ) hM_unit_ZMod
  have hredA_surj : Function.Surjective redA := by
    intro y
    refine ⟨algebraMap ℤ A y.val, ?_⟩
    rw [IsLocalization.Away.lift_eq]; simp
  have hredA_ker : ∀ y : A, redA y = 0 → ∃ t : A, y = (p : A) * t := by
    intro y hy
    obtain ⟨⟨z, ⟨_, ⟨e, rfl⟩⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (M : ℤ)) y
    have h1 := congrArg redA hz
    rw [map_mul, hy, zero_mul, IsLocalization.Away.lift_eq] at h1
    have hdvd : (p : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h1.symm
    obtain ⟨w, rfl⟩ := hdvd
    have hu : IsUnit (algebraMap ℤ A ((M : ℤ) ^ e)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (M : ℤ)).pow e
    obtain ⟨u, hu_eq⟩ := hu
    refine ⟨algebraMap ℤ A w * (↑u⁻¹ : A), ?_⟩
    calc y = y * algebraMap ℤ A ((M : ℤ) ^ e) * (↑u⁻¹ : A) := by
            rw [mul_assoc, ← hu_eq, Units.mul_inv, mul_one]
      _ = algebraMap ℤ A ((p : ℤ) * w) * (↑u⁻¹ : A) := by rw [hz]
      _ = (p : A) * (algebraMap ℤ A w * (↑u⁻¹ : A)) := by
            rw [map_mul, eq_intCast, Int.cast_natCast, mul_assoc]
  let gA : Polynomial A := g.map (algebraMap ℤ A)
  have hgA_monic : gA.Monic := hg_monic.map (algebraMap ℤ A)
  letI : CommRing (Polynomial A) := inferInstance
  let IgA : Ideal (Polynomial A) := Ideal.span ({gA} : Set (Polynomial A))
  let S := Polynomial A ⧸ IgA
  let mkS : Polynomial A →+* S := Ideal.Quotient.mk IgA
  have hrem_mkS : ∀ f : Polynomial A, mkS f = mkS (f %ₘ gA) := fun f => by
    rw [Ideal.Quotient.eq]
    change f - f %ₘ gA ∈ IgA
    rw [Ideal.mem_span_singleton]
    have hdiv := Polynomial.modByMonic_add_div f gA
    exact ⟨f /ₘ gA, (sub_eq_of_eq_add' hdiv.symm)⟩
  have hS_ptf : ∀ s : S, (p : S) * s = 0 → s = 0 := by
    intro s hs
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hrem_mkS f] at hs ⊢
    rw [← map_natCast mkS p, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hs
    change (p : Polynomial A) * (f %ₘ gA) ∈ Ideal.span ({gA} : Set (Polynomial A)) at hs
    rw [Ideal.mem_span_singleton] at hs
    obtain ⟨q, hq⟩ := hs
    have hdeg_lt : ((p : Polynomial A) * (f %ₘ gA)).degree < gA.degree := by
      by_cases h0 : f %ₘ gA = 0
      · rw [h0, mul_zero, Polynomial.degree_zero, Polynomial.degree_eq_natDegree hgA_monic.ne_zero]
        exact WithBot.bot_lt_coe _
      · calc ((p : Polynomial A) * (f %ₘ gA)).degree
            ≤ (p : Polynomial A).degree + (f %ₘ gA).degree := Polynomial.degree_mul_le _ _
          _ ≤ 0 + (f %ₘ gA).degree := by
              gcongr
              rw [show (p : Polynomial A) = Polynomial.C (p : A) by simp]
              exact Polynomial.degree_C_le
          _ = (f %ₘ gA).degree := zero_add _
          _ < gA.degree := Polynomial.degree_modByMonic_lt f hgA_monic
    have hq0 : q = 0 := by
      by_contra hq_ne
      have hge : gA.degree ≤ (gA * q).degree := by
        rw [mul_comm, Polynomial.degree_eq_natDegree hgA_monic.ne_zero,
          Polynomial.degree_eq_natDegree (hgA_monic.mul_left_ne_zero hq_ne),
          mul_comm q gA, hgA_monic.natDegree_mul' hq_ne]
        exact Nat.cast_le.mpr (Nat.le_add_right _ _)
      rw [← hq] at hge
      exact not_lt_of_ge hge hdeg_lt
    rw [hq0, mul_zero] at hq
    have hrem0 : f %ₘ gA = 0 := by
      ext i
      have hi := congrArg (fun r : Polynomial A => embA (r.coeff i)) hq
      simp only [Polynomial.coeff_natCast_mul, map_mul, map_natCast, Polynomial.coeff_zero] at hi
      rw [map_zero] at hi
      rcases mul_eq_zero.mp hi with hp0 | hf0
      · exact absurd (Nat.cast_eq_zero.mp hp0) hp.ne_zero
      · exact hembA_inj (by rw [hf0, Polynomial.coeff_zero, map_zero])
    rw [hrem0, map_zero]
  have hgA_eval : Polynomial.eval₂ ((algebraMap ℚ Qbar).comp embA) α gA = 0 := by
    have hcomp : Polynomial.eval₂ ((algebraMap ℚ Qbar).comp embA) α gA = Polynomial.aeval α gQ := by
      simp only [gA, gQ, Polynomial.eval₂_map, Polynomial.aeval_def]
      congr 1; ext z; simp [embA, IsLocalization.Away.lift_eq]
    rw [hcomp, hgQ_eval]
  let embS : S →+* Qbar := Ideal.Quotient.lift IgA
    (Polynomial.eval₂RingHom ((algebraMap ℚ Qbar).comp embA) α)
    (fun f hf => by
      change f ∈ Ideal.span ({gA} : Set (Polynomial A)) at hf
      rw [Ideal.mem_span_singleton] at hf
      obtain ⟨q, rfl⟩ := hf
      simp [hgA_eval])
  have hembS_mk : ∀ f : Polynomial A,
      embS (mkS f) = Polynomial.eval₂ ((algebraMap ℚ Qbar).comp embA) α f := fun f => by
    change Ideal.Quotient.lift IgA _ _ (Ideal.Quotient.mk IgA f) = _
    rw [Ideal.Quotient.lift_mk]; rfl
  have hembS_inj : Function.Injective embS := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro s hs
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hrem_mkS f] at hs ⊢
    have hev : Polynomial.aeval α ((f %ₘ gA).map embA) = 0 := by
      rw [hembS_mk] at hs
      simpa [Polynomial.aeval_def, Polynomial.eval₂_map] using hs
    have hdvd : gQ ∣ (f %ₘ gA).map embA := by
      have hmin := minpoly.dvd ℚ α hev
      have hmin_dvd_gQ := minpoly.dvd ℚ α hgQ_eval
      rcases hgQ_irred.dvd_iff.mp hmin_dvd_gQ with hu | hassoc
      · exact absurd hu (minpoly.irreducible (hQbar_int α)).not_isUnit
      · exact hassoc.dvd.trans hmin
    have hdeg_lt : ((f %ₘ gA).map embA).degree < gQ.degree := by
      calc ((f %ₘ gA).map embA).degree
          ≤ (f %ₘ gA).degree := Polynomial.degree_map_le
        _ < gA.degree := Polynomial.degree_modByMonic_lt f hgA_monic
        _ = gQ.degree := by
            rw [Polynomial.degree_eq_natDegree hgA_monic.ne_zero,
              Polynomial.degree_eq_natDegree (hg_monic.map (Int.castRingHom ℚ)).ne_zero,
              hg_monic.natDegree_map, hg_monic.natDegree_map]
    have hmap0 : (f %ₘ gA).map embA = 0 := by
      by_contra hne
      exact not_lt_of_ge (Polynomial.degree_le_of_dvd hdvd hne) hdeg_lt
    have hrem0 : f %ₘ gA = 0 := by
      ext i
      exact hembA_inj (by
        have := congrArg (fun r : Polynomial ℚ => r.coeff i) hmap0
        simpa [Polynomial.coeff_map] using this)
    rw [hrem0, map_zero]
  have hunit_of_dvd_M : ∀ D : ℕ, D ∣ M → ∃ u : Aˣ, (u : A) = algebraMap ℤ A (D : ℤ) := by
    intro D hDM
    obtain ⟨c, hc⟩ := hDM
    have hMu : IsUnit (algebraMap ℤ A (M : ℤ)) := IsLocalization.Away.algebraMap_isUnit (M : ℤ)
    have hEq : algebraMap ℤ A (M : ℤ) = algebraMap ℤ A (D : ℤ) * algebraMap ℤ A (c : ℤ) := by
      rw [← map_mul]; congr 1; exact_mod_cast hc
    rw [hEq] at hMu
    obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hMu
    exact ⟨u, hu⟩
  have hxS : ∀ j : Fin k, ∃ y : S, embS y = x j := by
    intro j
    obtain ⟨u, hu⟩ := hunit_of_dvd_M (Df j)
      (dvd_trans (Finset.dvd_prod_of_mem Df (Finset.mem_univ j)) (dvd_mul_left _ _))
    refine ⟨mkS (Polynomial.C (↑u⁻¹ : A) * (fZ j).map (algebraMap ℤ A)), ?_⟩
    rw [hembS_mk, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map, RingHom.comp_apply]
    have hu_emb : embA (↑u⁻¹ : A) = ((Df j : ℚ))⁻¹ := by
      have h1 : embA (u : A) * embA (↑u⁻¹ : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have h2 : embA (u : A) = (Df j : ℚ) := by rw [hu, IsLocalization.Away.lift_eq]; simp
      rw [h2] at h1; exact eq_inv_of_mul_eq_one_right h1
    have hcomp : embA.comp (algebraMap ℤ A) = Int.castRingHom ℚ := by
      ext z; simp [embA, IsLocalization.Away.lift_eq]
    rw [hu_emb, RingHom.comp_assoc, hcomp, ← Polynomial.eval₂_map]
    change algebraMap ℚ Qbar (Df j : ℚ)⁻¹ * Polynomial.aeval α ((fZ j).map (Int.castRingHom ℚ)) = x j
    rw [hfZ_eval j, ← mul_assoc, show (Df j : Qbar) = algebraMap ℚ Qbar (Df j : ℚ) by simp,
      ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (hDf j).ne'), map_one, one_mul]
  choose xS hxS_eq using hxS
  let evS : MvPolynomial (Fin k) ℤ →+* S := MvPolynomial.eval₂Hom (Int.castRingHom S) xS
  have hevS_emb : ∀ f : MvPolynomial (Fin k) ℤ,
      embS (evS f) = MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C z => simp [evS]
    | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X f j ih =>
      rw [map_mul, map_mul, map_mul, map_mul, ih, MvPolynomial.map_X, MvPolynomial.aeval_X]
      congr 1; simp [evS, hxS_eq j]
  have hker_le : ∀ f : MvPolynomial (Fin k) ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom L) a f = 0 → evS f = 0 := by
    intro f hf
    apply hembS_inj; rw [hevS_emb, map_zero]; exact hx_ker f hf
  have hlift_R : ∀ r : R, ∃ f : MvPolynomial (Fin k) ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom L) a f = (r : L) := fun r => by
    have hr : (r : L) ∈ (MvPolynomial.eval₂Hom (Int.castRingHom L) a).range := by
      rw [← hR]; exact r.prop
    exact hr
  choose repR hrepR using hlift_R
  let ψ : R →+* S :=
    { toFun := fun r => evS (repR r)
      map_one' := by
        rw [← map_one evS, ← sub_eq_zero, ← map_sub]
        exact hker_le _ (by rw [map_sub, hrepR 1, map_one]; simp)
      map_mul' := fun r₁ r₂ => by
        rw [← map_mul, ← sub_eq_zero, ← map_sub]
        exact hker_le _ (by rw [map_sub, map_mul, hrepR, hrepR, hrepR]; simp)
      map_zero' := by
        rw [← map_zero evS, ← sub_eq_zero, ← map_sub]
        exact hker_le _ (by rw [map_sub, hrepR 0, map_zero]; simp)
      map_add' := fun r₁ r₂ => by
        rw [← map_add, ← sub_eq_zero, ← map_sub]
        exact hker_le _ (by rw [map_sub, map_add, hrepR, hrepR, hrepR]; simp) }
  have hW0_unit : IsUnit (ψ W0) := by
    obtain ⟨u, hu⟩ := hunit_of_dvd_M Dq (dvd_trans (dvd_mul_left Dq (Du * Dv)) (dvd_mul_right _ _))
    let invW0 : S := mkS (Polynomial.C (↑u⁻¹ : A) * qZ.map (algebraMap ℤ A))
    have hmul1 : invW0 * ψ W0 = 1 := by
      apply hembS_inj
      rw [map_mul, map_one]
      have hψW0 : embS (ψ W0) = MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom ℚ) P0) := by
        have heq : evS (repR W0) = evS P0 := by
          rw [← sub_eq_zero, ← map_sub]
          exact hker_le _ (by rw [map_sub, hrepR W0, hP0, sub_self])
        change embS (evS (repR W0)) = _
        rw [heq, hevS_emb]
      have hinvW0 : embS invW0 = algebraMap ℚ Qbar (Dq : ℚ)⁻¹ *
          Polynomial.aeval α (qZ.map (Int.castRingHom ℚ)) := by
        rw [hembS_mk, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map,
          RingHom.comp_apply]
        have hu_emb : embA (↑u⁻¹ : A) = ((Dq : ℚ))⁻¹ := by
          have h1 : embA (u : A) * embA (↑u⁻¹ : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
          have h2 : embA (u : A) = (Dq : ℚ) := by rw [hu, IsLocalization.Away.lift_eq]; simp
          rw [h2] at h1; exact eq_inv_of_mul_eq_one_right h1
        have hcomp : embA.comp (algebraMap ℤ A) = Int.castRingHom ℚ := by
          ext z; simp [embA, IsLocalization.Away.lift_eq]
        rw [hu_emb, RingHom.comp_assoc, hcomp, ← Polynomial.eval₂_map]; rfl
      rw [hinvW0, hψW0, mul_assoc, hqZ_eval, show (Dq : Qbar) = algebraMap ℚ Qbar (Dq : ℚ) by simp,
        ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hDq.ne'), map_one]
    exact ⟨⟨ψ W0, invW0, by rw [mul_comm, hmul1], hmul1⟩, rfl⟩
  let gp : Polynomial (ZMod p) := g.map (Int.castRingHom (ZMod p))
  have hgp_monic : gp.Monic := hg_monic.map (Int.castRingHom (ZMod p))
  have hgp_sep : Polynomial.Separable gp := by
    have hbez_p := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hbez
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
      Int.cast_natCast] at hbez_p
    rw [← Polynomial.derivative_map] at hbez_p
    have hDuDv_ne : ((Du * Dv : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hM_ndvd (dvd_trans hdvd (dvd_trans (dvd_mul_right _ Dq) (dvd_mul_right _ _)))
    have hinv := inv_mul_cancel₀ hDuDv_ne
    refine ⟨Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) * (Polynomial.C (Dv : ZMod p) * uZ.map (Int.castRingHom (ZMod p))),
      Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) * (Polynomial.C (Du : ZMod p) * vZ.map (Int.castRingHom (ZMod p))), ?_⟩
    calc Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) * (Polynomial.C (Dv : ZMod p) * uZ.map (Int.castRingHom (ZMod p))) * gp +
          Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) * (Polynomial.C (Du : ZMod p) * vZ.map (Int.castRingHom (ZMod p))) * gp.derivative
        = Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) *
            (Polynomial.C (Dv : ZMod p) * uZ.map (Int.castRingHom (ZMod p)) * gp +
             Polynomial.C (Du : ZMod p) * vZ.map (Int.castRingHom (ZMod p)) * gp.derivative) := by ring
      _ = Polynomial.C (((Du * Dv : ℕ) : ZMod p)⁻¹) * Polynomial.C ((Du * Dv : ℕ) : ZMod p) := by
            rw [hbez_p]
      _ = 1 := by rw [← map_mul, hinv, map_one]
  have hgp_sqf : Squarefree gp := hgp_sep.squarefree
  have hgp_deg : 1 ≤ gp.natDegree := by rw [hg_monic.natDegree_map]; exact hg_deg
  let Igp : Ideal (Polynomial (ZMod p)) := Ideal.span ({gp} : Set (Polynomial (ZMod p)))
  let B := Polynomial (ZMod p) ⧸ Igp
  let mkB : Polynomial (ZMod p) →+* B := Ideal.Quotient.mk Igp
  let qB : S →+* B := Ideal.Quotient.lift IgA
    (mkB.comp (Polynomial.mapRingHom redA))
    (fun f hf => by
      change f ∈ Ideal.span ({gA} : Set (Polynomial A)) at hf
      rw [Ideal.mem_span_singleton] at hf
      obtain ⟨q, rfl⟩ := hf
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, map_mul]
      have hgp_eq : gA.map redA = gp := by
        simp only [gA, gp, Polynomial.map_map]
        congr 1; ext z; simp [redA, IsLocalization.Away.lift_eq]
      rw [hgp_eq]
      have h0 : mkB gp = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [h0, zero_mul])
  have hqB_mk : ∀ f : Polynomial A, qB (mkS f) = mkB (f.map redA) := fun f => by
    change Ideal.Quotient.lift IgA _ _ (Ideal.Quotient.mk IgA f) = _
    rw [Ideal.Quotient.lift_mk]; rfl
  have hqB_surj : Function.Surjective qB := by
    intro b
    obtain ⟨fp, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hlift_poly : ∃ f : Polynomial A, f.map redA = fp := by
      choose c hc using fun i => hredA_surj (fp.coeff i)
      refine ⟨∑ i ∈ Finset.range (fp.natDegree + 1), Polynomial.monomial i (c i), ?_⟩
      ext i
      simp only [Polynomial.map_sum, Polynomial.map_monomial, Polynomial.finsetSum_coeff,
        Polynomial.coeff_monomial]
      by_cases hi : i ≤ fp.natDegree
      · rw [Finset.sum_eq_single i (fun j _ hne => if_neg hne)
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl, hc i]
      · rw [Finset.sum_eq_zero (fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega)),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    obtain ⟨f, hf⟩ := hlift_poly
    exact ⟨mkS f, by rw [hqB_mk, hf]⟩
  have hqB_ker : ∀ s : S, qB s = 0 → ∃ t : S, s = (p : S) * t := by
    intro s hs
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hrem_mkS f] at hs ⊢
    rw [hqB_mk] at hs
    rw [Ideal.Quotient.eq_zero_iff_mem] at hs
    change (f %ₘ gA).map redA ∈ Ideal.span ({gp} : Set (Polynomial (ZMod p))) at hs
    rw [Ideal.mem_span_singleton] at hs
    have hdeg_lt : ((f %ₘ gA).map redA).degree < gp.degree := by
      calc ((f %ₘ gA).map redA).degree
          ≤ (f %ₘ gA).degree := Polynomial.degree_map_le
        _ < gA.degree := Polynomial.degree_modByMonic_lt f hgA_monic
        _ = gp.degree := by
            rw [Polynomial.degree_eq_natDegree hgA_monic.ne_zero,
              Polynomial.degree_eq_natDegree hgp_monic.ne_zero,
              hg_monic.natDegree_map, hg_monic.natDegree_map]
    have hmap0 : (f %ₘ gA).map redA = 0 := by
      by_contra hne
      exact not_lt_of_ge (Polynomial.degree_le_of_dvd hs hne) hdeg_lt
    have hcoeff_div : ∀ i, ∃ t : A, (f %ₘ gA).coeff i = (p : A) * t := fun i =>
      hredA_ker _ (by have := congrArg (fun r : Polynomial (ZMod p) => r.coeff i) hmap0; simpa using this)
    choose t ht using hcoeff_div
    refine ⟨mkS (∑ i ∈ Finset.range ((f %ₘ gA).natDegree + 1), Polynomial.monomial i (t i)), ?_⟩
    rw [← map_natCast mkS p, ← map_mul]
    congr 1
    ext i
    simp only [Polynomial.coeff_natCast_mul, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ≤ (f %ₘ gA).natDegree
    · rw [Finset.sum_eq_single i (fun j _ hne => if_neg hne)
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl, ht i]
    · rw [Finset.sum_eq_zero (fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega)),
        mul_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  let φ_S : W S n →ₐ[S] W S n := weylAlgHom_baseChange ψ φ_R
  let φ_B : W B n →ₐ[B] W B n := weylAlgHom_baseChange qB φ_S
  choose fB hfB using fun v => weyl_centerLift_of_squarefree_quot hp gp hgp_monic.ne_zero hgp_sqf
    mkB Ideal.Quotient.mk_surjective
    (fun f => by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change f ∈ Ideal.span ({gp} : Set (Polynomial (ZMod p))) ↔ gp ∣ f
      exact Ideal.mem_span_singleton)
    φ_B v
  have hlift_FS : ∀ v : Fin n ⊕ Fin n, ∃ fS : P S n, MvPolynomial.map qB fS = fB v := by
    intro v
    choose c hc using fun d => hqB_surj ((fB v).coeff d)
    refine ⟨∑ d ∈ (fB v).support, monomial d (c d), ?_⟩
    rw [map_sum]
    conv_rhs => rw [(fB v).as_sum]
    refine Finset.sum_congr rfl fun d _ => by rw [MvPolynomial.map_monomial, hc d]
  choose F_lift hF_lift using hlift_FS
  have hModW_lift : ∀ v : Fin n ⊕ Fin n, ModW p (φ_S (WeylAlgebra.of S v ^ p)) (centerLift S n p (F_lift v)) := by
    intro v
    have hmap0 : weylMap qB (φ_S (WeylAlgebra.of S v ^ p) - centerLift S n p (F_lift v)) = 0 := by
      rw [map_sub, ← weylAlgHom_baseChange_weylMap, map_pow, weylMap_of, weylMap_centerLift,
        hF_lift v, hfB v, sub_self]
    have hpoly0 : MvPolynomial.map qB (toMvPoly S n (φ_S (WeylAlgebra.of S v ^ p) - centerLift S n p (F_lift v))) = 0 := by
      rw [← toMvPoly_weylMap, hmap0, map_zero]
    let diffP := toMvPoly S n (φ_S (WeylAlgebra.of S v ^ p) - centerLift S n p (F_lift v))
    have hcoeff_p : ∀ d, ∃ t : S, diffP.coeff d = (p : S) * t := fun d =>
      hqB_ker _ (by
        have h := congrArg (fun r : P B n => r.coeff d) hpoly0
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
        exact h)
    choose t ht using hcoeff_p
    refine ⟨ofMvPoly S n (∑ d ∈ diffP.support, monomial d (t d)), ?_⟩
    apply toMvPoly_injective S n
    rw [map_smul, toMvPoly_ofMvPoly]
    change diffP = (p : S) • ∑ d ∈ diffP.support, monomial d (t d)
    conv_lhs => rw [diffP.as_sum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => by rw [smul_monomial, smul_eq_mul, ht d]
  have hgp_not_unit : ¬ IsUnit gp := by
    intro hu; have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨q, hq_irred, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hgp_not_unit hgp_monic.ne_zero
  have : (Ideal.span ({q} : Set (Polynomial (ZMod p)))).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hq_irred
  let Iq : Ideal (Polynomial (ZMod p)) := Ideal.span ({q} : Set (Polynomial (ZMod p)))
  let F : Type := Polynomial (ZMod p) ⧸ Iq
  let _ : Field F := Ideal.Quotient.field Iq
  let mkq : Polynomial (ZMod p) →+* F := Ideal.Quotient.mk Iq
  have : CharP F p := charP_of_injective_ringHom (mkq.comp Polynomial.C).injective p
  let πB : B →+* F := Ideal.Quotient.lift Igp mkq
    (fun r hr => by
      change r ∈ Ideal.span ({gp} : Set (Polynomial (ZMod p))) at hr
      rw [Ideal.mem_span_singleton] at hr
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change r ∈ Ideal.span ({q} : Set (Polynomial (ZMod p)))
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hq_dvd hr)
  let πS : S →+* F := πB.comp qB
  let π : R →+* F := πS.comp ψ
  let φ₀ : P F n →ₐ[F] P F n := MvPolynomial.aeval (fun v => MvPolynomial.map πS (F_lift v))
  refine ⟨p, hp, hmp, F, inferInstance, inferInstance, π, φ₀, ?_, ?_, ?_⟩
  · exact (hW0_unit.map πS).ne_zero
  · exact isPoissonEndomorphism_of_lift hp hS_ptf φ_S πS F_lift hModW_lift
  · intro f
    have hcomp_φ : weylAlgHom_baseChange π φ_R = weylAlgHom_baseChange πS φ_S := by
      apply AlgHom.ext; intro a
      have h1 : ∀ r : F, (weylAlgHom_baseChange π φ_R).toRingHom (algebraMap F (W F n) r) =
          (weylAlgHom_baseChange πS φ_S).toRingHom (algebraMap F (W F n) r) := fun r => by simp
      have h2 : ∀ v : Fin n ⊕ Fin n, (weylAlgHom_baseChange π φ_R).toRingHom (WeylAlgebra.of F v) =
          (weylAlgHom_baseChange πS φ_S).toRingHom (WeylAlgebra.of F v) := fun v => by
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, weylAlgHom_baseChange, weylLift_of]
        have hcomp : weylMap (n := n) π = (weylMap (n := n) πS).comp (weylMap (n := n) ψ) :=
          weylRingHom_ext (fun r => by simp [π]) (fun w => by simp)
        rw [hcomp, RingHom.comp_apply]
        congr 1
        rw [← weylMap_of ψ v, weylAlgHom_baseChange_weylMap]
      exact congrFun (congrArg DFunLike.coe (weylRingHom_ext h1 h2)) a
    rw [hcomp_φ]
    induction f using MvPolynomial.induction_on with
    | C r => simp [centerEmb]
    | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | mul_X f v ih =>
      rw [map_mul, map_mul, ih, map_mul, MvPolynomial.aeval_X, map_mul]
      congr 1
      have hXv : centerEmb F n p (X v) = WeylAlgebra.of F v ^ p := by
        simp only [centerEmb, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]
      rw [hXv, ← weylMap_of πS v, ← map_pow, weylAlgHom_baseChange_weylMap]
      obtain ⟨t, ht⟩ := hModW_lift v
      have hmap := congrArg (weylMap πS) ht
      have hpF : (p : F) = 0 := CharP.cast_eq_zero F p
      rw [map_sub, Algebra.smul_def, map_mul, weylMap_algebraMap, map_natCast,
        hpF, map_zero, zero_mul, sub_eq_zero, weylMap_centerLift,
        centerLift_eq_centerEmb] at hmap
      exact hmap

/-- Ultraproduct of a family of fields `F : ℕ → Type` along an ultrafilter `𝒰 : Ultrafilter ℕ`. -/
def ultraIdeal (F : ℕ → Type) [∀ m, Field (F m)] (𝒰 : Ultrafilter ℕ) : Ideal (∀ m, F m) where
  carrier := {f | {m | f m = 0} ∈ 𝒰}
  add_mem' {f g} hf hg := Filter.mem_of_superset (Filter.inter_mem hf hg) fun m ⟨h1, h2⟩ => by
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    simp [h1, h2]
  zero_mem' := by
    change {m | (0 : F m) = 0} ∈ (𝒰 : Filter ℕ)
    simp
  smul_mem' c {f} hf := Filter.mem_of_superset hf fun m h => by
    simp only [Set.mem_setOf_eq] at h ⊢
    simp [h]

lemma ultraIdeal_isMaximal (F : ℕ → Type) [∀ m, Field (F m)] (𝒰 : Ultrafilter ℕ) :
    (ultraIdeal F 𝒰).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h1
    have hemp : (∅ : Set ℕ) ∈ (𝒰 : Filter ℕ) := by
      have heq : {m | (1 : F m) = 0} = (∅ : Set ℕ) := by ext m; simp
      rw [← heq]; exact h1
    exact Filter.empty_notMem (𝒰 : Filter ℕ) hemp
  · intro J f hIJ hf_not hfJ
    have hne : {m | f m ≠ 0} ∈ (𝒰 : Filter ℕ) :=
      Ultrafilter.compl_mem_iff_notMem.mpr hf_not
    let g : ∀ m, F m := fun m => (f m)⁻¹
    have h1_sub : 1 - g * f ∈ ultraIdeal F 𝒰 :=
      Filter.mem_of_superset hne fun m hm => by
        simp only [Set.mem_setOf_eq] at hm ⊢
        simp [g, inv_mul_cancel₀ hm]
    have h1 : (1 : ∀ m, F m) = (1 - g * f) + g * f := by ring
    rw [h1]
    exact J.add_mem (hIJ h1_sub) (J.mul_mem_left g hfJ)

/-- Ultraproduct contradiction: given char-`p_m` Poisson specializations `φ₀m m` of degree `≤ d`
with `p_m > m` and witnesses `w D` nonvanishing for `D ≤ m`, derive `False` from `hPC`. -/
lemma ultraproduct_poisson_contra {n : ℕ} {R : Type*} [CommRing R]
    (hPC : ∀ (K : Type) [Field K] [CharZero K], PoissonConjectureFor K n)
    (φ_R : W R n →ₐ[R] W R n) (v₀ : Fin n ⊕ Fin n) (d : ℕ)
    (w : ℕ → R)
    (hw_prop : ∀ D (F : Type) [Field F] (π : R →+* F), π (w D) ≠ 0 →
      ∀ a : W F n, (toMvPoly F n a).totalDegree ≤ D →
        weylAlgHom_baseChange π φ_R a ≠ WeylAlgebra.of F v₀)
    (pm : ℕ → ℕ) (hpm_prime : ∀ m, (pm m).Prime) (hpm_gt : ∀ m, m < pm m)
    (Fm : ℕ → Type) [∀ m, Field (Fm m)] [∀ m, CharP (Fm m) (pm m)]
    (πm : ∀ m, R →+* Fm m) (φ₀m : ∀ m, P (Fm m) n →ₐ[Fm m] P (Fm m) n)
    (hπm_Wm : ∀ m, πm m (∏ D ∈ Finset.range (m + 1), w D) ≠ 0)
    (hφ₀m_pois : ∀ m, IsPoissonEndomorphism (φ₀m m))
    (hφ₀m_cent : ∀ m (f : P (Fm m) n),
      weylAlgHom_baseChange (πm m) φ_R (centerEmb (Fm m) n (pm m) f) =
        centerEmb (Fm m) n (pm m) (φ₀m m f))
    (hφ₀m_deg : ∀ m v, (φ₀m m (X v)).totalDegree ≤ d) : False := by
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  let 𝔪 := ultraIdeal Fm 𝒰
  have : 𝔪.IsMaximal := ultraIdeal_isMaximal Fm 𝒰
  let K : Type := (∀ m, Fm m) ⧸ 𝔪
  let _ : Field K := Ideal.Quotient.field 𝔪
  let mkK : (∀ m, Fm m) →+* K := Ideal.Quotient.mk 𝔪
  have : CharZero K := by
    have hnat_zero : ∀ r : ℕ, (r : K) = 0 → r = 0 := by
      intro r hr
      by_contra hr0
      have hmem : {m | ((r : ℕ) : Fm m) = 0} ∈ (𝒰 : Filter ℕ) := by
        have hmk : mkK (fun m => (r : Fm m)) = 0 := by
          have h1 : (fun m => (r : Fm m)) = ((r : ℕ) : ∀ m, Fm m) := by funext m; simp
          rw [h1, map_natCast mkK r]; exact hr
        exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
      have hcof : {m | r ≤ m} ∈ (𝒰 : Filter ℕ) :=
        Ultrafilter.of_le Filter.cofinite (Filter.mem_cofinite.mpr (by
          convert Set.finite_lt_nat r using 1; ext m; simp))
      obtain ⟨m, hm1, hm2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hmem hcof)
      have hdvd : pm m ∣ r := (CharP.cast_eq_zero_iff (Fm m) (pm m) r).mp hm1
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hdvd
      have hrm : r ≤ m := hm2
      have := hpm_gt m
      omega
    refine ⟨fun r s hrs => ?_⟩
    rcases le_total s r with hsr | hrs'
    · have h0 := hnat_zero (r - s) (by rw [Nat.cast_sub hsr, hrs, sub_self]); omega
    · have h0 := hnat_zero (s - r) (by rw [Nat.cast_sub hrs', hrs, sub_self]); omega
  let Φ_X : (Fin n ⊕ Fin n) → P K n := fun v =>
    ∑ e ∈ monLeFinset n d, monomial e (mkK fun m => (φ₀m m (X v)).coeff e)
  let Φ : P K n →ₐ[K] P K n := MvPolynomial.aeval Φ_X
  let projm : ∀ m, P (∀ k, Fm k) n →+* P (Fm m) n := fun m =>
    MvPolynomial.map (Pi.evalRingHom Fm m)
  let quotP : P (∀ m, Fm m) n →+* P K n := MvPolynomial.map mkK
  have hΦ_lift : ∀ v, quotP (∑ e ∈ monLeFinset n d, monomial e (fun m => (φ₀m m (X v)).coeff e)) = Φ (X v) := by
    intro v; simp [quotP, Φ, Φ_X, map_sum, MvPolynomial.map_monomial]
  have hproj_lift : ∀ m v, projm m (∑ e ∈ monLeFinset n d, monomial e (fun k => (φ₀m k (X v)).coeff e)) = φ₀m m (X v) := by
    intro m v
    simp only [projm, map_sum, MvPolynomial.map_monomial, Pi.evalRingHom_apply]
    exact (poly_eq_sum_monLeFinset (hφ₀m_deg m v)).symm
  have hΦ_pois : IsPoissonEndomorphism Φ := by
    intro v w
    let Fv : P (∀ m, Fm m) n := ∑ e ∈ monLeFinset n d, monomial e (fun m => (φ₀m m (X v)).coeff e)
    let Fw : P (∀ m, Fm m) n := ∑ e ∈ monLeFinset n d, monomial e (fun m => (φ₀m m (X w)).coeff e)
    rw [← hΦ_lift v, ← hΦ_lift w, ← map_poissonBracket]
    have h0 : MvPolynomial.poissonBracket Fv Fw = MvPolynomial.poissonBracket (X v) (X w) := by
      ext e m
      have hm := congrArg (fun r : P (Fm m) n => r.coeff e) (hφ₀m_pois m v w)
      rw [← hproj_lift m v, ← hproj_lift m w, ← map_poissonBracket] at hm
      have hm' : (projm m (MvPolynomial.poissonBracket Fv Fw)).coeff e =
          (projm m (MvPolynomial.poissonBracket (X v) (X w))).coeff e := by
        rw [hm, map_poissonBracket]
        simp [projm]
      simpa only [projm, MvPolynomial.coeff_map, Pi.evalRingHom_apply] using hm'
    rw [h0, map_poissonBracket]
    simp [quotP]
  have hΦ_bij : Function.Bijective Φ := hPC K Φ hΦ_pois
  choose ψ_K hψ_K using fun v : Fin n ⊕ Fin n => hΦ_bij.2 (X v)
  let D₀ : ℕ := Finset.univ.sup fun v : Fin n ⊕ Fin n => (ψ_K v).totalDegree
  have hlift_ψ : ∀ v : Fin n ⊕ Fin n, ∃ g : P (∀ m, Fm m) n, quotP g = ψ_K v ∧
      ∀ m, (projm m g).totalDegree ≤ D₀ := by
    intro v
    have hdeg : (ψ_K v).totalDegree ≤ D₀ :=
      Finset.le_sup (f := fun w => (ψ_K w).totalDegree) (Finset.mem_univ v)
    choose c hc using fun e => Ideal.Quotient.mk_surjective ((ψ_K v).coeff e)
    refine ⟨∑ e ∈ monLeFinset n D₀, monomial e (c e), ?_, ?_⟩
    · simp only [quotP, map_sum, MvPolynomial.map_monomial]
      conv_rhs => rw [poly_eq_sum_monLeFinset hdeg]
      refine Finset.sum_congr rfl fun e _ => by rw [hc e]
    · intro m
      simp only [projm, map_sum, MvPolynomial.map_monomial, Pi.evalRingHom_apply]
      refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
      refine Finset.sup_le fun e he => ?_
      exact le_trans (MvPolynomial.totalDegree_monomial_le e (c e m)) (mem_monLeFinset_iff.mp he)
  choose ψ_seq hψ_seq_quot hψ_seq_deg using hlift_ψ
  let F_seq : (Fin n ⊕ Fin n) → P (∀ m, Fm m) n := fun v =>
    ∑ e ∈ monLeFinset n d, monomial e (fun m => (φ₀m m (X v)).coeff e)
  let Φ_seq : P (∀ m, Fm m) n →ₐ[∀ m, Fm m] P (∀ m, Fm m) n := MvPolynomial.aeval F_seq
  let Ψ_seq : P (∀ m, Fm m) n →ₐ[∀ m, Fm m] P (∀ m, Fm m) n := MvPolynomial.aeval ψ_seq
  have hquot_Φ : ∀ g, quotP (Φ_seq g) = Φ (quotP g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C r => simp [quotP, Φ_seq]
    | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih, map_mul, MvPolynomial.map_X, map_mul]
      congr 1
      rw [show Φ_seq (X v) = F_seq v from MvPolynomial.aeval_X F_seq v]
      exact hΦ_lift v
  have hquot_Ψ : ∀ g, quotP (Ψ_seq g) = MvPolynomial.aeval ψ_K (quotP g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C r => simp [quotP, Ψ_seq]
    | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih, map_mul, MvPolynomial.map_X, map_mul]
      simp [Ψ_seq, hψ_seq_quot v]
  have hproj_Φ : ∀ m g, projm m (Φ_seq g) = φ₀m m (projm m g) := by
    intro m g
    induction g using MvPolynomial.induction_on with
    | C r => simp [projm, Φ_seq]
    | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih, map_mul, MvPolynomial.map_X, map_mul]
      congr 1
      rw [show Φ_seq (X v) = F_seq v from MvPolynomial.aeval_X F_seq v]
      exact hproj_lift m v
  let Ψ_m : ∀ m, P (Fm m) n →ₐ[Fm m] P (Fm m) n := fun m =>
    MvPolynomial.aeval (fun v => projm m (ψ_seq v))
  have hproj_Ψ : ∀ m g, projm m (Ψ_seq g) = Ψ_m m (projm m g) := by
    intro m g
    induction g using MvPolynomial.induction_on with
    | C r => simp [projm, Ψ_seq, Ψ_m]
    | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih, map_mul, MvPolynomial.map_X, map_mul]
      simp [Ψ_seq, Ψ_m]
  have hΦΨ_K : ∀ v : Fin n ⊕ Fin n, quotP (Φ_seq (ψ_seq v) - X v) = 0 := by
    intro v; rw [map_sub, hquot_Φ, hψ_seq_quot, hψ_K v]; simp [quotP]
  have hΨΦ_K : ∀ v : Fin n ⊕ Fin n, quotP (Ψ_seq (F_seq v) - X v) = 0 := by
    intro v
    rw [map_sub, hquot_Ψ, hΦ_lift]
    have hcomp_id : MvPolynomial.aeval ψ_K (Φ (X v)) = X v := by
      apply hΦ_bij.1
      have hΦ_aeval : ∀ g : P K n, Φ (MvPolynomial.aeval ψ_K g) = g := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C r => simp
        | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
        | mul_X g w ih => rw [map_mul, map_mul, ih, MvPolynomial.aeval_X, hψ_K w]
      rw [hΦ_aeval]
    rw [hcomp_id]; simp [quotP]
  have hgood_poly : ∀ g : P (∀ m, Fm m) n, quotP g = 0 → {m | projm m g = 0} ∈ 𝒰 := by
    intro g hg
    have hsupp : ∀ e ∈ g.support, {m | g.coeff e m = 0} ∈ 𝒰 := by
      intro e _
      have he := congrArg (fun r : P K n => r.coeff e) hg
      simp only [quotP, MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at he
      exact Ideal.Quotient.eq_zero_iff_mem.mp he
    have hinter : (⋂ e ∈ g.support, {m | g.coeff e m = 0}) ∈ 𝒰 :=
      (Filter.biInter_finset_mem g.support).mpr hsupp
    refine Filter.mem_of_superset hinter fun m hm => ?_
    ext e
    simp only [projm, MvPolynomial.coeff_map, Pi.evalRingHom_apply, MvPolynomial.coeff_zero]
    by_cases he : e ∈ g.support
    · exact Set.mem_iInter₂.mp hm e he
    · exact congrFun (MvPolynomial.notMem_support_iff.mp he) m
  have hS1 : (⋂ v : Fin n ⊕ Fin n, {m | projm m (Φ_seq (ψ_seq v) - X v) = 0}) ∈ 𝒰 :=
    Filter.iInter_mem.mpr fun v => hgood_poly _ (hΦΨ_K v)
  have hS2 : (⋂ v : Fin n ⊕ Fin n, {m | projm m (Ψ_seq (F_seq v) - X v) = 0}) ∈ 𝒰 :=
    Filter.iInter_mem.mpr fun v => hgood_poly _ (hΨΦ_K v)
  have hS3 : {m | D₀ ≤ m} ∈ (𝒰 : Filter ℕ) :=
    Ultrafilter.of_le Filter.cofinite (Filter.mem_cofinite.mpr (by
      convert Set.finite_lt_nat D₀ using 1; ext m; simp))
  obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ := Filter.nonempty_of_mem (Filter.inter_mem (Filter.inter_mem hS1 hS2) hS3)
  have hm3' : D₀ ≤ m := hm3
  have hφ₀_left : ∀ g : P (Fm m) n, φ₀m m (Ψ_m m g) = g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C r => simp
    | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih]; congr 1
      have hv : projm m (Φ_seq (ψ_seq v) - X v) = 0 := Set.mem_iInter.mp hm1 v
      rw [map_sub, sub_eq_zero, hproj_Φ] at hv
      simpa [Ψ_m, projm] using hv
  have hφ₀_right : ∀ g : P (Fm m) n, Ψ_m m (φ₀m m g) = g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C r => simp
    | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | mul_X g v ih =>
      rw [map_mul, map_mul, ih]; congr 1
      have hv : projm m (Ψ_seq (F_seq v) - X v) = 0 := Set.mem_iInter.mp hm2 v
      rw [map_sub, sub_eq_zero, hproj_Ψ, hproj_lift] at hv
      simpa [projm] using hv
  have hφ₀_bij : Function.Bijective (φ₀m m) :=
    Function.bijective_iff_has_inverse.mpr ⟨Ψ_m m, hφ₀_right, hφ₀_left⟩
  let φ_m := weylAlgHom_baseChange (πm m) φ_R
  have hφm_bij : Function.Bijective φ_m :=
    bijective_of_centerMap_bijective (hpm_prime m) φ_m (φ₀m m) (hφ₀m_cent m) hφ₀_bij
  obtain ⟨am, ham⟩ := hφm_bij.2 (WeylAlgebra.of (Fm m) v₀)
  have ham_ne : am ≠ 0 := by
    intro h0; rw [h0, map_zero] at ham
    have h1 := congrArg (toMvPoly (Fm m) n) ham
    rw [map_zero] at h1
    have hX : toMvPoly (Fm m) n (WeylAlgebra.of (Fm m) v₀) = X v₀ := by
      rcases v₀ with i | i
      · simp [toMvPoly, toEnd]
      · change (toEnd (Fm m) n (WeylAlgebra.of (Fm m) (Sum.inr i))) 1 = X (Sum.inr i)
        simp only [toEnd, weylLift_of, LinearMap.sub_apply, LinearMap.mulLeft_apply, mul_one]
        simp
    rw [hX] at h1
    exact MvPolynomial.X_ne_zero v₀ h1.symm
  have ham_pow : am ^ pm m = centerEmb (Fm m) n (pm m) (projm m (ψ_seq v₀)) := by
    apply hφm_bij.1
    rw [map_pow, ham, hφ₀m_cent m]
    have hXv : WeylAlgebra.of (Fm m) v₀ ^ pm m = centerEmb (Fm m) n (pm m) (X v₀) := by
      simp only [centerEmb, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]
    rw [hXv]; congr 1
    have hv : projm m (Φ_seq (ψ_seq v₀) - X v₀) = 0 := Set.mem_iInter.mp hm1 v₀
    rw [map_sub, sub_eq_zero, hproj_Φ] at hv
    simpa [projm] using hv.symm
  have ham_deg : (toMvPoly (Fm m) n am).totalDegree ≤ D₀ := by
    have h1 := congrArg (fun z => (toMvPoly (Fm m) n z).totalDegree) ham_pow
    rw [toMvPoly_pow_totalDegree ham_ne, toMvPoly_centerEmb,
      totalDegree_expand (hpm_prime m).pos] at h1
    rw [Nat.eq_of_mul_eq_mul_left (hpm_prime m).pos h1]
    exact hψ_seq_deg v₀ m
  have hπ_wD0 : πm m (w D₀) ≠ 0 := by
    intro h0; apply hπm_Wm m
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) h0
  exact hw_prop D₀ (Fm m) (πm m) hπ_wD0 am ham_deg ham

/-- Main theorem: `PoissonConjectureFor` over all char-0 fields implies `DixmierConjectureFor`
over all char-0 fields! -/
theorem dixmier_of_poisson (n : ℕ)
    (hPC : ∀ (K : Type) [Field K] [CharZero K], PoissonConjectureFor K n)
    (L : Type) [Field L] [CharZero L] : DixmierConjectureFor L n := by
  classical
  intro φ
  refine ⟨weylAlgHom_injective φ, ?_⟩
  -- It suffices to show every generator `WeylAlgebra.of L v` is in `Set.range φ`
  suffices hgen : ∀ v₀ : Fin n ⊕ Fin n, WeylAlgebra.of L v₀ ∈ Set.range φ by
    intro b
    obtain ⟨f, rfl⟩ := ofMvPoly_surjective L n b
    induction f using MvPolynomial.induction_on' with
    | monomial d s =>
      rw [ofMvPoly_monomial]
      have hwx : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
          (l.map (fun i => wx L i ^ e i)).prod ∈ Set.range φ := by
        intro l e; induction l with
        | nil => exact ⟨1, map_one _⟩
        | cons i l ih =>
          obtain ⟨a, ha⟩ := hgen (Sum.inl i)
          obtain ⟨b, hb⟩ := ih
          exact ⟨a ^ e i * b, by rw [map_mul, map_pow, ha, hb]; rfl⟩
      have hwy : ∀ (l : List (Fin n)) (e : Fin n → ℕ),
          (l.map (fun i => wy L i ^ e i)).prod ∈ Set.range φ := by
        intro l e; induction l with
        | nil => exact ⟨1, map_one _⟩
        | cons i l ih =>
          obtain ⟨a, ha⟩ := hgen (Sum.inr i)
          obtain ⟨b, hb⟩ := ih
          exact ⟨a ^ e i * b, by rw [map_mul, map_pow, ha, hb]; rfl⟩
      obtain ⟨ax, hax⟩ := hwx (List.finRange n) (fun i => d (Sum.inl i))
      obtain ⟨ay, hay⟩ := hwy (List.finRange n) (fun i => d (Sum.inr i))
      exact ⟨s • (ax * ay), by rw [map_smul, map_mul, hax, hay]; rfl⟩
    | add f₁ f₂ h₁ h₂ =>
      obtain ⟨a₁, ha₁⟩ := h₁; obtain ⟨a₂, ha₂⟩ := h₂
      exact ⟨a₁ + a₂, by rw [map_add, ha₁, ha₂, map_add]⟩
  -- Proof by contradiction: assume `WeylAlgebra.of L v₀ ∉ Set.range φ`
  intro v₀
  by_contra hnot
  -- Collect all coefficients of `toMvPoly L n (φ (of L v))` into a finite tuple `a : Fin k → L`
  let coeffSet : Finset L := Finset.univ.biUnion fun v : Fin n ⊕ Fin n =>
    (toMvPoly L n (φ (WeylAlgebra.of L v))).support.image
      (toMvPoly L n (φ (WeylAlgebra.of L v))).coeff
  let k : ℕ := coeffSet.card
  let eCoeff : Fin k ≃ coeffSet := (Fintype.equivFinOfCardEq (by simp [k])).symm
  let a : Fin k → L := fun j => (eCoeff j).val
  let evL : MvPolynomial (Fin k) ℤ →+* L := MvPolynomial.eval₂Hom (Int.castRingHom L) a
  let R : Subring L := evL.range
  -- Lift `φ` to `φ_R : W R n →ₐ[R] W R n`
  have hlift_gen : ∀ v : Fin n ⊕ Fin n, ∃ g : W R n, weylMap R.subtype g = φ (WeylAlgebra.of L v) := by
    intro v
    let P_v := toMvPoly L n (φ (WeylAlgebra.of L v))
    have hmem : ∀ d ∈ P_v.support, P_v.coeff d ∈ R := by
      intro d hd
      have hc : P_v.coeff d ∈ coeffSet :=
        Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
      let j : Fin k := eCoeff.symm ⟨P_v.coeff d, hc⟩
      refine ⟨MvPolynomial.X j, ?_⟩
      simp [evL, a, j]
    let PR : P R n := ∑ d ∈ P_v.support.attach,
      monomial d.val ⟨P_v.coeff d.val, hmem d.val d.prop⟩
    refine ⟨ofMvPoly R n PR, ?_⟩
    apply toMvPoly_injective L n
    rw [toMvPoly_weylMap, toMvPoly_ofMvPoly]
    simp only [PR, map_sum, MvPolynomial.map_monomial, Subring.coe_subtype]
    conv_rhs => change P_v; rw [P_v.as_sum]
    rw [Finset.sum_attach P_v.support (fun d => monomial d (P_v.coeff d))]
  choose genR hgenR using hlift_gen
  have hweylMap_inj : Function.Injective (weylMap R.subtype : W R n →+* W L n) := by
    intro x y hxy
    apply toMvPoly_injective R n
    apply MvPolynomial.map_injective R.subtype Subtype.val_injective
    rw [← toMvPoly_weylMap, ← toMvPoly_weylMap, hxy]
  let φ_R : W R n →ₐ[R] W R n := weylLift genR
    (fun i j => hweylMap_inj (by rw [map_mul, map_mul, hgenR, hgenR, ← map_mul, ← map_mul, WeylAlgebra.of_inl_mul_comm]))
    (fun i j => hweylMap_inj (by rw [map_mul, map_mul, hgenR, hgenR, ← map_mul, ← map_mul, WeylAlgebra.of_inr_mul_comm]))
    (fun i j hij => hweylMap_inj (by rw [map_mul, map_mul, hgenR, hgenR, ← map_mul, ← map_mul, WeylAlgebra.of_inl_mul_of_inr_of_ne L hij]))
    (fun i => hweylMap_inj (by rw [map_mul, map_add, map_mul, map_one, hgenR, hgenR, ← map_mul, ← map_mul, ← map_one φ, ← map_add, WeylAlgebra.of_inl_mul_of_inr_self]))
  have hφ_base : weylAlgHom_baseChange R.subtype φ_R = φ := by
    apply AlgHom.ext; intro x
    have h1 : ∀ r : L, (weylAlgHom_baseChange R.subtype φ_R).toRingHom (algebraMap L (W L n) r) =
        φ.toRingHom (algebraMap L (W L n) r) := fun r => by simp
    have h2 : ∀ v : Fin n ⊕ Fin n, (weylAlgHom_baseChange R.subtype φ_R).toRingHom (WeylAlgebra.of L v) =
        φ.toRingHom (WeylAlgebra.of L v) := fun v => by
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, weylAlgHom_baseChange, weylLift_of,
        φ_R, hgenR v]
    exact congrFun (congrArg DFunLike.coe (weylRingHom_ext h1 h2)) x
  rw [← hφ_base] at hnot
  -- Degree bound `d` for `φ_R`
  let d : ℕ := Finset.univ.sup fun v : Fin n ⊕ Fin n => (toMvPoly R n (φ_R (WeylAlgebra.of R v))).totalDegree
  -- For each degree `D`, get non-surjectivity witness `w D ∈ R \ {0}`
  choose w hw_ne hw_prop using fun D => exists_nonSurj_witness R φ_R v₀ hnot D
  -- For each `m : ℕ`, let `W_m = ∏_{D ≤ m} w D ≠ 0` and specialize to char `p_m > m`!
  let Wm : ℕ → R := fun m => ∏ D ∈ Finset.range (m + 1), w D
  have hWm_ne : ∀ m, Wm m ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun D _ => hw_ne D
  have hspec : ∀ m : ℕ, ∃ (p : ℕ) (_ : p.Prime) (_ : m < p) (F : Type) (_ : Field F) (_ : CharP F p)
      (π : R →+* F) (φ₀ : P F n →ₐ[F] P F n),
      π (Wm m) ≠ 0 ∧ IsPoissonEndomorphism φ₀ ∧
      (∀ f : P F n, weylAlgHom_baseChange π φ_R (centerEmb F n p f) = centerEmb F n p (φ₀ f)) :=
    fun m => exists_charP_specialization a R rfl φ_R (Wm m) (hWm_ne m) m
  choose pm hpm_prime hpm_gt Fm hFm_field hFm_charP πm φ₀m hπm_Wm hφ₀m_pois hφ₀m_cent using hspec
  letI : ∀ m, Field (Fm m) := hFm_field
  letI : ∀ m, CharP (Fm m) (pm m) := hFm_charP
  -- Every `φ₀m m (X v)` has total degree `≤ d`!
  have hφ₀m_deg : ∀ m v, (φ₀m m (X v)).totalDegree ≤ d := by
    intro m v
    rw [centerMap_totalDegree_eq (hpm_prime m) (weylAlgHom_baseChange (πm m) φ_R) (φ₀m m) (hφ₀m_cent m) v]
    have hmap : toMvPoly (Fm m) n (weylAlgHom_baseChange (πm m) φ_R (WeylAlgebra.of (Fm m) v)) =
        MvPolynomial.map (πm m) (toMvPoly R n (φ_R (WeylAlgebra.of R v))) := by
      rw [← weylMap_of (πm m) v, weylAlgHom_baseChange_weylMap, toMvPoly_weylMap]
    rw [hmap]
    have hdeg_map : (MvPolynomial.map (πm m) (toMvPoly R n (φ_R (WeylAlgebra.of R v)))).totalDegree ≤
        (toMvPoly R n (φ_R (WeylAlgebra.of R v))).totalDegree := by
      refine Finset.sup_le fun e he => ?_
      exact MvPolynomial.le_totalDegree (MvPolynomial.support_map_subset (πm m) _ he)
    exact le_trans hdeg_map
      (Finset.le_sup (f := fun w => (toMvPoly R n (φ_R (WeylAlgebra.of R w))).totalDegree) (Finset.mem_univ v))
  exact ultraproduct_poisson_contra hPC φ_R v₀ d w hw_prop pm hpm_prime hpm_gt Fm πm φ₀m
    hπm_Wm hφ₀m_pois hφ₀m_cent hφ₀m_deg

end UltraproductProof

end DixmierPoissonProof

theorem OMA.solution :
    type_of% @Arxiv.«math.0608009».dixmier_conjecture.variants.poisson_implication :=
  DixmierPoissonProof.dixmier_of_poisson
