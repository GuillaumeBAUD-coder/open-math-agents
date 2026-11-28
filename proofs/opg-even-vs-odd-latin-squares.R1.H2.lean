import OMAReductions.R_opg_even_vs_odd_latin_squares_R1
import Mathlib

/-!
# Glynn's theorem: Alon–Tarsi conjecture for `n = p - 1` (step H2 of opg-even-vs-odd-latin-squares.R1)

We prove that for every positive even integer `n = m + 1` such that `p = m + 2 = n + 1` is prime,
the numbers of even and odd reduced Latin squares of order `n` differ.

Proof outline (David G. Glynn, 2010):
1. Over `ZMod p`, evaluate `S(A) = ∑ y : Fin n → ZMod p, ∏ i, (A *ᵥ y) i ^ (p - 1)` in two ways:
   - Linear-algebraically: `S(A) = (-1)^n * A.det ^ (p - 1)` (bijection when `det A ≠ 0`; kernel shift
     when `det A = 0`).
   - By multinomial expansion: `S(A) = (-1)^n * eval A (glynnPoly n p)`, where `glynnPoly n p`
     sums `monomial E (∏ i, multinomial (E i))` over all `n × n` nonnegative integer matrices `E`
     with all row and column sums equal to `p - 1`.
2. Both `XMat.det ^ (p - 1)` and `glynnPoly n p` have individual degree at most `p - 1` in each
   entry `X (i, j)`, so by `MvPolynomial.eq_zero_of_eval_eq_zero` they are equal as polynomials.
3. For `n = p - 1`, the coefficient of `∏ i j, X (i, j)` in `glynnPoly n p` is
   `((p - 1)! : ZMod p) ^ (p - 1) = (-1) ^ (p - 1) ≠ 0` by Wilson's theorem.
4. Over `ℤ`, the coefficient of `∏ i j, X (i, j)` in `XMat.det ^ n` equals
   `Perm.sign (Equiv.prodComm (Fin n) (Fin n)) * (#{even Latin squares} - #{odd Latin squares})`.
   Reducing modulo `p` shows `#{even} ≠ #{odd}`, and `R1`'s normalization transfers this to
   reduced Latin squares.
-/

namespace GlynnAlonTarsi

open OMA.S_opg_even_vs_odd_latin_squares
open OMA.R_opg_even_vs_odd_latin_squares_R1
open Equiv Finset MvPolynomial Matrix

/- ### Part 1: Finite-field power sums and Glynn's polynomial identity -/

private lemma sum_pow_zmod_sub_one (p : ℕ) [Fact p.Prime] :
    ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hsub : p - 1 ≠ 0 := by omega
  calc ∑ x : ZMod p, x ^ (p - 1)
      = ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ (p - 1) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow hsub, zero_add]
    _ = ∑ _x ∈ Finset.univ.erase (0 : ZMod p), (1 : ZMod p) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        exact ZMod.pow_card_sub_one_eq_one (Finset.ne_of_mem_erase hx)
    _ = ((p - 1 : ℕ) : ZMod p) := by
        rw [Finset.sum_const, nsmul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card]
    _ = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_pow_zmod_lt (p : ℕ) [Fact p.Prime] {c : ℕ} (hc : c < p - 1) :
    ∑ x : ZMod p, x ^ c = 0 := by
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) c (by rw [ZMod.card]; exact hc)

private lemma glynnSum_eq_det_pow {n p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    ∑ y : Fin n → ZMod p, ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1) =
      (-1 : ZMod p) ^ n * A.det ^ (p - 1) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hsub : p - 1 ≠ 0 := by omega
  by_cases hdet : A.det = 0
  · rw [hdet, zero_pow hsub, mul_zero]
    have hker : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
      exact hdet
    obtain ⟨k, hk_mem, hk_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hAk : A *ᵥ k = 0 := by simpa [LinearMap.mem_ker, Matrix.toLin'_apply] using hk_mem
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, k j0 ≠ 0 := Function.ne_iff.mp hk_ne
    let e : {z : Fin n → ZMod p // z j0 = 0} × ZMod p ≃ (Fin n → ZMod p) :=
      { toFun := fun q => q.1.val + q.2 • k
        invFun := fun y => (⟨y - (y j0 * (k j0)⁻¹) • k, by simp [mul_assoc, inv_mul_cancel₀ hj0]⟩, y j0 * (k j0)⁻¹)
        left_inv := by
          rintro ⟨⟨z, hz⟩, t⟩
          have ht : (z + t • k) j0 * (k j0)⁻¹ = t := by
            simp [hz, mul_assoc, mul_inv_cancel₀ hj0]
          apply Prod.ext
          · apply Subtype.ext
            simp [hz, mul_assoc, mul_inv_cancel₀ hj0]
          · exact ht
        right_inv := fun y => by simp }
    calc ∑ y : Fin n → ZMod p, ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1)
        = ∑ q : {z : Fin n → ZMod p // z j0 = 0} × ZMod p,
            ∏ i : Fin n, (A *ᵥ (q.1.val + q.2 • k)) i ^ (p - 1) :=
          (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = ∑ z : {z : Fin n → ZMod p // z j0 = 0}, ∑ _t : ZMod p,
            ∏ i : Fin n, (A *ᵥ z.val) i ^ (p - 1) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAk, smul_zero, add_zero]
      _ = ∑ z : {z : Fin n → ZMod p // z j0 = 0},
            (p : ZMod p) * ∏ i : Fin n, (A *ᵥ z.val) i ^ (p - 1) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = 0 := by simp
  · obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
    let e : (Fin n → ZMod p) ≃ (Fin n → ZMod p) :=
      { toFun := A.mulVec
        invFun := ((U⁻¹ : (Matrix (Fin n) (Fin n) (ZMod p))ˣ) : Matrix _ _ _).mulVec
        left_inv := fun y => by
          rw [Matrix.mulVec_mulVec, ← hU, Units.inv_mul, Matrix.one_mulVec]
        right_inv := fun y => by
          rw [Matrix.mulVec_mulVec, ← hU, Units.mul_inv, Matrix.one_mulVec] }
    calc ∑ y : Fin n → ZMod p, ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1)
        = ∑ v : Fin n → ZMod p, ∏ i : Fin n, v i ^ (p - 1) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∏ _i : Fin n, ∑ t : ZMod p, t ^ (p - 1) :=
          (Fintype.prod_sum fun (_ : Fin n) (t : ZMod p) => t ^ (p - 1)).symm
      _ = ∏ _i : Fin n, (-1 : ZMod p) := by
          refine Finset.prod_congr rfl fun _ _ => sum_pow_zmod_sub_one p
      _ = (-1 : ZMod p) ^ n := by simp
      _ = (-1 : ZMod p) ^ n * A.det ^ (p - 1) := by
          rw [ZMod.pow_card_sub_one_eq_one hdet, mul_one]

private noncomputable def glynnSupport (n p : ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.piAntidiag (Finset.univ : Finset (Fin n)) (p - 1)).filter
    fun E => ∀ j : Fin n, ∑ i : Fin n, E i j = p - 1

private noncomputable def matToFinsupp {n : ℕ} (E : Fin n → Fin n → ℕ) : (Fin n × Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ij => E ij.1 ij.2

private lemma matToFinsupp_apply {n : ℕ} (E : Fin n → Fin n → ℕ) (ij : Fin n × Fin n) :
    matToFinsupp E ij = E ij.1 ij.2 := rfl

private lemma matToFinsupp_injective {n : ℕ} : Function.Injective (@matToFinsupp n) := by
  intro E1 E2 h
  funext i j
  have := DFunLike.congr_fun h (i, j)
  simpa [matToFinsupp_apply] using this

private noncomputable def glynnPoly (n p : ℕ) : MvPolynomial (Fin n × Fin n) (ZMod p) :=
  ∑ E ∈ glynnSupport n p,
    MvPolynomial.monomial (matToFinsupp E)
      (∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p))

private lemma eval_glynnPoly {n p : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    MvPolynomial.eval (fun ij : Fin n × Fin n => A ij.1 ij.2) (glynnPoly n p) =
      ∑ E ∈ glynnSupport n p,
        (∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
          ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j := by
  simp only [glynnPoly, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun E _ => ?_
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  rfl

private lemma glynnSum_eq_eval_glynnPoly {n p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    ∑ y : Fin n → ZMod p, ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1) =
      (-1 : ZMod p) ^ n * MvPolynomial.eval (fun ij => A ij.1 ij.2) (glynnPoly n p) := by
  let S := Fintype.piFinset fun _ : Fin n =>
    Finset.piAntidiag (Finset.univ : Finset (Fin n)) (p - 1)
  have hexpand : ∀ y : Fin n → ZMod p,
      ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1) =
        ∑ E ∈ S,
          ((∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
            ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j) *
            ∏ j : Fin n, y j ^ (∑ i : Fin n, E i j) := by
    intro y
    have hrow : ∀ i : Fin n,
        (A *ᵥ y) i ^ (p - 1) =
          ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (p - 1),
            (Nat.multinomial Finset.univ e : ZMod p) * ∏ j : Fin n, (A i j * y j) ^ e j := by
      intro i
      simpa [Matrix.mulVec, dotProduct] using
        Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n))
          (fun j => A i j * y j) (p - 1)
    calc ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1)
        = ∏ i : Fin n, ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (p - 1),
            (Nat.multinomial Finset.univ e : ZMod p) * ∏ j : Fin n, (A i j * y j) ^ e j :=
          Finset.prod_congr rfl fun i _ => hrow i
      _ = ∑ E ∈ S, ∏ i : Fin n,
            ((Nat.multinomial Finset.univ (E i) : ZMod p) *
              ∏ j : Fin n, (A i j * y j) ^ E i j) := by
          rw [← Finset.sum_prod_piFinset]
      _ = ∑ E ∈ S,
            ((∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
              ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j) *
              ∏ j : Fin n, y j ^ (∑ i : Fin n, E i j) := by
          refine Finset.sum_congr rfl fun E _ => ?_
          simp only [Finset.prod_mul_distrib, mul_pow]
          rw [← mul_assoc]
          congr 1
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [Finset.prod_pow_eq_pow_sum]
  calc ∑ y : Fin n → ZMod p, ∏ i : Fin n, (A *ᵥ y) i ^ (p - 1)
      = ∑ y : Fin n → ZMod p, ∑ E ∈ S,
          ((∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
            ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j) *
            ∏ j : Fin n, y j ^ (∑ i : Fin n, E i j) :=
        Finset.sum_congr rfl fun y _ => hexpand y
    _ = ∑ E ∈ S,
          ((∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
            ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j) *
            ∑ y : Fin n → ZMod p, ∏ j : Fin n, y j ^ (∑ i : Fin n, E i j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun E _ => (Finset.mul_sum ..).symm
    _ = ∑ E ∈ S,
          if (∀ j : Fin n, ∑ i : Fin n, E i j = p - 1) then
            (-1 : ZMod p) ^ n *
              ((∏ i : Fin n, (Nat.multinomial Finset.univ (E i) : ZMod p)) *
                ∏ i : Fin n, ∏ j : Fin n, A i j ^ E i j)
          else 0 := by
        refine Finset.sum_congr rfl fun E hE => ?_
        have hysum : ∑ y : Fin n → ZMod p, ∏ j : Fin n, y j ^ (∑ i : Fin n, E i j) =
            ∏ j : Fin n, ∑ t : ZMod p, t ^ (∑ i : Fin n, E i j) :=
          (Fintype.prod_sum fun (j : Fin n) (t : ZMod p) => t ^ (∑ i : Fin n, E i j)).symm
        rw [hysum]
        split_ifs with hcol
        · have hprod : ∏ j : Fin n, ∑ t : ZMod p, t ^ (∑ i : Fin n, E i j) = (-1 : ZMod p) ^ n := by
            calc ∏ j : Fin n, ∑ t : ZMod p, t ^ (∑ i : Fin n, E i j)
                = ∏ _j : Fin n, (-1 : ZMod p) :=
                  Finset.prod_congr rfl fun j _ => by rw [hcol j, sum_pow_zmod_sub_one p]
              _ = (-1 : ZMod p) ^ n := by simp
          rw [hprod, mul_comm]
        · have hlt : ∃ j0 : Fin n, ∑ i : Fin n, E i j0 < p - 1 := by
            by_contra! hge
            have htot : ∑ j : Fin n, ∑ i : Fin n, E i j = ∑ _j : Fin n, (p - 1) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              exact (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hE i)).1
            have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hge j)).mp htot.symm
            exact hcol fun j => (heq j (Finset.mem_univ j)).symm
          obtain ⟨j0, hj0⟩ := hlt
          have hz : ∏ j : Fin n, ∑ t : ZMod p, t ^ (∑ i : Fin n, E i j) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ j0) (sum_pow_zmod_lt p hj0)
          rw [hz, mul_zero]
    _ = (-1 : ZMod p) ^ n * MvPolynomial.eval (fun ij => A ij.1 ij.2) (glynnPoly n p) := by
        rw [← Finset.sum_filter, ← Finset.mul_sum, eval_glynnPoly]
        rfl

private noncomputable def XMat (n : ℕ) (R : Type*) [CommSemiring R] :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

private lemma det_XMat_mem_restrictDegree (n : ℕ) (R : Type*) [CommRing R] :
    (XMat n R).det ∈ MvPolynomial.restrictDegree (Fin n × Fin n) R 1 := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hprod : ∏ j : Fin n, XMat n R (σ j) j =
      MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (σ j, j) 1) (1 : R) := by
    simpa [XMat, MvPolynomial.X] using
      (MvPolynomial.monomial_sum_one (R := R) (Finset.univ : Finset (Fin n))
        (fun j => Finsupp.single (σ j, j) 1)).symm
  have hmem_mon : MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (σ j, j) 1) (1 : R) ∈
      MvPolynomial.restrictDegree (Fin n × Fin n) R 1 := by
    rw [MvPolynomial.mem_restrictDegree]
    intro s hs ij
    have hs_eq : s = ∑ j : Fin n, Finsupp.single (σ j, j) 1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
    rw [hs_eq, Finsupp.finsetSum_apply]
    have hterm : ∀ j : Fin n, (Finsupp.single (σ j, j) 1 : (Fin n × Fin n) →₀ ℕ) ij =
        if j = ij.2 ∧ σ ij.2 = ij.1 then 1 else 0 := by
      intro j
      rw [Finsupp.single_apply]
      by_cases hj : j = ij.2
      · subst hj
        simp [Prod.ext_iff]
      · have : (σ j, j) ≠ ij := fun h => hj (congrArg Prod.snd h)
        simp [this, hj]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    calc ({x ∈ Finset.univ | x = ij.2 ∧ σ ij.2 = ij.1} : Finset (Fin n)).card
        ≤ ({ij.2} : Finset (Fin n)).card := Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hx ⊢
          exact hx.1)
      _ = 1 := Finset.card_singleton _
  rw [hprod]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa [h] using hmem_mon
  · simpa [h] using Submodule.neg_mem _ hmem_mon

private lemma det_pow_mem_restrictDegree (n p : ℕ) :
    (XMat n (ZMod p)).det ^ (p - 1) ∈ MvPolynomial.restrictDegree (Fin n × Fin n) (ZMod p) (p - 1) := by
  have h1 := (MvPolynomial.mem_restrictDegree_iff_sup (p := (XMat n (ZMod p)).det) (n := 1)).mp
    (det_XMat_mem_restrictDegree n (ZMod p))
  rw [MvPolynomial.mem_restrictDegree_iff_sup]
  intro ij
  calc ((XMat n (ZMod p)).det ^ (p - 1)).degrees.count ij
      ≤ ((p - 1) • (XMat n (ZMod p)).det.degrees).count ij :=
        Multiset.count_le_of_le ij MvPolynomial.degrees_pow_le
    _ = (p - 1) * (XMat n (ZMod p)).det.degrees.count ij := Multiset.count_nsmul _ _ _
    _ ≤ (p - 1) * 1 := Nat.mul_le_mul_left (p - 1) (h1 ij)
    _ = p - 1 := mul_one _

private lemma glynnPoly_mem_restrictDegree (n p : ℕ) :
    glynnPoly n p ∈ MvPolynomial.restrictDegree (Fin n × Fin n) (ZMod p) (p - 1) := by
  refine Submodule.sum_mem _ fun E hE => ?_
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs ij
  have hs_eq : s = matToFinsupp E :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
  rw [hs_eq, matToFinsupp_apply]
  have hrow : ∑ j : Fin n, E ij.1 j = p - 1 :=
    (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hE).1 ij.1)).1
  calc E ij.1 ij.2 ≤ ∑ j : Fin n, E ij.1 j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ij.2)
    _ = p - 1 := hrow

private lemma det_pow_eq_glynnPoly (n p : ℕ) [Fact p.Prime] :
    (XMat n (ZMod p)).det ^ (p - 1) = glynnPoly n p := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero
  · intro v
    let A : Matrix (Fin n) (Fin n) (ZMod p) := Matrix.of fun i j => v (i, j)
    have heval_det : MvPolynomial.eval v ((XMat n (ZMod p)).det ^ (p - 1)) = A.det ^ (p - 1) := by
      rw [map_pow, RingHom.map_det]
      congr 1
      apply congrArg Matrix.det
      ext i j
      simp [XMat, A]
    have h1 := glynnSum_eq_det_pow A
    have h2 := glynnSum_eq_eval_glynnPoly A
    have hmul : (-1 : ZMod p) ^ n * A.det ^ (p - 1) =
        (-1 : ZMod p) ^ n * MvPolynomial.eval v (glynnPoly n p) := h1.symm.trans h2
    have hcancel : A.det ^ (p - 1) = MvPolynomial.eval v (glynnPoly n p) := by
      have hsq : (-1 : ZMod p) ^ n * (-1 : ZMod p) ^ n = 1 := by
        rw [← mul_pow]; norm_num
      have := congrArg ((-1 : ZMod p) ^ n * ·) hmul
      simpa only [← mul_assoc, hsq, one_mul] using this
    rw [map_sub, heval_det, hcancel, sub_self]
  · rw [ZMod.card]
    exact Submodule.sub_mem _ (det_pow_mem_restrictDegree n p) (glynnPoly_mem_restrictDegree n p)

private noncomputable def oneMonomial (n : ℕ) : (Fin n × Fin n) →₀ ℕ :=
  matToFinsupp fun _ _ => 1

private lemma coeff_oneMonomial_glynnPoly_ne_zero (p : ℕ) [Fact p.Prime] :
    MvPolynomial.coeff (oneMonomial (p - 1)) (glynnPoly (p - 1) p) ≠ 0 := by
  let n := p - 1
  have hmem : (fun (_ _ : Fin n) => (1 : ℕ)) ∈ glynnSupport n p := by
    simp only [glynnSupport, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, n]
  have hcoeff : MvPolynomial.coeff (oneMonomial n) (glynnPoly n p) =
      ∏ _i : Fin n, (Nat.multinomial (Finset.univ : Finset (Fin n)) (fun _ => 1) : ZMod p) := by
    rw [glynnPoly, MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial, oneMonomial, matToFinsupp_injective.eq_iff]
    rw [Finset.sum_ite_eq' (glynnSupport n p) (fun _ _ => 1), if_pos hmem]
  have hmult : Nat.multinomial (Finset.univ : Finset (Fin n)) (fun _ => 1) = n.factorial := by
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin n)) (fun _ => 1)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hspec
  rw [hcoeff]
  simp only [hmult, n, ZMod.wilsons_lemma, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  intro hzero
  have hsq : (-1 : ZMod p) ^ (p - 1) * (-1 : ZMod p) ^ (p - 1) = 1 := by
    rw [← mul_pow]; norm_num
  rw [hzero, zero_mul] at hsq
  exact zero_ne_one hsq

/- ### Part 2: Relating `coeff oneMonomial (XMat.det ^ n)` to Latin square signs -/

private noncomputable def latinEquivTuple (n : ℕ) :
    {f : Fin n → Equiv.Perm (Fin n) // ∀ j : Fin n, Function.Bijective fun k => f k j} ≃
      LatinSquare n where
  toFun f :=
    ⟨fun i j => (Equiv.ofBijective _ (f.2 j)).symm i,
      fun i => by
        refine (Finite.injective_iff_bijective).mp fun j1 j2 h => ?_
        set k := (Equiv.ofBijective _ (f.2 j1)).symm i
        have h1 : f.1 k j1 = i := (Equiv.ofBijective _ (f.2 j1)).apply_symm_apply i
        have h2 : f.1 k j2 = i := by
          dsimp only at h
          have := (Equiv.ofBijective _ (f.2 j2)).apply_symm_apply i
          rwa [← h] at this
        exact (f.1 k).injective (h1.trans h2.symm),
      fun j => (Equiv.ofBijective _ (f.2 j)).symm.bijective⟩
  invFun := fun ⟨L, hL1, hL2⟩ =>
    ⟨fun k => Equiv.ofBijective (fun j => (Equiv.ofBijective (fun i => L i j) (hL2 j)).symm k) (by
      refine (Finite.injective_iff_bijective).mp fun j1 j2 h => ?_
      set i := (Equiv.ofBijective (fun i => L i j1) (hL2 j1)).symm k
      have h1 : L i j1 = k := (Equiv.ofBijective (fun i => L i j1) (hL2 j1)).apply_symm_apply k
      have h2 : L i j2 = k := by
        have := (Equiv.ofBijective (fun i => L i j2) (hL2 j2)).apply_symm_apply k
        rwa [← h] at this
      exact (hL1 i).1 (h1.trans h2.symm)),
    fun j => by
      have heq : (fun k => (Equiv.ofBijective (fun i => L i j) (hL2 j)).symm k) =
          (Equiv.ofBijective (fun i => L i j) (hL2 j)).symm := rfl
      simp [heq]⟩
  left_inv f := by
    apply Subtype.ext
    funext k
    apply Equiv.ext
    intro j
    change (Equiv.ofBijective _ (Equiv.ofBijective _ (f.2 j)).symm.bijective).symm k = f.1 k j
    exact (Equiv.ofBijective _ (f.2 j)).symm.injective (by
      simp only [Equiv.ofBijective_apply_symm_apply]
      exact ((Equiv.ofBijective _ (f.2 j)).symm_apply_apply k).symm)
  right_inv L := by
    rcases L with ⟨L, hL1, hL2⟩
    apply Subtype.ext
    funext i j
    let g : Equiv.Perm (Fin n) := Equiv.ofBijective (fun i => L i j) (hL2 j)
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective (fun k => g.symm k) g.symm.bijective
    change e.symm i = L i j
    apply e.injective
    rw [Equiv.apply_symm_apply]
    change i = g.symm (L i j)
    exact (g.symm_apply_apply i).symm

private lemma tuple_sign_eq_latin_sign {n : ℕ}
    (f : {f : Fin n → Equiv.Perm (Fin n) // ∀ j : Fin n, Function.Bijective fun k => f k j}) :
    ∏ k : Fin n, Equiv.Perm.sign (f.1 k) =
      Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) * sign (latinEquivTuple n f) := by
  let L := latinEquivTuple n f
  let row (i : Fin n) : Equiv.Perm (Fin n) := Equiv.ofBijective _ (L.property.1 i)
  let col (j : Fin n) : Equiv.Perm (Fin n) := Equiv.ofBijective _ (L.property.2 j)
  have hL : ∀ k j, L.val (f.1 k j) j = k := fun k j =>
    (Equiv.ofBijective _ (f.2 j)).symm_apply_apply k
  let Psym : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongrRight f.1
  let Pcol : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongrRight col
  let Prow : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongrRight row
  let S : Equiv.Perm (Fin n × Fin n) := Equiv.prodComm (Fin n) (Fin n)
  have hcomp : Psym = S.trans (Pcol.symm.trans (S.trans (Prow.trans S))) := by
    apply Equiv.ext
    rintro ⟨k, j⟩
    have h1 : Pcol.symm (j, k) = (j, f.1 k j) := by
      apply Pcol.injective
      simp [Pcol, col, hL]
    change (k, f.1 k j) = S (Prow (S (Pcol.symm (j, k))))
    rw [h1]
    simp [S, Prow, row, hL]
  have hsign := congrArg Equiv.Perm.sign hcomp
  have hsymm : Equiv.Perm.sign Pcol.symm = Equiv.Perm.sign Pcol := by
    change Equiv.Perm.sign Pcol⁻¹ = Equiv.Perm.sign Pcol
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right (Int.units_mul_self _)
  simp only [Equiv.Perm.sign_trans, hsymm, Psym, Pcol, Prow,
    Equiv.Perm.sign_prodCongrRight] at hsign
  have hS2 : Equiv.Perm.sign S * Equiv.Perm.sign S = 1 := Int.units_mul_self _
  rw [hsign]
  change _ = Equiv.Perm.sign S *
    ((∏ i : Fin n, Equiv.Perm.sign (row i)) * ∏ j : Fin n, Equiv.Perm.sign (col j))
  calc (Equiv.Perm.sign S * ∏ i, Equiv.Perm.sign (row i)) * Equiv.Perm.sign S *
        (∏ j, Equiv.Perm.sign (col j)) * Equiv.Perm.sign S
      = (Equiv.Perm.sign S * Equiv.Perm.sign S) * Equiv.Perm.sign S *
          ((∏ i, Equiv.Perm.sign (row i)) * ∏ j, Equiv.Perm.sign (col j)) := by ac_rfl
    _ = Equiv.Perm.sign S *
          ((∏ i, Equiv.Perm.sign (row i)) * ∏ j, Equiv.Perm.sign (col j)) := by rw [hS2, one_mul]

private lemma coeff_oneMonomial_det_pow_int (n : ℕ) :
    MvPolynomial.coeff (oneMonomial n) ((XMat n ℤ).det ^ n) =
      (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) : ℤ) *
        ((Nat.card {L : LatinSquare n // sign L = 1} : ℤ) -
         (Nat.card {L : LatinSquare n // sign L = -1} : ℤ)) := by
  have hexp : (XMat n ℤ).det ^ n =
      ∑ f : Fin n → Equiv.Perm (Fin n),
        MvPolynomial.monomial (∑ k : Fin n, ∑ j : Fin n, Finsupp.single (f k j, j) 1)
          (∏ k : Fin n, (Equiv.Perm.sign (f k) : ℤ)) := by
    calc (XMat n ℤ).det ^ n
        = ∏ _k : Fin n, ∑ σ : Equiv.Perm (Fin n),
            MvPolynomial.C (Equiv.Perm.sign σ : ℤ) * ∏ j : Fin n, XMat n ℤ (σ j) j := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Matrix.det_apply']
          congr 1
      _ = ∑ f : Fin n → Equiv.Perm (Fin n), ∏ k : Fin n,
            (MvPolynomial.C (Equiv.Perm.sign (f k) : ℤ) * ∏ j : Fin n, XMat n ℤ (f k j) j) :=
          Fintype.prod_sum _
      _ = ∑ f : Fin n → Equiv.Perm (Fin n),
            MvPolynomial.monomial (∑ k : Fin n, ∑ j : Fin n, Finsupp.single (f k j, j) 1)
              (∏ k : Fin n, (Equiv.Perm.sign (f k) : ℤ)) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.prod_mul_distrib]
          have hmon : ∏ k : Fin n, ∏ j : Fin n, XMat n ℤ (f k j) j =
              MvPolynomial.monomial (∑ k : Fin n, ∑ j : Fin n, Finsupp.single (f k j, j) 1) 1 := by
            have hinner : ∀ k : Fin n, ∏ j : Fin n, XMat n ℤ (f k j) j =
                MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (f k j, j) 1) 1 := fun k => by
              simpa [XMat, MvPolynomial.X] using
                (MvPolynomial.monomial_sum_one (R := ℤ) (Finset.univ : Finset (Fin n))
                  (fun j => Finsupp.single (f k j, j) 1)).symm
            simp_rw [hinner]
            exact (MvPolynomial.monomial_sum_one (R := ℤ) (Finset.univ : Finset (Fin n))
              (fun k => ∑ j : Fin n, Finsupp.single (f k j, j) 1)).symm
          rw [hmon, ← map_prod, MvPolynomial.C_mul_monomial, mul_one]
  have hiff : ∀ f : Fin n → Equiv.Perm (Fin n),
      (∑ k : Fin n, ∑ j : Fin n, Finsupp.single (f k j, j) 1) = oneMonomial n ↔
        ∀ j : Fin n, Function.Bijective fun k => f k j := by
    intro f
    rw [Finsupp.ext_iff]
    constructor
    · intro h j
      refine (Finite.surjective_iff_bijective).mp fun i => ?_
      have hij := h (i, j)
      simp only [Finsupp.finsetSum_apply, oneMonomial, matToFinsupp_apply] at hij
      have hterm : ∀ k j', (Finsupp.single (f k j', j') 1 : (Fin n × Fin n) →₀ ℕ) (i, j) =
          if j' = j ∧ f k j = i then 1 else 0 := by
        intro k j'
        rw [Finsupp.single_apply]
        by_cases hj' : j' = j
        · subst hj'; simp [Prod.ext_iff]
        · have : (f k j', j') ≠ (i, j) := fun h => hj' (congrArg Prod.snd h)
          simp [this, hj']
      simp_rw [hterm] at hij
      have hne : ∃ k : Fin n, f k j = i := by
        by_contra! hnone
        have : ∑ k : Fin n, ∑ j' : Fin n, (if j' = j ∧ f k j = i then (1 : ℕ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j' _ => ?_
          simp [hnone k]
        omega
      exact hne
    · intro hbij ⟨i, j⟩
      simp only [Finsupp.finsetSum_apply, oneMonomial, matToFinsupp_apply]
      have hterm : ∀ k j', (Finsupp.single (f k j', j') 1 : (Fin n × Fin n) →₀ ℕ) (i, j) =
          if j' = j ∧ f k j = i then 1 else 0 := by
        intro k j'
        rw [Finsupp.single_apply]
        by_cases hj' : j' = j
        · subst hj'; simp [Prod.ext_iff]
        · have : (f k j', j') ≠ (i, j) := fun h => hj' (congrArg Prod.snd h)
          simp [this, hj']
      simp_rw [hterm]
      obtain ⟨k0, hk0⟩ := (hbij j).2 i
      calc ∑ k : Fin n, ∑ j' : Fin n, (if j' = j ∧ f k j = i then (1 : ℕ) else 0)
          = ∑ k : Fin n, (if f k j = i then (1 : ℕ) else 0) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            by_cases hk : f k j = i <;> simp [hk]
        _ = 1 := by
            rw [Finset.sum_eq_single k0]
            · simp [hk0]
            · intro k _ hkne
              have : f k j ≠ i := fun h => hkne ((hbij j).1 (h.trans hk0.symm))
              simp [this]
            · intro h; exact absurd (Finset.mem_univ k0) h
  rw [hexp, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, hiff]
  classical
  let : Fintype (LatinSquare n) := Fintype.ofEquiv _ (latinEquivTuple n)
  calc ∑ f : Fin n → Equiv.Perm (Fin n),
        (if ∀ j : Fin n, Function.Bijective fun k => f k j then
          ∏ k : Fin n, (Equiv.Perm.sign (f k) : ℤ) else 0)
      = ∑ f : {f : Fin n → Equiv.Perm (Fin n) // ∀ j, Function.Bijective fun k => f k j},
          ∏ k : Fin n, (Equiv.Perm.sign (f.1 k) : ℤ) := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype
          (Finset.univ.filter fun f : Fin n → Equiv.Perm (Fin n) =>
            ∀ j : Fin n, Function.Bijective fun k => f k j)
          (fun _ => by simp)
          (fun f : Fin n → Equiv.Perm (Fin n) => ∏ k : Fin n, (Equiv.Perm.sign (f k) : ℤ))
    _ = ∑ f : {f : Fin n → Equiv.Perm (Fin n) // ∀ j, Function.Bijective fun k => f k j},
          (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) : ℤ) *
            (sign (latinEquivTuple n f) : ℤ) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have hs := congrArg (fun u : ℤˣ => (u : ℤ)) (tuple_sign_eq_latin_sign f)
        simpa [Units.val_mul] using hs
    _ = (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) : ℤ) *
          ∑ L : LatinSquare n, (sign L : ℤ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (latinEquivTuple n) _ _ (fun _ => rfl)
    _ = (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) : ℤ) *
          ((Nat.card {L : LatinSquare n // sign L = 1} : ℤ) -
           (Nat.card {L : LatinSquare n // sign L = -1} : ℤ)) := by
        congr 1
        have hsplit : ∑ L : LatinSquare n, (sign L : ℤ) =
            (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => sign L = 1), (1 : ℤ)) +
            (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => sign L = -1), (-1 : ℤ)) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun L : LatinSquare n => sign L = 1)]
          congr 1
          · exact Finset.sum_congr rfl fun L hL => by
              rw [(Finset.mem_filter.mp hL).2]; rfl
          · have hfilt : Finset.univ.filter (fun L : LatinSquare n => ¬ sign L = 1) =
                Finset.univ.filter (fun L : LatinSquare n => sign L = -1) := by
              ext L
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rcases Int.units_eq_one_or (sign L) with h | h <;> simp [h]
            rw [hfilt]
            exact Finset.sum_congr rfl fun L hL => by
              rw [(Finset.mem_filter.mp hL).2]; rfl
        rw [hsplit]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, sub_eq_add_neg]
        congr 1
        · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        · congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma card_all_eq_of_card_reduced_eq {n : ℕ} [NeZero n] (he : Even n)
    (hred : let R := {L : LatinSquare n // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
      Nat.card {L : R // sign L.val = 1} = Nat.card {L : R // sign L.val = -1}) :
    Nat.card {L : LatinSquare n // sign L = 1} = Nat.card {L : LatinSquare n // sign L = -1} := by
  let R := {L : LatinSquare n // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
  let Stab := {b : Equiv.Perm (Fin n) // b 0 = 0}
  let act (L : LatinSquare n) (a b : Equiv.Perm (Fin n)) : LatinSquare n :=
    ⟨fun i j => L.val (a i) (b j), fun i => (L.2.1 (a i)).comp b.bijective,
      fun j => (L.2.2 (b j)).comp a.bijective⟩
  obtain ⟨E, hE⟩ := latin_normalize_equiv n act (fun _ _ _ _ _ => rfl)
  have hs (L : LatinSquare n) : sign (E L).2.2.val = sign L := by
    rw [hE]
    exact latin_sign_of_reindex he L _ _ _ (fun _ _ => rfl)
  have hc (s : ℤˣ) : Nat.card {L : LatinSquare n // sign L = s} =
      Nat.card (Equiv.Perm (Fin n)) * (Nat.card Stab * Nat.card {r : R // sign r.val = s}) := by
    let F : {L : LatinSquare n // sign L = s} ≃
        Equiv.Perm (Fin n) × Stab × {r : R // sign r.val = s} :=
      { toFun := fun x => ((E x.1).1, (E x.1).2.1, ⟨(E x.1).2.2, (hs x.1).trans x.2⟩)
        invFun := fun ⟨u, v, r⟩ => ⟨E.symm (u, v, r.1), by
          rw [← hs, E.apply_symm_apply]; exact r.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun ⟨u, v, r⟩ => by simp }
    simpa [Nat.card_prod] using Nat.card_congr F
  rw [hc 1, hc (-1), hred]

end GlynnAlonTarsi

theorem OMA.solution : OMA.R_opg_even_vs_odd_latin_squares_R1.H2 := by
  intro m he hp
  dsimp only
  intro hred
  let n := m + 1
  let p := m + 2
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero n := ⟨Nat.succ_ne_zero m⟩
  have hn_eq : n = p - 1 := by omega
  have hall := GlynnAlonTarsi.card_all_eq_of_card_reduced_eq he hred
  have hzero_int : MvPolynomial.coeff (GlynnAlonTarsi.oneMonomial n)
      ((GlynnAlonTarsi.XMat n ℤ).det ^ n) = 0 := by
    rw [GlynnAlonTarsi.coeff_oneMonomial_det_pow_int, hall, sub_self, mul_zero]
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod p)) ((GlynnAlonTarsi.XMat n ℤ).det ^ n) =
      (GlynnAlonTarsi.XMat n (ZMod p)).det ^ n := by
    rw [map_pow, RingHom.map_det]
    congr 1
    apply congrArg Matrix.det
    ext i j
    simp [GlynnAlonTarsi.XMat]
  have hzero_mod : MvPolynomial.coeff (GlynnAlonTarsi.oneMonomial n)
      ((GlynnAlonTarsi.XMat n (ZMod p)).det ^ n) = 0 := by
    rw [← hmap, MvPolynomial.coeff_map, hzero_int, map_zero]
  have hne : MvPolynomial.coeff (GlynnAlonTarsi.oneMonomial n)
      ((GlynnAlonTarsi.XMat n (ZMod p)).det ^ n) ≠ 0 := by
    rw [hn_eq, GlynnAlonTarsi.det_pow_eq_glynnPoly]
    exact GlynnAlonTarsi.coeff_oneMonomial_glynnPoly_ne_zero p
  exact hne hzero_mod
