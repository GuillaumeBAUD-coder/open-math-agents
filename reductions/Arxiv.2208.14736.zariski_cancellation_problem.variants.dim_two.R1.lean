import FormalConjectures.Arxiv.«2208.14736».ZariskiCancellation
import Mathlib

/-!
Zariski Cancellation in Dimension Two: Reduction

This file reduces Zariski's cancellation theorem for `k[X, Y]` over an arbitrary field `k`
in any universe (and arbitrary finitely generated `k`-algebra `B` in any independent universe)
to three canonical `Type 0` classical theorems:

1. `H1`: Fujita–Miyanishi–Sugie (1979) — cancellation of `K[X, Y]` over algebraically closed
   fields `K : Type` of characteristic `0`.
2. `H2`: Russell (1981) — cancellation of `K[X, Y]` over separably closed fields `K : Type`
   of prime characteristic `p`.
3. `H3`: Kambayashi (1975) — absence of nontrivial separable forms of the affine plane `𝔸²_k`
   over any field `k : Type`.

In `main`, we prove:
- Finitely generated subfield descent eliminating both independent universes (`k : Type u`,
  `B : Type v`) to a countable subfield `k₀ : Type 0` and a finitely presented `k₀`-algebra
  `B₀ : Type 0` with `(MvPolynomial (Fin 2) k₀)[X] ≃ₐ[k₀] B₀[X]` and `k ⊗[k₀] B₀ ≃ₐ[k] B`.
- Base change of polynomial algebras and cancellation isomorphisms to `K := SeparableClosure k₀`.
- Characteristic case split applying `H1` (in characteristic `0`, where `SeparableClosure k₀`
  is automatically algebraically closed) or `H2` (in prime characteristic `p`).
- Separable descent via `H3` and base change back to `k`.
-/

namespace OMA.R_Arxiv_2208_14736_zariski_cancellation_problem_variants_dim_two_R1

open Polynomial TensorProduct

universe u v

/-- Fujita–Miyanishi–Sugie (1979): `K[X, Y]` is cancellative over every algebraically closed
field `K : Type` of characteristic `0`. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (B : Type) [CommRing B] [Algebra K B] [Algebra.FiniteType K B],
    Nonempty ((MvPolynomial (Fin 2) K)[X] ≃ₐ[K] B[X]) →
    Nonempty (MvPolynomial (Fin 2) K ≃ₐ[K] B)

/-- Russell (1981): `K[X, Y]` is cancellative over every separably closed field `K : Type` of
prime characteristic `p`. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [IsSepClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (B : Type) [CommRing B] [Algebra K B] [Algebra.FiniteType K B],
    Nonempty ((MvPolynomial (Fin 2) K)[X] ≃ₐ[K] B[X]) →
    Nonempty (MvPolynomial (Fin 2) K ≃ₐ[K] B)

/-- Kambayashi (1975): the affine plane `𝔸²_k` has no nontrivial separable forms over any
field `k : Type`. -/
def H3 : Prop :=
  ∀ (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
    Nonempty (MvPolynomial (Fin 2) (SeparableClosure k) ≃ₐ[SeparableClosure k]
      (SeparableClosure k ⊗[k] B)) →
    Nonempty (MvPolynomial (Fin 2) k ≃ₐ[k] B)

section

/- Section 1: Countable subfield closure and base-change equivalences -/

private lemma exists_countable_subfield_containing
    (k : Type u) [Field k] (S : Set k) (hS : S.Countable) :
    ∃ (F : Subfield k), (F : Set k).Countable ∧ S ⊆ (F : Set k) := by
  let step : Set k → Set k := fun A =>
    A ∪
    ((fun p : k × k => p.1 + p.2) '' (A ×ˢ A)) ∪
    ((fun p : k × k => p.1 * p.2) '' (A ×ˢ A)) ∪
    (Neg.neg '' A) ∪
    (Inv.inv '' A)
  have hstep_cnt : ∀ A : Set k, A.Countable → (step A).Countable := fun A hA =>
    ((((hA.union ((hA.prod hA).image _)).union ((hA.prod hA).image _)).union
      (hA.image _)).union (hA.image _))
  let chain : ℕ → Set k := Nat.rec (S ∪ {0, 1}) (fun _ A => step A)
  have hchain_cnt : ∀ n, (chain n).Countable := by
    intro n
    induction n with
    | zero => exact hS.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih => exact hstep_cnt (chain n) ih
  have hchain_mono : ∀ n, chain n ⊆ chain (n + 1) := fun n x hx =>
    Or.inl (Or.inl (Or.inl (Or.inl hx)))
  have hchain_le : ∀ {m n}, m ≤ n → chain m ⊆ chain n := by
    intro m n hmn
    induction hmn with
    | refl => exact Set.Subset.rfl
    | step _ ih => exact ih.trans (hchain_mono _)
  let U : Set k := ⋃ n, chain n
  have hU_cnt : U.Countable := Set.countable_iUnion hchain_cnt
  let F : Subfield k := {
    carrier := U
    zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
    one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
    add_mem' := by
      intro x y hx hy
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inl (Or.inr ?_)))⟩
      exact ⟨(x, y), ⟨hchain_le (le_max_left m n) hm, hchain_le (le_max_right m n) hn⟩, rfl⟩
    mul_mem' := by
      intro x y hx hy
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inr ?_))⟩
      exact ⟨(x, y), ⟨hchain_le (le_max_left m n) hm, hchain_le (le_max_right m n) hn⟩, rfl⟩
    neg_mem' := by
      intro x hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨m + 1, Or.inl (Or.inr ⟨x, hm, rfl⟩)⟩
    inv_mem' := by
      intro x hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨m + 1, Or.inr ⟨x, hm, rfl⟩⟩
  }
  exact ⟨F, hU_cnt, fun x hx => Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩⟩

private lemma lift_tmul'
    {R : Type} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {A : Type} [CommRing A] [Algebra R A]
    {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : S →ₐ[S] B) (g : A →ₐ[R] B) (h : ∀ s a, Commute (f s) (g a))
    (s : S) (a : A) :
    Algebra.TensorProduct.lift f g h (s ⊗ₜ[R] a) = f s * g a := rfl

private lemma mvPolynomial_baseChange_equiv
    (k₀ : Type) [CommRing k₀] (K : Type u) [CommRing K] [Algebra k₀ K] (ι : Type) :
    Nonempty ((K ⊗[k₀] MvPolynomial ι k₀) ≃ₐ[K] MvPolynomial ι K) := by
  let fwd : (K ⊗[k₀] MvPolynomial ι k₀) →ₐ[K] MvPolynomial ι K :=
    Algebra.TensorProduct.lift
      (Algebra.ofId K (MvPolynomial ι K))
      (MvPolynomial.aeval (R := k₀) (S₁ := MvPolynomial ι K) (fun i => MvPolynomial.X i))
      (fun _ _ => Commute.all _ _)
  let bwd : MvPolynomial ι K →ₐ[K] (K ⊗[k₀] MvPolynomial ι k₀) :=
    MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k₀] MvPolynomial.X i)
  refine ⟨AlgEquiv.ofAlgHom fwd bwd ?_ ?_⟩
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, bwd, MvPolynomial.aeval_X, fwd, lift_tmul',
      map_one, one_mul]
  · apply Algebra.TensorProduct.ext'
    intro c p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : (c ⊗ₜ[k₀] MvPolynomial.C a : K ⊗[k₀] MvPolynomial ι k₀) =
          (c * algebraMap k₀ K a) ⊗ₜ[k₀] 1 := by
        rw [← MvPolynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
      rw [h1]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, fwd, lift_tmul', map_one, mul_one,
        Algebra.ofId_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      rfl
    | add p₁ p₂ hp₁ hp₂ =>
      rw [TensorProduct.tmul_add, map_add, map_add]
      exact congrArg₂ (· + ·) hp₁ hp₂
    | mul_X p i hp =>
      have hmul : (c ⊗ₜ[k₀] (p * MvPolynomial.X i) : K ⊗[k₀] MvPolynomial ι k₀) =
          (c ⊗ₜ[k₀] p) * ((1 : K) ⊗ₜ[k₀] MvPolynomial.X i) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hmul, map_mul, map_mul, hp]
      congr 1
      simp only [AlgHom.comp_apply, AlgHom.id_apply, fwd, lift_tmul', map_one, one_mul,
        MvPolynomial.aeval_X, bwd]

private lemma polynomial_baseChange_equiv
    (k₀ : Type) [CommRing k₀] (K : Type u) [CommRing K] [Algebra k₀ K]
    (A : Type) [CommRing A] [Algebra k₀ A] :
    Nonempty ((K ⊗[k₀] A[X]) ≃ₐ[K] (K ⊗[k₀] A)[X]) := by
  let inclA : A →ₐ[k₀] (K ⊗[k₀] A)[X] :=
    (Polynomial.CAlgHom (R := k₀) (A := K ⊗[k₀] A)).comp Algebra.TensorProduct.includeRight
  let coeffMap : (K ⊗[k₀] A) →ₐ[K] (K ⊗[k₀] A[X]) :=
    Algebra.TensorProduct.lift
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.comp (Polynomial.CAlgHom (R := k₀) (A := A)))
      (fun _ _ => Commute.all _ _)
  let bwd : (K ⊗[k₀] A)[X] →ₐ[K] (K ⊗[k₀] A[X]) :=
    Polynomial.eval₂AlgHom coeffMap ((1 : K) ⊗ₜ[k₀] (Polynomial.X : A[X])) (fun _ => Commute.all _ _)
  let fwd : (K ⊗[k₀] A[X]) →ₐ[K] (K ⊗[k₀] A)[X] :=
    Algebra.TensorProduct.lift
      (Algebra.ofId K (K ⊗[k₀] A)[X])
      (Polynomial.eval₂AlgHom inclA (Polynomial.X : (K ⊗[k₀] A)[X]) (fun _ => Commute.all _ _))
      (fun _ _ => Commute.all _ _)
  refine ⟨AlgEquiv.ofAlgHom fwd bwd ?_ ?_⟩
  · apply Polynomial.algHom_ext'
    · apply Algebra.TensorProduct.ext'
      intro c a
      let inclL : K →ₐ[K] (K ⊗[k₀] A[X]) := Algebra.TensorProduct.includeLeft
      have hc : bwd (Polynomial.C (c ⊗ₜ[k₀] a)) = c ⊗ₜ[k₀] Polynomial.C a := by
        rw [show bwd (Polynomial.C (c ⊗ₜ[k₀] a)) = coeffMap (c ⊗ₜ[k₀] a) by simp [bwd]]
        rw [show coeffMap (c ⊗ₜ[k₀] a) =
            inclL c *
              (Algebra.TensorProduct.includeRight.comp (Polynomial.CAlgHom (R := k₀) (A := A))) a from rfl]
        simp [inclL]
      change fwd (bwd (Polynomial.C (c ⊗ₜ[k₀] a))) = Polynomial.C (c ⊗ₜ[k₀] a)
      rw [hc]
      rw [show fwd (c ⊗ₜ[k₀] Polynomial.C a) =
          Algebra.ofId K (K ⊗[k₀] A)[X] c *
            Polynomial.eval₂AlgHom inclA (Polynomial.X : (K ⊗[k₀] A)[X]) (fun _ => Commute.all _ _)
              (Polynomial.C a) from rfl]
      simp only [Algebra.ofId_apply, Polynomial.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
        AlgHom.coe_toRingHom, inclA, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
        Polynomial.CAlgHom_apply, ← Polynomial.C_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, bwd, Polynomial.eval₂AlgHom_apply,
        Polynomial.eval₂_X, fwd, lift_tmul', map_one, one_mul]
  · apply Algebra.TensorProduct.ext'
    intro c f
    have hsplit : (c ⊗ₜ[k₀] f : K ⊗[k₀] A[X]) =
        algebraMap K (K ⊗[k₀] A[X]) c * ((1 : K) ⊗ₜ[k₀] f) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    rw [hsplit, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
    congr 1
    let inclR : A[X] →ₐ[k₀] (K ⊗[k₀] A[X]) := Algebra.TensorProduct.includeRight
    have hcomp : ((bwd.comp fwd).restrictScalars k₀).comp inclR = inclR := by
      apply Polynomial.algHom_ext'
      · apply AlgHom.ext
        intro a
        change bwd (fwd ((1 : K) ⊗ₜ[k₀] Polynomial.C a)) = (1 : K) ⊗ₜ[k₀] Polynomial.C a
        have hfC : fwd ((1 : K) ⊗ₜ[k₀] Polynomial.C a) = Polynomial.C ((1 : K) ⊗ₜ[k₀] a) := by
          rw [show fwd ((1 : K) ⊗ₜ[k₀] Polynomial.C a) =
              Algebra.ofId K (K ⊗[k₀] A)[X] 1 *
                Polynomial.eval₂AlgHom inclA (Polynomial.X : (K ⊗[k₀] A)[X])
                  (fun _ => Commute.all _ _) (Polynomial.C a) from rfl]
          rw [map_one, one_mul]
          simp [inclA]
        rw [hfC]
        let inclL : K →ₐ[K] (K ⊗[k₀] A[X]) := Algebra.TensorProduct.includeLeft
        rw [show bwd (Polynomial.C ((1 : K) ⊗ₜ[k₀] a)) = coeffMap ((1 : K) ⊗ₜ[k₀] a) by simp [bwd]]
        rw [show coeffMap ((1 : K) ⊗ₜ[k₀] a) =
            inclL 1 *
              (Algebra.TensorProduct.includeRight.comp (Polynomial.CAlgHom (R := k₀) (A := A))) a from rfl]
        simp [inclL]
      · change bwd (fwd ((1 : K) ⊗ₜ[k₀] Polynomial.X)) = (1 : K) ⊗ₜ[k₀] Polynomial.X
        have hfX : fwd ((1 : K) ⊗ₜ[k₀] Polynomial.X) = Polynomial.X := by
          rw [show fwd ((1 : K) ⊗ₜ[k₀] Polynomial.X) =
              Algebra.ofId K (K ⊗[k₀] A)[X] 1 *
                Polynomial.eval₂AlgHom inclA (Polynomial.X : (K ⊗[k₀] A)[X])
                  (fun _ => Commute.all _ _) Polynomial.X from rfl]
          rw [map_one, one_mul]
          simp
        rw [hfX]
        simp [bwd]
    exact AlgHom.congr_fun hcomp f

private lemma baseChange_cancel_iso
    (k₀ : Type) [Field k₀] (K : Type) [Field K] [Algebra k₀ K]
    (B₀ : Type) [CommRing B₀] [Algebra k₀ B₀]
    (e : (MvPolynomial (Fin 2) k₀)[X] ≃ₐ[k₀] B₀[X]) :
    Nonempty ((MvPolynomial (Fin 2) K)[X] ≃ₐ[K] (K ⊗[k₀] B₀)[X]) := by
  obtain ⟨eMv⟩ := mvPolynomial_baseChange_equiv k₀ K (Fin 2)
  obtain ⟨eP1⟩ := polynomial_baseChange_equiv k₀ K (MvPolynomial (Fin 2) k₀)
  obtain ⟨eP2⟩ := polynomial_baseChange_equiv k₀ K B₀
  let eTen : (K ⊗[k₀] (MvPolynomial (Fin 2) k₀)[X]) ≃ₐ[K] (K ⊗[k₀] B₀[X]) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  let ePolyMv : (MvPolynomial (Fin 2) K)[X] ≃ₐ[K] (K ⊗[k₀] MvPolynomial (Fin 2) k₀)[X] :=
    Polynomial.mapAlgEquiv eMv.symm
  exact ⟨ePolyMv.trans (eP1.symm.trans (eTen.trans eP2))⟩

private lemma quotient_mvPolynomial_baseChange_equiv
    (k₀ : Type) [CommRing k₀] (k : Type u) [CommRing k] [Algebra k₀ k]
    (m r : ℕ) (g₀ : Fin r → MvPolynomial (Fin m) k₀) :
    let I₀ : Ideal (MvPolynomial (Fin m) k₀) := Ideal.span (Set.range g₀)
    let I : Ideal (MvPolynomial (Fin m) k) :=
      Ideal.span (Set.range (fun a => MvPolynomial.map (algebraMap k₀ k) (g₀ a)))
    Nonempty ((k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀)) ≃ₐ[k] (MvPolynomial (Fin m) k ⧸ I)) := by
  intro I₀ I
  let q₀ : MvPolynomial (Fin m) k₀ →ₐ[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀) :=
    Ideal.Quotient.mkₐ k₀ I₀
  let q : MvPolynomial (Fin m) k →ₐ[k] (MvPolynomial (Fin m) k ⧸ I) :=
    Ideal.Quotient.mkₐ k I
  let mapP : MvPolynomial (Fin m) k₀ →ₐ[k₀] (MvPolynomial (Fin m) k ⧸ I) :=
    (q.restrictScalars k₀).comp (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))
  have hI₀_le : I₀ ≤ RingHom.ker mapP.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    show q (MvPolynomial.map (algebraMap k₀ k) (g₀ a)) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span ⟨a, rfl⟩)
  let barMap : (MvPolynomial (Fin m) k₀ ⧸ I₀) →ₐ[k₀] (MvPolynomial (Fin m) k ⧸ I) :=
    Ideal.Quotient.liftₐ I₀ mapP hI₀_le
  let fwd : (k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀)) →ₐ[k] (MvPolynomial (Fin m) k ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId k _) barMap (fun _ _ => Commute.all _ _)
  let liftBwd : MvPolynomial (Fin m) k →ₐ[k] (k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀)) :=
    MvPolynomial.aeval (fun j => (1 : k) ⊗ₜ[k₀] q₀ (MvPolynomial.X j))
  have hliftBwd_map : ∀ p : MvPolynomial (Fin m) k₀,
      liftBwd (MvPolynomial.map (algebraMap k₀ k) p) = (1 : k) ⊗ₜ[k₀] q₀ p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, liftBwd, MvPolynomial.aeval_C]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      change algebraMap k (k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀)) (algebraMap k₀ k a) =
        (1 : k) ⊗ₜ[k₀] algebraMap k₀ (MvPolynomial (Fin m) k₀ ⧸ I₀) a
      rw [Algebra.TensorProduct.algebraMap_apply]
      change (algebraMap k₀ k a) ⊗ₜ[k₀] (1 : MvPolynomial (Fin m) k₀ ⧸ I₀) =
        (1 : k) ⊗ₜ[k₀] (algebraMap k₀ (MvPolynomial (Fin m) k₀ ⧸ I₀) a)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      exact TensorProduct.smul_tmul a 1 1
    | add p₁ p₂ hp₁ hp₂ =>
      rw [map_add, map_add, map_add, TensorProduct.tmul_add, hp₁, hp₂]
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.map_X, map_mul, map_mul, hp]
      simp [liftBwd, Algebra.TensorProduct.tmul_mul_tmul]
  have hI_le : I ≤ RingHom.ker liftBwd.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    change liftBwd (MvPolynomial.map (algebraMap k₀ k) (g₀ a)) = 0
    rw [hliftBwd_map]
    have hzero : q₀ (g₀ a) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span ⟨a, rfl⟩)
    rw [hzero, TensorProduct.tmul_zero]
  let bwd : (MvPolynomial (Fin m) k ⧸ I) →ₐ[k] (k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀)) :=
    Ideal.Quotient.liftₐ I liftBwd hI_le
  refine ⟨AlgEquiv.ofAlgHom fwd bwd ?_ ?_⟩
  · apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change fwd (bwd (q p)) = q p
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h1 : q (MvPolynomial.C c) = algebraMap k (MvPolynomial (Fin m) k ⧸ I) c := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rw [h1, AlgHom.commutes, AlgHom.commutes]
    | add p₁ p₂ hp₁ hp₂ =>
      rw [map_add, map_add, map_add, hp₁, hp₂]
    | mul_X p j hp =>
      rw [map_mul, map_mul, map_mul, hp]
      congr 1
      have hb : bwd (q (MvPolynomial.X j)) = (1 : k) ⊗ₜ[k₀] q₀ (MvPolynomial.X j) := by
        change liftBwd (MvPolynomial.X j) = (1 : k) ⊗ₜ[k₀] q₀ (MvPolynomial.X j)
        simp [liftBwd]
      rw [hb]
      rw [show fwd ((1 : k) ⊗ₜ[k₀] q₀ (MvPolynomial.X j)) =
          Algebra.ofId k _ 1 * barMap (q₀ (MvPolynomial.X j)) from rfl]
      rw [map_one, one_mul]
      change q (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.X j)) = q (MvPolynomial.X j)
      rw [MvPolynomial.map_X]
  · apply Algebra.TensorProduct.ext'
    intro c x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change bwd (fwd (c ⊗ₜ[k₀] q₀ p)) = c ⊗ₜ[k₀] q₀ p
    have hfwd : fwd (c ⊗ₜ[k₀] q₀ p) =
        algebraMap k (MvPolynomial (Fin m) k ⧸ I) c * q (MvPolynomial.map (algebraMap k₀ k) p) := rfl
    rw [hfwd, map_mul, AlgHom.commutes]
    have hbwdq : bwd (q (MvPolynomial.map (algebraMap k₀ k) p)) = (1 : k) ⊗ₜ[k₀] q₀ p := by
      change liftBwd (MvPolynomial.map (algebraMap k₀ k) p) = (1 : k) ⊗ₜ[k₀] q₀ p
      exact hliftBwd_map p
    rw [hbwdq, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
    rfl

/- Section 2: Pulling back polynomials and finite-subfield descent from `(k, B)` to `Type 0` -/

private lemma mvPolynomial_lift_of_coeffs_mem
    {k₀ : Type} [CommRing k₀] {k : Type u} [CommRing k] [Algebra k₀ k]
    {m : ℕ} (p : MvPolynomial (Fin m) k)
    (hmem : ∀ d ∈ p.support, p.coeff d ∈ Set.range (algebraMap k₀ k)) :
    ∃ p₀ : MvPolynomial (Fin m) k₀, MvPolynomial.map (algebraMap k₀ k) p₀ = p := by
  classical
  have hch : ∀ d : Fin m →₀ ℕ, ∃ c : k₀, algebraMap k₀ k c = p.coeff d := fun d => by
    by_cases hd : d ∈ p.support
    · exact hmem d hd
    · refine ⟨0, ?_⟩
      rw [map_zero, MvPolynomial.notMem_support_iff.mp hd]
  choose coeff₀ hcoeff₀ using hch
  let p₀ : MvPolynomial (Fin m) k₀ := ∑ d ∈ p.support, MvPolynomial.monomial d (coeff₀ d)
  refine ⟨p₀, ?_⟩
  ext d
  rw [MvPolynomial.coeff_map]
  simp only [p₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  by_cases hd : d ∈ p.support
  · simp [hd, hcoeff₀ d]
  · simp [hd, MvPolynomial.notMem_support_iff.mp hd]

private lemma poly_mvPolynomial_lift_of_coeffs_mem
    {k₀ : Type} [CommRing k₀] {k : Type u} [CommRing k] [Algebra k₀ k]
    {m : ℕ} (f : (MvPolynomial (Fin m) k)[X])
    (hmem : ∀ n ∈ f.support, ∀ d ∈ (f.coeff n).support,
      (f.coeff n).coeff d ∈ Set.range (algebraMap k₀ k)) :
    ∃ f₀ : (MvPolynomial (Fin m) k₀)[X],
      f₀.map (MvPolynomial.map (algebraMap k₀ k)) = f := by
  classical
  have hch : ∀ n : ℕ, ∃ c : MvPolynomial (Fin m) k₀,
      MvPolynomial.map (algebraMap k₀ k) c = f.coeff n := fun n => by
    by_cases hn : n ∈ f.support
    · exact mvPolynomial_lift_of_coeffs_mem (f.coeff n) (hmem n hn)
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.notMem_support_iff.mp hn]
  choose c₀ hc₀ using hch
  let f₀ : (MvPolynomial (Fin m) k₀)[X] := ∑ n ∈ f.support, Polynomial.monomial n (c₀ n)
  refine ⟨f₀, ?_⟩
  ext n
  rw [Polynomial.coeff_map]
  simp only [f₀, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq']
  by_cases hn : n ∈ f.support
  · simp [hn, hc₀ n]
  · simp [hn, Polynomial.notMem_support_iff.mp hn]

private lemma descent_via_opaque_field
    (k₀ : Type) [Field k₀] (k : Type u) [Field k] [Algebra k₀ k]
    (B : Type v) [CommRing B] [Algebra k B]
    (m r : ℕ) (g₀ : Fin r → MvPolynomial (Fin m) k₀)
    (g : Fin r → MvPolynomial (Fin m) k)
    (hg₀ : ∀ a : Fin r, MvPolynomial.map (algebraMap k₀ k) (g₀ a) = g a)
    (eQ : (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range g)) ≃ₐ[k] B)
    (Ψ : (MvPolynomial (Fin 2) k)[X] ≃ₐ[k] (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range g))[X])
    (u₀' u₁' uX' : (MvPolynomial (Fin m) k₀)[X])
    (hu₀ : (u₀'.map (MvPolynomial.map (algebraMap k₀ k))).map
      (Ideal.Quotient.mkₐ k (Ideal.span (Set.range g))).toRingHom =
      Ψ (Polynomial.C (MvPolynomial.X 0)))
    (hu₁ : (u₁'.map (MvPolynomial.map (algebraMap k₀ k))).map
      (Ideal.Quotient.mkₐ k (Ideal.span (Set.range g))).toRingHom =
      Ψ (Polynomial.C (MvPolynomial.X 1)))
    (huX : (uX'.map (MvPolynomial.map (algebraMap k₀ k))).map
      (Ideal.Quotient.mkₐ k (Ideal.span (Set.range g))).toRingHom =
      Ψ Polynomial.X)
    (v' : Fin m → (MvPolynomial (Fin 2) k₀)[X])
    (hv' : ∀ j : Fin m, (v' j).map (MvPolynomial.map (algebraMap k₀ k)) =
      Ψ.symm (Polynomial.C (Ideal.Quotient.mkₐ k (Ideal.span (Set.range g)) (MvPolynomial.X j))))
    (vX' : (MvPolynomial (Fin 2) k₀)[X])
    (hvX' : vX'.map (MvPolynomial.map (algebraMap k₀ k)) = Ψ.symm Polynomial.X)
    (hΔ₀_mem : ∀ (j : Fin m) (n : ℕ),
      (((Polynomial.eval₂AlgHom
          (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀' else u₁'))
          uX' (fun _ => Commute.all _ _) (v' j)) -
        Polynomial.C (MvPolynomial.X j)).coeff n) ∈ Ideal.span (Set.range g₀))
    (hΔX₀_mem : ∀ n : ℕ,
      (((Polynomial.eval₂AlgHom
          (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀' else u₁'))
          uX' (fun _ => Commute.all _ _) vX') -
        Polynomial.X).coeff n) ∈ Ideal.span (Set.range g₀)) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra k₀ B₀) (_ : Algebra.FiniteType k₀ B₀),
      Nonempty ((MvPolynomial (Fin 2) k₀)[X] ≃ₐ[k₀] B₀[X]) ∧
      Nonempty ((k ⊗[k₀] B₀) ≃ₐ[k] B) := by
  let I' : Ideal (MvPolynomial (Fin m) k) := Ideal.span (Set.range g)
  let Q := MvPolynomial (Fin m) k ⧸ I'
  let q : MvPolynomial (Fin m) k →ₐ[k] Q := Ideal.Quotient.mkₐ k I'
  let I₀ : Ideal (MvPolynomial (Fin m) k₀) := Ideal.span (Set.range g₀)
  let B₀ : Type := MvPolynomial (Fin m) k₀ ⧸ I₀
  let q₀ : MvPolynomial (Fin m) k₀ →ₐ[k₀] B₀ := Ideal.Quotient.mkₐ k₀ I₀
  have hfinB₀ : Algebra.FiniteType k₀ B₀ :=
    Algebra.FiniteType.of_surjective q₀ Ideal.Quotient.mk_surjective
  let mapPm : MvPolynomial (Fin m) k₀ →+* MvPolynomial (Fin m) k := MvPolynomial.map (algebraMap k₀ k)
  let mapP2 : MvPolynomial (Fin 2) k₀ →+* MvPolynomial (Fin 2) k := MvPolynomial.map (algebraMap k₀ k)
  have hinj : Function.Injective (algebraMap k₀ k) := (algebraMap k₀ k).injective
  have hmapP2_inj : Function.Injective mapP2 := MvPolynomial.map_injective _ hinj
  have hmapP2X_inj : Function.Injective (Polynomial.map mapP2) := Polynomial.map_injective _ hmapP2_inj
  let u₀ : (MvPolynomial (Fin m) k)[X] := u₀'.map mapPm
  let u₁ : (MvPolynomial (Fin m) k)[X] := u₁'.map mapPm
  let uX : (MvPolynomial (Fin m) k)[X] := uX'.map mapPm
  let v : Fin m → (MvPolynomial (Fin 2) k)[X] := fun j => Ψ.symm (Polynomial.C (q (MvPolynomial.X j)))
  let vX : (MvPolynomial (Fin 2) k)[X] := Ψ.symm Polynomial.X
  let evalU_coeff : MvPolynomial (Fin 2) k →ₐ[k] (MvPolynomial (Fin m) k)[X] :=
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀ else u₁)
  let evalU : (MvPolynomial (Fin 2) k)[X] →ₐ[k] (MvPolynomial (Fin m) k)[X] :=
    Polynomial.eval₂AlgHom evalU_coeff uX (fun _ => Commute.all _ _)
  let evalU₀_coeff : MvPolynomial (Fin 2) k₀ →ₐ[k₀] (MvPolynomial (Fin m) k₀)[X] :=
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀' else u₁')
  let evalU₀ : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k₀)[X] :=
    Polynomial.eval₂AlgHom evalU₀_coeff uX' (fun _ => Commute.all _ _)
  have hevalU_mapq : ∀ w : (MvPolynomial (Fin 2) k)[X], (evalU w).map q.toRingHom = Ψ w := by
    intro w
    have hcomp : (Polynomial.mapAlgHom q).comp evalU = Ψ.toAlgHom := by
      apply Polynomial.algHom_ext'
      · apply MvPolynomial.algHom_ext
        intro i
        fin_cases i
        · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Polynomial.coe_mapAlgHom,
            evalU, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, evalU_coeff,
            AlgHom.coe_toRingHom, MvPolynomial.aeval_X, Fin.zero_eta, ↓reduceIte,
            AlgEquiv.coe_toAlgHom]
          exact hu₀
        · have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Polynomial.coe_mapAlgHom,
            evalU, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, evalU_coeff,
            AlgHom.coe_toRingHom, MvPolynomial.aeval_X, Fin.mk_one, h10, ↓reduceIte,
            AlgEquiv.coe_toAlgHom]
          exact hu₁
      · simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom, evalU, Polynomial.eval₂AlgHom_apply,
          Polynomial.eval₂_X, AlgEquiv.coe_toAlgHom]
        exact huX
    exact AlgHom.congr_fun hcomp w
  have hevalU₀_comm : ∀ f : (MvPolynomial (Fin 2) k₀)[X],
      (evalU₀ f).map mapPm = evalU (f.map mapP2) := by
    intro f
    let lhs : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k)[X] :=
      (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))).comp evalU₀
    let rhs : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k)[X] :=
      (evalU.restrictScalars k₀).comp
        (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k)))
    have hcomp : lhs = rhs := by
      apply Polynomial.algHom_ext'
      · apply MvPolynomial.algHom_ext
        intro i
        fin_cases i
        · simp [lhs, rhs, evalU₀, evalU₀_coeff, evalU, evalU_coeff, u₀, mapPm]
        · simp [lhs, rhs, evalU₀, evalU₀_coeff, evalU, evalU_coeff, u₁, mapPm]
      · simp [lhs, rhs, evalU₀, evalU, uX, mapPm]
    exact AlgHom.congr_fun hcomp f
  let evalV₀_coeff : MvPolynomial (Fin m) k₀ →ₐ[k₀] (MvPolynomial (Fin 2) k₀)[X] :=
    MvPolynomial.aeval v'
  let evalV_coeff : MvPolynomial (Fin m) k →ₐ[k] (MvPolynomial (Fin 2) k)[X] :=
    MvPolynomial.aeval v
  have hevalV₀_comm : ∀ p : MvPolynomial (Fin m) k₀,
      (evalV₀_coeff p).map mapP2 = evalV_coeff (mapPm p) := by
    intro p
    let lhs : MvPolynomial (Fin m) k₀ →ₐ[k₀] (MvPolynomial (Fin 2) k)[X] :=
      (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))).comp evalV₀_coeff
    let rhs : MvPolynomial (Fin m) k₀ →ₐ[k₀] (MvPolynomial (Fin 2) k)[X] :=
      (evalV_coeff.restrictScalars k₀).comp (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))
    have hcomp : lhs = rhs := by
      apply MvPolynomial.algHom_ext
      intro j
      change (evalV₀_coeff (MvPolynomial.X j)).map mapP2 =
        evalV_coeff (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.X j))
      simp only [evalV₀_coeff, evalV_coeff, MvPolynomial.aeval_X, MvPolynomial.map_X]
      exact hv' j
    exact AlgHom.congr_fun hcomp p
  have hevalV_eq : ∀ p : MvPolynomial (Fin m) k, evalV_coeff p = Ψ.symm (Polynomial.C (q p)) := by
    intro p
    have hcomp : evalV_coeff = (Ψ.symm.toAlgHom.comp Polynomial.CAlgHom).comp q := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [evalV_coeff, v]
    exact AlgHom.congr_fun hcomp p
  have hI₀_kerV : I₀ ≤ RingHom.ker evalV₀_coeff.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    show evalV₀_coeff (g₀ a) = 0
    apply hmapP2X_inj
    rw [hevalV₀_comm, Polynomial.map_zero, hevalV_eq]
    have hmem : mapPm (g₀ a) ∈ I' := by rw [hg₀ a]; exact Ideal.subset_span ⟨a, rfl⟩
    have hq0 : q (mapPm (g₀ a)) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [hq0, map_zero, map_zero]
  let barV₀ : B₀ →ₐ[k₀] (MvPolynomial (Fin 2) k₀)[X] :=
    Ideal.Quotient.liftₐ I₀ evalV₀_coeff hI₀_kerV
  let bwd₀ : B₀[X] →ₐ[k₀] (MvPolynomial (Fin 2) k₀)[X] :=
    Polynomial.eval₂AlgHom barV₀ vX' (fun _ => Commute.all _ _)
  let fwd₀ : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] B₀[X] :=
    (Polynomial.mapAlgHom q₀).comp evalU₀
  have hbwd_fwd : bwd₀.comp fwd₀ = AlgHom.id k₀ _ := by
    let evalV_full : (MvPolynomial (Fin m) k)[X] →ₐ[k] (MvPolynomial (Fin 2) k)[X] :=
      Polynomial.eval₂AlgHom evalV_coeff vX (fun _ => Commute.all _ _)
    have hevalV_full_eq : ∀ f : (MvPolynomial (Fin m) k)[X],
        evalV_full f = Ψ.symm (f.map q.toRingHom) := by
      intro f
      have hcomp : evalV_full = Ψ.symm.toAlgHom.comp (Polynomial.mapAlgHom q) := by
        apply Polynomial.algHom_ext'
        · apply MvPolynomial.algHom_ext
          intro j
          simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, evalV_full,
            Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, Polynomial.coe_mapAlgHom,
            Polynomial.map_C, AlgEquiv.coe_toAlgHom]
          exact hevalV_eq (MvPolynomial.X j)
        · simp [evalV_full, vX]
      exact AlgHom.congr_fun hcomp f
    have hbwd₀_comm : ∀ f : (MvPolynomial (Fin m) k₀)[X],
        (bwd₀ (f.map q₀.toRingHom)).map mapP2 = evalV_full (f.map mapPm) := by
      intro f
      let lhs : (MvPolynomial (Fin m) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin 2) k)[X] :=
        (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))).comp
          (bwd₀.comp (Polynomial.mapAlgHom q₀))
      let rhs : (MvPolynomial (Fin m) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin 2) k)[X] :=
        (evalV_full.restrictScalars k₀).comp
          (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k)))
      have hcomp : lhs = rhs := by
        apply Polynomial.algHom_ext'
        · apply MvPolynomial.algHom_ext
          intro j
          change (bwd₀ ((Polynomial.C (MvPolynomial.X j)).map q₀.toRingHom)).map mapP2 =
            evalV_full ((Polynomial.C (MvPolynomial.X j)).map mapPm)
          simp only [Polynomial.map_C, bwd₀, evalV_full, Polynomial.eval₂AlgHom_apply,
            Polynomial.eval₂_C, AlgHom.coe_toRingHom]
          exact hevalV₀_comm (MvPolynomial.X j)
        · simp only [lhs, rhs, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
            Polynomial.coe_mapAlgHom, Polynomial.map_X, bwd₀, evalV_full,
            Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]
          exact hvX'
      exact AlgHom.congr_fun hcomp f
    apply AlgHom.ext
    intro f
    apply hmapP2X_inj
    change (bwd₀ ((evalU₀ f).map q₀.toRingHom)).map mapP2 = f.map mapP2
    rw [hbwd₀_comm, hevalU₀_comm, hevalV_full_eq, hevalU_mapq, AlgEquiv.symm_apply_apply]
  have hfwd_bwd : fwd₀.comp bwd₀ = AlgHom.id k₀ _ := by
    have hfwd_v : ∀ j : Fin m, fwd₀ (v' j) = Polynomial.C (q₀ (MvPolynomial.X j)) := fun j => by
      change (evalU₀ (v' j)).map q₀.toRingHom = Polynomial.C (q₀ (MvPolynomial.X j))
      rw [← sub_eq_zero]
      ext n
      change ((evalU₀ (v' j)).map q₀.toRingHom - Polynomial.C (q₀.toRingHom (MvPolynomial.X j))).coeff n = 0
      rw [← Polynomial.map_C, ← Polynomial.map_sub, Polynomial.coeff_map]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hΔ₀_mem j n)
    have hfwd_vX : fwd₀ vX' = Polynomial.X := by
      change (evalU₀ vX').map q₀.toRingHom = Polynomial.X
      rw [← sub_eq_zero]
      ext n
      rw [← Polynomial.map_X (f := q₀.toRingHom), ← Polynomial.map_sub, Polynomial.coeff_map,
        Polynomial.coeff_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hΔX₀_mem n)
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.CAlgHom_apply, bwd₀,
        Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C]
      have hcomp : (fwd₀.comp barV₀).comp q₀ = Polynomial.CAlgHom.comp q₀ := by
        apply MvPolynomial.algHom_ext
        intro j
        change fwd₀ (evalV₀_coeff (MvPolynomial.X j)) = Polynomial.C (q₀ (MvPolynomial.X j))
        simp only [evalV₀_coeff, MvPolynomial.aeval_X]
        exact hfwd_v j
      exact AlgHom.congr_fun hcomp p
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, bwd₀, Polynomial.eval₂AlgHom_apply,
        Polynomial.eval₂_X]
      exact hfwd_vX
  let Ψ₀ : (MvPolynomial (Fin 2) k₀)[X] ≃ₐ[k₀] B₀[X] :=
    AlgEquiv.ofAlgHom fwd₀ bwd₀ hfwd_bwd hbwd_fwd
  obtain ⟨eQuot⟩ := quotient_mvPolynomial_baseChange_equiv k₀ k m r g₀
  have hI_match : Ideal.span (Set.range (fun a => MvPolynomial.map (algebraMap k₀ k) (g₀ a))) = I' := by
    congr 1; ext x; simp [hg₀]
  let eB₀ : (k ⊗[k₀] B₀) ≃ₐ[k] B :=
    eQuot.trans ((Ideal.quotientEquivAlgOfEq k hI_match).trans eQ)
  exact ⟨B₀, inferInstance, inferInstance, hfinB₀, ⟨Ψ₀⟩, ⟨eB₀⟩⟩

private lemma exists_descent_type0
    (k : Type u) [Field k]
    (B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (Φ : (MvPolynomial (Fin 2) k)[X] ≃ₐ[k] B[X]) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Algebra k₀ k)
      (B₀ : Type) (_ : CommRing B₀) (_ : Algebra k₀ B₀) (_ : Algebra.FiniteType k₀ B₀),
      Nonempty ((MvPolynomial (Fin 2) k₀)[X] ≃ₐ[k₀] B₀[X]) ∧
      Nonempty ((k ⊗[k₀] B₀) ≃ₐ[k] B) := by
  classical
  obtain ⟨s, hs⟩ := ‹Algebra.FiniteType k B›
  let m : ℕ := s.card
  let eS : Fin m ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  let π : MvPolynomial (Fin m) k →ₐ[k] B := MvPolynomial.aeval (fun j => (eS j).1)
  have hπ_surj : Function.Surjective π := by
    intro b
    have hb : b ∈ Algebra.adjoin k (s : Set B) := by rw [hs]; trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      refine ⟨MvPolynomial.X (eS.symm ⟨x, hx⟩), ?_⟩
      simp [π]
    · intro c; exact ⟨MvPolynomial.C c, by simp [π]⟩
    · rintro x y _ _ ⟨px, rfl⟩ ⟨py, rfl⟩; exact ⟨px + py, map_add π px py⟩
    · rintro x y _ _ ⟨px, rfl⟩ ⟨py, rfl⟩; exact ⟨px * py, map_mul π px py⟩
  let I : Ideal (MvPolynomial (Fin m) k) := RingHom.ker π.toRingHom
  obtain ⟨sI, hsI⟩ := IsNoetherian.noetherian I
  let r : ℕ := sI.card
  let eI : Fin r ≃ sI := (Fintype.equivFinOfCardEq (Fintype.card_coe sI)).symm
  let g : Fin r → MvPolynomial (Fin m) k := fun a => (eI a).1
  have hI_eq : Ideal.span (Set.range g) = I := by
    rw [← hsI]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, g]
    constructor
    · rintro ⟨a, rfl⟩; exact (eI a).2
    · intro hx; exact ⟨eI.symm ⟨x, hx⟩, by simp⟩
  let I' : Ideal (MvPolynomial (Fin m) k) := Ideal.span (Set.range g)
  let Q := MvPolynomial (Fin m) k ⧸ I'
  let q : MvPolynomial (Fin m) k →ₐ[k] Q := Ideal.Quotient.mkₐ k I'
  let eQ : Q ≃ₐ[k] B :=
    (Ideal.quotientEquivAlgOfEq k hI_eq).trans (Ideal.quotientKerAlgEquivOfSurjective hπ_surj)
  let Ψ : (MvPolynomial (Fin 2) k)[X] ≃ₐ[k] Q[X] := Φ.trans (Polynomial.mapAlgEquiv eQ.symm)
  have hmapq_surj : Function.Surjective (Polynomial.map q.toRingHom) :=
    Polynomial.map_surjective q.toRingHom Ideal.Quotient.mk_surjective
  obtain ⟨u₀, hu₀⟩ := hmapq_surj (Ψ (Polynomial.C (MvPolynomial.X 0)))
  obtain ⟨u₁, hu₁⟩ := hmapq_surj (Ψ (Polynomial.C (MvPolynomial.X 1)))
  obtain ⟨uX, huX⟩ := hmapq_surj (Ψ Polynomial.X)
  let v : Fin m → (MvPolynomial (Fin 2) k)[X] := fun j => Ψ.symm (Polynomial.C (q (MvPolynomial.X j)))
  let vX : (MvPolynomial (Fin 2) k)[X] := Ψ.symm Polynomial.X
  let evalU_coeff : MvPolynomial (Fin 2) k →ₐ[k] (MvPolynomial (Fin m) k)[X] :=
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀ else u₁)
  let evalU : (MvPolynomial (Fin 2) k)[X] →ₐ[k] (MvPolynomial (Fin m) k)[X] :=
    Polynomial.eval₂AlgHom evalU_coeff uX (fun _ => Commute.all _ _)
  have hevalU_mapq : ∀ w : (MvPolynomial (Fin 2) k)[X], (evalU w).map q.toRingHom = Ψ w := by
    intro w
    have hcomp : (Polynomial.mapAlgHom q).comp evalU = Ψ.toAlgHom := by
      apply Polynomial.algHom_ext'
      · apply MvPolynomial.algHom_ext
        intro i
        fin_cases i
        · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Polynomial.coe_mapAlgHom,
            evalU, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, evalU_coeff,
            AlgHom.coe_toRingHom, MvPolynomial.aeval_X, Fin.zero_eta, ↓reduceIte,
            AlgEquiv.coe_toAlgHom]
          exact hu₀
        · have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Polynomial.coe_mapAlgHom,
            evalU, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, evalU_coeff,
            AlgHom.coe_toRingHom, MvPolynomial.aeval_X, Fin.mk_one, h10, ↓reduceIte,
            AlgEquiv.coe_toAlgHom]
          exact hu₁
      · simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom, evalU, Polynomial.eval₂AlgHom_apply,
          Polynomial.eval₂_X, AlgEquiv.coe_toAlgHom]
        exact huX
    exact AlgHom.congr_fun hcomp w
  let Δ : Fin m → (MvPolynomial (Fin m) k)[X] := fun j => evalU (v j) - Polynomial.C (MvPolynomial.X j)
  let ΔX : (MvPolynomial (Fin m) k)[X] := evalU vX - Polynomial.X
  have hΔ_mem : ∀ (j : Fin m) (n : ℕ), ((Δ j).coeff n) ∈ I' := by
    intro j n
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q.toRingHom ((Δ j).coeff n) = 0
    rw [← Polynomial.coeff_map]
    have h0 : (Δ j).map q.toRingHom = 0 := by
      simp only [Δ, Polynomial.map_sub, hevalU_mapq, Polynomial.map_C]
      exact sub_eq_zero.mpr (Ψ.apply_symm_apply _)
    rw [h0, Polynomial.coeff_zero]
  have hΔX_mem : ∀ n : ℕ, (ΔX.coeff n) ∈ I' := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q.toRingHom (ΔX.coeff n) = 0
    rw [← Polynomial.coeff_map]
    have h0 : ΔX.map q.toRingHom = 0 := by
      simp only [ΔX, Polynomial.map_sub, hevalU_mapq, vX, AlgEquiv.apply_symm_apply,
        Polynomial.map_X, sub_self]
    rw [h0, Polynomial.coeff_zero]
  have hΔ_wit_ex : ∀ (j : Fin m) (n : ℕ),
      ∃ c : Fin r → MvPolynomial (Fin m) k, ∑ a : Fin r, c a * g a = (Δ j).coeff n := fun j n =>
    Ideal.mem_span_range_iff_exists_fun.mp (hΔ_mem j n)
  choose cΔ hcΔ using hΔ_wit_ex
  have hΔX_wit_ex : ∀ n : ℕ,
      ∃ c : Fin r → MvPolynomial (Fin m) k, ∑ a : Fin r, c a * g a = ΔX.coeff n := fun n =>
    Ideal.mem_span_range_iff_exists_fun.mp (hΔX_mem n)
  choose cΔX hcΔX using hΔX_wit_ex
  let coeffsMv : ∀ {t : ℕ}, MvPolynomial (Fin t) k → Set k := fun p =>
    (fun d => p.coeff d) '' (p.support : Set _)
  let coeffsPoly : ∀ {t : ℕ}, (MvPolynomial (Fin t) k)[X] → Set k := fun f =>
    ⋃ n ∈ (f.support : Set ℕ), coeffsMv (f.coeff n)
  have hcoeffsMv_cnt : ∀ {t : ℕ} (p : MvPolynomial (Fin t) k), (coeffsMv p).Countable :=
    fun p => p.support.countable_toSet.image _
  have hcoeffsPoly_cnt : ∀ {t : ℕ} (f : (MvPolynomial (Fin t) k)[X]), (coeffsPoly f).Countable :=
    fun f => Set.Countable.biUnion f.support.countable_toSet (fun n _ => hcoeffsMv_cnt (f.coeff n))
  let S : Set k :=
    (⋃ a : Fin r, coeffsMv (g a)) ∪
    coeffsPoly u₀ ∪ coeffsPoly u₁ ∪ coeffsPoly uX ∪
    (⋃ j : Fin m, coeffsPoly (v j)) ∪ coeffsPoly vX ∪
    (⋃ j : Fin m, ⋃ n ∈ ((Δ j).support : Set ℕ), ⋃ a : Fin r, coeffsMv (cΔ j n a)) ∪
    (⋃ n ∈ (ΔX.support : Set ℕ), ⋃ a : Fin r, coeffsMv (cΔX n a))
  have hS_cnt : S.Countable :=
    (((((((Set.countable_iUnion (fun a => hcoeffsMv_cnt (g a))).union
      (hcoeffsPoly_cnt u₀)).union (hcoeffsPoly_cnt u₁)).union (hcoeffsPoly_cnt uX)).union
      (Set.countable_iUnion (fun j => hcoeffsPoly_cnt (v j)))).union (hcoeffsPoly_cnt vX)).union
      (Set.countable_iUnion (fun j => Set.Countable.biUnion (Δ j).support.countable_toSet
        (fun n _ => Set.countable_iUnion (fun a => hcoeffsMv_cnt (cΔ j n a)))))).union
      (Set.Countable.biUnion ΔX.support.countable_toSet
        (fun n _ => Set.countable_iUnion (fun a => hcoeffsMv_cnt (cΔX n a))))
  obtain ⟨F, hF_cnt, hS_sub⟩ := exists_countable_subfield_containing k S hS_cnt
  have _ : Countable F := Set.countable_coe_iff.mpr hF_cnt
  let k₀ : Type := Shrink.{0} F
  let eF : k₀ ≃+* F := Shrink.ringEquiv.{0} F
  let _ : Algebra k₀ k := (F.subtype.comp eF.toRingHom).toAlgebra
  have hinj : Function.Injective (algebraMap k₀ k) := F.subtype_injective.comp eF.injective
  have hmem_range : ∀ x ∈ S, x ∈ Set.range (algebraMap k₀ k) := fun x hx =>
    ⟨eF.symm ⟨x, hS_sub hx⟩, by change (eF (eF.symm ⟨x, _⟩) : k) = x; simp⟩
  have hg₀_ex : ∀ a : Fin r, ∃ p₀ : MvPolynomial (Fin m) k₀,
      MvPolynomial.map (algebraMap k₀ k) p₀ = g a := fun a =>
    mvPolynomial_lift_of_coeffs_mem (g a) (fun d hd =>
      hmem_range _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨a, ⟨d, hd, rfl⟩⟩)))))))))
  choose g₀ hg₀ using hg₀_ex
  obtain ⟨u₀', hu₀'⟩ := poly_mvPolynomial_lift_of_coeffs_mem u₀ (fun n hn d hd =>
    hmem_range _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (Set.mem_biUnion hn ⟨d, hd, rfl⟩)))))))))
  obtain ⟨u₁', hu₁'⟩ := poly_mvPolynomial_lift_of_coeffs_mem u₁ (fun n hn d hd =>
    hmem_range _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (Set.mem_biUnion hn ⟨d, hd, rfl⟩))))))))
  obtain ⟨uX', huX'⟩ := poly_mvPolynomial_lift_of_coeffs_mem uX (fun n hn d hd =>
    hmem_range _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (Set.mem_biUnion hn ⟨d, hd, rfl⟩)))))))
  have hv'_ex : ∀ j : Fin m, ∃ f₀ : (MvPolynomial (Fin 2) k₀)[X],
      f₀.map (MvPolynomial.map (algebraMap k₀ k)) = v j := fun j =>
    poly_mvPolynomial_lift_of_coeffs_mem (v j) (fun n hn d hd =>
      hmem_range _ (Or.inl (Or.inl (Or.inl (Or.inr
        (Set.mem_iUnion.mpr ⟨j, Set.mem_biUnion hn ⟨d, hd, rfl⟩⟩))))))
  choose v' hv' using hv'_ex
  obtain ⟨vX', hvX'⟩ := poly_mvPolynomial_lift_of_coeffs_mem vX (fun n hn d hd =>
    hmem_range _ (Or.inl (Or.inl (Or.inr (Set.mem_biUnion hn ⟨d, hd, rfl⟩)))))
  let mapPm : MvPolynomial (Fin m) k₀ →+* MvPolynomial (Fin m) k := MvPolynomial.map (algebraMap k₀ k)
  let mapP2 : MvPolynomial (Fin 2) k₀ →+* MvPolynomial (Fin 2) k := MvPolynomial.map (algebraMap k₀ k)
  have hmapPm_inj : Function.Injective mapPm := MvPolynomial.map_injective _ hinj
  let evalU₀ : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k₀)[X] :=
    Polynomial.eval₂AlgHom
      (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u₀' else u₁'))
      uX' (fun _ => Commute.all _ _)
  have hevalU₀_comm : ∀ f : (MvPolynomial (Fin 2) k₀)[X],
      (evalU₀ f).map mapPm = evalU (f.map mapP2) := by
    intro f
    let lhs : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k)[X] :=
      (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k))).comp evalU₀
    let rhs : (MvPolynomial (Fin 2) k₀)[X] →ₐ[k₀] (MvPolynomial (Fin m) k)[X] :=
      (evalU.restrictScalars k₀).comp
        (Polynomial.mapAlgHom (MvPolynomial.mapAlgHom (Algebra.ofId k₀ k)))
    have hcomp : lhs = rhs := by
      apply Polynomial.algHom_ext'
      · apply MvPolynomial.algHom_ext
        intro i
        fin_cases i
        · change (evalU₀ (Polynomial.C (MvPolynomial.X 0))).map mapPm =
            evalU ((Polynomial.C (MvPolynomial.X 0)).map mapP2)
          simp only [evalU₀, evalU, evalU_coeff, Polynomial.map_C, mapP2, MvPolynomial.map_X,
            Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, AlgHom.coe_toRingHom,
            MvPolynomial.aeval_X, ↓reduceIte]
          exact hu₀'
        · change (evalU₀ (Polynomial.C (MvPolynomial.X 1))).map mapPm =
            evalU ((Polynomial.C (MvPolynomial.X 1)).map mapP2)
          simp only [evalU₀, evalU, evalU_coeff, Polynomial.map_C, mapP2, MvPolynomial.map_X,
            Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, AlgHom.coe_toRingHom,
            MvPolynomial.aeval_X, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte]
          exact hu₁'
      · simp only [lhs, rhs, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
          Polynomial.coe_mapAlgHom, Polynomial.map_X, evalU₀, evalU,
          Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]
        exact huX'
    exact AlgHom.congr_fun hcomp f
  have hΔ₀_mem : ∀ (j : Fin m) (n : ℕ),
      ((evalU₀ (v' j) - Polynomial.C (MvPolynomial.X j)).coeff n) ∈ Ideal.span (Set.range g₀) := by
    intro j n
    have hmap_eq : mapPm ((evalU₀ (v' j) - Polynomial.C (MvPolynomial.X j)).coeff n) = (Δ j).coeff n := by
      rw [← Polynomial.coeff_map]
      have hpoly : (evalU₀ (v' j) - Polynomial.C (MvPolynomial.X j)).map mapPm = Δ j := by
        rw [Polynomial.map_sub, hevalU₀_comm, hv' j, Polynomial.map_C]
        simp only [Δ, mapPm, MvPolynomial.map_X]
      rw [hpoly]
    by_cases hn : n ∈ (Δ j).support
    · have hwit : ∀ a : Fin r, ∃ c₀ : MvPolynomial (Fin m) k₀, mapPm c₀ = cΔ j n a := fun a =>
        mvPolynomial_lift_of_coeffs_mem (cΔ j n a) (fun d hd =>
          hmem_range _ (Or.inl (Or.inr
            (Set.mem_iUnion.mpr ⟨j, Set.mem_biUnion hn (Set.mem_iUnion.mpr ⟨a, ⟨d, hd, rfl⟩⟩)⟩))))
      choose c₀ hc₀ using hwit
      have hsum : ∑ a : Fin r, c₀ a * g₀ a = (evalU₀ (v' j) - Polynomial.C (MvPolynomial.X j)).coeff n := by
        apply hmapPm_inj
        rw [hmap_eq, map_sum]
        have hterm : ∀ a : Fin r, mapPm (c₀ a * g₀ a) = cΔ j n a * g a := fun a => by
          rw [map_mul, hc₀ a, hg₀ a]
        simp_rw [hterm]
        exact hcΔ j n
      exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨c₀, hsum⟩
    · have h0 : (Δ j).coeff n = 0 := Polynomial.notMem_support_iff.mp hn
      have h0' : (evalU₀ (v' j) - Polynomial.C (MvPolynomial.X j)).coeff n = 0 :=
        hmapPm_inj (hmap_eq.trans (h0.trans (map_zero mapPm).symm))
      rw [h0']
      exact Submodule.zero_mem _
  have hΔX₀_mem : ∀ n : ℕ, ((evalU₀ vX' - Polynomial.X).coeff n) ∈ Ideal.span (Set.range g₀) := by
    intro n
    have hmap_eq : mapPm ((evalU₀ vX' - Polynomial.X).coeff n) = ΔX.coeff n := by
      rw [← Polynomial.coeff_map]
      have hpoly : (evalU₀ vX' - Polynomial.X).map mapPm = ΔX := by
        rw [Polynomial.map_sub, hevalU₀_comm, hvX', Polynomial.map_X]
      rw [hpoly]
    by_cases hn : n ∈ ΔX.support
    · have hwit : ∀ a : Fin r, ∃ c₀ : MvPolynomial (Fin m) k₀, mapPm c₀ = cΔX n a := fun a =>
        mvPolynomial_lift_of_coeffs_mem (cΔX n a) (fun d hd =>
          hmem_range _ (Or.inr
            (Set.mem_biUnion hn (Set.mem_iUnion.mpr ⟨a, ⟨d, hd, rfl⟩⟩))))
      choose c₀ hc₀ using hwit
      have hsum : ∑ a : Fin r, c₀ a * g₀ a = (evalU₀ vX' - Polynomial.X).coeff n := by
        apply hmapPm_inj
        rw [hmap_eq, map_sum]
        have hterm : ∀ a : Fin r, mapPm (c₀ a * g₀ a) = cΔX n a * g a := fun a => by
          rw [map_mul, hc₀ a, hg₀ a]
        simp_rw [hterm]
        exact hcΔX n
      exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨c₀, hsum⟩
    · have h0 : ΔX.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
      have h0' : (evalU₀ vX' - Polynomial.X).coeff n = 0 :=
        hmapPm_inj (hmap_eq.trans (h0.trans (map_zero mapPm).symm))
      rw [h0']
      exact Submodule.zero_mem _
  obtain ⟨B₀, _, _, hfinB₀, hΨ₀, heB₀⟩ :=
    descent_via_opaque_field k₀ k B m r g₀ g hg₀ eQ Ψ u₀' u₁' uX'
      (by rwa [hu₀']) (by rwa [hu₁']) (by rwa [huX']) v' hv' vX' hvX' hΔ₀_mem hΔX₀_mem
  exact ⟨k₀, inferInstance, inferInstance, B₀, inferInstance, inferInstance, hfinB₀, hΨ₀, heB₀⟩

end

theorem main : H1 → H2 → H3 →
    type_of% @Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_two := by
  intro h1 h2 h3 k _ B _ _ _ ⟨Φ⟩
  obtain ⟨k₀, _, _, B₀, _, _, _, ⟨Ψ₀⟩, ⟨eB₀⟩⟩ := exists_descent_type0 k B Φ
  let K : Type := SeparableClosure k₀
  obtain ⟨ΨK⟩ := baseChange_cancel_iso k₀ K B₀ Ψ₀
  have hSep : Nonempty (MvPolynomial (Fin 2) K ≃ₐ[K] (K ⊗[k₀] B₀)) := by
    rcases CharP.char_is_prime_or_zero k₀ (ringChar k₀) with hp | hp0
    · have : Fact (ringChar k₀).Prime := ⟨hp⟩
      have : CharP K (ringChar k₀) :=
        (RingHom.charP_iff_charP (algebraMap k₀ K) (ringChar k₀)).mp inferInstance
      exact h2 K (ringChar k₀) (K ⊗[k₀] B₀) ⟨ΨK⟩
    · have hchar0 : CharP k₀ 0 := by
        simpa [hp0] using (inferInstance : CharP k₀ (ringChar k₀))
      have : CharZero k₀ := CharP.charP_to_charZero k₀
      have : CharZero K := charZero_of_injective_algebraMap (algebraMap k₀ K).injective
      exact h1 K (K ⊗[k₀] B₀) ⟨ΨK⟩
  obtain ⟨e₀⟩ := h3 k₀ B₀ hSep
  obtain ⟨eMv⟩ := mvPolynomial_baseChange_equiv k₀ k (Fin 2)
  let eTen : (k ⊗[k₀] MvPolynomial (Fin 2) k₀) ≃ₐ[k] (k ⊗[k₀] B₀) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e₀
  exact ⟨eMv.symm.trans (eTen.trans eB₀)⟩

end OMA.R_Arxiv_2208_14736_zariski_cancellation_problem_variants_dim_two_R1
