import FormalConjectures.Paper.KaplanskyUInvariant
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.Field.Equiv
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.Nat.Basic

/-!
# Fields with arbitrary positive even u-invariant

This is Merkurjev's theorem on even u-invariants. We construct a countable
field for each value. The binary case uses the field of three elements.

For dimension 2r+2 with r positive, start with a division algebra obtained
by adjoining r generic quaternion factors. It has dimension 4^r. Products
of its canonical generators give 2r+1 anticommuting elements and a diagonal
anisotropic form of dimension 2r+2. This form remains anisotropic under any
extension preserving the division algebra.

To split a given form of dimension 2r+3, use an affine chart of its quadric.
A square root of the radicand in the parameter-extended algebra would yield
2r+2 anticommuting elements over the original field, by polynomial lattice
straightening. Their distinct eigencharacters under conjugation would force
the algebra to have dimension at least 2^(2r+2), exceeding 4^r.

Finally, enumerate the forms over each countable field in the tower. Pair the
stage number and the index of each form to schedule the step that splits it.
In the direct limit every (2r+3)-dimensional form is isotropic, and the
original lower-dimensional form is still anisotropic.

References include Merkurjev, Simple algebras and quadratic forms (1991),
and Elman, Karpenko and Merkurjev, The Algebraic and Geometric Theory of
Quadratic Forms, sections 30 and 38.
-/

section

section

namespace KaplanskyTrans
open Polynomial
open scoped TensorProduct

variable (K A : Type*) [Field K] [Ring A] [Algebra K A]

/-- The coefficientwise embedding of an algebra polynomial ring into its
scalar extension by the rational function field. -/
noncomputable def polynomialImage : A[X] →ₐ[K] RatFunc K ⊗[K] A :=
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f := Algebra.TensorProduct.map s (AlgHom.id K A)
  let e := (polyEquivTensor K A).trans (Algebra.TensorProduct.comm K A K[X])
  f.comp e.toAlgHom

theorem polynomialImage_injective : Function.Injective (polynomialImage K A) := by
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f := Algebra.TensorProduct.map s (AlgHom.id K A)
  let e := (polyEquivTensor K A).trans (Algebra.TensorProduct.comm K A K[X])
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A) s.toLinearMap (RatFunc.algebraMap_injective K)
  exact hf.comp e.injective

theorem polynomialImage_C (a : A) : polynomialImage K A (C a) = (1 : RatFunc K) ⊗ₜ[K] a := by
  simp [polynomialImage,Algebra.TensorProduct.includeLeft_apply]

theorem polynomialImage_map (p : K[X]) : polynomialImage K A (p.map (algebraMap K A)) =
    (algebraMap K[X] (RatFunc K) p) ⊗ₜ[K] (1:A) := by
  have h : polyEquivTensor K A (p.map (algebraMap K A)) = (1:A) ⊗ₜ[K] p := by
    apply (polyEquivTensor K A).symm.injective
    rw [AlgEquiv.symm_apply_apply,polyEquivTensor_symm_apply_tmul_eq_smul,one_smul]
  simp [polynomialImage, h]

theorem polynomialImage_X : polynomialImage K A X = RatFunc.X ⊗ₜ[K] (1:A) := by
  simpa using polynomialImage_map K A X

theorem polynomialImage_quadratic (a b : A) :
    polynomialImage K A (C a*X^2+C b) =
      ((1:RatFunc K) ⊗ₜ[K] a) * (RatFunc.X ⊗ₜ[K] (1:A))^2 + (1:RatFunc K) ⊗ₜ[K] b := by
  rw [map_add,map_mul,map_pow, polynomialImage_C, polynomialImage_C, polynomialImage_X]

/-- A finite list of rational scalar extensions admits one nonzero scalar polynomial
whose product with every member belongs to the polynomial algebra. -/
theorem polynomialImage_clear (xs : List (RatFunc K ⊗[K] A)) :
    ∃ p : K[X], p ≠ 0 ∧ ∀ x ∈ xs, ∃ q : A[X], polynomialImage K A q =
      algebraMap (RatFunc K) _ (algebraMap K[X] (RatFunc K) p) * x := by
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let j := polynomialImage K A
  have mult (p : K[X]) (u : A[X]) :
      j (p.map (algebraMap K A)*u) = s p • j u := by
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * j u) (polynomialImage_map K A p)
  have clear (a : RatFunc K ⊗[K] A) : ∃ (p : K[X]) (b : A[X]), p ≠ 0 ∧ j b = s p • a := by
    induction a using TensorProduct.induction_on with
    | zero => exact ⟨1,0,one_ne_zero,by simp⟩
    | tmul r d =>
      refine ⟨r.denom,r.num.map (algebraMap K A) * C d,r.denom_ne_zero,?_⟩
      have den : s r.denom * r = s r.num := by
        have nz : s r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
        exact (mul_comm _ _).trans ((eq_div_iff nz).mp (RatFunc.num_div_denom r).symm)
      rw [mult, show j (C d) = _ from polynomialImage_C K A d, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,den]
    | add a b ha hb =>
      obtain ⟨p,u,hp,hu⟩ := ha
      obtain ⟨q,v,hq,hv⟩ := hb
      refine ⟨p*q, q.map (algebraMap K A)*u + p.map (algebraMap K A)*v,mul_ne_zero hp hq,?_⟩
      rw [map_add,mult,mult,hu,hv,smul_smul,smul_smul,mul_comm (s q),map_mul,smul_add]
  suffices ∃ p : K[X], p ≠ 0 ∧ ∀ x ∈ xs, ∃ q : A[X], j q = s p • x by
    obtain ⟨p,hp,h⟩ := this
    refine ⟨p,hp,?_⟩
    intro x hx
    obtain ⟨q,hq⟩ := h x hx
    refine ⟨q,?_⟩
    rw [show polynomialImage K A q = s p • x from hq,Algebra.smul_def]
    rfl
  induction xs with
  | nil => exact ⟨1,one_ne_zero,by simp⟩
  | cons x xs ih =>
    obtain ⟨p,u,hp,hu⟩ := clear x
    obtain ⟨q,hq,htail⟩ := ih
    refine ⟨p*q, mul_ne_zero hp hq,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨q.map (algebraMap K A)*u,by rw [mult,hu,smul_smul,mul_comm (s q),map_mul]⟩
    · obtain ⟨v,hv⟩ := htail y hy
      exact ⟨p.map (algebraMap K A)*v,by rw [mult,hv,smul_smul,map_mul]⟩


/-- The same common denominator as a central nonzero element of the tensor algebra. -/
theorem polynomialImage_clear_central [Nontrivial A] (xs : List (RatFunc K ⊗[K] A)) :
    ∃ z : RatFunc K ⊗[K] A, z ≠ 0 ∧ (∀ x, Commute z x) ∧
      (∀ x ∈ xs, ∃ q : A[X], polynomialImage K A q = z*x) ∧
      ∃ p : K[X], polynomialImage K A (p.map (algebraMap K A)) = z := by
  obtain ⟨p,hp,h⟩ := polynomialImage_clear K A xs
  let z := algebraMap (RatFunc K) (RatFunc K ⊗[K] A) (algebraMap K[X] (RatFunc K) p)
  have eq : polynomialImage K A (p.map (algebraMap K A)) = z := polynomialImage_map K A p
  have nz : z ≠ 0 := by
    intro hz
    have zeroP := polynomialImage_injective K A (eq.trans (hz.trans (map_zero _).symm))
    apply hp
    exact Polynomial.map_injective (algebraMap K A) (algebraMap K A).injective
      (zeroP.trans (Polynomial.map_zero _).symm)
  exact ⟨z,nz,Algebra.commutes _,h,p,eq⟩

end KaplanskyTrans

end

section

open scoped TensorProduct
namespace KaplanskySeed

/-- Base change of a tensor product distributes over both factors, also for
noncommutative algebras. -/
noncomputable def tensor_basechange (K L A B : Type*) [CommRing K] [CommRing L]
    [Ring A] [Ring B] [Algebra K L] [Algebra K A] [Algebra K B] :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.distribBaseChange K L A B)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

end KaplanskySeed

end

section

namespace KaplanskyTrans
open Polynomial
open scoped TensorProduct

/-- Purely transcendental extension preserves the absence of zero divisors,
including for noncommutative coefficient algebras. -/
theorem ratFunc_noZeroDivisors (K A : Type*) [Field K] [Ring A] [Algebra K A]
    [NoZeroDivisors A] : NoZeroDivisors (RatFunc K ⊗[K] A) := by
  classical
  let j : K[X] →ₐ[K] RatFunc K := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f : K[X] ⊗[K] A →ₐ[K] RatFunc K ⊗[K] A := Algebra.TensorProduct.map j (AlgHom.id K A)
  have hf : Function.Injective f := by
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := A) j.toLinearMap
      (RatFunc.algebraMap_injective K)
  let eqv := (Algebra.TensorProduct.comm K K[X] A).trans (polyEquivTensor K A).symm
  let _ : NoZeroDivisors (K[X] ⊗[K] A) :=
    Function.Injective.noZeroDivisors eqv eqv.injective (map_zero _) (map_mul _)
  have scal (p : K[X]) (a : K[X] ⊗[K] A) : f (p • a) = j p • f a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul q d =>
      simp only [TensorProduct.smul_tmul', smul_eq_mul, f, Algebra.TensorProduct.map_tmul,
        map_mul, AlgHom.id_apply]
    | add _ _ ih ih' => rw [smul_add, map_add, ih, ih', map_add, smul_add]
  have clear (a : RatFunc K ⊗[K] A) : ∃ (p : K[X]) (b : K[X] ⊗[K] A),
      p ≠ 0 ∧ f b = j p • a := by
    induction a using TensorProduct.induction_on with
    | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
    | tmul r d =>
      refine ⟨r.denom, r.num ⊗ₜ[K] d, r.denom_ne_zero, ?_⟩
      have den : j r.denom * r = j r.num := by
        have nz : j r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
        exact (mul_comm _ _).trans ((eq_div_iff nz).mp (RatFunc.num_div_denom r).symm)
      rw [TensorProduct.smul_tmul', smul_eq_mul, den]
      rfl
    | add a b ha hb =>
      obtain ⟨p,u,hp,hu⟩ := ha
      obtain ⟨q,v,hq,hv⟩ := hb
      refine ⟨p*q, q • u + p • v, mul_ne_zero hp hq, ?_⟩
      rw [map_add, scal, scal, hu,hv, smul_smul, smul_smul, mul_comm (j q), map_mul, smul_add]
  constructor
  intro x y xy
  obtain ⟨p,u,hp,hu⟩ := clear x
  obtain ⟨q,v,hq,hv⟩ := clear y
  have uv : u*v=0 := hf (by
    rw [map_mul,hu,hv,map_zero, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,xy,smul_zero,smul_zero])
  rcases eq_zero_or_eq_zero_of_mul_eq_zero uv with h | h
  · exact Or.inl ((smul_eq_zero.mp (hu.symm.trans (h ▸ map_zero f))).resolve_left
      (RatFunc.algebraMap_ne_zero hp))
  · exact Or.inr ((smul_eq_zero.mp (hv.symm.trans (h ▸ map_zero f))).resolve_left
      (RatFunc.algebraMap_ne_zero hq))

end KaplanskyTrans

end

section



open Polynomial
namespace KaplanskyTower

/-- A nonzero additive subgroup of the polynomial ring over a division ring, closed under
right multiplication, is generated on the right by a monic polynomial. -/
theorem polynomial_right_principal {D : Type*} [DivisionRing D] (I : AddSubgroup D[X])
    (nonzero : ∃ p ∈ I, p ≠ 0) (right : ∀ p ∈ I, ∀ q : D[X], p*q ∈ I) :
    ∃ u ∈ I, u.Monic ∧ ∀ p ∈ I, ∃ q, p = u*q := by
  classical
  let property (n : ℕ) := ∃ p ∈ I, p ≠ 0 ∧ p.natDegree = n
  have inhabited : ∃ n, property n := by
    obtain ⟨p,hp,notzero⟩ := nonzero
    exact ⟨p.natDegree,p,hp,notzero,rfl⟩
  obtain ⟨p,hp,np,degr⟩ := Nat.find_spec inhabited
  let u := p * C p.leadingCoeff⁻¹
  have mon : u.Monic := monic_mul_leadingCoeff_inv np
  have inI : u ∈ I := right p hp _
  have du : u.natDegree = Nat.find inhabited := by
    dsimp [u]
    rw [natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr np)),degr]
  refine ⟨u,inI,mon,?_⟩
  intro v hv
  have sum := modByMonic_add_div v u
  have inside : v %ₘ u ∈ I := by
    have h := I.sub_mem hv (right u inI (v /ₘ u))
    rw [eq_sub_of_add_eq sum]
    exact h
  have zero : v %ₘ u = 0 := by
    by_contra ne
    have low := natDegree_lt_natDegree ne (degree_modByMonic_lt v mon)
    have high : Nat.find inhabited ≤ (v %ₘ u).natDegree :=
      Nat.find_min' inhabited ⟨v %ₘ u,inside,ne,rfl⟩
    omega
  exact ⟨v /ₘ u,by simpa [zero] using sum.symm⟩

/-- A fractional right polynomial ideal over a division ring is principal whenever it admits
a common left denominator. No centrality assumption on that denominator is needed. -/
theorem principal_fractional_lattice {D E : Type*} [DivisionRing D] [DivisionRing E]
    (j : D[X] →+* E) (inj : Function.Injective j) (L : AddSubgroup E)
    (nonzero : ∃ x ∈ L, x ≠ 0) (right : ∀ x ∈ L, ∀ p : D[X], x*j p ∈ L)
    (clear : ∃ c : E, c ≠ 0 ∧ ∀ x ∈ L, ∃ p, j p = c*x) :
    ∃ u ∈ L, u ≠ 0 ∧ ∀ x ∈ L, ∃ p : D[X], x = u*j p := by
  classical
  obtain ⟨c,hc,denom⟩ := clear
  let I : AddSubgroup D[X] :=
    { carrier := {p | c⁻¹ * j p ∈ L}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change c⁻¹ * j (x+y) ∈ L
        simpa only [map_add,mul_add] using L.add_mem hx hy
      neg_mem' := by
        intro x hx
        change c⁻¹ * j (-x) ∈ L
        simpa only [map_neg,mul_neg] using L.neg_mem hx }
  have stable (p : D[X]) (hp : p ∈ I) (q : D[X]) : p*q ∈ I := by
    change c⁻¹ * j (p*q) ∈ L
    rw [map_mul,← mul_assoc]
    exact right _ hp _
  have inhabited : ∃ p ∈ I,p ≠ 0 := by
    obtain ⟨x,hx,xne⟩ := nonzero
    obtain ⟨a,ha⟩ := denom _ hx
    refine ⟨a,?_,?_⟩
    · change c⁻¹*j a ∈ L
      rwa [ha,inv_mul_cancel_left₀ hc]
    · intro az
      rw [az,map_zero] at ha
      exact (mul_ne_zero hc xne) ha.symm
  obtain ⟨p,hp,mon,gen⟩ := polynomial_right_principal I inhabited stable
  have nonzeroP : j p ≠ 0 := fun h => mon.ne_zero (inj ((map_zero j).symm ▸ h))
  refine ⟨c⁻¹*j p,hp,mul_ne_zero (inv_ne_zero hc) nonzeroP,?_⟩
  intro x hx
  obtain ⟨v,hv⟩ := denom x hx
  have eq : c⁻¹*j v = x := by rw [hv,inv_mul_cancel_left₀ hc]
  have mem : v ∈ I := by change c⁻¹*j v ∈ L; rwa [eq]
  obtain ⟨q,hq⟩ := gen v mem
  exact ⟨q, by rw [← eq,hq,map_mul,mul_assoc]⟩

/-- A family preserving the same fractional lattice can be conjugated simultaneously
into the polynomial ring. -/
theorem simultaneous_polynomial {D E : Type*} [DivisionRing D] [DivisionRing E]
    (j : D[X] →+* E) (inj : Function.Injective j) (L : AddSubgroup E)
    (nonzero : ∃ x ∈ L, x ≠ 0) (right : ∀ x ∈ L, ∀ p : D[X], x*j p ∈ L)
    (clear : ∃ c : E, c ≠ 0 ∧ ∀ x ∈ L, ∃ p, j p = c*x)
    (Y : Set E) (stable : ∀ y ∈ Y, ∀ x ∈ L, y*x ∈ L) :
    ∃ u : E, u ≠ 0 ∧ ∀ y ∈ Y, ∃ p : D[X], j p = u⁻¹*y*u := by
  obtain ⟨u,hu,une,gen⟩ := principal_fractional_lattice j inj L nonzero right clear
  refine ⟨u,une,?_⟩
  intro y hy
  obtain ⟨p,eq⟩ := gen (y*u) (stable y hy u hu)
  exact ⟨p,by rw [mul_assoc,eq,inv_mul_cancel_left₀ une]⟩

end KaplanskyTower

namespace KaplanskyStraight

/-- Ordered products of an anticommuting family are stable, up to central
coefficients, under left multiplication by every family member. -/
theorem stable_words {R E : Type*} [CommRing R] [Ring E] [Algebra R E]
    (ys : List E) (anti : ys.Pairwise fun a b => b*a = -(a*b))
    (square : ∀ y∈ys,∃ c:R,y*y=algebraMap R E c) :
    ∃ words : List E, 1∈words ∧ ∀ y∈ys, ∀ u∈words,
      ∃ v∈words,∃ c:R,y*u=v*algebraMap R E c := by
  induction ys with
  | nil => exact ⟨[1],by simp,by simp⟩
  | cons a ys ih =>
    obtain ⟨comm,rest⟩ := List.pairwise_cons.mp anti
    obtain ⟨tail,one,stable⟩ := ih rest (fun _ h => square _ (List.mem_cons_of_mem _ h))
    let all := tail ++ tail.map (fun v => a*v)
    have old {v:E} (h:v∈tail) : v∈all := List.mem_append_left _ h
    have new {v:E} (h:v∈tail) : a*v∈all := List.mem_append_right _ (List.mem_map.mpr ⟨v,h,rfl⟩)
    refine ⟨all,old one,?_⟩
    intro y hy u hu
    have hu' := List.mem_append.mp hu
    rcases List.mem_cons.mp hy with rfl | hy
    · rcases hu' with h | h
      · exact ⟨y*u,new h,1,by simp⟩
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        obtain ⟨c,hc⟩ := square y (List.mem_cons_self)
        exact ⟨v,old hv,c,by rw [←mul_assoc,hc,Algebra.commutes]⟩
    · rcases hu' with h | h
      · obtain ⟨v,hv,c,hc⟩ := stable y hy u h
        exact ⟨v,old hv,c,hc⟩
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        obtain ⟨w,hw,c,hc⟩ := stable y hy v hv
        exact ⟨a*w,new hw,-c,by rw [←mul_assoc,comm y hy,neg_mul,mul_assoc,hc,←mul_assoc,map_neg,mul_neg]⟩

end KaplanskyStraight

namespace KaplanskyStraight
open Polynomial

/-- The right polynomial span of the finite Clifford monomials is a
nonzero stable lattice with a common denominator. -/
theorem stable_lattice {D E R : Type*} [DivisionRing D] [DivisionRing E] [CommRing R] [Algebra R E]
    (j : Polynomial D →+* E) (as_poly : ∀ r:R, ∃p, j p = algebraMap R E r)
    (clear : ∀ w : List E,∃c:E,c≠0 ∧ ∀v∈w,∃p,j p=c*v)
    (ys : List E) (anti : ys.Pairwise fun a b => b*a = -(a*b))
    (square : ∀ y∈ys,∃ c:R,y*y=algebraMap R E c) :
    ∃ L : AddSubgroup E, (1:E)∈L ∧
      (∀ x∈L,∀p : Polynomial D,x*j p∈L) ∧
      (∃c:E,c≠0 ∧ ∀x∈L,∃p,j p=c*x) ∧
      ∀y∈ys,∀x∈L,y*x∈L := by
  classical
  obtain ⟨words,one,stable⟩ := stable_words ys anti square
  let A : Set E := {x | ∃ v∈words, ∃ p : Polynomial D, x = v*j p}
  let L := AddSubgroup.closure A
  have term (v : E) (hv:v∈words) (p : Polynomial D) : v*j p∈L :=
    AddSubgroup.subset_closure ⟨v,hv,p,rfl⟩
  obtain ⟨c,nz,clears⟩ := clear words
  refine ⟨L,by simpa using term 1 one 1,?_,⟨c,nz,?_⟩,?_⟩
  · intro x hx p
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      simpa [map_mul,mul_assoc] using term v hv (q*p)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact L.add_mem hx hy
    | neg x _ hx => rw [neg_mul]; exact L.neg_mem hx
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      obtain ⟨p,hp⟩ := clears v hv
      exact ⟨p*q,by rw [map_mul,hp,mul_assoc]⟩
    | zero => exact ⟨0,by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p,hp⟩ := hx
      obtain ⟨q,hq⟩ := hy
      exact ⟨p+q,by rw [map_add,hp,hq,mul_add]⟩
    | neg x _ hx =>
      obtain ⟨p,hp⟩ := hx
      exact ⟨-p,by rw [map_neg,hp,mul_neg]⟩
  · intro y hy x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      obtain ⟨w,hw,b,hb⟩ := stable y hy v hv
      obtain ⟨p,hp⟩ := as_poly b
      rw [←mul_assoc,hb,←hp,mul_assoc,←map_mul]
      exact term w hw _
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact L.add_mem hx hz
    | neg x _ hx => rw [mul_neg]; exact L.neg_mem hx

end KaplanskyStraight

namespace KaplanskyStraight
open Polynomial

theorem constant_of_square {D : Type*} [DivisionRing D] (q : D[X]) (a : D)
    (h : q*q = C a) : q = C (q.coeff 0) := by
  by_cases q0 : q=0
  · simp [q0]
  have deg := natDegree_mul q0 q0
  rw [h,natDegree_C] at deg
  exact eq_C_of_natDegree_eq_zero (by omega)

set_option maxHeartbeats 700000 in
theorem components_of_square {D : Type*} [DivisionRing D] (p : D[X]) (u v : D)
    (h : p*p = C u * X^2+C v) :
    p.coeff 1*p.coeff 1 = u ∧ p.coeff 0*p.coeff 0 = v ∧
      p.coeff 1*p.coeff 0 = -(p.coeff 0*p.coeff 1) := by
  have le : p.natDegree ≤ 1 := by
    by_cases p0 : p=0
    · simp [p0]
    have hd := natDegree_mul p0 p0
    have bound : (C u * X^2+C v).natDegree ≤ 2 := (natDegree_add_le _ _).trans (max_le
      (natDegree_C_mul_X_pow_le u 2) (by rw [natDegree_C]; omega))
    rw [←h,hd] at bound
    omega
  have hi : p.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have first := congrArg (fun z : D[X] => z.coeff 0) h
  have second := congrArg (fun z : D[X] => z.coeff 1) h
  have third := congrArg (fun z : D[X] => z.coeff 2) h
  simp only [coeff_add, C_mul_X_pow_eq_monomial] at first second third
  simp [coeff_mul, Finset.Nat.antidiagonal_eq_map,Finset.sum_range_succ] at third
  change p.coeff 0*p.coeff 2 + p.coeff 1*p.coeff 1 + p.coeff 2*p.coeff 0 = u at third
  simp [hi] at third
  simp [mul_coeff_one, coeff_monomial] at second
  simp [coeff_monomial] at first
  exact ⟨third,first,eq_neg_of_add_eq_zero_left (by rwa [add_comm])⟩

end KaplanskyStraight

namespace KaplanskyStraight
open Polynomial

theorem step {D E R : Type*} [DivisionRing D] [DivisionRing E] [CommRing R] [Algebra R E]
    (j : D[X] →+* E) (inj : Function.Injective j)
    (as_poly : ∀r : R,∃p,j p=algebraMap R E r)
    (clear : ∀w : List E,∃c:E,c≠0 ∧ ∀v∈w,∃p,j p=c*v)
    {m : ℕ} (a : Fin m → D) (u v : D) (old : Fin m → E) (y : E)
    (scalar : ∀i,∃c:R,j (C (a i))=algebraMap R E c)
    (curScalar : ∃c:R,j (C u*X^2+C v)=algebraMap R E c)
    (osq : ∀i,old i*old i=j (C (a i))) (ysq : y*y=j (C u*X^2+C v))
    (anti : ∀i k,i≠k → old i*old k=-(old k*old i)) (cross : ∀i,old i*y=-(y*old i)) :
    ∃g : Fin m → D,∃b c:D, (∀i,g i*g i=a i) ∧ b*b=u ∧ c*c=v ∧ b*c=-(c*b) ∧
      (∀i k,i≠k → g i*g k=-(g k*g i)) ∧ (∀i,g i*b=-(b*g i)) ∧ (∀i,g i*c=-(c*g i)) := by
  classical
  let ys := y :: List.ofFn old
  have hanti : ys.Pairwise fun a b => b*a = -(a*b) := List.pairwise_cons.mpr ⟨by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact cross i, List.pairwise_ofFn.mpr fun {_ _} h => anti _ _ h.ne'⟩
  have hsquare (w : E) (hw : w ∈ ys) : ∃r:R,w*w=algebraMap R E r := by
    rcases List.mem_cons.mp hw with rfl | ht
    · rwa [ysq]
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      rw [osq]; exact scalar i
  obtain ⟨L,one,closed,den,stable⟩ := stable_lattice j as_poly clear ys hanti hsquare
  obtain ⟨k,k0,hk⟩ := KaplanskyTower.simultaneous_polynomial j inj L ⟨1,one,one_ne_zero⟩ closed den {z | z∈ys} stable
  let conj (z : E) := k⁻¹*z*k
  have mul (x z : E) : conj x*conj z = conj (x*z) := by simp [conj,mul_assoc,k0]
  have neg (x : E) : conj (-x) = -conj x := by simp [conj]
  have center (p : D[X]) (hp : ∃c:R,j p=algebraMap R E c) : conj (j p)=j p := by
    obtain ⟨c,hc⟩ := hp
    rw [hc]
    change k⁻¹ * algebraMap R E c * k = _
    rw [mul_assoc,Algebra.commutes,←mul_assoc,inv_mul_cancel₀ k0,one_mul]
  obtain ⟨Y,hY⟩ := hk y (List.mem_cons_self)
  choose Q hQ using fun i => hk (old i) (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have Qsq (i : Fin m) : Q i * Q i=C (a i) := by
    apply inj
    rw [map_mul,hQ]
    exact (mul _ _).trans ((congrArg conj (osq i)).trans (center _ (scalar i)))
  have Ysq : Y*Y=C u*X^2+C v := by
    apply inj
    rw [map_mul,hY]
    exact (mul _ _).trans ((congrArg conj ysq).trans (center _ curScalar))
  let g (i : Fin m) := (Q i).coeff 0
  have Qc (i : Fin m) : Q i = C (g i) := constant_of_square _ _ (Qsq i)
  have lifted {p q : D[X]} {x z : E} (hp : j p=conj x) (hq : j q=conj z) (xz:x*z=-(z*x)) :
      p*q=-(q*p) := by
    apply inj
    rw [map_neg,map_mul,map_mul,hp,hq,mul,mul,xz,neg]
  obtain ⟨b2,c2,bc⟩ := components_of_square Y u v Ysq
  refine ⟨g,Y.coeff 1,Y.coeff 0,fun i => ?_,b2,c2,bc,?_,?_,?_⟩
  · simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (Qsq i)
  · intro i l hil
    simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (lifted (hQ i) (hQ l) (anti i l hil))
  · intro i
    have eqn := lifted (hQ i) hY (cross i)
    rw [Qc] at eqn
    simpa using congrArg (fun p : D[X] => p.coeff 1) eqn
  · intro i
    simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (lifted (hQ i) hY (cross i))

end KaplanskyStraight

open scoped TensorProduct
open Polynomial
namespace KaplanskyStraight

/-- Over a rational-function extension of a finite division algebra, an anticommuting
family with one quadratic square specializes to a family with two more constant terms. -/
theorem ratFunc_step {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] {m : ℕ} (c : Fin m → K) (b a : K)
    (old : Fin m → RatFunc K ⊗[K] D) (y : RatFunc K ⊗[K] D)
    (osq : ∀ i, old i*old i = algebraMap (RatFunc K) _ (RatFunc.C (c i)))
    (ysq : y*y = algebraMap (RatFunc K) _ (RatFunc.C b*RatFunc.X^2+RatFunc.C a))
    (anti : ∀ i k, i ≠ k → old i*old k = -(old k*old i))
    (cross : ∀ i, old i*y = -(y*old i)) :
    ∃ g : Fin m → D, ∃ v w : D,
      (∀ i, g i*g i=algebraMap K D (c i)) ∧ v*v=algebraMap K D b ∧ w*w=algebraMap K D a ∧
      v*w=-(w*v) ∧ (∀ i k, i ≠ k → g i*g k=-(g k*g i)) ∧
      (∀ i, g i*v=-(v*g i)) ∧ (∀ i, g i*w=-(w*g i)) := by
  let E := RatFunc K ⊗[K] D
  let j := (KaplanskyTrans.polynomialImage K D).toRingHom
  let f := (algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K))
  let : Algebra K[X] E := f.toAlgebra' (fun p z => Algebra.commutes _ _)
  have central (p : K[X]) : j (p.map (algebraMap K D)) = algebraMap K[X] E p :=
    KaplanskyTrans.polynomialImage_map K D p
  have i1 (k : K) : j (C (algebraMap K D k)) = algebraMap (RatFunc K) E (RatFunc.C k) := by
    have h := central (C k)
    simpa [f, RingHom.algebraMap_toAlgebra', RatFunc.algebraMap_C] using h
  have i2 : j (C (algebraMap K D b)*X^2+C (algebraMap K D a)) =
      algebraMap (RatFunc K) E (RatFunc.C b*RatFunc.X^2+RatFunc.C a) := by
    have h := central (C b*X^2+C a)
    simpa [f, RingHom.algebraMap_toAlgebra', RatFunc.algebraMap_C, RatFunc.algebraMap_X] using h
  have one_ne : (1:E) ≠ 0 := fun h => one_ne_zero
    (KaplanskyTrans.polynomialImage_injective K D (((map_one j).trans h).trans (map_zero j).symm))
  let : Nontrivial E := nontrivial_of_ne 1 0 one_ne
  let : NoZeroDivisors E := KaplanskyTrans.ratFunc_noZeroDivisors K D
  let : IsDomain E := NoZeroDivisors.to_isDomain E
  let : DivisionRing E := divisionRingOfFiniteDimensional (RatFunc K) E
  apply step (R := K[X]) j (KaplanskyTrans.polynomialImage_injective K D)
    (fun p => ⟨_,central p⟩) ?_ (fun i => algebraMap K D (c i))
    (algebraMap K D b) (algebraMap K D a) old y ?_ ?_ ?_ ?_ anti cross
  · intro words
    obtain ⟨z,nz,hc,mem,p,hp⟩ := KaplanskyTrans.polynomialImage_clear_central K D words
    exact ⟨z,nz,mem⟩
  · intro i
    exact ⟨C (c i), by simpa using central (C (c i))⟩
  · refine ⟨C b*X^2+C a,?_⟩
    rw [i2]
    change _ = algebraMap (RatFunc K) E (algebraMap K[X] (RatFunc K) _)
    simp [RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  · intro i
    exact (osq i).trans (i1 _).symm
  · exact ysq.trans i2.symm

end KaplanskyStraight

end

section

open scoped TensorProduct
open Polynomial

namespace KaplanskyTrans

universe u

/-- A list of square roots with the Clifford anticommutation relations. -/
abbrev Frame {K A : Type u} [Field K] [Ring A] [Algebra K A] {n : ℕ} (c : Fin n → K) :=
  ∃ g : Fin n → A, (∀ i, g i*g i = algebraMap K A (c i)) ∧
    ∀ i j, i ≠ j → g i*g j = -(g j*g i)

theorem noncomm_basechange (K S T A : Type u) [Field K] [Field S] [Field T]
    [Ring A] [Algebra K A] [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower K S T] :
    Nonempty ((T ⊗[K] A) ≃ₐ[T] T ⊗[S] (S ⊗[K] A)) :=
  ⟨AlgEquiv.ofLinearEquiv
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ => by simp)⟩

/-- Unfold the variables of a diagonal affine pencil, preserving the
algebra and recovering a whole Clifford frame from one square root. -/
theorem pencil_induction
    (step : ∀ (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
        [FiniteDimensional K A] [NoZeroDivisors A] {n : ℕ} (a b : K) (c : Fin n → K),
      Frame (A := RatFunc K ⊗[K] A)
        (Fin.cons (algebraMap K (RatFunc K) b * RatFunc.X^2 + algebraMap K (RatFunc K) a)
          (fun i => algebraMap K (RatFunc K) (c i))) →
      Frame (A := A) (Fin.cons a (Fin.cons b c))) (n : ℕ) (K A : Type u)
    [Field K] [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A] [NoZeroDivisors A]
    (a : K) (c : Fin n → K) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra K T) (t : Fin n → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      δ = algebraMap K T a + ∑ i, algebraMap K T (c i) * t i ^ 2 ∧
      (∀ x : T ⊗[K] A, x*x = algebraMap T _ δ → Frame (A := A) (Fin.cons a c)) := by
  induction n generalizing K A with
  | zero =>
    let e := Algebra.TensorProduct.lid K A
    refine ⟨K, inferInstance, inferInstance, Fin.elim0, a,
      Function.Injective.noZeroDivisors e e.injective (map_zero _) (map_mul _), by simp, ?_⟩
    intro x hx
    refine ⟨fun _ => e x, ?_, ?_⟩
    · intro i
      have hi : i=0 := Fin.ext (by omega)
      subst i
      change e x * e x = algebraMap K A a
      rw [←map_mul, hx,e.commutes]
    · intro i j ne
      exact (ne (Fin.ext (by omega))).elim
  | succ n ih =>
    let S := RatFunc K
    let B := S ⊗[K] A
    let k := algebraMap K S
    let a' : S := k (c 0) * RatFunc.X ^ 2 + k a
    let c' (i : Fin n) := k (c i.succ)
    let _ : NoZeroDivisors B := ratFunc_noZeroDivisors K A
    let _ : Nontrivial B := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
      K S A k.injective
    obtain ⟨T, fT, algS, ts, δ, hd, value, lift⟩ := ih S B a' c'
    let j := algebraMap S T
    let _ : Algebra K T := (j.comp k).toAlgebra
    let _ : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨e⟩ := noncomm_basechange K S T A
    let _ := hd
    refine ⟨T, fT, inferInstance, Fin.cons (j RatFunc.X) ts, δ,
      Function.Injective.noZeroDivisors e e.injective (map_zero _) (map_mul _), ?_, ?_⟩
    · rw [value, Fin.sum_univ_succ]
      simp only [a', c', map_add, map_mul, map_pow, Fin.cons_zero, Fin.cons_succ]
      change j (k (c 0))*j RatFunc.X^2 + j (k a) + _ = j (k a) + (j (k (c 0))*j RatFunc.X^2 + _)
      ac_rfl
    · intro x hx
      have found := lift (e x) (by rw [←map_mul,hx,e.commutes])
      have descent := step K A a (c 0) (fun i => c i.succ) found
      have tu : Fin.cons (c 0) (fun i => c i.succ) = c := Fin.cons_self_tail c
      rwa [tu] at descent

end KaplanskyTrans

end

section

namespace KaplanskyTrans

theorem anticommuting_cons {A : Type*} [Ring A] {n : ℕ} (a : A) (v : Fin n → A)
    (old : ∀ i j, i ≠ j → v i * v j = -(v j * v i))
    (cross : ∀ i, v i * a = -(a * v i)) :
    let g : Fin (n+1) → A := Fin.cons a v
    ∀ i j, i ≠ j → g i * g j = -(g j * g i) := by
  intro g i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro h
    exact False.elim (h rfl)
  · intro _
    exact (neg_neg _).symm.trans (congrArg Neg.neg (cross j)).symm
  · intro _
    exact cross i
  · intro h
    exact old i j fun eq => h (congrArg Fin.succ eq)

universe u

theorem frame_of_parts {K A : Type u} [Field K] [Ring A] [Algebra K A] {n : ℕ}
    (a b : K) (r : Fin n → K) (g : Fin n → A) (v u : A)
    (old : ∀ i, g i*g i=algebraMap K A (r i)) (sqv : v*v=algebraMap K A b)
    (squ : u*u=algebraMap K A a) (pair : v*u=-(u*v))
    (anti : ∀ i j, i ≠ j → g i*g j=-(g j*g i))
    (yv : ∀ i, g i*v=-(v*g i)) (yu : ∀ i, g i*u=-(u*g i)) :
    Frame (A := A) (Fin.cons a (Fin.cons b r)) := by
  let h : Fin (n+1) → A := Fin.cons v g
  refine ⟨Fin.cons u h, ?_, anticommuting_cons u h (anticommuting_cons v g anti yv) ?_⟩
  · exact Fin.cases squ (Fin.cases sqv old)
  · exact Fin.cases pair yu

end KaplanskyTrans

end

section

namespace KaplanskyTrans
open scoped TensorProduct
universe u

theorem frame_step (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [FiniteDimensional K A] [NoZeroDivisors A] {n : ℕ} (a b : K) (c : Fin n → K) :
    Frame (A := RatFunc K ⊗[K] A)
      (Fin.cons (algebraMap K (RatFunc K) b * RatFunc.X^2 + algebraMap K (RatFunc K) a)
        (fun i => algebraMap K (RatFunc K) (c i))) →
    Frame (A := A) (Fin.cons a (Fin.cons b c)) := by
  rintro ⟨g, sqs, anti⟩
  let _ := NoZeroDivisors.to_isDomain A
  let _ := divisionRingOfFiniteDimensional K A
  obtain ⟨h, v, u, hh, hv, hu, pair, ha, hy, hz⟩ := KaplanskyStraight.ratFunc_step
    c b a (fun i => g i.succ) (g 0)
    (fun i => sqs i.succ) (sqs 0)
    (fun i j ne => anti i.succ j.succ (fun h => ne (Fin.succ_injective n h)))
    (fun i => anti i.succ 0 i.succ_ne_zero)
  exact frame_of_parts a b c h v u hh hv hu pair ha hy hz

end KaplanskyTrans

end

section

namespace KaplanskyQuadric

/-- Over a division ring, a central quadratic extension has no zero divisors
exactly when its radicand has no square root in the division ring. This
coordinate calculation uses the coefficient order arising from a central
indeterminate and does not require the division ring to commute. -/
theorem quadratic_pair_criterion {D : Type*} [DivisionRing D] (δ : D) :
    (∀ a b c d : D, a * c + b * δ * d = 0 → a * d + b * c = 0 →
      (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0)) ↔ (∀ u : D, u * u ≠ δ) := by
  constructor
  · intro nozero u square
    have first : -u * u + 1 * δ * 1 = 0 := by simp [square]
    have second : -u * 1 + 1 * u = 0 := by simp
    rcases nozero (-u) 1 u 1 first second with zero | zero <;> exact one_ne_zero zero.2
  · intro nosquare a b c d hre him
    by_cases hb : b = 0
    · subst b
      by_cases ha : a = 0
      · exact Or.inl ⟨ha, rfl⟩
      · right
        exact ⟨(mul_eq_zero.mp (by simpa using hre)).resolve_left ha,
          (mul_eq_zero.mp (by simpa using him)).resolve_left ha⟩
    let u := b⁻¹ * a
    have bu : b * u = a := by simp [u, hb]
    have real : u * c + δ * d = 0 := by
      apply (mul_eq_zero.mp (show b * (u * c + δ * d) = 0 by
        simpa only [mul_add, ← mul_assoc, bu] using hre)).resolve_left hb
    have imag : u * d + c = 0 := by
      apply (mul_eq_zero.mp (show b * (u * d + c) = 0 by
        simpa only [mul_add, ← mul_assoc, bu] using him)).resolve_left hb
    have ceq : c = -(u * d) := (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using imag))
    have cancel : (δ - u * u) * d = 0 := by
      rw [ceq, mul_neg, ← mul_assoc] at real
      rw [sub_mul, sub_eq_neg_add]
      exact real
    have dz : d = 0 := (mul_eq_zero.mp cancel).resolve_left
      (sub_ne_zero.mpr (nosquare u).symm)
    exact Or.inr ⟨by simpa [dz] using ceq, dz⟩

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct

/-- Scalar extension to a quadratic algebra preserves division precisely
when the radicand has no square root in the original division algebra. -/
theorem nosquare_iff_quadratic_tensor {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    (δ : K) :
    NoZeroDivisors (QuadraticAlgebra K δ 0 ⊗[K] D) ↔
      ∀ u : D, u * u ≠ algebraMap K D δ := by
  let Q := QuadraticAlgebra K δ 0
  let w : Q := QuadraticAlgebra.omega
  let pair (a b : D) : Q ⊗[K] D := (1 : Q) ⊗ₜ[K] a + w ⊗ₜ[K] b
  let re : Q ⊗[K] D →ₗ[K] D :=
    (TensorProduct.lid K D).toLinearMap.comp ((QuadraticAlgebra.reₗ δ 0).rTensor D)
  let im : Q ⊗[K] D →ₗ[K] D :=
    (TensorProduct.lid K D).toLinearMap.comp ((QuadraticAlgebra.imₗ δ 0).rTensor D)
  have parts (a b : D) : re (pair a b) = a ∧ im (pair a b) = b := by
    have re1 : (1 : Q).re = 1 := rfl
    have im1 : (1 : Q).im = 0 := rfl
    simp [pair, re, im, w, re1, im1]
  have zero (a b : D) : pair a b = 0 ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h
      exact ⟨(parts a b).1.symm.trans ((congrArg re h).trans (map_zero re)),
        (parts a b).2.symm.trans ((congrArg im h).trans (map_zero im))⟩
    · rintro ⟨rfl, rfl⟩
      simp [pair]
  have decompose (x : Q ⊗[K] D) : ∃ a b, x = pair a b := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, ((zero 0 0).2 ⟨rfl, rfl⟩).symm⟩
    | tmul v d =>
      obtain ⟨r, s⟩ := v
      refine ⟨r • d, s • d, ?_⟩
      rw [QuadraticAlgebra.mk_eq_add_smul_omega, TensorProduct.add_tmul]
      simp [pair, w, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by simp only [pair, TensorProduct.tmul_add]; abel⟩
  have product (a b c d : D) :
      pair a b * pair c d = pair (a*c+b*algebraMap K D δ*d) (a*d+b*c) := by
    have ww : w*w = δ • (1 : Q) := by simp [w, Q, QuadraticAlgebra.omega_mul_omega_eq_add]
    have scalar : b * algebraMap K D δ * d = δ • (b*d) := by
      rw [← Algebra.commutes δ b, ← Algebra.smul_def, smul_mul_assoc]
    simp only [pair, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      ww, scalar, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    abel
  rw [← quadratic_pair_criterion]
  constructor
  · intro domain a b c d hre him
    have z : pair a b * pair c d = 0 := (product a b c d).trans ((zero _ _).2 ⟨hre,him⟩)
    exact (domain.eq_zero_or_eq_zero_of_mul_eq_zero z).imp (zero a b).mp (zero c d).mp
  · intro criterion
    constructor
    intro x y h
    obtain ⟨a, b, rfl⟩ := decompose x
    obtain ⟨c, d, rfl⟩ := decompose y
    obtain ⟨hre, him⟩ := (zero _ _).mp ((product a b c d).symm.trans h)
    exact (criterion a b c d hre him).imp (zero a b).mpr (zero c d).mpr

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct
universe u v

/-- An affine chart of a diagonal quadric. A nonsquare radicand in the division algebra
gives a field over which the form has a nonzero isotropic vector and the scalar-extended
algebra continues to have no zero divisors. The tail may be specialized to independent
indeterminates, with its last coordinate set equal to one. -/
theorem split_diagonal_of_no_square {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
    {n : ℕ} (w : Fin (n+1) → K) (tail : Fin n → K)
    (δ : K) (value : w 0 * δ + ∑ i, w i.succ * tail i ^ 2 = 0)
    (hD : ∀ u : D, u*u ≠ algebraMap K D δ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), NoZeroDivisors (L ⊗[K] D) ∧
      ∃ v : Fin (n+1) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  let Q := QuadraticAlgebra K δ 0
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := by
    constructor
    intro r eq
    apply hD (algebraMap K D r)
    rw [← map_mul]
    congr 1
    simpa [sq] using eq
  let s : Q := QuadraticAlgebra.omega
  let f := algebraMap K Q
  have square : s ^ 2 = f δ := by simp [sq, s, f, Q, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  have nonzero : s ≠ 0 := by
    intro eq
    have im := congrArg QuadraticAlgebra.im eq
    exact one_ne_zero (show (1:K) = 0 from im)
  refine ⟨Q, inferInstance, inferInstance, (nosquare_iff_quadratic_tensor δ).2 hD,
    Fin.cons s (fun i => f (tail i)), ?_, ?_⟩
  · intro eq
    exact nonzero (by simpa only [Fin.cons_zero, Pi.zero_apply] using congr_fun eq 0)
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, square]
    simpa only [f, map_add, map_sum, map_pow, map_mul, map_zero] using congrArg f value

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct
universe u v

/-- A square-root obstruction over an intermediate extension gives a point on
the form over a further extension preserving the algebra with which we started. -/
theorem split_over_composite {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] {n : ℕ} (w : Fin (n+1) → K)
    (witness : ∃ (T : Type u) (_ : Field T) (_ : Algebra K T)
        (tail : Fin n → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i ^ 2 = 0 ∧
      ∀ x : T ⊗[K] A, x*x ≠ algebraMap T _ δ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), NoZeroDivisors (L ⊗[K] A) ∧
      ∃ v : Fin (n+1) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  obtain ⟨T, fieldT, algT, tail, δ, domain, value, noSquare⟩ := witness
  let B := T ⊗[K] A
  let : Nontrivial B := nontrivial_of_ne (0 : B) (algebraMap T B δ) (by simpa only [zero_mul] using noSquare 0)
  let : IsDomain B := NoZeroDivisors.to_isDomain B
  let : DivisionRing B := divisionRingOfFiniteDimensional T B
  obtain ⟨L, fieldL, algL, h, v, nonzero, point⟩ :=
    split_diagonal_of_no_square (D := B) (fun i => algebraMap K T (w i)) tail δ value noSquare
  let : Algebra K L := ((algebraMap T L).comp (algebraMap K T)).toAlgebra
  let : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : (L ⊗[K] A) ≃ₐ[L] L ⊗[T] (T ⊗[K] A) := AlgEquiv.ofLinearEquiv
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K T L L A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ => by simp)
  exact ⟨L, fieldL, inferInstance,
    Function.Injective.noZeroDivisors e e.injective (map_zero e) (map_mul e),
    v,nonzero,point⟩

end KaplanskyQuadric

end

section

namespace KaplanskyIndex
open Finset

/-- Nonzero simultaneous eigenvectors with distinct eigenvalue profiles are
linearly independent. The operators need only be diagonal on the given family. -/
theorem independent_of_profiles {K A I J : Type*} [Field K] [AddCommGroup A] [Module K A]
    (v : I → A) (nz : ∀ i, v i ≠ 0) (T : J → A →ₗ[K] A) (χ : I → J → K)
    (eig : ∀ i j, T j (v i) = χ i j • v i)
    (sep : ∀ {i i'}, i ≠ i' → ∃ j, χ i j ≠ χ i' j) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro c zero i hi
    by_cases possible : ∃ b ∈ S, b ≠ i
    · obtain ⟨b,hb,ne⟩ := possible
      obtain ⟨j,dist⟩ := sep ne.symm
      let U : A →ₗ[K] A := T j - χ b j • LinearMap.id
      have action (a : I) : U (v a) = (χ a j - χ b j) • v a := by
        simp [U,eig,sub_smul]
      have rel := congrArg U zero
      simp only [map_sum,map_smul,action,smul_smul,map_zero] at rel
      have erased : ∑ a ∈ S.erase b, (c a * (χ a j - χ b j)) • v a = 0 := by
        rwa [← Finset.sum_erase_add _ _ hb,sub_self,mul_zero,zero_smul,add_zero] at rel
      exact (mul_eq_zero.mp (ih (S.erase b) (Finset.erase_ssubset hb) _ erased i
        (Finset.mem_erase.mpr ⟨ne.symm,hi⟩))).resolve_right (sub_ne_zero.mpr dist)
    · have single : S = {i} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hi,fun b hb => by by_contra bad; exact possible ⟨b,hb,bad⟩⟩
      rw [single,Finset.sum_singleton] at zero
      exact (smul_eq_zero.mp zero).resolve_right (nz i)

end KaplanskyIndex

end

section

namespace KaplanskyIndex

/-- On an even set, the parities of all single-element erasures determine
a subset. For the empty ambient set this says its powerset is a singleton. -/
theorem even_erasure_parity_injective {I : Type*} [Fintype I] [DecidableEq I]
    (ev : Fintype.card I % 2 = 0) :
    Function.Injective (fun S : Finset I => fun k => (S.erase k).card % 2) := by
  intro S T eq
  have relation (k : I) := congrFun eq k
  have info (U : Finset I) (k : I) :
      (U.erase k).card + (if k ∈ U then 1 else 0) = U.card := by
    split_ifs with h
    · exact Finset.card_erase_add_one h
    · simp [Finset.erase_eq_of_notMem h]
  by_cases par : S.card % 2 = T.card % 2
  · ext k
    have a := info S k
    have b := info T k
    have h : (S.erase k).card % 2 = (T.erase k).card % 2 := relation k
    by_cases s : k ∈ S <;> by_cases t : k ∈ T <;> simp_all <;> omega
  · have comp : S = Tᶜ := by
      ext k
      have a := info S k
      have b := info T k
      have h : (S.erase k).card % 2 = (T.erase k).card % 2 := relation k
      by_cases s : k ∈ S <;> by_cases t : k ∈ T <;> simp_all
      all_goals omega
    have sum : S.card + T.card = Fintype.card I := by rw [comp,Finset.card_compl_add_card]
    omega

end KaplanskyIndex

end

section

namespace KaplanskyIndex

/-- For any even number of anticommuting units, the ordered Clifford monomials
are linearly independent; in particular the algebra has the stated dimension bound. -/
theorem pow_card_le_finrank_of_anticommuting {K A I : Type*} [Field K] [NeZero (2 : K)]
    [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A] [Fintype I]
    (ev : Fintype.card I % 2 = 0) (g : I → Aˣ)
    (anti : ∀ i j, i ≠ j → (g i : A) * g j = -(g j * (g i : A) : A)) :
    2 ^ Fintype.card I ≤ Module.finrank K A := by
  classical
  let flip (k : I) (l : List (I)) := l.foldr (fun j b => if j = k then b else !b) false
  let letters (m : Finset I) := m.toList
  let word (l : List (I)) := (l.map g).prod
  have move (k : I) (l : List (I)) :
      (g k : A) * (word l : A) = if flip k l then -((word l : A) * (g k : A))
        else (word l : A) * (g k : A) := by
    induction l with
    | nil => simp [flip,word]
    | cons j l ih =>
      change (g k : A) * ((g j : A) * (word l : A)) = _
      have split : flip k (j::l) = if j = k then flip k l else !flip k l := rfl
      rw [split]
      change (g k : A) * ((g j : A) * (word l : A)) = if _ then
        -((g j : A) * (word l : A) * (g k : A)) else (g j : A) * (word l : A) * (g k : A)
      by_cases eq : j = k
      · subst j
        calc
          _ = (g k : A) * (if flip k l then -((word l : A) * (g k : A))
                  else (word l : A) * (g k : A)) := congrArg (fun z : A => (g k : A) * z) ih
          _ = _ := by cases flip k l <;> simp [mul_assoc]
      · rw [← mul_assoc,anti k j (Ne.symm eq),neg_mul,mul_assoc,ih]
        cases flip k l <;> simp [eq,mul_assoc]
  let v (m : Finset I) : A := word (letters m)
  let T (k : I) : A →ₗ[K] A := {
    toFun := fun x => (g k : A) * x * ((g k)⁻¹ : Aˣ)
    map_add' := fun _ _ => by simp [mul_add,add_mul]
    map_smul' := fun r x => by simp [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  }
  let χ (m : Finset I) (k : I) : K := if flip k (letters m) then -1 else 1
  have eig (m : Finset I) (k : I) : T k (v m) = χ m k • v m := by
    change ((g k : A) * (word _ : A)) * ((g k)⁻¹ : Aˣ) = _
    rw [move]
    cases h : flip k (letters m) <;> simp [χ,v,h,mul_assoc,neg_mul]
  have count (k : I) (l : List I) :
      (if flip k l then 1 else 0 : ℕ) = l.countP (fun j => decide (j ≠ k)) % 2 := by
    induction l with
    | nil => rfl
    | cons j l ih =>
      change (if (if j = k then flip k l else !flip k l) then 1 else 0) = _
      by_cases e : j = k
      · simp [e,ih]
      · cases h : flip k l <;> simp [e,h] at ih ⊢ <;> omega
  have erase (k : I) (m : Finset I) : (if flip k (letters m) then 1 else 0 : ℕ) =
      (m.erase k).card % 2 := by
    rw [count]
    have c := m.nodup_toList.card_eq_countP (P := fun j => j ≠ k)
    rw [Finset.toList_toFinset,Finset.filter_ne'] at c
    exact congrArg (· % 2) c.symm
  have sep {a b : Finset I} (ne : a ≠ b) : ∃ k, χ a k ≠ χ b k := by
    by_contra! same
    have flags : (fun k => flip k (letters a)) = (fun k => flip k (letters b)) := by
      funext k
      have eq := same k
      have diff : (-1 : K) ≠ 1 := by
        intro bad
        exact NeZero.ne (2 : K) (by linear_combination -bad)
      cases ha : flip k (letters a) <;> cases hb : flip k (letters b)
      · rfl
      · exact False.elim (diff (by simpa [χ,ha,hb] using eq.symm))
      · exact False.elim (diff (by simpa [χ,ha,hb] using eq))
      · rfl
    apply ne (even_erasure_parity_injective ev ?_)
    funext k
    change (a.erase k).card % 2 = (b.erase k).card % 2
    rw [← erase k a,← erase k b]
    exact congrArg (fun t : Bool => if t then 1 else 0) (congrFun flags k)
  have indep := independent_of_profiles v (fun m => (word (letters m)).ne_zero) T χ eig sep
  simpa using indep.fintype_card_le_finrank

end KaplanskyIndex

end

section

namespace KaplanskyIndex

/-- A sufficiently small algebra cannot represent a diagonal Clifford system
with invertible scalar squares. -/
theorem no_frame_below_pow {K A I : Type*} [Field K] [NeZero (2 : K)] [Ring A]
    [Nontrivial A] [Algebra K A] [FiniteDimensional K A] [Fintype I]
    (ev : Fintype.card I % 2 = 0) (bound : Module.finrank K A < 2 ^ Fintype.card I)
    (w : I → K) (nz : ∀ i, w i ≠ 0) :
    ¬ ∃ x : I → A, (∀ i, x i ^ 2 = algebraMap K A (w i)) ∧
        ∀ i j, i ≠ j → x i * x j = -(x j * x i) := by
  rintro ⟨x,sq,anti⟩
  have unit (i : I) : IsUnit (x i) := by
    apply (isUnit_pow_iff (n := 2) (by decide)).mp
    rw [sq]
    exact (isUnit_iff_ne_zero.mpr (nz i)).map (algebraMap K A)
  exact (not_le_of_gt bound) (pow_card_le_finrank_of_anticommuting (K := K) ev
    (fun i => (unit i).unit) (fun i j ne => by simpa using anti i j ne))

end KaplanskyIndex

end

section

open scoped TensorProduct
namespace KaplanskyTrans
universe u

/-- An even number of Clifford generators forces a large dimension at the bottom
of the successive rational pencils. This produces a nonsquare on the given quadric's affine chart. -/
theorem even_rank_radicand (r : ℕ)
    (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [FiniteDimensional K A] [NoZeroDivisors A] [NeZero (2 : K)]
    (bound : Module.finrank K A < 2 ^ (2*r+2))
    (w : Fin (2*r+3) → K) (nw : ∀ i, w i ≠ 0)
    :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra K T) (tail : Fin (2*r+2) → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i^2 = 0 ∧
      ∀ x : T ⊗[K] A, x*x ≠ algebraMap T _ δ := by
  let v (i : Fin (2*r+2)) : K := -(w i.succ / w 0)
  have vanish i : w 0*v i= -w i.succ := by
    simp only [v, mul_neg]
    rw [mul_comm, div_mul_cancel₀ _ (nw 0)]
  obtain ⟨T, fT, al, ts, δ, hd, val, extract⟩ :=
    pencil_induction (@frame_step) (2*r+1) K A (v 0) (fun j => v j.succ)
  let f := algebraMap K T
  refine ⟨T,fT,al,Fin.cons 1 ts,δ,hd,?_,?_⟩
  · change f (w 0) * δ + ∑ i, f (w i.succ) * (Fin.cons (α := fun _ => T) 1 ts i)^2 = 0
    have vm (i : Fin (2*r+2)) : f (w 0) * f (v i) = -f (w i.succ) := by
      rw [←map_mul, vanish, map_neg]
    rw [Fin.sum_univ_succ, Fin.cons_zero, val]
    simp only [Fin.cons_succ, one_pow,mul_one]
    change f (w 0) * (f (v 0) + ∑ i, f (v i.succ) * ts i ^ 2) + _ = 0
    rw [mul_add, Finset.mul_sum, vm]
    simp_rw [←mul_assoc, vm, neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  · intro x hx
    obtain ⟨g, sqr, anti⟩ := extract x hx
    apply KaplanskyIndex.no_frame_below_pow (K := K) (A := A) (I := Fin (2*r+2))
      (by rw [Fintype.card_fin]; omega) (by simpa using bound) v (fun i => neg_ne_zero.mpr (div_ne_zero (nw i.succ) (nw 0)))
    refine ⟨g, ?_, anti⟩
    intro i
    have tu : Fin.cons (v 0) (fun j => v j.succ) = v := Fin.cons_self_tail v
    simpa only [sq,tu] using sqr i

/-- Diagonal forms of dimension 2r+3 become isotropic over an extension
preserving every division algebra of dimension strictly less than 2^(2r+2).
This also covers forms with a zero coefficient and the case r=0. -/
theorem preserve_small_algebra (r : ℕ) (K A : Type u) [Field K] [NeZero (2 : K)]
    [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A] [NoZeroDivisors A]
    (bound : Module.finrank K A < 2 ^ (2*r+2)) (w : Fin (2*r+3) → K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), NoZeroDivisors (L ⊗[K] A) ∧
      ∃ v : Fin (2*r+3) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  classical
  by_cases all : ∀ i, w i ≠ 0
  · exact KaplanskyQuadric.split_over_composite w (even_rank_radicand r K A bound w all)
  · push Not at all
    obtain ⟨i,hi⟩ := all
    let e := Algebra.TensorProduct.lid K A
    refine ⟨K,inferInstance,inferInstance,Function.Injective.noZeroDivisors e e.injective
      (map_zero _) (map_mul _),Pi.single i 1,?_,?_⟩
    · intro eq
      have := congrFun eq i
      simp at this
    · apply Finset.sum_eq_zero
      intro j _
      by_cases eq : j = i
      · simp [eq,hi]
      · simp [Pi.single_eq_of_ne eq]

end KaplanskyTrans

end

section

open scoped TensorProduct
namespace KaplanskyTrans
universe u

/-- The isotropic coordinates generate a countable intermediate field over
which the division property already descends. -/
theorem preserve_small_algebra_countable (r : ℕ) (K A : Type u) [Field K] [Countable K]
    [NeZero (2 : K)] [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A]
    [NoZeroDivisors A] (bound : Module.finrank K A < 2 ^ (2*r+2)) (w : Fin (2*r+3) → K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Countable L ∧ NoZeroDivisors (L ⊗[K] A) ∧
      ∃ v : Fin (2*r+3) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  obtain ⟨E, fieldE, algE, dom, v, nz, iso⟩ := preserve_small_algebra r K A bound w
  let L := IntermediateField.adjoin K (Set.range v)
  have hc : Countable L := Cardinal.mk_le_aleph0_iff.mp
    ((IntermediateField.cardinalMk_adjoin_le K (Set.range v)).trans
      (sup_le (sup_le (Cardinal.mk_le_aleph0) (Cardinal.mk_le_aleph0)) le_rfl))
  let j := Algebra.TensorProduct.map (R := K) L.val (AlgHom.id K A)
  have inj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat L.val.toLinearMap (LinearMap.id (R := K) (M := A))
      Subtype.val_injective Function.injective_id
  let vs (i : Fin (2*r+3)) : L := ⟨v i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  refine ⟨L, inferInstance, inferInstance, hc,
    Function.Injective.noZeroDivisors j inj (map_zero j) (map_mul j), vs, ?_, ?_⟩
  · intro zero
    apply nz
    funext i
    exact congrArg Subtype.val (congrFun zero i)
  · apply L.val.injective
    simp only [map_sum, map_mul, map_pow, map_zero]
    change ∑ i, algebraMap K E (w i) * v i ^ 2 = 0
    exact iso

/-- The dimension of a tensor product of r quaternion factors is 4^r. -/
theorem quaternion_dimension_bound (r : ℕ) : 4^r < 2^(2*r+2) := by
  rw [pow_add, pow_mul]
  change 4^r < 4^r * 4
  have hp : 0 < 4^r := pow_pos (by decide) _
  omega

end KaplanskyTrans

end

section

/-!
Generic quaternion division-algebra seed for even u-invariants (Elman, Karpenko and
Merkurjev, The Algebraic and Geometric Theory of Quadratic Forms, Proposition 98.18).
At each stage the two parameters are transcendental. Polynomial degree excludes
a square root of the first parameter and a twisted norm equal to the second one.
The new quaternion pair and the old frame multiplied by its volume element give
the required anticommuting family at the next stage.
-/

section

namespace KaplanskyGeneric

/-- Conjugation of a quadratic algebra sends its root of a to the negative root. -/
def quadSign {K : Type*} [Field K] (a : K) : QuadraticAlgebra K a 0 ≃ₐ[K] QuadraticAlgebra K a 0 where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_mul' := fun x y => (star_mul x y).trans (mul_comm _ _)
  commutes' := by intro x; ext <;> simp

theorem quadSign_mk {K : Type*} [Field K] (a x y : K) :
    quadSign a ⟨x,y⟩ = ⟨x,-y⟩ := by change star _ = _; simp

theorem quadSign_involutive {K : Type*} [Field K] (a : K) :
    Function.Involutive (quadSign a) := star_star

end KaplanskyGeneric

end

section

open scoped TensorProduct
open Polynomial

namespace KaplanskyGeneric
variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
open KaplanskyTrans

noncomputable def ratAction (σ : A ≃ₐ[K] A) :
    (RatFunc K ⊗[K] A) ≃ₐ[RatFunc K] (RatFunc K ⊗[K] A) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R:=RatFunc K)) σ

theorem ratAction_poly (σ : A ≃ₐ[K] A) (p : A[X]) : ratAction σ (polynomialImage K A p) =
    polynomialImage K A (p.map σ.toRingEquiv.toRingHom) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp [polynomialImage_C,polynomialImage_X,ratAction]

/-- An automorphism on the coefficient algebra has even generic norm degree.
In particular its twisted norm cannot be the new transcendental parameter. -/
theorem twisted_norm_ne_X [Nontrivial A] [NoZeroDivisors A] (σ : A ≃ₐ[K] A) (x : RatFunc K ⊗[K] A) :
    x * ratAction σ x ≠ RatFunc.X ⊗ₜ[K] (1:A) := by
  intro eq
  obtain ⟨p,hp,clear⟩ := polynomialImage_clear K A [x]
  obtain ⟨q,hq⟩ := clear x (by simp)
  let f := algebraMap K A
  let den := p.map f
  let s := algebraMap K[X] (RatFunc K) p
  let z := algebraMap (RatFunc K) (RatFunc K ⊗[K] A) s
  have jden : polynomialImage K A den = z := polynomialImage_map K A p
  change polynomialImage K A q = z*x at hq
  have hσ : ratAction σ z = z := (ratAction σ).commutes s
  have zcx := Algebra.commutes s x
  change z*x=x*z at zcx
  have ident : q*(q.map σ.toRingEquiv.toRingHom) = (den*den)*X := by
    apply polynomialImage_injective K A
    rw [map_mul,←ratAction_poly,hq,map_mul,hσ,map_mul,map_mul,jden,polynomialImage_X]
    calc (z*x)*(z*ratAction σ x) = z*(x*z)*ratAction σ x := by simp [mul_assoc]
         _ = (z*z)*(x*ratAction σ x) := by rw [←zcx]; simp [mul_assoc]
         _ = _ := by rw [eq]
  have dn : den ≠ 0 := fun h => hp (Polynomial.map_injective f f.injective (h.trans (Polynomial.map_zero _).symm))
  have rhn : den*den*X ≠ 0 := mul_ne_zero (mul_ne_zero dn dn) X_ne_zero
  have qn : q ≠ 0 := fun he => rhn (ident.symm.trans (by simp [he]))
  have mn : q.map σ.toRingEquiv.toRingHom ≠ 0 := fun he => rhn (ident.symm.trans (by rw [he,mul_zero]))
  have h := congrArg Polynomial.natDegree ident
  rw [natDegree_mul qn mn, natDegree_map_eq_of_injective σ.injective, natDegree_mul (mul_ne_zero dn dn) X_ne_zero,
    natDegree_mul dn dn, natDegree_X] at h
  omega

theorem square_ne_X [Nontrivial A] [NoZeroDivisors A] (x : RatFunc K ⊗[K] A) :
    x*x ≠ RatFunc.X ⊗ₜ[K] (1:A) := by
  have h : ratAction (AlgEquiv.refl (R:=K) (A₁:=A)) x = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx,hy]
    | tmul u v => rfl
  simpa only [h] using twisted_norm_ne_X (AlgEquiv.refl (R:=K) (A₁:=A)) x
end KaplanskyGeneric

end

section

open scoped TensorProduct

namespace KaplanskyGeneric

/-- The first generic quadratic parameter gives a division algebra extension,
when the original algebra was finite dimensional and had no zero divisors. -/
theorem first_stage {K D : Type*} [Field K] [Ring D] [Nontrivial D] [Algebra K D]
    [FiniteDimensional K D] [NoZeroDivisors D] :
    NoZeroDivisors (QuadraticAlgebra (RatFunc K) RatFunc.X 0 ⊗[RatFunc K] (RatFunc K ⊗[K] D)) := by
  let S := RatFunc K
  let A := S ⊗[K] D
  let _ : Nontrivial A := Module.nontrivial_of_finrank_pos (R:=S) (M:=A) (by
    rw [Module.finrank_baseChange]; exact Module.finrank_pos)
  let _ : NoZeroDivisors A := KaplanskyTrans.ratFunc_noZeroDivisors K D
  let _ : IsDomain A := NoZeroDivisors.to_isDomain _
  let _ := divisionRingOfFiniteDimensional S A
  apply (KaplanskyQuadric.nosquare_iff_quadratic_tensor (K:=S) (D:=A) RatFunc.X).2
  intro x
  exact square_ne_X x
end KaplanskyGeneric

end

section

open scoped TensorProduct
namespace KaplanskyGeneric

/-- Transfer the generic twisted norm obstruction through scalar extension of the
first quadratic algebra. The resulting crossed product has no zero divisors. -/
theorem second_stage {S A : Type*} [Field S] [Ring A] [Nontrivial A] [Algebra S A] [FiniteDimensional S A]
    (a : S) (domain : NoZeroDivisors (QuadraticAlgebra S a 0 ⊗[S] A)) :
    let L := RatFunc S
    let B := L ⊗[S] A
    let C := QuadraticAlgebra S a 0 ⊗[S] A
    let R := QuadraticAlgebra L (RatFunc.C a) 0 ⊗[L] B
    let σ := Algebra.TensorProduct.congr (quadSign a) (AlgEquiv.refl (R:=S) (A₁:=A))
    let τ := Algebra.TensorProduct.congr (quadSign (RatFunc.C a)) (AlgEquiv.refl (R:=L) (A₁:=B))
    (∃ e : L ⊗[S] C ≃ₐ[L] R, ∀ x, e (ratAction σ x) = τ (e x)) →
    (NoZeroDivisors R → (∀ u : R, u*τ u ≠ algebraMap L R RatFunc.X) →
      NoZeroDivisors (B ⊗[L] QuaternionAlgebra L (RatFunc.C a) 0 RatFunc.X)) →
    NoZeroDivisors (B ⊗[L] QuaternionAlgebra L (RatFunc.C a) 0 RatFunc.X) := by
  intro L B C R σ τ transport cross
  obtain ⟨e,twist⟩ := transport
  let _ : Nontrivial C := Module.nontrivial_of_finrank_pos (R:=S) (M:=C) (by
    rw [Module.finrank_tensorProduct,QuadraticAlgebra.finrank_eq_two]
    exact Nat.mul_pos (by decide) Module.finrank_pos)
  let _ : NoZeroDivisors C := domain
  let _ : NoZeroDivisors (L⊗[S] C) := KaplanskyTrans.ratFunc_noZeroDivisors S C
  apply cross (Function.Injective.noZeroDivisors e.symm e.symm.injective (map_zero _) (map_mul _))
  intro u norm
  apply twisted_norm_ne_X σ (e.symm u)
  apply e.injective
  rw [map_mul,twist,e.apply_symm_apply,norm]
  exact (e.commutes RatFunc.X).symm

end KaplanskyGeneric

end

section

open scoped TensorProduct

namespace KaplanskyGeneric

/-- A ring spanned by its two crossed-product coordinates has no zero divisors
when the central square of the second generator is excluded from twisted norms. -/
theorem twisted_span_domain {C B : Type*} [Ring C] [Ring B]
    (φ : C →+* B) (σ : C → C) (iv : Function.Involutive σ) (j : B) (d : C)
    (sq : j*j = φ d) (twist : ∀ u : C, j*φ u = φ (σ u)*j)
    (norm : ∀ u : C, u*σ u ≠ d) (units : ∀ x : C, x ≠ 0 → IsUnit x)
    (span : ∀ b : B, ∃ x y : C, b = φ x + φ y*j) : NoZeroDivisors B := by
  have flip (u : C) : (φ (σ u)-j)*(φ u+j) = φ (σ u*u-d) := by
    rw [sub_mul,mul_add,mul_add,twist,sq,map_sub,map_mul]
    abel
  have core (u : C) (z : B) (hz : (φ u+j)*z = 0) : z=0 := by
    have hn : σ u*u ≠ d := by simpa only [iv u] using norm (σ u)
    have hu := (units _ (sub_ne_zero.mpr hn)).map φ
    apply hu.mul_left_cancel
    rw [mul_zero,←flip,mul_assoc,hz,mul_zero]
  constructor
  intro x z hz
  obtain ⟨a,b,rfl⟩ := span x
  by_cases hb : b=0
  · subst b
    simp only [map_zero,zero_mul,add_zero] at hz ⊢
    by_cases ha : a=0
    · exact Or.inl (by simp [ha])
    · exact Or.inr (((units a ha).map φ).mul_left_cancel (hz.trans (mul_zero _).symm))
  · obtain ⟨v,rfl⟩ := units b hb
    let u : C := (↑v⁻¹ : C)*a
    have fac : φ (v : C)*(φ u+j) = φ a+φ (v : C)*j := by
      rw [mul_add,←map_mul]
      simp [u,←mul_assoc]
    rw [←fac,mul_assoc] at hz
    exact Or.inr (core u z ((v.isUnit.map φ).mul_left_cancel (hz.trans (mul_zero _).symm)))

/-- The subalgebra generated by i in the quaternion algebra. -/
def quadInQuaternion {F : Type*} [Field F] (s t : F) :
    QuadraticAlgebra F s 0 →ₐ[F] QuaternionAlgebra F s 0 t where
  toFun q := ⟨q.re,q.im,0,0⟩
  map_one' := rfl
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp
  map_mul' := by intro x y; ext <;> simp
  commutes' := by intro r; ext <;> simp

/-- The twisted norm criterion for the tensor product of an arbitrary finite
dimensional algebra with a quaternion algebra. -/
theorem quaternion_nzd_of_twisted_norm {F A : Type*} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] (s t : F)
    (domain : NoZeroDivisors (QuadraticAlgebra F s 0 ⊗[F] A))
    (norm : ∀ u : QuadraticAlgebra F s 0 ⊗[F] A,
      u * Algebra.TensorProduct.congr (quadSign s) (AlgEquiv.refl (R:=F) (A₁:=A)) u ≠
      algebraMap F _ t) : NoZeroDivisors (A ⊗[F] QuaternionAlgebra F s 0 t) := by
  let Q := QuadraticAlgebra F s 0
  let H := QuaternionAlgebra F s 0 t
  let C := Q ⊗[F] A
  let B := H ⊗[F] A
  let inc := quadInQuaternion s t
  let φ : C →ₐ[F] B := Algebra.TensorProduct.map inc (AlgHom.id F A)
  let σ : C ≃ₐ[F] C := Algebra.TensorProduct.congr (quadSign s) (AlgEquiv.refl (R:=F) (A₁:=A))
  let J : H := ⟨0,0,1,0⟩
  let j : B := J ⊗ₜ[F] (1:A)
  have qtw (q : Q) : J*inc q = inc (quadSign s q)*J := by
    rcases q with ⟨x,y⟩
    rw [quadSign_mk]
    ext <;> simp [inc,quadInQuaternion,J,H]
  have jsq : J*J=algebraMap F H t := by ext <;> simp [J,H]
  have hsq : j*j=φ (algebraMap F C t) := by
    rw [AlgHom.commutes]
    change (J ⊗ₜ[F] (1:A))*(J ⊗ₜ[F] (1:A)) = (algebraMap F H t) ⊗ₜ[F] (1:A)
    rw [Algebra.TensorProduct.tmul_mul_tmul,jsq,one_mul]
  have htw (u : C) : j*φ u=φ (σ u)*j := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [mul_add,add_mul,hx,hy]
    | tmul q a =>
      change (J ⊗ₜ[F] (1:A))*(inc q ⊗ₜ[F] a) = (inc (quadSign s q) ⊗ₜ[F] a)*(J ⊗ₜ[F] (1:A))
      simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,qtw]
  have hiv : Function.Involutive σ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx,hy]
    | tmul q a =>
      change quadSign s (quadSign s q) ⊗ₜ[F] a = q ⊗ₜ[F] a
      rw [quadSign_involutive]
  have hspan (b : B) : ∃ x y : C, b=φ x+φ y*j := by
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0,0,by simp⟩
    | add x y hx hy =>
      obtain ⟨a,b,rfl⟩ := hx
      obtain ⟨c,d,rfl⟩ := hy
      refine ⟨a+c,b+d,?_⟩
      rw [map_add,map_add,add_mul]
      abel
    | tmul q a =>
      let p : Q := ⟨q.re,q.imI⟩
      let v : Q := ⟨q.imJ,q.imK⟩
      have hq : inc p+inc v*J=q := by ext <;> simp [p,v,inc,quadInQuaternion,J,H]
      refine ⟨p ⊗ₜ[F] a,v ⊗ₜ[F] a,?_⟩
      change q ⊗ₜ[F] a=(inc p ⊗ₜ[F] a)+(inc v ⊗ₜ[F] a)*(J ⊗ₜ[F] (1:A))
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,←TensorProduct.add_tmul,hq]
  let _ : Nontrivial C := nontrivial_of_ne _ _ (norm 0)
  let _ : NoZeroDivisors C := domain
  let _ : IsDomain C := NoZeroDivisors.to_isDomain _
  let _ : NoZeroDivisors B := twisted_span_domain φ.toRingHom σ hiv j (algebraMap F C t)
    hsq htw norm (fun x hx => FiniteDimensional.isUnit F hx) hspan
  let e := Algebra.TensorProduct.comm F A H
  exact Function.Injective.noZeroDivisors e e.injective (map_zero _) (map_mul _)

end KaplanskyGeneric

end

section

open scoped TensorProduct
namespace KaplanskyGeneric

/-- Scalar extension of a quadratic algebra acts on each coordinate separately. -/
theorem quadratic_change (K L : Type*) [Field K] [Field L] [Algebra K L] (a : K) :
    ∃ e : (L ⊗[K] QuadraticAlgebra K a 0) ≃ₐ[L] QuadraticAlgebra L (algebraMap K L a) 0,
      ∀ (s : L) (x y : K), e (s ⊗ₜ[K] (⟨x,y⟩ : QuadraticAlgebra K a 0)) =
       ⟨s*algebraMap K L x,s*algebraMap K L y⟩ := by
  let Q := QuadraticAlgebra K a 0
  let T := QuadraticAlgebra L (algebraMap K L a) 0
  let incl : Q →ₗ[K] T :=
    { toFun := fun z => ⟨algebraMap K L z.re,algebraMap K L z.im⟩
      map_add' := by intro x y; ext <;> simp [Q,T]
      map_smul' := by
        intro r x
        ext <;> change (algebraMap K L) (r * _) = r • _ <;> rw [Algebra.smul_def,map_mul] }
  have one : incl 1=1 := by ext <;> change (algebraMap K L) _ = _
                                  <;> first | exact map_one _ | exact map_zero _
  have mul (x y : Q) : incl (x*y) = incl x*incl y := by
    ext <;> simp [incl,Q,T]
  let extd := incl.liftBaseChange L
  have surj : Function.Surjective extd := by
    rintro ⟨x,y⟩
    exact ⟨(x ⊗ₜ[K] (⟨1,0⟩ : Q))+(y ⊗ₜ[K] (⟨0,1⟩ : Q)), by ext <;> simp [extd,incl,Q,T]⟩
  have dim : Module.finrank L (L ⊗[K] Q) = Module.finrank L T := by
    rw [Module.finrank_baseChange]; simp [Q,T,QuadraticAlgebra.finrank_eq_two]
  let e : (L ⊗[K] Q) ≃ₗ[L] T := LinearEquiv.ofBijective extd
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mpr surj,surj⟩
  refine ⟨Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct e ?_ ?_,?_⟩
  · intro r s x y
    change extd ((r*s) ⊗ₜ[K] (x*y)) = extd (r ⊗ₜ[K] x) * extd (s ⊗ₜ[K] y)
    simp [extd,mul,smul_smul,mul_comm r s]
  · change extd (1 ⊗ₜ[K] 1) = 1
    simp [extd,one]
  · intro s x y
    change extd (s ⊗ₜ[K] _) = _
    rw [LinearMap.liftBaseChange_tmul]
    rfl

/-- Negating the quadratic generator commutes with extension by a new rational parameter,
including after tensoring by any (possibly noncommutative) coefficient algebra. -/
theorem quadratic_transport {S A : Type*} [Field S] [Ring A] [Algebra S A] (a : S) :
    let L := RatFunc S
    let C := QuadraticAlgebra S a 0 ⊗[S] A
    let B := L ⊗[S] A
    let R := QuadraticAlgebra L (RatFunc.C a) 0 ⊗[L] B
    ∃ e : L ⊗[S] C ≃ₐ[L] R, ∀ x, e (ratAction
      (Algebra.TensorProduct.congr (quadSign a) (AlgEquiv.refl (R:=S) (A₁:=A))) x) =
        Algebra.TensorProduct.congr (quadSign (RatFunc.C a)) (AlgEquiv.refl (R:=L) (A₁:=B)) (e x) := by
  intro L C B R
  let Q := QuadraticAlgebra S a 0
  obtain ⟨k,hk⟩ := quadratic_change S L a
  let d := KaplanskySeed.tensor_basechange S L Q A
  let e := d.trans (Algebra.TensorProduct.congr k (AlgEquiv.refl (R:=L) (A₁:=B)))
  refine ⟨e,?_⟩
  let f := ratAction (Algebra.TensorProduct.congr (quadSign a) (AlgEquiv.refl (R:=S) (A₁:=A)))
  let h := Algebra.TensorProduct.congr (quadSign (algebraMap S L a)) (AlgEquiv.refl (R:=L) (A₁:=B))
  intro z
  change e (f z) = h (e z)
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero,map_zero,map_zero]
  | add z w hz hw => rw [map_add,map_add,map_add,map_add,hz,hw]
  | tmul s c =>
    induction c using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero,map_zero,map_zero,map_zero]
    | add z w hz hw => rw [TensorProduct.tmul_add,map_add,map_add,map_add,map_add,hz,hw]
    | tmul q v =>
      obtain ⟨x,y⟩ := q
      change k (s ⊗ₜ[S] (quadSign a ⟨x,y⟩)) ⊗ₜ[L] ((1:L) ⊗ₜ[S] v) =
        (quadSign (algebraMap S L a) (k (s ⊗ₜ[S] (⟨x,y⟩ : Q)))) ⊗ₜ[L] ((1:L) ⊗ₜ[S] v)
      simp only [quadSign_mk,hk,map_neg]
      exact congrArg (fun t : L => (⟨s * algebraMap S L x,t⟩ : QuadraticAlgebra L (algebraMap S L a) 0) ⊗ₜ[L] ((1:L) ⊗ₜ[S] v)) (mul_neg s ((algebraMap S L) y))

end KaplanskyGeneric

end

section

open scoped TensorProduct
namespace KaplanskyGeneric

/-- Adjoining two independent rational parameters and tensoring with their
generic quaternion algebra preserves absence of zero divisors. -/
theorem quaternion_step {K D : Type*} [Field K] [Ring D] [Nontrivial D] [Algebra K D]
    [FiniteDimensional K D] [NoZeroDivisors D] :
    let S := RatFunc K
    let L := RatFunc S
    let A := S ⊗[K] D
    let B := L ⊗[S] A
    NoZeroDivisors (B ⊗[L] QuaternionAlgebra L (RatFunc.C (RatFunc.X : S)) 0 RatFunc.X) := by
  intro S L A B
  let _ : Nontrivial A := Module.nontrivial_of_finrank_pos (R:=S) (M:=A) (by
    rw [Module.finrank_baseChange]; exact Module.finrank_pos)
  exact second_stage (A:=A) (RatFunc.X : S) (first_stage (K:=K) (D:=D))
    (quadratic_transport (A:=A) (RatFunc.X : S))
    (quaternion_nzd_of_twisted_norm (A:=B) (RatFunc.C (RatFunc.X : S)) RatFunc.X)

end KaplanskyGeneric

end

section

open scoped TensorProduct
namespace KaplanskyEven
universe u

/-- Tensoring an anticommuting family with a quaternion factor adds the two quaternion
generators and multiplies each previous generator by the quaternion volume element. -/
theorem quaternion_step {K A : Type u} [Field K] [Ring A] [Algebra K A]
    {m : ℕ} (c : Fin m → K) (frame : KaplanskyTrans.Frame (A := A) c) (a b : K) :
    KaplanskyTrans.Frame (A := A ⊗[K] QuaternionAlgebra K a 0 b)
      (Fin.cons a (Fin.cons b (fun i => c i * (-(a*b))))) := by
  let Q := QuaternionAlgebra K a 0 b
  let I : Q := ⟨0,1,0,0⟩
  let J : Q := ⟨0,0,1,0⟩
  let H : Q := ⟨0,0,0,1⟩
  have si : I*I = algebraMap K Q a := by ext <;> simp [I,Q]
  have sj : J*J = algebraMap K Q b := by ext <;> simp [J,Q]
  have sh : H*H = algebraMap K Q (-(a*b)) := by ext <;> simp [H,Q]
  have ji : J*I = -(I*J) := by ext <;> simp [I,J,Q]
  have hi : H*I = -(I*H) := by ext <;> simp [I,H,Q]
  have hj : H*J = -(J*H) := by ext <;> simp [J,H,Q]
  obtain ⟨g,sq,anti⟩ := frame
  apply KaplanskyTrans.frame_of_parts a b (fun i => c i*(-(a*b)))
    (fun i => g i ⊗ₜ[K] H) ((1 : A) ⊗ₜ[K] J) ((1 : A) ⊗ₜ[K] I)
  · intro i
    rw [Algebra.TensorProduct.tmul_mul_tmul,sq,sh,Algebra.algebraMap_eq_smul_one (c i),
      TensorProduct.smul_tmul,Algebra.smul_def,Algebra.TensorProduct.algebraMap_apply',map_mul]
  · rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul,sj,Algebra.TensorProduct.algebraMap_apply']
  · rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul,si,Algebra.TensorProduct.algebraMap_apply']
  · rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,ji,TensorProduct.tmul_neg]
  · intro i j ne
    rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,anti i j ne,
      TensorProduct.neg_tmul]
  · intro i
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hj,TensorProduct.tmul_neg]
  · intro i
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hi,TensorProduct.tmul_neg]

/-- Scalar extension carries the same anticommuting family, with its square values
sent along the field inclusion. -/
theorem frame_basechange {K L A : Type u} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] {m : ℕ} (c : Fin m → K) (h : KaplanskyTrans.Frame (A := A) c) :
    KaplanskyTrans.Frame (A := L ⊗[K] A) (fun i => algebraMap K L (c i)) := by
  obtain ⟨g,sq,anti⟩ := h
  refine ⟨fun i => (1 : L) ⊗ₜ[K] g i,?_,?_⟩
  · intro i
    rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul,sq,← Algebra.TensorProduct.algebraMap_apply']
    rfl
  · intro i j ne
    rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
      anti i j ne,TensorProduct.tmul_neg]

/-- The initial one-element frame in the scalar field. -/
theorem frame_one (K : Type u) [Field K] :
    KaplanskyTrans.Frame (A := K) (fun _ : Fin 1 => (1:K)) := by
  exact ⟨fun _ => 1,fun _ => by simp,fun _ _ ne => (ne (Subsingleton.elim _ _)).elim⟩

/-- Nonzero square values are preserved by each quaternion step. -/
theorem quaternion_step_nonzero {K : Type u} [Field K] {m : ℕ}
    (c : Fin m → K) (nz : ∀ i, c i ≠ 0) {a b : K} (an : a ≠ 0) (bn : b ≠ 0) :
    ∀ i, Fin.cons (α := fun _ => K) a (Fin.cons (α := fun _ => K) b (fun j => c j * (-(a*b)))) i ≠ 0 :=
  Fin.cases an (Fin.cases bn (fun i => mul_ne_zero (nz i) (neg_ne_zero.mpr (mul_ne_zero an bn))))

end KaplanskyEven

end

section

open scoped TensorProduct
namespace KaplanskyEven

/-- Countability of rational functions follows from the unique reduced numerator and denominator. -/
theorem countable_rational (K : Type*) [Field K] [Countable K] : Countable (RatFunc K) := by
  let enc (p : Polynomial K) : ℕ →₀ K := p.toFinsupp.coeff
  have pinj : Function.Injective enc := fun _ _ h => Polynomial.toFinsupp_inj.mp (AddMonoidAlgebra.coeff_injective h)
  have : Countable (Polynomial K) := pinj.countable
  apply Function.Injective.countable (f := fun r : RatFunc K => (r.num,r.denom))
  intro r s h
  have hn : r.num = s.num := congrArg Prod.fst h
  have hd : r.denom = s.denom := congrArg Prod.snd h
  calc r = _ := r.num_div_denom.symm
       _ = _ := by rw [hn,hd]
       _ = s := s.num_div_denom

/-- Generic quaternion tensor powers over iterated rational function fields, conditional
only on preservation of the division property when a new generic factor is added. -/
theorem recursive_seed
    (domain_step : ∀ {K D : Type} [Field K] [Ring D] [Nontrivial D] [Algebra K D]
      [FiniteDimensional K D] [NoZeroDivisors D],
      let S := RatFunc K
      let L := RatFunc S
      let A := S ⊗[K] D
      let B := L ⊗[S] A
      NoZeroDivisors (B ⊗[L] QuaternionAlgebra L (RatFunc.C (RatFunc.X : S)) 0 RatFunc.X))
    (r : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NeZero (2 : K)) (_ : Countable K)
      (D : Type) (_ : Ring D) (_ : Nontrivial D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : NoZeroDivisors D), Module.finrank K D = 4^r ∧
      ∃ c : Fin (2*r+1) → K, (∀ i,c i ≠ 0) ∧ KaplanskyTrans.Frame (A := D) c := by
  induction r with
  | zero =>
      exact ⟨ℚ,inferInstance,inferInstance,inferInstance,ℚ,inferInstance,inferInstance,
        inferInstance,inferInstance,inferInstance,by simp,fun _ => 1,fun _ => one_ne_zero,frame_one ℚ⟩
  | succ r ih =>
      obtain ⟨K,fK,two,count,D,rd,nt,alg,fin,nd,rank,c,nz,frame⟩ := ih
      let S := RatFunc K
      let L := RatFunc S
      let A := S ⊗[K] D
      let B := L ⊗[S] A
      let p : L := RatFunc.C (RatFunc.X : S)
      let q : L := RatFunc.X
      let Q := QuaternionAlgebra L p 0 q
      let T := B ⊗[L] Q
      have cntS : Countable S := countable_rational K
      have cntL : Countable L := countable_rational S
      have twoS : NeZero (2:S) := NeZero.nat_of_injective (n := 2) (algebraMap K S).injective
      have twoL : NeZero (2:L) := NeZero.nat_of_injective (n := 2) (algebraMap S L).injective
      have deg : Module.finrank L T=4^(r+1) := by
        change Module.finrank L (B ⊗[L] QuaternionAlgebra L p 0 q) = _
        rw [Module.finrank_tensorProduct,QuaternionAlgebra.finrank_eq_four]
        change Module.finrank L (L ⊗[S] (S ⊗[K] D))*4 = _
        rw [Module.finrank_baseChange,Module.finrank_baseChange,rank,pow_succ]
      have dimpos : 0 < Module.finrank L T := by rw [deg]; positivity
      have nontriv : Nontrivial T := Module.nontrivial_of_finrank_pos dimpos
      have finite : FiniteDimensional L T := Module.finite_of_finrank_pos dimpos
      have dom : NoZeroDivisors T := domain_step (K := K) (D := D)
      let c' (i : Fin (2*r+1)) : L := algebraMap S L (algebraMap K S (c i))
      have h' : KaplanskyTrans.Frame (A := B) c' :=
        frame_basechange _ (frame_basechange c frame)
      have cnz (i) : c' i ≠ 0 :=
        (map_ne_zero (algebraMap S L)).mpr ((map_ne_zero (algebraMap K S)).mpr (nz i))
      have pn : p ≠ 0 := (map_ne_zero RatFunc.C).mpr RatFunc.X_ne_zero
      have qn : q ≠ 0 := RatFunc.X_ne_zero
      exact ⟨L,inferInstance,twoL,cntL,T,inferInstance,nontriv,inferInstance,finite,dom,deg,
        Fin.cons p (Fin.cons q (fun i => c' i * (-(p*q)))),
        quaternion_step_nonzero c' cnz pn qn,quaternion_step c' h' p q⟩

end KaplanskyEven

end

section

/-- A countable generic quaternion tensor power with an anticommuting frame. -/
theorem KaplanskyEven.all_seeds (r : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NeZero (2 : K)) (_ : Countable K)
      (D : Type) (_ : Ring D) (_ : Nontrivial D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : NoZeroDivisors D), Module.finrank K D = 4^r ∧
      ∃ c : Fin (2*r+1) → K, (∀ i,c i ≠ 0) ∧ KaplanskyTrans.Frame (A := D) c :=
  KaplanskyEven.recursive_seed (@KaplanskyGeneric.quaternion_step) r

end

end

section

section

namespace KaplanskyEven

/-- Each weight profile of the unit or of one generator differs from all the others. -/
theorem independent_frame {K A : Type*} [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [NeZero (2 : K)] {m : ℕ} (two : 2 ≤ m) (g : Fin m → Aˣ)
    (anti : ∀ i j, i ≠ j → (g i : A)*(g j : A) = -((g j : A)*(g i : A))) :
    LinearIndependent K (Fin.cons (1:A) (fun i => (g i : A))) := by
  classical
  let _ : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr two
  let T (k : Fin m) : A →ₗ[K] A :=
    { toFun := fun x => (g k : A) * x * ((g k)⁻¹ : Aˣ)
      map_add' := fun _ _ => by simp [mul_add,add_mul]
      map_smul' := fun r x => by simp [Algebra.mul_smul_comm,Algebra.smul_mul_assoc] }
  let χ (i : Fin (m+1)) (k : Fin m) : K :=
    Fin.cases 1 (fun j => if j = k then 1 else -1) i
  have diff : (-1 : K) ≠ 1 := by
    intro bad
    exact NeZero.ne (2 : K) (by linear_combination -bad)
  refine KaplanskyIndex.independent_of_profiles _ ?_ T χ ?_ ?_
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact one_ne_zero
    · exact (g j).ne_zero
  · intro i k
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [T,χ]
    · by_cases eq : j=k
      · subst j
        simp [T,χ,mul_assoc]
      · change (g k : A)*(g j : A)*((g k)⁻¹ : Aˣ) = _
        rw [anti k j (Ne.symm eq)]
        simp [χ,eq,neg_mul,mul_assoc]
  · intro i j ne
    revert ne
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · simp
      · obtain ⟨k,hk⟩ := exists_ne b
        exact ⟨k,by simpa [χ,hk.symm] using diff.symm⟩
    · refine Fin.cases ?_ (fun b ne => ?_) j
      · intro _
        obtain ⟨k,hk⟩ := exists_ne a
        exact ⟨k,by simpa [χ,hk.symm] using diff⟩
      · have ab : a ≠ b := fun h => ne (congrArg Fin.succ h)
        exact ⟨a,by simpa [χ,ab.symm] using diff.symm⟩

/-- In a sum of pairwise anticommuting elements all mixed square terms cancel. -/
theorem frame_sum_square {ι A : Type*} [Ring A] (f : ι → A)
    (anti : ∀ i j, i ≠ j → f i*f j = -(f j*f i)) (S : Finset ι) :
    (∑ i ∈ S, f i)^2 = ∑ i ∈ S, (f i)^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i s outside ih =>
    rw [Finset.sum_insert outside,Finset.sum_insert outside,pow_two,add_mul,mul_add,mul_add]
    have cross : f i*(∑ j ∈ s,f j) = -((∑ j ∈ s,f j)*f i) := by
      rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j hj => anti i j (fun eq => outside (eq ▸ hj)))
    rw [cross,←pow_two,←pow_two,ih]
    abel

/-- A frame of m ≥ 2 anticommuting elements with nonzero scalar squares in a
division algebra gives a diagonal anisotropic form of dimension m + 1. -/
theorem frame_anisotropic {K A : Type*} [Field K] [Ring A] [Nontrivial A] [NoZeroDivisors A]
    [Algebra K A] [NeZero (2 : K)] {m : ℕ} (two : 2 ≤ m) (a : Fin m → K)
    (nz : ∀ i, a i ≠ 0) (g : Fin m → A)
    (sq : ∀ i, g i ^ 2 = algebraMap K A (a i))
    (anti : ∀ i j, i ≠ j → g i*g j = -(g j*g i))
    (x : K) (v : Fin m → K) (eq : x^2 = ∑ i, a i*(v i)^2) :
    x = 0 ∧ v = 0 := by
  classical
  have units (i : Fin m) : IsUnit (g i) := by
    apply (isUnit_pow_iff (n := 2) (by decide)).mp
    rw [sq]
    exact (isUnit_iff_ne_zero.mpr (nz i)).map _
  let V : Fin (m+1) → A := Fin.cons (1:A) g
  have ind : LinearIndependent K V := by
    simpa only [IsUnit.unit_spec,V] using independent_frame (K := K) two
      (fun i => (units i).unit) (by simpa only [IsUnit.unit_spec] using anti)
  let z := ∑ i, v i • g i
  have square : z^2 = algebraMap K A (x^2) := by
    rw [eq,map_sum]
    apply (frame_sum_square (fun i => v i • g i) ?_ Finset.univ).trans
    · apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def, (show Commute (algebraMap K A (v i)) (g i)
        from Algebra.commutes _ _).mul_pow, sq, mul_comm (a i),map_mul,map_pow]
    · intro i j ne
      simp [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,anti i j ne,mul_comm (v i)]
  have commute := Algebra.commutes (R := K) (A := A) x z
  have zero : (algebraMap K A x-z)*(algebraMap K A x+z)=0 := by
    rw [sub_mul,mul_add,mul_add,←pow_two,←pow_two,square,map_pow,commute]
    abel
  have no_relation (c : K) (e : c • (1:A)+z=0) : c=0 ∧ v=0 := by
    let coeff : Fin (m+1) → K := Fin.cons c v
    have zz : ∑ i, coeff i • V i = 0 := by
      rw [Fin.sum_univ_succ]
      simpa [coeff,V,z] using e
    have zeroes := Fintype.linearIndependent_iff.mp ind coeff zz
    exact ⟨zeroes 0,funext fun i => zeroes i.succ⟩
  rcases eq_zero_or_eq_zero_of_mul_eq_zero zero with h | h
  · have e : (-x) • (1:A)+z = 0 := by
      simpa [Algebra.smul_def,neg_add_rev,sub_eq_add_neg,add_comm] using congrArg Neg.neg h
    obtain ⟨ne,y⟩ := no_relation (-x) e
    exact ⟨neg_eq_zero.mp ne,y⟩
  · exact no_relation x (by simpa [Algebra.smul_def] using h)

end KaplanskyEven

end

section

namespace KaplanskyEven
open QuadraticMap QuadraticForm
universe u

/-- A nondegenerate Clifford frame in a domain persists as an explicit anisotropic
diagonal form over its scalar field. -/
theorem frame_dimension {K A : Type u} [Field K] [Ring A] [Nontrivial A] [NoZeroDivisors A]
    [Algebra K A] [NeZero (2:K)] {m : ℕ} (two : 2 ≤ m) (c : Fin m → K)
    (nonzero : ∀ i, c i ≠ 0) (frame : KaplanskyTrans.Frame (A := A) c) :
    m+1 ∈ anisotropicDims K := by
  obtain ⟨g,sq,anti⟩ := frame
  let weights : Fin (m+1) → K := Fin.cons 1 (fun i => -(c i))
  refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares K weights,?_⟩
  intro v h
  simp only [weightedSumSquares_apply,Fin.sum_univ_succ,smul_eq_mul,weights,Fin.cons_zero,
    Fin.cons_succ,one_mul,neg_mul,Finset.sum_neg_distrib] at h
  have eq : v 0 ^ 2 = ∑ i, c i*(v i.succ)^2 := by
    apply sub_eq_zero.mp
    simpa only [pow_two,sub_eq_add_neg] using h
  obtain ⟨v0,vs⟩ := frame_anisotropic two c nonzero g (by simpa [pow_two] using sq) anti _ _ eq
  funext i
  exact Fin.cases v0 (fun j => congrFun vs j) i

end KaplanskyEven

end

section

namespace KaplanskyEven
open scoped TensorProduct
universe u

/-- An explicit lower-bound diagonal; the same tuple works throughout a tower preserving
the scalar extension of its algebra as a domain. -/
theorem frame_diagonal {K A : Type u} [Field K] [Ring A] [Nontrivial A] [NoZeroDivisors A]
    [Algebra K A] [NeZero (2:K)] {m : ℕ} (two : 2 ≤ m) (c : Fin m → K)
    (nonzero : ∀ i, c i ≠ 0) (frame : KaplanskyTrans.Frame (A := A) c)
    (v : Fin (m+1) → K)
    (h : ∑ i, Fin.cons (α := fun _ => K) 1 (fun j => -(c j)) i * v i ^ 2 = 0) : v = 0 := by
  obtain ⟨g,sq,anti⟩ := frame
  rw [Fin.sum_univ_succ,Fin.cons_zero,one_mul] at h
  simp only [Fin.cons_succ,neg_mul,Finset.sum_neg_distrib,←sub_eq_add_neg] at h
  obtain ⟨v0,vs⟩ := frame_anisotropic two c nonzero g (by simpa [pow_two] using sq) anti _ _ (sub_eq_zero.mp h)
  funext i
  exact Fin.cases v0 (fun j => congrFun vs j) i

theorem frame_diagonal_over {K A L : Type u} [Field K] [Ring A] [Algebra K A] [Field L]
    [Algebra K L] [NeZero (2:L)] [Nontrivial (L ⊗[K] A)] [NoZeroDivisors (L ⊗[K] A)]
    {m : ℕ} (two : 2 ≤ m) (c : Fin m → K) (nonzero : ∀ i, c i ≠ 0)
    (frame : KaplanskyTrans.Frame (A := A) c) (v : Fin (m+1) → L)
    (h : ∑ i, algebraMap K L (Fin.cons (α := fun _ => K) 1 (fun j => -(c j)) i) * v i ^ 2 = 0) : v = 0 := by
  have mapped := frame_basechange (L := L) c frame
  apply frame_diagonal two (fun i => algebraMap K L (c i)) (fun i => (map_ne_zero (algebraMap K L)).mpr (nonzero i)) mapped v
  simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,map_one,map_neg] using h

end KaplanskyEven

end

end

section

/-! The direct-limit and diagonalization arguments generalize the accepted six-dimensional
Kaplansky reduction (Open Math Agents PR 9836). -/

namespace KaplanskyEven

open KaplanskyUInvariant QuadraticMap QuadraticForm

/-- Once all diagonals of dimension `k` are isotropic, every larger quadratic form is isotropic. -/
theorem not_mem_anisotropicDims_of_ge {F : Type} [Field F] [NeZero (2 : F)] {k n : ℕ}
    (split : ∀ w : Fin k → F, ∃ v : Fin k → F, v ≠ 0 ∧ (∑ i, w i * v i^2) = 0)
    (hn : k ≤ n) : n ∉ anisotropicDims F := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hn
  rintro hmem
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmem
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hW : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    simpa using hQ _ h0
  have hm : Module.finrank F (Fin (k+s) → F) = k+s := by simp
  generalize Module.finrank F (Fin (k+s) → F) = N at w hW hm
  subst N
  obtain ⟨v, hne, hz⟩ := split (fun i => w (i.castAdd s))
  let u : Fin (k+s) → F := Fin.append v (fun _ : Fin s => 0)
  have hu : weightedSumSquares F w u = 0 := by
    simpa only [weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_add,
      u, Fin.append_left, Fin.append_right, zero_pow (by decide : 2≠0), zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
      ← _root_.sq] using hz
  have zero := hW u hu
  apply hne
  funext i
  simpa [u] using congr_fun zero (i.castAdd s)

/-- The prescribed lower diagonal remains anisotropic in the direct limit, and all
forms of the next dimension acquire an isotropic vector there. -/
theorem isGreatest_directLimit (n : ℕ) (G : ℕ → Type) [∀ i, Field (G i)]
    (trans : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G (fun i j h => trans i j h)]
    (a : Fin n → G 0) [NeZero (2 : G 0)]
    (anis : ∀ (i : ℕ) (x : Fin n → G i), (∑ r, trans 0 i (Nat.zero_le i) (a r) * x r^2) = 0 → x = 0)
    (split : ∀ (i : ℕ) (w : Fin (n+1) → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin (n+1) → G m),
      v ≠ 0 ∧ (∑ r, trans i m him (w r) * v r^2) = 0) :
    IsGreatest (anisotropicDims (DirectLimit G trans)) n := by
  let K := DirectLimit G trans
  let of : ∀ i, G i →+* K := fun i => DirectLimit.Ring.of G trans i
  have : NeZero (2 : K) := ⟨fun hz => NeZero.ne (2 : G 0) ((of 0).injective (by simpa only [map_ofNat,map_zero] using hz : of 0 2=of 0 0))⟩
  have compat {i j : ℕ} (h : i ≤ j) (u : G i) : of j (trans i j h u) = of i u :=
    DirectLimit.Ring.of_f (G := G) (f := trans) h u
  have lift {ι : Type} [Fintype ι] (u : ι → K) : ∃ (i : ℕ) (v : ι → G i), ∀ r, of i (v r) = u r := by
    choose j v h using fun r => DirectLimit.exists_eq_mk trans (u r)
    let i := Finset.univ.sup j
    refine ⟨i, fun r => trans (j r) i (Finset.le_sup (Finset.mem_univ r)) (v r), ?_⟩
    intro r
    change DirectLimit.Ring.of G trans i _ = u r
    rw [DirectLimit.Ring.of_f]
    exact (h r).symm
  change IsGreatest (anisotropicDims K) n
  constructor
  · refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares K (fun s => of 0 (a s)), ?_⟩
    intro u hu
    obtain ⟨i, v, hv⟩ := lift u
    have hz : (∑ r, trans 0 i (Nat.zero_le i) (a r) * v r^2)=0 := by
      apply (of i).injective
      rw [map_sum, map_zero]
      simpa only [map_mul, map_pow, compat, ← hv, weightedSumSquares_apply,
        smul_eq_mul, _root_.sq] using hu
    have hzero := anis i v hz
    funext r
    simp [← hv r, hzero]
  · have upper (w : Fin (n+1) → K) : ∃ v : Fin (n+1) → K, v ≠ 0 ∧ (∑ r, w r*v r^2)=0 := by
      obtain ⟨i, wi, hwi⟩ := lift w
      obtain ⟨m, him, v, nv, iso⟩ := split i wi
      refine ⟨fun r => of m (v r), ?_, ?_⟩
      · intro zero
        apply nv
        funext r
        apply (of m).injective
        simpa using congr_fun zero r
      · have mapped := congrArg (of m) iso
        simp only [map_sum, map_zero, map_mul, map_pow] at mapped
        simpa only [compat, ← hwi] using mapped
    intro s hs
    by_contra h
    exact not_mem_anisotropicDims_of_ge upper (by omega : n+1 ≤ s) hs

/-- The official `IsUInvariant` proposition follows with the direct limit itself as witness. -/
theorem isUInvariant_of_tower (n : ℕ) (G : ℕ → Type) [∀ i, Field (G i)]
    (trans : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G (fun i j h => trans i j h)]
    (a : Fin n → G 0) [NeZero (2 : G 0)]
    (anis : ∀ (i : ℕ) (x : Fin n → G i), (∑ r, trans 0 i (Nat.zero_le i) (a r) * x r^2)=0 → x=0)
    (split : ∀ (i : ℕ) (w : Fin (n+1) → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin (n+1) → G m),
      v ≠ 0 ∧ (∑ r, trans i m him (w r) * v r^2)=0) : IsUInvariant n := by
  let K := DirectLimit G trans
  let e := DirectLimit.Ring.of G trans 0
  have two : NeZero (2 : K) := ⟨fun hz => NeZero.ne (2 : G 0) (e.injective (by simpa only [map_ofNat,map_zero] using hz : e 2 = e 0))⟩
  exact ⟨K, inferInstance, two, isGreatest_directLimit n G trans a anis split⟩

end KaplanskyEven

end

section

open scoped TensorProduct
namespace KaplanskyEven

/-- A division algebra equipped with an anticommuting frame supplies exactly the
initial condition, persistent anisotropic diagonal and individual countable extension
steps used by the tower. -/
theorem tower_inputs_of_frame (r : ℕ) (hr : 0 < r) (K D : Type) [Field K]
    [NeZero (2 : K)] [Ring D] [Nontrivial D] [Algebra K D] [FiniteDimensional K D]
    [NoZeroDivisors D] (rank : Module.finrank K D = 4^r) (c : Fin (2*r+1) → K)
    (nz : ∀ i, c i ≠ 0) (frame : KaplanskyTrans.Frame (A := D) c) :
    ∃ (a : Fin (2*r+2) → K) (Good : ∀ (F : Type) [Field F], (K →+* F) → Prop),
      Good K (RingHom.id K) ∧
      (∀ (F : Type) [Field F] (f : K →+* F), Good F f →
        ∀ x : Fin (2*r+2) → F, (∑ i, f (a i)*x i^2) = 0 → x = 0) ∧
      (∀ (F : Type) [Field F] [Countable F] (f : K →+* F), Good F f →
        ∀ w : Fin (2*r+3) → F, ∃ (L : Type) (_ : Field L) (_ : Countable L) (g : F →+* L),
          Good L (g.comp f) ∧ ∃ v : Fin (2*r+3) → L, v ≠ 0 ∧ (∑ i, g (w i)*v i^2) = 0) := by
  let Good (F : Type) [Field F] (f : K →+* F) : Prop :=
    letI : Algebra K F := f.toAlgebra
    NoZeroDivisors (F ⊗[K] D)
  refine ⟨Fin.cons (α := fun _ => K) 1 (fun j => -(c j)), Good, ?_, ?_, ?_⟩
  · let e := Algebra.TensorProduct.lid K D
    exact Function.Injective.noZeroDivisors e e.injective (map_zero e) (map_mul e)
  · intro F _ f good x hx
    let : Algebra K F := f.toAlgebra
    let : NeZero (2 : F) := NeZero.nat_of_injective (n := 2) f.injective
    let : NoZeroDivisors (F ⊗[K] D) := good
    let : Nontrivial (F ⊗[K] D) := Module.nontrivial_of_finrank_pos (R := F) (by
      rw [Module.finrank_baseChange]; exact Module.finrank_pos)
    exact frame_diagonal_over (A := D) (by omega) c nz frame x hx
  · intro F _ _ f good w
    let : Algebra K F := f.toAlgebra
    let : NeZero (2 : F) := NeZero.nat_of_injective (n := 2) f.injective
    let : NoZeroDivisors (F ⊗[K] D) := good
    let : Nontrivial (F ⊗[K] D) := Module.nontrivial_of_finrank_pos (R := F) (by
      rw [Module.finrank_baseChange]; exact Module.finrank_pos)
    obtain ⟨L, fieldL, algL, countL, dom, v, nv, hv⟩ :=
      KaplanskyTrans.preserve_small_algebra_countable r F (F ⊗[K] D)
        (by rw [Module.finrank_baseChange, rank]; exact KaplanskyTrans.quaternion_dimension_bound r) w
    let g := algebraMap F L
    let : Algebra K L := (g.comp f).toAlgebra
    let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let e : (L ⊗[K] D) ≃ₐ[L] L ⊗[F] (F ⊗[K] D) := AlgEquiv.ofLinearEquiv
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L D).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ => by simp)
    exact ⟨L, fieldL, countL, g,
      Function.Injective.noZeroDivisors e e.injective (map_zero e) (map_mul e), v, nv, hv⟩

end KaplanskyEven

namespace KaplanskyEven

/-- At every even dimension above two there is a countable seed and a preservation
predicate that satisfies all the hypotheses of the countable tower construction. -/
theorem all_tower_inputs (r : ℕ) (hr : 0 < r) :
    ∃ (K : Type) (_ : Field K) (_ : NeZero (2 : K)) (_ : Countable K)
      (a : Fin (2*r+2) → K) (Good : ∀ (F : Type) [Field F], (K →+* F) → Prop),
      Good K (RingHom.id K) ∧
      (∀ (F : Type) [Field F] (f : K →+* F), Good F f →
        ∀ x : Fin (2*r+2) → F, (∑ i, f (a i)*x i^2) = 0 → x = 0) ∧
      (∀ (F : Type) [Field F] [Countable F] (f : K →+* F), Good F f →
        ∀ w : Fin (2*r+3) → F, ∃ (L : Type) (_ : Field L) (_ : Countable L) (g : F →+* L),
          Good L (g.comp f) ∧ ∃ v : Fin (2*r+3) → L, v ≠ 0 ∧ (∑ i, g (w i)*v i^2) = 0) := by
  obtain ⟨K, fieldK, two, count, D, ringD, nontriv, alg, fin, dom, rank, c, nz, frame⟩ := all_seeds r
  obtain ⟨a, good, initial, lower, advance⟩ := tower_inputs_of_frame r hr K D rank c nz frame
  exact ⟨K, fieldK, two, count, a, good, initial, lower, advance⟩

end KaplanskyEven

namespace KaplanskyEven

open KaplanskyUInvariant QuadraticMap QuadraticForm

/-- Over the three-element field, two squares form an anisotropic binary form and
every ternary diagonal form is isotropic. -/
theorem isGreatest_zmod_three : IsGreatest (anisotropicDims (ZMod 3)) 2 := by
  let : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have binary : ∀ x y : ZMod 3, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by decide
  have ternary : ∀ a b c : ZMod 3, ∃ x y z : ZMod 3,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ a*x^2 + b*y^2 + c*z^2 = 0 := by decide
  constructor
  · refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares (ZMod 3) (fun _ : Fin 2 => (1 : ZMod 3)), ?_⟩
    intro v h
    obtain ⟨h0,h1⟩ := binary (v 0) (v 1) (by
      simpa [weightedSumSquares_apply, Fin.sum_univ_succ, pow_two] using h)
    funext i
    fin_cases i <;> assumption
  · have split (w : Fin 3 → ZMod 3) : ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ (∑ i, w i * v i^2) = 0 := by
      obtain ⟨x,y,z,ne,h⟩ := ternary (w 0) (w 1) (w 2)
      refine ⟨![x,y,z], ?_, ?_⟩
      · intro hz
        rcases ne with hx | hy | hzz
        · exact hx (congrFun hz 0)
        · exact hy (congrFun hz 1)
        · exact hzz (congrFun hz 2)
      · simpa [Fin.sum_univ_succ, add_assoc] using h
    intro s hs
    by_contra contra
    exact not_mem_anisotropicDims_of_ge split (by omega : 3 ≤ s) hs

theorem isUInvariant_two : IsUInvariant 2 :=
  ⟨ZMod 3, inferInstance, ⟨by decide⟩, isGreatest_zmod_three⟩

end KaplanskyEven

end

end

section

namespace KaplanskyConstruction

structure Stage (K : Type) [Field K] (n : ℕ)
    (Good : ∀ (F : Type) [Field F], (K →+* F) → Prop) where
  F : Type
  [field : Field F]
  [countable : Countable F]
  base : K →+* F
  good : Good F base
  todo : ℕ → Fin (n + 1) → F

variable {K : Type} [Field K] {n : ℕ} {Good : ∀ (F : Type) [Field F], (K →+* F) → Prop}

instance (s : Stage K n Good) : Field s.F := s.field
instance (s : Stage K n Good) : Countable s.F := s.countable

noncomputable def enumerate (F : Type) [Field F] [Countable F] (n : ℕ) :
    ℕ → Fin (n+1) → F := by
  classical
  let _ := Encodable.ofCountable (Fin (n+1) → F)
  exact fun j => (Encodable.decode j).getD 0

theorem enumerate_surjective (F : Type) [Field F] [Countable F] (n : ℕ) :
    Function.Surjective (enumerate F n) := by
  classical
  let _ := Encodable.ofCountable (Fin (n+1) → F)
  intro w
  exact ⟨Encodable.encode w, by simp [enumerate]⟩

end KaplanskyConstruction

end

section

namespace KaplanskyConstruction
variable (F : ℕ → Type) [∀ i, Field (F i)] (g : ∀ i, F i →+* F (i+1))

def transition (i j : ℕ) (h : i ≤ j) : F i →+* F j :=
  Nat.leRecOn (C := fun k => F i →+* F k) h (fun {k} f => (g k).comp f) (RingHom.id (F i))

theorem transition_self (i : ℕ) : transition F g i i le_rfl = RingHom.id (F i) :=
  Nat.leRecOn_self _

theorem transition_succ {i j : ℕ} (h : i ≤ j) :
    transition F g i (j+1) (Nat.le_succ_of_le h) = (g j).comp (transition F g i j h) :=
  Nat.leRecOn_succ h _

theorem transition_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (transition F g j k hjk).comp (transition F g i j hij) =
      transition F g i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [transition_self, RingHom.id_comp]
  | succ m hm ih =>
    rw [transition_succ F g hm, transition_succ F g (hij.trans hm), RingHom.comp_assoc, ih]

theorem transition_directed :
    DirectedSystem F (fun i j h => transition F g i j h) where
  map_self := fun i x => DFunLike.congr_fun (transition_self F g i) x
  map_map := fun _ _ _ hij hjk x => DFunLike.congr_fun (transition_comp F g hij hjk) x

end KaplanskyConstruction

end

section

namespace KaplanskyConstruction
variable {K : Type} [Field K] {n : ℕ} {Good : ∀ (F : Type) [Field F], (K →+* F) → Prop}

/-- At time t split the form designated by the queue. At the next stage,
insert its newly enumerated forms and carry each earlier request forward. -/
structure Successor (s : Stage K n Good) (t : ℕ) where
  dest : Stage K n Good
  map : s.F →+* dest.F
  link : dest.base = map.comp s.base
  split : ∃ v : Fin (n+1) → dest.F, v ≠ 0 ∧ ∑ i, map (s.todo t i) * v i ^ 2 = 0
  queue : ∀ q, dest.todo q = if (Nat.unpair q).1 = t+1 then enumerate dest.F n (Nat.unpair q).2
    else fun i => map (s.todo q i)

theorem successor_exists (advance : ∀ (F : Type) [Field F] [Countable F] (f : K →+* F),
    Good F f → ∀ w : Fin (n+1) → F,
      ∃ (L : Type) (_ : Field L) (_ : Countable L) (g : F →+* L),
        Good L (g.comp f) ∧ ∃ v : Fin (n+1) → L, v ≠ 0 ∧ ∑ i, g (w i) * v i^2 = 0)
    (s : Stage K n Good) (t : ℕ) : Nonempty (Successor s t) := by
  classical
  obtain ⟨L, fieldL, countL, g, good, point⟩ := advance s.F s.base s.good (s.todo t)
  let dest : Stage K n Good := {
    F := L, field := fieldL, countable := countL, base := g.comp s.base, good := good
    todo := fun q => if (Nat.unpair q).1 = t+1 then enumerate L n (Nat.unpair q).2
      else fun i => g (s.todo q i) }
  exact ⟨⟨dest,g,rfl,point,fun _ => rfl⟩⟩

/-- Enumerate all finite forms over all stages by pairing the stage number and
the index of the form there. Each request is split by its assigned time. -/
theorem scheduled_tower [Countable K] (initial : Good K (RingHom.id K))
    (next : ∀ (s : Stage K n Good) (t : ℕ), Nonempty (Successor s t)) :
    ∃ (G : ℕ → Type) (_ : ∀ i, Field (G i))
      (trans : ∀ i j, i ≤ j → G i →+* G j)
      (_ : DirectedSystem G (fun i j h => trans i j h)) (base : ∀ i, K →+* G i),
      (∀ i, Good (G i) (base i)) ∧
      (∀ i j (h : i ≤ j), (trans i j h).comp (base i) = base j) ∧
      ∀ (i : ℕ) (w : Fin (n+1) → G i), ∃ (m : ℕ) (h : i ≤ m) (v : Fin (n+1) → G m),
        v ≠ 0 ∧ ∑ r, trans i m h (w r) * v r ^ 2 = 0 := by
  classical
  let start : Stage K n Good := {
    F := K, base := RingHom.id K, good := initial
    todo := fun q => enumerate K n (Nat.unpair q).2 }
  let step (s : Stage K n Good) (t : ℕ) := Classical.choice (next s t)
  let S (t : ℕ) : Stage K n Good := Nat.rec start (fun i s => (step s i).dest) t
  let G (t : ℕ) := (S t).F
  let fieldG : ∀ i, Field (G i) := fun i => (S i).field
  let g (t : ℕ) : @RingHom (G t) (G (t+1)) (fieldG t).toNonAssocSemiring (fieldG (t+1)).toNonAssocSemiring := (step (S t) t).map
  let trans := @transition G fieldG g
  let base (i : ℕ) : @RingHom K (G i) inferInstance (fieldG i).toNonAssocSemiring := (S i).base
  have link (i : ℕ) : base (i+1) = (g i).comp (base i) := (step (S i) i).link
  refine ⟨G,fieldG,trans,@transition_directed G fieldG g,base,fun i => (S i).good,?_,?_⟩
  · intro i j h
    induction j, h using Nat.le_induction with
    | base => exact (congrArg (fun f : @RingHom (G i) (G i) (fieldG i).toNonAssocSemiring (fieldG i).toNonAssocSemiring => f.comp (base i)) (@transition_self G fieldG g i)).trans (RingHom.id_comp _)
    | succ k hk ih =>
      exact (show (trans i (k+1) _).comp (base i) = (g k).comp (base k) by
        rw [show trans i (k+1) _ = (g k).comp (trans i k hk) from @transition_succ G fieldG g _ _ hk, RingHom.comp_assoc, ih]).trans (link k).symm
  · intro i w
    obtain ⟨j, hj⟩ := @enumerate_surjective (G i) (fieldG i) (S i).countable n w
    let q := Nat.pair i j
    have key : Nat.unpair q = (i,j) := Nat.unpair_pair i j
    have first : (S i).todo q = w := by
      cases i with
      | zero =>
        change enumerate K n (Nat.unpair q).2 = w
        rw [key]
        exact hj
      | succ k =>
        rw [show (S (k+1)).todo q = _ from (step (S k) k).queue q]
        simpa only [key, if_true] using hj
    have propagate (k : ℕ) (hk : i ≤ k) :
        (S k).todo q = fun l => trans i k hk (w l) := by
      induction k, hk using Nat.le_induction with
      | base => simpa only [trans, transition_self, RingHom.id_apply] using first
      | succ k hk ih =>
        rw [show (S (k+1)).todo q = _ from (step (S k) k).queue q]
        simp only [key, if_neg (show i ≠ k+1 by omega)]
        funext l
        rw [ih]
        exact (DFunLike.congr_fun (@transition_succ G fieldG g _ _ hk) (w l)).symm
    have hiq : i ≤ q := Nat.left_le_pair i j
    obtain ⟨v, nonzero, point⟩ := (step (S q) q).split
    refine ⟨q+1, Nat.le_succ_of_le hiq, v, nonzero, ?_⟩
    rw [propagate q hiq] at point
    simpa only [trans, @transition_succ G fieldG g _ _ hiq, RingHom.comp_apply, g] using point

end KaplanskyConstruction

end

section

namespace KaplanskyEven

open KaplanskyUInvariant KaplanskyConstruction

/-- The direct limit of the scheduled tower witnesses every positive even value.
The binary case already occurs over the three-element field. -/
theorem all_positive_even (n : ℕ) (hn : Even n) (hn₀ : n ≠ 0) : IsUInvariant n := by
  by_cases htwo : n = 2
  · simpa only [htwo] using isUInvariant_two
  obtain ⟨k, hk⟩ := hn
  let r := k-1
  have hr : 0 < r := by dsimp [r]; omega
  have hdim : n = 2*r+2 := by dsimp [r]; omega
  rw [hdim]
  obtain ⟨K, fieldK, two, count, a, good, initial, lower, advance⟩ := all_tower_inputs r hr
  obtain ⟨G, fieldG, trans, directed, base, kept, compat, split⟩ :=
    scheduled_tower (n := 2*r+2) (Good := good) initial (successor_exists advance)
  let : NeZero (2 : G 0) := NeZero.nat_of_injective (n := 2) (base 0).injective
  apply isUInvariant_of_tower (2*r+2) G trans (fun i => base 0 (a i)) _ split
  intro j x hx
  apply lower (G j) (base j) (kept j) x
  have map_base (i : Fin (2*r+2)) :
      trans 0 j (Nat.zero_le j) (base 0 (a i)) = base j (a i) :=
    DFunLike.congr_fun (compat 0 j (Nat.zero_le j)) (a i)
  simpa only [map_base] using hx

end KaplanskyEven

end

theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.even := KaplanskyEven.all_positive_even
