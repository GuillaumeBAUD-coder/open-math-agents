import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Higman-type lower bound for the number of groups of order `2^m` (`m ≥ 3`):
`2^(2*m^3) ≤ g (2^m)^27 * 2^(12*m^2)`.

We construct an explicit family of class-two central extensions of `(Fin d → ZMod 2)` by
`(Fin s → ZMod 2)` (`s ≤ d`, `d + s = m`) determined by a biadditive form whose first `s`
diagonal squares are pinned to the standard basis of the fiber. Any two members isomorphic
to the same reference group whose generator images share the same base projections must
agree on all squares and commutators, hence on the entire fiber and on every parameter slot.
Bounding the fiber size by `2^(d^2)` and optimizing `(d, s)` in each residue class of
`m mod 3` yields the required bound.
-/

namespace OMA.Erdos1160Higman

open CategoryTheory
open scoped BigOperators commutatorElement

private def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

private def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }

private instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance

private noncomputable abbrev modelOfTable {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance

private def grpMul (G : FiniteGrp) (a b : G) : G := a * b

private lemma modelOfTable_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    grpMul (modelOfTable t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b

private noncomputable def tableClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (modelOfTable t)

private lemma iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (grpMul G a b) = grpMul H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩

private lemma range_tableClass (n : ℕ) : Set.range (@tableClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨modelOfTable t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (modelOfTable_mul t a b)).trans
      (e.apply_symm_apply (e a * e b))

private lemma orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_tableClass]
  exact Set.finite_range _

private lemma card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]

private lemma card_le_of_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let classOf (a : A) : orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (orderClasses n) := (orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound classOf (Nat.card C)
  intro c
  let F := {a : A // classOf a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) : C := code a.val r.val (transport a)
    exact Nat.card_le_card_of_injective encode (fun {a b} h =>
      Subtype.ext (sep a.val b.val r.val (transport a) (transport b) h))
  · have : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ Nat.card C
    simp

private structure BiExt {V W : Type*} [AddCommGroup V] [AddCommGroup W] (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BiExt

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] {B : V →+ V →+ W}

private lemma ext {x y : BiExt B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all

private instance : Mul (BiExt B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩

private instance : One (BiExt B) := ⟨⟨0, 0⟩⟩

private instance : Inv (BiExt B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩

@[simp] private lemma mul_base (x y : BiExt B) : (x * y).base = x.base + y.base := rfl
@[simp] private lemma mul_fiber (x y : BiExt B) :
    (x * y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] private lemma inv_base (x : BiExt B) : (x⁻¹).base = -x.base := rfl
@[simp] private lemma inv_fiber (x : BiExt B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] private lemma one_base : (1 : BiExt B).base = 0 := rfl
@[simp] private lemma one_fiber : (1 : BiExt B).fiber = 0 := rfl

private instance : Group (BiExt B) where
  mul_assoc x y z := by
    apply BiExt.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BiExt.ext <;> simp
  mul_one x := by
    apply BiExt.ext <;> simp
  inv_mul_cancel x := by
    apply BiExt.ext <;> simp

private def toProd (B : V →+ V →+ W) : BiExt B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card (B : V →+ V →+ W) : Nat.card (BiExt B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (toProd B), Nat.card_prod]

private lemma comm_eq (x y : BiExt B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BiExt.ext <;> simp [map_add, map_neg]
  abel

private lemma double_zero {k : ℕ} (w : Fin k → ZMod 2) : w + w = 0 := by
  funext i
  exact (show ∀ z : ZMod 2, z + z = 0 by decide) (w i)

private lemma sq_eq_of_base_eq {s : ℕ} {B : V →+ V →+ (Fin s → ZMod 2)}
    {a b : BiExt B} (h : a.base = b.base) : a * a = b * b := by
  apply BiExt.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]

private lemma comm_eq_of_base_eq {a b c d : BiExt B}
    (hac : a.base = c.base) (hbd : b.base = d.base) : ⁅a, b⁆ = ⁅c, d⁆ := by
  rw [comm_eq, comm_eq, hac, hbd]

end BiExt

private abbrev Vec (k : ℕ) := Fin k → ZMod 2
private abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d - s)
private abbrev Param (d s : ℕ) := Slot d s → Vec s

private def basis {k : ℕ} (i : Fin k) : Vec k := Pi.single i 1

private def entry {d s : ℕ} (t : Param d s) (i j : Fin d) : Vec s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val, h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0

private lemma entry_fixed {d s : ℕ} {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]

private lemma entry_upper {d s : ℕ} {t : Param d s} {i j : Fin d} (h : i < j) :
    entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]

private lemma entry_injective {d s : ℕ} {t u : Param d s}
    (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i, j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry, hj, j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry, hi, i] using h i i

private def form {d s : ℕ} (t : Param d s) : Vec d →+ Vec d →+ Vec s where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a i * b j * entry t i j k
      map_zero' := by funext k; simp
      map_add' := by
        intro b c
        funext k
        simp [mul_add, add_mul, Finset.sum_add_distrib] }
  map_zero' := by ext b k; simp
  map_add' := by
    intro a b
    ext c k
    simp [add_mul, Finset.sum_add_distrib]

private abbrev FamGrp {d s : ℕ} (t : Param d s) := BiExt (form t)

private def gen {d s : ℕ} (t : Param d s) (i : Fin d) : FamGrp t := ⟨basis i, 0⟩
private def fiberEmb {d s : ℕ} (t : Param d s) (z : Vec s) : FamGrp t := ⟨0, z⟩

private lemma form_basis {d s : ℕ} (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

private lemma gen_sq {d s : ℕ} (t : Param d s) (i : Fin d) :
    gen t i * gen t i = fiberEmb t (entry t i i) := by
  apply BiExt.ext
  · exact BiExt.double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, form_basis]

private lemma gen_comm {d s : ℕ} (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = fiberEmb t (entry t i j) := by
  rw [BiExt.comm_eq]
  apply BiExt.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [form_basis, form_basis, entry_upper h, sub_zero]
    rfl

private lemma fiberEmb_injective {d s : ℕ} (t : Param d s) :
    Function.Injective (fiberEmb t) :=
  fun _ _ h => congrArg BiExt.fiber h

private lemma fiberEmb_add {d s : ℕ} (t : Param d s) (u v : Vec s) :
    fiberEmb t (u + v) = fiberEmb t u * fiberEmb t v := by
  apply BiExt.ext <;> simp [fiberEmb]

private lemma map_fiber_agree {d s : ℕ} {R : Type*} [Group R] {t u : Param d s}
    (e : FamGrp t →* R) (f : FamGrp u →* R)
    (h : ∀ i : Fin s, e (fiberEmb t (basis i)) = f (fiberEmb u (basis i))) (w : Vec s) :
    e (fiberEmb t w) = f (fiberEmb u w) := by
  have hz : e (fiberEmb t 0) = f (fiberEmb u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [fiberEmb_add, fiberEmb_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have hbit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hbit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i

private lemma recover_param {d s : ℕ} (hs : s ≤ d) (t u r : Param d s)
    (e : FamGrp t ≃* FamGrp r) (f : FamGrp u ≃* FamGrp r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsq (i : Fin d) : e (fiberEmb t (entry t i i)) = f (fiberEmb u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BiExt.sq_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (fiberEmb t (basis i)) = f (fiberEmb u (basis i)) := by
    simpa only [entry_fixed i hs] using hsq (Fin.castLE hs i)
  have recover {v w : Vec s} (hv : e (fiberEmb t v) = f (fiberEmb u w)) : v = w := by
    have hsame := map_fiber_agree e.toMonoidHom f.toMonoidHom hfix v
    exact fiberEmb_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsq i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BiExt.comm_eq_of_base_eq (h i) (h j)

private lemma triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

private instance {d s : ℕ} (t : Param d s) : Finite (FamGrp t) :=
  Finite.of_equiv _ (BiExt.toProd (form t)).symm

private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (FamGrp t)

private lemma bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d + s) := by
  change Nat.card (BiExt (form t)) = _
  rw [BiExt.card]
  simp only [Vec, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]

private lemma param_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]

private lemma family_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤ Erdos1160.g (2 ^ (d + s)) * 2 ^ (d * d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : Vec d :=
    (e (gen a i) : FamGrp r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_param hs a b r e f (congrFun h)
  have h := card_le_of_codes bundled bundled_order code sep
  rw [param_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

private lemma bound_of_choice (m d s : ℕ) (hs : s ≤ d) (horder : d + s = m)
    (hexp : 2 * m ^ 3 + (d * d) * 27 ≤ (s * (d * (d - 1) / 2 + d - s)) * 27 + 12 * m ^ 2) :
    2 ^ (2 * m ^ 3) ≤ Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2) := by
  have hcnt := Nat.pow_le_pow_left (family_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at hcnt
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ ((d * d) * 27)) _ (Nat.pow_pos (by decide))
  calc
    2 ^ (2 * m ^ 3) * 2 ^ ((d * d) * 27) = 2 ^ (2 * m ^ 3 + (d * d) * 27) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((s * (d * (d - 1) / 2 + d - s)) * 27 + 12 * m ^ 2) :=
      Nat.pow_le_pow_right (by decide) hexp
    _ = 2 ^ ((s * (d * (d - 1) / 2 + d - s)) * 27) * 2 ^ (12 * m ^ 2) := pow_add _ _ _
    _ ≤ (Erdos1160.g (2 ^ m) ^ 27 * 2 ^ ((d * d) * 27)) * 2 ^ (12 * m ^ 2) :=
      Nat.mul_le_mul_right _ hcnt
    _ = Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2) * 2 ^ ((d * d) * 27) :=
      Nat.mul_right_comm _ _ _

private lemma tri_even (u : ℕ) : (2 * u) * (2 * u - 1) / 2 = u * (2 * u - 1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]

private lemma tri_odd (u : ℕ) : (2 * u + 1) * (2 * u + 1 - 1) / 2 = (2 * u + 1) * u := by
  have h : 2 * u + 1 - 1 = 2 * u := by omega
  rw [h, show (2 * u + 1) * (2 * u) = (2 * u + 1) * u * 2 by ring, Nat.mul_div_cancel _ (by decide)]

private lemma main : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H3 := by
  intro m hm
  let k := m / 3 - 1
  have hcases : m = 3 * (k + 1) ∨ m = 3 * (k + 1) + 1 ∨ m = 3 * (k + 1) + 2 := by
    dsimp [k]
    omega
  have heven : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rcases hcases with h | h | h
  · apply bound_of_choice m (2 * (k + 1)) (k + 1) (by omega) (by omega)
    rw [h, tri_even, heven]
    have hsub : (k + 1) * (2 * k + 1) + 2 * (k + 1) - (k + 1) =
        (k + 1) * (2 * k + 1) + (k + 1) := by omega
    rw [hsub]
    exact le_of_eq (by ring)
  · apply bound_of_choice m (2 * (k + 1)) (k + 2) (by omega) (by omega)
    rw [h, tri_even, heven]
    have hsub : (k + 1) * (2 * k + 1) + 2 * (k + 1) - (k + 2) =
        (k + 1) * (2 * k + 1) + k := by omega
    rw [hsub]
    exact Nat.le.intro (k := 27 * k + 10) (by ring)
  · apply bound_of_choice m (2 * (k + 1) + 1) (k + 2) (by omega) (by omega)
    rw [h, tri_odd]
    have hsub : (2 * (k + 1) + 1) * (k + 1) + (2 * (k + 1) + 1) - (k + 2) =
        (2 * (k + 1) + 1) * (k + 1) + (k + 1) := by omega
    rw [hsub]
    exact Nat.le.intro (k := 18 * k + 23) (by ring)

end OMA.Erdos1160Higman

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H3 := by
  exact OMA.Erdos1160Higman.main
