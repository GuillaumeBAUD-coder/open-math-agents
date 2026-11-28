import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Abel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Higman-type Lower Bound for Groups of Order 2^m

Proves `OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2.H3`:
eventually `2 ^ (2 * m ^ 3) ≤ Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (13 * m ^ 2)`.

Adapted directly from the class-two central extension counting proof already formalized in
`proofs/Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H1.lean` (counting bilinear extensions
over `ZMod 2` with fixed diagonal squares, then clearing denominators across the three
residue classes mod 3).
-/


namespace Erdos1160.PresentationCount

open CategoryTheory

theorem card_le_of_relative_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}
  let G (c : S) : FiniteGrp.{0} := c.property.choose
  have rep (c : S) : Nat.card (G c) = n ∧ Quotient.mk _ (G c) = c.val :=
    c.property.choose_spec
  -- A labeled multiplication table determines the isomorphism class.
  let label (c : S) : G c ≃ Fin n := (Finite.equivFin _).trans (finCongr (rep c).1)
  let table (c : S) (x y : Fin n) := label c ((label c).symm x * (label c).symm y)
  have table_inj : Function.Injective table := by
    intro c d h
    let e : G c ≃* G d :=
      { (label c).trans (label d).symm with
        map_mul' := fun x y => by
          change (label d).symm (label c (x * y)) =
            (label d).symm (label c x) * (label d).symm (label c y)
          apply (label d).injective
          simpa [table] using congrFun (congrFun h (label c x)) (label c y) }
    apply Subtype.ext
    rw [← (rep c).2, ← (rep d).2]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩
  let : Finite S := Finite.of_injective table table_inj
  let cls (a : A) : S := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  -- Store the class and the code of a comparison with a representative in the family.
  let representative (c : Set.range cls) : A := c.property.choose
  let mark (c : Set.range cls) (a : A) (h : cls a = c.val) : C :=
    code a (representative c) (((inducedFunctor FiniteGrp.toGrp).mapIso
      (Classical.choice (Quotient.exact (congrArg Subtype.val
        (h.trans c.property.choose_spec.symm))))).groupIsoToMulEquiv)
  let encode (a : A) : S × C := (cls a, mark ⟨cls a, a, rfl⟩ a rfl)
  have injective : Function.Injective encode := by
    intro a b h
    have hc : cls a = cls b := congrArg Prod.fst h
    have hm := congrArg Prod.snd h
    change mark ⟨cls a, a, rfl⟩ a rfl = mark ⟨cls b, b, rfl⟩ b rfl at hm
    have hr : (⟨cls a, a, rfl⟩ : Set.range cls) = ⟨cls b, b, rfl⟩ := Subtype.ext hc
    have hm' : mark ⟨cls a, a, rfl⟩ a rfl = mark ⟨cls a, a, rfl⟩ b hc.symm := by
      have step (c : Set.range cls) (he : (⟨cls a, a, rfl⟩ : Set.range cls) = c)
          (hb : cls b = c.val) : mark ⟨cls a, a, rfl⟩ b hc.symm = mark c b hb := by
        subst c
        rfl
      exact hm.trans (step _ hr rfl).symm
    exact sep _ _ _ _ _ hm'
  change Nat.card A ≤ S.ncard * Nat.card C
  simpa only [Nat.card_prod, Nat.card_coe_set_eq] using
    Nat.card_le_card_of_injective encode injective

end Erdos1160.PresentationCount

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all

instance : Mul (BilinearExtension B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩

instance : One (BilinearExtension B) := ⟨⟨0, 0⟩⟩

instance : Inv (BilinearExtension B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩

@[simp] theorem mul_base (x y : BilinearExtension B) :
    (x * y).base = x.base + y.base := rfl
@[simp] theorem mul_fiber (x y : BilinearExtension B) :
    (x * y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] theorem inv_base (x : BilinearExtension B) : (x⁻¹).base = -x.base := rfl
@[simp] theorem inv_fiber (x : BilinearExtension B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] theorem one_base : (1 : BilinearExtension B).base = 0 := rfl
@[simp] theorem one_fiber : (1 : BilinearExtension B).fiber = 0 := rfl

instance : Group (BilinearExtension B) where
  mul_assoc x y z := by
    apply BilinearExtension.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BilinearExtension.ext <;> simp
  mul_one x := by
    apply BilinearExtension.ext <;> simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext <;> simp

def coordinateEquiv (B : V →+ V →+ W) : BilinearExtension B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card (B : V →+ V →+ W) :
    Nat.card (BilinearExtension B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (coordinateEquiv B), Nat.card_prod]

open scoped commutatorElement

theorem commutator_formula (x y : BilinearExtension B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BilinearExtension.ext <;> simp [map_add, map_neg]
  abel

private theorem double_zero {s : ℕ} (w : Fin s → ZMod 2) : w + w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z + z = 0 := by decide
  exact h (w i)

theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]

theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a, b⁆ = ⁅c, d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]

end BilinearExtension

end Erdos1160Growth

open scoped BigOperators commutatorElement

namespace Erdos1160Growth.SharpFamily

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d - s)
abbrev Param (d s : ℕ) := Slot d s → V s

variable {d s : ℕ}

def basis {k : ℕ} (i : Fin k) : V k := Pi.single i 1

def entry (t : Param d s) (i j : Fin d) : V s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val, h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0

theorem entry_fixed {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]

theorem entry_upper {t : Param d s} {i j : Fin d} (h : i < j) : entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]

theorem entry_injective {t u : Param d s} (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i, j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry, hj, j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry, hi, i] using h i i

def form (t : Param d s) : V d →+ V d →+ V s where
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

abbrev G (t : Param d s) := BilinearExtension (form t)

def gen (t : Param d s) (i : Fin d) : G t := ⟨basis i, 0⟩
def Z (t : Param d s) (z : V s) : G t := ⟨0, z⟩

lemma eval_basis (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

theorem double_zero {k : ℕ} (v : V k) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)

theorem gen_sq (t : Param d s) (i : Fin d) : gen t i * gen t i = Z t (entry t i i) := by
  apply BilinearExtension.ext
  · exact double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, eval_basis]

theorem gen_comm (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = Z t (entry t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [eval_basis, eval_basis, entry_upper h, sub_zero]
    rfl

theorem Z_injective (t : Param d s) : Function.Injective (Z t) :=
  fun _ _ h => congrArg BilinearExtension.fiber h

theorem Z_add (t : Param d s) (u v : V s) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]

/-- Two homomorphisms from different presentations that agree on all coordinate fibers
agree on every element of the common central vector space. -/
theorem map_Z_agree {R : Type*} [Group R] {t u : Param d s}
    (e : G t →* R) (f : G u →* R)
    (h : ∀ i : Fin s, e (Z t (basis i)) = f (Z u (basis i))) (w : V s) :
    e (Z t w) = f (Z u w) := by
  have hz : e (Z t 0) = f (Z u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [Z_add, Z_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have bit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases bit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i

/-- Projecting the images of the d generators into the elementary abelian quotient
gives a complete code for presentations mapping isomorphically into one fixed target. -/
theorem recover_of_equal_base (hs : s ≤ d) (t u r : Param d s)
    (e : G t ≃* G r) (f : G u ≃* G r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsquare (i : Fin d) : e (Z t (entry t i i)) = f (Z u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BilinearExtension.lift_square_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (Z t (basis i)) = f (Z u (basis i)) := by
    simpa only [entry_fixed i hs] using hsquare (Fin.castLE hs i)
  have recover {v w : V s} (hv : e (Z t v) = f (Z u w)) : v = w := by
    have hsame := map_Z_agree e.toMonoidHom f.toMonoidHom hfix v
    exact Z_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsquare i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BilinearExtension.lift_commutator_eq_of_base_eq (h i) (h j)

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

private instance {d s : ℕ} (t : Param d s) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm

private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (G t)

private theorem bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d + s) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]

theorem parameter_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]

/-- Lower bound from the explicit family with s diagonal squares fixed to a
fiber basis. A comparison with a representative needs only d base vectors
of d bits each. -/
theorem sharp_parameter_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤
      Erdos1160.g (2 ^ (d + s)) * 2 ^ (d * d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : V d :=
    (e (gen a i) : G r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_of_equal_base hs a b r e f (congrFun h)
  have h := Erdos1160.PresentationCount.card_le_of_relative_codes bundled bundled_order code sep
  rw [parameter_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

private theorem converted_bound (m d s : ℕ) (hs : s ≤ d) (horder : d + s = m)
    (hexp : 2 * m ^ 3 + (d * d) * 27 ≤ (s * (d * (d - 1) / 2 + d - s)) * 27 + 12 * m ^ 2) :
    2 ^ (2 * m ^ 3) ≤ Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2) := by
  have count := Nat.pow_le_pow_left (sharp_parameter_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at count
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ ((d * d) * 27)) _ (Nat.pow_pos (by decide))
  calc
    2 ^ (2 * m ^ 3) * 2 ^ ((d * d) * 27) = 2 ^ (2 * m ^ 3 + (d * d) * 27) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((s * (d * (d - 1) / 2 + d - s)) * 27 + 12 * m ^ 2) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := pow_add _ _ _
    _ ≤ (Erdos1160.g (2 ^ m) ^ 27 * 2 ^ ((d * d) * 27)) * 2 ^ (12 * m ^ 2) :=
      Nat.mul_le_mul_right _ count
    _ = _ := Nat.mul_right_comm _ _ _

private theorem triangle_even (u : ℕ) :
    (2 * u) * (2 * u - 1) / 2 = u * (2 * u - 1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]

private theorem triangle_odd (u : ℕ) :
    (2 * u + 1) * (2 * u + 1 - 1) / 2 = (2 * u + 1) * u := by
  have h : 2 * u + 1 - 1 = 2 * u := by omega
  rw [h, show (2 * u + 1) * (2 * u) = (2 * u + 1) * u * 2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- The sharp cubic and quadratic terms of Higman's lower bound, with all denominators
cleared and a single estimate valid in each of the three residue classes. -/
theorem higman_lower_all (m : ℕ) (hm : 3 ≤ m) :
    2 ^ (2 * m ^ 3) ≤ Erdos1160.g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2) := by
  let k := m / 3 - 1
  have cases_m : m = 3 * (k + 1) ∨ m = 3 * (k + 1) + 1 ∨ m = 3 * (k + 1) + 2 := by
    dsimp [k]
    omega
  have even_pred : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rcases cases_m with h | h | h
  · apply converted_bound m (2 * (k + 1)) (k + 1) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k + 1) * (2 * k + 1) + 2 * (k + 1) - (k + 1) = (k + 1) * (2 * k + 1) + (k + 1) := by omega
    rw [sub_id]
    exact le_of_eq (by ring)
  · apply converted_bound m (2 * (k + 1)) (k + 2) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k + 1) * (2 * k + 1) + 2 * (k + 1) - (k + 2) = (k + 1) * (2 * k + 1) + k := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 27 * k + 10)
    ring
  · apply converted_bound m (2 * (k + 1) + 1) (k + 2) (by omega) (by omega)
    rw [h, triangle_odd]
    have sub_id : (2 * (k + 1) + 1) * (k + 1) + (2 * (k + 1) + 1) - (k + 2) =
        (2 * (k + 1) + 1) * (k + 1) + (k + 1) := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 18 * k + 23)
    ring

end Erdos1160Growth.SharpFamily

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2.H3 := by
  apply Filter.eventually_atTop.mpr
  refine ⟨3, fun m hm => ?_⟩
  apply (Erdos1160Growth.SharpFamily.higman_lower_all m hm).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
