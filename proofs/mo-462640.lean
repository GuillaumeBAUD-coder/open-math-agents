import OMAStatements.S_mo_462640
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
The commutative tensor product over the common equalizer ring is a strong
amalgam. A balanced biadditive multiplication map from the tensor product
back to the original ambient ring detects both injectivity and intersection.
Only additivity of this detecting map is needed; the ambient ring remains
arbitrary and its two embedded commutative subrings may fail to commute.
-/

universe u v w

open scoped TensorProduct


namespace MO462640Proof

variable {C A B X : Type u} [CommRing C] [CommRing A] [CommRing B] [Ring X]
variable [Algebra C A] [Algebra C B]

def multiply (f : A →+* X) (g : B →+* X) : A →+ B →+ X where
  toFun a :=
    { toFun := fun b => f a * g b
      map_zero' := by simp
      map_add' := by intro b b'; simp [mul_add] }
  map_zero' := by ext b; simp
  map_add' a a' := by ext b; simp [add_mul]

def detector (f : A →+* X) (g : B →+* X)
    (h : ∀ c : C, f (algebraMap C A c) = g (algebraMap C B c)) :
    A ⊗[C] B →+ X :=
  TensorProduct.liftAddHom (multiply f g) (by
    intro c a b
    simp only [multiply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.smul_def]
    rw [mul_comm (algebraMap C A c) a, map_mul, map_mul, mul_assoc, h c])

lemma detector_tmul (f : A →+* X) (g : B →+* X)
    (h : ∀ c : C, f (algebraMap C A c) = g (algebraMap C B c)) (a : A) (b : B) :
    detector f g h (a ⊗ₜ[C] b) = f a * g b := rfl

lemma amalgamate_over_base (f : A →+* X) (g : B →+* X)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcompat : ∀ c : C, f (algebraMap C A c) = g (algebraMap C B c))
    (hinter : ∀ a : A, ∀ b : B, f a = g b →
      ∃ c : C, algebraMap C A c = a ∧ algebraMap C B c = b) :
    ∃ (Y : Type u) (_ : CommRing Y) (i : A →+* Y) (j : B →+* Y),
      Function.Injective i ∧ Function.Injective j ∧
        ∀ a : A, ∀ b : B, i a = j b ↔ f a = g b := by
  let i : A →+* A ⊗[C] B := Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A ⊗[C] B := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨A ⊗[C] B, inferInstance, i, j, ?_, ?_, ?_⟩
  · intro a a' haa
    apply hf
    have he := congrArg (detector f g hcompat) haa
    simpa [i, detector_tmul] using he
  · intro b b' hbb
    apply hg
    have he := congrArg (detector f g hcompat) hbb
    simpa [j, detector_tmul] using he
  · intro a b
    constructor
    · intro hab
      have he := congrArg (detector f g hcompat) hab
      simpa [i, j, detector_tmul] using he
    · intro hab
      obtain ⟨c, rfl, rfl⟩ := hinter a b hab
      exact congrArg (fun k : C →+* A ⊗[C] B => k c)
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := C) (A := A) (B := B))

end MO462640Proof

namespace AmalgamIntersection

variable {A : Type u} {B : Type v} {X : Type w}
variable [CommRing A] [CommRing B] [Ring X]

/-- The common elements of two rings embedded in one ambient ring. -/
def core (f : A →+* X) (g : B →+* X) : Subring (A × B) :=
  (f.comp (RingHom.fst A B)).eqLocus (g.comp (RingHom.snd A B))

def left (f : A →+* X) (g : B →+* X) : core f g →+* A :=
  (RingHom.fst A B).comp (core f g).subtype

def right (f : A →+* X) (g : B →+* X) : core f g →+* B :=
  (RingHom.snd A B).comp (core f g).subtype

theorem agree (f : A →+* X) (g : B →+* X) (c : core f g) :
    f (left f g c) = g (right f g c) := c.property

def pair (f : A →+* X) (g : B →+* X) (a : A) (b : B) (h : f a = g b) :
    core f g := ⟨(a, b), h⟩

@[simp] theorem left_pair (f : A →+* X) (g : B →+* X)
    (a : A) (b : B) (h : f a = g b) : left f g (pair f g a b h) = a := rfl

@[simp] theorem right_pair (f : A →+* X) (g : B →+* X)
    (a : A) (b : B) (h : f a = g b) : right f g (pair f g a b h) = b := rfl

theorem exists_core_iff (f : A →+* X) (g : B →+* X) (a : A) (b : B) :
    (∃ c : core f g, left f g c = a ∧ right f g c = b) ↔ f a = g b := by
  constructor
  · rintro ⟨c, rfl, rfl⟩
    exact agree f g c
  · intro h
    exact ⟨pair f g a b h, rfl, rfl⟩

end AmalgamIntersection

open AmalgamIntersection in
theorem OMA.solution : type_of% @OMA.S_mo_462640.main := by
  intro A B X _ _ _ f g hf hg
  let : Algebra (core f g) A := (left f g).toAlgebra
  let : Algebra (core f g) B := (right f g).toAlgebra
  apply MO462640Proof.amalgamate_over_base (C := core f g) f g hf hg
  · intro c
    exact agree f g c
  · intro a b h
    exact (exists_core_iff f g a b).mpr h
