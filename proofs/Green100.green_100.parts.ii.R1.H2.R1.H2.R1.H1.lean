import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1
import Mathlib

/-! A two-bit permutation construction for the marked double. -/
-- Problem: Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H1
-- Credit: @sobrien032

namespace LambdaLamp

abbrev Bit := ZMod 2
abbrev Config (X : Type*) := X → Bit
noncomputable section
variable {X Q : Type*} [Group Q] [MulAction Q X]

def translate (v : Config X) : Equiv.Perm (Config X) := Equiv.addLeft v

theorem translate_mul (v q : Config X) : translate v * translate q = translate (v + q) := by
  ext p i
  change v i + (q i + p i) = (v i + q i) + p i
  abel

theorem translate_inv (v : Config X) : (translate v)⁻¹ = translate v := by
  ext p i
  change -v i + p i = v i + p i
  rw [ZModModule.neg_eq_self]

def shift : Q →* Equiv.Perm (Config X) where
  toFun g := {
    toFun := fun p i => p (g⁻¹ • i)
    invFun := fun p i => p (g • i)
    left_inv := by intro p; ext i; simp
    right_inv := by intro p; ext i; simp }
  map_one' := by ext p i; change p ((1 : Q)⁻¹ • i) = p i; simp
  map_mul' g h := by ext p i; change p ((g * h)⁻¹ • i) = p (h⁻¹ • (g⁻¹ • i)); simp [mul_smul]

def delta (x : X) : Config X := by classical exact fun i => if i = x then 1 else 0

theorem shift_delta (g : Q) (x : X) :
    shift g * translate (delta x) * (shift g)⁻¹ = translate (delta (g • x)) := by
  classical
  ext p i
  change delta x (g⁻¹ • i) + p (g • g⁻¹ • i) = delta (g • x) i + p i
  simp [delta, inv_smul_eq_iff]

def copy (x : X) (b : Bool) : Q →* Equiv.Perm (Config X) :=
  if b then (MulAut.conj (translate (delta x))).toMonoidHom.comp shift else shift

theorem copy_true (x : X) (g : Q) : copy x true g =
    translate (delta x) * shift g * (translate (delta x))⁻¹ := rfl
theorem copy_false (x : X) (g : Q) : copy x false g = shift g := rfl

theorem copy_fixes (x : X) (g : Q) (hg : g • x = x) : copy x true g = copy x false g := by
  have hh := shift_delta g x
  rw [hg] at hh
  rw [copy_false, copy_true, mul_inv_eq_iff_eq_mul]
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The commutator acts as the sum of two point lamps at t·x and h·t·x. -/
theorem commutator {x : X} (h t : Q) (hx : h • x = x) :
    let a := copy x true t * (copy x false t)⁻¹
    shift h * a * (shift h)⁻¹ * a⁻¹ =
      translate (delta (h • t • x) + delta (t • x)) := by
  dsimp only
  have ha : copy x true t * (copy x false t)⁻¹ =
      translate (delta x) * translate (delta (t • x)) := by
    rw [copy_true, copy_false, translate_inv, ← shift_delta t x]
    group
  rw [ha, mul_inv_rev, translate_inv, translate_inv]
  have hc : shift h * (translate (delta x) * translate (delta (t • x))) * (shift h)⁻¹ =
      translate (delta x) * translate (delta (h • t • x)) := by
    have split (a b : Equiv.Perm (Config X)) : shift h * (a * b) * (shift h)⁻¹ =
        (shift h * a * (shift h)⁻¹) * (shift h * b * (shift h)⁻¹) := by group
    rw [split, shift_delta, shift_delta, hx]
  rw [hc]
  simp only [translate_mul]
  congr 1
  ext i
  simp only [Pi.add_apply]
  calc
    _ = (delta (h • t • x) i + delta (t • x) i) + (delta x i + delta x i) := by abel
    _ = _ := by rw [ZModModule.add_self, add_zero]

def onFirst : Equiv.Perm (Config X) →* Equiv.Perm (Config X × Bit) where
  toFun f := f.prodCongr (Equiv.refl Bit)
  map_one' := rfl
  map_mul' _ _ := rfl

def toggle (readBit : Config X → Bit) : Equiv.Perm (Config X × Bit) where
  toFun z := (z.1, z.2 + readBit z.1)
  invFun z := (z.1, z.2 + readBit z.1)
  left_inv z := by simp [add_assoc, ZModModule.add_self]
  right_inv z := by simp [add_assoc, ZModModule.add_self]

end
end LambdaLamp


open scoped commutatorElement
namespace LambdaLamp
noncomputable section

/-- A strict move of one point produces a nontrivial central involution in the marked double. -/
theorem marked_double_model
    (Q : Type) [Group Q] (X : Type) [MulAction Q X] (x : X) (h t : Q)
    (hh : h • x = x) (ht : h • (t • x) ≠ t • x) :
    ∃ (G : Type) (_ : Group G) (a b : Q →* G) (j z : G),
      (∀ q : Q, q • x = x → a q = b q) ∧
      j ≠ 1 ∧ j ^ 2 = 1 ∧ (∀ q : Q, Commute j (a q) ∧ Commute j (b q)) ∧ Commute j z ∧
      (let w := ⁅a h, b t * (a t)⁻¹⁆; z*w*z⁻¹ = w*j) := by
  let a := onFirst.comp (copy x false (Q := Q))
  let b := onFirst.comp (copy x true (Q := Q))
  let j : Equiv.Perm (Config X × Bit) := toggle fun _ => 1
  let z : Equiv.Perm (Config X × Bit) := toggle fun c => c (t • x)
  refine ⟨Equiv.Perm (Config X × Bit), inferInstance, a, b, j, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact congrArg onFirst (copy_fixes x q hq).symm
  · intro hj
    have hv := congrArg (fun g : Equiv.Perm (Config X × Bit) => (g (0,0)).2) hj
    change (0 : Bit) + 1 = 0 at hv
    norm_num at hv
  · rw [pow_two]
    apply Equiv.ext
    intro p
    change (p.1, p.2 + 1 + 1) = p
    simp [add_assoc, ZModModule.add_self]
  · intro q
    exact ⟨rfl, rfl⟩
  · apply Equiv.ext
    intro p
    change (p.1, p.2 + p.1 (t • x) + 1) = (p.1, p.2 + 1 + p.1 (t • x))
    congr 1
    abel
  · let v : Config X := delta (h • t • x) + delta (t • x)
    have hv : v (t • x) = 1 := by classical simp [v, delta, Ne.symm ht]
    have hw : ⁅a h, b t * (a t)⁻¹⁆ = onFirst (translate v) := by
      have hc := congrArg onFirst (commutator (x := x) h t hh)
      simp only [map_mul, map_inv] at hc
      exact hc
    dsimp only
    rw [hw]
    apply Equiv.ext
    intro p
    change (v+p.1, p.2 + p.1 (t • x) + (v (t • x) + p.1 (t • x))) = (v+p.1, p.2+1)
    rw [hv]
    congr 1
    calc
      _ = (p.2+1)+(p.1 (t • x) + p.1 (t • x)) := by abel
      _ = _ := by rw [ZModModule.add_self, add_zero]
end
end LambdaLamp

theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1.H1 := LambdaLamp.marked_double_model
