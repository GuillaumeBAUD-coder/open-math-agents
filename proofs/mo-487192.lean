import OMAStatements.S_mo_487192

/-!
The square-zero obstruction in statement PR 9503 gives a concrete counterexample over ℂ.
-/

namespace OMA.MO487192

-- A central square-zero element vanishes in a semisimple ring.
theorem central_square_zero {R : Type} [Ring R] [IsSemisimpleRing R]
    (x : R) (central : ∀ y : R, y * x = x * y) (hx : x * x = 0) : x = 0 := by
  let I : Submodule R R := Submodule.span R {x}
  have hxI : x ∈ I := Submodule.mem_span_singleton_self x
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  have h1 : (1 : R) ∈ I ⊔ J := by rw [hIJ.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have hxa : x * a = 0 := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    change x * (r * x) = 0
    rw [← mul_assoc, ← central r, mul_assoc, hx, mul_zero]
  have hxb : x = x * b := calc
    x = x * (a + b) := by rw [hab, mul_one]
    _ = x * b := by rw [mul_add, hxa, zero_add]
  exact (Submodule.disjoint_def.mp hIJ.disjoint) x hxI (hxb ▸ J.smul_mem x hb)

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def nilpotent : Mat := !![1, Complex.I; Complex.I, -1]

theorem nilpotent_transpose : nilpotent.transpose = nilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem nilpotent_sq : nilpotent * nilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem nilpotent_ne_zero : nilpotent ≠ 0 := by
  intro h
  have he := congrArg (fun m : Mat => m 0 0) h
  norm_num [nilpotent] at he

end OMA.MO487192

open OMA.MO487192 OMA.S_mo_487192

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487192.main) := by
  intro h
  let A : Mat := 1 + nilpotent
  have hA : IsUnit A := by
    refine ⟨⟨A, 1 - nilpotent, ?_, ?_⟩, rfl⟩
    · calc
        A * (1 - nilpotent) = 1 - nilpotent * nilpotent := by dsimp [A]; noncomm_ring
        _ = 1 := by rw [nilpotent_sq, sub_zero]
    · calc
        (1 - nilpotent) * A = 1 - nilpotent * nilpotent := by dsimp [A]; noncomm_ring
        _ = 1 := by rw [nilpotent_sq, sub_zero]
  have hAt : A.transpose = A := by simp [A, nilpotent_transpose]
  let S := jointCentralizer ℂ A
  have hS : nilpotent ∈ S := by
    change nilpotent ∈ Subalgebra.centralizer ℂ ({A, A.transpose} : Set Mat)
    rw [Subalgebra.mem_centralizer_iff]
    intro B hB
    have hBA : B = A := by simpa [hAt] using hB
    subst B
    simp [A, add_mul, mul_add]
  let x : S := ⟨nilpotent, hS⟩
  have hxSq : x * x = 0 := Subtype.ext nilpotent_sq
  have hxCenter (y : S) : y * x = x * y := by
    apply Subtype.ext
    change (y : Mat) * nilpotent = nilpotent * (y : Mat)
    have hy : (y : Mat) ∈ Subalgebra.centralizer ℂ ({A, A.transpose} : Set Mat) := y.property
    have hyA := (Subalgebra.mem_centralizer_iff ℂ).mp hy A (by simp)
    dsimp only [A] at hyA
    rw [add_mul, mul_add, one_mul, mul_one] at hyA
    exact (add_left_cancel hyA).symm
  letI : IsSemisimpleRing S := h.2.2 ℂ 2 (by decide) A hA
  have hxZero := central_square_zero x hxCenter hxSq
  exact nilpotent_ne_zero (congrArg Subtype.val hxZero)
