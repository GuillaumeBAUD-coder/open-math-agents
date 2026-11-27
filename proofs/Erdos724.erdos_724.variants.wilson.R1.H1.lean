import OMAReductions.R_Erdos724_erdos_724_variants_wilson_R1

-- Step Erdos724.erdos_724.variants.wilson.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.wilson.R1

/-!
Over a field `F` with `q` elements, identified with `Fin q`, the squares `L_c x y = c x + y` for
`c ≠ 0` are Latin, distinct, and pairwise orthogonal: `(c x + y, c' x + y)` determines
`(c - c') x`, hence `x` and then `y`. That gives `q - 1` mutually orthogonal squares. For a prime
power `q = p ^ k` take the Galois field.
-/

open Erdos724
open scoped Classical

namespace OMA

/-- The Latin square `(x, y) ↦ c x + y` over a field identified with `Fin n`. -/
def fieldLS {F : Type} [Field F] {n : ℕ} (e : F ≃ Fin n) (c : F) (hc : c ≠ 0) : LatinSquare n where
  mat := fun x y => e (c * e.symm x + e.symm y)
  row_injective := by
    intro x y y' h
    have h0 : e (c * e.symm x + e.symm y) = e (c * e.symm x + e.symm y') := h
    exact e.symm.injective (add_left_cancel (e.injective h0))
  col_injective := by
    intro y x x' h
    have h0 : e (c * e.symm x + e.symm y) = e (c * e.symm x' + e.symm y) := h
    exact e.symm.injective (mul_left_cancel₀ hc (add_right_cancel (e.injective h0)))

theorem fieldLS_mat {F : Type} [Field F] {n : ℕ} (e : F ≃ Fin n) (c : F) (hc : c ≠ 0)
    (x y : Fin n) : (fieldLS e c hc).mat x y = e (c * e.symm x + e.symm y) := rfl

theorem field_orth {F : Type} [Field F] {n : ℕ} (e : F ≃ Fin n) (c c' : F) (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hne : c ≠ c') : IsOrthogonal (fieldLS e c hc) (fieldLS e c' hc') := by
  unfold IsOrthogonal
  intro p q h
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  have hA : (fieldLS e c hc).mat x y = (fieldLS e c hc).mat x' y' := congrArg Prod.fst h
  have hB : (fieldLS e c' hc').mat x y = (fieldLS e c' hc').mat x' y' := congrArg Prod.snd h
  rw [fieldLS_mat, fieldLS_mat] at hA hB
  have hA' := e.injective hA
  have hB' := e.injective hB
  have hsub : (c - c') * (e.symm x - e.symm x') = 0 := by linear_combination hA' - hB'
  have hx0 : e.symm x - e.symm x' = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hx : e.symm x = e.symm x' := sub_eq_zero.mp hx0
  have hy : e.symm y = e.symm y' := by
    rw [hx] at hA'
    exact add_left_cancel hA'
  rw [e.symm.injective hx, e.symm.injective hy]

theorem field_inj {F : Type} [Field F] {n : ℕ} (e : F ≃ Fin n) (c c' : F) (hc : c ≠ 0)
    (hc' : c' ≠ 0) (h : fieldLS e c hc = fieldLS e c' hc') : c = c' := by
  have h1 : (fieldLS e c hc).mat (e 1) (e 0) = (fieldLS e c' hc').mat (e 1) (e 0) := by rw [h]
  rw [fieldLS_mat, fieldLS_mat] at h1
  have h2 := e.injective h1
  simpa using h2

theorem bound (F : Type) [Field F] {n : ℕ} (e : F ≃ Fin n) : n - 1 ≤ maxMOLS n := by
  have : Fintype F := Fintype.ofEquiv (Fin n) e.symm
  have hinj : Function.Injective (fun u : Fˣ => fieldLS e (u : F) u.ne_zero) := by
    intro u u' h
    exact Units.ext (field_inj e _ _ _ _ h)
  show n - 1 ≤ sSup {k : ℕ | ∃ S : Finset (LatinSquare n), S.card = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}
  refine le_csSup ⟨Fintype.card (LatinSquare n), ?_⟩
    ⟨(Finset.univ : Finset Fˣ).image (fun u : Fˣ => fieldLS e (u : F) u.ne_zero), ?_, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact Finset.card_le_univ S
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_units,
      Fintype.card_congr e, Fintype.card_fin]
  · intro X hX Y hY hXY
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hX)
    obtain ⟨u', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hY)
    apply field_orth
    intro h
    exact hXY (by rw [Units.ext h])

end OMA

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H1 := by
  unfold OMA.R_Erdos724_erdos_724_variants_wilson_R1.H1
  intro p k hp hk
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
  obtain ⟨e⟩ : Nonempty (GaloisField p k ≃ Fin (p ^ k)) := ⟨Finite.equivFinOfCardEq hcard⟩
  exact OMA.bound (GaloisField p k) e
