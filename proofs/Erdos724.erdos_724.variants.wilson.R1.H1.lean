import OMAReductions.R_Erdos724_erdos_724_variants_wilson_R1
import Mathlib.FieldTheory.Finite.GaloisField

/-! The nonzero slopes over a finite field give mutually orthogonal affine Latin squares. -/

namespace WilsonField
variable {F : Type} [Field F] {n : ℕ} (e : F ≃ Fin n)

def square (c : Fˣ) : LatinSquare n where
  mat i j := e ((c : F) * e.symm i + e.symm j)
  row_injective i j k h := e.symm.injective (add_left_cancel (e.injective h))
  col_injective j i k h :=
    e.symm.injective (mul_left_cancel₀ c.ne_zero (add_right_cancel (e.injective h)))

lemma slope_injective : Function.Injective (square e) := by
  intro c d h
  have he := congrArg (fun S : LatinSquare n => S.mat (e 1) (e 0)) h
  apply Units.ext
  simpa [square] using he

lemma orth {c d : Fˣ} (hne : c ≠ d) : Erdos724.IsOrthogonal (square e c) (square e d) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have h1 := e.injective (congrArg Prod.fst h)
  have h2 := e.injective (congrArg Prod.snd h)
  change (c:F)*e.symm i + e.symm j = (c:F)*e.symm k + e.symm l at h1
  change (d:F)*e.symm i + e.symm j = (d:F)*e.symm k + e.symm l at h2
  have hz : ((c:F)-d) * (e.symm i-e.symm k) = 0 := by linear_combination h1 - h2
  have hi : e.symm i = e.symm k :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun h => hne (Units.ext h))))
  rw [hi] at h1
  exact Prod.ext (e.symm.injective hi) (e.symm.injective (add_left_cancel h1))

end WilsonField

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H1 := by
  classical
  intro p k hp hk
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  letI : Fintype F := Fintype.ofFinite _
  have hc : Fintype.card F = p^k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p k (by omega)
  let e := Fintype.equivFinOfCardEq hc
  let f : Fˣ ↪ LatinSquare (p^k) := ⟨WilsonField.square e, WilsonField.slope_injective e⟩
  apply le_csSup
  · refine ⟨Fintype.card (LatinSquare (p^k)), ?_⟩
    rintro _ ⟨S, rfl, _⟩
    exact S.card_le_univ
  · refine ⟨Finset.univ.map f, ?_, ?_⟩
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_units, hc]
    · rintro _ hx _ hy hxy
      obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hy
      exact WilsonField.orth e (fun h => hxy (congrArg f h))

