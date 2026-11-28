import OMAStatements.S_mo_353633
import Mathlib

open Matrix Finset

open OMA.S_mo_353633



theorem OMA.solution : type_of% @OMA.S_mo_353633.main := by
  intro K _ _ n k x hRank
  classical
  let S := (Finset.univ : Finset (Fin n)).image x
  let D := {u : K // u ∈ S}
  let d := Fintype.card D
  have hCard : d = S.card := Fintype.card_coe S
  have hd : d ≤ n := by
    rw [hCard]
    exact Finset.card_image_le.trans (by simp)
  let label : Fin n → D := fun i => ⟨x i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let L : Matrix (Fin n) D K := fun i j => if j = label i then 1 else 0
  let R : Matrix D (Fin n) K := fun i j => i.val ^ j.val
  have hFactor : Matrix.vandermonde x = L * R := by
    ext i j
    rw [Matrix.mul_apply,Finset.sum_eq_single (label i)]
    · simp [Matrix.vandermonde_apply,L,R,label]
    · intro u _ hu
      simp [L,hu]
    · simp
  have hUpper : (Matrix.vandermonde x).rank ≤ d := by
    rw [hFactor]
    exact (Matrix.rank_mul_le L R).trans ((min_le_left _ _).trans (Matrix.rank_le_card_width L))
  let pick (u : D) : Fin n := Classical.choose (Finset.mem_image.mp u.property)
  have hPick (u : D) : x (pick u) = u.val := (Classical.choose_spec (Finset.mem_image.mp u.property)).2
  let e := (Fintype.equivFin D).symm
  let y : Fin d → K := fun i => (e i).val
  have hInj : Function.Injective y := fun _ _ he => e.injective (Subtype.ext he)
  have hSub : (Matrix.vandermonde x).submatrix (pick ∘ e) (Fin.castLE hd) = Matrix.vandermonde y := by
    ext i j
    simp [Matrix.vandermonde_apply,Matrix.submatrix_apply,Function.comp_def,hPick,y]
  have hDet := Matrix.det_vandermonde_ne_zero_iff.mpr hInj
  have hFull : d ≤ (Matrix.vandermonde y).rank := by
    let V := Matrix.vandermonde y
    have he : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.mpr hDet)
    have hBound := (Matrix.rank_mul_le V V⁻¹).trans (min_le_left _ _)
    rw [he,Matrix.rank_one,Fintype.card_fin] at hBound
    exact hBound
  have hLow := Matrix.rank_submatrix_le (Matrix.vandermonde x) (pick ∘ e) (Fin.castLE hd)
  rw [hSub] at hLow
  have he := le_antisymm hUpper (hFull.trans hLow)
  change S.card = k
  rw [←hCard,←he,hRank]
