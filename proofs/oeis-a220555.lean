import OMAStatements.S_oeis_a220555

open OMA.S_oeis_a220555

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a220555.main) := by
  intro h
  let A : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2
  let B := matMod 3 A
  have hsq : B ^ 2 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    decide +kernel
  have hne : B ≠ 1 := by
    intro he
    have he' := congrArg (fun M : Matrix (Fin 1) (Fin 1) (ZMod 3) => M 0 0) he
    exact (by decide : (2 : ZMod 3) ≠ 1) he'
  have hpos : 0 < orderOf B :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hsq) (by decide)
  have hle : orderOf B ≤ 2 := orderOf_le_of_pow_eq_one (by decide) hsq
  have hnot : orderOf B ≠ 1 := fun he => hne (orderOf_eq_one_iff.mp he)
  have ho : orderOf B = 2 := by omega
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := h 1 3 (by decide) (by decide) A hpos
  have hr : r = 1 := by omega
  have hmax : a220555 1 3 = 1 := by
    have hu : (Finset.univ : Finset (Fin 1)) = {0} := by decide
    have hi : matMod 3 (danzerMatrix 1 0) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      decide +kernel
    unfold a220555
    rw [hu, Finset.sup_singleton]
    change orderOf (matMod 3 (danzerMatrix 1 0)) = 1
    rw [hi, orderOf_one]
  change orderOf B ≤ a220555 r 3 at hr₃
  rw [ho, hr, hmax] at hr₃
  omega