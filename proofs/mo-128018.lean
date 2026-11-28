import OMAStatements.S_mo_128018
open Polynomial OMA.S_mo_128018 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_128018.main) := by
  intro h
  have e : integerImage (C 2 * X) = C 2 * X := by simp [integerImage, C_ofNat]
  have v : complexValue (C 2 * X) (1 / 2) = (1 : ℤ) := by norm_num [complexValue]
  obtain ⟨-, -, d, -, -, hd, -⟩ := h _ _ X X (by
    rw [e]; exact ⟨monic_X, dvd_mul_left _ _, dvd_mul_left _ _,
      fun H h _ => (isUnit_C.2 (by norm_num)).dvd_mul_left.1 h⟩)
    ⟨1, one_pos, by simp [integerImage], fun _ h _ => h⟩ _ ⟨1, v⟩ ⟨1, v⟩
  have : 2 * d = 1 := by
    exact_mod_cast (show ((2 * d : ℤ) : ℂ) = 1 by push_cast; simp [complexValue] at hd; rw [← hd]; norm_num)
  omega
