import OMAStatements.S_mo_479120

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_479120.main) := by
  intro hmain
  have h := hmain 1 2 1 (by decide) (by decide) (by decide)
  have h1 : 3 * (1 + 1 + 1) ≤ 2 * OMA.S_mo_479120.a 1 2 1 := h.1
  have hval : OMA.S_mo_479120.a 1 2 1 = 4 := by
    simp [OMA.S_mo_479120.a, Nat.gcd_self]
  rw [hval] at h1
  exact absurd h1 (by decide)
