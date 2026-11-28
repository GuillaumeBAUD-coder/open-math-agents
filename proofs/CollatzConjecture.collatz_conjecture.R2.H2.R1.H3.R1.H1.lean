import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2_H2_R1_H3_R1

-- Proof of CollatzConjecture.collatz_conjecture.R2.H2.R1.H3.R1.H1
-- Credit: @Twalways

open CollatzConjecture

private def cstep (x : ℕ) : ℕ :=
  if Nat.beq (x % 2) 0 then x / 2 else 3 * x + 1

private lemma cstep_eq (x : ℕ) : cstep x = CollatzConjecture.collatzStep x := by
  unfold cstep CollatzConjecture.collatzStep
  cases h : Nat.beq (x % 2) 0
  · have hne : x % 2 ≠ 0 := by intro he; rw [he] at h; simp at h
    have ho : ¬ Even x := by rw [Nat.even_iff]; omega
    simp [ho]
  · have he : Even x := Nat.even_iff.mpr (Nat.beq_eq.mp h)
    simp [he]


private def checkRatio : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, e, o => Nat.ble e 13 && Nat.blt (3001 ^ o) (2 ^ e * 1000 ^ o)
  | fuel + 1, x, e, o =>
    if Nat.ble e 13 && Nat.blt (3001 ^ o) (2 ^ e * 1000 ^ o) then true
    else if Nat.beq (x % 2) 0 then checkRatio fuel (x / 2) (e + 1) o
    else checkRatio fuel (3 * x + 1) e (o + 1)

private lemma checkRatio_sound (r : ℕ) : ∀ fuel t : ℕ,
    checkRatio fuel (collatzStep^[t] r)
      ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card
      ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card = true →
    ∃ m : ℕ, m ≤ t + fuel ∧
      ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 13 ∧
      3001 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card *
      1000 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card
  | 0, t, h => by
    simp only [checkRatio, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    exact ⟨t, by omega, h⟩
  | fuel + 1, t, h => by
    simp only [checkRatio] at h
    cases hok : (Nat.ble ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card 13 &&
        Nat.blt (3001 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card)
          (2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card *
           1000 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card))
    · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
      cases hev : Nat.beq (collatzStep^[t] r % 2) 0
      · simp only [hev, Bool.false_eq_true, ↓reduceIte] at h
        have hodd : collatzStep^[t] r % 2 = 1 := by
          have hne : collatzStep^[t] r % 2 ≠ 0 := by intro he; rw [he] at hev; simp at hev
          omega
        have hstep : collatzStep^[t + 1] r = 3 * collatzStep^[t] r + 1 := by
          rw [Function.iterate_succ_apply', ← cstep_eq, cstep, hev]; rfl
        have hni1 : t ∉ (Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1) := by simp
        have he_eq : ((Finset.range (t + 1)).filter (fun i => collatzStep^[i] r % 2 = 0)).card =
            ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card := by
          rw [Finset.range_add_one, Finset.filter_insert]; simp [hodd]
        have ho_eq : ((Finset.range (t + 1)).filter (fun i => collatzStep^[i] r % 2 = 1)).card =
            ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert]
          simp [hodd, Finset.card_insert_of_notMem hni1]
        rw [← hstep, ← he_eq, ← ho_eq] at h
        obtain ⟨m, hm, hr1, hr2⟩ := checkRatio_sound r fuel (t + 1) h
        exact ⟨m, by omega, hr1, hr2⟩
      · simp only [hev, ↓reduceIte] at h
        have he0 : collatzStep^[t] r % 2 = 0 := Nat.beq_eq.mp hev
        have hstep : collatzStep^[t + 1] r = collatzStep^[t] r / 2 := by
          rw [Function.iterate_succ_apply', ← cstep_eq, cstep, hev]; rfl
        have hni0 : t ∉ (Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0) := by simp
        have he_eq : ((Finset.range (t + 1)).filter (fun i => collatzStep^[i] r % 2 = 0)).card =
            ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert]
          simp [he0, Finset.card_insert_of_notMem hni0]
        have ho_eq : ((Finset.range (t + 1)).filter (fun i => collatzStep^[i] r % 2 = 1)).card =
            ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card := by
          rw [Finset.range_add_one, Finset.filter_insert]; simp [he0]
        rw [← hstep, ← he_eq, ← ho_eq] at h
        obtain ⟨m, hm, hr1, hr2⟩ := checkRatio_sound r fuel (t + 1) h
        exact ⟨m, by omega, hr1, hr2⟩
    · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
      exact ⟨t, by omega, hok⟩

private lemma checkAll_ok :
    ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ).all (fun r => checkRatio 21 r 0 0) = true := by decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1_H3_R1.H1 := by
  intro r hr
  have hok := List.all_eq_true.mp checkAll_ok r hr
  obtain ⟨m, hm, he, hrat⟩ := checkRatio_sound r 21 0 (by simpa using hok)
  exact ⟨m, by omega, he, hrat⟩
