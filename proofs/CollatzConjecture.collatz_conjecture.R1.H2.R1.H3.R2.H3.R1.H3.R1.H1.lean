import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1_H3_R1

-- Proof of CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2.H3.R1.H3.R1.H1
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


private lemma affine_even {a b q : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    collatzStep (a * q + b) = (a / 2) * q + b / 2 := by
  have hev : (a * q + b) % 2 = 0 := by
    have ha' : a = 2 * (a / 2) := by omega
    rw [ha', show 2 * (a / 2) * q + b = 2 * ((a / 2) * q) + b by ring]
    omega
  rw [← cstep_eq, cstep]
  have hbeq : Nat.beq ((a * q + b) % 2) 0 = true := Nat.beq_eq.mpr hev
  rw [hbeq]
  simp only [↓reduceIte]
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have hmul : a * q + b = 2 * ((a / 2) * q + b / 2) := by
    conv_lhs => rw [ha', hb']
    ring
  rw [hmul, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

private lemma affine_odd {a b q : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    collatzStep (a * q + b) = (3 * a) * q + (3 * b + 1) := by
  have hodd : (a * q + b) % 2 ≠ 0 := by
    have ha' : a = 2 * (a / 2) := by omega
    rw [ha', show 2 * (a / 2) * q + b = 2 * ((a / 2) * q) + b by ring]
    omega
  rw [← cstep_eq, cstep]
  have hbeq : Nat.beq ((a * q + b) % 2) 0 = false := by
    cases hc : Nat.beq ((a * q + b) % 2) 0
    · rfl
    · exact absurd (Nat.beq_eq.mp hc) hodd
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

private def checkAffine (r : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, a, b => Nat.blt a 8192 && Nat.blt b r
  | fuel + 1, a, b =>
    if Nat.blt a 8192 && Nat.blt b r then true
    else if Nat.beq (a % 2) 0 then
      if Nat.beq (b % 2) 0 then checkAffine r fuel (a / 2) (b / 2)
      else checkAffine r fuel (3 * a) (3 * b + 1)
    else false

private lemma checkAffine_sound (r q : ℕ) : ∀ fuel a b s : ℕ,
    collatzStep^[s] (8192 * q + r) = a * q + b →
    checkAffine r fuel a b = true →
    ∃ t : ℕ, collatzStep^[t] (8192 * q + r) < 8192 * q + r
  | 0, a, b, s, hval, h => by
    simp only [checkAffine, Bool.and_eq_true, Nat.blt_eq] at h
    refine ⟨s, ?_⟩
    rw [hval]
    nlinarith
  | fuel + 1, a, b, s, hval, h => by
    simp only [checkAffine] at h
    cases hok : (Nat.blt a 8192 && Nat.blt b r)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
      cases ha : Nat.beq (a % 2) 0
      · simp [ha] at h
      · simp only [ha, ↓reduceIte] at h
        have ha0 : a % 2 = 0 := Nat.beq_eq.mp ha
        cases hb : Nat.beq (b % 2) 0
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          have hb1 : b % 2 = 1 := by
            have hne : b % 2 ≠ 0 := by intro he; rw [he] at hb; simp at hb
            omega
          have hnext : collatzStep^[s + 1] (8192 * q + r) = (3 * a) * q + (3 * b + 1) := by
            rw [Function.iterate_succ_apply', hval, affine_odd ha0 hb1]
          exact checkAffine_sound r q fuel (3 * a) (3 * b + 1) (s + 1) hnext h
        · simp only [hb, ↓reduceIte] at h
          have hb0 : b % 2 = 0 := Nat.beq_eq.mp hb
          have hnext : collatzStep^[s + 1] (8192 * q + r) = (a / 2) * q + b / 2 := by
            rw [Function.iterate_succ_apply', hval, affine_even ha0 hb0]
          exact checkAffine_sound r q fuel (a / 2) (b / 2) (s + 1) hnext h
    · simp only [Bool.and_eq_true, Nat.blt_eq] at hok
      refine ⟨s, ?_⟩
      rw [hval]
      nlinarith

private lemma checkAll_ok :
    ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ).all (fun r => checkAffine r 21 8192 r) = true := by
  decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1_H3_R1.H1 := by
  intro n _ h8192
  have hok := List.all_eq_true.mp checkAll_ok (n % 8192) h8192
  obtain ⟨s, hlt⟩ := checkAffine_sound (n % 8192) (n / 8192) 21 8192 (n % 8192) 0 (by simp) hok
  have hdiv : 8192 * (n / 8192) + n % 8192 = n := Nat.div_add_mod n 8192
  rw [hdiv] at hlt
  exact ⟨s, hlt⟩
