import OMAReductions.R_OeisA250131_conjecture_1_R1

/-! A finite check by the kernel. For n ≤ 79: if b n = 1, or some earlier non-1 value b k
divides b n, then n is not a sieved index. The remaining indices are 1, 2, 16, 27, 36, 50,
64 and 76, with b n = 2, 3, 5, 7, 11, 13, 17 and 19, all prime. -/

theorem OMA.solution : OMA.R_OeisA250131_conjecture_1_R1.H1 := by
  intro n hn hmem
  obtain ⟨h1, hb1, hall⟩ := hmem
  interval_cases n
  · exact (by decide +kernel : (OeisA250131.b 1).Prime)
  · exact (by decide +kernel : (OeisA250131.b 2).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 3 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 4 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 5 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 6 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 7 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 8 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 9 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 10 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 11 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 12 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 13 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 14 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 15 = 1) hb1
  · exact (by decide +kernel : (OeisA250131.b 16).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 17 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 18 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 19 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 20)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 21 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 22)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 23 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 24)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 25 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 26 = 1) hb1
  · exact (by decide +kernel : (OeisA250131.b 27).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 27 ∣ OeisA250131.b 28)
      (hall 27 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 29 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 30 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 31 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 27 ∣ OeisA250131.b 32)
      (hall 27 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 33 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 27 ∣ OeisA250131.b 34)
      (hall 27 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 35 = 1) hb1
  · exact (by decide +kernel : (OeisA250131.b 36).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 37 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 38 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 39)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 40)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 41 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 42)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 36 ∣ OeisA250131.b 43)
      (hall 36 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 44)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 45 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 46)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 36 ∣ OeisA250131.b 47)
      (hall 36 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 48 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 27 ∣ OeisA250131.b 49)
      (hall 27 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact (by decide +kernel : (OeisA250131.b 50).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 51 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 52 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 50 ∣ OeisA250131.b 53)
      (hall 50 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 50 ∣ OeisA250131.b 54)
      (hall 50 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 55)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 56 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 57)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 58)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 59 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 27 ∣ OeisA250131.b 60)
      (hall 27 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 50 ∣ OeisA250131.b 61)
      (hall 50 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 36 ∣ OeisA250131.b 62)
      (hall 36 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 63)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact (by decide +kernel : (OeisA250131.b 64).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 64 ∣ OeisA250131.b 65)
      (hall 64 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 66 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 67)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 50 ∣ OeisA250131.b 68)
      (hall 50 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 69 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 64 ∣ OeisA250131.b 70)
      (hall 64 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 64 ∣ OeisA250131.b 71)
      (hall 64 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 72 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 73)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 74 = 1) hb1
  · exact absurd (by decide +kernel : OeisA250131.b 64 ∣ OeisA250131.b 75)
      (hall 64 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact (by decide +kernel : (OeisA250131.b 76).Prime)
  · exact absurd (by decide +kernel : OeisA250131.b 16 ∣ OeisA250131.b 77)
      (hall 16 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 64 ∣ OeisA250131.b 78)
      (hall 64 ⟨by norm_num, by norm_num, by decide +kernel⟩)
  · exact absurd (by decide +kernel : OeisA250131.b 79 = 1) hb1
