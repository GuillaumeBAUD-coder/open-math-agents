import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @marcusbuffett
-- H1 := OeisA108129.a 254602 = -1

lemma riesel_cover (t : Fin 24) : ∃ p : ℕ, 2 ≤ p ∧ p ≤ 241 ∧
    2 ^ 24 ≡ 1 [MOD p] ∧ 509203 * 2 ^ t.val ≡ 1 [MOD p] := by
  fin_cases t <;> first
    | exact ⟨3, by decide⟩
    | exact ⟨5, by decide⟩
    | exact ⟨7, by decide⟩
    | exact ⟨13, by decide⟩
    | exact ⟨17, by decide⟩
    | exact ⟨241, by decide⟩

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by decide), dif_neg]
  rintro ⟨m, _, hm⟩
  change (509203 * 2 ^ m - 1).Prime at hm
  obtain ⟨p, hp, hsmall, hperiod, hres⟩ := riesel_cover ⟨m % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ m ≡ 2 ^ (m % 24) [MOD p] := by
    calc
      2 ^ m = 2 ^ (m % 24) * (2 ^ 24) ^ (m / 24) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ 2 ^ (m % 24) * 1 ^ (m / 24) [MOD p] :=
        (hperiod.pow _).mul_left _
      _ = _ := by simp
  have hd := ((hpow.mul_left 509203).trans hres).symm.dvd'
  have hbig : 0 < (2 : ℕ) ^ m := by positivity
  rcases hm.eq_one_or_self_of_dvd p hd with h | h <;> omega
