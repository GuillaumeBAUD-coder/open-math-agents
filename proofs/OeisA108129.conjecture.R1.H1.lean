import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @sanjog-p
-- H1 := OeisA108129.a 254602 = -1
-- Proof: covering set {3, 5, 7, 13, 17, 241}; every prime in it divides 2^24 - 1.

theorem OMA.riesel_step (p r m : ℕ) (hp : 2 ^ 24 ≡ 1 [MOD p]) (hr : m % 24 = r)
    (h : 509203 * 2 ^ r ≡ 1 [MOD p]) : 509203 * 2 ^ m ≡ 1 [MOD p] := by
  have e : 2 ^ m = (2 ^ 24) ^ (m / 24) * 2 ^ (m % 24) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  subst hr
  rw [e]
  calc 509203 * ((2 ^ 24) ^ (m / 24) * 2 ^ (m % 24))
      ≡ 509203 * (1 ^ (m / 24) * 2 ^ (m % 24)) [MOD p] :=
        ((hp.pow _).mul_right _).mul_left _
    _ = 509203 * 2 ^ (m % 24) := by simp
    _ ≡ 1 [MOD p] := h

theorem OMA.riesel_cover (m : ℕ) :
    ∃ p, 1 < p ∧ p ≤ 241 ∧ 509203 * 2 ^ m ≡ 1 [MOD p] := by
  have hr : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have key : ∀ r, r < 24 → m % 24 = r →
      ∃ p, 1 < p ∧ p ≤ 241 ∧ 509203 * 2 ^ m ≡ 1 [MOD p] := by
    intro r hr24 hmr
    interval_cases r
    all_goals first
      | exact ⟨3, by norm_num, by norm_num, OMA.riesel_step 3 _ m (by decide) hmr (by decide)⟩
      | exact ⟨5, by norm_num, by norm_num, OMA.riesel_step 5 _ m (by decide) hmr (by decide)⟩
      | exact ⟨7, by norm_num, by norm_num, OMA.riesel_step 7 _ m (by decide) hmr (by decide)⟩
      | exact ⟨13, by norm_num, by norm_num, OMA.riesel_step 13 _ m (by decide) hmr (by decide)⟩
      | exact ⟨17, by norm_num, by norm_num, OMA.riesel_step 17 _ m (by decide) hmr (by decide)⟩
      | exact ⟨241, by norm_num, by norm_num, OMA.riesel_step 241 _ m (by decide) hmr (by decide)⟩
  exact key _ hr rfl

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm0, hprime⟩
  have h2 : (2 * 254602 - 1 : ℕ) = 509203 := by norm_num
  rw [h2] at hprime
  obtain ⟨p, hp1, hp241, hmod⟩ := OMA.riesel_cover m
  have hpos : 1 ≤ 509203 * 2 ^ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  have hbig : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm0)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega
