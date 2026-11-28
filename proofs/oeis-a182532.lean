import OMAStatements.S_oeis_a182532

-- Problem: OEIS A182532, Carmichael numbers divisible by 7 and 17.
-- Conjectures (1)-(4) of the entry: such a number C with last digit 1, 5, 3, 9 is
-- 7*17*(120n+119), 7*17*(120n+95), 7*17*(120n+47), 7*17*(120n+71) respectively.
-- Proof. Korselt's necessary condition for the primes 7 and 17: pick b = 3 mod 119 and b = 1 mod the
-- part of C prime to 119 (Chinese remainder theorem), so b is prime to C and b^(C-1) = 1 mod C.
-- Since 3 has order 6 mod 7 and order 16 mod 17, we get C = 1 mod 6 and C = 1 mod 16.
-- Together with 119 | C and the last digit this fixes C modulo 119*120.

open OMA.S_oeis_a182532

lemma OMA.pow3_mod7 (e : ℕ) (h : 3 ^ e % 7 = 1) : e % 6 = 0 := by
  have hr : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have he : 3 ^ e % 7 = 3 ^ (e % 6) % 7 := by
    conv_lhs => rw [← Nat.div_add_mod e 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [he] at h
  have hsmall : ∀ r < 6, 3 ^ r % 7 = 1 → r = 0 := by decide
  exact hsmall _ hr h

lemma OMA.pow3_mod17 (e : ℕ) (h : 3 ^ e % 17 = 1) : e % 16 = 0 := by
  have hr : e % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have he : 3 ^ e % 17 = 3 ^ (e % 16) % 17 := by
    conv_lhs => rw [← Nat.div_add_mod e 16, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [he] at h
  have hsmall : ∀ r < 16, 3 ^ r % 17 = 1 → r = 0 := by decide
  exact hsmall _ hr h

/-- Korselt's condition at the primes 7 and 17. -/
lemma OMA.carm_mod (C : ℕ) (hC : IsCarmichael C) (h7 : 7 ∣ C) (h17 : 17 ∣ C) :
    C % 6 = 1 ∧ C % 16 = 1 := by
  obtain ⟨hC1, -, hb⟩ := hC
  have hC0 : C ≠ 0 := by omega
  obtain ⟨u, M1, h7M1, hCu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hC0 7 (by norm_num)
  have hM10 : M1 ≠ 0 := by
    rintro rfl
    simp at hCu
    exact hC0 hCu
  obtain ⟨v, M, h17M, hM1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM10 17 (by norm_num)
  have h7M : ¬ 7 ∣ M := fun h => h7M1 (hM1 ▸ Dvd.dvd.mul_left h _)
  have c7 : Nat.Coprime 7 M := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7M
  have c17 : Nat.Coprime 17 M := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h17M
  have hcop : Nat.Coprime 119 M := by
    have h := Nat.Coprime.mul_left c7 c17
    simpa using h
  obtain ⟨b, hb119, hbM⟩ := Nat.chineseRemainder hcop 3 1
  have hb7 : b ≡ 3 [MOD 7] := hb119.of_dvd (by norm_num)
  have hb17 : b ≡ 3 [MOD 17] := hb119.of_dvd (by norm_num)
  have g7 : Nat.Coprime b 7 := by
    unfold Nat.Coprime
    rw [hb7.gcd_eq]
    norm_num
  have g17 : Nat.Coprime b 17 := by
    unfold Nat.Coprime
    rw [hb17.gcd_eq]
    norm_num
  have gM : Nat.Coprime b M := by
    unfold Nat.Coprime
    rw [hbM.gcd_eq]
    simp
  have hbC : Nat.Coprime b C := by
    rw [hCu, hM1]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right u g7)
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right v g17) gM)
  have key := hb b hbC
  have k7 : 3 ^ (C - 1) ≡ 1 [MOD 7] := ((hb7.pow (C - 1)).symm).trans (key.of_dvd h7)
  have k17 : 3 ^ (C - 1) ≡ 1 [MOD 17] := ((hb17.pow (C - 1)).symm).trans (key.of_dvd h17)
  have e6 : (C - 1) % 6 = 0 := OMA.pow3_mod7 (C - 1) k7
  have e16 : (C - 1) % 16 = 0 := OMA.pow3_mod17 (C - 1) k17
  constructor <;> omega

lemma OMA.fin (m r : ℕ) (hm : m % 120 = r) : 119 * m = 7 * 17 * (120 * (m / 120) + r) := by
  omega

lemma OMA.res1 (m : ℕ) (h6 : m % 6 = 5) (h16 : m % 16 = 7) (h : 119 * m % 10 = 1) :
    m % 120 = 119 := by
  have h10 : m % 10 = 9 := by omega
  clear h
  omega

lemma OMA.res5 (m : ℕ) (h6 : m % 6 = 5) (h16 : m % 16 = 7) (h : 119 * m % 10 = 5) :
    m % 120 = 95 := by
  have h10 : m % 10 = 5 := by omega
  clear h
  omega

lemma OMA.res3 (m : ℕ) (h6 : m % 6 = 5) (h16 : m % 16 = 7) (h : 119 * m % 10 = 3) :
    m % 120 = 47 := by
  have h10 : m % 10 = 7 := by omega
  clear h
  omega

lemma OMA.res9 (m : ℕ) (h6 : m % 6 = 5) (h16 : m % 16 = 7) (h : 119 * m % 10 = 9) :
    m % 120 = 71 := by
  have h10 : m % 10 = 1 := by omega
  clear h
  omega

lemma OMA.mod6 (m : ℕ) (h : 119 * m % 6 = 1) : m % 6 = 5 := by omega

lemma OMA.mod16 (m : ℕ) (h : 119 * m % 16 = 1) : m % 16 = 7 := by omega

theorem OMA.solution : type_of% @OMA.S_oeis_a182532.main := by
  intro C hC h7 h17
  obtain ⟨h6, h16⟩ := OMA.carm_mod C hC h7 h17
  obtain ⟨m, rfl⟩ : 119 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 17) h7 h17
  have hm6 : m % 6 = 5 := OMA.mod6 m h6
  have hm16 : m % 16 = 7 := OMA.mod16 m h16
  exact ⟨fun h => ⟨m / 120, OMA.fin m 119 (OMA.res1 m hm6 hm16 h)⟩,
    fun h => ⟨m / 120, OMA.fin m 95 (OMA.res5 m hm6 hm16 h)⟩,
    fun h => ⟨m / 120, OMA.fin m 47 (OMA.res3 m hm6 hm16 h)⟩,
    fun h => ⟨m / 120, OMA.fin m 71 (OMA.res9 m hm6 hm16 h)⟩⟩
