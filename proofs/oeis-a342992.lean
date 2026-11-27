import OMAStatements.S_oeis_a342992

namespace OMA.S_oeis_a342992

private lemma exists_two_pow_dvd_ofDigits (a : ℕ) :
    ∃ l : List ℕ, l.length = a ∧ (∀ d ∈ l, d = 2 ∨ d = 3) ∧ 2 ^ a ∣ Nat.ofDigits 10 l := by
  induction a with
  | zero =>
    exact ⟨[], rfl, fun _ h => by simp at h, one_dvd _⟩
  | succ a ih =>
    rcases ih with ⟨l, hlen, hd, ⟨q, hq⟩⟩
    obtain ⟨t, ht⟩ := (by decide : Odd 5).pow (n := a)
    by_cases hq2 : q % 2 = 0
    · refine ⟨l ++ [2], by simp [hlen], ?_, ?_⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hd x hx
        · exact Or.inl rfl
      · refine ⟨q / 2 + 5 ^ a, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, hq]
        have h10 : (10 : ℕ) ^ a = 2 ^ a * 5 ^ a := by
          rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
        rw [h10]
        have hq' : q = 2 * (q / 2) := by omega
        nth_rw 1 [hq']
        ring
    · refine ⟨l ++ [3], by simp [hlen], ?_, ?_⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hd x hx
        · exact Or.inr rfl
      · refine ⟨q / 2 + 3 * t + 2, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, hq]
        have h10 : (10 : ℕ) ^ a = 2 ^ a * 5 ^ a := by
          rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
        rw [h10, ht]
        have hq' : q = 2 * (q / 2) + 1 := by omega
        nth_rw 1 [hq']
        ring

private lemma repBlock_length (k : ℕ) (blk : List ℕ) :
    (List.replicate k blk).flatten.length = k * blk.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]

private lemma repBlock_mem (k : ℕ) (blk : List ℕ) {d : ℕ}
    (hd : d ∈ (List.replicate k blk).flatten) : d ∈ blk := by
  induction k with
  | zero => simp at hd
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.mem_append] at hd
    rcases hd with h | h
    · exact h
    · exact ih h

private lemma ofDigits_repBlock_zmod {m T : ℕ} (hpow : (10 ^ T : ZMod m) = 1)
    (k : ℕ) (blk : List ℕ) (hblk : blk.length = T) :
    ((Nat.ofDigits (10 : ℕ) (List.replicate k blk).flatten : ℕ) : ZMod m) =
      k * (Nat.ofDigits (10 : ℕ) blk : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, hblk]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    rw [hpow, one_mul, ih]
    ring

theorem main_proof : ∀ n : ℕ, 1 ≤ n → ¬ 5 ∣ n → ∃ k : ℕ, 1 ≤ k ∧ HasOnlyPrimeDigits (k * n) := by
  intro n hn h5
  have hn0 : n ≠ 0 := by omega
  set a : ℕ := n.factorization 2
  set m : ℕ := ordCompl[2] n
  have hm_pos : 1 ≤ m := Nat.ordCompl_pos 2 hn0
  have hm_ne0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm_ne0⟩
  have h2m_dvd : 2 ^ a * m = n := by
    simpa [a, m, Nat.prime_two] using Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2_ndvd_m : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have h5_ndvd_m : ¬ 5 ∣ m := by
    intro h5m
    apply h5
    exact h5m.trans (Nat.ordCompl_dvd n 2)
  have hcop10 : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr h2_ndvd_m).mul_left
      (Nat.prime_five.coprime_iff_not_dvd.mpr h5_ndvd_m)
  have hcop10a : Nat.Coprime (10 ^ a) m := hcop10.pow_left a
  obtain ⟨l₀, hl₀_len, hl₀_dig, hl₀_dvd⟩ := exists_two_pow_dvd_ofDigits a
  set T : ℕ := m.totient
  have hT_pos : 1 ≤ T := Nat.totient_pos.mpr hm_pos
  have hpowT : (10 ^ T : ZMod m) = 1 := by
    have hme : 10 ^ T ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop10
    simpa [← ZMod.natCast_eq_natCast_iff] using hme
  let r : List ℕ := List.replicate (T - 1) 2
  let block2 : List ℕ := 2 :: r
  let block3 : List ℕ := 3 :: r
  have hblock2_len : block2.length = T := by simp [block2, r]; omega
  have hblock3_len : block3.length = T := by simp [block3, r]; omega
  have hblock_val : Nat.ofDigits 10 block3 = Nat.ofDigits 10 block2 + 1 := by
    simp [block2, block3, Nat.ofDigits_cons]
    ring
  let z : ZMod m := - ((Nat.ofDigits (10 : ℕ) l₀ : ℕ) : ZMod m) * ((10 ^ a : ℕ) : ZMod m)⁻¹
  let c : ℕ := z.val
  have hc_lt : c < m := ZMod.val_lt z
  have hc_cast : (c : ZMod m) = z := ZMod.natCast_zmod_val z
  let l₁ : List ℕ := (List.replicate c block3).flatten ++ (List.replicate (m - c) block2).flatten
  let L : List ℕ := l₀ ++ l₁
  have hl₁_ne : l₁ ≠ [] := by
    intro h
    have hlen : l₁.length = 0 := by rw [h]; rfl
    have hlen2 : l₁.length = m * T := by
      simp [l₁, hblock3_len, hblock2_len]
      rw [← Nat.add_mul, Nat.add_sub_of_le hc_lt.le]
    have hmT : 1 ≤ m * T := Nat.mul_pos hm_pos hT_pos
    omega
  have hL_ne : L ≠ [] := by simp [L, hl₁_ne]
  have hL_dig : ∀ d ∈ L, d = 2 ∨ d = 3 := by
    intro d hd
    simp only [L, List.mem_append] at hd
    rcases hd with hd | hd
    · exact hl₀_dig d hd
    · simp only [l₁, List.mem_append] at hd
      rcases hd with hd | hd
      · have hb := repBlock_mem c block3 hd
        simp only [block3, r, List.mem_cons, List.mem_replicate] at hb
        rcases hb with rfl | ⟨_, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      · have hb := repBlock_mem (m - c) block2 hd
        simp only [block2, r, List.mem_cons, List.mem_replicate] at hb
        rcases hb with rfl | ⟨_, rfl⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
  let X : ℕ := Nat.ofDigits 10 L
  have h2a_dvd_X : 2 ^ a ∣ X := by
    dsimp [X, L]
    rw [Nat.ofDigits_append, hl₀_len]
    have h2a_10a : 2 ^ a ∣ 10 ^ a := by
      rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
      exact dvd_mul_right _ _
    exact dvd_add hl₀_dvd (dvd_mul_of_dvd_left h2a_10a _)
  have hm_dvd_X : m ∣ X := by
    rw [← ZMod.natCast_eq_zero_iff]
    dsimp [X, L]
    rw [Nat.ofDigits_append, hl₀_len]
    have hl₁_zmod : ((Nat.ofDigits (10 : ℕ) l₁ : ℕ) : ZMod m) = (c : ZMod m) := by
      dsimp [l₁]
      rw [Nat.ofDigits_append, repBlock_length, hblock3_len]
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      simp only [Nat.cast_ofNat]
      have hpowc : (10 : ZMod m) ^ (c * T) = 1 := by
        rw [pow_mul', hpowT, one_pow]
      rw [hpowc, one_mul, ofDigits_repBlock_zmod hpowT c block3 hblock3_len,
        ofDigits_repBlock_zmod hpowT (m - c) block2 hblock2_len, hblock_val, Nat.cast_add, Nat.cast_one]
      have hmc : ((m - c : ℕ) : ZMod m) = - (c : ZMod m) := by
        rw [Nat.cast_sub hc_lt.le, ZMod.natCast_self, zero_sub]
      rw [hmc]
      ring
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    simp only [Nat.cast_ofNat]
    rw [hl₁_zmod, hc_cast]
    dsimp [z]
    have hinv : ((10 : ZMod m) ^ a) * ((10 ^ a : ℕ) : ZMod m)⁻¹ = 1 := by
      simpa using ZMod.coe_mul_inv_eq_one (10 ^ a) hcop10a
    calc
      ((Nat.ofDigits (10 : ℕ) l₀ : ℕ) : ZMod m) +
          (10 : ZMod m) ^ a * (- ((Nat.ofDigits (10 : ℕ) l₀ : ℕ) : ZMod m) * ((10 ^ a : ℕ) : ZMod m)⁻¹)
          = ((Nat.ofDigits (10 : ℕ) l₀ : ℕ) : ZMod m) -
              ((Nat.ofDigits (10 : ℕ) l₀ : ℕ) : ZMod m) * (((10 : ZMod m) ^ a) * ((10 ^ a : ℕ) : ZMod m)⁻¹) := by ring
      _ = 0 := by rw [hinv, mul_one, sub_self]
  have hn_dvd_X : n ∣ X := by
    rw [← h2m_dvd]
    have hcop2m : Nat.Coprime (2 ^ a) m :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2_ndvd_m).pow_left a
    exact hcop2m.mul_dvd_of_dvd_of_dvd h2a_dvd_X hm_dvd_X
  obtain ⟨k, hk⟩ := hn_dvd_X
  have hX_dig : Nat.digits 10 X = L := by
    apply Nat.digits_ofDigits 10 (by norm_num) L
    · intro d hd
      rcases hL_dig d hd with rfl | rfl <;> norm_num
    · intro hne
      have hmem := List.getLast_mem hne
      rcases hL_dig _ hmem with h2 | h3 <;> omega
  have hX_pos : 1 ≤ X := by
    by_contra h0
    have hX0 : X = 0 := by omega
    rw [hX0, Nat.digits_zero] at hX_dig
    exact hL_ne hX_dig.symm
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    rw [hk_eq, mul_zero] at hk
    omega
  refine ⟨k, hk_pos, ?_⟩
  dsimp [HasOnlyPrimeDigits]
  rw [mul_comm k n, ← hk, hX_dig]
  intro d hd
  rcases hL_dig d hd with rfl | rfl <;> simp

end OMA.S_oeis_a342992

theorem OMA.solution : type_of% @OMA.S_oeis_a342992.main :=
  OMA.S_oeis_a342992.main_proof
