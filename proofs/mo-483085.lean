import OMAStatements.S_mo_483085

namespace OMA.Aux483085

open OMA.S_mo_483085

lemma three_mul_W (n : ℕ) (hn : Odd n) : 3 * W n = 2 ^ n + 1 := by
  unfold W
  have h : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, rfl⟩ := hn
    have e : (2:ℕ) ^ (2 * k + 1) + 1 = 2 * 4 ^ k + 1 := by
      rw [pow_succ, pow_mul]; ring
    rw [e]
    have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  exact Nat.mul_div_cancel' h

lemma W_odd (n : ℕ) (hn : Odd n) (h1 : 1 ≤ n) : W n % 2 = 1 := by
  have h3 := three_mul_W n hn
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

lemma pow_sq_zero {R : Type*} [CommRing R] (x c : R) (hx : x ^ 2 = 0) (t : ℕ) :
    (1 + c * x) ^ t = 1 + (t : R) * c * x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ih]
    have : (1 + (t : R) * c * x) * (1 + c * x) = 1 + ((t : R) + 1) * c * x + (t : R) * c ^ 2 * x ^ 2 := by
      ring
    rw [this, hx]; push_cast; ring

lemma two_n_dvd_totient (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n) : 2 * n ∣ (W n).totient := by
  have h3 := three_mul_W n hn
  have hpow5 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
  have hm2 : 2 < W n := by omega
  haveI : Fact (2 < W n) := ⟨hm2⟩
  haveI : NeZero (W n) := ⟨by omega⟩
  have hodd := W_odd n hn (by omega)
  have hcop : Nat.Coprime 2 (W n) := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hodd
  have hneg : (2 : ZMod (W n)) ^ n = -1 := by
    have h0 : ((3 * W n : ℕ) : ZMod (W n)) = 0 := by
      push_cast; simp
    rw [h3] at h0
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hphi : (2 : ZMod (W n)) ^ (W n).totient = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient hcop)
    push_cast at this
    exact this
  set o := orderOf (2 : ZMod (W n)) with ho
  have ho_phi : o ∣ (W n).totient := orderOf_dvd_of_pow_eq_one hphi
  have ho_2n : o ∣ 2 * n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul', hneg]; norm_num
  have hne : (-1 : ZMod (W n)) ≠ 1 := ZMod.neg_one_ne_one
  have ho_n : ¬ o ∣ n := by
    intro h
    have := (orderOf_dvd_iff_pow_eq_one).1 h
    rw [hneg] at this
    exact hne this
  -- o is even
  have ho_even : 2 ∣ o := by
    by_contra hc
    have hco : Nat.Coprime o 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; exact hc
    exact ho_n (hco.dvd_of_dvd_mul_left ho_2n)
  obtain ⟨e, he⟩ := ho_even
  have he_n : e ∣ n := by
    rw [he] at ho_2n
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) ho_2n
  obtain ⟨k, hk⟩ := he_n
  have hk_odd : Odd k := by
    rw [hk] at hn
    exact (Nat.odd_mul.1 hn).2
  by_cases hk1 : k = 1
  · have hon : o = 2 * n := by rw [he, hk, hk1, mul_one]
    rw [← hon]
    exact ho_phi
  · exfalso
    have hk3 : 3 ≤ k := by
      obtain ⟨j, rfl⟩ := hk_odd
      omega
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hk; omega
      · exact h
    -- y = 2^e satisfies y^2 = 1, so 2^n = y^k = y
    have hy2 : ((2 : ZMod (W n)) ^ e) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, ← he, ho]; exact pow_orderOf_eq_one _
    have hyk : ((2 : ZMod (W n)) ^ e) ^ k = (2 : ZMod (W n)) ^ e := by
      obtain ⟨j, rfl⟩ := hk_odd
      rw [pow_succ, pow_mul, hy2, one_pow, one_mul]
    have hy : (2 : ZMod (W n)) ^ e = -1 := by
      rw [← hyk, ← pow_mul, ← hk, hneg]
    have hdvd : W n ∣ 2 ^ e + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [hy]; ring
    have hle : W n ≤ 2 ^ e + 1 := Nat.le_of_dvd (by positivity) hdvd
    have h3e : 3 * e ≤ n := by rw [hk]; nlinarith
    have hp : 2 ^ (3 * e) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3e
    have hx : 2 ^ (3 * e) = (2 ^ e) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [hx] at hp
    have hx2 : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
    rcases Nat.eq_or_lt_of_le he1 with h | h
    · subst h; omega
    · have hx4 : 4 ≤ 2 ^ e := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h
      generalize 2 ^ e = y at hle hp hx4
      have h16 : 4 * 4 ≤ y * y := Nat.mul_le_mul hx4 hx4
      have hy16 : 16 * y ≤ y ^ 3 := by
        calc 16 * y ≤ (y * y) * y := Nat.mul_le_mul_right y h16
          _ = y ^ 3 := by ring
      omega

lemma key (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n) :
    ∃ t : ℕ, 6 * t < W n ∧ a (W n) = W n - 6 * t := by
  have h3 := three_mul_W n hn
  have hpow5 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
  set m := W n with hm
  have hm2 : 2 < m := by omega
  obtain ⟨t, ht⟩ := two_n_dvd_totient n hn h5
  rw [← hm] at ht
  have htot : m.totient < m := Nat.totient_lt m (by omega)
  have h6t : 6 * t < m := by
    have : n * (6 * t) < n * m := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨t, h6t, ?_⟩
  -- computation modulo m^2
  have hpos : 1 ≤ 2 ^ m.totient := Nat.one_le_two_pow
  have hmod : (2 ^ m.totient - 1) ≡ (m - 6 * t) * m [MOD m ^ 2] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_sub hpos, Nat.cast_mul, Nat.cast_sub h6t.le]
    set x : ZMod (m ^ 2) := (m : ZMod (m ^ 2)) with hx
    have hx2 : x ^ 2 = 0 := by
      rw [hx, ← Nat.cast_pow]; simp
    have h2n : (2 : ZMod (m ^ 2)) ^ n = 3 * x - 1 := by
      have : ((2 ^ n + 1 : ℕ) : ZMod (m ^ 2)) = ((3 * m : ℕ) : ZMod (m ^ 2)) := by rw [h3]
      push_cast at this
      rw [hx]; linear_combination this
    have h22n : (2 : ZMod (m ^ 2)) ^ (2 * n) = 1 + (-6) * x := by
      rw [pow_mul', h2n]; linear_combination (9 : ZMod (m ^ 2)) * hx2
    have : (2 : ZMod (m ^ 2)) ^ m.totient = 1 + (t : ZMod (m ^ 2)) * (-6) * x := by
      rw [ht, pow_mul, h22n, pow_sq_zero x (-6) hx2 t]
    push_cast
    rw [this]
    linear_combination (-1 : ZMod (m ^ 2)) * hx2
  unfold a
  rw [hmod]
  have htp : 0 < m.totient := Nat.totient_pos.2 (by omega)
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; omega
    · exact h
  have hlt : (m - 6 * t) * m < m ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hm0 : 0 < m := by omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ hm0]

end OMA.Aux483085

theorem OMA.solution : type_of% @OMA.S_mo_483085.main := by
  have h3 : OMA.S_mo_483085.a (OMA.S_mo_483085.W 3) = 1 := by
    have hw : OMA.S_mo_483085.W 3 = 3 := by decide
    rw [hw]
    unfold OMA.S_mo_483085.a
    rw [Nat.totient_prime Nat.prime_three]
    norm_num
  have gen : ∀ n : ℕ, Odd n → 1 < n →
      OMA.S_mo_483085.a (OMA.S_mo_483085.W n) % 2 = 1 := by
    intro n hn h1
    rcases (show n = 3 ∨ 5 ≤ n by obtain ⟨j, rfl⟩ := hn; omega) with h | h
    · subst h; rw [h3]
    · obtain ⟨t, ht, ha⟩ := OMA.Aux483085.key n hn h
      have hodd := OMA.Aux483085.W_odd n hn (by omega)
      rw [ha]; omega
  refine ⟨gen, ?_⟩
  intro n hn h1 h0
  have := gen n hn h1
  rw [h0] at this
  simp at this
