import OMAReductions.R_Idoneal_idoneal_numbers_completeness_R2

-- For a base m, pick an odd prime q not dividing m with s^2 + m divisible by q. Then for every prime p > q the
-- number a = +-(s*p) mod q (the representative below q/2) has q dividing p^2*m + a^2, which gives the triple
-- (a, q - a, (p^2*m + a^2)/q - a). The finitely many primes p <= q get explicit triples.

lemma idoH2_key (n q a : ℕ) (ha : 0 < a) (h2 : 2 * a < q) (hd : q ∣ n + a ^ 2) (hbig : q ^ 2 < n + a ^ 2) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c := by
  obtain ⟨y, hy⟩ := hd
  have hqy : q < y := by
    by_contra hle
    have hle' : y ≤ q := Nat.le_of_not_lt hle
    have : q * y ≤ q * q := Nat.mul_le_mul_left q hle'
    nlinarith
  obtain ⟨b, rfl⟩ : ∃ b, q = a + b := ⟨q - a, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, y = a + c := ⟨y - a, by omega⟩
  refine ⟨a, b, c, ha, by omega, by omega, ?_⟩
  have h : n + a ^ 2 = a ^ 2 + (a * b + b * c + a * c) := by rw [hy]; ring
  omega

lemma idoH2_big (m q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hs : q ∣ s ^ 2 + m) (hm : ¬ q ∣ m) (hm0 : 0 < m)
    (p : ℕ) (hp : p.Prime) (hqp : q < p) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * m = a * b + b * c + a * c := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqs : ¬ q ∣ s := by
    intro h
    have h1 : q ∣ s ^ 2 := dvd_pow h (by norm_num)
    exact hm ((Nat.dvd_add_right h1).mp hs)
  have hqp' : ¬ q ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h1
    · exact hq.one_lt.ne' h1
    · omega
  have hsp : ¬ q ∣ s * p := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · exact hqs h1
    · exact hqp' h1
  have ht0 : (s * p) % q ≠ 0 := fun h => hsp (Nat.dvd_of_mod_eq_zero h)
  have htq : (s * p) % q < q := Nat.mod_lt _ hq.pos
  have hodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  have hsz : ((s : ZMod q)) ^ 2 + (m : ZMod q) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (s ^ 2 + m) q).mpr hs
    push_cast at this
    exact this
  have htz : (((s * p) % q : ℕ) : ZMod q) = (s : ZMod q) * (p : ZMod q) := by
    rw [ZMod.natCast_mod]; push_cast; ring
  have hbig : ∀ a : ℕ, q ^ 2 < p ^ 2 * m + a ^ 2 := by
    intro a
    have h1 : q ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hqp (by norm_num)
    have h2 : p ^ 2 * 1 ≤ p ^ 2 * m := Nat.mul_le_mul_left _ hm0
    have h3 : 0 ≤ a ^ 2 := Nat.zero_le _
    omega
  rcases Nat.lt_or_ge (2 * ((s * p) % q)) q with h | h
  · refine idoH2_key (p ^ 2 * m) q ((s * p) % q) (Nat.pos_of_ne_zero ht0) h ?_ (hbig _)
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [htz]
    linear_combination ((p : ZMod q)) ^ 2 * hsz
  · refine idoH2_key (p ^ 2 * m) q (q - (s * p) % q) (by omega) (by omega) ?_ (hbig _)
    rw [← ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sub htq.le, htz]
    push_cast
    rw [ZMod.natCast_self]
    linear_combination ((p : ZMod q)) ^ 2 * hsz

lemma idoH2_m1 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 1 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 1 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 1 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact absurd hp (by norm_num)
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot

lemma idoH2_m2 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 2 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 2 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 3 p with h | h
  · exact idoH2_big 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot

lemma idoH2_m3 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 3 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 3 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 3 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 3, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 18, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 36, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m4 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 4 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 4 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 4 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨2, 3, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m5 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 5 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 5 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 3 p with h | h
  · exact idoH2_big 5 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot

lemma idoH2_m6 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 6 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 6 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 6 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 4, 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 5, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m7 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 7 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 7 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 7 11 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 3, 15, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 85, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 211, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m8 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 8 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 8 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 3 p with h | h
  · exact idoH2_big 8 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 2, 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot

lemma idoH2_m9 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 9 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 9 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 9 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 3, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 15, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m10 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 10 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 10 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 10 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 6, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 4, 34, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 11, 36, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m12 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 12 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 12 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 12 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨2, 5, 14, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 6, 42, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 30, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m13 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 13 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 13 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 13 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 5, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 4, 15, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 5, 45, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 10, 57, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m15 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 15 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 15 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 15 17 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 3, 33, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 93, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 183, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 453, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 633, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 3, 1083, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m16 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 16 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 16 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 16 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 4, 28, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 9, 28, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m18 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 18 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 18 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 18 11 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 16, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 10, 40, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 96, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 240, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m21 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 21 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 21 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 21 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 4, 16, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 4, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 6, 45, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m22 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 22 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 22 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 22 13 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 28, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 82, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 29, 84, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 14, 192, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m24 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 24 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 24 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 5 p with h | h
  · exact idoH2_big 24 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 3, 18, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 6, 30, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 4, 84, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m25 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 25 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 25 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 25 13 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 15, 35, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 13, 69, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 177, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 26, 143, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m28 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 28 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 28 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 28 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 10, 22, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 86, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 170, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 422, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m30 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 30 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 30 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 30 11 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 28, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 11, 56, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 9, 132, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 21, 156, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m33 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 33 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 33 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 33 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 6, 18, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 5, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 6, 117, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 19, 67, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m37 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 37 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 37 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 19 p with h | h
  · exact idoH2_big 37 19 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 35, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 14, 45, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 21, 77, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨7, 24, 139, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 117, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 17, 561, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 29, 429, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m40 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 40 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 40 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 40 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 6, 22, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 5, 50, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 6, 142, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 52, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m42 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 42 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 42 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 42 13 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 40, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 15, 60, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 70, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 390, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 30, 228, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m45 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 45 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 45 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 45 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 21, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 6, 57, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 4, 159, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 243, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m48 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 48 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 48 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact idoH2_big 48 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 5, 26, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 4, 60, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 5, 170, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 180, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m57 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 57 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 57 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 57 11 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 27, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 9, 45, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 22, 61, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 10, 253, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 65, 101, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m58 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 58 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 58 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 31 p with h | h
  · exact idoH2_big 58 31 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 56, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 54, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 42, 56, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨7, 30, 184, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 26, 312, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 81, 200, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 35, 564, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 60, 502, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨4, 27, 1570, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 138, 400, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m60 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 60 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 60 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 60 17 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨2, 6, 66, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 78, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 172, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 136, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 1266, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 6, 2166, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m70 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 70 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 70 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 70 17 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 68, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 102, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 46, 72, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 196, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 59, 192, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 65, 300, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m72 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 72 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 72 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 72 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨3, 6, 30, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 10, 58, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 9, 162, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 390, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 6, 966, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m78 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 78 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 78 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 19 p with h | h
  · exact idoH2_big 78 19 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 18, 36, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 74, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 15, 198, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 44, 198, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 17, 692, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨6, 47, 420, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 970, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m85 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 85 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 85 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 85 11 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 10, 30, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 83, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 8, 191, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 9, 377, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 277, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m88 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 88 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 88 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 88 13 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 12, 60, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 30, 70, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 226, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 22, 462, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 106, 138, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m93 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 93 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 93 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 93 17 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 45, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 91, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 15, 135, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 105, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 661, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 541, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 88, 301, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m102 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 102 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 102 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 23 p with h | h
  · exact idoH2_big 102 23 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 100, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 98, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 39, 120, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 20, 534, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 35, 464, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 40, 718, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 22, 1600, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨5, 32, 1454, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m105 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 105 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 105 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 105 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 51, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 10, 85, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 201, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 30, 165, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 69, 177, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m112 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 112 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 112 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 112 11 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 25, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 9, 90, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 7, 252, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 10, 498, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 68, 188, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m120 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 120 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 120 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 11 p with h | h
  · exact idoH2_big 120 11 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 12, 36, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 22, 46, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 14, 174, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 10, 450, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 1116, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m130 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 130 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 130 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 23 p with h | h
  · exact idoH2_big 130 23 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 128, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 19, 138, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 22, 276, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨5, 18, 680, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 126, 172, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨5, 68, 510, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 70, 660, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 135, 500, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m133 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 133 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 133 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 133 13 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 12, 40, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 131, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 9, 253, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 10, 499, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 1237, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 79, 267, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m165 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 165 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 165 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 165 13 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 81, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 163, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 10, 315, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 12, 621, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 66, 297, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 72, 381, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m168 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 168 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 168 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 13 p with h | h
  · exact idoH2_big 168 13 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 11, 50, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 16, 88, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 20, 180, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 27, 282, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 700, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 29, 914, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m177 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 177 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 177 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 31 p with h | h
  · exact idoH2_big 177 31 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 87, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 175, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 41, 101, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨7, 42, 171, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 29, 689, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨6, 61, 441, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨6, 107, 447, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 1485, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨4, 67, 1315, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 262, 565, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 63, 2535, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m190 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 190 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 190 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 29 p with h | h
  · exact idoH2_big 190 29 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 28, 58, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 186, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨7, 42, 184, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 82, 276, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 162, 196, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 1276, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 112, 606, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 27, 3464, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 107, 1464, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m210 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 210 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 210 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 29 p with h | h
  · exact idoH2_big 210 29 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨1, 30, 60, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 58, 88, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 40, 250, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 95, 260, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 37, 862, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 136, 442, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 46, 1612, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 26, 3828, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 231, 756, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m232 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 232 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 232 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 31 p with h | h
  · exact idoH2_big 232 31 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 55, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 230, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 34, 154, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 28, 364, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 66, 418, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨7, 30, 1054, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨4, 79, 804, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 60, 1372, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 30, 3958, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 58, 3306, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 137, 1602, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m240 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 240 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 240 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 240 17 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨3, 14, 54, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 238, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 352, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 618, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 112, 256, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 46, 862, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 138, 498, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m253 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 253 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 253 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 253 17 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 125, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 16, 133, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 13, 369, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨7, 42, 247, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 15, 1799, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 59, 699, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨6, 185, 377, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m273 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 273 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 273 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 273 17 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 135, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 21, 105, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 14, 399, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 20, 579, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 82, 397, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 2713, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 102, 765, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m280 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 280 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 280 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 17 p with h | h
  · exact idoH2_big 280 17 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 18, 58, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 278, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 15, 410, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 45, 290, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 16, 1992, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 78, 598, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 4258, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m312 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 312 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 312 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 19 p with h | h
  · exact idoH2_big 312 19 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 75, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 17, 146, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 268, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨7, 42, 306, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 1986, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 66, 786, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 2436, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 162, 690, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m330 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 330 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 330 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 37 p with h | h
  · exact idoH2_big 330 37 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 328, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 222, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 102, 156, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 72, 546, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 1296, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 282, 336, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 148, 786, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 189, 912, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 191, 1436, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 306, 1032, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 111, 3996, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m345 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 345 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 345 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 19 p with h | h
  · exact idoH2_big 345 19 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 171, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 343, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 18, 453, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 78, 213, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 81, 501, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 14, 3065, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨8, 11, 5243, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 57, 2109, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m357 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 357 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 357 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 19 p with h | h
  · exact idoH2_big 357 19 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 6, 177, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 355, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 353, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 14, 917, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 16, 2271, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 96, 621, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 78, 1305, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 57, 2109, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m385 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 385 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 385 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 23 p with h | h
  · exact idoH2_big 385 23 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 22, 66, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 383, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 27, 307, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 75, 235, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨5, 54, 785, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 29, 2097, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 20, 4835, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 21, 6041, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨4, 349, 573, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m408 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 408 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 408 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 23 p with h | h
  · exact idoH2_big 408 23 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 22, 70, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 406, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 38, 246, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 56, 336, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 106, 450, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 1300, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 60, 1932, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 21, 6402, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨7, 52, 3652, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m462 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 462 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 462 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 43 p with h | h
  · exact idoH2_big 462 43 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact absurd (by simp [Idoneal.knownIdonealNumbers]) hnot
    · exact ⟨3, 6, 460, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 51, 216, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 43, 478, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨4, 69, 762, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 78, 936, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 99, 1320, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 87, 1872, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 254, 948, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 7330, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 71, 6080, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 46, 13456, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 42, 18060, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 540, 1578, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m520 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 520 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 520 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 23 p with h | h
  · exact idoH2_big 520 23 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 127, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 30, 150, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 516, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 82, 306, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨10, 13, 2730, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 125, 690, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 66, 2242, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 69, 2642, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 138, 1978, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m760 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 760 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 760 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 29 p with h | h
  · exact idoH2_big 760 29 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨4, 12, 187, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 27, 234, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 20, 756, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 166, 222, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 81, 1106, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 28, 4428, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 238, 918, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 111, 2426, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 336, 1192, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 330, 1930, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m840 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 840 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 840 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 29 p with h | h
  · exact idoH2_big 840 29 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 27, 114, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 29, 242, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 57, 354, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 39, 1002, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 28, 3276, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨3, 34, 3834, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 30, 7830, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 70, 4270, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 430, 1030, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 19092, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m1320 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 1320 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 1320 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 37 p with h | h
  · exact idoH2_big 1320 37 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨3, 38, 126, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 1318, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 60, 540, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 70, 910, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 71, 2186, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 40, 5440, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 281, 1346, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 112, 4216, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 78, 8838, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 502, 2206, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 72, 17376, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 196, 9172, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m1365 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 1365 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 1365 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 37 p with h | h
  · exact idoH2_big 1365 37 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, 42, 126, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 1363, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 112, 301, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 1261, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 268, 613, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 347, 659, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 34, 10659, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 36, 13317, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 178, 4033, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 100, 11365, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 769, 1693, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 40, 43455, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma idoH2_m1848 (p : ℕ) (hp : p.Prime) (hnot : p ^ 2 * 1848 ∉ Idoneal.knownIdonealNumbers) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * 1848 = a * b + b * c + a * c := by
  rcases Nat.lt_or_ge 43 p with h | h
  · exact idoH2_big 1848 43 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p hp h
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨2, 41, 170, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 6, 1846, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 46, 982, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 82, 1090, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 310, 718, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨5, 542, 566, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 50, 10074, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, 85, 7492, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, 226, 4266, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 51, 29322, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨1, 240, 7368, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨2, 45, 53826, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨1, 52, 58612, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact absurd hp (by norm_num)
    · exact ⟨2, 539, 6314, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem OMA.solution : OMA.R_Idoneal_idoneal_numbers_completeness_R2.H2 := by
  intro m hm p hp hnot
  simp only [Idoneal.knownIdonealNumbers, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idoH2_m1 p hp hnot
  · exact idoH2_m2 p hp hnot
  · exact idoH2_m3 p hp hnot
  · exact idoH2_m4 p hp hnot
  · exact idoH2_m5 p hp hnot
  · exact idoH2_m6 p hp hnot
  · exact idoH2_m7 p hp hnot
  · exact idoH2_m8 p hp hnot
  · exact idoH2_m9 p hp hnot
  · exact idoH2_m10 p hp hnot
  · exact idoH2_m12 p hp hnot
  · exact idoH2_m13 p hp hnot
  · exact idoH2_m15 p hp hnot
  · exact idoH2_m16 p hp hnot
  · exact idoH2_m18 p hp hnot
  · exact idoH2_m21 p hp hnot
  · exact idoH2_m22 p hp hnot
  · exact idoH2_m24 p hp hnot
  · exact idoH2_m25 p hp hnot
  · exact idoH2_m28 p hp hnot
  · exact idoH2_m30 p hp hnot
  · exact idoH2_m33 p hp hnot
  · exact idoH2_m37 p hp hnot
  · exact idoH2_m40 p hp hnot
  · exact idoH2_m42 p hp hnot
  · exact idoH2_m45 p hp hnot
  · exact idoH2_m48 p hp hnot
  · exact idoH2_m57 p hp hnot
  · exact idoH2_m58 p hp hnot
  · exact idoH2_m60 p hp hnot
  · exact idoH2_m70 p hp hnot
  · exact idoH2_m72 p hp hnot
  · exact idoH2_m78 p hp hnot
  · exact idoH2_m85 p hp hnot
  · exact idoH2_m88 p hp hnot
  · exact idoH2_m93 p hp hnot
  · exact idoH2_m102 p hp hnot
  · exact idoH2_m105 p hp hnot
  · exact idoH2_m112 p hp hnot
  · exact idoH2_m120 p hp hnot
  · exact idoH2_m130 p hp hnot
  · exact idoH2_m133 p hp hnot
  · exact idoH2_m165 p hp hnot
  · exact idoH2_m168 p hp hnot
  · exact idoH2_m177 p hp hnot
  · exact idoH2_m190 p hp hnot
  · exact idoH2_m210 p hp hnot
  · exact idoH2_m232 p hp hnot
  · exact idoH2_m240 p hp hnot
  · exact idoH2_m253 p hp hnot
  · exact idoH2_m273 p hp hnot
  · exact idoH2_m280 p hp hnot
  · exact idoH2_m312 p hp hnot
  · exact idoH2_m330 p hp hnot
  · exact idoH2_m345 p hp hnot
  · exact idoH2_m357 p hp hnot
  · exact idoH2_m385 p hp hnot
  · exact idoH2_m408 p hp hnot
  · exact idoH2_m462 p hp hnot
  · exact idoH2_m520 p hp hnot
  · exact idoH2_m760 p hp hnot
  · exact idoH2_m840 p hp hnot
  · exact idoH2_m1320 p hp hnot
  · exact idoH2_m1365 p hp hnot
  · exact idoH2_m1848 p hp hnot
