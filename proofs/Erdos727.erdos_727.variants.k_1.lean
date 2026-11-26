import FormalConjectures.ErdosProblems.«727»

-- Problem: Erdős Problem 727 — k 1
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/727.lean:56 (declaration Erdos727.erdos_727.variants.k_1)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- If `n` lies in the upper half of the residue block `[M*d, M*(d+1))`, there is a carry. -/
lemma carry (n M d : ℕ) (h1 : 2 * (M * d) + M ≤ 2 * n) (h2 : n < M * (d + 1)) :
    M ≤ 2 * (n % M) := by
  have hd : n / M = d := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  have h3 := Nat.div_add_mod n M
  rw [hd] at h3
  omega

/-- Kummer: every position with a carry contributes to the valuation of `C(2n, n)`. -/
lemma val_ge (r n : ℕ) (hr : r.Prime) (S : Finset ℕ)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ r ^ i ≤ 2 * (n % r ^ i)) :
    r ^ S.card ∣ (n + n).choose n := by
  have : Fact r.Prime := ⟨hr⟩
  rw [padicValNat_dvd_iff_le (Nat.choose_pos (by omega)).ne']
  rw [padicValNat_choose' (lt_add_one _)]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨h1, h2⟩ := hS i hi
  rw [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨h1, ?_⟩, by omega⟩
  have h3 : i ≤ Nat.log r (n + n) :=
    Nat.le_log_of_pow_le hr.one_lt (by have := Nat.mod_le n (r ^ i); omega)
  omega

/-- Balakram's family: `n + 1 = p q` with `3p/2 < q < 2p`. -/
lemma c1 (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (h1 : 3 * p < 2 * q) (h2 : q < 2 * p)
    (hn : n + 1 = p * q) : (n + 1) ^ 2 ∣ (n + n).choose n := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq : p ≠ q := by omega
  have hc : ({1, 2} : Finset ℕ).card = 2 := by decide
  have hP : p ^ 2 ∣ (n + n).choose n := by
    have h := val_ge p n hp {1, 2} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine ⟨le_rfl, ?_⟩
        rw [pow_one]
        obtain ⟨q0, rfl⟩ : ∃ q0, q = q0 + 1 := ⟨q - 1, by omega⟩
        exact carry n p q0 (by nlinarith) (by nlinarith)
      · refine ⟨by norm_num, ?_⟩
        have e1 := Nat.mul_le_mul_left p (show 3 * p + 1 ≤ 2 * q by omega)
        have e2 := Nat.mul_le_mul_left p (show q ≤ 2 * p by omega)
        exact carry n (p ^ 2) 1 (by nlinarith) (by nlinarith))
    rwa [hc] at h
  have hQ : q ^ 2 ∣ (n + n).choose n := by
    have h := val_ge q n hq {1, 2} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine ⟨le_rfl, ?_⟩
        rw [pow_one]
        obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact carry n q p0 (by nlinarith) (by nlinarith)
      · refine ⟨by norm_num, ?_⟩
        have e1 := Nat.mul_le_mul_left q (show q + 1 ≤ 2 * p by omega)
        have e2 := Nat.mul_le_mul_left q (show p + 1 ≤ q by omega)
        exact carry n (q ^ 2) 0 (by nlinarith) (by nlinarith))
    rwa [hc] at h
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp hq).2 hpq)
  have e : (n + 1) ^ 2 = p ^ 2 * q ^ 2 := by rw [hn]; ring
  rw [e]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hP hQ

/-- Second family: `n + 1 = 4 p q` with `11p/8 < q < 3p/2` and `p q - 1` not a power of two. -/
lemma c4 (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (h1 : 11 * p < 8 * q) (h2 : 2 * q < 3 * p)
    (hn : n + 1 = 4 * (p * q))
    (hb : ∃ a b w', p * q = 2 ^ a + w' + 1 ∧ 2 ^ b ≤ w' ∧ w' < 2 ^ (b + 1) ∧ b < a) :
    (n + 1) ^ 2 ∣ (n + n).choose n := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq : p ≠ q := by omega
  have hp' : 2 ≠ p := by omega
  have hq' : 2 ≠ q := by omega
  have hc : ({1, 2} : Finset ℕ).card = 2 := by decide
  have hP : p ^ 2 ∣ (n + n).choose n := by
    have h := val_ge p n hp {1, 2} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine ⟨le_rfl, ?_⟩
        rw [pow_one]
        obtain ⟨d, hd⟩ : ∃ d, 4 * q = d + 1 := ⟨4 * q - 1, by omega⟩
        have e : p * (4 * q) = p * (d + 1) := by rw [hd]
        exact carry n p d (by nlinarith) (by nlinarith)
      · refine ⟨by norm_num, ?_⟩
        have e1 := Nat.mul_le_mul_left p (show 11 * p + 1 ≤ 8 * q by omega)
        have e2 := Nat.mul_le_mul_left p (show 2 * q ≤ 3 * p by omega)
        exact carry n (p ^ 2) 5 (by nlinarith) (by nlinarith))
    rwa [hc] at h
  have hQ : q ^ 2 ∣ (n + n).choose n := by
    have h := val_ge q n hq {1, 2} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine ⟨le_rfl, ?_⟩
        rw [pow_one]
        obtain ⟨d, hd⟩ : ∃ d, 4 * p = d + 1 := ⟨4 * p - 1, by omega⟩
        have e : q * (4 * p) = q * (d + 1) := by rw [hd]
        exact carry n q d (by nlinarith) (by nlinarith)
      · refine ⟨by norm_num, ?_⟩
        have e1 := Nat.mul_le_mul_left q (show 5 * q + 1 ≤ 8 * p by omega)
        have e2 := Nat.mul_le_mul_left q (show 4 * p + 1 ≤ 3 * q by omega)
        exact carry n (q ^ 2) 2 (by nlinarith) (by nlinarith))
    rwa [hc] at h
  have hT : 2 ^ 4 ∣ (n + n).choose n := by
    obtain ⟨a, b, w', hw, hb1, hb2, hba⟩ := hb
    have hn' : n = 4 * 2 ^ a + 4 * w' + 3 := by rw [hw] at hn; omega
    have hpa : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba
    have eb1 : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    have eb3 : 2 ^ (b + 3) = 8 * 2 ^ b := by ring
    have ea3 : 2 ^ (a + 3) = 8 * 2 ^ a := by ring
    have hc4 : ({1, 2, b + 3, a + 3} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      · omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h := val_ge 2 n Nat.prime_two {1, 2, b + 3, a + 3} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · refine ⟨le_rfl, ?_⟩
        exact carry n (2 ^ 1) (2 * 2 ^ a + 2 * w' + 1) (by omega) (by omega)
      · refine ⟨by norm_num, ?_⟩
        exact carry n (2 ^ 2) (2 ^ a + w') (by omega) (by omega)
      · refine ⟨by omega, ?_⟩
        have e2 : 2 ^ (b + 3) * 2 ^ (a - b - 1) = 4 * 2 ^ a := by
          rw [← pow_add]
          have : b + 3 + (a - b - 1) = a + 2 := by omega
          rw [this]; ring
        refine carry n (2 ^ (b + 3)) (2 ^ (a - b - 1)) ?_ ?_
        · rw [e2, eb3]; omega
        · rw [mul_add, mul_one, e2, eb3]; omega
      · refine ⟨by omega, ?_⟩
        refine carry n (2 ^ (a + 3)) 0 ?_ ?_
        · rw [ea3]; omega
        · rw [ea3]; omega)
    rwa [hc4] at h
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp hq).2 hpq)
  have hcop2 : Nat.Coprime (2 ^ 4) (p ^ 2 * q ^ 2) :=
    Nat.Coprime.mul_right
      (Nat.Coprime.pow 4 2 ((Nat.coprime_primes Nat.prime_two hp).2 hp'))
      (Nat.Coprime.pow 4 2 ((Nat.coprime_primes Nat.prime_two hq).2 hq'))
  have e : (n + 1) ^ 2 = 2 ^ 4 * (p ^ 2 * q ^ 2) := by rw [hn]; ring
  rw [e]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 hT
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hP hQ)

/-- A positive number that is not a power of two has two binary digits equal to one. -/
lemma bits (w : ℕ) (hw : w ≠ 0) (h : ∀ k, w ≠ 2 ^ k) :
    ∃ a b w', w = 2 ^ a + w' ∧ 2 ^ b ≤ w' ∧ w' < 2 ^ (b + 1) ∧ b < a := by
  have h1 := Nat.pow_log_le_self 2 hw
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) w
  have hw' : w - 2 ^ Nat.log 2 w ≠ 0 := by
    intro h0
    exact h (Nat.log 2 w) (by omega)
  have h3 := Nat.pow_log_le_self 2 hw'
  have h4 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (w - 2 ^ Nat.log 2 w)
  refine ⟨Nat.log 2 w, Nat.log 2 (w - 2 ^ Nat.log 2 w), w - 2 ^ Nat.log 2 w,
    by omega, h3, h4, ?_⟩
  by_contra hcon
  have h5 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hcon)
  rw [Nat.succ_eq_add_one, pow_succ] at h2
  omega

lemma small_prime (r a b : ℕ) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime)
    (h1 : r < a) (h2 : r < b) (hd : r ∣ a * b) : False := by
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hr ha).1 h
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hr hb).1 h
    omega

/-- With `a` between `4^j` and `2.75 * 4^j` and `a < b < 1.5 a`, `a b - 1` is no power of two. -/
lemma no_exc (a b j k : ℕ) (ha : a.Prime) (hb : b.Prime) (hj : 16 ≤ 4 ^ j) (h1 : 4 ^ j < a)
    (h2 : 8 * a ≤ 22 * 4 ^ j) (h3 : a < b) (h4 : 2 * b < 3 * a) : a * b ≠ 2 ^ k + 1 := by
  intro h
  have m3 : ∀ i : ℕ, 16 ^ i % 3 = 1 := by
    intro i
    rw [Nat.pow_mod]
    norm_num
  have m5 : ∀ i : ℕ, 16 ^ i % 5 = 1 := by
    intro i
    rw [Nat.pow_mod]
    norm_num
  have e16 : ∀ i : ℕ, 2 ^ (4 * i) = 16 ^ i := by
    intro i
    rw [pow_mul]
    norm_num
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ :
      ∃ i, k = 4 * i ∨ k = 4 * i + 1 ∨ k = 4 * i + 2 ∨ k = 4 * i + 3 := ⟨k / 4, by omega⟩
  · have e : (16 : ℕ) ^ i = 4 ^ i * 4 ^ i := by
      rw [← mul_pow]; norm_num
    rw [e16, e] at h
    rcases le_or_gt i j with hij | hij
    · have hY : 4 ^ i ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hij
      have := Nat.mul_le_mul (show 4 ^ i + 1 ≤ a by omega) (show 4 ^ i + 2 ≤ b by omega)
      generalize 4 ^ i = Y at *
      nlinarith
    · have hY : 4 ^ (j + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) hij
      rw [pow_succ] at hY
      have A := Nat.mul_le_mul h2 h2
      have B := Nat.mul_le_mul_left a (show 2 * b ≤ 3 * a by omega)
      have C := Nat.mul_le_mul hY hY
      generalize 4 ^ i = Y at *
      generalize 4 ^ j = X at *
      nlinarith
  · have e : 2 ^ (4 * i + 1) = 2 * 16 ^ i := by rw [pow_succ, e16]; ring
    rw [e] at h
    have := m3 i
    exact small_prime 3 a b Nat.prime_three ha hb (by omega) (by omega)
      (by rw [h]; exact Nat.dvd_of_mod_eq_zero (by omega))
  · have e : 2 ^ (4 * i + 2) = 4 * 16 ^ i := by rw [pow_add, e16]; ring
    rw [e] at h
    have := m5 i
    exact small_prime 5 a b Nat.prime_five ha hb (by omega) (by omega)
      (by rw [h]; exact Nat.dvd_of_mod_eq_zero (by omega))
  · have e : 2 ^ (4 * i + 3) = 8 * 16 ^ i := by rw [pow_add, e16]; ring
    rw [e] at h
    have := m3 i
    exact small_prime 3 a b Nat.prime_three ha hb (by omega) (by omega)
      (by rw [h]; exact Nat.dvd_of_mod_eq_zero (by omega))

/-- From Bertrand alone: near every prime `p` there is a pair of primes with ratio in
`(11/8, 3/2)` or in `(3/2, 2)`. -/
lemma pair (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ a b, a.Prime ∧ b.Prime ∧ p ≤ a ∧ 8 * a ≤ 11 * p ∧
      ((3 * a < 2 * b ∧ b < 2 * a) ∨ (11 * a < 8 * b ∧ 2 * b < 3 * a)) := by
  have hle : p ≤ 11 * p / 8 := by omega
  have hq : (Nat.findGreatest Nat.Prime (11 * p / 8)).Prime := Nat.findGreatest_spec hle hp
  have hpq : p ≤ Nat.findGreatest Nat.Prime (11 * p / 8) := Nat.le_findGreatest hle hp
  have hqle : Nat.findGreatest Nat.Prime (11 * p / 8) ≤ 11 * p / 8 := Nat.findGreatest_le _
  have hmax : ∀ k, Nat.findGreatest Nat.Prime (11 * p / 8) < k → k ≤ 11 * p / 8 → ¬ k.Prime :=
    fun k hk hkb => Nat.findGreatest_is_greatest hk hkb
  generalize Nat.findGreatest Nat.Prime (11 * p / 8) = q at hq hpq hqle hmax
  obtain ⟨q', hq', hlt, hle2⟩ := Nat.exists_prime_lt_and_le_two_mul q (by omega)
  have hbig : 11 * p / 8 < q' := by
    by_contra hcon
    exact hmax q' hlt (not_lt.mp hcon) hq'
  have hodd : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ 2 ∣ r := by
    intro r hr h5r hd
    rcases (Nat.dvd_prime hr).1 hd with h | h <;> omega
  have hne1 : 2 * q' ≠ 3 * p := by
    intro h
    exact hodd p hp h5 (by omega)
  have hne2 : q' ≠ 2 * p := by
    intro h
    rw [h] at hq'
    rcases (Nat.dvd_prime hq').1 (Dvd.intro_left 2 rfl) with h' | h' <;> omega
  have hne3 : 2 * q' ≠ 3 * q := by
    intro h
    exact hodd q hq (by omega) (by omega)
  have hne4 : q' ≠ 2 * q := by
    intro h
    rw [h] at hq'
    rcases (Nat.dvd_prime hq').1 (Dvd.intro_left 2 rfl) with h' | h' <;> omega
  by_cases hc : q' < 2 * p
  · refine ⟨p, q', hp, hq', le_rfl, by omega, ?_⟩
    omega
  · refine ⟨q, q', hq, hq', hpq, by omega, ?_⟩
    omega

lemma exists_n (N : ℕ) : ∃ n, N < n ∧ (n + 1) ^ 2 ∣ (n + n).choose n := by
  have hN : N + 2 < 4 ^ (N + 2) := Nat.lt_pow_self (by norm_num)
  have h16 : 16 ≤ 4 ^ (N + 2) :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ (N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨p, hp, hXp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (4 ^ (N + 2)) (by omega)
  obtain ⟨a, b, ha, hb, hpa, hap, hcase⟩ := pair p hp (by omega)
  have hb2 := hb.two_le
  have hab := Nat.mul_le_mul_left a hb2
  rcases hcase with ⟨c1a, c1b⟩ | ⟨c4a, c4b⟩
  · refine ⟨a * b - 1, by omega, ?_⟩
    exact c1 a b (a * b - 1) ha hb c1a c1b (by omega)
  · refine ⟨4 * (a * b) - 1, by omega, ?_⟩
    obtain ⟨x, y, w', hw, hy1, hy2, hyx⟩ := bits (a * b - 1) (by omega) (by
      intro k hk
      exact no_exc a b (N + 2) k ha hb h16 (by omega) (by omega) (by omega) c4b (by omega))
    exact c4 a b (4 * (a * b) - 1) ha hb c4a c4b (by omega) ⟨x, y, w', by omega, hy1, hy2, hyx⟩

lemma fact_dvd (n : ℕ) (h : (n + 1) ^ 2 ∣ (n + n).choose n) :
    (n + 1).factorial ^ 2 ∣ (2 * n).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + n by omega)
  rw [Nat.add_sub_cancel] at h1
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [two_mul, ← h1, hc, Nat.factorial_succ]
  ring

end OMA

theorem OMA.solution : type_of% @Erdos727.erdos_727.variants.k_1 := by
  show Set.Infinite {n : ℕ | (n + 1).factorial ^ 2 ∣ (2 * n).factorial}
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn, hd⟩ := OMA.exists_n N
  exact ⟨n, OMA.fact_dvd n hd, hn⟩
