import OMAStatements.S_oeis_a000350

-- Complete proof of OEIS A000350 via 2-adic Pisano period induction
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a000350

private lemma ofDigits_append (b : ℕ) :
    ∀ l₁ l₂ : List ℕ,
      Nat.ofDigits b (l₁ ++ l₂) = Nat.ofDigits b l₁ + b ^ l₁.length * Nat.ofDigits b l₂
  | [], l₂ => by simp [Nat.ofDigits]
  | a :: t, l₂ => by
    simp only [List.cons_append, Nat.ofDigits, List.length_cons, pow_succ', ofDigits_append b t l₂]
    ring

private lemma ofDigits_lt_pow {b : ℕ} (hb : 0 < b) :
    ∀ l : List ℕ, (∀ d ∈ l, d < b) → Nat.ofDigits b l < b ^ l.length
  | [], _ => by simp [Nat.ofDigits]
  | a :: t, h => by
    have ha : a < b := h a (by simp)
    have ht : Nat.ofDigits b t < b ^ t.length :=
      ofDigits_lt_pow hb t (fun d hd => h d (by simp [hd]))
    simp only [Nat.ofDigits, List.length_cons, pow_succ']
    have hmul : b * (Nat.ofDigits b t + 1) ≤ b * b ^ t.length := Nat.mul_le_mul_left b ht
    linarith

private lemma fib_add_shift (a : ℕ) :
    ∀ b : ℕ, Nat.fib (a + 1 + b) = Nat.fib a * Nat.fib b + Nat.fib (a + 1) * Nat.fib (b + 1)
  | 0 => by simp
  | 1 => by
    rw [show a + 1 + 1 = a + 2 by omega, Nat.fib_add_two]
    simp
  | b + 2 => by
    have h1 := fib_add_shift a b
    have h2 := fib_add_shift a (b + 1)
    have h3 : a + 1 + (b + 2) = (a + 1 + b) + 2 := by omega
    have hfb : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
    have hfb1 : Nat.fib (b + 2 + 1) = Nat.fib (b + 1) + Nat.fib (b + 2) := Nat.fib_add_two
    have hfb0 : Nat.fib (b + 1 + 1) = Nat.fib (b + 2) := rfl
    rw [h3, Nat.fib_add_two, show a + 1 + b + 1 = a + 1 + (b + 1) by omega, h1, h2, hfb0, hfb1, hfb]
    ring

private lemma fib_two_mul (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n) = Nat.fib n * (Nat.fib (n - 1) + Nat.fib (n + 1)) := by
  have h := fib_add_shift (n - 1) n
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 1 + 1 + n = 2 * n := by omega
  rw [h2, h1] at h
  rw [h]
  ring

private lemma fib_two_mul_add_one (n : ℕ) :
    Nat.fib (2 * n + 1) = Nat.fib n ^ 2 + Nat.fib (n + 1) ^ 2 := by
  have h := fib_add_shift n n
  have h1 : n + 1 + n = 2 * n + 1 := by omega
  rw [h1] at h
  rw [h]
  ring

private lemma fib_mod_periodic {N M : ℕ} (h0 : Nat.fib N % M = 0) (h1 : Nat.fib (N + 1) % M = 1 % M) :
    ∀ n : ℕ, Nat.fib (N + n) % M = Nat.fib n % M
  | 0 => by simpa using h0
  | 1 => by simpa using h1
  | n + 2 => by
    have ih0 := fib_mod_periodic h0 h1 n
    have ih1 := fib_mod_periodic h0 h1 (n + 1)
    have hadd : N + (n + 2) = (N + n) + 2 := by omega
    rw [hadd, Nat.fib_add_two, Nat.fib_add_two, Nat.add_mod,
        show N + n + 1 = N + (n + 1) by omega, ih0, ih1, ← Nat.add_mod]

private lemma fib_mod_periodic_mul {N M : ℕ} (h0 : Nat.fib N % M = 0)
    (h1 : Nat.fib (N + 1) % M = 1 % M) (r : ℕ) :
    ∀ q : ℕ, Nat.fib (N * q + r) % M = Nat.fib r % M
  | 0 => by simp
  | q + 1 => by
    have ih := fib_mod_periodic_mul h0 h1 r q
    rw [mul_add, mul_one, show N * q + N + r = N + (N * q + r) by omega,
        fib_mod_periodic h0 h1, ih]

private lemma pisano_pow2 :
    ∀ t : ℕ,
      Nat.fib (3 * 2 ^ (t + 2)) % 2 ^ (t + 3) = 0 ∧
      Nat.fib (3 * 2 ^ (t + 2) + 1) % 2 ^ (t + 3) = 1
  | 0 => by decide
  | t + 1 => by
    obtain ⟨h0, h1⟩ := pisano_pow2 t
    set N := 3 * 2 ^ (t + 2)
    set M := 2 ^ (t + 3)
    have hN1 : 1 ≤ N := Nat.mul_pos (by omega) (by positivity)
    have hM_even : 2 ∣ M := ⟨2 ^ (t + 2), by simp [M, pow_succ']⟩
    have h2N : 3 * 2 ^ (t + 1 + 2) = 2 * N := by simp [N, pow_succ]; ring
    have h2M : 2 ^ (t + 1 + 3) = 2 * M := by simp [M, pow_succ']
    rw [h2N, h2M]
    obtain ⟨u, hu⟩ : M ∣ Nat.fib N := Nat.dvd_of_mod_eq_zero h0
    have hMgt1 : 1 < M := by
      have : 2 ^ 3 ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨v, hv⟩ : ∃ v, Nat.fib (N + 1) = M * v + 1 :=
      ⟨Nat.fib (N + 1) / M, by have := Nat.div_add_mod (Nat.fib (N + 1)) M; omega⟩
    have hprev : Nat.fib (N - 1) + Nat.fib N = Nat.fib (N + 1) := by
      have := Nat.fib_add_two (n := N - 1)
      have ha : N - 1 + 2 = N + 1 := by omega
      have hb : N - 1 + 1 = N := by omega
      rw [ha, hb] at this
      omega
    obtain ⟨m2, hm2⟩ := hM_even
    constructor
    · rw [fib_two_mul N hN1, hu]
      have heven : 2 ∣ (Nat.fib (N - 1) + Nat.fib (N + 1)) :=
        ⟨Nat.fib (N - 1) + m2 * u, by rw [← hprev, hu, hm2]; ring⟩
      obtain ⟨w, hw⟩ := heven
      rw [hw]
      have : M * u * (2 * w) = 2 * M * (u * w) := by ring
      rw [this, Nat.mul_mod_right]
    · rw [fib_two_mul_add_one N, hu, hv]
      have : (M * u) ^ 2 + (M * v + 1) ^ 2 =
          2 * M * (m2 * u ^ 2 + m2 * v ^ 2 + v) + 1 := by
        rw [hm2]; ring
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private lemma fib_mod4_cases (r : ℕ) (hlt : r < 12) (h : Nat.fib r % 4 = r % 4) :
    r = 0 ∨ r = 1 ∨ r = 5 := by
  interval_cases r <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | (exfalso; revert h; decide)

private lemma fib_eq_mod_pow2 :
    ∀ t : ℕ, ∀ m : ℕ, Nat.fib m % 2 ^ (t + 2) = m % 2 ^ (t + 2) →
      m % (3 * 2 ^ (t + 2)) = 0 ∨ m % (3 * 2 ^ (t + 2)) = 1 ∨ m % (3 * 2 ^ (t + 2)) = 5
  | 0, m, hm => by
    have hm4 : Nat.fib m % 4 = m % 4 := by simpa using hm
    have hp0 : Nat.fib 6 % 4 = 0 := by decide
    have hp1 : Nat.fib 7 % 4 = 1 % 4 := by decide
    have hper : Nat.fib m % 4 = Nat.fib (m % 12) % 4 := by
      have hdiv : m = 6 * (2 * (m / 12)) + m % 12 := by omega
      conv_lhs => rw [hdiv]
      exact fib_mod_periodic_mul hp0 hp1 (m % 12) (2 * (m / 12))
    have hm12 : Nat.fib (m % 12) % 4 = (m % 12) % 4 := by
      rw [← hper, hm4]; omega
    exact fib_mod4_cases (m % 12) (Nat.mod_lt m (by omega)) hm12
  | t + 1, m, hm => by
    have hmk : Nat.fib m % 2 ^ (t + 2) = m % 2 ^ (t + 2) := by
      have h1 : (Nat.fib m % 2 ^ (t + 3)) % 2 ^ (t + 2) =
          (m % 2 ^ (t + 3)) % 2 ^ (t + 2) := congrArg (· % 2 ^ (t + 2)) hm
      rwa [Nat.mod_mod_of_dvd _ ⟨2, by rw [pow_succ]⟩,
           Nat.mod_mod_of_dvd _ ⟨2, by rw [pow_succ]⟩] at h1
    have ihr := fib_eq_mod_pow2 t m hmk
    set N := 3 * 2 ^ (t + 2)
    set M := 2 ^ (t + 3)
    obtain ⟨hp0, hp1⟩ := pisano_pow2 t
    have hMge8 : 8 ≤ M := by
      have : 2 ^ 3 ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hp1' : Nat.fib (N + 1) % M = 1 % M := by
      rw [hp1, Nat.mod_eq_of_lt (by omega)]
    set q := m / N
    set r := m % N
    have hdiv : m = N * q + r := (Nat.div_add_mod m N).symm
    have hfib_m : Nat.fib m % M = Nat.fib r % M := by
      conv_lhs => rw [hdiv]
      exact fib_mod_periodic_mul hp0 hp1' r q
    have hfib_r : Nat.fib r = r := by
      rcases ihr with hr | hr | hr
      · rw [hr]; decide
      · rw [hr]; decide
      · rw [hr]; decide
    have hmod : (N * q + r) % M = r := by
      have hrlt : r < M := by rcases ihr with hr | hr | hr <;> omega
      rw [← hdiv, ← hm, hfib_m, hfib_r, Nat.mod_eq_of_lt hrlt]
    have hdvd : M ∣ N * q := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hrlt : r < M := by rcases ihr with hr | hr | hr <;> omega
      have hstep : (N * q % M + r) % M = r := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hmod]
      have hlt2 : N * q % M < M := Nat.mod_lt _ (by positivity)
      by_contra hne
      have hpos : 0 < N * q % M := Nat.pos_of_ne_zero hne
      by_cases hsum : N * q % M + r < M
      · rw [Nat.mod_eq_of_lt hsum] at hstep; omega
      · have hsub : (N * q % M + r) % M = N * q % M + r - M := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hsub] at hstep; omega
    have hq_even : 2 ∣ q := by
      obtain ⟨u, hu⟩ := hdvd
      have hM2 : M = 2 ^ (t + 2) * 2 := by simp [M, pow_succ]
      have hN2 : N = 2 ^ (t + 2) * 3 := by simp [N]; ring
      rw [hM2, hN2] at hu
      have h3q : 3 * q = 2 * u := by
        have hpos : 0 < 2 ^ (t + 2) := by positivity
        have : 2 ^ (t + 2) * (3 * q) = 2 ^ (t + 2) * (2 * u) := by linarith
        exact Nat.eq_of_mul_eq_mul_left hpos this
      omega
    obtain ⟨q', hq'⟩ := hq_even
    have hN2 : 3 * 2 ^ (t + 1 + 2) = 2 * N := by simp [N, pow_succ]; ring
    have hmod2 : m % (3 * 2 ^ (t + 1 + 2)) = r := by
      rw [hdiv, hq', hN2, show N * (2 * q') + r = (2 * N) * q' + r by ring, Nat.mul_add_mod]
      have hrlt : r < 2 * N := by
        have : r < N := Nat.mod_lt m (by positivity)
        omega
      exact Nat.mod_eq_of_lt hrlt
    rw [hmod2]
    exact ihr

theorem OMA.solution : type_of% @OMA.S_oeis_a000350.main := by
  intro m hm
  constructor
  · rintro ⟨front, hrev⟩
    have hdig : Nat.digits 2 (Nat.fib m) = Nat.digits 2 m ++ front.reverse := by
      have := congrArg List.reverse hrev
      simpa using this
    set k := (Nat.digits 2 m).length
    have hval : Nat.fib m = m + 2 ^ k * Nat.ofDigits 2 front.reverse := by
      have h1 := congrArg (Nat.ofDigits 2) hdig
      rw [Nat.ofDigits_digits, ofDigits_append, Nat.ofDigits_digits] at h1
      exact h1
    have hmlt : m < 2 ^ k := by
      have hlt := ofDigits_lt_pow (b := 2) (by omega) (Nat.digits 2 m)
        (fun d hd => Nat.digits_lt_base (by omega) hd)
      rwa [Nat.ofDigits_digits] at hlt
    have hkpos : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0] at hmlt
      omega
    by_cases hk1 : k = 1
    · rw [hk1] at hmlt
      left; omega
    · have hkge : 2 ≤ k := by omega
      have hmod : Nat.fib m % 2 ^ k = m % 2 ^ k := by
        rw [hval, Nat.add_mul_mod_self_left]
      have hk_eq : k = (k - 2) + 2 := by omega
      rw [hk_eq] at hmod hmlt
      have hres := fib_eq_mod_pow2 (k - 2) m hmod
      have hmlt3 : m < 3 * 2 ^ ((k - 2) + 2) := by omega
      rw [Nat.mod_eq_of_lt hmlt3] at hres
      rcases hres with rfl | rfl | rfl
      · omega
      · left; rfl
      · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨[], by decide⟩
    · exact ⟨[], by decide⟩
