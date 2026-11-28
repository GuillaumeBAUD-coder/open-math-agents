import OMAStatements.S_oeis_a180337

open OMA.S_oeis_a180337 in
theorem OMA.solution : type_of% @OMA.S_oeis_a180337.main := by
  let E : Finset ℕ := {2, 5, 11, 23, 26, 47, 56, 95, 116, 122, 236, 254, 518, 530, 1082, 2210}
  have hiff : ∀ n : ℕ, n ∈ ({2, 5, 11, 23, 26, 47, 56, 95, 116, 122, 236, 254, 518, 530, 1082, 2210} : Set ℕ) ↔ n ∈ E := by
    intro n
    simp [E]
  -- Every value of `f` on a list of primes is positive and outside `E`.
  have stepA : ∀ p x : ℕ, p.Prime → x ∉ E → 1 + p * x ∉ E := by
    intro p x hp hx h
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · have := hp.two_le
      have : p * x = 1 := by omega
      have : x = 0 ∨ 1 ≤ x := by omega
      rcases this with h0 | h1
      · subst h0; omega
      · nlinarith
    · have hc : p * x = 4 := by omega
      have hd : p ∣ 2 * 2 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
    · have hc : p * x = 10 := by omega
      have hd : p ∣ 2 * 5 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
    · have hc : p * x = 22 := by omega
      have hd : p ∣ 2 * 11 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
    · have hc : p * x = 25 := by omega
      have hd : p ∣ 5 * 5 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
    · have hc : p * x = 46 := by omega
      have hd : p ∣ 2 * 23 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
    · have hc : p * x = 55 := by omega
      have hd : p ∣ 5 * 11 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
    · have hc : p * x = 94 := by omega
      have hd : p ∣ 2 * 47 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 2 := by omega
        exact hx (by decide)
    · have hc : p * x = 115 := by omega
      have hd : p ∣ 5 * 23 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
    · have hc : p * x = 121 := by omega
      have hd : p ∣ 11 * 11 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
    · have hc : p * x = 235 := by omega
      have hd : p ∣ 5 * 47 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 5 := by omega
        exact hx (by decide)
    · have hc : p * x = 253 := by omega
      have hd : p ∣ 11 * 23 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
    · have hc : p * x = 517 := by omega
      have hd : p ∣ 11 * 47 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 11 := by omega
        exact hx (by decide)
    · have hc : p * x = 529 := by omega
      have hd : p ∣ 23 * 23 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
    · have hc : p * x = 1081 := by omega
      have hd : p ∣ 23 * 47 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 23 := by omega
        exact hx (by decide)
    · have hc : p * x = 2209 := by omega
      have hd : p ∣ 47 * 47 := ⟨x, by omega⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        obtain rfl : x = 47 := by omega
        exact hx (by decide)
  have hA : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → f l ∉ E ∧ 0 < f l := by
    intro l
    induction l with
    | nil => intro _; exact ⟨by simp [f, E], by simp [f]⟩
    | cons p l ih =>
      intro hl
      have hp : p.Prime := hl p (by simp)
      obtain ⟨hx, hx0⟩ := ih (fun q hq => hl q (by simp [hq]))
      refine ⟨?_, by simp only [f]; omega⟩
      simp only [f]
      exact stepA p (f l) hp hx
  -- For `m ≥ 2` with `m + 1 ∉ E` some prime `q ∣ m` has `m / q ∉ E`.
  have stepB : ∀ m : ℕ, 2 ≤ m → m + 1 ∉ E → ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ m / q ∉ E := by
    intro m hm hn
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, hpd, hpmin⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q :=
      ⟨m.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd m,
        fun q hq hqd => Nat.minFac_le_of_dvd hq.two_le hqd⟩
    obtain ⟨e, he, hme⟩ : ∃ e ∈ E, m = p * e := ⟨m / p, hcon p hp hpd, (Nat.mul_div_cancel' hpd).symm⟩
    have he2 : 2 ≤ e := by
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      omega
    have hle : p ≤ e.minFac :=
      hpmin _ (Nat.minFac_prime (by omega)) (dvd_trans (Nat.minFac_dvd e) (by rw [hme]; exact dvd_mul_left e p))
    have hp2 := hp.two_le
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num at hle
      subst hme
      interval_cases p
    all_goals
      first
      | (revert hp; decide)
      | (revert hn; decide)
      | (have h := hcon 2; revert h; decide)
      | (have h := hcon 3; revert h; decide)
      | (have h := hcon 5; revert h; decide)
      | (have h := hcon 7; revert h; decide)
      | (have h := hcon 11; revert h; decide)
      | (have h := hcon 13; revert h; decide)
      | (have h := hcon 17; revert h; decide)
      | (have h := hcon 19; revert h; decide)
      | (have h := hcon 23; revert h; decide)
      | (have h := hcon 29; revert h; decide)
      | (have h := hcon 31; revert h; decide)
      | (have h := hcon 37; revert h; decide)
      | (have h := hcon 41; revert h; decide)
      | (have h := hcon 43; revert h; decide)
      | (have h := hcon 47; revert h; decide)
      | (have h := hcon 53; revert h; decide)
      | (have h := hcon 59; revert h; decide)
      | (have h := hcon 61; revert h; decide)
      | (have h := hcon 127 (by norm_num); revert h; decide)
      | (have h := hcon 541 (by norm_num); revert h; decide)
  have hB : ∀ n : ℕ, 0 < n → n ∉ E → ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ f l = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn0 hnE
      by_cases h1 : n = 1
      · exact ⟨[], by simp, by simp [f, h1]⟩
      have hn2 : n ≠ 2 := by rintro rfl; exact hnE (by decide)
      obtain ⟨q, hq, hqd, hqE⟩ := stepB (n - 1) (by omega) (by rwa [Nat.sub_add_cancel hn0])
      have hq0 : 0 < (n - 1) / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq.pos
      have hlt : (n - 1) / q < n := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      obtain ⟨l, hl, hfl⟩ := ih _ hlt hq0 hqE
      refine ⟨q :: l, ?_, ?_⟩
      · intro p hpl
        simp only [List.mem_cons] at hpl
        rcases hpl with rfl | hpl
        · exact hq
        · exact hl p hpl
      · simp only [f, hfl]
        rw [Nat.mul_div_cancel' hqd]
        omega
  ext n
  simp only [Set.mem_setOf_eq]
  rw [hiff n]
  constructor
  · rintro ⟨hn0, hno⟩
    by_contra hnE
    exact hno (hB n hn0 hnE)
  · intro hnE
    refine ⟨?_, ?_⟩
    · simp only [E, Finset.mem_insert, Finset.mem_singleton] at hnE
      omega
    · rintro ⟨l, hl, rfl⟩
      exact (hA l hl).1 hnE
