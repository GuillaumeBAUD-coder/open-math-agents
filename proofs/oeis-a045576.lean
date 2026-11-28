import OMAStatements.S_oeis_a045576

-- Problem oeis-a045576: if k divides 3^k + 2^k and k is not 1, then k = p * m with p prime and m again a number
-- dividing 3^m + 2^m.
-- Upstream: statements/oeis-a045576.lean (declaration OMA.S_oeis_a045576.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: k is coprime to 6. Let p be the largest prime factor of k and m = k / p. For every prime q dividing m we
-- show v_q(m) <= v_q(3^m + 2^m).
-- (i) q divides 3^m + 2^m. For q = p this is Fermat: a^p = a mod p. For q < p put t = 3/2 mod q; then
--     t^(pm) = -1, so t^(2pm) = 1 and t^(q-1) = 1; as p is coprime to q - 1, t^(2m) = 1, so t^m = 1 or -1, and
--     t^m = 1 would give t^(pm) = 1. Hence t^m = -1.
-- (ii) Lifting the exponent: v_q((3^m)^p + (2^m)^p) = v_q(3^m + 2^m) + v_q(p).
-- (iii) v_q(p) + v_q(m) = v_q(k) <= v_q(3^k + 2^k), and the v_q(p) cancels.

open OMA.S_oeis_a045576

theorem OMA.solution : type_of% @OMA.S_oeis_a045576.main := by
  intro k hk hk1
  unfold IsTerm at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hk2 : 2 ≤ k := by omega
  have hne : k.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hk2
  obtain ⟨p, hpdef⟩ : ∃ p, p = k.primeFactors.max' hne := ⟨_, rfl⟩
  have hpmem : p ∈ k.primeFactors := by
    rw [hpdef]
    exact Finset.max'_mem _ hne
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpk : p ∣ k := Nat.dvd_of_mem_primeFactors hpmem
  have hmax : ∀ q : ℕ, q.Prime → q ∣ k → q ≤ p := by
    intro q hq hqk
    rw [hpdef]
    exact Finset.le_max' _ q (Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩)
  obtain ⟨m, hkm⟩ := hpk
  subst hkm
  refine ⟨p, m, hpp, ?_, rfl⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hk0
  have hq_odd : ∀ q : ℕ, q.Prime → q ∣ p * m → q ≠ 2 ∧ q ≠ 3 := by
    intro q hq hqk
    constructor
    · rintro rfl
      have h2 : 2 ∣ 3 ^ (p * m) + 2 ^ (p * m) := dvd_trans hqk hk
      have h22 : 2 ∣ 2 ^ (p * m) := dvd_pow_self 2 hk0
      have h23 : 2 ∣ 3 ^ (p * m) + 2 ^ (p * m) - 2 ^ (p * m) := Nat.dvd_sub h2 h22
      rw [Nat.add_sub_cancel] at h23
      have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h23
      omega
    · rintro rfl
      have h3 : 3 ∣ 3 ^ (p * m) + 2 ^ (p * m) := dvd_trans hqk hk
      have h33 : 3 ∣ 3 ^ (p * m) := dvd_pow_self 3 hk0
      have h32 : 3 ∣ 3 ^ (p * m) + 2 ^ (p * m) - 3 ^ (p * m) := Nat.dvd_sub h3 h33
      rw [Nat.add_sub_cancel_left] at h32
      have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
      omega
  have hpodd : Odd p := hpp.odd_of_ne_two (hq_odd p hpp (dvd_mul_right p m)).1
  show m ∣ 3 ^ m + 2 ^ m
  have hN0 : 3 ^ m + 2 ^ m ≠ 0 := by positivity
  rw [← Nat.factorization_prime_le_iff_dvd hm0 hN0]
  intro q hq
  by_cases hqm : q ∣ m
  swap
  · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
    exact Nat.zero_le _
  have hfact : Fact q.Prime := ⟨hq⟩
  have hqk : q ∣ p * m := Dvd.dvd.mul_left hqm p
  obtain ⟨hq2, hq3⟩ := hq_odd q hq hqk
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h
    have hc : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hc
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hc)
  have h3ne : (3 : ZMod q) ≠ 0 := by
    intro h
    have hc : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hc
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hc)
  have h0 : (3 : ZMod q) ^ (p * m) + 2 ^ (p * m) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (3 ^ (p * m) + 2 ^ (p * m)) q).mpr (dvd_trans hqk hk)
    push_cast at h
    exact h
  have hi : q ∣ 3 ^ m + 2 ^ m := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    by_cases hqp : q = p
    · rw [← hqp, mul_comm q m, pow_mul, pow_mul, ZMod.pow_card, ZMod.pow_card] at h0
      exact h0
    · have hqltp : q < p := lt_of_le_of_ne (hmax q hq hqk) hqp
      obtain ⟨t, ht⟩ : ∃ t : ZMod q, t = 3 / 2 := ⟨_, rfl⟩
      have htn : ∀ n : ℕ, t ^ n * 2 ^ n = 3 ^ n := by
        intro n
        rw [ht, div_pow, div_mul_cancel₀ _ (pow_ne_zero n h2ne)]
      have ht0 : t ≠ 0 := by
        rw [ht]
        exact div_ne_zero h3ne h2ne
      have htk : t ^ (p * m) = -1 := by
        have h1 := htn (p * m)
        have h3 : (3 : ZMod q) ^ (p * m) = -(2 ^ (p * m)) := eq_neg_of_add_eq_zero_left h0
        rw [h3] at h1
        have h2k : (2 : ZMod q) ^ (p * m) ≠ 0 := pow_ne_zero _ h2ne
        have h4 : t ^ (p * m) * 2 ^ (p * m) = (-1) * 2 ^ (p * m) := by
          rw [h1]
          ring
        exact mul_right_cancel₀ h2k h4
      have hfer : t ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one ht0
      have h2k1 : t ^ (2 * (p * m)) = 1 := by
        rw [mul_comm, pow_mul, htk]
        norm_num
      have hg : t ^ Nat.gcd (2 * (p * m)) (q - 1) = 1 := pow_gcd_eq_one.mpr ⟨h2k1, hfer⟩
      have hcop : Nat.Coprime p (q - 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd hpp]
        intro hd
        have hq1 : 0 < q - 1 := by
          have := hq.two_le
          omega
        have := Nat.le_of_dvd hq1 hd
        omega
      have hgd : Nat.gcd (2 * (p * m)) (q - 1) ∣ 2 * m := by
        have e2 : 2 * (p * m) = p * (2 * m) := by ring
        rw [e2, Nat.Coprime.gcd_mul_left_cancel (2 * m) hcop]
        exact Nat.gcd_dvd_left _ _
      obtain ⟨c, hc⟩ := hgd
      have h2m : t ^ (2 * m) = 1 := by
        rw [hc, pow_mul, hg, one_pow]
      have hsq : t ^ m * t ^ m = 1 := by
        rw [← pow_add, ← two_mul]
        exact h2m
      rcases mul_self_eq_one_iff.mp hsq with h1 | h1
      · exfalso
        have h5 : t ^ (p * m) = 1 := by
          rw [mul_comm, pow_mul, h1, one_pow]
        rw [htk] at h5
        apply h2ne
        linear_combination (-1 : ZMod q) * h5
      · have h3m := htn m
        rw [h1] at h3m
        rw [← h3m]
        ring
  have hx : ¬ q ∣ 3 ^ m := fun h =>
    hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h))
  have hlte := padicValNat.pow_add_pow (p := q) (x := 3 ^ m) (y := 2 ^ m) hqodd hi hx hpodd
  have hkN : padicValNat q (p * m) ≤ padicValNat q (3 ^ (p * m) + 2 ^ (p * m)) := by
    have h := (Nat.factorization_le_iff_dvd hk0 (by positivity)).mpr hk q
    rwa [Nat.factorization_def _ hq, Nat.factorization_def _ hq] at h
  have hmul : padicValNat q (p * m) = padicValNat q p + padicValNat q m :=
    padicValNat.mul hpp.ne_zero hm0
  have e : 3 ^ (p * m) + 2 ^ (p * m) = (3 ^ m) ^ p + (2 ^ m) ^ p := by
    rw [mul_comm, pow_mul, pow_mul]
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  rw [e, hlte, hmul] at hkN
  omega
