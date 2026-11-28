import OMAStatements.S_oeis_a034444

-- Problem: A034444 (Ianakiev's conjecture): for n > 0 and every k, the sum of the k-th powers of the odd
--   unitary divisors of n divides the sum of the k-th powers of all unitary divisors of n.
-- Credit: @alan-phobos-claude
-- Proof (as in Bala's comment on the OEIS entry): write n = 2^a * m with m odd. If a = 0 the sums are equal.
--   Otherwise the even unitary divisors are exactly 2^a * e for e an odd unitary divisor, so the full sum is
--   (1 + 2^(a*k)) times the odd one.

open OMA.S_oeis_a034444 Finset

/-- `d` is a unitary divisor of `N ≠ 0` iff `N = d * c` with `d` and `c` coprime. -/
lemma A034444.mem_unitary {N d : ℕ} (hN : N ≠ 0) :
    d ∈ unitary N ↔ ∃ c, N = d * c ∧ Nat.Coprime d c := by
  simp only [unitary, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨c, rfl⟩, -⟩, h⟩
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
    exact ⟨c, rfl, by rwa [Nat.mul_div_cancel_left _ hd] at h⟩
  · rintro ⟨c, rfl, h⟩
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
    exact ⟨⟨dvd_mul_right _ _, hN⟩, by rwa [Nat.mul_div_cancel_left _ hd]⟩

/-- A divisor of an odd number is odd. -/
lemma A034444.odd_of_dvd {m d : ℕ} (hm : Odd m) (h : d ∣ m) : Odd d := by
  obtain ⟨c, rfl⟩ := h; exact (Nat.odd_mul.1 hm).1

/-- Every `n ≠ 0` is `2 ^ a * m` with `m` odd. -/
lemma A034444.two_pow_mul_odd (n : ℕ) (hn : n ≠ 0) : ∃ a m, Odd m ∧ n = 2 ^ a * m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨q, rfl⟩ | h
    · obtain ⟨a, m, hm, rfl⟩ := ih q (by omega) (by omega)
      exact ⟨a + 1, m, hm, by rw [pow_succ, mul_right_comm, mul_two]⟩
    · exact ⟨0, n, h, by simp⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a034444.main := by
  intro n hn k
  obtain ⟨a, m, hm, rfl⟩ := A034444.two_pow_mul_odd _ hn.ne'
  have hN : 2 ^ a * m ≠ 0 := hn.ne'
  rw [← sum_filter_add_sum_filter_not (unitary (2 ^ a * m)) Odd]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- `n` is odd: every unitary divisor is odd, so the two sums are equal
    rw [sum_eq_zero (s := (unitary (2 ^ 0 * m)).filter (fun d => ¬ Odd d)) (fun d hd => ?_), add_zero]
    rw [mem_filter, A034444.mem_unitary hN] at hd
    obtain ⟨⟨c, hc, -⟩, hodd⟩ := hd
    exact absurd (A034444.odd_of_dvd hm ⟨c, by simpa using hc⟩) hodd
  · -- `n = 2^a * m` with `a > 0`: the even unitary divisors are exactly `2^a * e`, `e` odd unitary
    suffices h : ∑ d ∈ (unitary (2 ^ a * m)).filter (fun d => ¬ Odd d), d ^ k =
        (2 ^ a) ^ k * ∑ d ∈ (unitary (2 ^ a * m)).filter Odd, d ^ k by
      rw [h]; exact dvd_add dvd_rfl (dvd_mul_left _ _)
    have hmul : ∀ s : Finset ℕ, ∑ e ∈ s, (2 ^ a) ^ k * e ^ k = (2 ^ a) ^ k * ∑ e ∈ s, e ^ k := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [sum_insert hx, sum_insert hx, ih, mul_add]
    rw [← hmul]; symm
    refine sum_nbij (2 ^ a * ·) (fun e he => ?_) ((mul_right_injective₀ (pow_ne_zero a two_ne_zero)).injOn)
      (fun d hd => ?_) (fun e _ => (mul_pow _ _ _).symm)
    · -- `e` odd unitary ⇒ `2^a * e` even unitary
      rw [mem_filter, A034444.mem_unitary hN] at he
      obtain ⟨⟨c, hc, hec⟩, he⟩ := he
      have : 2 ^ a ∣ c := ((Nat.coprime_two_left.2 he).pow_left a).dvd_of_dvd_mul_left ⟨m, hc.symm⟩
      obtain ⟨c', rfl⟩ := this
      have hmc : m = e * c' := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_left_comm])
      have hc' : Odd c' := A034444.odd_of_dvd hm ⟨e, by rw [hmc, mul_comm]⟩
      rw [mem_filter, A034444.mem_unitary hN]
      refine ⟨⟨c', by rw [hmc, mul_assoc], Nat.coprime_mul_iff_left.2
        ⟨(Nat.coprime_two_left.2 hc').pow_left a, hec.coprime_dvd_right (dvd_mul_left _ _)⟩⟩, ?_⟩
      exact Nat.not_odd_iff_even.2 (even_iff_two_dvd.2 (dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') e))
    · -- `d` even unitary ⇒ `d = 2^a * e` with `e` odd unitary
      rw [mem_coe, mem_filter, A034444.mem_unitary hN] at hd
      obtain ⟨⟨c, hc, hdc⟩, hd⟩ := hd
      have hco : Odd c :=
        Nat.coprime_two_left.1 (hdc.coprime_dvd_left (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hd)))
      obtain ⟨e, rfl⟩ : 2 ^ a ∣ d :=
        ((Nat.coprime_two_left.2 hco).pow_left a).dvd_of_dvd_mul_right ⟨m, hc.symm⟩
      have hmc : m = e * c := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_assoc])
      have he : Odd e := A034444.odd_of_dvd hm ⟨c, hmc⟩
      refine ⟨e, ?_, rfl⟩
      rw [mem_coe, mem_filter, A034444.mem_unitary hN]
      exact ⟨⟨2 ^ a * c, by rw [hmc, mul_left_comm], Nat.coprime_mul_iff_right.2
        ⟨((Nat.coprime_two_left.2 he).pow_left a).symm, hdc.coprime_dvd_left (dvd_mul_left _ _)⟩⟩, he⟩
