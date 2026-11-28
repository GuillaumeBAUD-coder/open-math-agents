import OMAStatements.S_oeis_a082090

namespace OMA.S_oeis_a082090

private theorem nth_prime_bound (i : ℕ) : Nat.nth Nat.Prime i ≤ 2 ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨q, hqp, hql, hqu⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime i)
        (by have := Nat.add_two_le_nth_prime i; omega)
    have hq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hqp
    have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hi : i < Nat.count Nat.Prime q := hmono.lt_iff_lt.mp (hq.symm ▸ hql)
    have hnext : Nat.nth Nat.Prime (i + 1) ≤ q := by
      rw [← hq]
      exact hmono.monotone (Nat.succ_le_of_lt hi)
    calc
      _ ≤ 2 * Nat.nth Nat.Prime i := hnext.trans hqu
      _ ≤ 2 * 2 ^ (i + 1) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ 2 (i + 1), Nat.mul_comm]

private theorem prime_index_bounds {p : ℕ} (hp : p.Prime) :
    Nat.primeCounting p < p ∧ p ≤ 2 ^ Nat.primeCounting p := by
  have he : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have hlow := Nat.add_two_le_nth_prime (Nat.count Nat.Prime p)
  have hu := nth_prime_bound (Nat.count Nat.Prime p)
  rw [he] at hlow hu
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ, if_pos hp]
  exact ⟨by omega, hu⟩

private theorem factor_list_bounds (l : List ℕ) (h : ∀ p ∈ l, p.Prime) :
    (l.map Nat.primeCounting).sum < l.prod ∧ l.prod ≤ 2 ^ (l.map Nat.primeCounting).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := h p List.mem_cons_self
    obtain ⟨hl, hu⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    obtain ⟨hpl, hpu⟩ := prime_index_bounds hp
    have haux : p + l.prod ≤ p * l.prod + 1 := by
      obtain ⟨d, hd⟩ : ∃ d, l.prod = d + 1 := ⟨l.prod - 1, by omega⟩
      have hmul : d ≤ p * d := by
        simpa using Nat.mul_le_mul_right d (show 1 ≤ p from hp.pos)
      rw [hd, Nat.mul_add, Nat.mul_one]
      omega
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact ⟨by omega, by rw [pow_add]; exact Nat.mul_le_mul hpu hu⟩

private theorem pseudo_bounds {n : ℕ} (hn : 0 < n) :
    A056239 n < n ∧ n ≤ 2 ^ A056239 n := by
  unfold A056239
  simpa only [Nat.prod_primeFactorsList hn.ne'] using
    factor_list_bounds n.primeFactorsList (fun _ h => Nat.prime_of_mem_primeFactorsList h)

private theorem pseudo_pow_two (j : ℕ) : A056239 (2 ^ j) = j := by
  have hc : Nat.count Nat.Prime 2 = 0 := by
    simpa only [Nat.primeCounting', Nat.nth_prime_zero_eq_two] using Nat.primeCounting'_nth_eq 0
  have htwo : Nat.primeCounting 2 = 1 := by
    unfold Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_succ, if_pos Nat.prime_two, hc]
  simp [A056239, Nat.prime_two.primeFactorsList_pow, htwo, List.sum_replicate]

private theorem saturated (m : ℕ) : ∀ fuel, m < fuel → lenFuel fuel m = A082090 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases hm : m = 0
    · subst m
      simp [A082090, lenFuel]
    · have hlt := (pseudo_bounds (Nat.pos_of_ne_zero hm)).1
      simp only [A082090, lenFuel, if_neg hm]
      rw [ih _ hlt f (by omega), ih _ hlt m hlt]

private theorem length_step {m : ℕ} (hm : 0 < m) :
    A082090 m = 1 + A082090 (A056239 m) := by
  unfold A082090
  rw [lenFuel, if_neg hm.ne']
  exact congrArg (1 + ·) (saturated _ _ (pseudo_bounds hm).1)

private theorem length_zero : A082090 0 = 1 := by simp [A082090, lenFuel]

private theorem length_positive (m : ℕ) : 0 < A082090 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [length_zero]
  · rw [length_step hm]
    omega

private theorem tower_positive (j : ℕ) : 0 < tower j := by
  cases j with
  | zero => decide
  | succ j =>
    change 0 < 2 ^ tower j
    positivity

private theorem tower_length (j : ℕ) : A082090 (tower j) = j + 2 := by
  induction j with
  | zero => simp [tower, A082090, lenFuel, A056239]
  | succ j ih =>
    rw [length_step (tower_positive _)]
    change 1 + A082090 (A056239 (2 ^ tower j)) = j + 1 + 2
    rw [pseudo_pow_two, ih]
    omega

private theorem tower_bound (j m : ℕ) (hm : 0 < m) (hlen : A082090 m = j + 2) :
    m ≤ tower j := by
  induction j generalizing m with
  | zero =>
    have hl := length_step hm
    have he : A056239 m = 0 := by
      by_contra h
      have hp := length_step (Nat.pos_of_ne_zero h)
      have hn := length_positive (A056239 (A056239 m))
      omega
    have h := (pseudo_bounds hm).2
    simpa [he, tower] using h
  | succ j ih =>
    have hl := length_step hm
    have he : 0 < A056239 m := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, length_zero] at hl
      omega
    have hlen' : A082090 (A056239 m) = j + 2 := by omega
    exact (pseudo_bounds hm).2.trans (Nat.pow_le_pow_right (by decide) (ih _ he hlen'))

end OMA.S_oeis_a082090

open OMA.S_oeis_a082090 in
theorem OMA.solution : type_of% @OMA.S_oeis_a082090.main := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨tower_length j, fun n hn h => tower_bound j n (by omega) h⟩
