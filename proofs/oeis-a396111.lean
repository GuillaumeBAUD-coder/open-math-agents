import OMAStatements.S_oeis_a396111

/-!
# A396111 — `a n = n ^ 4 mod (2 * n + 1)` takes every value, and only finitely often

Write `m = 2 * n + 1`.  Always `16 * n ^ 4 - 1 = (2 * n - 1) * (2 * n + 1) * (4 * n ^ 2 + 1)`, so
`16 * n ^ 4 ≡ 1 (mod m)`.

* Every `k` occurs: take `k = j + 1` and `n = 8 * j + 7`, so `m = 16 * j + 15 = 16 * k - 1`.  Then
  `(8 * j + 7) ^ 4 = (j + 1) + (16 * j + 15) * (256 * j ^ 3 + 656 * j ^ 2 + 561 * j + 160)`, so
  `n ^ 4 ≡ k (mod m)`; and `0 ^ 4 mod 1 = 0` covers `k = 0`.
* Each fibre is finite: from `n ^ 4 ≡ k (mod m)` and `16 * n ^ 4 ≡ 1 (mod m)` we get
  `16 * k ≡ 1 (mod m)`, i.e. `m ∣ 16 * k - 1`.  For `k ≥ 1` that forces `m ≤ 16 * k - 1`, and for
  `k = 0` it forces `n = 0`.
-/

namespace OMA.A396111

open OMA.S_oeis_a396111

/-- `16 * n ^ 4 - 1` factors, in the form `16 * n ^ 4 = 1 + (2 * n + 1) * (...)`. -/
lemma sixteen_four (n : ℕ) (hn : 1 ≤ n) :
    16 * n ^ 4 = 1 + (2 * n + 1) * ((2 * n - 1) * (4 * n ^ 2 + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 from by omega]
  ring

/-- Writing `k = j + 1`, the index `n = 8 * j + 7` witnesses the value `j + 1`. -/
lemma a_witness (j : ℕ) : a (8 * j + 7) = j + 1 := by
  have hid : (8 * j + 7) ^ 4 =
      (j + 1) + (16 * j + 15) * (256 * j ^ 3 + 656 * j ^ 2 + 561 * j + 160) := by
    ring
  rw [a, show 2 * (8 * j + 7) + 1 = 16 * j + 15 from by ring, hid,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Every natural number occurs as a value of the sequence. -/
lemma exists_eq (k : ℕ) : ∃ n : ℕ, a n = k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    exact ⟨0, by decide⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨8 * j + 7, a_witness j⟩

/-- From `a n = k` we get `16 * k ≡ 1` modulo `2 * n + 1`. -/
lemma modEq_of_a_eq {n k : ℕ} (hn : 1 ≤ n) (h : a n = k) :
    Nat.ModEq (2 * n + 1) (16 * k) 1 := by
  have hd : (2 * n + 1) * (n ^ 4 / (2 * n + 1)) + n ^ 4 % (2 * n + 1) = n ^ 4 :=
    Nat.div_add_mod (n ^ 4) (2 * n + 1)
  rw [a] at h
  rw [h] at hd
  have hmul : (2 * n + 1) * (16 * (n ^ 4 / (2 * n + 1))) + 16 * k = 16 * n ^ 4 := by
    calc (2 * n + 1) * (16 * (n ^ 4 / (2 * n + 1))) + 16 * k
        = 16 * ((2 * n + 1) * (n ^ 4 / (2 * n + 1)) + k) := by ring
      _ = 16 * n ^ 4 := by rw [hd]
  have heq : (2 * n + 1) * (16 * (n ^ 4 / (2 * n + 1))) + 16 * k
      = 1 + (2 * n + 1) * ((2 * n - 1) * (4 * n ^ 2 + 1)) := by
    rw [hmul, sixteen_four n hn]
  have h1 : (16 * k + (2 * n + 1) * (16 * (n ^ 4 / (2 * n + 1)))) % (2 * n + 1)
      = 16 * k % (2 * n + 1) := Nat.add_mul_mod_self_left _ _ _
  have h2 : (1 + (2 * n + 1) * ((2 * n - 1) * (4 * n ^ 2 + 1))) % (2 * n + 1)
      = 1 % (2 * n + 1) := Nat.add_mul_mod_self_left _ _ _
  show 16 * k % (2 * n + 1) = 1 % (2 * n + 1)
  rw [← h1, add_comm, heq, h2]

/-- For `k ≥ 1` the index of a fibre is bounded by `8 * k - 1`. -/
lemma le_of_a_eq {n k : ℕ} (hk : 1 ≤ k) (h : a n = k) : n ≤ 8 * k - 1 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [a] at h
    simp at h
    omega
  · have hm := modEq_of_a_eq hn h
    have hbound : 2 * n + 1 ≤ 16 * k - 1 := by
      rcases Nat.lt_or_ge (2 * n + 1) 2 with hsmall | hbig
      · omega
      · have h1m : 1 % (2 * n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        have hmod : 16 * k % (2 * n + 1) = 1 := by
          have := hm
          unfold Nat.ModEq at this
          rw [h1m] at this
          exact this
        have hdiv : (2 * n + 1) * (16 * k / (2 * n + 1)) + 1 = 16 * k := by
          have := Nat.div_add_mod (16 * k) (2 * n + 1)
          rw [hmod] at this
          exact this
        have hdvd : (2 * n + 1) ∣ 16 * k - 1 := ⟨16 * k / (2 * n + 1), by omega⟩
        exact Nat.le_of_dvd (by omega) hdvd
    omega

/-- `a n = 0` forces `n = 0`. -/
lemma eq_zero_of_a_eq_zero {n : ℕ} (h : a n = 0) : n = 0 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · exact hn0
  · have hm := modEq_of_a_eq hn h
    have h0 : 0 % (2 * n + 1) = 1 % (2 * n + 1) := by
      have hm' := hm
      unfold Nat.ModEq at hm'
      simpa using hm'
    rcases Nat.lt_or_ge (2 * n + 1) 2 with hsmall | hbig
    · omega
    · have h1m : 1 % (2 * n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m, Nat.zero_mod] at h0
      omega

/-- Every fibre is finite. -/
lemma finite_fibre (k : ℕ) : Set.Finite {n : ℕ | a n = k} := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hsub : {n : ℕ | a n = 0} ⊆ {0} := by
      intro n hn
      exact Set.mem_singleton_iff.mpr (eq_zero_of_a_eq_zero hn)
    exact Set.Finite.subset (Set.finite_singleton 0) hsub
  · have hsub : {n : ℕ | a n = k} ⊆ Set.Iic (8 * k - 1) := by
      intro n hn
      exact le_of_a_eq hk hn
    exact Set.Finite.subset (Set.finite_Iic (8 * k - 1)) hsub

end OMA.A396111

theorem OMA.solution : type_of% @OMA.S_oeis_a396111.main := by
  exact ⟨OMA.A396111.exists_eq, OMA.A396111.finite_fibre⟩
