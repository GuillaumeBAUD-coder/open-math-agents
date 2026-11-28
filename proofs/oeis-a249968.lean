import OMAStatements.S_oeis_a249968

open OMA.S_oeis_a249968

def both : List ℕ :=
  (List.range 100).filter fun r =>
    (List.range 100).any (fun i => i * i % 100 == r) &&
      (List.range 100).any (fun i => i * (i + 1) % 100 == r)

lemma both_eq : both = [0, 56] := by
  decide

lemma mod10000 (q s : ℕ) : (10000 * q + s) % 10000 = s % 10000 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

lemma squareForm (q : ℕ) : (10 * q + 5) ^ 2 = 100 * (q * (q + 1)) + 25 := by
  ring

lemma reduce (q : ℕ) : (100 * q + 25) % 10000 = 100 * (q % 100) + 25 := by
  have h := Nat.div_add_mod q 100
  have hlt : 100 * (q % 100) + 25 < 10000 := by
    have := Nat.mod_lt q (show 0 < 100 by decide)
    omega
  calc
    (100 * q + 25) % 10000
        = (100 * (100 * (q / 100) + q % 100) + 25) % 10000 := by
          nth_rw 1 [← h]
    _ = (10000 * (q / 100) + (100 * (q % 100) + 25)) % 10000 := by ring
    _ = (100 * (q % 100) + 25) % 10000 := by rw [mod10000]
    _ = 100 * (q % 100) + 25 := Nat.mod_eq_of_lt hlt

lemma notSquare_of_bounds {n a : ℕ} (hlo : a * a < n) (hhi : n < (a + 1) * (a + 1)) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  rcases Nat.lt_or_ge k (a + 1) with h | h
  · have hk' : k ≤ a := by omega
    have : k * k ≤ a * a := Nat.mul_le_mul hk' hk'
    omega
  · have : (a + 1) * (a + 1) ≤ k * k := Nat.mul_le_mul h h
    omega

lemma mod100 (k s : ℕ) : (100 * k + s) % 100 = s % 100 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

lemma last5 (r : ℕ) : (100 * r + 25) % 10 = 5 := by
  have h100 : (100 * r) % 10 = 0 := by
    rw [Nat.mul_mod]
    norm_num
  rw [Nat.add_mod, h100]

lemma prodMod (q : ℕ) : (q % 100) * ((q % 100) + 1) % 100 = q * (q + 1) % 100 := by
  have hdiv := Nat.div_add_mod q 100
  set a := q / 100
  set b := q % 100
  have hq : q = 100 * a + b := by omega
  have hexpand :
      (100 * a + b) * (100 * a + b + 1) =
        100 * ((100 * a + b) * a + (b + 1) * a) + b * (b + 1) := by
    ring_nf
  rw [hq, hexpand, mod100]

lemma inBoth {r : ℕ} (hr : r < 100)
    (hs : ∃ i, i < 100 ∧ i * i % 100 = r)
    (hp : ∃ i, i < 100 ∧ i * (i + 1) % 100 = r) :
    r = 0 ∨ r = 56 := by
  have hmem : r ∈ both := by
    rw [both]
    refine List.mem_filter.2 ⟨List.mem_range.2 hr, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [List.any_eq_true]
      rcases hs with ⟨i, hi, hi'⟩
      exact ⟨i, List.mem_range.2 hi, by simp [hi']⟩
    · rw [List.any_eq_true]
      rcases hp with ⟨i, hi, hi'⟩
      exact ⟨i, List.mem_range.2 hi, by simp [hi']⟩
  have : r ∈ [0, 56] := by simpa [both_eq] using hmem
  simp at this
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a249968.main := by
  intro n hn
  obtain ⟨hn0, hsq⟩ := hn
  have hsmall : n < 10 → False := by
    intro hlt
    interval_cases n
    · have hw : wrap (1 ^ 2) = 2125 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 46 * 46 < 2125) (by norm_num) hsq
    · have hw : wrap (2 ^ 2) = 2425 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 49 * 49 < 2425) (by norm_num) hsq
    · have hw : wrap (3 ^ 2) = 2925 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 54 * 54 < 2925) (by norm_num) hsq
    · have hw : wrap (4 ^ 2) = 21625 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 147 * 147 < 21625) (by norm_num) hsq
    · have hw : wrap (5 ^ 2) = 22525 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 150 * 150 < 22525) (by norm_num) hsq
    · have hw : wrap (6 ^ 2) = 23625 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 153 * 153 < 23625) (by norm_num) hsq
    · have hw : wrap (7 ^ 2) = 24925 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 157 * 157 < 24925) (by norm_num) hsq
    · have hw : wrap (8 ^ 2) = 26425 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 162 * 162 < 26425) (by norm_num) hsq
    · have hw : wrap (9 ^ 2) = 28125 := by decide
      rw [hw] at hsq
      exact notSquare_of_bounds (by norm_num : 167 * 167 < 28125) (by norm_num) hsq
  have hn10 : 10 ≤ n := by
    by_contra h
    exact hsmall (by omega)
  have h100 : 100 ≤ n ^ 2 := by nlinarith
  refine ⟨h100, ?_⟩
  let L := (Nat.digits 10 (n ^ 2)).length
  have hlen : 2 < L :=
    (Nat.lt_digits_length_iff (by decide : 1 < 10) (n ^ 2)).2 (by simpa [L] using h100)
  have hpow : 10 ^ (L + 2) = 10 ^ (L - 2) * 10000 := by
    have : L + 2 = L - 2 + 4 := by omega
    rw [this, pow_add]
    norm_num
  have hsplit : wrap (n ^ 2) = 10000 * (2 * 10 ^ (L - 2)) + (100 * n ^ 2 + 25) := by
    unfold wrap
    rw [hpow]
    ring
  have hmod : wrap (n ^ 2) % 10000 = (100 * n ^ 2 + 25) % 10000 := by
    rw [hsplit, mod10000]
  have hrest : 100 * n ^ 2 + 25 = 10000 * (n ^ 2 / 100) + (100 * (n ^ 2 % 100) + 25) := by
    have hdiv := Nat.div_add_mod (n ^ 2) 100
    conv_lhs => rw [← hdiv]
    ring
  have hlt : 100 * (n ^ 2 % 100) + 25 < 10000 := by
    have := Nat.mod_lt (n ^ 2) (show 0 < 100 by decide)
    omega
  have hwrap : wrap (n ^ 2) % 10000 = 100 * (n ^ 2 % 100) + 25 := by
    rw [hmod, hrest, mod10000, Nat.mod_eq_of_lt hlt]
  obtain ⟨t, ht⟩ := hsq
  have htmod : t * t % 10000 = 100 * (n ^ 2 % 100) + 25 := by
    rw [← ht, hwrap]
  have hlast : t % 10 = 5 := by
    have hfive : (100 * (n ^ 2 % 100) + 25) % 10 = 5 := last5 _
    have : t * t % 10 = 5 := by
      have hdiv10 : 10 ∣ 10000 := by decide
      have h10 : t * t % 10 = (t * t % 10000) % 10 :=
        (Nat.mod_mod_of_dvd (t * t) hdiv10).symm
      rw [h10, htmod]
      exact hfive
    have hd : t % 10 < 10 := Nat.mod_lt _ (by decide)
    have hsqd : (t % 10) * (t % 10) % 10 = 5 := by
      rw [← this]
      exact (Nat.mul_mod t t 10).symm
    have : ∀ d : Fin 10, (d : ℕ) * (d : ℕ) % 10 = 5 → (d : ℕ) = 5 := by decide
    exact this ⟨t % 10, hd⟩ hsqd
  let q := t / 10
  have htq : t = 10 * q + 5 := by
    have := Nat.div_add_mod t 10
    omega
  have htform : t * t = 100 * (q * (q + 1)) + 25 := by
    rw [htq]
    simpa [Nat.pow_two] using squareForm q
  have hr : q * (q + 1) % 100 = n ^ 2 % 100 := by
    have hmul : (100 * (q * (q + 1)) + 25) % 10000 = 100 * (n ^ 2 % 100) + 25 := by
      rw [← htform, htmod]
    rw [reduce] at hmul
    omega
  have hrlt : n ^ 2 % 100 < 100 := Nat.mod_lt _ (by decide)
  refine inBoth hrlt ?_ ?_
  · refine ⟨n % 100, Nat.mod_lt _ (by decide), ?_⟩
    simpa [Nat.pow_two] using (Nat.mul_mod n n 100).symm
  · refine ⟨q % 100, Nat.mod_lt _ (by decide), ?_⟩
    rw [prodMod, hr]
