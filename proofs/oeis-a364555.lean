import OMAStatements.S_oeis_a364555

-- Problem oeis-a364555: for m > 0, no triangular number equals m times a prime if and only if for every divisor d
-- of m (with r = m / d) and every prime q, none of 2r - 1 = q d, 2r + 1 = q d, r - 1 = 2 q d, r + 1 = 2 q d holds.
-- Upstream: statements/oeis-a364555.lean (declaration OMA.S_oeis_a364555.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: k(k+1)/2 = m p means k(k+1) = 2 m p. The prime p divides k or k + 1.
-- If k = p c then c (p c + 1) = 2m: for even c = 2d we get m = d (2pd + 1), i.e. r - 1 = 2 p d; for odd c the
-- factor p c + 1 is even, p c + 1 = 2e, m = c e, i.e. 2r - 1 = p c with d = c.
-- If k + 1 = p c then k c = 2m: for even c = 2d we get m = d k, i.e. r + 1 = 2 p d; for odd c, k = 2e, m = c e,
-- i.e. 2r + 1 = p c with d = c.
-- Conversely each of the four equations gives k explicitly (k = q d, 2r, 2 q d, r respectively).

open OMA.S_oeis_a364555

theorem OMA.solution : type_of% @OMA.S_oeis_a364555.main := by
  intro m hm
  have key : (∃ k p : ℕ, p.Prime ∧ k * (k + 1) / 2 = m * p) ↔
      ∃ d ∈ m.divisors, ∃ q : ℕ, q.Prime ∧
        (2 * (m / d) - 1 = q * d ∨ 2 * (m / d) + 1 = q * d ∨
          m / d - 1 = q * (2 * d) ∨ m / d + 1 = q * (2 * d)) := by
    constructor
    · rintro ⟨k, p, hp, hk⟩
      have hev : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
      have hk2 : k * (k + 1) = 2 * (m * p) := by
        have h := Nat.div_mul_cancel hev
        rw [hk] at h
        omega
      have hpdvd : p ∣ k * (k + 1) := ⟨2 * m, by rw [hk2]; ring⟩
      rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h | h
      · obtain ⟨c, rfl⟩ := h
        have hc : c * (p * c + 1) = 2 * m := by
          have h1 : p * (c * (p * c + 1)) = p * (2 * m) := by
            have h2 : p * (c * (p * c + 1)) = p * c * (p * c + 1) := by ring
            rw [h2, hk2]
            ring
          exact Nat.eq_of_mul_eq_mul_left hp.pos h1
        rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d', hd'⟩
        · subst hd
          have hm' : m = d * (2 * p * d + 1) := by
            have h2 : 2 * m = 2 * (d * (2 * p * d + 1)) := by
              rw [← hc]
              ring
            omega
          have hd0 : 0 < d := by
            rcases Nat.eq_zero_or_pos d with h0 | h0
            · subst h0
              simp at hm'
              omega
            · exact h0
          refine ⟨d, Nat.mem_divisors.mpr ⟨⟨2 * p * d + 1, hm'⟩, hm.ne'⟩, p, hp,
            Or.inr (Or.inr (Or.inl ?_))⟩
          rw [hm', Nat.mul_div_cancel_left _ hd0, Nat.add_sub_cancel]
          ring
        · have h2 : 2 ∣ c * (p * c + 1) := ⟨m, hc⟩
          have hcodd : ¬ 2 ∣ c := by
            rw [hd']
            omega
          obtain ⟨e, he⟩ := ((Nat.Prime.dvd_mul Nat.prime_two).mp h2).resolve_left hcodd
          have hme : m = c * e := by
            have h3 : 2 * m = 2 * (c * e) := by
              rw [← hc, he]
              ring
            omega
          have hc0 : 0 < c := by
            rw [hd']
            omega
          refine ⟨c, Nat.mem_divisors.mpr ⟨⟨e, hme⟩, hm.ne'⟩, p, hp, Or.inl ?_⟩
          rw [hme, Nat.mul_div_cancel_left _ hc0]
          omega
      · obtain ⟨c, hc1⟩ := h
        have hc0 : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · subst h0
            simp at hc1
          · exact h0
        have hkc : k * c = 2 * m := by
          have h1 : p * (k * c) = p * (2 * m) := by
            have h2 : p * (k * c) = k * (p * c) := by ring
            rw [h2, ← hc1, hk2]
            ring
          exact Nat.eq_of_mul_eq_mul_left hp.pos h1
        rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d', hd'⟩
        · subst hd
          have hmd : m = d * k := by
            have h2 : 2 * m = 2 * (d * k) := by
              rw [← hkc]
              ring
            omega
          have hd0 : 0 < d := by omega
          refine ⟨d, Nat.mem_divisors.mpr ⟨⟨k, hmd⟩, hm.ne'⟩, p, hp,
            Or.inr (Or.inr (Or.inr ?_))⟩
          rw [hmd, Nat.mul_div_cancel_left _ hd0, hc1]
          ring
        · have h2 : 2 ∣ k * c := ⟨m, hkc⟩
          have hcodd : ¬ 2 ∣ c := by
            rw [hd']
            omega
          obtain ⟨e, he⟩ := ((Nat.Prime.dvd_mul Nat.prime_two).mp h2).resolve_right hcodd
          have hme : m = c * e := by
            have h3 : 2 * m = 2 * (c * e) := by
              rw [← hkc, he]
              ring
            omega
          refine ⟨c, Nat.mem_divisors.mpr ⟨⟨e, hme⟩, hm.ne'⟩, p, hp, Or.inr (Or.inl ?_)⟩
          rw [hme, Nat.mul_div_cancel_left _ hc0, ← hc1, he]
    · rintro ⟨d, hd, q, hq, h⟩
      obtain ⟨⟨e, he⟩, _⟩ := Nat.mem_divisors.mp hd
      have hd0 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0
          simp at he
          omega
        · exact h0
      have he0 : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0
          simp at he
          omega
        · exact h0
      have hdiv : m / d = e := by
        rw [he]
        exact Nat.mul_div_cancel_left e hd0
      rw [hdiv] at h
      rcases h with h | h | h | h
      · refine ⟨q * d, q, hq, ?_⟩
        have h1 : q * d + 1 = 2 * e := by omega
        rw [h1, he, show q * d * (2 * e) = d * e * q * 2 by ring,
          Nat.mul_div_cancel _ (by norm_num)]
      · refine ⟨2 * e, q, hq, ?_⟩
        rw [h, he, show 2 * e * (q * d) = d * e * q * 2 by ring,
          Nat.mul_div_cancel _ (by norm_num)]
      · refine ⟨q * (2 * d), q, hq, ?_⟩
        have h1 : q * (2 * d) + 1 = e := by omega
        rw [h1, he, show q * (2 * d) * e = d * e * q * 2 by ring,
          Nat.mul_div_cancel _ (by norm_num)]
      · refine ⟨e, q, hq, ?_⟩
        rw [h, he, show e * (q * (2 * d)) = d * e * q * 2 by ring,
          Nat.mul_div_cancel _ (by norm_num)]
  unfold InSeq
  constructor
  · rintro ⟨_, hnot⟩ d hd q hq
    exact ⟨fun h => hnot (key.mpr ⟨d, hd, q, hq, Or.inl h⟩),
      fun h => hnot (key.mpr ⟨d, hd, q, hq, Or.inr (Or.inl h)⟩),
      fun h => hnot (key.mpr ⟨d, hd, q, hq, Or.inr (Or.inr (Or.inl h))⟩),
      fun h => hnot (key.mpr ⟨d, hd, q, hq, Or.inr (Or.inr (Or.inr h))⟩)⟩
  · intro hall
    refine ⟨hm, fun hP => ?_⟩
    obtain ⟨d, hd, q, hq, h⟩ := key.mp hP
    obtain ⟨h1, h2, h3, h4⟩ := hall d hd q hq
    rcases h with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
