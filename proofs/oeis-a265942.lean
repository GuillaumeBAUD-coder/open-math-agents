import OMAStatements.S_oeis_a265942

-- Problem: A265942: G.f. A(x) satisfies: x = Sum_{n>=1} x^n * A(-n*x).
-- Upstream: formal-conjectures statements/oeis-a265942.lean:0 (declaration OMA.S_oeis_a265942.main)
-- Original Lean proof: @agchua.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: strong induction. For n = r + 3 write a(n) = F 0 + F 1 + F 2 + Sum_{j<r} F (3+j),
-- with F k = (-1)^(n-k+1) * (n-k+1)^k * a(k). For k = 3 + j the induction gives a(k) = 4q + 2,
-- and since x^k - x is even, F k = 2 x mod 4 with x = n - k + 1 = r + 1 - j; the sum of
-- 2 (r + 1 - j) over j < r is r^2 + 3r. With a(0) = a(1) = a(2) = 1 the first three terms add up to
-- (-1)^r (r+1)(r+2), and a(n) - 2 is then 2 (r^2 + 3r) mod 4 for even r and -4 for odd r.

open OMA.S_oeis_a265942 in
theorem OMA.solution : type_of% @OMA.S_oeis_a265942.main := by
  have hrec : ∀ n : ℕ, a (n + 1) = ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n + 1 - k + 1) * ((n + 1 - k + 1 : ℕ) : ℤ) ^ k * a k := by
    intro n
    rw [a, Finset.sum_range]
  have h0 : a 0 = 1 := by rw [a]
  have h1 : a 1 = 1 := by simpa [h0] using hrec 0
  have h2 : a 2 = 1 := by simpa [Finset.sum_range_succ, h0, h1] using hrec 1
  have Sar : ∀ r : ℕ, ∑ j ∈ Finset.range r, 2 * ((r + 1 - j : ℕ) : ℤ) = (r : ℤ) ^ 2 + 3 * r := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
      rw [Finset.sum_range_succ']
      have e : ∀ j ∈ Finset.range r,
          2 * ((r + 1 + 1 - (j + 1) : ℕ) : ℤ) = 2 * ((r + 1 - j : ℕ) : ℤ) := by
        intro j _
        rw [show r + 1 + 1 - (j + 1) = r + 1 - j by omega]
      rw [Finset.sum_congr rfl e, ihr, show r + 1 + 1 - 0 = r + 2 by omega]
      push_cast
      ring
  have key : ∀ n : ℕ, 3 ≤ n → a n % 4 = 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 + 1 := ⟨n - 3, by omega⟩
      let F (k : ℕ) : ℤ :=
        (-1 : ℤ) ^ (r + 2 + 1 - k + 1) * ((r + 2 + 1 - k + 1 : ℕ) : ℤ) ^ k * a k
      have hsum : a (r + 2 + 1) = F 0 + F 1 + F 2 + ∑ j ∈ Finset.range r, F (3 + j) := by
        rw [hrec (r + 2)]
        change ∑ k ∈ Finset.range (r + 2 + 1), F k = _
        rw [show r + 2 + 1 = 3 + r by omega, Finset.sum_range_add]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have hstart : F 0 + F 1 + F 2 = (-1 : ℤ) ^ r * ((r : ℤ) + 1) * (r + 2) := by
        simp only [F, h0, h1, h2,
          show r + 2 + 1 - 0 + 1 = r + 4 by omega,
          show r + 2 + 1 - 1 + 1 = r + 3 by omega,
          show r + 2 + 1 - 2 + 1 = r + 2 by omega]
        push_cast
        ring
      have T : ∀ j : ℕ, j < r → 4 ∣ F (3 + j) - 2 * ((r + 1 - j : ℕ) : ℤ) := by
        intro j hj
        let y := r + 1 - j
        have ha : (2 : ℤ) ≡ a (3 + j) [ZMOD 4] := (ih (3 + j) (by omega) (by omega)).symm
        have hp : (y : ℤ) ≡ (y : ℤ) ^ (3 + j) [ZMOD 2] := by
          apply Int.modEq_iff_dvd.mpr
          rcases Int.even_or_odd (y : ℤ) with hx | hx
          · exact (Even.sub (hx.pow_of_ne_zero (n := 3 + j) (by omega)) hx).two_dvd
          · exact (Odd.sub_odd (hx.pow (n := 3 + j)) hx).two_dvd
        have hs : (1 : ℤ) ≡ (-1 : ℤ) ^ y [ZMOD 2] := by
          simpa only [one_pow] using (show (1 : ℤ) ≡ -1 [ZMOD 2] by decide).pow y
        have hh := (hs.mul hp).mul_right' (c := 2)
        dsimp only [F]
        rw [show r + 2 + 1 - (3 + j) + 1 = y by dsimp [y]; omega]
        exact Int.modEq_iff_dvd.mp (by
          simpa only [one_mul, mul_comm (y : ℤ) 2, show (2 : ℤ) * 2 = 4 by decide, y] using
            hh.trans (ha.mul_left _))
      have htail : 4 ∣ ∑ j ∈ Finset.range r, F (3 + j) -
          ∑ j ∈ Finset.range r, 2 * ((r + 1 - j : ℕ) : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.dvd_sum (fun j hj => T j (Finset.mem_range.mp hj))
      have hbase : 4 ∣ F 0 + F 1 + F 2 + ((r : ℤ) ^ 2 + 3 * r) - 2 := by
        rw [hstart]
        rcases Nat.even_or_odd r with he | ho
        · rw [he.neg_one_pow]
          obtain ⟨t, rfl⟩ := he
          exact ⟨2 * (t : ℤ) ^ 2 + 3 * t, by push_cast; ring⟩
        · rw [ho.neg_one_pow]
          exact ⟨-1, by ring⟩
      obtain ⟨q, hq⟩ := dvd_add hbase htail
      have hfin : 4 ∣ a (r + 2 + 1) - 2 := ⟨q, by
        rw [hsum]
        linear_combination hq + Sar r⟩
      omega
  intro n hn
  exact key n (by omega)
