import OMAStatements.S_oeis_a130770

-- Problem: A130770: One third of the least common multiple of 3 and n^2+n+1.
-- Upstream: formal-conjectures statements/oeis-a130770.lean:0 (declaration OMA.S_oeis_a130770.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a130770

open OMA.S_oeis_a130770

lemma den_of (p q : ℤ) (hq : 0 < q) (h : IsCoprime p q) :
    (((p : ℚ) / (q : ℚ)).den : ℤ) = q := by
  have := Rat.den_div_eq_of_coprime hq (Int.isCoprime_iff_gcd_eq_one.mp h)
  exact_mod_cast this

lemma solve : ∀ n : ℕ, 0 < n → a n = A046163 n := by
  intro n hn
  unfold a A046163
  by_cases h3 : n % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    have hl : Nat.lcm 3 ((3 * k + 1) ^ 2 + (3 * k + 1) + 1) =
        (3 * k + 1) ^ 2 + (3 * k + 1) + 1 :=
      Nat.lcm_eq_right ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩
    have e : (((3 * k + 1 : ℕ) : ℚ) - 1) ^ 2 / (((3 * k + 1 : ℕ) : ℚ) ^ 2 + ((3 * k + 1 : ℕ) : ℚ) + 1)
        = ((3 * (k : ℤ) ^ 2 : ℤ) : ℚ) / ((3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 : ℤ) : ℚ) := by
      push_cast
      have : (3 * (k : ℚ) ^ 2 + 3 * k + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hc : IsCoprime (3 * (k : ℤ) ^ 2) (3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) := by
      have h1 : IsCoprime (3 : ℤ) (3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) :=
        ⟨-((k : ℤ) ^ 2 + k), 1, by ring⟩
      have h2 : IsCoprime (k : ℤ) (3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) :=
        ⟨-(3 * (k : ℤ) + 3), 1, by ring⟩
      exact h1.mul_left h2.pow_left
    have hq : (0 : ℤ) < 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 := by positivity
    rw [hl, e]
    have := den_of _ _ hq hc
    have h' : ((3 * k + 1) ^ 2 + (3 * k + 1) + 1) / 3 = 3 * k ^ 2 + 3 * k + 1 := by
      rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
      omega
    rw [h']
    exact_mod_cast this.symm
  · have hm : (n ^ 2 + n + 1) % 3 = 1 := by
      obtain ⟨k, hk | hk⟩ : ∃ k, n = 3 * k ∨ n = 3 * k + 2 := ⟨n / 3, by omega⟩
      · subst hk
        have : (3 * k) ^ 2 + 3 * k + 1 = 3 * (3 * k ^ 2 + k) + 1 := by ring
        omega
      · subst hk
        have : (3 * k + 2) ^ 2 + (3 * k + 2) + 1 = 3 * (3 * k ^ 2 + 5 * k + 2) + 1 := by ring
        omega
    have hcop : Nat.Coprime 3 (n ^ 2 + n + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hcop.lcm_eq_mul, Nat.mul_div_cancel_left _ (by norm_num)]
    have h1 : IsCoprime ((n : ℤ) - 1) 3 := by
      obtain ⟨k, hk | hk⟩ : ∃ k, n = 3 * k ∨ n = 3 * k + 2 := ⟨n / 3, by omega⟩
      · subst hk
        exact ⟨-1, k, by push_cast; ring⟩
      · subst hk
        exact ⟨1, -k, by push_cast; ring⟩
    have h2 : IsCoprime ((n : ℤ) - 1) n := ⟨-1, 1, by ring⟩
    have h3 : IsCoprime (((n : ℤ) - 1) ^ 2) (3 * (n : ℤ)) := (h1.mul_right h2).pow_left
    have hc : IsCoprime (((n : ℤ) - 1) ^ 2) ((n : ℤ) ^ 2 + n + 1) := by
      have := h3.add_mul_left_right 1
      have e : 3 * (n : ℤ) + ((n : ℤ) - 1) ^ 2 * 1 = (n : ℤ) ^ 2 + n + 1 := by ring
      rwa [e] at this
    have hq : (0 : ℤ) < (n : ℤ) ^ 2 + n + 1 := by positivity
    have e : (((n : ℚ) - 1) ^ 2) / ((n : ℚ) ^ 2 + n + 1) =
        (((((n : ℤ) - 1) ^ 2 : ℤ)) : ℚ) / ((((n : ℤ) ^ 2 + n + 1 : ℤ)) : ℚ) := by
      push_cast
      ring
    rw [e]
    have := den_of _ _ hq hc
    exact_mod_cast this.symm

end OMA.P_oeis_a130770

theorem OMA.solution : type_of% @OMA.S_oeis_a130770.main := OMA.P_oeis_a130770.solve
