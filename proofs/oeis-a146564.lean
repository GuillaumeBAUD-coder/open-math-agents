import OMAStatements.S_oeis_a146564

-- Problem: A146564: a(n) is the number of solutions of the equation k*n/(k-n) = c. k,c integers.
-- Upstream: formal-conjectures statements/oeis-a146564.lean:0 (declaration OMA.S_oeis_a146564.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- This is a KNOWN result: U. Cerruti, Percorsi tra i numeri, Corollario 4 (linked from the OEIS
-- entry A146564), proves a(n) = A048691(n) + A063647(n) for all n > 0. This file is a Lean
-- formalization of that statement, along the same lines:
--   * for k > n, (k - n) | k n iff (k - n) | n^2, so these k are n + d with d a divisor of n^2;
--   * for 0 < k < n, (k - n) | k n iff 1/n = 1/k - 1/c for some c > k, so these k are exactly
--     the b counted by A063647 (mem_B_iff).

namespace OMA.A146564

lemma mem_B_iff (n k : ℕ) (hn : 1 ≤ n) :
    (0 < k ∧ ∃ c : ℕ, k < c ∧ (1 : ℚ) / n = 1 / k - 1 / c)
      ↔ (0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · rintro ⟨hk, c, hkc, hq⟩
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_sub_div _ _ hk0 hc0, div_eq_div_iff hn0 (mul_ne_zero hk0 hc0)] at hq
    have hz : k * c + k * n = c * n := by
      have h1 : ((k * c + k * n : ℕ) : ℚ) = ((c * n : ℕ) : ℚ) := by
        push_cast
        linear_combination hq
      exact_mod_cast h1
    have hkn : k < n := by
      by_contra hcon
      have h2 : n ≤ k := by omega
      have h3 : c * n ≤ c * k := Nat.mul_le_mul_left c h2
      have h4 : 0 < k * n := Nat.mul_pos hk (by omega)
      have h5 : k * c = c * k := Nat.mul_comm k c
      omega
    refine ⟨hk, hkn, ⟨-(c : ℤ), ?_⟩⟩
    have hzz : (k : ℤ) * c + k * n = c * n := by exact_mod_cast hz
    linear_combination hzz
  · rintro ⟨hk, hkn, hd⟩
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd' : ((n - k : ℕ) : ℤ) ∣ ((k * n : ℕ) : ℤ) := by
      have e : ((n - k : ℕ) : ℤ) = -((k : ℤ) - n) := by
        push_cast [Nat.cast_sub hkn.le]
        ring
      rw [e]
      push_cast
      exact (neg_dvd).mpr hd
    obtain ⟨c, hc⟩ := Int.natCast_dvd_natCast.mp hd'
    have hkc : k < c := by
      by_contra hcon
      have h2 : c ≤ k := by omega
      have h3 : (n - k) * c ≤ (n - k) * k := Nat.mul_le_mul_left _ h2
      have h4 : (n - k) * k < n * k := mul_lt_mul_of_pos_right (by omega) hk
      have h5 : n * k = k * n := Nat.mul_comm n k
      omega
    have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨hk, c, hkc, ?_⟩
    rw [div_sub_div _ _ hk0 hc0, div_eq_div_iff hn0 (mul_ne_zero hk0 hc0)]
    have hq : (k : ℚ) * n = ((n : ℚ) - k) * c := by
      have h6 := congrArg (fun x : ℕ => (x : ℚ)) hc
      push_cast [Nat.cast_sub hkn.le] at h6
      exact h6
    linear_combination hq

end OMA.A146564

theorem OMA.solution : type_of% @OMA.S_oeis_a146564.main := by
  intro n hn
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hB : {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c}
      = {k : ℕ | 0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} := by
    ext k
    exact OMA.A146564.mem_B_iff n k hn
  have hS : {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n}
      = (fun d => n + d) '' ((n ^ 2).divisors : Set ℕ)
        ∪ {k : ℕ | 0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]
    constructor
    · rintro ⟨hk, hkn, hd⟩
      rcases lt_or_gt_of_ne hkn with h | h
      · right
        exact ⟨hk, h, hd⟩
      · left
        refine ⟨k - n, ⟨?_, hn2⟩, by omega⟩
        have e : ((k : ℤ) - n) ∣ (n : ℤ) ^ 2 := by
          have h1 : (k : ℤ) * n = ((k : ℤ) - n) * n + (n : ℤ) ^ 2 := by ring
          rw [h1] at hd
          exact (dvd_add_right (dvd_mul_right _ _)).mp hd
        have e2 : ((k - n : ℕ) : ℤ) = (k : ℤ) - n := by
          push_cast [Nat.cast_sub h.le]
          ring
        rw [← e2] at e
        exact_mod_cast e
    · rintro (⟨d, ⟨hd, _⟩, rfl⟩ | ⟨hk, hkn, hd⟩)
      · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn2)
        refine ⟨by omega, by omega, ?_⟩
        have e : (((n + d : ℕ) : ℤ) - n) = (d : ℤ) := by
          push_cast
          ring
        rw [e]
        have h1 : ((n + d : ℕ) : ℤ) * n = (d : ℤ) * n + (n : ℤ) ^ 2 := by
          push_cast
          ring
        rw [h1]
        exact dvd_add (dvd_mul_right _ _) (by exact_mod_cast hd)
      · exact ⟨hk, by omega, hd⟩
  have hdisj : Disjoint ((fun d => n + d) '' ((n ^ 2).divisors : Set ℕ))
      {k : ℕ | 0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} := by
    rw [Set.disjoint_left]
    rintro k ⟨d, _, hdk⟩ ⟨_, hlt, _⟩
    have hdk' : n + d = k := hdk
    omega
  have hf1 : ((fun d => n + d) '' ((n ^ 2).divisors : Set ℕ)).Finite :=
    (Finset.finite_toSet _).image _
  have hf2 : {k : ℕ | 0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n}.Finite :=
    (Set.finite_lt_nat n).subset (fun k hk => hk.2.1)
  have hinj : Function.Injective (fun d : ℕ => n + d) := fun x y h => by
    have h' : n + x = n + y := h
    omega
  have key : Set.ncard {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n}
      = (n ^ 2).divisors.card
        + Set.ncard {k : ℕ | 0 < k ∧ k < n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} := by
    rw [hS, Set.ncard_union_eq hdisj hf1 hf2, Set.ncard_image_of_injective _ hinj,
      Set.ncard_coe_finset]
  show Set.ncard {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n}
    = (n ^ 2).divisors.card
      + Set.ncard {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c}
  rw [hB]
  exact key
