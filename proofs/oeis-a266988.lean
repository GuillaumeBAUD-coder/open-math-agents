import OMAStatements.S_oeis_a266988

-- Problem: A266988: The indices of primes for which the average of the primitive roots is < p/2.
-- Upstream: formal-conjectures statements/oeis-a266988.lean:0 (declaration OMA.S_oeis_a266988.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: suppose p is prime and not 3 mod 4, so p = 2 or p = 4t + 1. Then g -> p - g maps the
-- primitive roots onto themselves: for p = 2 it fixes g = 1; for p = 4t + 1 and x of order 4t,
-- y = x^(2t) has y^2 = 1 and y <> 1, so y = -1, hence -x = x^(2t+1) and x = (-x)^(2t+1), and
-- -x has the same order as x. So the sum S of the primitive roots equals the sum of p - g,
-- 2S = p * card, and card > 0 (the units of ZMod p are cyclic). Hence the average is p/2.

open OMA.S_oeis_a266988 in
theorem OMA.solution : type_of% @OMA.S_oeis_a266988.main := by
  intro p hp hlt
  by_contra h3
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcase : p = 2 ∨ p % 4 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      omega
  -- for p = 4t + 1, negation preserves the order p - 1
  have hneg : p % 4 = 1 → ∀ x : ZMod p, orderOf x = p - 1 → orderOf (-x) = p - 1 := by
    intro h1 x hx
    obtain ⟨t, ht⟩ : ∃ t, p - 1 = 4 * t := ⟨(p - 1) / 4, by omega⟩
    have ht0 : 0 < t := by omega
    have hx4 : x ^ (4 * t) = 1 := by
      rw [← ht, ← hx]
      exact pow_orderOf_eq_one x
    have hy : x ^ (2 * t) = -1 := by
      have hsq : x ^ (2 * t) * x ^ (2 * t) = 1 := by
        rw [← pow_add, show 2 * t + 2 * t = 4 * t by ring]
        exact hx4
      rcases mul_self_eq_one_iff.mp hsq with h1' | h1'
      · exfalso
        have hd : orderOf x ∣ 2 * t := orderOf_dvd_of_pow_eq_one h1'
        rw [hx, ht] at hd
        have hle := Nat.le_of_dvd (by omega) hd
        omega
      · exact h1'
    have hnx : -x = x ^ (2 * t + 1) := by
      rw [pow_succ, hy]
      ring
    have hxx : x = (-x) ^ (2 * t + 1) := by
      rw [hnx, ← pow_mul, show (2 * t + 1) * (2 * t + 1) = 4 * t * (t + 1) + 1 by ring,
        pow_succ, pow_mul, hx4, one_pow, one_mul]
    apply Nat.dvd_antisymm
    · rw [← hx, hnx]
      exact orderOf_pow_dvd _
    · have h2 : orderOf ((-x) ^ (2 * t + 1)) ∣ orderOf (-x) := orderOf_pow_dvd _
      rw [← hxx, hx] at h2
      exact h2
  -- g -> p - g maps primitive roots to primitive roots
  have hsym : ∀ g ∈ primRoots p, p - g ∈ primRoots p := by
    intro g hg
    unfold primRoots at hg ⊢
    simp only [Finset.mem_filter, Finset.mem_Icc] at hg ⊢
    obtain ⟨⟨hg1, hg2⟩, hgo⟩ := hg
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rcases hcase with h2 | h1
    · have hpg : p - g = g := by omega
      rw [hpg]
      exact hgo
    · have hcast : ((p - g : ℕ) : ZMod p) = -((g : ℕ) : ZMod p) := by
        rw [Nat.cast_sub (by omega : g ≤ p), ZMod.natCast_self, zero_sub]
      rw [hcast]
      exact hneg h1 _ hgo
  -- there is a primitive root
  have hne : (primRoots p).Nonempty := by
    have := ZMod.isCyclic_units_prime hp
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hou : orderOf (u : ZMod p) = p - 1 := by
      rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
        ZMod.card_units p]
    refine ⟨(u : ZMod p).val, ?_⟩
    unfold primRoots
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra h0
      have h0' : (u : ZMod p).val = 0 := by omega
      rw [ZMod.val_eq_zero] at h0'
      exact u.ne_zero h0'
    · have hlt' := ZMod.val_lt (u : ZMod p)
      omega
    · rw [ZMod.natCast_zmod_val]
      exact hou
  have hS : ∀ g ∈ primRoots p, g ≤ p := by
    intro g hg
    unfold primRoots at hg
    simp only [Finset.mem_filter, Finset.mem_Icc] at hg
    obtain ⟨⟨_, hg2⟩, _⟩ := hg
    omega
  have hsum : ∑ g ∈ primRoots p, (g : ℚ) = ∑ g ∈ primRoots p, ((p : ℚ) - (g : ℚ)) := by
    refine Finset.sum_nbij' (fun g => p - g) (fun g => p - g) hsym hsym ?_ ?_ ?_
    · intro g hg
      have hgp := hS g hg
      show p - (p - g) = g
      omega
    · intro g hg
      have hgp := hS g hg
      show p - (p - g) = g
      omega
    · intro g hg
      have hgp := hS g hg
      show (g : ℚ) = (p : ℚ) - ((p - g : ℕ) : ℚ)
      rw [Nat.cast_sub hgp]
      ring
  have hsub : ∑ g ∈ primRoots p, ((p : ℚ) - (g : ℚ)) =
      ((primRoots p).card : ℚ) * (p : ℚ) - ∑ g ∈ primRoots p, (g : ℚ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℚ) < ((primRoots p).card : ℚ) := by
    exact_mod_cast hne.card_pos
  have havg : avg p = (p : ℚ) / 2 := by
    unfold avg
    rw [div_eq_iff hcard.ne']
    linear_combination (hsum + hsub) / 2
  rw [havg] at hlt
  exact lt_irrefl _ hlt
