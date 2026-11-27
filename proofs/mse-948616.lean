import OMAStatements.S_mse_948616
import Mathlib

-- Problem: mse-948616, a variation of Fermat's little theorem: a^(n-d) = a (mod n) for all a.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- If m = d + 1 is squarefree, take a prime p > m with p = 1 modulo the product of the q - 1
-- over the primes q dividing m. Then n = p m is squarefree and n - d = (p - 1) m + 1, and for
-- every prime r dividing n the number r - 1 divides (p - 1) m, so Fermat's little theorem gives
-- a^(n-d) = a modulo r, hence modulo n. There are infinitely many such p. If m is not
-- squarefree, say q^2 divides m, and n is a proper multiple of m, then n - d >= 2 and a = q
-- gives q^2 | q^(n-d) - q, which is impossible.

namespace MSE948616

open OMA.S_mse_948616

lemma fermat (r : ℕ) (hr : r.Prime) (t : ℕ) (ht : (r - 1) ∣ t) (a : ℤ) :
    (r : ℤ) ∣ a ^ (t + 1) - a := by
  have hfact : Fact r.Prime := ⟨hr⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  by_cases ha : (a : ZMod r) = 0
  · rw [ha]
    simp
  · obtain ⟨c, rfl⟩ := ht
    rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow, one_mul, sub_self]

lemma sqfree_dvd (N : ℕ) (hN : Squarefree N) (x : ℤ)
    (h : ∀ r : ℕ, r.Prime → r ∣ N → (r : ℤ) ∣ x) : (N : ℤ) ∣ x := by
  have hprod : ((∏ r ∈ N.primeFactors, r : ℕ) : ℤ) ∣ x := by
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro r hr s hs hrs
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hr) (Nat.prime_of_mem_primeFactors hs)).mpr hrs)
    · intro r hr
      exact h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  rwa [Nat.prod_primeFactors_of_squarefree hN] at hprod

lemma part2 (d : ℕ) (hns : ¬ Squarefree (d + 1)) (n : ℕ) (hdn : d + 1 ∣ n)
    (hne : n ≠ d + 1) : ¬ Valid d n := by
  rintro ⟨hle, hval⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  obtain ⟨q, hq⟩ : ∃ q, ¬ (q.Prime → ¬ q * q ∣ d + 1) := not_forall.mp hns
  have hqp : q.Prime := by
    by_contra hc
    exact hq (fun h => absurd h hc)
  have hqq : q * q ∣ d + 1 := by
    by_contra hc
    exact hq (fun _ => hc)
  have hn2 : d + 2 ≤ n - d := by
    obtain ⟨c, rfl⟩ := hdn
    have hc : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hle
      · simp at hne
      · omega
    have h := Nat.mul_le_mul_left (d + 1) hc
    omega
  have h1 := hval (q : ℤ)
  have h2 : (n : ℤ) ∣ (q : ℤ) - (q : ℤ) ^ (n - d) := Int.modEq_iff_dvd.mp h1
  have h3 : ((q * q : ℕ) : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (hqq.trans hdn)
  have h4 : ((q * q : ℕ) : ℤ) ∣ (q : ℤ) ^ (n - d) := by
    obtain ⟨k, hk⟩ : ∃ k, n - d = 2 + k := ⟨n - d - 2, by omega⟩
    rw [hk, pow_add]
    exact Dvd.intro ((q : ℤ) ^ k) (by push_cast; ring)
  have h5 : ((q * q : ℕ) : ℤ) ∣ (q : ℤ) := by
    have h := dvd_add (h3.trans h2) h4
    simpa using h
  have h6 : q * q ∣ q := Int.natCast_dvd_natCast.mp h5
  have h7 := Nat.le_of_dvd hqp.pos h6
  nlinarith [hqp.two_le]

lemma part1 (d : ℕ) (hs : Squarefree (d + 1)) :
    {p : ℕ | p.Prime ∧ Valid d (p * (d + 1))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  have hK : (∏ q ∈ (d + 1).primeFactors, (q - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have h := (Nat.prime_of_mem_primeFactors hq).two_le
    omega
  obtain ⟨p, hp, hpN, hpK⟩ := Nat.exists_prime_gt_modEq_one (N + (d + 1)) hK
  refine ⟨p, ⟨hp, ?_⟩, by omega⟩
  unfold Valid
  refine ⟨Nat.le_mul_of_pos_left _ hp.pos, ?_⟩
  intro a
  have hexp : p * (d + 1) - d = (p - 1) * (d + 1) + 1 := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    have h : (p' + 1) * (d + 1) = p' * (d + 1) + (d + 1) := by ring
    simp only [Nat.add_sub_cancel]
    omega
  rw [hexp]
  apply Int.modEq_iff_dvd.mpr
  rw [← dvd_neg, neg_sub]
  have hpd : ¬ p ∣ d + 1 := fun h => by
    have h' := Nat.le_of_dvd (by omega) h
    omega
  have hsq : Squarefree (p * (d + 1)) := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpd, hp.squarefree, hs⟩
  apply sqfree_dvd _ hsq
  intro r hr hrd
  apply fermat r hr
  rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
  · have e : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
    rw [e]
    exact Dvd.intro _ rfl
  · have hrmem : r ∈ (d + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hr, h, by omega⟩
    have h1 : (r - 1) ∣ ∏ q ∈ (d + 1).primeFactors, (q - 1) :=
      Finset.dvd_prod_of_mem (fun q => q - 1) hrmem
    have h2 : (∏ q ∈ (d + 1).primeFactors, (q - 1)) ∣ p - 1 :=
      (Nat.modEq_iff_dvd' hp.one_lt.le).mp hpK.symm
    exact Dvd.dvd.mul_right (h1.trans h2) _

end MSE948616

theorem OMA.solution : type_of% @OMA.S_mse_948616.main := fun d =>
  ⟨MSE948616.part1 d, fun hns n hdn hne => MSE948616.part2 d hns n hdn hne⟩
