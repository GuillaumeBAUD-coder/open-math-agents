import OMAStatements.S_oeis_a395896
import Mathlib.Tactic

-- Problem: A395896: Number of k < m^2 such that both rad(k) and rad(k+1) divide m, where rad = A007947 and m = A019565(n).
-- Upstream: formal-conjectures statements/oeis-a395896.lean:0 (declaration OMA.S_oeis_a395896.main)
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open UniqueFactorizationMonoid

namespace OMA

/-- A product of odd numbers indexed by a finset is odd. -/
lemma odd_finsetProd {s : Finset ℕ} {f : ℕ → ℕ} (h : ∀ i ∈ s, Odd (f i)) :
    Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Odd.mul (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- For an even index the A019565 term is a product of odd primes: bit `0` of an even number is
unset, so the prime `2 = Nat.nth Nat.Prime 0` never occurs among the factors. -/
lemma odd_squarefreeTerm (n : ℕ) (hn : Even n) : Odd (S_oeis_a395896.squarefreeTerm n) := by
  unfold S_oeis_a395896.squarefreeTerm
  refine odd_finsetProd (fun i hi => ?_)
  have hi' : i ∈ n.bitIndices := List.mem_toFinset.mp hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    have h1 : n.testBit 0 = true := Nat.mem_bitIndices.mp hi'
    rw [Nat.testBit_zero] at h1
    simp [Nat.even_iff.mp hn] at h1
  have hp : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
  exact hp.odd_of_ne_two (by
    intro h2
    have h3 : Nat.nth Nat.Prime i = Nat.nth Nat.Prime 0 := by
      rw [h2, Nat.nth_prime_zero_eq_two]
    exact hi0 (Nat.nth_injective Nat.infinite_setOfPred_prime h3))

/-- If an odd number is a multiple of `radical k`, then `k` itself is odd. -/
lemma odd_of_radical_dvd {m k : ℕ} (hm : Odd m) (hk : k ≠ 0) (h : radical k ∣ m) : Odd k := by
  rw [← Nat.not_even_iff_odd]
  intro he
  have hk2 : 2 ∣ k := even_iff_two_dvd.mp he
  have h2r : 2 ∣ radical k := by
    rw [Nat.radical_eq_prod_primeFactors]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hk2, hk⟩)
  have h2m : 2 ∣ m := dvd_trans h2r h
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m)

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a395896.main := by
  intro n hn
  have hm : Odd (OMA.S_oeis_a395896.squarefreeTerm n) := OMA.odd_squarefreeTerm n hn
  simp only [OMA.S_oeis_a395896.a]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk1, _⟩ := hk
  have hoddk : Odd k := OMA.odd_of_radical_dvd hm (by omega) h1
  have hoddk1 : Odd (k + 1) := OMA.odd_of_radical_dvd hm (by omega) h2
  have heven : Even (k + 1) := by
    simpa using Odd.add_odd hoddk odd_one
  exact (Nat.not_even_iff_odd.mpr hoddk1) heven
