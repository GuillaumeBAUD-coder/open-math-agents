import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- A composite n with phi(n) dividing n - 1 has at least three distinct prime factors.
-- Original Lean proof of a classical fact (Lehmer 1932 has at least seven, by a longer analysis). Such an n is
-- odd (phi(n) is even for n > 2), and (n - 1) / phi(n) is at least 2 because phi(n) = n - 1 only for primes, so
-- 2 phi(n) < n. From phi(n) * prod p = n * prod (p - 1) over the primes dividing n this gives
-- 2 * prod (p - 1) < prod p. For r distinct odd numbers >= 3 the product of p / (p - 1) is at most
-- (3/2)(5/4)...((2r+1)/(2r)), by induction adding the largest element, and that is below 2 for r <= 2.
-- A classical first step, not progress on Lehmer's totient problem.

namespace OMA.Lehmer2

open Finset

/-- For distinct odd numbers `≥ 3`: `∏ p / (p - 1) ≤ ∏_{j < r} (2j + 3) / (2j + 2)`. -/
lemma odd_prod_bound (s : Finset ℕ) :
    (∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1) →
    (∏ j ∈ range s.card, (2 * j + 2)) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (2 * j + 3)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, (x - 3) / 2 ∈ range ((a - 3) / 2) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x - 3) / 2) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ (a - 3) / 2 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => (x - 3) / 2) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (2 * s.card + 2) * a ≤ (2 * s.card + 3) * (a - 1) := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : 2 * s.card + 2 ≤ c := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (2 * j + 2)) * (2 * s.card + 2) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (2 * j + 2)) * ∏ p ∈ s, p) * ((2 * s.card + 2) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (2 * j + 3)) * ∏ p ∈ s, (p - 1)) * ((2 * s.card + 3) * (a - 1)) :=
          Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (2 * j + 3)) * (2 * s.card + 3) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by
          ring

theorem few_primes (n : ℕ) (hn : 1 < n) (hnp : ¬ n.Prime) (hc : n.primeFactors.card ≤ 2) :
    ¬ n.totient ∣ n - 1 := by
  intro hdvd
  have hn2 : n ≠ 2 := fun h => hnp (h ▸ Nat.prime_two)
  have hodd : n % 2 = 1 := by
    by_contra hne
    have heven : 2 ∣ n := by omega
    have h1 : 2 ∣ n.totient := (Nat.totient_even (by omega)).two_dvd
    have h2 : 2 ∣ n - 1 := h1.trans hdvd
    omega
  have hlt : 2 * n.totient < n := by
    obtain ⟨k, hk⟩ := hdvd
    have hne : n.totient ≠ n - 1 := fun h => hnp ((Nat.totient_eq_iff_prime (by omega)).mp h)
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · omega
      · exact h
    have h3 : n.totient * 2 ≤ n.totient * k := Nat.mul_le_mul_left _ hk2
    omega
  have htot := Nat.totient_mul_prod_primeFactors n
  have hge : ∀ q ∈ n.primeFactors, 3 ≤ q ∧ q % 2 = 1 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hqo : q % 2 = 1 := by
      obtain ⟨d, hd⟩ := hqd
      by_contra hne
      have hqe : q % 2 = 0 := by omega
      have : (q * d) % 2 = 0 := by rw [Nat.mul_mod, hqe]; simp
      omega
    have h2 := hqp.two_le
    exact ⟨by omega, hqo⟩
  have hP : 0 < ∏ q ∈ n.primeFactors, q :=
    Finset.prod_pos fun q hq => by have := (hge q hq).1; omega
  have hkey : 2 * ∏ q ∈ n.primeFactors, (q - 1) < ∏ q ∈ n.primeFactors, q := by
    have h1 : n * (2 * ∏ q ∈ n.primeFactors, (q - 1)) = (2 * n.totient) * ∏ q ∈ n.primeFactors, q := by
      calc n * (2 * ∏ q ∈ n.primeFactors, (q - 1)) = 2 * (n * ∏ q ∈ n.primeFactors, (q - 1)) := by ring
        _ = 2 * (n.totient * ∏ q ∈ n.primeFactors, q) := by rw [htot]
        _ = _ := by ring
    have h3 : (2 * n.totient) * ∏ q ∈ n.primeFactors, q < n * ∏ q ∈ n.primeFactors, q :=
      Nat.mul_lt_mul_of_pos_right hlt hP
    rw [← h1] at h3
    exact Nat.lt_of_mul_lt_mul_left h3
  have hodd' := odd_prod_bound n.primeFactors hge
  have hfinal : 2 * (∏ j ∈ range n.primeFactors.card, (2 * j + 2)) <
      ∏ j ∈ range n.primeFactors.card, (2 * j + 3) := by
    have hA : 0 < ∏ j ∈ range n.primeFactors.card, (2 * j + 2) :=
      Finset.prod_pos fun j _ => by omega
    have h3 : (∏ q ∈ n.primeFactors, (q - 1)) * (2 * ∏ j ∈ range n.primeFactors.card, (2 * j + 2)) <
        (∏ q ∈ n.primeFactors, (q - 1)) * ∏ j ∈ range n.primeFactors.card, (2 * j + 3) := by
      calc (∏ q ∈ n.primeFactors, (q - 1)) * (2 * ∏ j ∈ range n.primeFactors.card, (2 * j + 2))
          = (∏ j ∈ range n.primeFactors.card, (2 * j + 2)) * (2 * ∏ q ∈ n.primeFactors, (q - 1)) := by
            ring
        _ < (∏ j ∈ range n.primeFactors.card, (2 * j + 2)) * ∏ q ∈ n.primeFactors, q :=
            Nat.mul_lt_mul_of_pos_left hkey hA
        _ ≤ (∏ j ∈ range n.primeFactors.card, (2 * j + 3)) * ∏ q ∈ n.primeFactors, (q - 1) := hodd'
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_left h3
  generalize n.primeFactors.card = r at hc hfinal
  interval_cases r <;> simp [Finset.prod_range_succ] at hfinal

end OMA.Lehmer2

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H2 := by
  intro n hn hnp hc
  exact OMA.Lehmer2.few_primes n hn hnp hc
