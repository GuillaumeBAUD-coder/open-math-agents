import OMAReductions.R_OeisA108569_conjecture_R2_H1_R1

-- For an odd prime p with phi(2p - 1) = p - 1, the number 2p - 1 has at least three distinct prime factors.
-- Original proof of an elementary fact. With m = 2p - 1 the equation is 2 phi(m) = m - 1; from
-- phi(m) * prod q = m * prod (q - 1) over the primes q dividing m this gives 2 * prod (q - 1) < prod q.
-- For r distinct odd numbers >= 3 the product of q / (q - 1) is at most (3/2)(5/4)...((2r+1)/(2r)), by
-- induction adding the largest element, and that is below 2 for r <= 2.
-- An elementary case of Lehmer's totient problem for the ratio 2, not progress on it.

namespace OMA.A108569

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

theorem few_primes (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hc : (p + p.totient).primeFactors.card ≤ 2) : p.totient ≠ (p + p.totient).totient := by
  intro heq
  rw [Nat.totient_prime hp] at heq hc
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨c, hcc⟩ := hodd
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = p + (p - 1) := ⟨_, rfl⟩
  rw [← hm] at heq hc
  have hm5 : 5 ≤ m := by omega
  have htot := Nat.totient_mul_prod_primeFactors m
  rw [← heq] at htot
  have hge : ∀ q ∈ m.primeFactors, 3 ≤ q ∧ q % 2 = 1 := by
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
  have hQ : 0 < ∏ q ∈ m.primeFactors, (q - 1) :=
    Finset.prod_pos fun q hq => by have := (hge q hq).1; omega
  have hkey : 2 * ∏ q ∈ m.primeFactors, (q - 1) < ∏ q ∈ m.primeFactors, q := by
    have h1 : m * (2 * ∏ q ∈ m.primeFactors, (q - 1)) = (m - 1) * ∏ q ∈ m.primeFactors, q := by
      have h2 : m - 1 = 2 * (p - 1) := by omega
      rw [h2]
      calc m * (2 * ∏ q ∈ m.primeFactors, (q - 1)) = 2 * (m * ∏ q ∈ m.primeFactors, (q - 1)) := by ring
        _ = 2 * ((p - 1) * ∏ q ∈ m.primeFactors, q) := by rw [htot]
        _ = _ := by ring
    have hP : 0 < ∏ q ∈ m.primeFactors, q :=
      Finset.prod_pos fun q hq => by have := (hge q hq).1; omega
    have h3 : (m - 1) * ∏ q ∈ m.primeFactors, q < m * ∏ q ∈ m.primeFactors, q :=
      Nat.mul_lt_mul_of_pos_right (by omega) hP
    rw [← h1] at h3
    exact Nat.lt_of_mul_lt_mul_left h3
  have hodd' := odd_prod_bound m.primeFactors hge
  have hfinal : 2 * (∏ j ∈ range m.primeFactors.card, (2 * j + 2)) <
      ∏ j ∈ range m.primeFactors.card, (2 * j + 3) := by
    have hA : 0 < ∏ j ∈ range m.primeFactors.card, (2 * j + 2) :=
      Finset.prod_pos fun j _ => by omega
    have h3 : (∏ q ∈ m.primeFactors, (q - 1)) * (2 * ∏ j ∈ range m.primeFactors.card, (2 * j + 2)) <
        (∏ q ∈ m.primeFactors, (q - 1)) * ∏ j ∈ range m.primeFactors.card, (2 * j + 3) := by
      calc (∏ q ∈ m.primeFactors, (q - 1)) * (2 * ∏ j ∈ range m.primeFactors.card, (2 * j + 2))
          = (∏ j ∈ range m.primeFactors.card, (2 * j + 2)) * (2 * ∏ q ∈ m.primeFactors, (q - 1)) := by
            ring
        _ < (∏ j ∈ range m.primeFactors.card, (2 * j + 2)) * ∏ q ∈ m.primeFactors, q :=
            Nat.mul_lt_mul_of_pos_left hkey hA
        _ ≤ (∏ j ∈ range m.primeFactors.card, (2 * j + 3)) * ∏ q ∈ m.primeFactors, (q - 1) := hodd'
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_left h3
  generalize m.primeFactors.card = r at hc hfinal
  interval_cases r <;> simp [Finset.prod_range_succ] at hfinal

end OMA.A108569

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R2_H1_R1.H1 := by
  intro p hp hodd hc
  exact OMA.A108569.few_primes p hp hodd hc
