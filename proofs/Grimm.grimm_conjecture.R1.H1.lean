import OMAReductions.R_Grimm_grimm_conjecture_R1

-- Step Grimm.grimm_conjecture.R1.H1: hypothesis H1 of reduction Grimm.grimm_conjecture.R1
-- Credit: @Moti1125

namespace OMAGrimm

/-- A prime cannot divide two consecutive numbers. -/
lemma not_dvd_succ {p a : ℕ} (hp : p.Prime) (ha : p ∣ a) (ha1 : p ∣ a + 1) : False := by
  have h1 : p ∣ 1 := (Nat.dvd_add_right ha).mp ha1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- `n` and `n + 2` have distinct prime divisors when both are composite. -/
lemma two_apart (n : ℕ) (hn : n.Composite) (hn2 : (n + 2).Composite) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∣ n ∧ q ∣ n + 2 ∧ p ≠ q := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · -- `n = 2 m`: one of `m`, `m + 1` is odd and greater than one.
    rcases Nat.even_or_odd m with ⟨l, hl⟩ | ⟨l, hl⟩
    · have hq : (m + 1).minFac.Prime := Nat.minFac_prime (by omega)
      refine ⟨2, (m + 1).minFac, Nat.prime_two, hq, ⟨m, by omega⟩,
        (Nat.minFac_dvd _).trans ⟨2, by omega⟩, ?_⟩
      intro h
      have h2 : 2 ∣ m + 1 := h ▸ Nat.minFac_dvd (m + 1)
      omega
    · have hm1 : m ≠ 1 := by
        rintro rfl
        exact hn.2 (by rw [hm]; exact Nat.prime_two)
      have hp : m.minFac.Prime := Nat.minFac_prime hm1
      refine ⟨m.minFac, 2, hp, Nat.prime_two, (Nat.minFac_dvd _).trans ⟨2, by omega⟩,
        ⟨m + 1, by omega⟩, ?_⟩
      intro h
      have h2 : 2 ∣ m := h ▸ Nat.minFac_dvd m
      omega
  · -- `n` odd: a common prime divisor of `n` and `n + 2` divides `2`, so it is `2`.
    have hp : n.minFac.Prime := Nat.minFac_prime (by have := hn.1; omega)
    have hq : (n + 2).minFac.Prime := Nat.minFac_prime (by omega)
    refine ⟨n.minFac, (n + 2).minFac, hp, hq, Nat.minFac_dvd _, Nat.minFac_dvd _, ?_⟩
    intro h
    have hdn : (n + 2).minFac ∣ n := h ▸ Nat.minFac_dvd n
    have h2 : (n + 2).minFac ∣ 2 := (Nat.dvd_add_right hdn).mp (Nat.minFac_dvd _)
    have hle : (n + 2).minFac ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have heq : (n + 2).minFac = 2 := le_antisymm hle hq.two_le
    rw [heq] at hdn
    obtain ⟨c, hc⟩ := hodd
    omega

end OMAGrimm

open OMAGrimm

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1.H1 := by
  intro n k hn hk hk3 h
  interval_cases k
  · -- One composite: any prime factor.
    have hp : n.minFac.Prime := Nat.minFac_prime (by have := (h 0).1; simp at this; omega)
    refine ⟨⟨fun _ => n.minFac, fun i j _ => Subsingleton.elim i j⟩, ?_⟩
    intro i
    fin_cases i
    simpa using ⟨hp, Nat.minFac_dvd n⟩
  · -- Two composites: consecutive numbers share no prime.
    have h0 := (h 0).1
    have hp : n.minFac.Prime := Nat.minFac_prime (by simp at h0; omega)
    have hq : (n + 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hne : n.minFac ≠ (n + 1).minFac := by
      intro he
      exact not_dvd_succ hq (he ▸ Nat.minFac_dvd n) (Nat.minFac_dvd (n + 1))
    refine ⟨⟨![n.minFac, (n + 1).minFac], ?_⟩, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact hne hij
      · exact hne hij.symm
    · intro i
      fin_cases i
      · simpa using ⟨hp, Nat.minFac_dvd n⟩
      · simpa using ⟨hq, Nat.minFac_dvd (n + 1)⟩
  · -- Three composites: the middle prime is new, and `n`, `n + 2` get distinct primes.
    have hc0 : n.Composite := by simpa using h 0
    have hc2 : (n + 2).Composite := by simpa using h 2
    obtain ⟨p, q, hp, hq, hpn, hqn, hpq⟩ := two_apart n hc0 hc2
    have hr : (n + 1).minFac.Prime := Nat.minFac_prime (by have := hc0.1; omega)
    have hpr : p ≠ (n + 1).minFac := by
      intro he
      exact not_dvd_succ hr (he ▸ hpn) (Nat.minFac_dvd (n + 1))
    have hqr : q ≠ (n + 1).minFac := by
      intro he
      exact not_dvd_succ hr (Nat.minFac_dvd (n + 1)) (he ▸ hqn)
    refine ⟨⟨![p, (n + 1).minFac, q], ?_⟩, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact hpr hij
      · exact hpq hij
      · exact hpr hij.symm
      · exact hqr hij.symm
      · exact hpq hij.symm
      · exact hqr hij
    · intro i
      fin_cases i
      · simpa using ⟨hp, hpn⟩
      · simpa using ⟨hr, Nat.minFac_dvd (n + 1)⟩
      · simpa using ⟨hq, hqn⟩
