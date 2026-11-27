import OMAReductions.R_OeisA135508_conjecture_R1

namespace OMA.R_OeisA135508_conjecture_R1_H2_R1

open OeisA135508
open OMA.R_OeisA135508_conjecture_R1

/-- A finite table of primes r where the multiplier r+2 introduces q before its square. -/
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 1000000 →
    ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r + 2

/-- For the remaining candidates, any prime factor of p-2 and any timely witness suffice. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p % 3 = 1 → ¬ (p - 2).Prime →
    1000000 < (p - 2).minFac →
    ∃ q : ℕ, q.Prime ∧ q ∣ p - 2 ∧
      ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < p - 2 ∧ r % 3 = 2 ∧ q ∣ r + 2

lemma three_persists : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))

lemma divides_later {q m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hd : q ∣ x m) :
    q ∣ x n := by
  induction n, hmn using Nat.le_induction with
  | base => exact hd
  | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))

lemma witness_divides_later {q r n : ℕ} (hr : r.Prime) (h5 : 5 < r)
    (hmod : r % 3 = 2) (hdiv : q ∣ r + 2) (hrn : r ≤ n) : q ∣ x n := by
  have ha := prime_mod_three_two three_persists hr hmod (by omega)
  have hxr := x_succ_mul_a (r - 1) (by omega)
  rw [show r - 1 + 1 = r by omega, ha] at hxr
  apply divides_later (m := r) (by omega) hrn
  rw [hxr]
  exact dvd_mul_of_dvd_right hdiv _

theorem main : H1 → H2 → OMA.R_OeisA135508_conjecture_R1.H2 := by
  intro hfinite hlarge p hp hp5 hmod hcomposite hcop
  have hp7 : 7 ≤ p := by omega
  let q := (p - 2).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqm : q ∣ p - 2 := Nat.minFac_dvd _
  have exclude {s : ℕ} (hs : s.Prime) (hsm : s ∣ p - 2) (hsx : s ∣ x (p - 3)) : False := by
    have hg := Nat.dvd_gcd hsx hsm
    rw [hcop.gcd_eq_one] at hg
    exact hs.not_dvd_one hg
  by_cases hcut : q ≤ 1000000
  · apply exclude hq hqm
    by_cases hq5 : 5 ≤ q
    · obtain ⟨r, hr, h5, hrsq, hrmod, hd⟩ := hfinite q hq hq5 hcut
      have hsq : q^2 ≤ p - 2 := Nat.minFac_sq_le_self (by omega) hcomposite
      exact witness_divides_later hr h5 hrmod hd (by omega)
    · have hq2 := hq.two_le
      have hq4 : q ≠ 4 := fun eq => (by decide : ¬ Nat.Prime 4) (eq ▸ hq)
      have h23 : q = 2 ∨ q = 3 := by omega
      apply divides_later (m := 4) (by decide) (by omega)
      rcases h23 with h | h <;> rw [h] <;> decide
  · obtain ⟨s, hs, hsm, r, hr, h5, htime, hrmod, hd⟩ :=
      hlarge p hp hp5 hmod hcomposite (lt_of_not_ge hcut)
    exact exclude hs hsm (witness_divides_later hr h5 hrmod hd (by omega))

end OMA.R_OeisA135508_conjecture_R1_H2_R1
