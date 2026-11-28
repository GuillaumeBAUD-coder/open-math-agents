import OMAStatements.S_oeis_a067745

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write 3n-2 = 2^v * o with o odd. A common divisor of o and n divides 2 (so is 1),
-- and a common divisor of o and 2n-1 divides 2(3n-2)-3(2n-1) = -1; so o is coprime to
-- the denominator D = n^(2n-1) (2n-1) 4^(n-1). Also 2^v <= 3n-2 <= 4^(n-1) gives 2^v | 4^(n-1) | D.
-- Hence the fraction equals o / (D / 2^v) in lowest terms and its numerator is o.

namespace OMA.A067745Proof

open OMA.S_oeis_a067745

lemma cop_n (n o : ℕ) (hn : 1 ≤ n) (ho : o ∣ 3 * n - 2) (hodd : Odd o) : Nat.Coprime o n := by
  set g := Nat.gcd o n with hg
  have hg1 : g ∣ 3 * n - 2 := (Nat.gcd_dvd_left o n).trans ho
  have hg2 : g ∣ 3 * n := Dvd.dvd.mul_left (Nat.gcd_dvd_right o n) 3
  have h2 : g ∣ 2 := by
    have := Nat.dvd_sub hg2 hg1
    rwa [show 3 * n - (3 * n - 2) = 2 by omega] at this
  have hgo : Odd g := Odd.of_dvd_nat hodd (Nat.gcd_dvd_left o n)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact h
  · rw [h] at hgo; exact absurd hgo (by decide)

lemma cop_m (n o : ℕ) (hn : 1 ≤ n) (ho : o ∣ 3 * n - 2) : Nat.Coprime o (2 * n - 1) := by
  set g := Nat.gcd o (2 * n - 1)
  have hg1 : g ∣ 2 * (3 * n - 2) := Dvd.dvd.mul_left ((Nat.gcd_dvd_left _ _).trans ho) 2
  have hg2 : g ∣ 3 * (2 * n - 1) := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3
  have := Nat.dvd_sub hg2 hg1
  rwa [show 3 * (2 * n - 1) - 2 * (3 * n - 2) = 1 by omega, Nat.dvd_one] at this

lemma cop_D (n o : ℕ) (hn : 1 ≤ n) (ho : o ∣ 3 * n - 2) (hodd : Odd o) :
    Nat.Coprime o (n ^ (2 * n - 1) * (2 * n - 1) * 4 ^ (n - 1)) := by
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ (cop_m n o hn ho)) ?_
  · exact Nat.Coprime.pow_right _ (cop_n n o hn ho hodd)
  · have : Nat.Coprime o 4 := by
      have h2 : Nat.Coprime o 2 := Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
          (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hodd))
      simpa using Nat.Coprime.pow_right 2 h2
    exact Nat.Coprime.pow_right _ this

lemma two_pow_dvd (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (3 * n - 2).factorization 2 ∣ 4 ^ (n - 1) := by
  have h4k : ∀ k : ℕ, 3 * (k + 1) - 2 ≤ 4 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; omega
  have h4 : 3 * n - 2 ≤ 4 ^ (n - 1) := by
    have := h4k (n - 1)
    rwa [show n - 1 + 1 = n by omega] at this
  have hle : 2 ^ (3 * n - 2).factorization 2 ≤ 3 * n - 2 :=
    Nat.le_of_dvd (by omega) (Nat.ordProj_dvd _ _)
  rw [show (4 : ℕ) ^ (n - 1) = 2 ^ (2 * (n - 1)) by rw [pow_mul]; norm_num]
  apply Nat.pow_dvd_pow
  by_contra hc
  push Not at hc
  have : 2 ^ (2 * (n - 1) + 1) ≤ 2 ^ (3 * n - 2).factorization 2 := Nat.pow_le_pow_right (by norm_num) hc
  rw [pow_succ, pow_mul] at this
  norm_num at this
  omega

end OMA.A067745Proof

open OMA.S_oeis_a067745 OMA.A067745Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a067745.main := by
  intro n hn
  set m := 3 * n - 2 with hm
  set v := m.factorization 2
  set o := m / 2 ^ v with ho_def
  set D := n ^ (2 * n - 1) * (2 * n - 1) * 4 ^ (n - 1) with hD
  have hm0 : m ≠ 0 := by omega
  have hvm : 2 ^ v ∣ m := Nat.ordProj_dvd _ _
  have hmo : m = 2 ^ v * o := (Nat.mul_div_cancel' hvm).symm
  have hodd : Odd o := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hm0
  have ho_dvd : o ∣ 3 * n - 2 := Nat.div_dvd_of_dvd hvm
  have hvD : 2 ^ v ∣ D := (two_pow_dvd n hn).trans (Dvd.intro_left _ rfl)
  have hDpos : 0 < D := by
    rw [hD]; apply Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by positivity)
  set E := D / 2 ^ v with hE
  have hDE : D = 2 ^ v * E := (Nat.mul_div_cancel' hvD).symm
  have hEpos : 0 < E := Nat.div_pos (Nat.le_of_dvd hDpos hvD) (by positivity)
  have hcop : Nat.Coprime o E :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hDE.symm) (cop_D n o hn ho_dvd hodd)
  have hq : (3 * (n : ℚ) - 2) / ((n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1))
      = ((o : ℤ) : ℚ) / ((E : ℤ) : ℚ) := by
    have e1 : (3 * (n : ℚ) - 2) = (m : ℚ) := by rw [hm]; push_cast [Nat.cast_sub (show 2 ≤ 3 * n by omega)]; ring
    have e2 : (n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1) = (D : ℚ) := by
      rw [hD]; push_cast [Nat.cast_sub (show 1 ≤ 2 * n by omega)]; ring
    rw [e1, e2, hmo, hDE]
    push_cast
    have : (2 : ℚ) ^ v ≠ 0 := by positivity
    rw [mul_div_mul_left _ _ this]
  unfold a
  rw [hq, Rat.num_div_eq_of_coprime (by exact_mod_cast hEpos)]
  · rfl
  · simpa using hcop
