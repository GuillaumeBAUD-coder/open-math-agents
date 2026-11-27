import OMAStatements.S_oeis_a207262
import Mathlib

-- Problem: oeis-a207262
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P207262
open OMA.S_oeis_a207262

lemma odd_div (o : ℕ) (ho : Odd o) : (Nat.divisors (2 * o)).filter Odd = Nat.divisors o := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, by rintro rfl; simp at ho⟩
    have hc : Nat.Coprime d 2 := Nat.Coprime.symm ((Nat.coprime_two_left).mpr h3)
    exact hc.dvd_of_dvd_mul_left h1
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Dvd.dvd.mul_left h1 2, by omega⟩, Odd.of_dvd_nat ho h1⟩

lemma sum_split (o k : ℕ) (ho : Odd o) :
    ∑ d ∈ Nat.divisors (2 * o), d ^ k = (1 + 2 ^ k) * ∑ d ∈ Nat.divisors o, d ^ k := by
  have hc : Nat.Coprime 2 o := (Nat.coprime_two_left).mpr ho
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := k)).map_mul_of_coprime hc
  simp only [ArithmeticFunction.sigma_apply] at h
  rw [h, Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num)]
  simp [add_comm]

theorem sol : type_of% @OMA.S_oeis_a207262.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : 4 * (m + 1) - 2 = 2 * (2 * m + 1) := by omega
  have ho : Odd (2 * m + 1) := ⟨m, rfl⟩
  unfold a
  rw [e, odd_div _ ho, sum_split _ _ ho]
  have hpos : 0 < ∑ d ∈ Nat.divisors (2 * m + 1), d ^ (2 * (2 * m + 1)) := by
    apply Finset.sum_pos (fun i hi => by
      have := Nat.pos_of_mem_divisors hi; positivity) ⟨1, by simp⟩
  have hq : ((∑ d ∈ Nat.divisors (2 * m + 1), d ^ (2 * (2 * m + 1)) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [Nat.cast_mul, mul_div_assoc, div_self hq, mul_one]
  push_cast
  ring

end OMA.P207262

theorem OMA.solution : type_of% @OMA.S_oeis_a207262.main := OMA.P207262.sol
