import OMAReductions.R_OeisA69004_conjecture2_variants_without_upper_bound_R1
import Mathlib

/-! A primitive odd sum of two squares has no prime divisor congruent to three modulo four. -/

open Finset

namespace A69004PrimeTest

private theorem parity_test (n s : ℕ) : 2 ∣ n^2+s^2 ↔ n%2 = s%2 := by
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  have hs := Nat.mod_lt s (by decide : 0 < 2)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod n, Nat.pow_mod s]
  interval_cases n%2 <;> interval_cases s%2 <;> decide

private theorem residue_one {n s p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (hc : n.Coprime s) (hpd : p ∣ n^2+s^2) : p%4 = 1 := by
  have hsd : ¬ p ∣ s := by
    intro hs
    have hn : p ∣ n := hp.dvd_of_dvd_pow (by
      have h := Nat.dvd_sub hpd (hs.trans (dvd_pow_self s (by decide : 2 ≠ 0)))
      simpa using h)
    have hd := Nat.dvd_gcd hn hs
    rw [hc.gcd_eq_one] at hd
    exact hp.not_dvd_one hd
  let : Fact p.Prime := ⟨hp⟩
  have hs0 : (s : ZMod p) ≠ 0 := fun h => hsd ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hzero : (n:ZMod p)^2 + (s:ZMod p)^2 = 0 := by
    simpa only [Nat.cast_add,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  have hsq : ((n : ZMod p)/(s : ZMod p))^2 = -1 := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hs0)]
    linear_combination hzero
  have hneq3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp₂)
  omega

private theorem prime_iff_test {n s : ℕ} (hs : s ∈ Ico 1 n) :
    (n^2+s^2).Prime ↔ n%2 ≠ s%2 ∧ n.Coprime s ∧
      ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2 := by
  let N := n^2+s^2
  have hs1 := (mem_Ico.mp hs).1
  have hsn := (mem_Ico.mp hs).2
  have hN2 : 2 < N := by dsimp [N]; nlinarith
  change N.Prime ↔ _
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_⟩
    · intro he
      have hdiv : 2 ∣ N := (parity_test n s).mpr he
      have h := (Nat.dvd_prime_two_le hp (by decide)).mp hdiv
      omega
    · have hdiv : n.gcd s ∣ N := dvd_add
        ((Nat.gcd_dvd_left n s).trans (dvd_pow_self n (by decide : 2 ≠ 0)))
        ((Nat.gcd_dvd_right n s).trans (dvd_pow_self s (by decide : 2 ≠ 0)))
      rcases (Nat.dvd_prime hp).mp hdiv with h | h
      · exact h
      · have hle := Nat.le_of_dvd hs1 (Nat.gcd_dvd_right n s)
        rw [h] at hle
        dsimp [N] at hle
        nlinarith
    · intro q hq hqP _ hdiv
      have hqN := (Nat.dvd_prime_two_le hp hqP.two_le).mp hdiv
      have hsqrt := Nat.sqrt_lt_self (show 1 < N by omega)
      have hle : q ≤ N.sqrt := Nat.lt_succ_iff.mp (mem_range.mp hq)
      omega
  · rintro ⟨hpar,hcop,htest⟩
    by_contra hN
    let q := N.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega : N ≠ 1)
    have hdiv : q ∣ N := Nat.minFac_dvd N
    have hq₂ : q ≠ 2 := by
      intro h
      apply hpar
      apply (parity_test n s).mp
      simpa [h] using hdiv
    have hqle : q ≤ N.sqrt := Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega : 0 < N) hN)
    exact htest q (mem_range.mpr (Nat.lt_succ_of_le hqle)) hq (residue_one hq hq₂ hcop hdiv) hdiv

private def test (n s : ℕ) : Prop := n%2 ≠ s%2 ∧ n.Coprime s ∧
  ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2

private noncomputable instance (n s : ℕ) : Decidable (test n s) := Classical.propDecidable _

theorem characterization : ∀ n : ℕ, OeisA69004.a n = ((Ico 1 n).filter (test n)).card := by
  intro n
  unfold OeisA69004.a
  calc
    _ = ∑ s ∈ Ico 1 n, if test n s then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro s hs
      exact if_congr (prime_iff_test hs) rfl rfl
    _ = _ := by simp

end A69004PrimeTest

theorem OMA.solution : OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H2 := by
  intro n
  rw [A69004PrimeTest.characterization n]
  apply congrArg Finset.card
  ext s
  simp only [Finset.mem_filter, A69004PrimeTest.test]