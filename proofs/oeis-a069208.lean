import OMAStatements.S_oeis_a069208
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: P f n is the sum over divisors d of n of chi d * f d (sum over a filter). The function
-- d -> chi d * f d is multiplicative, because for coprime m, n a number m*n is powerful iff m and
-- n are (a prime square dividing m*n and coprime to n divides m). Summing a multiplicative function
-- over divisors gives a multiplicative function (Dirichlet product with zeta). No computer search.

namespace OMA.A069208Proof

open OMA.S_oeis_a069208 ArithmeticFunction
open scoped ArithmeticFunction.zeta

theorem powerful_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    (∀ p ∈ (m * n).primeFactors, p ^ 2 ∣ m * n) ↔
      (∀ p ∈ m.primeFactors, p ^ 2 ∣ m) ∧ (∀ p ∈ n.primeFactors, p ^ 2 ∣ n) := by
  rw [Nat.primeFactors_mul hm hn]
  constructor
  · intro H
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have hpn : ¬ p ∣ n := fun hpn =>
        (Nat.prime_of_mem_primeFactors hp).not_dvd_one
          (h.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpn)
      have hc : (p ^ 2).Coprime n :=
        Nat.Coprime.pow_left 2 (((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd).mpr hpn)
      exact hc.dvd_of_dvd_mul_right (H p (Finset.mem_union_left _ hp))
    · have hpm : ¬ p ∣ m := fun hpm =>
        (Nat.prime_of_mem_primeFactors hp).not_dvd_one
          (h.gcd_eq_one ▸ Nat.dvd_gcd hpm (Nat.dvd_of_mem_primeFactors hp))
      have hc : (p ^ 2).Coprime m :=
        Nat.Coprime.pow_left 2 (((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd).mpr hpm)
      exact hc.dvd_of_dvd_mul_left (H p (Finset.mem_union_right _ hp))
  · rintro ⟨H1, H2⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact dvd_mul_of_dvd_left (H1 p hp) n
    · exact dvd_mul_of_dvd_right (H2 p hp) m

theorem chi_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    chi (m * n) = chi m * chi n := by
  unfold chi
  rw [if_congr (powerful_mul hm hn h) rfl rfl]
  split_ifs <;> simp_all

theorem P_eq (f : ℕ → ℤ) (n : ℕ) : P f n = ∑ d ∈ n.divisors, chi d * f d := by
  unfold P chi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

theorem result : ∀ f : ℕ → ℤ, f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    (P f 1 = 1 ∧
      ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → P f (m * n) = P f m * P f n) ∧
    ∀ n : ℕ, 0 < n → P f n = ∑ d ∈ n.divisors, chi d * f d := by
  intro f h1 hmul
  let F : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else chi n * f n, rfl⟩
  have hF : F.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [F, chi, h1]
    · intro m n h
      by_cases hm : m = 0
      · simp [F, hm]
      by_cases hn : n = 0
      · simp [F, hn]
      simp only [F, coe_mk, mul_eq_zero, hm, hn, or_self, if_false]
      rw [chi_mul hm hn h, hmul m n h]
      ring
  have hG : (F * ζ).IsMultiplicative := hF.mul isMultiplicative_zeta.natCast
  have hPG : ∀ n : ℕ, 0 < n → P f n = (F * ζ) n := by
    intro n hn
    rw [P_eq, coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    simp [F, this]
  refine ⟨⟨?_, ?_⟩, fun n _ => P_eq f n⟩
  · rw [hPG 1 one_pos, hG.map_one]
  · intro m n hm hn h
    rw [hPG _ (Nat.mul_pos hm hn), hPG m hm, hPG n hn, hG.map_mul_of_coprime h]

end OMA.A069208Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a069208.main := OMA.A069208Proof.result
