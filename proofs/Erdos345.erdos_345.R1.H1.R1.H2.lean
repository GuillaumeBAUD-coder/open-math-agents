import OMAReductions.R_Erdos345_erdos_345_R1_H1_R1
import Mathlib

/-!
Count the integers in `[1, M]` coprime to `d` by Möbius inversion:
`#{a ≤ M : gcd(a, d) = 1} = ∑_{e ∣ d} μ(e) ⌊M / e⌋` and `φ(d) = ∑_{e ∣ d} μ(e) (d / e)`.
Then `d · count - M · φ(d) = -∑_{e ∣ d} μ(e) (d / e) (M mod e) ≥ -d · τ(d)`.
-/
open Finset ArithmeticFunction

namespace OMA.CoprimeCount

lemma moebius_sum_divisors (n : ℕ) :
    ∑ e ∈ n.divisors, (moebius e : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  exact h

lemma card_dvd_Icc (M e : ℕ) : #{a ∈ Icc 1 M | e ∣ a} = M / e := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

lemma count_eq (d M : ℕ) (hd : 0 < d) :
    ((#{a ∈ Icc 1 M | a.Coprime d} : ℕ) : ℤ) = ∑ e ∈ d.divisors, (moebius e : ℤ) * ((M / e : ℕ) : ℤ) := by
  rw [natCast_card_filter]
  have h1 : ∀ a ∈ Icc 1 M, (if a.Coprime d then (1 : ℤ) else 0) =
      ∑ e ∈ d.divisors, if e ∣ a then (moebius e : ℤ) else 0 := by
    intro a ha
    have hg : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right _ hd
    rw [← sum_filter]
    have hs : d.divisors.filter (· ∣ a) = (Nat.gcd a d).divisors := by
      ext e
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, hg.ne'⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hd.ne'⟩, h1⟩
    rw [hs, moebius_sum_divisors]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_filter, sum_const, card_dvd_Icc, nsmul_eq_mul, mul_comm]

lemma totient_eq (d : ℕ) (hd : 0 < d) :
    ((d.totient : ℕ) : ℤ) = ∑ e ∈ d.divisors, (moebius e : ℤ) * ((d / e : ℕ) : ℤ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun n => (n.totient : ℤ))
    (g := fun n => (n : ℤ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n) d hd
  rw [← h]
  simp only [Int.cast_id]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (moebius x : ℤ) * (y : ℤ))]

theorem coprime_count (d M : ℕ) (hd : 0 < d) :
    M * d.totient / d - d.divisors.card ≤ #{a ∈ Icc 1 M | a.Coprime d} := by
  suffices hb : ((M * d.totient : ℕ) : ℤ) ≤
      (d : ℤ) * ((#{a ∈ Icc 1 M | a.Coprime d} + d.divisors.card : ℕ) : ℤ) by
    have hb' : M * d.totient ≤ d * (#{a ∈ Icc 1 M | a.Coprime d} + d.divisors.card) := by
      exact_mod_cast hb
    have : M * d.totient / d ≤ #{a ∈ Icc 1 M | a.Coprime d} + d.divisors.card :=
      Nat.div_le_of_le_mul hb'
    omega
  have hC := count_eq d M hd
  have hφ := totient_eq d hd
  rw [Nat.cast_mul, Nat.cast_add, hC, hφ, mul_add, mul_sum, mul_sum, card_eq_sum_ones, Nat.cast_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun e he => ?_
  have hed : e ∣ d := Nat.dvd_of_mem_divisors he
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  obtain ⟨k, hk⟩ := hed
  have hdk : d / e = k := by rw [hk, Nat.mul_div_cancel_left _ he0]
  rw [hdk]
  have hmod : (M : ℤ) = e * ((M / e : ℕ) : ℤ) + ((M % e : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod M e).symm
  have hr0 : (0 : ℤ) ≤ ((M % e : ℕ) : ℤ) := by positivity
  have hr1 : ((M % e : ℕ) : ℤ) ≤ e := by exact_mod_cast (Nat.mod_lt M he0).le
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hdk' : (d : ℤ) = e * k := by exact_mod_cast hk
  rw [hdk', hmod]
  generalize ((M / e : ℕ) : ℤ) = q
  generalize ((M % e : ℕ) : ℤ) = r at hr0 hr1 ⊢
  rcases moebius_eq_or e with h | h | h <;> rw [h] <;> push_cast <;> nlinarith [mul_le_mul_of_nonneg_right hr1 hk0, mul_nonneg hr0 hk0]

end OMA.CoprimeCount

theorem OMA.solution : OMA.R_Erdos345_erdos_345_R1_H1_R1.H2 :=
  fun d M hd => OMA.CoprimeCount.coprime_count d M hd
