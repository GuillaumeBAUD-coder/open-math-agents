import OMAStatements.S_oeis_a101035
import Mathlib

open ArithmeticFunction Finset

namespace A101035Aux

def Pf : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ k ∈ Finset.Icc 1 n, ((Nat.gcd k n : ℕ) : ℤ), by simp⟩

def Z : ArithmeticFunction ℤ := ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)

def nu : ArithmeticFunction ℤ := ⟨fun n => moebius n * n, by simp⟩

def phi : ArithmeticFunction ℤ := ⟨fun n => (Nat.totient n : ℤ), by simp⟩

def idZ : ArithmeticFunction ℤ := ⟨fun n => (n : ℤ), by simp⟩

lemma nu_mul_id : nu * idZ = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => nu x * idZ y)]
  have h1 : ∀ d ∈ n.divisors, nu d * idZ (n / d) = (n : ℤ) * moebius d := by
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    obtain ⟨c, rfl⟩ := hdn
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    simp only [nu, idZ, coe_mk]
    rw [Nat.mul_div_cancel_left _ hd0]
    push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h2 : ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f n) (show (moebius : ArithmeticFunction ℤ) * Z = 1 from moebius_mul_coe_zeta)
    simp only [mul_apply, one_apply] at this
    rw [Nat.sum_divisorsAntidiagonal (f := fun x y => (moebius x : ℤ) * (Z y))] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have : n / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hn hdn) (Nat.pos_of_mem_divisors hd)
      omega
    simp [Z, natCoe_apply, zeta_apply, this]
  rw [h2, one_apply]
  split_ifs with h
  · subst h; simp
  · simp

lemma phi_mul_zeta : phi * Z = idZ := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => phi x * Z y)]
  have : ∑ d ∈ n.divisors, phi d * Z (n / d) = ∑ d ∈ n.divisors, (Nat.totient d : ℤ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have : n / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hn hdn) (Nat.pos_of_mem_divisors hd)
      omega
    simp [Z, natCoe_apply, zeta_apply, this, phi]
  rw [this]
  have h := Nat.sum_totient n
  simp only [idZ, coe_mk]
  exact_mod_cast h

lemma Pf_eq : Pf = idZ * phi := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => idZ x * phi y)]
  simp only [Pf, idZ, phi, coe_mk]
  have h0 : ∑ k ∈ Finset.Icc 1 n, ((Nat.gcd k n : ℕ) : ℤ) = ∑ k ∈ Finset.range n, ((Nat.gcd n k : ℕ) : ℤ) := by
    have e1 : ∑ k ∈ Finset.range (n + 1), ((Nat.gcd n k : ℕ) : ℤ)
        = ∑ k ∈ Finset.range n, ((Nat.gcd n k : ℕ) : ℤ) + n := by
      rw [Finset.sum_range_succ]; simp
    have e2 : ∑ k ∈ Finset.range (n + 1), ((Nat.gcd n k : ℕ) : ℤ)
        = ∑ k ∈ Finset.Icc 1 n, ((Nat.gcd k n : ℕ) : ℤ) + n := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      simp only [Nat.gcd_zero_right]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr
      · ext k; simp
      · intro k _; rw [Nat.gcd_comm]
    linarith
  rw [h0]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => Nat.gcd n k) (t := n.divisors)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    rw [Finset.sum_congr rfl (g := fun _ => (d : ℤ))]
    · rw [Finset.sum_const, Nat.totient_div_of_dvd hdn]
      simp [mul_comm]
    · intro k hk
      simp only [Finset.mem_filter] at hk
      rw [hk.2]
  · intro k _
    simp [Nat.gcd_dvd_left, hn.ne']

def B : ArithmeticFunction ℤ := nu * (nu * Z)

lemma Pf_mul_B : Pf * B = 1 := by
  have h1 : phi = idZ * moebius := by
    have := phi_mul_zeta
    calc phi = phi * (Z * moebius) := by rw [show Z * (moebius : ArithmeticFunction ℤ) = 1 from coe_zeta_mul_moebius, mul_one]
      _ = idZ * moebius := by rw [← mul_assoc, this]
  rw [Pf_eq, h1, B]
  calc idZ * (idZ * (moebius : ArithmeticFunction ℤ)) * (nu * (nu * Z))
      = (nu * idZ) * (nu * idZ) * ((moebius : ArithmeticFunction ℤ) * Z) := by ring
    _ = 1 := by rw [nu_mul_id, show (moebius : ArithmeticFunction ℤ) * Z = 1 from moebius_mul_coe_zeta]; simp

end A101035Aux

open A101035Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a101035.main := by
  intro a ha m hm
  let A : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
  have hA : A * Pf = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => A x * Pf y), one_apply, ← ha n hn]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [A, Pf, hd0]
  have hAB : A = B := by
    calc A = A * (Pf * B) := by rw [Pf_mul_B, mul_one]
      _ = (A * Pf) * B := by rw [mul_assoc]
      _ = B := by rw [hA, one_mul]
  have ham : a m = B m := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f m) hAB
    have hm0 : m ≠ 0 := by omega
    simpa only [A, coe_mk, if_neg hm0] using this
  have hB : B m = ∑ n ∈ m.divisors, ∑ k ∈ (m / n).divisors,
      (moebius n * n) * (moebius k * k) := by
    rw [B, mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => nu x * (nu * Z) y)]
    apply Finset.sum_congr rfl
    intro n hn
    have hnm : n ∣ m := Nat.dvd_of_mem_divisors hn
    have hq : 0 < m / n := Nat.div_pos (Nat.le_of_dvd hm hnm) (Nat.pos_of_mem_divisors hn)
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => nu x * Z y), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkq : k ∣ m / n := Nat.dvd_of_mem_divisors hk
    have : m / n / k ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hq hkq) (Nat.pos_of_mem_divisors hk)
      omega
    simp [nu, Z, natCoe_apply, zeta_apply, this]
  rw [ham, hB]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hnm : n ∣ m := Nat.dvd_of_mem_divisors hn
  have hn0 : 0 < n := Nat.pos_of_mem_divisors hn
  have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
  have hkq : k ∣ m / n := Nat.dvd_of_mem_divisors hk
  have hnk : n * k ∣ m := by
    obtain ⟨c, hc⟩ := hkq
    obtain ⟨e, he⟩ := hnm
    rw [he, Nat.mul_div_cancel_left _ hn0] at hc
    rw [he, hc]; exact ⟨c, by ring⟩
  rw [Nat.cast_div hnk (by positivity)]
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hn0' : (n : ℚ) ≠ 0 := by positivity
  have hk0' : (k : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
