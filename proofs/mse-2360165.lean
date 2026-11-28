import OMAStatements.S_mse_2360165
import Mathlib

open OMA.S_mse_2360165 Filter

private def correction (n : ℕ) : ℕ := if 2 ∣ n then 2 else 1

private theorem correction_mul {a b : ℕ} (h : Nat.Coprime a b) :
    correction (a*b) = correction a * correction b := by
  unfold correction
  simp only [Nat.prime_two.dvd_mul]
  by_cases ha : 2 ∣ a <;> by_cases hb : 2 ∣ b
  · have h2 := Nat.dvd_gcd ha hb
    rw [h] at h2
    norm_num at h2
  · simp [ha,hb]
  · simp [ha,hb]
  · simp [ha,hb]

private theorem prime_power_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p^(k+1) ≤ correction (p^(k+1)) * (p^(k+1)).totient^2 := by
  rw [Nat.totient_prime_pow_succ hp]
  have hpow : 1 ≤ p^k := Nat.one_le_pow k _ (by have := hp.pos; omega)
  have hbase : p ≤ correction (p^(k+1)) * (p-1)^2 := by
    by_cases h2 : p=2
    · subst p
      have hd : 2 ∣ 2^(k+1) := dvd_pow_self _ (by omega)
      simp [correction,hd]
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      have hcp : ¬ 2 ∣ p^(k+1) := fun hh =>
        h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow hh)).symm
      simp only [correction, if_neg hcp, one_mul]
      have he : p = (p-1)+1 := by omega
      rw [he] at h3
      have h4 : 2 ≤ p-1 := by omega
      have hm := Nat.mul_le_mul_left (p-1) h4
      have hh : (p-1)+1 ≤ (p-1)^2 := by rw [pow_two]; omega
      omega
  calc
    p^(k+1) = p^k*p := pow_succ _ _
    _ ≤ p^k * (correction (p^(k+1))*(p-1)^2) := Nat.mul_le_mul_left _ hbase
    _ ≤ (p^k*p^k) * (correction (p^(k+1))*(p-1)^2) :=
      Nat.mul_le_mul_right _ (by simpa only [mul_one] using Nat.mul_le_mul_left (p^k) hpow)
    _ = correction (p^(k+1))*(p^k*(p-1))^2 := by ring

private theorem totient_bound (n : ℕ) : n ≤ correction n * n.totient^2 := by
  induction n using Nat.recOnPrimePow with
  | zero => simp
  | one => norm_num [correction]
  | prime_pow_mul a p k hp hpa hk ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hcop : (p^(j+1)).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left _
    rw [Nat.totient_mul hcop,correction_mul hcop]
    calc
      p^(j+1)*a ≤ (correction (p^(j+1)) * (p^(j+1)).totient^2) *
          (correction a * a.totient^2) := Nat.mul_le_mul (prime_power_bound hp j) ih
      _ = _ := by ring

theorem OMA.solution : type_of% @OMA.S_mse_2360165.main := by
  intro n _ _
  unfold tailTotientLiminf
  refine le_liminf_of_le (by isBoundedDefault) ?_
  let B := n.totient
  filter_upwards [eventually_ge_atTop (2*B^2)] with k hk
  have hbound := totient_bound (n+k+1)
  have hcoef : correction (n+k+1) ≤ 2 := by unfold correction; split <;> decide
  have hl : n+k+1 ≤ 2*(n+k+1).totient^2 :=
    hbound.trans (Nat.mul_le_mul_right _ hcoef)
  have h : B ≤ (n+k+1).totient := by
    by_contra hh
    have hs : (n+k+1).totient^2 ≤ B^2 := Nat.pow_le_pow_left (by omega) _
    have ht := Nat.mul_le_mul_left 2 hs
    omega
  exact_mod_cast h