import OMAStatements.S_oeis_a258903
import Mathlib

open OMA.S_oeis_a258903

namespace OMA.Period258903

private theorem exponent_le {p : ℕ} (hp : p.Prime) (e : ℕ) : e ≤ p^e := by
  induction e with
  | zero => simp
  | succ i ih =>
    rw [pow_succ]
    have hpos : 0 < p^i := pow_pos hp.pos _
    have htwo := Nat.mul_le_mul_left (p^i) hp.two_le
    nlinarith

/-- Euler periodicity on every prime power, including those dividing the base. -/
private theorem pow_period (M : ℕ) : 0 < M → ∀ x n t : ℕ, M ≤ n → M.totient ∣ t →
    x ^ (n + t) ≡ x ^ n [MOD M] := by
  induction M using Nat.recOnPrimeCoprime with
  | zero => intro h; omega
  | prime_pow p e hp =>
    intro _ x n t hn ht
    by_cases hpx : p ∣ x
    · have he := exponent_le hp e
      have hdn : p ^ e ∣ x ^ n :=
        dvd_trans (pow_dvd_pow_of_dvd hpx e) (pow_dvd_pow x (he.trans hn))
      exact (Nat.modEq_zero_iff_dvd.mpr (hdn.trans (pow_dvd_pow x (by omega : n ≤ n+t)))).trans
        (Nat.modEq_zero_iff_dvd.mpr hdn).symm
    · have hc : x.Coprime (p ^ e) := (hp.coprime_iff_not_dvd.mpr hpx).symm.pow_right e
      obtain ⟨j, rfl⟩ := ht
      have h := (Nat.ModEq.pow_totient hc).pow j
      simpa only [pow_add, pow_mul, one_pow, mul_one] using h.mul_left (x^n)
  | coprime a b ha hb hab ia ib =>
    intro _ x n t hn ht
    have da : a ∣ a*b := dvd_mul_right a b
    have db : b ∣ a*b := dvd_mul_left b a
    exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨
      ia (by omega) x n t ((Nat.le_of_dvd (by positivity) da).trans hn)
        ((Nat.totient_dvd_of_dvd da).trans ht),
      ib (by omega) x n t ((Nat.le_of_dvd (by positivity) db).trans hn)
        ((Nat.totient_dvd_of_dvd db).trans ht)⟩

private theorem interior {M d e n : ℕ} (hM : 0 < M) (hn : 2*M+4 ≤ n)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hmul : d*e=n) :
    M ∣ term 2 3 n (d,e) := by
  have hsum : M+(d+e) ≤ n := by
    have hprod : 0 ≤ ((d:ℤ)-2)*((e:ℤ)-2) := mul_nonneg (by omega) (by omega)
    zify at hmul hn ⊢
    nlinarith
  have hden := Nat.factorial_mul_factorial_dvd_factorial_add d e
  have hfac : M * (d.factorial * e.factorial) ∣ n.factorial :=
    ((Nat.mul_dvd_mul (Nat.dvd_factorial hM (le_refl M)) hden).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add M (d+e))).trans
      (Nat.factorial_dvd_factorial hsum)
  obtain ⟨w, hw⟩ := hfac
  let D := d.factorial * e.factorial
  have hD : 0 < D := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  change M ∣ (2^d * 3^e * n.factorial) / D
  refine ⟨2^d * 3^e * w, ?_⟩
  have hnum : 2^d * 3^e * n.factorial = (M*(2^d*3^e*w))*D := by
    rw [hw]; dsimp [D]; ring
  rw [hnum, Nat.mul_div_cancel _ hD]

private theorem collapse {M n : ℕ} (hM : 0 < M) (hn : 2*M+4 ≤ n) :
    seq 2 3 n ≡ 2*3^n + 3*2^n [MOD M] := by
  classical
  let f (z : ℕ × ℕ) := (if z = (1,n) then 2*3^n else 0) +
    (if z = (n,1) then 3*2^n else 0)
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have h1n : (1,n) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr (by simp [hn0])
  have hn1' : (n,1) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr (by simp [hn0])
  rw [seq, if_neg hn0]
  calc
    _ ≡ ∑ z ∈ n.divisorsAntidiagonal, f z [MOD M] := by
      apply Nat.ModEq.sum
      rintro ⟨d,e⟩ hz
      have hm : d*e=n := (Nat.mem_divisorsAntidiagonal.mp hz).1
      rcases eq_or_ne d 1 with rfl|hd
      · simp only [one_mul] at hm
        subst e
        have hval : term 2 3 n (1,n) = 2*3^n := by
          simpa only [term, pow_one, Nat.factorial_one, one_mul, Prod.fst, Prod.snd] using
            Nat.mul_div_cancel (2*3^n) (Nat.factorial_pos n)
        simp [Nat.ModEq, f, hval, hn1, Ne.symm hn1]
      rcases eq_or_ne e 1 with rfl|he
      · simp only [mul_one] at hm
        subst d
        have hval : term 2 3 n (n,1) = 2^n*3 := by
          simpa only [term, pow_one, Nat.factorial_one, mul_one, Prod.fst, Prod.snd] using
            Nat.mul_div_cancel (2^n*3) (Nat.factorial_pos n)
        simp [Nat.ModEq, f, hval, hn1, Ne.symm hn1, mul_comm]
      have hd0 : d ≠ 0 := by rintro rfl; simp_all
      have he0 : e ≠ 0 := by rintro rfl; simp_all
      simpa [f, hd, he] using (Nat.modEq_zero_iff_dvd.mpr
        (interior hM hn (by omega : 2 ≤ d) (by omega : 2 ≤ e) hm))
    _ = _ := by simp [f, Finset.sum_add_distrib, h1n, hn1']

end OMA.Period258903

theorem OMA.solution : type_of% @OMA.S_oeis_a258903.main := by
  intro M hM
  refine ⟨2*M+4, ?_⟩
  intro n hn
  have h₂ := (OMA.Period258903.pow_period M hM 2 n M.totient (by omega) dvd_rfl).mul_left 3
  have h₃ := (OMA.Period258903.pow_period M hM 3 n M.totient (by omega) dvd_rfl).mul_left 2
  exact (OMA.Period258903.collapse hM (by omega : 2*M+4 ≤ n+M.totient)).trans
    ((h₃.add h₂).trans (OMA.Period258903.collapse hM hn).symm)
