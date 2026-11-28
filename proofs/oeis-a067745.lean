import OMAStatements.S_oeis_a067745
import Mathlib

/-! Proof for OEIS A067745: write `3n - 2 = 2^v o` with `o` odd. Since `3n - 2 ≤ 4^(n-1)`, `2^v` divides
`4^(n-1)`, so the denominator is `2^v C`. The odd part `o` is coprime to `n` (as
`gcd(3n - 2, n) ∣ 2`), to `2n - 1` (as `3(2n - 1) - 2(3n - 2) = 1`) and to `4^(n-1)`, hence to `C`, so
the fraction reduces to `o / C` and its numerator is `o`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P067745
open OMA.S_oeis_a067745

lemma le_four_pow (n : ℕ) (hn : 1 ≤ n) : 3 * n - 2 ≤ 4 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have := ih hk
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      have : 1 ≤ 4 ^ (k - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega

lemma gcd_n (n : ℕ) (hn : 1 ≤ n) : Nat.gcd (3 * n - 2) n ∣ 2 := by
  have h1 : Nat.gcd (3 * n - 2) n ∣ 3 * n - 2 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (3 * n - 2) n ∣ 3 * n := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3
  have := Nat.dvd_sub h2 h1
  rwa [show 3 * n - (3 * n - 2) = 2 by omega] at this

lemma coprime_2n1 (n : ℕ) (hn : 1 ≤ n) : Nat.Coprime (3 * n - 2) (2 * n - 1) := by
  have h1 : Nat.gcd (3 * n - 2) (2 * n - 1) ∣ 2 * (3 * n - 2) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
  have h2 : Nat.gcd (3 * n - 2) (2 * n - 1) ∣ 3 * (2 * n - 1) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3
  have := Nat.dvd_sub h2 h1
  rw [show 3 * (2 * n - 1) - 2 * (3 * n - 2) = 1 by omega] at this
  exact Nat.dvd_one.mp this

end OMA.P067745

theorem OMA.P067745.old_main : ∀ n : ℕ, 1 ≤ n →
    (((3 * n - 2 : ℕ) : ℚ) / ((n : ℚ) ^ (2 * n - 1) * ((2 * n - 1 : ℕ) : ℚ) * 4 ^ (n - 1))).num
      = (OMA.S_oeis_a067745.oddPart (3 * n - 2) : ℤ) := by
  intro n hn
  open OMA.P067745 OMA.S_oeis_a067745 in
  set A := 3 * n - 2 with hA
  have hA0 : A ≠ 0 := by omega
  set v := A.factorization 2 with hv
  set o := oddPart A with ho
  have hAo : A = 2 ^ v * o := (Nat.ordProj_mul_ordCompl_eq_self A 2).symm
  have hodd : Nat.Coprime 2 o := Nat.coprime_ordCompl Nat.prime_two hA0
  -- 2^v divides 4^(n-1)
  have hvle : v ≤ 2 * (n - 1) := by
    have h1 : 2 ^ v ≤ A := Nat.ordProj_le 2 hA0
    have h2 : A ≤ 2 ^ (2 * (n - 1)) := by rw [pow_mul]; exact OMA.P067745.le_four_pow n hn
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h1.trans h2)
  set B := n ^ (2 * n - 1) * (2 * n - 1) * 4 ^ (n - 1) with hB
  have hdvdB : 2 ^ v ∣ B := by
    have : 2 ^ v ∣ 4 ^ (n - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_dvd_pow 2 hvle
    exact Dvd.dvd.mul_left this _
  obtain ⟨C, hC⟩ := hdvdB
  have hBpos : 0 < B := by
    have h1 : 0 < n ^ (2 * n - 1) := pow_pos (by omega) _
    have h2 : 0 < 2 * n - 1 := by omega
    have h3 : 0 < 4 ^ (n - 1) := pow_pos (by norm_num) _
    exact Nat.mul_pos (Nat.mul_pos h1 h2) h3
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · rw [h, mul_zero] at hC; omega
    · exact h
  -- o is coprime to B, hence to C
  have hoA : o ∣ A := ⟨2 ^ v, by rw [hAo]; ring⟩
  have hon : Nat.Coprime o n := by
    have hg : Nat.gcd o n ∣ 2 :=
      (Nat.gcd_dvd_gcd_of_dvd_left n hoA).trans (OMA.P067745.gcd_n n hn)
    have hg1 : Nat.gcd o n ∣ o := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
    · exact h
    · exfalso; rw [h] at hg1
      have := Nat.Coprime.eq_one_of_dvd hodd hg1
      omega
  have ho2n : Nat.Coprime o (2 * n - 1) := Nat.Coprime.coprime_dvd_left hoA (OMA.P067745.coprime_2n1 n hn)
  have ho4 : Nat.Coprime o (4 ^ (n - 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.Coprime.pow_right _ hodd.symm
  have hoB : Nat.Coprime o B :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hon) ho2n) ho4
  have hoC : Nat.Coprime o C := Nat.Coprime.coprime_dvd_right ⟨2 ^ v, by rw [hC]; ring⟩ hoB
  -- rewrite the fraction as o / C
  have hfrac : (((3 * n - 2 : ℕ) : ℚ) / ((n : ℚ) ^ (2 * n - 1) * ((2 * n - 1 : ℕ) : ℚ) * 4 ^ (n - 1)))
      = ((o : ℤ) : ℚ) / ((C : ℤ) : ℚ) := by
    have hBq : ((n : ℚ) ^ (2 * n - 1) * ((2 * n - 1 : ℕ) : ℚ) * 4 ^ (n - 1)) = ((2 ^ v * C : ℕ) : ℚ) := by
      rw [← hC, hB]; push_cast; ring
    rw [hBq, show (3 * n - 2 : ℕ) = 2 ^ v * o from hAo]
    have h2 : (2 : ℚ) ^ v ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
  rw [hfrac, Rat.num_div_eq_of_coprime (by exact_mod_cast hCpos) (by simpa using hoC)]

theorem OMA.solution : type_of% @OMA.S_oeis_a067745.main := by
  intro n hn
  have h := OMA.P067745.old_main n hn
  unfold OMA.S_oeis_a067745.a
  rw [← h]
  congr 2
  · rw [Nat.cast_sub (by omega)]; push_cast; ring
  · rw [Nat.cast_sub (by omega)]; push_cast; ring
