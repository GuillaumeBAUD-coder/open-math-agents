import OMAStatements.S_oeis_a134003
import Mathlib

namespace OMA.A134003Proof

/-- `s^2 = 3 P^2` is impossible for a prime `P`. -/
lemma no_sq3 {P s : ℤ} (hP : Prime P) (h : s ^ 2 = 3 * P ^ 2) : False := by
  have hd : P ∣ s ^ 2 := ⟨3 * P, by rw [h]; ring⟩
  obtain ⟨u, rfl⟩ := hP.dvd_of_dvd_pow hd
  have hP0 : P ≠ 0 := hP.ne_zero
  have hu : u ^ 2 = 3 := by
    have h2 : P ^ 2 * (u ^ 2 - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3) hP0
    · linarith
  have h1 : -2 < u := by nlinarith
  have h2 : u < 2 := by nlinarith
  interval_cases u <;> norm_num at hu

lemma small_lt (t : ℤ) (h : t ^ 2 < 4) : t = -1 ∨ t = 0 ∨ t = 1 := by
  have h1 : -2 < t := by nlinarith
  have h2 : t < 2 := by nlinarith
  omega

lemma small_le (t : ℤ) (h : t ^ 2 ≤ 4) (h0 : 0 < t) : t = 1 ∨ t = 2 := by
  have h2 : t < 3 := by nlinarith
  omega

lemma sq_bound_lt {P t q : ℤ} (hP : 0 < P) (hq : 0 < q) (h : (P * t) ^ 2 + q ^ 2 = 4 * P ^ 2) :
    t ^ 2 < 4 := by
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have h3 : P ^ 2 * t ^ 2 < P ^ 2 * 4 := by
    have : (P * t) ^ 2 = P ^ 2 * t ^ 2 := by ring
    linarith
  exact lt_of_mul_lt_mul_left h3 (sq_nonneg P)

lemma sq_bound_le {P t q : ℤ} (hP : 0 < P) (h : (P * t) ^ 2 + q ^ 2 = 4 * P ^ 2) :
    t ^ 2 ≤ 4 := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have h3 : P ^ 2 * t ^ 2 ≤ P ^ 2 * 4 := by
    have : (P * t) ^ 2 = P ^ 2 * t ^ 2 := by ring
    linarith
  exact le_of_mul_le_mul_left h3 (pow_pos hP 2)

theorem main_proof :
    ∀ n : ℕ, 0 < n → (n ^ 2 + (n + 5) ^ 2).Prime →
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5) := by
  rintro n hn hpn ⟨a, b, ha, hb, hab⟩
  set P : ℤ := (n : ℤ) ^ 2 + ((n : ℤ) + 5) ^ 2 with hPdef
  have hP : Prime P := by
    have := Nat.prime_iff_prime_int.mp hpn
    simpa [hPdef] using this
  have hP37 : 37 ≤ P := by
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  have habZ : (n : ℤ) * (n + 5) = a * (a + 5) + b * (b + 5) := by exact_mod_cast hab
  have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
  set X : ℤ := 2 * a + 5 with hX
  set Y : ℤ := 2 * b + 5 with hY
  set Z : ℤ := 2 * n + 5 with hZ
  have hX7 : 7 ≤ X := by omega
  have hY7 : 7 ≤ Y := by omega
  have hZ7 : 7 ≤ Z := by
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    omega
  have hXY : X ^ 2 + Y ^ 2 = 2 * P := by
    simp only [hX, hY, hPdef]; linear_combination 4 * habZ.symm
  have hZP : Z ^ 2 + 25 = 2 * P := by
    simp only [hZ, hPdef]; ring
  have key : (5 * X - Y * Z) * (5 * X + Y * Z) = P * (2 * (X ^ 2 - Z ^ 2)) := by
    have hY2 : Y ^ 2 = 2 * P - X ^ 2 := by linarith
    have hZ2 : Z ^ 2 = 2 * P - 25 := by linarith
    have : (5 * X - Y * Z) * (5 * X + Y * Z) = 25 * X ^ 2 - Y ^ 2 * Z ^ 2 := by ring
    rw [this, hY2, hZ2]
    ring
  have hdvd : P ∣ (5 * X - Y * Z) * (5 * X + Y * Z) := ⟨_, key⟩
  have id1 : (5 * X + Y * Z) ^ 2 + (X * Z - 5 * Y) ^ 2 = 4 * P ^ 2 := by
    have : (5 * X + Y * Z) ^ 2 + (X * Z - 5 * Y) ^ 2 = (X ^ 2 + Y ^ 2) * (Z ^ 2 + 25) := by ring
    rw [this, hXY, hZP]; ring
  have id2 : (5 * X - Y * Z) ^ 2 + (X * Z + 5 * Y) ^ 2 = 4 * P ^ 2 := by
    have : (5 * X - Y * Z) ^ 2 + (X * Z + 5 * Y) ^ 2 = (X ^ 2 + Y ^ 2) * (Z ^ 2 + 25) := by ring
    rw [this, hXY, hZP]; ring
  rcases hP.dvd_or_dvd hdvd with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- `P ∣ 5X - YZ`
    rw [ht] at id2
    have hq : 0 < X * Z + 5 * Y := by
      have := mul_pos (by linarith : (0 : ℤ) < X) (by linarith : (0 : ℤ) < Z)
      linarith
    have ht2 : t ^ 2 < 4 := sq_bound_lt (by linarith) hq id2
    rcases small_lt t ht2 with rfl | rfl | rfl
    · exact no_sq3 hP (s := X * Z + 5 * Y) (by linarith)
    · have hq2 : X * Z + 5 * Y = 2 * P := by
        have : (X * Z + 5 * Y - 2 * P) * (X * Z + 5 * Y + 2 * P) = 0 := by linear_combination id2
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      have e1 : 5 * X - Y * Z = 0 := by linarith
      have e2 : X * Z + 5 * Y = Z ^ 2 + 25 := by linarith
      have : (Y - 5) * (Z ^ 2 + 25) = 0 := by linear_combination (-Z) * e1 + 5 * e2
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · have := sq_nonneg Z
        linarith
    · exact no_sq3 hP (s := X * Z + 5 * Y) (by linarith)
  · -- `P ∣ 5X + YZ`
    rw [ht] at id1
    have hpos : 0 < 5 * X + Y * Z := by
      have := mul_pos (by linarith : (0 : ℤ) < Y) (by linarith : (0 : ℤ) < Z)
      linarith
    have htpos : 0 < t := by
      rw [ht] at hpos
      exact pos_of_mul_pos_right hpos (by linarith)
    have ht2 : t ^ 2 ≤ 4 := sq_bound_le (by linarith) id1
    rcases small_le t ht2 htpos with rfl | rfl
    · exact no_sq3 hP (s := X * Z - 5 * Y) (by linarith)
    · have e1 : X * Z - 5 * Y = 0 := by
        have : (X * Z - 5 * Y) ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have e2 : 5 * X + Y * Z = Z ^ 2 + 25 := by linarith
      have : (X - 5) * (Z ^ 2 + 25) = 0 := by linear_combination Z * e1 + 5 * e2
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · have := sq_nonneg Z
        linarith

end OMA.A134003Proof

open OMA.A134003Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a134003.main := main_proof
