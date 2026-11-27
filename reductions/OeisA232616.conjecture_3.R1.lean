import FormalConjectures.OEIS.«232616»
import Mathlib.Tactic

-- Credit: @ArtemCherbaev
namespace OMA.R_OeisA232616_conjecture_3_R1

-- Exclude squares when the left exponent is odd.
def H1 : Prop :=
  ∀ x z n : ℕ, 1 < x → 1 < z → 1 < n → ¬ 2 ∣ n → x ^ n + n ≠ z ^ 2

-- Classify odd prime powers when the prime does not divide the left exponent.
def H2 : Prop :=
  ∀ x z n p : ℕ, 1 < x → 1 < z → 1 < n → p.Prime → 2 < p → ¬ p ∣ n →
    x ^ n + n = z ^ p →
      (x = 5 ∧ n = 2 ∧ z = 3 ∧ p = 3) ∨ (x = 5 ∧ n = 3 ∧ z = 2 ∧ p = 7)

lemma consecutive_gap (a d : ℕ) (ha : 1 ≤ a) :
    a ^ (d + 2) + (d + 2) * a ≤ (a + 1) ^ (d + 2) := by
  induction d with
  | zero => simp only [Nat.zero_add, pow_two]; nlinarith
  | succ d ih =>
    have hmul := Nat.mul_le_mul_right a ih
    have hscale := Nat.mul_le_mul_left ((d + 2) * a) ha
    change a ^ ((d + 2) + 1) + ((d + 2) + 1) * a ≤ (a + 1) ^ ((d + 2) + 1)
    rw [pow_succ a (d + 2), pow_succ (a + 1) (d + 2)]
    nlinarith only [hmul, hscale, ih, Nat.zero_le (a ^ (d + 2)), Nat.zero_le (d * a)]

lemma exponent_not_dvd {x z n p : ℕ} (hx : 1 < x) (hn : 1 < n) (hp : 2 ≤ p)
    (heq : x ^ n + n = z ^ p) : ¬ p ∣ n := by
  rintro ⟨k, rfl⟩
  rw [Nat.mul_comm p k, pow_mul] at heq
  have hlt : x ^ k < z := by
    by_contra! h
    have hpow := Nat.pow_le_pow_left h p
    have hpos : 0 < k * p := by simpa [Nat.mul_comm] using (show 0 < p * k by omega)
    omega
  have hgap : (x ^ k) ^ p + p * (x ^ k) ≤ (x ^ k + 1) ^ p := by
    have h := consecutive_gap (x ^ k) (p - 2) (Nat.one_le_pow k x (by omega))
    simpa only [show p - 2 + 2 = p by omega] using h
  have hupper := Nat.pow_le_pow_left (show x ^ k + 1 ≤ z by omega) p
  have hstrict := Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_self (n := k) hx) (show 0 < p by omega)
  rw [Nat.mul_comm k p] at heq
  omega

lemma small_power_exponent {y k : ℕ} (hy : 1 < y) (hk : 0 < k) (h : y ^ k ≤ 3) :
    k = 1 := by
  by_contra! hne
  have hbase := Nat.pow_le_pow_left (show 2 ≤ y by omega) 2
  have hexp := Nat.pow_le_pow_right (show 0 < y by omega) (show 2 ≤ k by omega)
  omega

theorem main : H1 → H2 → type_of% @OeisA232616.conjecture_3 := by
  intro hsq hodd x y n m hx hy hn hm
  constructor
  · intro heq
    obtain ⟨p, hp, k, hmk⟩ : ∃ p : ℕ, p.Prime ∧ ∃ k : ℕ, m = p * k :=
      ⟨m.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd m⟩
    have hk : 0 < k := by
      by_contra! h
      have : k = 0 := by omega
      simp [this] at hmk
      omega
    have hz := Nat.one_lt_pow (by omega : k ≠ 0) hy
    have he : x ^ n + n = (y ^ k) ^ p := by
      simpa only [hmk, Nat.mul_comm p k, pow_mul] using heq
    have hnd := exponent_not_dvd hx hn hp.two_le he
    by_cases htwo : p = 2
    · subst p
      exact False.elim (hsq x (y ^ k) n hx hz hn hnd he)
    · have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm htwo)
      rcases hodd x (y ^ k) n p hx hz hn hp hpgt hnd he with h | h
      · obtain ⟨rfl, rfl, hz3, rfl⟩ := h
        have hk1 := small_power_exponent hy hk (show y ^ k ≤ 3 by omega)
        subst k
        simp_all
      · obtain ⟨rfl, rfl, hz2, rfl⟩ := h
        have hk1 := small_power_exponent hy hk (show y ^ k ≤ 3 by omega)
        subst k
        simp_all
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> decide

end OMA.R_OeisA232616_conjecture_3_R1
