import OMAStatements.S_oeis_a055008

namespace OMA.P_oeis_a055008

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- A square or twice a square. -/
def Q (k : ℕ) : Prop := IsSquare k ∨ ∃ m, k = 2 * m ^ 2

lemma geom_mod_two (p : ℕ) (hp : Odd p) (n : ℕ) :
    (∑ j ∈ range (n + 1), p ^ j) % 2 = (n + 1) % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp (hp.pow : Odd (p ^ (n + 1)))]
    omega

lemma Q_prime_pow (p n : ℕ) (hp : p.Prime) (h : Odd (σ 1 (p ^ n))) : Q (p ^ n) := by
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left; exact ⟨p ^ t, by rw [pow_add]⟩
  · rcases hp.eq_two_or_odd' with rfl | hodd
    · right; exact ⟨2 ^ t, by ring⟩
    · rw [sigma_one_apply_prime_pow hp] at h
      have := geom_mod_two p hodd (2 * t + 1)
      rw [Nat.odd_iff.mp h] at this
      omega

lemma Q_mul (a b : ℕ) (hab : Nat.Coprime a b) (ha : Q a) (hb : Q b) : Q (a * b) := by
  rcases ha with ⟨r, rfl⟩ | ⟨s, rfl⟩ <;> rcases hb with ⟨u, rfl⟩ | ⟨t, rfl⟩
  · left; exact ⟨r * u, by ring⟩
  · right; exact ⟨r * t, by ring⟩
  · right; exact ⟨s * u, by ring⟩
  · exfalso
    have h2 : 2 ∣ Nat.gcd (2 * s ^ 2) (2 * t ^ 2) :=
      Nat.dvd_gcd (dvd_mul_right 2 _) (dvd_mul_right 2 _)
    rw [hab] at h2
    omega

lemma Q_of_odd_sigma : ∀ k : ℕ, Odd (σ 1 k) → Q k := by
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact Q_prime_pow p n hp
  | zero => intro h; simp at h
  | one => intro _; left; exact ⟨1, rfl⟩
  | coprime a b _ _ hab iha ihb =>
    intro h
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, Nat.odd_mul] at h
    exact Q_mul a b hab (iha h.1) (ihb h.2)

end OMA.P_oeis_a055008

open OMA.P_oeis_a055008 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055008.main := by
  intro k h
  rcases Nat.lt_or_ge 2 k with hk | hk
  · apply Q_of_odd_sigma
    rcases Nat.even_or_odd (ArithmeticFunction.sigma 1 k) with he | ho
    · exfalso
      have h2 : 2 ∣ Nat.gcd k.totient (ArithmeticFunction.sigma 1 k) :=
        Nat.dvd_gcd (even_iff_two_dvd.mp (Nat.totient_even hk)) (even_iff_two_dvd.mp he)
      rw [h] at h2
      omega
    · exact ho
  · interval_cases k
    · simp at h
    · left; exact ⟨1, rfl⟩
    · right; exact ⟨1, rfl⟩
