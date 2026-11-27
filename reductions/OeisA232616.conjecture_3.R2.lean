import FormalConjectures.OEIS.«232616»

/-! Remove the full common divisor from any imprimitive solution. -/

namespace OMA.R_OeisA232616_conjecture_3_R2

/-- Classify primitive solutions. -/
def H1 : Prop := ∀ x y n m : ℕ, 1 < x → 1 < y → 1 < n → 1 < m →
  x.Coprime y → x ^ n + n = y ^ m →
  (x = 5 ∧ n = 2 ∧ y = 3 ∧ m = 3) ∨ (x = 5 ∧ n = 3 ∧ y = 2 ∧ m = 7)

/-- Exclude perfect powers after removing the common scale from both bases. -/
def H2 : Prop := ∀ d a b t m : ℕ, 1 < d → 0 < a → 0 < b → 0 < t → 1 < m →
  a.Coprime b → let n := d ^ m * t
  d ^ (n - m) * a ^ n + t ≠ b ^ m

theorem main : H1 → H2 → type_of% @OeisA232616.conjecture_3 := by
  intro prim scaled x y n m hx hy hn hm
  constructor
  · intro eqn
    by_cases hc : x.Coprime y
    · exact prim x y n m hx hy hn hm hc eqn
    let d := x.gcd y
    have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd2 : 1 < d := by
      change x.gcd y ≠ 1 at hc
      change 1 < x.gcd y
      dsimp [d] at hd
      omega
    have dx : d ∣ x := Nat.gcd_dvd_left ..
    have dy : d ∣ y := Nat.gcd_dvd_right ..
    have divides (k : ℕ) (kn : k ≤ n) (km : k ≤ m) : d ^ k ∣ n := by
      have hsum : d ^ k ∣ x ^ n + n := eqn ▸ pow_dvd_pow_of_dvd_of_le dy km
      exact (Nat.dvd_add_right (pow_dvd_pow_of_dvd_of_le dx kn)).mp hsum
    have mn : m < n := by
      by_contra! h
      have hle := Nat.le_of_dvd (by omega : 0 < n) (divides n le_rfl h)
      have hp : 2 ^ n ≤ d ^ n := by gcongr <;> omega
      have := n.lt_two_pow_self
      omega
    obtain ⟨t, ht⟩ := divides m mn.le le_rfl
    let a := x / d
    let b := y / d
    have hxa : a * d = x := Nat.div_mul_cancel dx
    have hyb : b * d = y := Nat.div_mul_cancel dy
    have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
    have ha : 0 < a := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hxa; omega
    have hb : 0 < b := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hyb; omega
    have htpos : 0 < t := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at ht; omega
    exfalso
    apply scaled d a b t m hd2 ha hb htpos hm hab
    rw [← ht]
    have hdexp : d ^ (n - m) * d ^ m = d ^ n := by rw [← pow_add, Nat.sub_add_cancel mn.le]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hd m)
    calc
      (d ^ (n - m) * a ^ n + t) * d ^ m = a ^ n * (d ^ (n - m) * d ^ m) + d ^ m * t := by ring
      _ = x ^ n + n := by rw [hdexp, ← mul_pow, hxa, ← ht]
      _ = b ^ m * d ^ m := by rw [eqn, ← mul_pow, hyb]
  · rintro (⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩) <;> decide

end OMA.R_OeisA232616_conjecture_3_R2
