import OMAStatements.S_oeis_a392943
import Mathlib

/-!
# OEIS A392943: a primitive Heronian triangle never has an integer circumradius

Let `a, b, c` be the sides of a triangle with `gcd(a, b, c) = 1`, integer area `K`
(`16 K² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`) and circumradius `R` (`4 R K = a b c`). We show
that `R` cannot be an integer.

**Parity.** Modulo 2 the four factors of `16 K²` are all congruent to `a + b + c`, so the
perimeter is even. As the sides are not all even, exactly one side is even; call it `c`.

**Setting up the descent.** Since `a b` is odd and `4 ∣ a b c`, we get `c = 4 c'`. Heron's
formula can be written `(4K)² + (b² + c² - a²)² = (2bc)²`. Here `b² - a² ≡ 0 (mod 8)`, so
`b² + c² - a² = 8 w'`, which forces `K = 2 K'` and leaves

  `K'² + w'² = b² c'²`   and   `2 R K' = a b c'`.

**Descent.** In any integer solution of these two equations with `a, b` odd, `c'` is even
(second equation), hence `K'² + w'² ≡ 0 (mod 4)`, hence `K'` and `w'` are even, and halving
all three gives another solution. So `c'` is divisible by every power of two: `c' = 0`,
contradicting `c > 0`.
-/

open OMA.S_oeis_a392943

namespace OMA.A392943

/-- The descent: with `a`, `b` odd, the system `K² + w² = b² c²`, `2 R K = a b c` forces `c = 0`. -/
lemma descent {a b R : ℤ} (ha : Odd a) (hb : Odd b) :
    ∀ n : ℕ, ∀ c K w : ℤ, c.natAbs ≤ n → K ^ 2 + w ^ 2 = b ^ 2 * c ^ 2 →
      2 * R * K = a * b * c → c = 0 := by
  intro n
  induction n with
  | zero =>
    intro c K w hc _ _
    omega
  | succ n ih =>
    intro c K w hc h1 h2
    -- `c` is even, because `a * b * c = 2 * (R * K)` and `a`, `b` are odd
    have hc_even : Even c := by
      have h : Even (a * b * c) := ⟨R * K, by linear_combination (-1 : ℤ) * h2⟩
      rcases Int.even_mul.1 h with h | h
      · rcases Int.even_mul.1 h with h | h
        · exact absurd h (Int.not_even_iff_odd.2 ha)
        · exact absurd h (Int.not_even_iff_odd.2 hb)
      · exact h
    obtain ⟨c', rfl⟩ := hc_even
    -- `K² + w² ≡ 0 (mod 4)` forces `K` and `w` to be even
    have hKw : Even K ∧ Even w := by
      rcases Int.even_or_odd K with ⟨p, hp⟩ | ⟨p, hp⟩ <;>
        rcases Int.even_or_odd w with ⟨q, hq⟩ | ⟨q, hq⟩
      · exact ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
      · exfalso
        subst hp hq
        have e : 4 * (p * p) + 4 * (q * q) + 4 * q + 1 = 4 * (b ^ 2 * (c' * c')) := by
          linear_combination h1
        omega
      · exfalso
        subst hp hq
        have e : 4 * (p * p) + 4 * p + 1 + 4 * (q * q) = 4 * (b ^ 2 * (c' * c')) := by
          linear_combination h1
        omega
      · exfalso
        subst hp hq
        have e : 4 * (p * p) + 4 * p + 4 * (q * q) + 4 * q + 2 = 4 * (b ^ 2 * (c' * c')) := by
          linear_combination h1
        omega
    obtain ⟨⟨K', rfl⟩, ⟨w', rfl⟩⟩ := hKw
    -- the halved triple is again a solution
    have hc' : c' = 0 :=
      ih c' K' w' (by omega) (by linarith [h1]) (by linarith [h2])
    rw [hc']
    norm_num

/-- If `a` and `b` are odd, Heron's formula and `4 R K = a b c` force `c = 0`. -/
lemma core {a b c K R : ℤ} (ha : Odd a) (hb : Odd b)
    (hA : (4 * K) ^ 2 = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c))
    (hR : 4 * R * K = a * b * c) : c = 0 := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  -- `4 ∣ c`, because `a * b` is odd
  obtain ⟨c', rfl⟩ : (4 : ℤ) ∣ c :=
    ⟨(2 * k + 1) * (2 * l + 1) * R * K - (2 * k * l + k + l) * (2 * k * l + k + l + 1) * c, by
      linear_combination (-((2 * k + 1) * (2 * l + 1))) * hR⟩
  -- `k (k + 1)` and `l (l + 1)` are even; this gives `b² - a² ≡ 0 (mod 8)`
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self l
  -- Heron's formula becomes `16 K² + 64 w'² = 64 b² c'²` with `w' = s - r + 2 c'²`
  have h16 : 16 * K ^ 2 + (8 * s - 8 * r + 16 * c' ^ 2) ^ 2
      = 64 * ((2 * l + 1) ^ 2 * c' ^ 2) := by
    linear_combination hA
      + (-4 * ((8 * s - 8 * r + 16 * c' ^ 2)
          + (4 * (l * (l + 1)) - 4 * (k * (k + 1)) + 16 * c' ^ 2))) * hs
      + (4 * ((8 * s - 8 * r + 16 * c' ^ 2)
          + (4 * (l * (l + 1)) - 4 * (k * (k + 1)) + 16 * c' ^ 2))) * hr
  -- hence `K` is even
  have hK : Even K := by
    have h : Even (K * K) :=
      ⟨2 * ((2 * l + 1) ^ 2 * c' ^ 2 - (s - r + 2 * c' ^ 2) ^ 2), by linarith [h16]⟩
    exact (Int.even_mul.1 h).elim id id
  obtain ⟨K', rfl⟩ := hK
  -- and the descent applies
  have hc' : c' = 0 :=
    descent (odd_two_mul_add_one k) (odd_two_mul_add_one l) c'.natAbs c' K'
      (s - r + 2 * c' ^ 2) le_rfl (by linarith [h16]) (by linarith [hR])
  rw [hc']
  norm_num

/-- Modulo 2, Heron's formula says the perimeter is even. -/
lemma perimeter_even_aux : ∀ α β γ κ : ZMod 2,
    (4 * κ) ^ 2 = (α + β + γ) * (-α + β + γ) * (α - β + γ) * (α + β - γ) → α + β + γ = 0 := by
  decide

end OMA.A392943

open OMA.A392943 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392943.main := by
  rintro ⟨a, b, c, K, R, ha, hb, hc, -, -, -, hgcd, -, hArea, -, hR⟩
  have hA : (4 * (K : ℤ)) ^ 2
      = ((a : ℤ) + b + c) * (-(a : ℤ) + b + c) * ((a : ℤ) - b + c) * ((a : ℤ) + b - c) := hArea
  have hR' : 4 * (R : ℤ) * K = (a : ℤ) * b * c := by exact_mod_cast hR
  -- the perimeter is even
  have hper : (a + b + c) % 2 = 0 := by
    have h2 := congrArg (Int.cast : ℤ → ZMod 2) hA
    push_cast at h2
    have h0 : ((a + b + c : ℕ) : ZMod 2) = 0 := by
      push_cast
      exact perimeter_even_aux _ _ _ _ h2
    have := (ZMod.natCast_eq_zero_iff (a + b + c) 2).1 h0
    omega
  -- the sides are not all even
  have hnot : ¬ (a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0) := by
    rintro ⟨h1, h2, h3⟩
    have hdvd : 2 ∣ Nat.gcd (Nat.gcd a b) c :=
      Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2))
        (Nat.dvd_of_mod_eq_zero h3)
    rw [hgcd] at hdvd
    omega
  -- so exactly one side is even; apply `core` with that side in the last position
  have hcases : (a % 2 = 1 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ c % 2 = 1) ∨ (b % 2 = 1 ∧ c % 2 = 1) := by
    omega
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h0 : (c : ℤ) = 0 :=
      core (Nat.odd_iff.2 h1).natCast (Nat.odd_iff.2 h2).natCast hA hR'
    omega
  · have h0 : (b : ℤ) = 0 :=
      core (a := (a : ℤ)) (b := (c : ℤ)) (c := (b : ℤ)) (K := (K : ℤ)) (R := (R : ℤ))
        (Nat.odd_iff.2 h1).natCast (Nat.odd_iff.2 h2).natCast
        (by linear_combination hA) (by linear_combination hR')
    omega
  · have h0 : (a : ℤ) = 0 :=
      core (a := (b : ℤ)) (b := (c : ℤ)) (c := (a : ℤ)) (K := (K : ℤ)) (R := (R : ℤ))
        (Nat.odd_iff.2 h1).natCast (Nat.odd_iff.2 h2).natCast
        (by linear_combination hA) (by linear_combination hR')
    omega
