import FormalConjectures.OEIS.«261307»

-- A countdown from a positive value x subtracts g = gcd(x,7n+6).
-- Use b = 7(n+x)+6. A state is sufficient for the induction if b is prime
-- or its least prime factor is at most x. Restarts and unit steps preserve
-- this condition. For nonunit steps there are two different obstructions.
namespace OMA.R_OeisA261307_conjecture_R1

open OeisA261307

-- A nonunit jump straight to zero occurs precisely when x>1 divides 7n+6.
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → 1 < a n → a n ∣ 7*n+6 → Nat.Prime (7*(n+1)+6)

-- For a jump with a positive remainder, only the range x < 2*minFac(b')
-- needs a new argument. Here b' is the post-jump potential. The step
-- asks for a detectable factor of b' in the remaining countdown.
def H2 : Prop :=
  ∀ n : ℕ, 2 < n →
    let x := a n
    let g := Nat.gcd x (7*n+6)
    let b' := 7*(n+1+(x-g))+6
    1 < g → g < x → ¬ Nat.Prime b' → x < 2*b'.minFac → b'.minFac ≤ x-g

theorem recurrence_step (n : ℕ) (hn : 0 < n) :
    a (n+1) = Int.natAbs ((a n : ℤ) - (Nat.gcd (a n) (7*n+6) : ℤ)) := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem restart_value (n : ℕ) (hn : 0 < n) (hz : a n=0) : a (n+1)=7*n+6 := by
  rw [recurrence_step n hn, hz, Nat.gcd_zero_left]
  change Int.natAbs (-(Int.ofNat (7*n+6))) = 7*n+6
  rw [Int.natAbs_neg]
  rfl

theorem positive_step (n : ℕ) (hn : 0 < n) (ha : 0 < a n) :
    a (n+1) = a n - Nat.gcd (a n) (7*n+6) := by
  rw [recurrence_step n hn, ← Int.ofNat_sub (Nat.gcd_le_left _ ha)]
  rfl

set_option maxRecDepth 4096 in
theorem prime_167 : Nat.Prime 167 := by decide

theorem main : H1 → H2 → type_of% @OeisA261307.conjecture := by
  intro habrupt hshort
  let b (i : ℕ) := 7*(i+a i)+6
  have good : ∀ n : ℕ, 2 < n → (b n).Prime ∨ (b n).minFac ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      by_cases hbase : n=2
      · subst n
        left
        have hb : b 3 = 167 := by decide
        rw [hb]
        exact prime_167
      have hn' : 2 < n := by omega
      by_cases hz : a n = 0
      · have hx := restart_value n (by omega) hz
        by_cases hp : (b (n+1)).Prime
        · exact Or.inl hp
        right
        have hpos : 0 < b (n+1) := by dsimp [b]; omega
        have hfac := Nat.minFac_sq_le_self hpos hp
        have hlarge : b (n+1) ≤ (a (n+1))^2 := by
          dsimp [b]
          rw [hx]
          calc
            _ ≤ 20*(7*n+6) := by omega
            _ ≤ (7*n+6)^2 := by
              rw [pow_two]
              exact Nat.mul_le_mul_right _ (by omega)
        by_contra! h
        have := Nat.pow_lt_pow_left h (by decide : (2 : ℕ) ≠ 0)
        omega
      have ha : 0 < a n := by omega
      let g := Nat.gcd (a n) (7*n+6)
      have hstep : a (n+1) = a n-g := positive_step n (by omega) ha
      have hle : g ≤ a n := Nat.gcd_le_left _ ha
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha
      have hgb : g = Nat.gcd (a n) (b n) := by
        dsimp [g,b]
        rw [show 7*(n+a n)+6 = (7*n+6)+7*a n by omega]
        exact (Nat.gcd_add_mul_right_right _ _ _).symm
      by_cases hg : g=1
      · have hsame : b (n+1) = b n := by dsimp [b]; omega
        rw [hsame]
        rcases ih hn' with hp | hf
        · exact Or.inl hp
        right
        have hne : a n ≠ (b n).minFac := by
          intro he
          have hd := Nat.dvd_gcd (show (b n).minFac ∣ a n by rw [he]) (Nat.minFac_dvd (b n))
          rw [← hgb, hg] at hd
          have hb1 : b n ≠ 1 := by dsimp [b]; omega
          exact (Nat.minFac_prime hb1).not_dvd_one hd
        omega
      have hg' : 1 < g := by omega
      by_cases hend : g = a n
      · left
        have hd : a n ∣ 7*n+6 := hend ▸ (Nat.gcd_dvd_right (a n) (7*n+6))
        have hp := habrupt n hn' (by omega) hd
        dsimp [b]
        rw [show a (n+1)=0 by omega, Nat.add_zero]
        exact hp
      by_cases hp : (b (n+1)).Prime
      · exact Or.inl hp
      right
      have hd : g ∣ a (n+1) := by
        rw [hstep]
        exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.dvd_refl _)
      have hrem := Nat.le_of_dvd (by omega : 0 < a (n+1)) hd
      by_cases hshortRange : a n < 2*(b (n+1)).minFac
      · have hb' : b (n+1) = 7*(n+1+(a n-g))+6 := by dsimp [b]; rw [hstep]
        rw [hb'] at hp hshortRange ⊢
        rw [hstep]
        exact hshort n hn' hg' (by omega) hp hshortRange
      · omega
  intro n hn hz
  rcases good n hn with hp | hf
  · simpa [b,hz] using hp
  · have hb1 : b n ≠ 1 := by dsimp [b]; omega
    have := (Nat.minFac_prime hb1).pos
    omega

end OMA.R_OeisA261307_conjecture_R1
