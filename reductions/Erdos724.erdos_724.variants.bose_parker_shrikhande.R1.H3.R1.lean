import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1

/-! Factor the odd part to reduce to doubled primes and order eighteen. -/

-- Credit: @marcusbuffett
namespace OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1

open Erdos724

/-- Doubled primes other than two and three. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 5 ≤ p →
  ∃ L M : LatinSquare (2*p), L ≠ M ∧ IsOrthogonal L M

/-- The base order when the odd part is a power of three. -/
def H2 : Prop := ∃ L M : LatinSquare 18, L ≠ M ∧ IsOrthogonal L M

/-- The direct product with a pair of orthogonal squares of odd order. -/
def H3 : Prop := ∀ a b : ℕ, Odd b → 3 ≤ b →
  (∃ L M : LatinSquare a, L ≠ M ∧ IsOrthogonal L M) →
  ∃ L M : LatinSquare (a*b), L ≠ M ∧ IsOrthogonal L M

theorem main : H1 → H2 → H3 → OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H3 := by
  intro hp h18 hprod n hn hn10
  let P (v : ℕ) : Prop := ∃ L M : LatinSquare v, L ≠ M ∧ IsOrthogonal L M
  suffices step : ∀ m : ℕ, Odd m → 5 ≤ m →
      ∃ L M : LatinSquare (2*m), L ≠ M ∧ IsOrthogonal L M by
    have hm := step (n/2) (by exact ⟨n/4, by omega⟩) (by omega)
    exact Eq.mp (congrArg P (show 2*(n/2) = n by omega)) hm
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hm5
    by_cases prime : m.Prime
    · exact hp m prime hm5
    obtain ⟨p,pp,q,rfl⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    have hpq := Nat.odd_mul.mp hm
    have p2 := pp.two_le
    have p3 : 3 ≤ p := by obtain ⟨k,h⟩ := hpq.1; omega
    have q3 : 3 ≤ q := by
      obtain ⟨k,h⟩ := hpq.2
      by_contra! hlt
      have : q = 1 := by omega
      simp [this, pp] at prime
    by_cases large : 5 ≤ p
    · exact Eq.mp (congrArg P (Nat.mul_assoc 2 p q)) (hprod (2*p) q hpq.2 q3 (hp p pp large))
    have small : p = 3 := by obtain ⟨k,h⟩ := hpq.1; omega
    subst p
    by_cases q5 : 5 ≤ q
    · have hq := ih q (by omega) hpq.2 q5
      exact Eq.mp (congrArg P (show 2*q*3 = 2*(3*q) by ring)) (hprod (2*q) 3 (by decide) (by decide) hq)
    · have : q = 3 := by obtain ⟨k,h⟩ := hpq.2; omega
      subst q
      exact h18

end OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1
