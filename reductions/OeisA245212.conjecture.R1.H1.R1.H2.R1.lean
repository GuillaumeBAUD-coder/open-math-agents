import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1

/-! A reduction of the remaining odd A245212 branch. The quantitative H3 is
proved independently at the permanent source cited in the pull request. -/

namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Remaining odd inputs outside four-prime factorizations with least prime three. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n → 2 * n.totient < n →
    (¬ ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3 ≤ p ∧ 5 ≤ q ∧
      0 < e ∧ 0 < f ∧ n = p^e*q^f) →
    (¬ ∃ k p q r e f g : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧
      5 ≤ p ∧ p < q ∧ q < r ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ n = 3^k*p^e*q^f*r^g) →
    OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- Four prime factors with least prime three, whose exponent is at least two. -/
def H2 : Prop :=
  ∀ k p q r e f g : ℕ, 2 ≤ k → p.Prime → q.Prime → r.Prime →
    5 ≤ p → p < q → q < r → 0 < e → 0 < f → 0 < g →
    let n := 3^k*p^e*q^f*r^g
    2 * n.totient < n → OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- The sharp quantitative gap when the exponent of the least prime three is one. -/
def H3 : Prop :=
  ∀ p q r e f g : ℕ, p.Prime → q.Prime → r.Prime →
    5 ≤ p → p < q → q < r → 0 < e → 0 < f → 0 < g →
    let n := 3*p^e*q^f*r^g
    37*(n:ℤ)*n.divisors.card ≤ 288*(OeisA245212.a n - (σ 1 n : ℤ))

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R1_H1_R1.H2 := by
  intro outside deep gap n hn ho hpp hphi htwo
  by_cases form : ∃ k p q r e f g : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧
      5 ≤ p ∧ p < q ∧ q < r ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ n = 3^k*p^e*q^f*r^g
  · obtain ⟨k,p,q,r,e,f,g,hk,hp,hq,hr,hp5,hpq,hqr,he,hf,hg,rfl⟩ := form
    by_cases hk1 : k = 1
    · subst k
      simp only [pow_one] at hn ⊢
      let m := 3*p^e*q^f*r^g
      have hm : 0 < m := by change 0 < 3*p^e*q^f*r^g; omega
      have hc : 0 < m.divisors.card :=
        card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm.ne'⟩
      have H := gap p q r e f g hp hq hr hp5 hpq hqr he hf hg
      change 37*(m:ℤ)*m.divisors.card ≤
        288*(OeisA245212.a m - (σ 1 m : ℤ)) at H
      intro heq
      rw [heq, sub_self, mul_zero] at H
      exact (not_lt_of_ge H)
        (mul_pos (mul_pos (by decide) (by exact_mod_cast hm)) (by exact_mod_cast hc))
    · exact deep k p q r e f g (by omega) hp hq hr hp5 hpq hqr he hf hg hphi
  · exact outside n hn ho hpp hphi htwo form

end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1
