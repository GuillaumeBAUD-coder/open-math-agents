import FormalConjectures.Wikipedia.RefactorableNumber

/-!
Reduction of the refactorable-triple theorem to a fourth-power criterion and
Ljunggren's equation. The elementary odd-square argument is proved below.
-/

-- Reduction RefactorableNumber.no_three_consecutive_refactorable.R1 of Zelinsky's Theorem (2002)
-- Credit: @limaries30
-- Following Joshua Zelinsky, J. Integer Sequences 5 (2002), Article 02.2.8, Theorem 59.
-- https://cs.uwaterloo.ca/journals/JIS/VOL5/Zelinsky/zelinsky9.pdf
-- H1 isolates the divisor-count and quadratic-residue argument.
-- H2 is the independent Ljunggren equation classification.
-- Neither hypothesis is proved here; this is a conditional reduction.

namespace OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1

/-- The odd prime exponents of a refactorable successor of an odd square are
divisible by four, so that successor is twice a fourth power. -/
def H1 : Prop :=
  ∀ x : ℕ, Odd x → (x ^ 2 + 1).IsRefactorable →
    ∃ y : ℕ, x ^ 2 + 1 = 2 * y ^ 4

/-- Ljunggren: the only nonnegative first coordinates are 1 and 239. -/
def H2 : Prop :=
  ∀ x y : ℕ, x ^ 2 + 1 = 2 * y ^ 4 → x = 1 ∨ x = 239

lemma odd_refactorable_square {n : ℕ} (hn : n.IsRefactorable) (ho : Odd n) :
    ∃ x : ℕ, n = x ^ 2 := by
  have hn0 : n ≠ 0 := by have := hn.pos; omega
  have hcount : Odd n.divisors.card := ho.of_dvd_nat hn.2
  have hexp (p : ℕ) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
    have hd : n.factorization p + 1 ∣ n.divisors.card := by
      rw [Nat.card_divisors hn0]
      exact Finset.dvd_prod_of_mem _ hp
    have := Nat.odd_iff.mp (hcount.of_dvd_nat hd)
    exact Nat.even_iff.mpr (by omega)
  have hs : IsSquare n := by
    rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod]
    apply Finset.isSquare_prod
    intro p hp
    obtain ⟨k, hk⟩ := hexp p (by simpa using hp)
    refine ⟨p ^ k, ?_⟩
    rw [hk, pow_add]
  exact hs.exists_sq

lemma odd_pair_first_eq_one (h1 : H1) (h2 : H2) {n : ℕ}
    (ho : Odd n) (hn : n.IsRefactorable) (hs : (n + 1).IsRefactorable) : n = 1 := by
  obtain ⟨x, hx⟩ := odd_refactorable_square hn ho
  have hxo : Odd x := (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp (hx ▸ ho)
  obtain ⟨y, hy⟩ := h1 x hxo (by simpa [hx] using hs)
  rcases h2 x y hy with h | h
  · simpa [h] using hx
  · have hnval : n = 57121 := by norm_num [h] at hx; exact hx
    have bad : ¬ Nat.IsRefactorable 57122 := by decide +kernel
    exact False.elim (bad (by simpa [hnval] using hs))

theorem main : H1 → H2 → type_of% @RefactorableNumber.no_three_consecutive_refactorable := by
  intro h1 h2 n h
  rcases h with ⟨hn, hn1, hn2⟩
  rcases Nat.even_or_odd n with he | ho
  · have hodd : Odd (n + 1) := he.add_odd (by decide)
    have hsmall := odd_pair_first_eq_one h1 h2 hodd hn1 (by simpa [Nat.add_assoc] using hn2)
    have := hn.pos
    omega
  · have hsmall := odd_pair_first_eq_one h1 h2 ho hn hn1
    have bad : ¬ Nat.IsRefactorable 3 := by decide
    exact bad (by simpa [hsmall] using hn2)

end OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1
