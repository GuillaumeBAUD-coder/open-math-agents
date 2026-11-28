import OMAReductions.R_arxiv_1801_04770_R1
import Mathlib

namespace SquareProduct

theorem large_power {a n : ℕ} (ha : 2 < a) (hn : 0 < n) : 2 < a ^ n :=
  lt_of_lt_of_le ha (le_self_pow (by omega) hn.ne')

/- The first factor lies strictly between consecutive squares. -/
theorem not_square {a n : ℕ} (ha : 2 < a) (hn : 6 < n) (he : Even n)
    (y : ℕ) : y ^ 2 ≠ a ^ n - 2 := by
  obtain ⟨h, rfl⟩ := he
  let t := a ^ h
  have ht : 2 < t := large_power ha (by omega)
  have hpow : a ^ (h+h) = t*t := pow_add _ _ _
  rw [hpow]
  intro eqn
  have near : y^2 + 2 = t*t := by
    have : 2 ≤ t*t := by nlinarith
    omega
  by_cases below : y < t
  · have h := Nat.mul_self_le_mul_self (by omega : y+1 ≤ t)
    nlinarith
  · have h := Nat.mul_self_le_mul_self (by omega : t ≤ y)
    nlinarith

/- Twice a square is also impossible. Equality forces a even, hence
16 divides its nth power, whereas twice a square plus two never vanishes
modulo 16. The residue calculation is independent of the exponent. -/
theorem not_twice_square {a n : ℕ} (ha : 2 < a) (hn : 6 < n)
    (y : ℕ) : y ^ 2 * 2 ≠ a ^ n - 2 := by
  intro bad
  have size := large_power ha (by omega : 0 < n)
  have eqn : a ^ n = y^2 * 2 + 2 := by omega
  have twoDiv : 2 ∣ a ^ n := ⟨y^2 + 1, by rw [eqn]; ring⟩
  have evenA := Nat.prime_two.dvd_of_dvd_pow twoDiv
  have div16 : 2 ^ 4 ∣ a ^ n :=
    (pow_dvd_pow_of_dvd evenA 4).trans (pow_dvd_pow a (by omega))
  have impossible : ¬ 16 ∣ y^2 * 2 + 2 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at hz
    have residues : ∀ v : ZMod 16, v ^ 2 * 2 + 2 ≠ 0 := by decide
    exact residues (y : ZMod 16) hz
  exact impossible (eqn ▸ div16)

theorem odd_factor {D : ℕ} (sqf : Squarefree D) (large : 2 < D) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ D := by
  by_cases h : 2 ∣ D
  · obtain ⟨t, ht⟩ := h
    obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
    have ne : q ≠ 2 := by
      intro same
      subst q
      exact (Nat.squarefree_iff_prime_squarefree.mp sqf 2 Nat.prime_two)
        (ht ▸ Nat.mul_dvd_mul_left 2 hqt)
    exact ⟨q, hq, ne, hqt.trans ⟨2, by simpa [Nat.mul_comm] using ht⟩⟩
  · obtain ⟨q, hq, divides⟩ := Nat.exists_prime_and_dvd (by omega : D ≠ 1)
    exact ⟨q, hq, fun same => h (same ▸ divides), divides⟩

end SquareProduct

theorem OMA.solution : OMA.R_arxiv_1801_04770_R1.H1 := by
  intro a b n x ha hab hn evenN eqn
  have aLarge := SquareProduct.large_power ha (by omega : 0 < n)
  have bLarge := SquareProduct.large_power (by omega : 2 < b) (by omega : 0 < n)
  let A := a ^ n - 2
  let B := b ^ n - 2
  have hA : 0 < A := by dsimp [A]; omega
  have hB : 0 < B := by dsimp [B]; omega
  have product : A * B = x ^ 2 := by
    dsimp [A, B]
    zify [aLarge.le, bLarge.le]
    exact eqn
  obtain ⟨D, y, posD, posY, rep, sqf⟩ := Nat.sq_mul_squarefree_of_pos hA
  have bigD : 2 < D := by
    by_contra! small
    interval_cases D
    · exact SquareProduct.not_square ha hn evenN y (by simpa using rep)
    · exact SquareProduct.not_twice_square ha hn y rep
  obtain ⟨q, hq, oddQ, divides⟩ := SquareProduct.odd_factor sqf bigD
  have single := Nat.factorization_eq_one_of_squarefree sqf hq divides
  have vA := congrArg (fun z : ℕ => z.factorization q) rep
  simp only [Nat.factorization_mul (pow_ne_zero _ posY.ne') posD.ne',
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, single] at vA
  have vProd := congrArg (fun z : ℕ => z.factorization q) product
  simp only [Nat.factorization_mul hA.ne' hB.ne', Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at vProd
  change ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Odd (A.factorization q) ∧ Odd (B.factorization q)
  refine ⟨q,hq,oddQ, ⟨y.factorization q, by omega⟩, ?_⟩
  refine ⟨x.factorization q - y.factorization q - 1, ?_⟩
  omega
