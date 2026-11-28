import OMAStatements.S_oeis_a014442
import Mathlib

/-!
# Proof for OEIS A014442: every Pythagorean prime is the largest prime factor of some n^2 + 1

`-1` is a square modulo `p`, giving a root `1 ≤ x < p` of `x^2 + 1`; any prime factor `q > p`
of `x^2 + 1` would give `p * q ≤ x^2 + 1 < p^2`.
-/

namespace A014442Proof

private lemma le_of_dvd_small {p n : ℕ} (hp : p.Prime) (hn : n < p) (h : p ∣ n ^ 2 + 1) :
    ∀ q ∈ (n ^ 2 + 1).primeFactors, q ≤ p := by
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqd : q ∣ n ^ 2 + 1 := Nat.dvd_of_mem_primeFactors hq
  by_contra hlt
  have hlt' : p < q := not_le.mp hlt
  have hpq : p * q ∣ n ^ 2 + 1 :=
    Nat.Prime.dvd_mul_of_dvd_ne (Nat.ne_of_lt hlt') hp hqp h hqd
  have hle : p * q ≤ n ^ 2 + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
  have h1 : p * p < p * q := mul_lt_mul_of_pos_left hlt' hp.pos
  have h2 : (n + 1) * (n + 1) ≤ p * p :=
    Nat.mul_le_mul (Nat.succ_le_of_lt hn) (Nat.succ_le_of_lt hn)
  have h3 : n ^ 2 + 1 ≤ (n + 1) * (n + 1) := by nlinarith
  exact absurd (lt_of_lt_of_le h1 (hle.trans (h3.trans h2))) (lt_irrefl _)

private lemma exists_root {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ x : ℕ, 1 ≤ x ∧ x < p ∧ p ∣ x ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨y, hy⟩ := hsq
  have hd : p ∣ y.val ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val]
    linear_combination -hy
  refine ⟨y.val, ?_, ZMod.val_lt y, hd⟩
  rcases Nat.eq_zero_or_pos y.val with h0 | h0
  · exfalso
    have hd' : p ∣ 1 := by simpa [h0] using hd
    exact hp.ne_one (Nat.dvd_one.mp hd')
  · exact h0

end A014442Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a014442.main := by
  intro p hp h4
  obtain ⟨x, hx1, hxp, hxd⟩ := A014442Proof.exists_root hp h4
  exact ⟨x, hx1, hxd, A014442Proof.le_of_dvd_small hp hxp hxd⟩
