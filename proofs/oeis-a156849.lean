import OMAStatements.S_oeis_a156849
import Mathlib

/-! Proof for OEIS A156849: `k^2 ≡ 2 (mod 529)` iff `k ≡ 156` or `373 (mod 529)` (checked by `decide` on the residues);
the increasing enumeration of these is `529 ⌊k/2⌋ + 156 + 217 (k mod 2)`, identified with `Nat.nth`;
the closed form follows by parity and the recurrence from the closed form.
Credit: Sudharsan Rajendiran -/

namespace OMA.P156849
open OMA.S_oeis_a156849

/-- the defining property: `k^2 ≡ 2 (mod 23^2)`. -/
def P (k : ℕ) : Prop := k ^ 2 % 23 ^ 2 = 2

lemma res : ∀ r < 529, (r ^ 2 % 529 = 2 ↔ r = 156 ∨ r = 373) := by decide +kernel

lemma P_iff_mod (k : ℕ) : P k ↔ k % 529 = 156 ∨ k % 529 = 373 := by
  unfold P
  rw [show (23 : ℕ) ^ 2 = 529 by norm_num, Nat.pow_mod]
  exact res _ (Nat.mod_lt _ (by norm_num))

/-- The enumeration `156, 373, 685, 902, …`. -/
def g (k : ℕ) : ℕ := 529 * (k / 2) + 156 + 217 * (k % 2)

lemma g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro k; unfold g; omega

lemma P_iff (m : ℕ) : P m ↔ ∃ k, g k = m := by
  rw [P_iff_mod]
  constructor
  · rintro (h | h)
    · exact ⟨2 * (m / 529), by unfold g; omega⟩
    · exact ⟨2 * (m / 529) + 1, by unfold g; omega⟩
  · rintro ⟨k, rfl⟩
    unfold g
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> omega

lemma nth_eq (k : ℕ) : Nat.nth P k = g k := by
  have hinf : (Set.ofPred P).Infinite := by
    have : Set.range g ⊆ Set.ofPred P := by
      rintro _ ⟨k, rfl⟩; exact (P_iff _).2 ⟨k, rfl⟩
    exact Set.Infinite.mono this (Set.infinite_range_of_injective g_strictMono.injective)
  have hall : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => (hinf hf).elim
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn g ?_ ?_ ?_ (hall k)).symm
  · intro m hm
    obtain ⟨j, hj⟩ := (P_iff m).1 hm
    exact ⟨j, hall j, hj⟩
  · intro j _; exact (P_iff _).2 ⟨j, rfl⟩
  · exact fun a _ b _ h => g_strictMono h

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : 4 * (a n : ℤ) = 1058 * n - 529 - 95 * (-1) ^ n := by
  change 4 * ((Nat.nth P (n - 1) : ℕ) : ℤ) = _
  rw [nth_eq]
  unfold g
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have h1 : (j + j) / 2 = j := by omega
    have h2 : (j + j) % 2 = 0 := by omega
    rw [h1, h2, pow_succ, Even.neg_one_pow ⟨j, rfl⟩]
    push_cast; ring
  · subst hj
    have h1 : (2 * j + 1) / 2 = j := by omega
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    rw [h1, h2, pow_succ, Odd.neg_one_pow ⟨j, rfl⟩]
    push_cast; ring

lemma rec (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3) := by
  have e0 := a_eq n (by omega)
  have e1 := a_eq (n - 1) (by omega)
  have e2 := a_eq (n - 2) (by omega)
  have e3 := a_eq (n - 3) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    Nat.add_sub_cancel] at *
  push_cast at *
  rw [pow_succ, pow_succ, pow_succ] at e0
  rw [pow_succ, pow_succ] at e1
  rw [pow_succ] at e2
  linarith

end OMA.P156849

theorem OMA.solution : type_of% @OMA.S_oeis_a156849.main := by
  constructor
  · intro n hn
    have h := OMA.P156849.rec n hn
    exact_mod_cast h
  · intro n hn
    have h := OMA.P156849.a_eq n hn
    have h' : 4 * (OMA.S_oeis_a156849.a n : ℚ) = 1058 * n - 529 - 95 * (-1) ^ n := by exact_mod_cast h
    linarith
