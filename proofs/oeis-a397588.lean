import OMAStatements.S_oeis_a397588
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a397588.Proof

/-- Over `ZMod 2`, the `n`-th coefficient of `A²` is `a_{n/2}` for even `n` and `0` for odd `n`. -/
lemma sq_coeff_mod2 (A : PowerSeries ℤ) (n : ℕ) :
    ((coeff n (A ^ 2) : ℤ) : ZMod 2) =
      if n % 2 = 0 then ((coeff (n / 2) A : ℤ) : ZMod 2) else 0 := by
  rw [pow_two, coeff_mul, Int.cast_sum]
  set f : ℕ × ℕ → ZMod 2 := fun p => ((coeff p.1 A * coeff p.2 A : ℤ) : ZMod 2) with hf
  have hswap : ∀ p : ℕ × ℕ, f p + f p.swap = 0 := by
    intro p
    simp only [hf, Prod.fst_swap, Prod.snd_swap, Int.cast_mul]
    rw [mul_comm ((coeff p.2 A : ℤ) : ZMod 2), ← two_mul]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hmem : (m, m) ∈ Finset.HasAntidiagonal.antidiagonal (2 * m) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; ring
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (2 * m)).erase (m, m), f x = 0 := by
      refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hswap p) ?_ ?_ ?_
      · intro p hp _ heq
        rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
        apply hp.1
        have h1 : p.2 = p.1 := congrArg Prod.fst heq
        ext <;> simp <;> omega
      · intro p hp
        rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
        refine ⟨?_, ?_⟩
        · intro h
          apply hp.1
          rw [← Prod.swap_swap p, h]; rfl
        · simp only [Prod.fst_swap, Prod.snd_swap]; omega
      · intro p _
        exact Prod.swap_swap p
    show f (m, m) + _ = _
    rw [hrest, add_zero]
    have h2 : 2 * m / 2 = m := by omega
    rw [h2]
    simp only [hf, Int.cast_mul]
    generalize ((coeff m A : ℤ) : ZMod 2) = x
    fin_cases x <;> rfl
  · refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hswap p) ?_ ?_ ?_
    · intro p hp _ heq
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 : p.2 = p.1 := congrArg Prod.fst heq
      omega
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p _
      exact Prod.swap_swap p

lemma pow2_double (m : ℕ) : (∃ k : ℕ, 2 * m = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by rw [pow_succ]; ring⟩

lemma not_pow2_odd (n : ℕ) (h1 : 1 < n) (h2 : n % 2 = 1) : ¬ ∃ k : ℕ, n = 2 ^ k := by
  rintro ⟨k, rfl⟩
  rcases k with _ | k
  · simp at h1
  · rw [pow_succ] at h2; omega

theorem solution : ∀ A : PowerSeries ℤ, A.coeff 0 = 0 →
    A = PowerSeries.X + PowerSeries.derivative ℤ (PowerSeries.X * A ^ 2) →
    ∀ n : ℕ, 1 ≤ n → (((A.coeff n : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  intro A _ hA
  have hrec : ∀ n : ℕ, ((A.coeff n : ℤ) : ZMod 2) =
      (if n = 1 then 1 else 0) + ((n : ZMod 2) + 1) *
        (if n % 2 = 0 then ((coeff (n / 2) A : ℤ) : ZMod 2) else 0) := by
    intro n
    conv_lhs => rw [hA]
    rw [map_add, coeff_derivative, coeff_succ_X_mul, coeff_X, Int.cast_add, Int.cast_mul,
      sq_coeff_mod2]
    push_cast
    split_ifs <;> ring
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hrec n]
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      simp only [if_true]
      have : ((1 : ℕ) : ZMod 2) + 1 = 0 := rfl
      rw [this, zero_mul, add_zero]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    · rw [if_neg (by omega)]
      rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
      · subst hm
        have hm1 : 1 ≤ m := by omega
        rw [if_pos (by omega), show 2 * m / 2 = m by omega, pow2_double, ← ih m (by omega) hm1]
        have : ((2 * m : ℕ) : ZMod 2) + 1 = 1 := by
          push_cast
          rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
        rw [this, one_mul, zero_add]
      · rw [if_neg (by omega), mul_zero, add_zero]
        constructor
        · intro h0; exact absurd h0 (by decide)
        · intro h0; exact absurd h0 (not_pow2_odd n (by omega) (by omega))

end OMA.S_oeis_a397588.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a397588.main := OMA.S_oeis_a397588.Proof.solution
