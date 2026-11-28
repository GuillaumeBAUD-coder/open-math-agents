import OMAStatements.S_oeis_a397588
import Mathlib.Tactic

-- Problem: A397588: G.f. A(x) satisfies A(x) = x + (x*A(x)^2)'.
-- Upstream: statements/oeis-a397588.lean (declaration OMA.S_oeis_a397588.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A397588

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma antidiag_sq_even_zmod2 (f : ℕ → ZMod 2) (m : ℕ) :
    (∑ p ∈ Finset.antidiagonal (2 * m), f p.1 * f p.2) = f m := by
  let S := Finset.antidiagonal (2 * m)
  let Slt := S.filter (fun p => p.1 < p.2)
  let Sgt := S.filter (fun p => p.2 < p.1)
  let Seq := S.filter (fun p => p.1 = p.2)
  have hpart : S = Slt ∪ (Sgt ∪ Seq) := by
    ext p
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr (Or.inr ⟨hp, h⟩)
      · exact Or.inr (Or.inl ⟨hp, h⟩)
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hd1 : Disjoint Slt (Sgt ∪ Seq) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    omega
  have hd2 : Disjoint Sgt Seq := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Sgt, Seq, Finset.mem_filter] at hp1 hp2
    omega
  have hswap : (∑ p ∈ Slt, f p.1 * f p.2) = ∑ p ∈ Sgt, f p.1 * f p.2 := by
    refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      omega
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap,
        Prod.snd_swap] at hq ⊢
      omega
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap, mul_comm]
  have hSeq : Seq = {(m, m)} := by
    ext p
    simp only [Seq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
      Prod.ext_iff]
    omega
  change ∑ p ∈ S, f p.1 * f p.2 = f m
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hswap, ← add_assoc,
    zmod2_add_self, zero_add, hSeq, Finset.sum_singleton, zmod2_mul_self]

lemma coeff_mod2_eq (A : PowerSeries ℤ)
    (hA : A = PowerSeries.X + PowerSeries.derivative ℤ (PowerSeries.X * A ^ 2)) (n : ℕ) :
    ((A.coeff n : ℤ) : ZMod 2) =
      (if n = 1 then (1 : ZMod 2) else 0) +
      ((n + 1 : ℕ) : ZMod 2) *
        ∑ p ∈ Finset.antidiagonal n, ((A.coeff p.1 : ℤ) : ZMod 2) * ((A.coeff p.2 : ℤ) : ZMod 2) := by
  have h := congrArg (PowerSeries.coeff n) hA
  rw [map_add, PowerSeries.coeff_X, PowerSeries.coeff_derivative,
    mul_comm PowerSeries.X (A ^ 2), PowerSeries.coeff_succ_mul_X, sq, PowerSeries.coeff_mul] at h
  have hz := congrArg (Int.cast : ℤ → ZMod 2) h
  push_cast at hz
  rw [hz]
  congr 1
  push_cast
  ring

end OMA.A397588

theorem OMA.solution : type_of% @OMA.S_oeis_a397588.main := by
  intro A _ hA n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hc := OMA.A397588.coeff_mod2_eq A hA n
    by_cases h1 : n = 1
    · subst h1
      have h2 : ((1 + 1 : ℕ) : ZMod 2) = 0 := by decide
      rw [if_pos rfl, h2, zero_mul, add_zero] at hc
      rw [hc]
      exact ⟨fun _ => ⟨0, by norm_num⟩, fun _ => rfl⟩
    · have hn2 : 2 ≤ n := by omega
      rw [if_neg h1, zero_add] at hc
      rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm1 : 1 ≤ m := by omega
        have hm_lt : m < m + m := by omega
        have h2m : m + m = 2 * m := by omega
        rw [h2m] at hc ⊢
        have hodd : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
          push_cast
          have h20 : (2 : ZMod 2) = 0 := by decide
          rw [h20, zero_mul, zero_add]
        rw [hodd, one_mul, OMA.A397588.antidiag_sq_even_zmod2 (fun i => ((A.coeff i : ℤ) : ZMod 2)) m] at hc
        rw [hc, ih m (by omega) hm1]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [hk, pow_succ']⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k =>
            rw [pow_succ'] at hk
            exact ⟨k, by omega⟩
      · have hev : ((2 * m + 1 + 1 : ℕ) : ZMod 2) = 0 := by
          have : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
          rw [this]
          push_cast
          have h20 : (2 : ZMod 2) = 0 := by decide
          rw [h20, zero_mul]
        rw [hev, zero_mul] at hc
        rw [hc]
        constructor
        · intro h01
          exact False.elim ((by decide : (0 : ZMod 2) ≠ 1) h01)
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k =>
            rw [pow_succ'] at hk
            omega
