import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

namespace E142W

theorem no_ap (k : ℕ) (hk : 2 ≤ k) (S : Finset ℕ) (hS : (S : Set ℕ).IsAPOfLengthFree k)
    (a d : ℕ) (hd : 0 < d) (h : ∀ i < k, a + i * d ∈ S) : False := by
  let f : ℕ → ℕ := fun n => a + n * d
  have hf : Function.Injective f := by
    intro m n hmn
    have : m * d = n * d := by simpa [f] using hmn
    exact Nat.eq_of_mul_eq_mul_right hd this
  have ht : ({x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} : Set ℕ)
      = ((Finset.range k).image f : Set ℕ) := by
    ext x
    simp [f, smul_eq_mul]
  have hsub : ({x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} : Set ℕ)
      ⊆ (S : Set ℕ) := by
    rw [ht]
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact h n hn
  have hap : ({x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} : Set ℕ).IsAPOfLength
      (k : ℕ∞) := by
    refine ⟨a, d, ?_, rfl⟩
    rw [ht, ← Set.encard, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ hf, Finset.card_range]
  have := hS _ hsub hap
  have : k ≤ 1 := by exact_mod_cast this
  omega

end E142W

open Finset in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  intro k N hk hN
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  -- extremizer
  have hne : ({Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} : Set ℕ).Nonempty :=
    ⟨0, ∅, Finset.empty_subset _, by
      intro t ht _
      have : t = ∅ := by simpa using ht
      subst this
      exact absurd ‹_› (Set.not_isAPOfLength_empty (by exact_mod_cast (by omega : 0 < k)))
      , rfl⟩
  have hbdd : BddAbove ({Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} : Set ℕ) := by
    refine ⟨N, ?_⟩
    rintro n ⟨S, hS, _, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hSsub, hSfree, hScard⟩ := Nat.sSup_mem hne hbdd
  have hSle : ∀ x ∈ S, x ≤ N := fun x hx => (Finset.mem_Icc.mp (hSsub hx)).2
  refine ⟨p, hp, S.image (Nat.cast : ℕ → ZMod p), by omega, by omega, ?_, ?_⟩
  · have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (S : Set ℕ) := by
      intro x hx y hy hxy
      have := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
      rwa [Nat.mod_eq_of_lt (by have := hSle x hx; omega),
        Nat.mod_eq_of_lt (by have := hSle y hy; omega)] at this
    rw [Finset.card_image_of_injOn hinj, hScard]
    rfl
  · intro a d had
    by_contra hd0
    have h : ∀ i < k, ∃ x ∈ S, (x : ZMod p) = a + (i : ZMod p) * d := by
      intro i hi
      have := had ⟨i, hi⟩
      simpa using this
    choose! x hxS hx using h
    -- consecutive relation in ℕ
    have hrel : ∀ i, i + 2 < k → x i + x (i + 2) = 2 * x (i + 1) := by
      intro i hi
      have hz : ((x i + x (i + 2) : ℕ) : ZMod p) = ((2 * x (i + 1) : ℕ) : ZMod p) := by
        push_cast
        rw [hx i (by omega), hx (i + 2) hi, hx (i + 1) (by omega)]
        push_cast
        ring
      have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hz
      have h1 := hSle _ (hxS i (by omega))
      have h2 := hSle _ (hxS (i + 2) hi)
      have h3 := hSle _ (hxS (i + 1) (by omega))
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    set δ : ℤ := (x 1 : ℤ) - x 0 with hδ
    have hlin : ∀ i, i + 1 < k →
        (x i : ℤ) = x 0 + i * δ ∧ (x (i + 1) : ℤ) = x 0 + (i + 1) * δ := by
      intro i
      induction i with
      | zero => intro _; simp [hδ]
      | succ n ih =>
        intro hn
        obtain ⟨_, h2⟩ := ih (by omega)
        have hr := hrel n (by omega)
        have hr' : (x n : ℤ) + x (n + 2) = 2 * x (n + 1) := by exact_mod_cast hr
        refine ⟨by push_cast; linarith, ?_⟩
        have e1 := (ih (by omega)).1
        push_cast
        linarith
    have hall : ∀ i < k, (x i : ℤ) = x 0 + i * δ := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [(hlin j (by omega)).2]
        push_cast
        ring
    have hδ0 : δ ≠ 0 := by
      intro h0
      have : x 1 = x 0 := by omega
      have e1 := hx 1 (by omega)
      have e0 := hx 0 (by omega)
      rw [this, e0] at e1
      simp at e1
      exact hd0 e1
    rcases lt_or_gt_of_ne hδ0 with hneg | hpos
    · -- decreasing progression: reverse it
      refine E142W.no_ap k (by omega) S hSfree (x (k - 1)) (x 0 - x 1) (by omega) ?_
      intro i hi
      have key : x (k - 1) + i * (x 0 - x 1) = x (k - 1 - i) := by
        zify [show x 1 ≤ x 0 by omega]
        rw [hall (k - 1) (by omega), hall (k - 1 - i) (by omega)]
        push_cast [show 1 ≤ k by omega, show i ≤ k - 1 by omega]
        rw [hδ]
        ring
      rw [key]
      exact hxS _ (by omega)
    · refine E142W.no_ap k (by omega) S hSfree (x 0) (x 1 - x 0) (by omega) ?_
      intro i hi
      have key : x 0 + i * (x 1 - x 0) = x i := by
        zify [show x 0 ≤ x 1 by omega]
        rw [hall i hi, hδ]
      rw [key]
      exact hxS i hi
