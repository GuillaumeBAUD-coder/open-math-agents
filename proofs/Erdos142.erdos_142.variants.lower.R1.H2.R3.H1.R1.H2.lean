import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: take an extremal k-AP-free set S in [1, N] (sSup of a bounded nonempty set of naturals
-- is attained), a prime p in (2N, 4N] by Bertrand, and A the image of S in ZMod p (injective since
-- N < p). If a + i*d lies in A for all i < k with d nonzero, lift the terms to x_i in S; consecutive
-- integer differences are congruent mod p and smaller than 2N < p in absolute value, so they are all
-- equal to a nonzero integer delta, and S contains a genuine k-term progression (read forwards or
-- backwards), contradicting freeness.

open Finset Erdos142

namespace OMA.P_Erdos142_lower_R1_H2_R3_H1_R1_H2


lemma oma_free_empty (k : ℕ) : ((∅ : Finset ℕ) : Set ℕ).IsAPOfLengthFree k := by
  intro t ht hap
  have h0 : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
  subst h0
  have h := hap.card
  simp at h
  rw [← h]
  norm_num

lemma oma_not_free {S : Finset ℕ} {k : ℕ} (hk : 2 ≤ k) (hS : (S : Set ℕ).IsAPOfLengthFree k)
    (a d : ℕ) (hd : 0 < d) (h : ∀ i < k, a + i * d ∈ S) : False := by
  classical
  let T : Finset ℕ := (Finset.range k).image (fun n => a + n * d)
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro m n hmn
    simp only at hmn
    have : m * d = n * d := by omega
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hTcard : T.card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : (T : Set ℕ) ⊆ (S : Set ℕ) := by
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact h n hn
  have hap : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · show Set.encard (T : Set ℕ) = k
      rw [Set.encard_coe_eq_coe_finsetCard, hTcard]
    · ext x
      simp only [T, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
        Set.mem_ofPred_eq, smul_eq_mul, Nat.cast_lt]
      constructor
      · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  have := hS _ hsub hap
  have : (k : ℕ∞) ≤ 1 := this
  norm_cast at this
  omega

end OMA.P_Erdos142_lower_R1_H2_R3_H1_R1_H2

open OMA.P_Erdos142_lower_R1_H2_R3_H1_R1_H2 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  set M : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)} with hM
  have hne : M.Nonempty := ⟨0, ∅, by simp, oma_free_empty k, by simp⟩
  have hbdd : BddAbove M := by
    refine ⟨N, ?_⟩
    rintro n ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hSsub, hSfree, hScard⟩ := Nat.sSup_mem hne hbdd
  have hr : r k N = S.card := by
    rw [hScard]; rfl
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hSb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N := fun x hx => by
    simpa using hSsub hx
  refine ⟨p, hp, S.image (fun x : ℕ => (x : ZMod p)), hlt, by omega, ?_, ?_⟩
  · rw [hr, Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have h := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    have hx' := hSb x hx; have hy' := hSb y hy
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  · intro a d hall
    by_contra hd
    have hex : ∀ i : Fin k, ∃ x ∈ S, (x : ZMod p) = a + (i.val : ZMod p) * d := by
      intro i
      simpa using hall i
    choose x hxS hxa using hex
    have hk0 : 0 < k := by omega
    have hk1 : 1 < k := by omega
    let x0 : ℕ := x ⟨0, hk0⟩
    let x1 : ℕ := x ⟨1, hk1⟩
    set δ : ℤ := (x1 : ℤ) - x0 with hδ
    have hdδ : d = ((δ : ℤ) : ZMod p) := by
      have e1 := hxa ⟨1, hk1⟩
      have e0 := hxa ⟨0, hk0⟩
      simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero] at e1 e0
      rw [hδ]; push_cast
      show d = ((x ⟨1, hk1⟩ : ℕ) : ZMod p) - ((x ⟨0, hk0⟩ : ℕ) : ZMod p)
      rw [e1, e0]; ring
    have hstep : ∀ i (hi : i + 1 < k),
        ((x ⟨i + 1, hi⟩ : ℕ) : ℤ) - (x ⟨i, by omega⟩ : ℕ) = δ := by
      intro i hi
      have e1 := hxa ⟨i + 1, hi⟩
      have e0 := hxa ⟨i, by omega⟩
      have hz : (((((x ⟨i + 1, hi⟩ : ℕ) : ℤ) - (x ⟨i, by omega⟩ : ℕ)) : ℤ) : ZMod p)
          = ((δ : ℤ) : ZMod p) := by
        rw [← hdδ]; push_cast
        rw [e1, e0]; push_cast; ring
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hz
      have b1 := hSb _ (hxS ⟨i + 1, hi⟩)
      have b0 := hSb _ (hxS ⟨i, by omega⟩)
      have c1 := hSb _ (hxS ⟨1, hk1⟩)
      have c0 := hSb _ (hxS ⟨0, hk0⟩)
      have hz0 := Int.eq_zero_of_abs_lt_dvd hz (by
        rw [abs_lt]; constructor <;> simp only [hδ, x0, x1] <;> omega)
      omega
    have hform : ∀ i (hi : i < k), ((x ⟨i, hi⟩ : ℕ) : ℤ) = x0 + i * δ := by
      intro i
      induction i with
      | zero => intro hi; simp [x0]
      | succ j ih =>
        intro hi
        have := hstep j hi
        have := ih (by omega)
        push_cast
        linarith
    have hδ0 : δ ≠ 0 := by
      intro h0; apply hd; rw [hdδ, h0]; simp
    rcases lt_or_gt_of_ne hδ0 with hneg | hpos
    · obtain ⟨e, he⟩ : ∃ e : ℕ, δ = -(e : ℤ) := ⟨δ.natAbs, by omega⟩
      apply oma_not_free (by omega) hSfree (x ⟨k - 1, by omega⟩) e (by omega)
      intro j hj
      have hm : ((x ⟨k - 1, by omega⟩ : ℕ) + j * e : ℕ) = x ⟨k - 1 - j, by omega⟩ := by
        have h1 := hform (k - 1) (by omega)
        have h2 := hform (k - 1 - j) (by omega)
        have : (((x ⟨k - 1, by omega⟩ : ℕ) + j * e : ℕ) : ℤ) = (x ⟨k - 1 - j, by omega⟩ : ℕ) := by
          push_cast
          rw [h1, h2, he]
          push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show j ≤ k - 1 by omega)]
          ring
        exact_mod_cast this
      rw [hm]; exact hxS _
    · obtain ⟨e, he⟩ : ∃ e : ℕ, δ = (e : ℤ) := ⟨δ.natAbs, by omega⟩
      apply oma_not_free (by omega) hSfree x0 e (by omega)
      intro j hj
      have hm : (x0 + j * e : ℕ) = x ⟨j, hj⟩ := by
        have h2 := hform j hj
        have : ((x0 + j * e : ℕ) : ℤ) = (x ⟨j, hj⟩ : ℕ) := by
          push_cast; rw [h2, he]
        exact_mod_cast this
      rw [hm]; exact hxS _
