import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1
-- Credit: @LAPRAI
-- The lemmas no_positive_step and extremizer are copied from reduction lower.R1.H2.R1 (credit @NicholasWierenga).

open Finset Real Erdos142

namespace OMA.Erdos142_lower_R1_H2_R3_H1_R1_H2

lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (Finset.range k).image fun i => a + i * d
  have hcard : T.card = k := by
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap' : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  have hle := hfree (T : Set ℕ) hsub hap'
  exact (not_le_of_gt hk) (by exact_mod_cast hle)

lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

end OMA.Erdos142_lower_R1_H2_R3_H1_R1_H2

open OMA.Erdos142_lower_R1_H2_R3_H1_R1_H2 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨S, hS, hfree, hcard⟩ := extremizer (show 1 < k by omega) N
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hSp : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.mp (hS hx)
  refine ⟨p, hp, S.image (fun x : ℕ => (x : ZMod p)), hlo, by omega, ?_, ?_⟩
  · rw [← hcard, Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have h := congrArg ZMod.val hxy
    simp only [ZMod.val_natCast] at h
    have hx' := hSp x hx; have hy' := hSp y hy
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  · intro a d hall
    by_contra hd
    -- the lifted terms
    set x : ℕ → ℕ := fun i => (a + (i : ZMod p) * d).val with hxdef
    have hmem : ∀ i < k, x i ∈ S := by
      intro i hi
      obtain ⟨s, hs, hs'⟩ := Finset.mem_image.mp (hall ⟨i, hi⟩)
      have : x i = s := by
        simp only [hxdef]
        rw [← hs', ZMod.val_natCast, Nat.mod_eq_of_lt (by have := hSp s hs; omega)]
      exact this ▸ hs
    have hcast : ∀ i, ((x i : ℕ) : ZMod p) = a + (i : ZMod p) * d := fun i => by
      simp only [hxdef, ZMod.natCast_zmod_val]
    have hrec : ∀ i, i + 2 < k → x (i + 2) + x i = 2 * x (i + 1) := by
      intro i hi
      have h0 := hSp _ (hmem i (by omega))
      have h1 := hSp _ (hmem (i + 1) (by omega))
      have h2 := hSp _ (hmem (i + 2) (by omega))
      have hz : ((x (i + 2) + x i : ℕ) : ZMod p) = ((2 * x (i + 1) : ℕ) : ZMod p) := by
        push_cast [hcast]; ring
      have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hz
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have hlin : ∀ i, i < k → (x i : ℤ) = x 0 + i * ((x 1 : ℤ) - x 0) := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        match i, ih with
        | 0, _ => simp
        | 1, _ => simp
        | j + 2, ih =>
          have e := hrec j hi
          have e0 := ih j (by omega) (by omega)
          have e1 := ih (j + 1) (by omega) (by omega)
          have e' : (x (j + 2) : ℤ) = 2 * x (j + 1) - x j := by omega
          rw [e', e0, e1]; push_cast; ring
    apply no_positive_step (show 1 < k by omega) hfree
    rcases lt_trichotomy (x 0) (x 1) with h | h | h
    · refine ⟨x 0, x 1 - x 0, by omega, fun i hi => ?_⟩
      have := hlin i hi
      have e : x 0 + i * (x 1 - x 0) = x i := by
        zify [h.le]; linear_combination -this
      rw [e]; exact hmem i hi
    · exfalso; apply hd
      have := hcast 0; have h1 := hcast 1
      rw [h] at this; rw [this] at h1
      simpa using h1
    · refine ⟨x (k - 1), x 0 - x 1, by omega, fun i hi => ?_⟩
      have h1 := hlin (k - 1) (by omega)
      have h2 := hlin (k - 1 - i) (by omega)
      have e : x (k - 1) + i * (x 0 - x 1) = x (k - 1 - i) := by
        have hc1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
        have hc2 : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - i := by omega
        rw [hc1] at h1; rw [hc2] at h2
        zify [h.le]
        linear_combination h1 - h2
      rw [e]; exact hmem _ (by omega)
