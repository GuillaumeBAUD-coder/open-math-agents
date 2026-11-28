import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

/-!
Embedding an interval extremizer into a prime cyclic group without creating progressions.

Take a prime p with 2N < p ≤ 4N (Bertrand) and a k-progression-free S ⊆ [1, N] of size r k N,
and let A be the image of S in ZMod p. If a + i d ∈ A for all i < k, lift the terms to x i ∈ S.
Consecutive differences x (i+1) - x i are integers of absolute value < N that are all congruent
to d modulo p > 2N, so they are equal: the x i form an integer progression. If d ≠ 0 its step is
nonzero, and after reversing it if the step is negative it is a k-term progression with positive
step inside S, a contradiction.
-/

open Finset Erdos142


lemma OMA.noAP_of_free {S : Set ℕ} {k : ℕ} (hk : 1 < k) (hS : S.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  rintro ⟨a, d, hd, h⟩
  have hinj : Function.Injective (fun i : ℕ => a + i * d) := fun i j hij =>
    Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  let T : Finset ℕ := (range k).image fun i => a + i * d
  have hc : T.card = k := by simp [T, card_image_of_injective _ hinj]
  have hT : (T : Set ℕ).IsAPOfLength k := ⟨a, d, by simp [hc], by ext x; simp [T]⟩
  have hsub : (T : Set ℕ) ⊆ S := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact h i (mem_range.mp hi)
  have := hS T hsub hT
  exact absurd this (by exact_mod_cast not_le.mpr hk)

lemma OMA.exists_extremal {k : ℕ} (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  have hne : ({Finset.card S | (S) (_ : S ⊆ Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)} : Set ℕ).Nonempty := by
    refine ⟨0, ∅, by simp, ?_, rfl⟩
    intro t ht h
    have h0 : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have := h.card
    simp [h0] at this
    simp [← this]
  have hb : BddAbove ({Finset.card S | (S) (_ : S ⊆ Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)} : Set ℕ) := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem hne hb
  exact ⟨S, hS, hf, he⟩

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  intro k N hk hN
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  obtain ⟨S, hS, hfree, hcard⟩ := OMA.exists_extremal (k := k) N
  have hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N := fun x hx => mem_Icc.mp (hS hx)
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) S := by
    intro x hx y hy hxy
    have h := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    have := hb x hx
    have := hb y hy
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  refine ⟨p, hp, S.image (fun x : ℕ => (x : ZMod p)), hlo, by omega, ?_, ?_⟩
  · rw [card_image_of_injOn hinj, hcard]
  intro a d h
  by_contra hd
  have h' : ∀ i, i < k → ∃ x, x ∈ S ∧ (x : ZMod p) = a + (i : ZMod p) * d := fun i hi => by
    simpa using mem_image.mp (h ⟨i, hi⟩)
  choose! x hxS hx using h'
  set δ : ℤ := (x 1 : ℤ) - x 0 with hδ
  have hdδ : ((δ : ℤ) : ZMod p) = d := by
    simp [hδ, hx 1 (by omega), hx 0 (by omega)]
  have key : ∀ i, i < k → (x i : ℤ) = x 0 + i * δ := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hi' := ih (by omega)
      have hz : (((x (i + 1) : ℤ) - x i - δ : ℤ) : ZMod p) = 0 := by
        simp [hdδ, hx (i + 1) hi, hx i (by omega)]
        ring
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
      have b1 := hb _ (hxS (i + 1) hi)
      have b2 := hb _ (hxS i (by omega))
      have b3 := hb _ (hxS 1 (by omega))
      have b4 := hb _ (hxS 0 (by omega))
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
      push_cast
      linarith
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hd
    rw [← hdδ, h0]
    simp
  rcases lt_or_gt_of_ne hδ0 with hneg | hpos
  · refine OMA.noAP_of_free (by omega) hfree ⟨x (k - 1), (-δ).toNat, by omega, fun i hi => ?_⟩
    have e : x (k - 1) + i * (-δ).toNat = x (k - 1 - i) := by
      have h1 := key (k - 1) (by omega)
      have h2 := key (k - 1 - i) (by omega)
      have h3 : ((-δ).toNat : ℤ) = -δ := Int.toNat_of_nonneg (by omega)
      have h4 : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - i := by omega
      have h5 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have : ((x (k - 1) + i * (-δ).toNat : ℕ) : ℤ) = x (k - 1 - i) := by
        push_cast
        rw [h3, h1, h2, h4, h5]
        ring
      exact_mod_cast this
    rw [e]
    exact hxS _ (by omega)
  · refine OMA.noAP_of_free (by omega) hfree ⟨x 0, δ.toNat, by omega, fun i hi => ?_⟩
    have e : x 0 + i * δ.toNat = x i := by
      have h1 := key i hi
      have h3 : (δ.toNat : ℤ) = δ := Int.toNat_of_nonneg (by omega)
      have : ((x 0 + i * δ.toNat : ℕ) : ℤ) = x i := by
        push_cast
        rw [h3, h1]
      exact_mod_cast this
    rw [e]
    exact hxS _ hi
