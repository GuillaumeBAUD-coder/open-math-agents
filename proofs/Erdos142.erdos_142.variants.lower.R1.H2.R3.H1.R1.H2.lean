import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H2:
-- Embed an interval extremizer in a prime cyclic group of size in (2N, 4N]
-- without introducing nontrivial k-term arithmetic progressions.
-- Credit: @DPS0340

namespace Erdos142R1H2R3H1R1H2

open Finset Erdos142

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

end Erdos142R1H2R3H1R1H2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  have hk1 : 1 < k := by omega
  obtain ⟨S, hS, hf, hcard⟩ := Erdos142R1H2R3H1R1H2.exists_maximizer hk1 N
  have hno := (Erdos142R1H2R3H1R1H2.apFree_iff hk1).mp hf
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hhi4 : p ≤ 4 * N := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  let A : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : x < p := by
      have := (Finset.mem_Icc.mp (hS hx)).2
      omega
    have hylt : y < p := by
      have := (Finset.mem_Icc.mp (hS hy)).2
      omega
    have hval := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hval
  have hAcard : Erdos142.r k N = A.card := by
    rw [hcard, Finset.card_image_of_injOn hinj]
  refine ⟨p, hp, A, hlo, hhi4, hAcard, ?_⟩
  intro a d hAP
  have hex : ∀ i : Fin k, ∃ x ∈ S, (x : ZMod p) = a + (i.val : ZMod p) * d := fun i =>
    Finset.mem_image.mp (hAP i)
  choose x hxS hxEq using hex
  have hxle : ∀ i : Fin k, x i ≤ N := fun i => (Finset.mem_Icc.mp (hS (hxS i))).2
  have hmid : ∀ i : ℕ, ∀ hi : i + 2 < k,
      x ⟨i, by omega⟩ + x ⟨i + 2, hi⟩ = 2 * x ⟨i + 1, by omega⟩ := by
    intro i hi
    have h1 : x ⟨i, by omega⟩ + x ⟨i + 2, hi⟩ < p := by
      have := hxle ⟨i, by omega⟩
      have := hxle ⟨i + 2, hi⟩
      omega
    have h2 : 2 * x ⟨i + 1, by omega⟩ < p := by
      have := hxle ⟨i + 1, by omega⟩
      omega
    have hmod : ((x ⟨i, by omega⟩ + x ⟨i + 2, hi⟩ : ℕ) : ZMod p) =
        ((2 * x ⟨i + 1, by omega⟩ : ℕ) : ZMod p) := by
      push_cast
      rw [hxEq ⟨i, by omega⟩, hxEq ⟨i + 2, hi⟩, hxEq ⟨i + 1, by omega⟩]
      simp only [Nat.cast_add, Nat.cast_ofNat]
      ring
    have hval := congrArg ZMod.val hmod
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
  let f0 := x ⟨0, by omega⟩
  let f1 := x ⟨1, by omega⟩
  rcases lt_trichotomy f0 f1 with hlt | heq | hgt
  · exfalso
    let δ := f1 - f0
    have hδ : 0 < δ := by omega
    have hlin : ∀ n : ℕ, ∀ hn : n < k, x ⟨n, hn⟩ = f0 + n * δ := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        match n with
        | 0 => simp [f0]
        | 1 => simp [f1, δ]; omega
        | m + 2 =>
          have hm0 := ih m (by omega) (by omega)
          have hm1 := ih (m + 1) (by omega) (by omega)
          have hm := hmid m hn
          have hmul1 : (m + 1) * δ = m * δ + δ := by ring
          have hmul2 : (m + 2) * δ = m * δ + 2 * δ := by ring
          omega
    exact hno ⟨f0, δ, hδ, fun i hi => by
      have := hxS ⟨i, hi⟩
      rwa [hlin i hi] at this⟩
  · have h0 := hxEq ⟨0, by omega⟩
    have h1 := hxEq ⟨1, by omega⟩
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] at h0 h1
    change (f0 : ZMod p) = a at h0
    change (f1 : ZMod p) = a + d at h1
    have hEqA : a = a + d := h0.symm.trans (by rw [heq, h1])
    have hEq0 : a + 0 = a + d := by simpa using hEqA
    exact (add_left_cancel hEq0).symm
  · exfalso
    let δ := f0 - f1
    have hδ : 0 < δ := by omega
    have hlin : ∀ n : ℕ, ∀ hn : n < k, x ⟨n, hn⟩ + n * δ = f0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        match n with
        | 0 => simp [f0]
        | 1 => simp [f1, δ]; omega
        | m + 2 =>
          have hm0 := ih m (by omega) (by omega)
          have hm1 := ih (m + 1) (by omega) (by omega)
          have hm := hmid m hn
          have hmul1 : (m + 1) * δ = m * δ + δ := by ring
          have hmul2 : (m + 2) * δ = m * δ + 2 * δ := by ring
          omega
    refine hno ⟨x ⟨k - 1, by omega⟩, δ, hδ, fun j hj => ?_⟩
    have hk_last := hlin (k - 1) (by omega)
    have hidx := hlin (k - 1 - j) (by omega)
    have hsum : (k - 1 - j) * δ + j * δ = (k - 1) * δ := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have heq' : x ⟨k - 1, by omega⟩ + j * δ = x ⟨k - 1 - j, by omega⟩ := by omega
    rw [heq']
    exact hxS ⟨k - 1 - j, by omega⟩
