import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H2
-- Credit: @mijuny

/-!
# Cyclic group embedding of interval progression-free extremizers via Bertrand's postulate

Given `4 ≤ k` and `2 ≤ N`, Bertrand's postulate provides a prime `p` with `2 * N < p ≤ 4 * N`.
Projecting an extremizer `S ⊆ Finset.Icc 1 N` of size `r k N` into `ZMod p` preserves cardinality
and introduces no non-constant `k`-term progression: lifting any progression in `A ⊆ ZMod p` via
`ZMod.val` yields integers in `[1, N]` whose second differences are divisible by `p` and strictly
bounded by `p` in absolute value, hence vanish identically.
-/

open Finset Real Erdos142

namespace Pre32923

lemma apFree_iff {S : Set ℕ} {k : ℕ} (hk : 1 < k) :
    S.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hS ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ S := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hS _ hsub ⟨a, d, by simp [hcard], hT⟩)
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

lemma eq_zero_of_dvd_of_abs_lt {p Δ : ℤ} (hdvd : p ∣ Δ) (hlo : -p < Δ) (hhi : Δ < p) :
    Δ = 0 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hp : 0 < p := by linarith
  by_cases hm0 : m = 0
  · simp [hm0]
  · rcases lt_or_gt_of_ne hm0 with hneg | hpos
    · have hm1 : m ≤ -1 := by omega
      nlinarith
    · have hm1 : 1 ≤ m := by omega
      nlinarith

theorem prove_H2 : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨p, hp, hlo, hhi'⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hhi : p ≤ 4 * N := by omega
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hk1 : 1 < k := by omega
  obtain ⟨S, hS, hfree, hcard⟩ := exists_maximizer hk1 N
  have hnoAP : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := (apFree_iff hk1).mp hfree
  let A : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hlt_p : ∀ x ∈ S, x < p := by
    intro x hx
    have hxN := (Finset.mem_Icc.mp (hS hx)).2
    omega
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hval := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt (hlt_p x hx), ZMod.val_natCast_of_lt (hlt_p y hy)] using hval
  have hAcard : r k N = A.card := by
    rw [hcard, Finset.card_image_of_injOn hinj]
  refine ⟨p, hp, A, hlo, hhi, hAcard, ?_⟩
  intro a d hAP
  let f (i : ℕ) : ℕ := (a + (i : ZMod p) * d).val
  have hf_mem : ∀ i < k, f i ∈ S := by
    intro i hi
    have hmem := hAP ⟨i, hi⟩
    obtain ⟨x, hxS, hxz⟩ := Finset.mem_image.mp hmem
    have hval : f i = x := by
      dsimp [f]
      rw [← hxz, ZMod.val_natCast_of_lt (hlt_p x hxS)]
    rwa [hval]
  have hf_bounds : ∀ i < k, 1 ≤ f i ∧ f i ≤ N := fun i hi => Finset.mem_Icc.mp (hS (hf_mem i hi))
  have hf_cast : ∀ i : ℕ, ((f i : ℕ) : ZMod p) = a + (i : ZMod p) * d := fun i =>
    ZMod.natCast_zmod_val _
  have hsecond : ∀ i : ℕ, i + 2 < k →
      (f (i + 2) : ℤ) - 2 * (f (i + 1) : ℤ) + (f i : ℤ) = 0 := by
    intro i hi2
    let Δ : ℤ := (f (i + 2) : ℤ) - 2 * (f (i + 1) : ℤ) + (f i : ℤ)
    have hdvd : (p : ℤ) ∣ Δ := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      dsimp [Δ]
      push_cast
      rw [hf_cast (i + 2), hf_cast (i + 1), hf_cast i]
      push_cast
      ring
    have b0 := hf_bounds i (by omega)
    have b1 := hf_bounds (i + 1) (by omega)
    have b2 := hf_bounds (i + 2) hi2
    exact eq_zero_of_dvd_of_abs_lt hdvd (by omega) (by omega)
  let δ : ℤ := (f 1 : ℤ) - (f 0 : ℤ)
  have hlin : ∀ i : ℕ, i < k → (f i : ℤ) = (f 0 : ℤ) + (i : ℤ) * δ := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      match i with
      | 0 => simp
      | 1 => dsimp [δ]; ring
      | i + 2 =>
        have hs := hsecond i hi
        have ih0 := ih i (by omega) (by omega)
        have ih1 := ih (i + 1) (by omega) (by omega)
        push_cast at ih1 ⊢
        linarith
  rcases lt_trichotomy δ 0 with hneg | hzero | hpos
  · exfalso
    let dn : ℕ := (-δ).toNat
    have hdn_pos : 0 < dn := by dsimp [dn]; omega
    have hdn_cast : (dn : ℤ) = -δ := Int.toNat_of_nonneg (by omega)
    apply hnoAP
    refine ⟨f (k - 1), dn, hdn_pos, fun j hj => ?_⟩
    have hsub_lt : k - 1 - j < k := by omega
    have hj1 := hlin (k - 1 - j) hsub_lt
    have hk1' := hlin (k - 1) (by omega)
    have heqZ : (f (k - 1) + j * dn : ℤ) = (f (k - 1 - j) : ℤ) := by
      have hcast_sub : ((k - 1 - j : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - (j : ℤ) := by omega
      rw [hcast_sub] at hj1
      nlinarith [hdn_cast, hj1, hk1']
    have heqN : f (k - 1) + j * dn = f (k - 1 - j) := by exact_mod_cast heqZ
    rw [heqN]
    exact hf_mem (k - 1 - j) hsub_lt
  · have hf10 : f 1 = f 0 := by dsimp [δ] at hzero; omega
    have hcast10 : ((f 1 : ℕ) : ZMod p) = ((f 0 : ℕ) : ZMod p) := by rw [hf10]
    rw [hf_cast 1, hf_cast 0] at hcast10
    simpa using hcast10
  · exfalso
    let dn : ℕ := δ.toNat
    have hdn_pos : 0 < dn := by dsimp [dn]; omega
    have hdn_cast : (dn : ℤ) = δ := Int.toNat_of_nonneg (by omega)
    apply hnoAP
    refine ⟨f 0, dn, hdn_pos, fun i hi => ?_⟩
    have hiZ := hlin i hi
    rw [← hdn_cast] at hiZ
    have heqN : f 0 + i * dn = f i := by exact_mod_cast hiZ.symm
    rw [heqN]
    exact hf_mem i hi

end Pre32923

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 :=
  Pre32923.prove_H2
