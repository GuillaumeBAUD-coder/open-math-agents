import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

/-!
Prime embedding for Eilam Carmi's reduction #32923.
The extremizer lemmas follow mucoucah's merged R3. The no-wrap lift uses
AlfredMelson's Lean lemma from desk note #172267 on the related H3 step.
-/

namespace Erdos142PrimeEmbedding

open Erdos142

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

theorem lift_short_ap {p N k : ℕ} (short : 2*N < p) (hk : 2 ≤ k)
    {S : Set ℕ} (bound : ∀ x ∈ S, x ≤ N) {a d : ZMod p} (hd : d≠0)
    (ap : ∀ i < k, a+i*d ∈ (fun x : ℕ => (x : ZMod p)) '' S) :
    ∃ b e : ℕ, 0 < e ∧ ∀ i < k, b+i*e ∈ S := by
  classical
  have hsel (i : ℕ) : ∃ x : ℕ, i < k → x∈S ∧ (x:ZMod p)=a+i*d := by
    by_cases h : i < k
    · obtain ⟨x,hx,he⟩ := ap i h
      exact ⟨x,fun _ => ⟨hx,he⟩⟩
    · exact ⟨0,by omega⟩
  choose x sel using hsel
  have mid (i : ℕ) (hi : i+2 < k) : x (i+2)+x i=2*x (i+1) := by
    have modEq : ((x (i+2)+x i : ℕ) : ZMod p) = ((2*x (i+1) : ℕ) : ZMod p) := by
      push_cast
      rw [(sel _ hi).2,(sel i (by omega)).2,(sel (i+1) (by omega)).2]
      push_cast
      ring
    have h := (ZMod.natCast_eq_natCast_iff' ..).mp modEq
    have h0 := bound _ (sel i (by omega)).1
    have h1 := bound _ (sel (i+1) (by omega)).1
    have h2 := bound _ (sel _ hi).1
    simpa [Nat.mod_eq_of_lt (by omega : x (i+2)+x i < p),
      Nat.mod_eq_of_lt (by omega : 2*x (i+1) < p)] using h
  have nz : x 0 ≠ x 1 := by
    intro eq
    have h0 := (sel 0 (by omega)).2
    rw [eq,(sel 1 (by omega)).2] at h0
    exact hd (by simpa using h0)
  let D : ℤ := (x 1:ℤ)-x 0
  have diff (i : ℕ) (hi : i+1 < k) : (x (i+1):ℤ)-x i=D := by
    induction i with
    | zero => rfl
    | succ i ih =>
      specialize ih (by omega)
      have h := mid i hi
      change (x (i+2):ℤ)-x (i+1)=D
      omega
  have line (i : ℕ) (hi : i < k) : (x i : ℤ)=x 0+(i:ℤ)*D := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h := diff i hi
      rw [Nat.cast_succ]
      linear_combination h + ih (by omega)
  by_cases forward : x 0 < x 1
  · refine ⟨x 0,x 1-x 0,by omega,?_⟩
    intro i hi
    have h : x 0+i*(x 1-x 0)=x i := by
      zify [forward.le]
      exact (line i hi).symm
    rw [h]; exact (sel i hi).1
  · refine ⟨x (k-1),x 0-x 1,by omega,?_⟩
    intro i hi
    have h : x (k-1)+i*(x 0-x 1)=x (k-1-i) := by
      zify [show x 1≤x 0 by omega]
      rw [line _ (by omega),line (k-1-i) (by omega)]
      push_cast [Nat.cast_sub (by omega : i≤k-1)]
      dsimp [D]
      ring
    rw [h]; exact (sel _ (by omega)).1

end Erdos142PrimeEmbedding

open Erdos142 Erdos142PrimeEmbedding in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨p, hPrime, hShort, hComparable⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  obtain ⟨S, hS, hFree, hSize⟩ := exists_maximizer (k := k) (by omega) N
  let A := S.image (fun x : ℕ => (x : ZMod p))
  have hBound {x : ℕ} (hx : x ∈ S) : x ≤ N := (Finset.mem_Icc.mp (hS hx)).2
  have hCard : A.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxLt : x < p := (hBound hx).trans_lt (by omega)
    have hyLt : y < p := (hBound hy).trans_lt (by omega)
    simpa only [ZMod.val_natCast_of_lt hxLt, ZMod.val_natCast_of_lt hyLt] using
      congrArg ZMod.val hxy
  refine ⟨p, hPrime, A, hShort, by omega, hSize.trans hCard.symm, ?_⟩
  intro a d hProgression
  by_contra hNonzero
  have hImage : ∀ i < k, a + i * d ∈ (fun x : ℕ => (x : ZMod p)) '' (S : Set ℕ) := by
    intro i hi
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (hProgression ⟨i, hi⟩)
    exact ⟨x, hx, he⟩
  exact (apFree_iff (by omega : 1 < k)).mp hFree
    (lift_short_ap hShort (by omega : 2 ≤ k) (fun _ hx => hBound hx) hNonzero hImage)
