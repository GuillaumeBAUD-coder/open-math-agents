import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

/-! The prime-embedding reduction and its earlier proof are documented in PR #32923. The extremizer and natural progression criterion follow the merged lower.R2 reduction. Orient the cyclic progression first so each step lifts without wrapping. -/
namespace OMA.E142.HalfStep
open Finset Erdos142

private lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k)
    (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (range k).image fun i => a + i * d
  have hinj : Function.Injective (fun i : ℕ => a + i * d) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hmem i (mem_range.mp hi)
  have hap : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [T, card_image_of_injective _ hinj], ?_⟩
    ext x
    simp [T]
  exact (not_le_of_gt hk) (by exact_mod_cast hfree T hsub hap)

private lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hn : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hp
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hp)).elim
  have hb : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    simpa using card_le_card hs
  obtain ⟨S, hS, hf, hc⟩ := Nat.sSup_mem hn hb
  exact ⟨S, hS, hf, hc⟩

-- A step in the positive half of ZMod p never wraps from a representative in [1,N].
private lemma small_step {N p k : ℕ} [NeZero p] {S : Finset ℕ}
    (hN : 2*N < p) (hk : 1 < k) (hb : S ⊆ Icc 1 N) (hf : (S : Set ℕ).IsAPOfLengthFree k)
    (a d : ZMod p) (hd : d ≠ 0) (hs : 2*d.val ≤ p)
    (h : ∀ i : Fin k, a+(i.val : ZMod p)*d ∈ S.image (fun x : ℕ => (x : ZMod p))) : False := by
  let x (i : ℕ) := a+(i : ZMod p)*d
  have mem (i : ℕ) (hi : i < k) : (x i).val ∈ S := by
    obtain ⟨y, hy, he⟩ := mem_image.mp (h ⟨i,hi⟩)
    change (y : ZMod p) = x i at he
    rw [← he, ZMod.val_natCast_of_lt (by have := (mem_Icc.mp (hb hy)).2; omega)]
    exact hy
  have lift (i : ℕ) (hi : i < k) : (x i).val = a.val + i*d.val := by
    induction i with
    | zero => simp [x]
    | succ i ih =>
      have e : x (i+1) = x i + d := by simp [x, add_mul, add_assoc]
      have bound := (mem_Icc.mp (hb (mem i (by omega)))).2
      rw [e, ZMod.val_add_of_lt (by omega), ih (by omega), Nat.succ_mul, Nat.add_assoc]
  exact no_positive_step hk hf ⟨a.val, d.val, ZMod.val_pos.mpr hd, fun i hi => lift i hi ▸ mem i hi⟩

end OMA.E142.HalfStep

open Finset Erdos142 OMA.E142.HalfStep in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨S,hb,hf,hs⟩ := extremizer (show 1 < k by omega) N
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*N) (by omega)
  let : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨p,hp,S.image (fun x : ℕ => (x : ZMod p)),hlo,by omega,?_,?_⟩
  · rw [← hs, Finset.card_image_of_injOn]
    intro x hx y hy he
    have small (t) (ht : t ∈ S) : t < p := by have := (mem_Icc.mp (hb ht)).2; omega
    simpa only [ZMod.val_natCast_of_lt (small x hx), ZMod.val_natCast_of_lt (small y hy)]
      using congrArg ZMod.val he
  · intro a d h
    by_contra hd
    by_cases hhalf : 2*d.val ≤ p
    · exact small_step hlo (by omega) hb hf a d hd hhalf h
    · apply small_step hlo (by omega) hb hf (a + ((k-1 : ℕ) : ZMod p)*d) (-d) (neg_ne_zero.mpr hd)
      · rw [ZMod.neg_val, if_neg hd]
        omega
      · intro i
        have e : a + ((k-1 : ℕ) : ZMod p)*d + (i.val : ZMod p)*(-d) =
            a + ((k-1-i.val : ℕ) : ZMod p)*d := by
          rw [Nat.cast_sub (by have := i.isLt; omega : i.val ≤ k-1)]
          ring
        rw [e]
        exact h ⟨k-1-i.val, by omega⟩
