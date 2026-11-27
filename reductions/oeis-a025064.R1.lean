import OMAStatements.S_oeis_a025064
import Mathlib

/-!
The rank calculation reduces to representability above 1848. The class 3 mod 4
has an explicit witness. The initial counts are verified by bounded search
inside Lean. The two remaining tails correspond to the complementary residue
classes 1 mod 4 and 0 or 2 mod 4.

Credit: @caa1982.
-/

namespace OMA.R_oeis_a025064_R1

open OMA.S_oeis_a025064 Finset

/-- The odd tail in the residue class 1 modulo 4. -/
def H1 : Prop := ∀ m : ℕ, 1848 < m → m % 4 = 1 → Representable m

/-- The even tail. -/
def H2 : Prop := ∀ m : ℕ, 1848 < m → m % 2 = 0 → Representable m

lemma rep_three {m : ℕ} (hm : 1848 < m) (h : m % 4 = 3) :
    Representable m := by
  refine ⟨1, 3, m / 4, by decide, by decide, by omega, ?_⟩
  omega

private lemma rep_tail (h₁ : H1) (h₂ : H2) {m : ℕ} (hm : 1848 < m) :
    Representable m := by
  by_cases even : m % 2 = 0
  · exact h₂ m hm even
  · by_cases one : m % 4 = 1
    · exact h₁ m hm one
    · exact rep_three hm (by omega)

-- If a < b < c is a witness, then b² ≤ m and c is determined by a and b.
private def candidate (m a b : ℕ) : Bool :=
  let c := (m - a * b) / (a + b)
  decide (0 < a ∧ a < b ∧ b < c ∧ m = a * b + b * c + a * c)

private def repTest (m : ℕ) : Bool :=
  (List.range (m.sqrt + 1)).any fun a =>
    (List.range (m.sqrt + 1)).any fun b => candidate m a b

private lemma repTest_correct (m : ℕ) : repTest m = true ↔ Representable m := by
  simp only [repTest, List.any_eq_true, List.mem_range, candidate, decide_eq_true_eq]
  constructor
  · rintro ⟨a, _, b, _, ha, hab, hbc, hm⟩
    exact ⟨a, b, (m - a * b) / (a + b), ha, hab, hbc, hm⟩
  · rintro ⟨a, b, c, ha, hab, hbc, hm⟩
    have hb : b ≤ m.sqrt := Nat.le_sqrt.mpr (calc
      b * b ≤ b * c := Nat.mul_le_mul_left b hbc.le
      _ ≤ m := by omega)
    have hc : (m - a * b) / (a + b) = c := by
      have he : m = a * b + (a + b) * c := by rw [hm]; ring
      rw [he, Nat.add_sub_cancel_left]
      exact Nat.mul_div_cancel_left c (by omega)
    exact ⟨a, by omega, b, by omega, ha, hab, by simpa only [hc] using hbc,
      by simpa only [hc] using hm⟩

private def missing (f : ℕ → Bool) (m : ℕ) : ℕ :=
  ((Icc 1 m).filter fun j => f j = false).card

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma missing_small : missing repTest 1848 = 65 := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma missing_squares : missing (fun j => repTest (3 * j ^ 2)) 24 = 3 := by
  decide +kernel

private lemma rank_tail (P : ℕ → Prop) (f : ℕ → Bool)
    (hf : ∀ j, f j = true ↔ P j) {b m : ℕ} (hbm : b ≤ m)
    (htail : ∀ j, b < j → P j) :
    countTo P m = m - missing f b := by
  classical
  have hfilter : ((Icc 1 m).filter fun j => ¬ P j) =
      (Icc 1 b).filter fun j => f j = false := by
    ext j
    simp only [mem_filter, mem_Icc, ← hf, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨hj, _⟩, hfalse⟩
      refine ⟨⟨hj, le_of_not_gt ?_⟩, hfalse⟩
      intro h
      rw [(hf j).mpr (htail j h)] at hfalse
      contradiction
    · rintro ⟨⟨hj, hjb⟩, hfalse⟩
      exact ⟨⟨hj, hjb.trans hbm⟩, hfalse⟩
  have hcount := card_filter_add_card_filter_not (s := Icc 1 m) P
  rw [hfilter, Nat.card_Icc] at hcount
  change countTo P m + missing f b = m + 1 - 1 at hcount
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a025064.main := by
  intro h₁ h₂ n hn
  have hs (j : ℕ) (hj : 24 < j) : 1848 < 3 * j ^ 2 := by nlinarith
  let k := n + 3
  have hk : 24 < k := by dsimp [k]; omega
  refine ⟨k, by omega, rep_tail h₁ h₂ (hs k hk), ?_, ?_⟩
  · rw [rank_tail _ (fun j => repTest (3 * j ^ 2))
      (fun j => repTest_correct _) (show 24 ≤ k by omega)
      (fun j hj => rep_tail h₁ h₂ (hs j hj)), missing_squares]
    dsimp [k]
    omega
  · rw [rank_tail _ repTest repTest_correct (show 1848 ≤ 3 * k ^ 2 from (hs k hk).le)
      (fun j hj => rep_tail h₁ h₂ hj), missing_small]
    have hp : 3 * k ^ 2 = 3 * n ^ 2 + 18 * n + 27 := by dsimp [k]; ring
    rw [hp]
    omega

end OMA.R_oeis_a025064_R1
