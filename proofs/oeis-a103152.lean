import OMAStatements.S_oeis_a103152
import Mathlib

-- McNeil's counterexample (OEIS A103152): a(23) = 725, which is not divisible by 3. The representation
-- counts of all odd m <= 725 are evaluated by decide +kernel through a copy rep' that looks primality up in a
-- bitmask PM of the primes below 726, proved equivalent to Nat.Prime there by decide +kernel.

namespace OMA.P21A103152

open OMA.S_oeis_a103152

def PM : ℕ := 2760529851718890358268076798578308459400086460667767524382036453062798643029691111456041629571334607485359782341806658644021097812034336826194874419862978234595417052425593627301893980692263665201876798434959239555244

def fpb (p : ℕ) : Bool := PM.testBit p

lemma hfp : ∀ p, p < 726 → (Nat.Prime p ↔ fpb p = true) := by decide +kernel

def rep' (m : ℕ) : ℕ :=
  ((Finset.range (m / 2 + 1)).filter fun p =>
    fpb p = true ∧ p % 2 = 1 ∧ fpb (m - 2 * p) = true ∧ (m - 2 * p) % 2 = 1).card

lemma rep_eq (m : ℕ) (hm : m < 726) : representations m = rep' m := by
  unfold representations rep'
  exact congrArg Finset.card (Finset.filter_congr (fun p hp => by
    rw [Finset.mem_range] at hp
    rw [hfp p (by omega), hfp (m - 2 * p) (by omega), Nat.odd_iff, Nat.odd_iff]))

lemma low : ∀ k, k < 725 → k % 2 = 1 → rep' k ≠ 23 := by decide +kernel

lemma top : rep' 725 = 23 := by decide +kernel

lemma sInf_eq_of {S : Set ℕ} {m : ℕ} (hm : m ∈ S) (hlow : ∀ k < m, k ∉ S) : sInf S = m :=
  le_antisymm (Nat.sInf_le hm) (le_csInf ⟨m, hm⟩ (fun k hk => by
    by_contra h
    push_neg at h
    exact hlow k h hk))

lemma a23 : a 23 = 725 := by
  unfold a
  apply sInf_eq_of
  · exact ⟨by decide, by rw [rep_eq 725 (by norm_num)]; exact top⟩
  · intro k hk hS
    obtain ⟨hodd, hr⟩ := hS
    rw [rep_eq k (by omega)] at hr
    exact low k hk (Nat.odd_iff.mp hodd) hr

end OMA.P21A103152

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103152.main) := by
  intro h
  have h23 := h 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [OMA.P21A103152.a23] at h23
  norm_num at h23
