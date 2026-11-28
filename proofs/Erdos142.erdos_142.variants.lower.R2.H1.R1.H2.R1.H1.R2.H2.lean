import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2

Choose a natural representative x i in S for each residue a + i d. Every representative is at
most N and 2 N is below the modulus, so the congruence x (i+2) + x i = 2 x (i+1) holds as an
equation of natural numbers. Hence the integers x i have vanishing second differences and form
an affine sequence. The first two terms differ because d is nonzero, so the common difference
is nonzero; if it is negative, read the progression backwards from its last term.
-/

namespace OMA.Helpers

/-- Natural numbers below the modulus are determined by their residues. -/
theorem e142ap_nat_eq_of_zmod {p u v : ℕ} (hu : u < p) (hv : v < p)
    (h : (u : ZMod p) = (v : ZMod p)) : u = v := by
  have := (ZMod.natCast_eq_natCast_iff' u v p).mp h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at this

/-- An integer sequence with vanishing second differences is affine (pairwise form). -/
theorem e142ap_affine_pair (y : ℕ → ℤ) (k : ℕ)
    (h : ∀ i, i + 2 < k → y (i + 2) + y i = 2 * y (i + 1)) :
    ∀ i, i + 1 < k →
      y i = y 0 + i * (y 1 - y 0) ∧ y (i + 1) = y 0 + (i + 1) * (y 1 - y 0) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    obtain ⟨h0, h1⟩ := ih (by omega)
    have h2 : y (j + 1 + 1) + y j = 2 * y (j + 1) := h j (by omega)
    push_cast
    exact ⟨h1, by linear_combination h2 - h0 + 2 * h1⟩

/-- An integer sequence with vanishing second differences is affine. -/
theorem e142ap_affine (y : ℕ → ℤ) (k : ℕ)
    (h : ∀ i, i + 2 < k → y (i + 2) + y i = 2 * y (i + 1)) :
    ∀ i, i < k → y i = y 0 + i * (y 1 - y 0) := by
  intro i hi
  rcases i with _ | j
  · simp
  · exact (e142ap_affine_pair y k h j hi).2.trans (by push_cast; ring)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2 := by
  classical
  intro k N p hk hNp S hS hprog
  obtain ⟨a, d, hd, hmem⟩ := hprog
  have hlift : ∀ i < k, ∃ n ∈ S, (n : ZMod p) = a + (i : ZMod p) * d := fun i hi =>
    Finset.mem_image.mp (hmem i hi)
  choose! x hxS hxeq using hlift
  have hxN : ∀ i < k, x i ≤ N := fun i hi => (Finset.mem_Icc.mp (hS (hxS i hi))).2
  have hrec : ∀ i, i + 2 < k → x (i + 2) + x i = 2 * x (i + 1) := by
    intro i hi
    have b2 := hxN (i + 2) hi
    have b1 := hxN (i + 1) (by omega)
    have b0 := hxN i (by omega)
    apply e142ap_nat_eq_of_zmod (p := p) (by omega) (by omega)
    push_cast
    rw [hxeq _ hi, hxeq _ (by omega), hxeq _ (by omega)]
    push_cast
    ring
  have haff := e142ap_affine (fun i => (x i : ℤ)) k
    (fun i hi => by exact_mod_cast hrec i hi)
  have hne : x 1 ≠ x 0 := by
    intro h
    apply hd
    have h1 := hxeq 1 (by omega)
    have h0 := hxeq 0 (by omega)
    rw [h, h0] at h1
    simpa using h1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨x (k - 1), x 0 - x 1, by omega, ?_⟩
    intro i hi
    have e1 := haff (k - 1) (by omega)
    have e2 := haff (k - 1 - i) (by omega)
    have key : x (k - 1) + i * (x 0 - x 1) = x (k - 1 - i) := by
      have hz : ((x (k - 1) + i * (x 0 - x 1) : ℕ) : ℤ) = (x (k - 1 - i) : ℤ) := by
        rw [e2, Nat.cast_add, Nat.cast_mul, e1, Nat.cast_sub hlt.le,
          Nat.cast_sub (show i ≤ k - 1 by omega), Nat.cast_sub (show 1 ≤ k by omega)]
        push_cast
        ring
      exact_mod_cast hz
    rw [key]
    exact hxS _ (by omega)
  · refine ⟨x 0, x 1 - x 0, by omega, ?_⟩
    intro i hi
    have e1 := haff i hi
    have key : x 0 + i * (x 1 - x 0) = x i := by
      have hz : ((x 0 + i * (x 1 - x 0) : ℕ) : ℤ) = (x i : ℤ) := by
        rw [e1, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hgt.le]
      exact_mod_cast hz
    rw [key]
    exact hxS i hi
