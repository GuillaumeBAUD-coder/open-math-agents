import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-! In the separated blocks from reduction R2, a factor of two cannot change
the block index. In particular the second and third progression terms belong
to one block. Their separation then bounds the common difference. -/

namespace OMA.E142Block

private lemma separated {i j x y : ℕ} (h : i < j)
    (hx : x ≤ 5 * 4^i) (hy : 4 * 4^j < y) : 2*x < y := by
  have scale : 4 * 4^i ≤ 4^j := by
    simpa only [pow_succ'] using Nat.pow_le_pow_right (n := 4) (by decide) h
  omega

end OMA.E142Block

open OMA.E142Block in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB free ⟨a,d,hd,terms⟩
  choose! j b hb he using terms
  have bounds i (hi : i < k) : 4 * 4^(j i) < a + i*d ∧ a + i*d ≤ 5 * 4^(j i) := by
    have := Finset.mem_Icc.mp (hB _ (hb i hi))
    rw [he i hi]
    omega
  have adjacent (i : ℕ) (hi : i+1 < k) (h : d ≤ a+i*d) :
      j i = j (i+1) := by
    have H := bounds i (by omega)
    have K := bounds (i+1) hi
    rcases lt_trichotomy (j i) (j (i+1)) with lt | eq | gt
    · have := separated lt H.2 K.1
      simp only [Nat.add_mul, one_mul] at this
      omega
    · exact eq
    · have := separated gt K.2 H.1
      simp only [Nat.add_mul, one_mul] at this
      omega
  have one := bounds 1 (by omega)
  have two := bounds 2 (by omega)
  rw [← adjacent 1 (by omega) (by omega)] at two
  have small : d ≤ a := by omega
  have same (i : ℕ) (hi : i < k) : j i = j 0 := by
    induction i with
    | zero => rfl
    | succ i ih => exact (adjacent i hi (by omega)).symm.trans (ih (by omega))
  apply free (j 0)
  refine ⟨a - 4*4^(j 0), d, hd, fun i hi => ?_⟩
  have e := he i hi
  have m := hb i hi
  rw [same i hi] at e m
  have zero := bounds 0 (by omega)
  rwa [show a - 4*4^(j 0) + i*d = b i by omega]
