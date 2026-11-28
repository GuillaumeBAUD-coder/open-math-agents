import OMAReductions.R_Singmaster_singmaster_R1
import Mathlib

-- Step Singmaster.singmaster.R1.H1: hypothesis H1 of reduction Singmaster.singmaster.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Singmaster_singmaster_R1.H1 := by
  intro t _
  apply (((Finset.range (2 * t + 1)) ×ˢ (Finset.range (2 * t + 1))).finite_toSet).subset
  rintro ⟨n, k⟩ ⟨hk, hkn, hc⟩
  have h1 : k + 1 ≤ n.choose k := by
    calc k + 1 = (k + 1).choose k := (Nat.choose_succ_self_right k).symm
      _ ≤ n.choose k := Nat.choose_le_choose k (by omega)
  have h2 : n - k + 1 ≤ n.choose k := by
    rw [← Nat.choose_symm hkn.le]
    calc n - k + 1 = (n - k + 1).choose (n - k) := (Nat.choose_succ_self_right _).symm
      _ ≤ n.choose (n - k) := Nat.choose_le_choose _ (by omega)
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  omega
