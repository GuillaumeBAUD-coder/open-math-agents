import OMAReductions.R_Erdos686_erdos_686_R1
import Mathlib.NumberTheory.Pell

-- Step Erdos686.erdos_686.R1.H1: hypothesis H1 of reduction Erdos686.erdos_686.R1
-- Credit: @DeepDuke
-- H1 := ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),     (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i))  /-- The square case: every square N at least 2 has such a representation (open). -/

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  intro N hN hnot
  have hni : ¬IsSquare (N : ℤ) := by
    rintro ⟨z,hz⟩
    apply hnot
    refine ⟨z.natAbs,?_⟩
    simpa only [Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs hz
  obtain ⟨z,hzx,hzy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare
    (show (0 : ℤ) < N by omega) hni
  let a := z.x.toNat
  let b := z.y.toNat
  have hxa : (a : ℤ)=z.x := Int.toNat_of_nonneg (by omega)
  have hya : (b : ℤ)=z.y := Int.toNat_of_nonneg (by omega)
  have ha : 2 ≤ a := by
    have h : (2 : ℤ) ≤ a := by rw [hxa]; omega
    exact_mod_cast h
  have hb : 0 < b := by
    have h : (0 : ℤ) < b := by rw [hya]; exact hzy
    exact_mod_cast h
  have hpell : a^2=N*b^2+1 := by
    have h := z.prop_x
    rw [← hxa,← hya] at h
    exact_mod_cast (by simpa only [add_comm] using h :
      (a : ℤ)^2=(N : ℤ)*(b : ℤ)^2+1)
  let A := N*b*(a+b)
  let B := b*(N*b+a)
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hab : 2 ≤ a*b := ha.trans (Nat.le_mul_of_pos_right a hb)
  have hdiff : A+a*b=B+N*(a*b) := by dsimp [A,B]; ring
  have hscale := Nat.mul_le_mul_right (a*b) hN
  have hgap : B+2 ≤ A := by nlinarith only [hab,hdiff,hscale]
  have hidentity : A*(A+1)=N*B*(B+1) := by
    have he : (a : ℤ)^2=(N : ℤ)*(b : ℤ)^2+1 := by exact_mod_cast hpell
    have hZ : (A : ℤ)*((A : ℤ)+1)=(N : ℤ)*(B : ℤ)*((B : ℤ)+1) := by
      dsimp [A,B]
      push_cast
      linear_combination (N : ℤ)*((N : ℤ)-1)*(b : ℤ)^2 * he
    exact_mod_cast hZ
  refine ⟨2,by decide,B-1,A-1,by omega,?_⟩
  have hprod (c : ℕ) : (∏ i ∈ Finset.Icc 1 2, (c+i))=(c+1)*(c+2) := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hprod,hprod]
  have hA1 : A-1+1=A := by omega
  have hA2 : A-1+2=A+1 := by omega
  have hB1 : B-1+1=B := by omega
  have hB2 : B-1+2=B+1 := by omega
  rw [hA1,hA2,hB1,hB2]
  have hq : ((A*(A+1) : ℕ) : ℚ)=(N : ℚ)*((B*(B+1) : ℕ) : ℚ) := by
    exact_mod_cast (by simpa only [mul_assoc] using hidentity : A*(A+1)=N*(B*(B+1)))
  apply (eq_div_iff (by positivity : ((B*(B+1) : ℕ) : ℚ) ≠ 0)).mpr
  exact hq.symm

