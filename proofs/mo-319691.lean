import OMAStatements.S_mo_319691
import Mathlib



open OMA.S_mo_319691

private theorem power_has_room (m : ℕ) : m+1 ≤ 2^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [pow_succ]
    omega

private theorem denominator_between (n : ℕ) (hn : 0 < n) :
    ∃ t : ℕ, 1 ≤ t ∧ n^3 ≤ 2^t ∧ 2^t ≤ 2*n^3 := by
  have hex : ∃ k : ℕ, n^3 ≤ 2^(k+1) := ⟨n^3,by
    have ht := power_has_room (n^3+1)
    omega⟩
  let k := Nat.find hex
  have hk : n^3 ≤ 2^(k+1) := Nat.find_spec hex
  refine ⟨k+1,by omega,hk,?_⟩
  by_cases h : k = 0
  · have hp : 0 < n^3 := pow_pos hn _
    simp only [h,Nat.zero_add,pow_one]
    omega
  · have hsub : k-1+1 = k := by omega
    have hprev : 2^k < n^3 := by
      by_contra hnq
      have hf : n^3 ≤ 2^(k-1+1) := by rw [hsub]; omega
      have he := Nat.find_min' hex hf
      change k ≤ k-1 at he
      omega
    rw [pow_succ]
    omega

theorem OMA.solution : type_of% @OMA.S_mo_319691.main := by
  refine ⟨1/2,1,1,3,by norm_num,by norm_num,by norm_num,?_⟩
  intro n k hn _
  obtain ⟨t,ht,hLower,hUpper⟩ := denominator_between n hn
  let q := 2^t
  let x := inputFraction n k
  have hX : 0 ≤ x := by unfold x inputFraction; positivity
  let w := (q : ℝ)*x/2
  let r := ⌊w⌋₊
  let p := 2*r+1
  have hW : 0 ≤ w := by dsimp [w]; positivity
  have hLo : (r : ℝ) ≤ w := Nat.floor_le hW
  have hHi : w < (r : ℝ)+1 := Nat.lt_floor_add_one w
  have hq : 0 < q := pow_pos (by decide) t
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPowR : 0 < (n : ℝ)^3 := pow_pos hnR _
  have hCoprime₂ : Nat.Coprime p 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨r,rfl⟩
  have hCoprime : Nat.Coprime p q := hCoprime₂.pow_right t
  have hL : (n : ℝ)^3 ≤ q := by exact_mod_cast hLower
  have hU : (q : ℝ) ≤ 2*(n : ℝ)^3 := by exact_mod_cast hUpper
  have hDown : (1/2 : ℝ)/(n : ℝ)^3 ≤ 1/(q : ℝ) := by
    apply (div_le_div_iff₀ hPowR hqR).mpr
    linarith
  have hUp : (1 : ℝ)/(q : ℝ) ≤ 1/(n : ℝ)^3 := one_div_le_one_div_of_le hPowR hL
  have hError : |(q : ℝ)*x - (p : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    dsimp [w] at hLo hHi
    simp only [p,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    constructor <;> linarith
  refine ⟨p,q,hq,hCoprime,hDown,hUp,?_⟩
  change |x - (p : ℝ)/(q : ℝ)| ≤ 1/(n : ℝ)^3
  rw [show x-(p : ℝ)/(q : ℝ) = ((q : ℝ)*x-(p : ℝ))/(q : ℝ) by
    field_simp [hqR.ne'],abs_div,abs_of_pos hqR]
  exact (div_le_div_of_nonneg_right hError hqR.le).trans hUp
