import OMAReductions.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1

/-! # Integer parameters for the sparse Ramsey construction -/
-- Credit: @steveDOTdigital
namespace OMA.RamseyParameters
open Filter

-- Integer powers leave one full power of t for each strict inequality.
private lemma edge_exponent (p : ℕ) (hp : 3 ≤ p) :
    (p+1)*(p-2) = 2*(p.choose 2-1) ∧ 1 ≤ p.choose 2-1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
  have h := Nat.add_one_mul_choose_eq (j+2) 1
  simp only [Nat.choose_one_right] at h
  have he : 3+j=j+2+1 := by omega
  rw [he]
  have sz : 2 ≤ (j+2+1).choose 2 := by nlinarith only [h,Nat.zero_le (j*j),Nat.zero_le j]
  have sub := Nat.sub_add_cancel (show 1 ≤ (j+2+1).choose 2 by omega)
  constructor
  · rw [show j+2+1-2=j+1 by omega]
    nlinarith only [h,sub]
  · omega

private lemma parameters (p : ℕ) (hp : 3 ≤ p) (b : ℝ) (hb : 2/((p:ℝ)+1)<b) :
    ∃ᶠ n : ℕ in atTop, ∃ B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) ∧ (m : ℝ) ≤ (n : ℝ)^b := by
  have gap : 0 < ((p:ℝ)+1)*b-2 := by
    have h := (div_lt_iff₀ (show 0<(p:ℝ)+1 by positivity)).mp hb
    linarith
  obtain ⟨s,hs⟩ := exists_nat_gt (2/(((p:ℝ)+1)*b-2))
  have hs' := (div_lt_iff₀ gap).mp hs
  have s0 : 0<s := by
    by_contra! h
    have hz : s=0 := by omega
    rw [hz] at hs'
    norm_num at hs'
  let d := (p+1)*s
  let e := 2*s+1
  let f := 2*s+2
  have dpos : 0<d := Nat.mul_pos (by omega) s0
  have fd : f ≤ d := by dsimp [f,d]; nlinarith [Nat.mul_le_mul_right s hp]
  have fR : (f:ℝ) ≤ (d:ℝ)*b := by dsimp [f,d]; push_cast; nlinarith only [hs']
  rw [Filter.frequently_atTop]
  intro M
  let x := M+128*(d+1)+64*p^2+p+3
  let t := x^2
  have xle : x ≤ t := Nat.le_self_pow (by decide : 2 ≠ 0) x
  have big : M ≤ x ∧ p ≤ x ∧ 3 ≤ x ∧ 64*p^2 ≤ x ∧ 128*(d+1) ≤ x := by dsimp [x]; omega
  have tn : t ≤ t^d := Nat.le_self_pow dpos.ne' _
  have be : t ≤ t^e := Nat.le_self_pow (by dsimp [e]; omega) _
  have fm : t ≤ t^f := Nat.le_self_pow (by dsimp [f]; omega) _
  have edge := edge_exponent p hp
  let r := p.choose 2-1
  have expEq : r+d*(p-2)=e*r := by
    calc
      _ = r+s*((p+1)*(p-2)) := by dsimp [d]; ring
      _ = _ := by rw [edge.1]; dsimp [e,r]; ring
  have compare : 64*p^2*(t^d)^(p-2) ≤ (t^e)^r := by
    rw [←pow_mul t d (p-2),←pow_mul t e r,←expEq,pow_add]
    exact Nat.mul_le_mul_right _ ((big.2.2.2.1.trans xle).trans (Nat.le_self_pow (Nat.ne_of_gt edge.2) t))
  have x0 : 0<(x:ℝ) := by exact_mod_cast (show 0<x by omega)
  have dt : 128*((d:ℝ)+1) ≤ x := by exact_mod_cast big.2.2.2.2
  have logt : Real.log (t:ℝ) ≤ 2*(x:ℝ) := by
    have := Real.log_le_sub_one_of_pos x0
    dsimp [t]; rw [Nat.cast_pow,Real.log_pow]; norm_num; linarith
  have tcap : 32*((d:ℝ)*Real.log (t:ℝ)+1) ≤ t := by
    have a := mul_le_mul_of_nonneg_left logt (by positivity : 0 ≤ (d:ℝ))
    have x3 : (3:ℝ) ≤ x := by exact_mod_cast big.2.2.1
    have h := mul_le_mul_of_nonneg_right dt x0.le
    calc
      _ ≤ (x:ℝ)^2 := by nlinarith only [a,h,x3,mul_nonneg (by positivity : 0≤(d:ℝ)) x0.le]
      _ = _ := by simp [t]
  refine ⟨t^d,by omega,t^e,t^f,⟨hp,by omega,by omega,by omega,
    Nat.pow_le_pow_right (by omega : 0<t) fd,compare,?_⟩,?_⟩
  · push_cast
    rw [Real.log_pow,show f=e+1 by rfl,pow_succ (t:ℝ) e]
    nlinarith only [mul_le_mul_of_nonneg_left tcap (by positivity : 0 ≤ (t:ℝ)^e)]
  · push_cast
    rw [←Real.rpow_natCast_mul (by positivity)]
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ t by omega)) fR

end OMA.RamseyParameters

theorem OMA.solution : OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1.H2 := OMA.RamseyParameters.parameters
