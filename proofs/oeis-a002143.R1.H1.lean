import OMAReductions.R_oeis_a002143_R1

/-! The trigonometric part of the class-number identity, by counting square roots. -/

open Finset Real

namespace OMA.CotangentSum

private theorem cosecant_double (x : ℝ) :
    1 / sin (2*x) = cot x - cot (2*x) := by
  simp only [cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  by_cases s : sin x = 0
  · simp [s]
  by_cases c : cos x = 0
  · simp [c]
  field_simp
  nlinarith [sin_sq_add_cos_sq x]

private noncomputable def cotAt {p : ℕ} (x : ZMod p) : ℝ := cot (π*x.val/p)

private theorem cotAt_nat {p : ℕ} [NeZero p] (n : ℕ) :
    cotAt (n : ZMod p) = cot (π*n/p) := by
  have d : ((n%p : ℕ) : ℝ)+(p:ℝ)*(n/p : ℕ)=n := by exact_mod_cast Nat.mod_add_div n p
  have pp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have a : π*n/p = π*(n%p : ℕ)/p + (n/p : ℕ)*π := by
    calc π*n/p = π*(((n%p : ℕ):ℝ)+(p:ℝ)*(n/p : ℕ))/p := by rw [d]
         _ = _ := by field_simp
  simp only [cotAt,ZMod.val_natCast,a,←tan_inv_eq_cot,tan_add_nat_mul_pi]

private theorem full_interval {p : ℕ} [NeZero p] (f : ZMod p → ℝ) (zero : f 0=0) :
    (∑ x : ZMod p, f x) = ∑ k ∈ Icc 1 (p-1), f k := by
  classical
  have toRange : (∑ x : ZMod p, f x) = ∑ k ∈ range p, f k := by
    apply sum_bij' (s:=(univ : Finset (ZMod p))) (t:=range p)
      (fun (x : ZMod p) _ ↦ x.val) (fun (k : ℕ) _ ↦ (k : ZMod p))
    · exact fun x _ ↦ mem_range.mpr (ZMod.val_lt x)
    · simp
    · exact fun x _ ↦ ZMod.natCast_zmod_val x
    · exact fun k hk ↦ ZMod.val_natCast_of_lt (mem_range.mp hk)
    · simp
  rw [toRange,←Nat.Ico_zero_eq_range,←Ico_add_one_right_eq_Icc,
    show p-1+1=p by have := NeZero.pos p; omega]
  have split := sum_Ico_consecutive (fun k : ℕ ↦ f k) (m:=0) (n:=1) (k:=p)
    (by decide) (NeZero.pos p)
  simpa [zero] using split.symm

private theorem twice_half {p : ℕ} [NeZero p] (odd : Odd p) (f : ZMod p → ℝ)
    (zero : f 0=0) (even : ∀ x, f (-x)=f x) :
    (∑ x : ZMod p, f x) = 2*∑ k ∈ Icc 1 ((p-1)/2), f k := by
  let h := (p-1)/2
  obtain ⟨j,hj⟩ := odd
  have size : p=2*h+1 := by dsimp [h]; omega
  have ref := sum_Ico_reflect (fun k : ℕ ↦ f k) 1 (m:=h+1) (n:=p) (by omega)
  rw [show p+1-(h+1)=h+1 by omega,show p+1-1=p by omega] at ref
  have mirror : (∑ k ∈ Ico 1 (h+1), f ((p-k : ℕ) : ZMod p)) =
      ∑ k ∈ Ico 1 (h+1), f k := by
    apply sum_congr rfl
    intro k hk
    have := mem_Ico.mp hk
    rw [Nat.cast_sub (by omega : k≤p),ZMod.natCast_self,zero_sub,even]
  rw [full_interval f zero,←Ico_add_one_right_eq_Icc,
    show p-1+1=p by omega,←sum_Ico_consecutive (fun k : ℕ ↦ f k)
      (show 1≤h+1 by omega) (show h+1≤p by omega),←ref,mirror,Ico_add_one_right_eq_Icc]
  ring

private theorem weighted {p : ℕ} [Fact p.Prime] (big : 3<p) (res : p%8=3)
    (f : ZMod p → ℝ) :
    (∑ x : ZMod p, (f (x^2)-f (2*x^2))) =
      2*∑ x : ZMod p, (quadraticChar (ZMod p) x : ℝ)*f x := by
  classical
  let χ := fun x : ZMod p ↦ (quadraticChar (ZMod p) x : ℝ)
  have hp : p≠2 := by omega
  have atTwo : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two hp,ZMod.χ₈_nat_mod_eight,res]
    decide
  have neg : χ (2:ZMod p) = -1 := by
    change (quadraticChar (ZMod p) (2 : ZMod p) : ℝ) = -1
    exact_mod_cast (show quadraticChar (ZMod p) (2:ZMod p) = -1 by
      simpa [legendreSym] using atTwo)
  have flip (x : ZMod p) : χ (2*x) = -χ x := by
    dsimp only [χ]
    rw [map_mul,Int.cast_mul]
    change χ 2 * χ x = -χ x
    rw [neg,neg_one_mul]
  have fibers (G : ZMod p → ℝ) : (∑ x : ZMod p, G (x^2)) =
      ∑ x : ZMod p, (χ x+1)*G x := by
    rw [←Finset.sum_fiberwise' (univ : Finset (ZMod p)) (fun x ↦ x^2) G]
    apply sum_congr rfl
    intro x _
    rw [sum_const,nsmul_eq_mul]
    congr 1
    have same : univ.filter (fun y : ZMod p ↦ y^2=x) =
        {y : ZMod p | y^2=x}.toFinset := by ext; simp
    rw [same]
    dsimp only [χ]
    exact_mod_cast quadraticChar_card_sqrts ((ZMod.ringChar_zmod_n p).substr hp) x
  have nz : (2 : ZMod p) ≠ 0 := by
    intro z
    have := neg
    simp [χ,z] at this
  have perm : Function.Bijective (fun x : ZMod p ↦ 2*x) := by
    exact ⟨fun _ _ eq ↦ mul_left_cancel₀ nz eq,fun y ↦ ⟨y/2,by field_simp⟩⟩
  have shift : (∑ x : ZMod p, (χ x+1)*f (2*x)) =
      ∑ x : ZMod p, (1-χ x)*f x := by
    calc _ = ∑ x : ZMod p, (1-χ (2*x))*f (2*x) := by
              apply sum_congr rfl
              intro x _
              rw [flip]
              ring
         _ = _ := perm.sum_comp (fun y ↦ (1-χ y)*f y)
  change _ = 2*∑ x : ZMod p, χ x*f x
  rw [fibers (fun y ↦ f y - f (2*y))]
  simp_rw [mul_sub]
  rw [sum_sub_distrib,shift,←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro x _
  ring

end OMA.CotangentSum

open OMA.CotangentSum in
theorem OMA.solution : OMA.R_oeis_a002143_R1.H1 := by
  classical
  intro p inst big res
  let g := fun x : ZMod p ↦ cotAt (x^2)-cotAt (2*x^2)
  have value (k : ℕ) : g k = 1/sin (2*π*(k:ℝ)^2/p) := by
    have a : (k : ZMod p)^2=((k^2 : ℕ) : ZMod p) := by norm_cast
    have b : 2*(k : ZMod p)^2=((2*k^2 : ℕ) : ZMod p) := by norm_cast
    dsimp only [g]
    rw [b,a,cotAt_nat,cotAt_nat]
    push_cast
    rw [show 2*π*(k:ℝ)^2/p=2*(π*(k:ℝ)^2/p) by ring,
      show π*(2*(k:ℝ)^2)/p=2*(π*(k:ℝ)^2/p) by ring,cosecant_double]
  have odd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have half := twice_half odd g (by simp [g]) (fun x ↦ by simp [g])
  have full := weighted big res (cotAt (p:=p))
  have zero : (fun x : ZMod p ↦ (quadraticChar (ZMod p) x : ℝ)*cotAt x) 0=0 := by simp
  rw [full_interval (fun x : ZMod p ↦ (quadraticChar (ZMod p) x : ℝ)*cotAt x) zero] at full
  have eq : (∑ k ∈ Icc 1 ((p-1)/2), g k) =
      ∑ k ∈ Icc 1 (p-1), (quadraticChar (ZMod p) (k:ZMod p) : ℝ)*cotAt (k:ZMod p) := by
    change (∑ x : ZMod p, g x) = _ at full
    linarith
  simpa only [value,cotAt_nat,legendreSym,Int.cast_natCast] using eq
