import OMAStatements.S_oeis_a361717

/-! Both congruences follow from the binomial product formulas, finite
summation by parts, and reflection of reciprocal powers modulo a prime square. -/

namespace A361717Proof

open Finset

private theorem reflect_sum {R : Type*} [AddCommMonoid R] {p k : ℕ} (hk : k < p)
    (f : ℕ → R) :
    (∑ j ∈ Ico 1 (k+1), f (p-j)) = ∑ j ∈ Ico (p-k) p, f j := by
  refine Finset.sum_bij (fun j _ => p-j) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hl,hr⟩ := mem_Ico.mp hj
    apply mem_Ico.mpr
    omega
  · intro i hi j hj h
    obtain ⟨hi0,hi1⟩ := mem_Ico.mp hi
    obtain ⟨hj0,hj1⟩ := mem_Ico.mp hj
    omega
  · intro j hj
    obtain ⟨h0,h1⟩ := mem_Ico.mp hj
    refine ⟨p-j, mem_Ico.mpr ⟨by omega,by omega⟩, by omega⟩
  · intro j hj
    rfl

section Nilpotent
variable {R : Type*} [CommRing R]

private theorem prod_linearize {ι : Type*} (s : Finset ι) (t : ι → R) {P : R} (hP : P^2=0) :
    (∏ i ∈ s, (1+P*t i)) = 1+P*(∑ i ∈ s,t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    linear_combination (t i * (∑ j ∈ s, t j)) * hP

private def harmon (x : ℕ → R) (k : ℕ) : R :=
  ∑ j ∈ Ico 1 (k+1), x j

private theorem harmon_step (x : ℕ → R) {k : ℕ} (hk : 1 ≤ k) :
    harmon x k = harmon x (k-1)+x k := by
  rw [harmon, harmon, show k-1+1 = k by omega, Finset.sum_Ico_succ_top hk]

private theorem cancel_two (h2 : IsUnit (2 : R)) {y : R} (h : 2*y=0) : y=0 := by
  obtain ⟨u, hu⟩ := h2
  rw [← hu] at h
  have hh := congrArg (fun z : R => (↑(u⁻¹) : R)*z) h
  simpa [← mul_assoc] using hh

private theorem inv_reflect {p : ℕ} {x : ℕ → R} (hP : (p:R)^2=0)
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1) {j : ℕ} (hj : j ∈ Ico 1 p) :
    x (p-j) = -x j -(p:R)*x j^2 := by
  obtain ⟨hj0,hj1⟩ := mem_Ico.mp hj
  have hy := hx (p-j) (mem_Ico.mpr ⟨by omega,by omega⟩)
  have hz : ((p-j:ℕ):R)*(-x j -(p:R)*x j^2)=1 := by
    rw [Nat.cast_sub (by omega : j ≤ p)]
    linear_combination (1+(p:R)*x j)*hx j hj - (x j)^2*hP
  calc
    x (p-j) = x (p-j)*(((p-j:ℕ):R)*(-x j-(p:R)*x j^2)) := by rw [hz,mul_one]
    _ = ((p-j:ℕ):R)*x (p-j)*(-x j-(p:R)*x j^2) := by ring
    _ = _ := by rw [hy,one_mul]

private theorem weighted_harmon_reflect {p : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2 : R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1) {k : ℕ} (hk : k ∈ Ico 1 p) :
    (p:R)*harmon x (p-k-1) = (p:R)*harmon x k := by
  have hInv (j : ℕ) (hj : j ∈ Ico 1 p) : (p:R)*x (p-j) = -(p:R)*x j := by
    rw [inv_reflect hP hx hj]
    linear_combination -(x j)^2*hP
  have full : (p:R)*harmon x (p-1)=0 := by
    have h := reflect_sum (R:=R) (p:=p) (k:=p-1) (by omega) (fun j => (p:R)*x j)
    rw [show p-1+1=p by omega, show p-(p-1)=1 by omega] at h
    simp_rw [show (∑ j ∈ Ico 1 p, (p:R)*x (p-j)) = ∑ j ∈ Ico 1 p, -(p:R)*x j from
      sum_congr rfl hInv] at h
    rw [← mul_sum, ← mul_sum] at h
    apply cancel_two h2
    rw [harmon, show p-1+1=p by omega]
    linear_combination -h
  obtain ⟨hk0,hk1⟩ := mem_Ico.mp hk
  have hup : (∑ j ∈ Ico (p-k) p, (p:R)*x j) = -(p:R)*harmon x k := by
    rw [← reflect_sum (R:=R) hk1 (fun j => (p:R)*x j), harmon, mul_sum]
    exact sum_congr rfl (fun j hj => hInv j (mem_Ico.mpr
      ⟨(mem_Ico.mp hj).1,by have := (mem_Ico.mp hj).2; omega⟩))
  have hadd := Finset.sum_Ico_consecutive (fun j => (p:R)*x j)
    (show 1 ≤ p-k by omega) (show p-k ≤ p by omega)
  rw [hup, ←mul_sum, ←mul_sum] at hadd
  have hf : (p:R)*∑ j ∈ Ico 1 p, x j = 0 := by
    simpa [harmon,show p-1+1=p by omega] using full
  rw [hf] at hadd
  rw [harmon, show p-k-1+1=p-k by omega]
  linear_combination hadd

end Nilpotent

section Residues

variable {p : ℕ} [hp : Fact p.Prime]

private noncomputable def reduce (p : ℕ) : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p)

private theorem mul_prime_of_reduce_zero (a : ZMod (p^2)) (ha : reduce p a=0) :
    (p : ZMod (p^2))*a=0 := by
  have hcast := ZMod.natCast_zmod_val a
  have hmod : (a.val : ZMod p) = 0 := by
    calc
      _ = reduce p (a.val : ZMod (p^2)) := (map_natCast (reduce p) _).symm
      _ = reduce p a := congrArg (reduce p) hcast
      _ = 0 := ha
  have hd := (ZMod.natCast_eq_zero_iff a.val p).1 hmod
  rw [← hcast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  obtain ⟨k,hk⟩ := hd
  exact ⟨k, by rw [hk,pow_two,mul_assoc]⟩

private theorem inverse_power_sum_field (r : ℕ) (hr : 0 < r) (hl : r < p-1) :
    (∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹)^r) = 0 := by
  classical
  have hNz (j : ℕ) (hj : j ∈ Ico 1 p) : (j : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
      ((ZMod.natCast_eq_zero_iff j p).1 hz)
  have hb :
      (∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹)^r) = ∑ u : (ZMod p)ˣ, (↑u⁻¹ : ZMod p)^r := by
    refine Finset.sum_bij'
      (fun j hj => Units.mk0 (j : ZMod p) (hNz j hj))
      (fun u _ => (u : ZMod p).val)
      (fun _ _ => Finset.mem_univ _)
      (fun u _ => ?_)
      (fun j hj => ?_)
      (fun u _ => ?_)
      (fun j hj => ?_)
    · exact mem_Ico.mpr ⟨Nat.one_le_of_lt (ZMod.val_pos.mpr u.ne_zero), ZMod.val_lt _⟩
    · exact ZMod.val_cast_of_lt (mem_Ico.mp hj).2
    · exact Units.ext (ZMod.natCast_zmod_val _)
    · simp
  rw [hb]
  calc
    _ = ∑ u : (ZMod p)ˣ, (↑u : ZMod p)^r :=
      Equiv.sum_comp (Equiv.inv ((ZMod p)ˣ)) (fun u : (ZMod p)ˣ => (↑u : ZMod p)^r)
    _ = 0 := by
      rw [FiniteField.sum_pow_units, ZMod.card, if_neg (Nat.not_dvd_of_pos_of_lt hr hl)]

private theorem inverse_power_sum_mod (r : ℕ) (hr : 0 < r) (hl : r < p-1)
    {x : ℕ → ZMod (p^2)} (hx : ∀ j ∈ Ico 1 p, (j:ZMod (p^2))*x j = 1) :
    (p:ZMod (p^2))*(∑ j ∈ Ico 1 p, x j^r)=0 := by
  apply mul_prime_of_reduce_zero
  have hw (j : ℕ) (hj : j ∈ Ico 1 p) : reduce p (x j) = (j:ZMod p)⁻¹ := by
    have h := congrArg (reduce p) (hx j hj)
    simp only [map_mul,map_natCast,map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [map_sum]
  simp_rw [map_pow]
  calc
    _ = ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹)^r := sum_congr rfl (fun j hj => by rw [hw j hj])
    _ = 0 := inverse_power_sum_field r hr hl

end Residues

section Products

variable {K : Type*} [Field K] [CharZero K]

private theorem lower_binomial (p k : ℕ) (hk : k < p) :
    (((p-1).choose k : ℕ) : K) * (-1)^k =
      ∏ j ∈ Ico 1 (k+1), (1-(p:K)/(j:K)) := by
  have hn (j : ℕ) (hj : j ∈ Ico 1 (k+1)) : (j:K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hj).1; omega)
  have hp : (∏ j ∈ Ico 1 (k+1), ((p:K)-(j:K))) =
      ((p-1).descFactorial k : ℕ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    apply prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (by have := mem_range.mp hj; omega)]
    push_cast [Nat.cast_sub (show 1 ≤ p by omega)]
    ring
  symm
  calc
    _ = ∏ j ∈ Ico 1 (k+1), -1 * (((p:K)-(j:K))/(j:K)) := by
      apply prod_congr rfl
      intro j hj
      field_simp [hn j hj]
      ring
    _ = (-1 : K)^k * (((p-1).descFactorial k : ℕ) / (k.factorial : K)) := by
      rw [prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel,
        prod_div_distrib, hp, ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
    _ = _ := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]

private theorem upper_binomial (p k : ℕ) (hp0 : 0 < p) (hk : 1 ≤ k) :
    (((p-1+k).choose k : ℕ) : K) =
      (p:K)/(k:K) * ∏ j ∈ Ico 1 k, (1+(p:K)/(j:K)) := by
  have hn (j : ℕ) (hj : j ∈ Ico 1 k) : (j:K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hj).1; omega)
  have he : (∏ j ∈ Ico 1 k, (j:K)) = ((k-1).factorial : ℕ) := by
    rw [← Nat.cast_prod, ← Finset.prod_Ico_id_eq_factorial, show k-1+1=k by omega]
  have hp : (p:K) * (∏ j ∈ Ico 1 k, ((p:K)+(j:K))) = (p.ascFactorial k : ℕ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    simp only [Nat.cast_add]
    rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega : 0 < k)]
    simp
  have hft : (k.factorial : K) = (k:K)*((k-1).factorial:ℕ) := by
    have ht := Nat.factorial_succ (k-1)
    rw [show k-1+1=k by omega] at ht
    exact_mod_cast ht
  have hfac : (p.ascFactorial k : ℕ) = k.factorial * (p-1+k).choose k := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose (p-1) k
    rwa [show p-1+1=p by omega] at h
  -- Clear the common factorial after assembling the ascending product.
  symm
  calc
    _ = (p:K)/(k:K) * ∏ j ∈ Ico 1 k, (((p:K)+(j:K))/(j:K)) := by
      congr 1
      apply prod_congr rfl
      intro j hj
      field_simp [hn j hj]
      ring
    _ = ((p:K)*(∏ j ∈ Ico 1 k, ((p:K)+(j:K)))) /
        ((k:K)*((k-1).factorial:ℕ)) := by
      rw [prod_div_distrib, he]
      ring
    _ = _ := by
      rw [hp, ← hft, hfac, Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]

end Products

open scoped Padic
open OMA.S_oeis_a361717

section PadicModel
variable {p : ℕ} [hp : Fact p.Prime]

private theorem padicNat_isUnit (k : ℕ) (hk : k ∈ Ico 1 p) :
    IsUnit (k : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, hp.out.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hk).1 (mem_Ico.mp hk).2

private noncomputable def pinv (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ_[p] :=
  (k : ℤ_[p]).inv

private theorem pinv_spec (k : ℕ) (hk : k ∈ Ico 1 p) : (k : ℤ_[p])*pinv p k=1 :=
  PadicInt.mul_inv ((PadicInt.isUnit_iff).mp (padicNat_isUnit k hk))

private theorem pinv_coe (k : ℕ) (hk : k ∈ Ico 1 p) :
    ((pinv p k : ℤ_[p]) : ℚ_[p]) = (k:ℚ_[p])⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hh := congrArg (PadicInt.Coe.ringHom (p:=p)) (pinv_spec k hk)
  rw [map_mul,map_natCast,map_one] at hh
  exact hh

end PadicModel

section Summation

variable {R : Type*} [CommRing R]

private theorem telescope (f : ℕ → R) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Ico a b, (f (k+1)-f k)) = f b-f a := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a+n.succ=(a+n)+1 by omega, Finset.sum_Ico_succ_top (by omega : a ≤ a+n)]
    rw [ih (by omega)]
    abel

private theorem full_reflect {p : ℕ} (hp : 1 ≤ p) (f : ℕ → R) :
    (∑ j ∈ Ico 1 p, f (p-j)) = ∑ j ∈ Ico 1 p, f j := by
  simpa only [show p-1+1=p by omega, show p-(p-1)=1 by omega] using
    reflect_sum (R:=R) (p:=p) (k:=p-1) (by omega) f

private theorem harm_zero {p : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2:R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1)
    (hPow : (p:R)*(∑ j ∈ Ico 1 p,x j^2)=0) :
    (∑ j ∈ Ico 1 p, x j)=0 := by
  have h := full_reflect (Nat.one_le_of_lt hp) x
  have hsum : (∑ j ∈ Ico 1 p,x (p-j)) =
      -(∑ j ∈ Ico 1 p,x j) -(p:R)*(∑ j ∈ Ico 1 p,x j^2) := by
    rw [← Finset.sum_neg_distrib,mul_sum,←sum_sub_distrib]
    exact sum_congr rfl (fun j hj => inv_reflect hP hx hj)
  rw [hsum,hPow,sub_zero] at h
  apply cancel_two h2
  linear_combination -h

private theorem weighted_harm_current_reflect {p : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2:R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1)
    {j : ℕ} (hj : j ∈ Ico 1 p) :
    (p:R)*harmon x (p-j) = (p:R)*harmon x (j-1) := by
  have ⟨h0,h1⟩ := mem_Ico.mp hj
  rw [harmon_step x (show 1≤p-j by omega), mul_add,
    weighted_harmon_reflect hp hP h2 hx hj, harmon_step x h0,inv_reflect hP hx hj]
  linear_combination -(x j)^2*hP

private theorem weighted_reciprocal_harm {p : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2:R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1)
    (hPow : (p:R)*(∑ j ∈ Ico 1 p,x j^2)=0) :
    (∑ j ∈ Ico 1 p, (p:R)*x j*harmon x j)=0 := by
  let f := fun j => (p:R)*x j*harmon x j
  have hh := full_reflect (Nat.one_le_of_lt hp) f
  have hterm (j : ℕ) (hj : j ∈ Ico 1 p) :
      f j + f (p-j) = (p:R)*x j^2 := by
    change (p:R)*x j*harmon x j+(p:R)*x (p-j)*harmon x (p-j) = _
    have hr : (p:R)*x (p-j) = -(p:R)*x j := by
      rw [inv_reflect hP hx hj]
      linear_combination -(x j)^2*hP
    rw [hr,show -(p:R)*x j*harmon x (p-j) = -x j*((p:R)*harmon x (p-j)) by ring,
      weighted_harm_current_reflect hp hP h2 hx hj, harmon_step x (mem_Ico.mp hj).1]
    ring
  apply cancel_two h2
  change (2:R)*(∑ j ∈ Ico 1 p,f j)=0
  calc
    _ = ∑ j ∈ Ico 1 p,(f j+f (p-j)) := by rw [sum_add_distrib,hh]; ring
    _ = (p:R)*(∑ j ∈ Ico 1 p,x j^2) := by rw [mul_sum]; exact sum_congr rfl hterm
    _ = 0 := hPow

private theorem sum_cast_weight {p : ℕ} (hp : 1 ≤ p) :
    (2:R)*(∑ j ∈ Ico 1 p, (j:R)) = (p:R)*((p:R)-1) := by
  have hh := full_reflect (R:=R) hp (fun j => (j:R))
  calc
    _ = ∑ j ∈ Ico 1 p, ((j:R)+((p-j:ℕ):R)) := by rw [sum_add_distrib,hh]; ring
    _ = (p:R)*((p:R)-1) := by
      calc
        _ = ∑ _j ∈ Ico 1 p,(p:R) := by
          exact sum_congr rfl (fun j hj => by
            rw [Nat.cast_sub (mem_Ico.mp hj).2.le]
            ring)
        _ = _ := by simp [Nat.card_Ico,Nat.cast_sub hp,mul_comm,nsmul_eq_mul]

private theorem weighted_linear_harm {p : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2:R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1)
    (hZ : (∑ j ∈ Ico 1 p,x j)=0) :
    (2:R)*(∑ j ∈ Ico 1 p, ((j:R)+2)*(p:R)*harmon x j) = 3*(p:R) := by
  have hcard : (∑ _j ∈ Ico 1 p, (1:R)) = (p:R)-1 := by
    simp [Nat.card_Ico,Nat.cast_sub (Nat.one_le_of_lt hp),nsmul_eq_mul]
  have hH : (∑ j ∈ Ico 1 p, harmon x j) = 1-(p:R) := by
    let f := fun j : ℕ => (j:R)*harmon x (j-1)
    have h_tel := telescope f (Nat.one_le_of_lt hp)
    have h_step (j : ℕ) (hj : j∈Ico 1 p) :
        f (j+1)-f j=harmon x j+1 := by
      change ((↑(j+1):R)*harmon x (j+1-1))-(j:R)*harmon x (j-1)=_
      rw [Nat.cast_add,Nat.cast_one, Nat.add_sub_cancel, harmon_step x (mem_Ico.mp hj).1]
      linear_combination hx j hj
    rw [sum_congr rfl h_step, sum_add_distrib,hcard] at h_tel
    have hf0 : f 1 = 0 := by simp [f,harmon]
    have hfp : f p = 0 := by
      simp only [f,harmon,show p-1+1=p by omega,hZ,mul_zero]
    rw [hf0,hfp] at h_tel
    linear_combination h_tel
  let f := fun j : ℕ => ((j:R)+2)*(p:R)*harmon x j
  have hh := full_reflect (Nat.one_le_of_lt hp) f
  have hpair (j : ℕ) (hj : j ∈ Ico 1 p) :
      f j + f (p-j) = 4*(p:R)*harmon x j + (p:R)-2*(p:R)*x j := by
    have hk := (mem_Ico.mp hj).2.le
    change ((j:R)+2)*(p:R)*harmon x j+(((p-j:ℕ):R)+2)*(p:R)*harmon x (p-j)=_
    rw [show (((p-j:ℕ):R)+2)*(p:R)*harmon x (p-j) =
      (((p-j:ℕ):R)+2)*((p:R)*harmon x (p-j)) by ring,
      weighted_harm_current_reflect hp hP h2 hx hj,Nat.cast_sub hk,
      harmon_step x (mem_Ico.mp hj).1]
    linear_combination harmon x (j-1)*hP + (p:R)*hx j hj
  change 2*(∑ j ∈ Ico 1 p, f j) = _
  calc
    _ = ∑ j ∈ Ico 1 p,(f j+f (p-j)) := by rw [sum_add_distrib,hh]; ring
    _ = ∑ j ∈ Ico 1 p,(4*(p:R)*harmon x j + (p:R)-2*(p:R)*x j) :=
      sum_congr rfl hpair
    _ = _ := by
      rw [sum_sub_distrib,sum_add_distrib,←mul_sum,←mul_sum,hH,hZ,mul_zero,sub_zero]
      simp [Nat.card_Ico,Nat.cast_sub (Nat.one_le_of_lt hp),nsmul_eq_mul]
      linear_combination -3*hP

end Summation

section FirstCongruence

variable {R : Type*} [CommRing R]

private def lowerProduct (p : ℕ) (x : ℕ → R) (k : ℕ) : R :=
  ∏ j ∈ Ico 1 (k+1), (1-(p:R)*x j)

private def plusProduct (p : ℕ) (x : ℕ → R) (k : ℕ) : R :=
  ∏ j ∈ Ico 1 (k+1), (1+(p:R)*x j)

private theorem lowerProduct_step (p : ℕ) (x : ℕ → R) (k : ℕ) :
    lowerProduct p x (k+1)=lowerProduct p x k*(1-(p:R)*x (k+1)) := by
  rw [lowerProduct,lowerProduct,Finset.prod_Ico_succ_top (by omega : 1≤k+1)]

private def antiderivative (p : ℕ) (x : ℕ → R) (k : ℕ) : R :=
  if k=p then 0 else (k:R)*lowerProduct p x k

private theorem antiderivative_step {p : ℕ} {x : ℕ → R}
    (hx : ∀ j ∈ Ico 1 p,(j:R)*x j=1) (k : ℕ) (hk : k<p) :
    antiderivative p x (k+1)-antiderivative p x k =
      (1-(p:R))*lowerProduct p x k := by
  unfold antiderivative
  rw [if_neg (by omega : k≠p)]
  by_cases hs : k+1=p
  · rw [if_pos hs, ← hs, Nat.cast_add, Nat.cast_one]
    ring
  · rw [if_neg hs, lowerProduct_step,Nat.cast_add,Nat.cast_one]
    have h := hx (k+1) (mem_Ico.mpr ⟨by omega,by omega⟩)
    rw [Nat.cast_add,Nat.cast_one] at h
    linear_combination -(p:R)*lowerProduct p x k*h

private theorem cancel_prime_sub {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hx : ∀ j ∈ Ico 1 p,(j:R)*x j=1) {y : R} (hy : (1-(p:R))*y=0) :
    y=0 := by
  have h := hx (p-1) (mem_Ico.mpr ⟨by omega,by omega⟩)
  rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one] at h
  have he : (1-(p:R))*(-x (p-1))=1 := by linear_combination h
  calc
    y = ((1-(p:R))*(-x (p-1)))*y := by rw [he,one_mul]
    _ = (-x (p-1))*((1-(p:R))*y) := by ring
    _ = 0 := by rw [hy,mul_zero]

private theorem lowerProduct_sum {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hx : ∀ j ∈ Ico 1 p,(j:R)*x j=1) :
    (∑ k ∈ range p,lowerProduct p x k)=0 := by
  have h := telescope (antiderivative p x) (Nat.zero_le p)
  rw [Nat.Ico_zero_eq_range] at h
  have hpoint (k : ℕ) (hk : k∈range p) := antiderivative_step hx k (mem_range.mp hk)
  rw [sum_congr rfl hpoint,←mul_sum] at h
  apply cancel_prime_sub hp hx
  simpa [antiderivative,if_neg (by omega : (0:ℕ)≠p)] using h

private theorem lowerProduct_harmonic_sum {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hx : ∀ j ∈ Ico 1 p,(j:R)*x j=1) :
    (1-(p:R))*(∑ k ∈ Ico 1 p,lowerProduct p x k*harmon (fun j=>x j^2) k) =
      -(∑ k ∈ Ico 1 p,lowerProduct p x k*x k) := by
  let h := harmon (fun j=>x j^2)
  let t := antiderivative p x
  let f := fun k => t k*h (k-1)
  have hTel := telescope f (Nat.one_le_of_lt hp)
  have hStep (k : ℕ) (hk : k∈Ico 1 p) :
      f (k+1)-f k =
        (1-(p:R))*lowerProduct p x k*h k+lowerProduct p x k*x k := by
    have hk0 := (mem_Ico.mp hk).1
    have hk1 := (mem_Ico.mp hk).2
    have ht : t (k+1)-t k=(1-(p:R))*lowerProduct p x k := antiderivative_step hx k hk1
    have hD : h k-h (k-1)=x k^2 := by
      dsimp [h]
      rw [harmon_step _ hk0,add_sub_cancel_left]
    change t (k+1)*h (k+1-1)-t k*h (k-1)=_
    rw [Nat.add_sub_cancel]
    calc
      _=(t (k+1)-t k)*h k+t k*(h k-h (k-1)) := by ring
      _=_ := by
        rw [ht,hD,show t k=(k:R)*lowerProduct p x k by
          simp [t,antiderivative,if_neg (by omega : k≠p)]]
        linear_combination lowerProduct p x k*x k*hx k hk
  rw [sum_congr rfl hStep,sum_add_distrib] at hTel
  have hf1 : f 1 = 0 := by simp [f,h,harmon]
  have hfp : f p = 0 := by simp [f,t,antiderivative]
  rw [hf1,hfp,sub_zero] at hTel
  have he : (∑ k ∈ Ico 1 p,(1-(p:R))*lowerProduct p x k*h k) =
      (1-(p:R))*∑ k ∈ Ico 1 p,lowerProduct p x k*h k := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  change (∑ k ∈ Ico 1 p,(1-(p:R))*lowerProduct p x k*h k)+
    (∑ k ∈ Ico 1 p,lowerProduct p x k*x k)=0 at hTel
  rw [he] at hTel
  linear_combination hTel

private def firstProductSum (p : ℕ) (x : ℕ → R) : R :=
  ∑ k ∈ range p, lowerProduct p x k *
    (∏ j ∈ Ico 1 (k+1), (1-(p:R)^2*x j^2))

private theorem firstProductSum_zero {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hP : (p:R)^4=0) (hx : ∀ j ∈ Ico 1 p,(j:R)*x j=1)
    (hH : (p:R)^2*(∑ k ∈ Ico 1 p,lowerProduct p x k*x k)=0) :
    firstProductSum p x=0 := by
  let h := harmon (fun j=>x j^2)
  have htw : (-(p:R)^2)^2=0 := by rw [neg_sq,←pow_mul]; exact hP
  have hprod (k : ℕ) : (∏ j ∈ Ico 1 (k+1), (1-(p:R)^2*x j^2))=1-(p:R)^2*h k := by
    simpa only [neg_mul,sub_eq_add_neg,h,harmon] using
      prod_linearize (Ico 1 (k+1)) (fun j=>x j^2) htw
  have hm := lowerProduct_harmonic_sum hp hx
  have hw : (p:R)^2*(∑ k ∈ Ico 1 p,lowerProduct p x k*h k)=0 := by
    apply cancel_prime_sub hp hx
    calc
      _=(p:R)^2*((1-(p:R))*(∑ k ∈ Ico 1 p,lowerProduct p x k*h k)) := by ring
      _= -((p:R)^2*(∑ k ∈ Ico 1 p,lowerProduct p x k*x k)) := by rw [hm,mul_neg]
      _=0 := by rw [hH,neg_zero]
  have hTerm (k : ℕ) : lowerProduct p x k * (∏ j ∈ Ico 1 (k+1), (1-(p:R)^2*x j^2)) =
      lowerProduct p x k - (p:R)^2*(lowerProduct p x k*h k) := by rw [hprod]; ring
  unfold firstProductSum
  rw [sum_congr rfl (fun k _=>hTerm k),sum_sub_distrib,←mul_sum,lowerProduct_sum hp hx]
  have he : (∑ k ∈ range p,lowerProduct p x k*h k) =
      ∑ k ∈ Ico 1 p,lowerProduct p x k*h k := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 1≤p by omega),sum_range_one]
    simp [h,harmon]
  rw [he,hw,sub_zero]

end FirstCongruence

section SecondCongruence

variable {R : Type*} [CommRing R]

private theorem lowerProduct_linear {p : ℕ} (x : ℕ → R) (k : ℕ)
    (hP : (p:R)^2=0) :
    lowerProduct p x k = 1-(p:R)*harmon x k := by
  have hN : (-(p:R))^2=0 := by rwa [neg_sq]
  simpa only [lowerProduct,harmon,sub_eq_add_neg,neg_mul] using
    prod_linearize (Ico 1 (k+1)) x hN

private def secondProductTerm (p : ℕ) (x : ℕ → R) (k : ℕ) : R :=
  x k * ((((p-1-k:ℕ):R)*x (p-1))^2) *
    lowerProduct p x k ^ 2 * plusProduct p x (k-1)

private theorem secondProduct_linear {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hP : (p:R)^2=0) (hx : ∀ j∈Ico 1 p,(j:R)*x j=1) {k : ℕ} (hk : k∈Ico 1 p) :
    secondProductTerm p x k =
      (k:R)+2+x k + (2*(p:R))*(k:R)+(p:R)-(2*(p:R))*x k-(p:R)*x k^2
        -((k:R)+2)*(p:R)*harmon x k-(p:R)*x k*harmon x k := by
  have hk0 := (mem_Ico.mp hk).1
  have hk1 := (mem_Ico.mp hk).2
  have hx1 : x 1=1 := by
    have h := hx 1 (mem_Ico.mpr ⟨by omega,hp⟩)
    simpa using h
  have hxlast : x (p-1)= -1-(p:R) := by
    have h := inv_reflect hP hx (j:=1) (mem_Ico.mpr ⟨by omega,hp⟩)
    simpa [hx1] using h
  have hdiv : (((p-1-k:ℕ):R)*x (p-1))=1+(k:R)+(p:R)*(k:R) := by
    rw [hxlast, Nat.cast_sub (by omega : k≤p-1),
      Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
    linear_combination -hP
  have hSq : x k*(1+(k:R)+(p:R)*(k:R))^2 =
      ((k:R)+2+x k)+2*(p:R)*((k:R)+1) := by
    linear_combination ((k:R)+2+2*(p:R)*(1+(k:R)))*hx k hk +
      x k*(k:R)^2*hP
  have hupper : plusProduct p x (k-1)=1+(p:R)*(harmon x k-x k) := by
    unfold plusProduct
    rw [prod_linearize _ _ hP, harmon_step x hk0, add_sub_cancel_right]
    rfl
  have hTwo : (1-(p:R)*harmon x k)^2*(1+(p:R)*(harmon x k-x k))=
      1-(p:R)*harmon x k-(p:R)*x k := by
    linear_combination (-(harmon x k)^2+2*harmon x k*x k+
      (p:R)*(harmon x k)^2*(harmon x k-x k))*hP
  unfold secondProductTerm
  rw [hdiv,hSq,lowerProduct_linear x k hP,hupper]
  rw [mul_assoc,hTwo]
  linear_combination -(p:R)*hx k hk -
    2*((k:R)+1)*(harmon x k+x k)*hP

private def secondProductSum (p : ℕ) (x : ℕ → R) : R :=
  ∑ k∈Ico 1 p,secondProductTerm p x k

private theorem secondProductSum_value {p : ℕ} (hp : 1<p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2:R)) (hx : ∀ j∈Ico 1 p,(j:R)*x j=1)
    (hPow : (p:R)*(∑ j∈Ico 1 p,x j^2)=0) :
    secondProductSum p x= -2-(p:R) := by
  have hZ := harm_zero hp hP h2 hx hPow
  have hHX := weighted_reciprocal_harm hp hP h2 hx hPow
  have hHJ := weighted_linear_harm hp hP h2 hx hZ
  have hJ := sum_cast_weight (R:=R) (Nat.one_le_of_lt hp)
  have hSum : secondProductSum p x=
      (∑ k∈Ico 1 p,(k:R))+2*((p:R)-1)+(2*(p:R))*(∑ k∈Ico 1 p,(k:R))+
        ((p:R)-1)*(p:R)-(∑ k∈Ico 1 p,((k:R)+2)*(p:R)*harmon x k) := by
    unfold secondProductSum
    rw [sum_congr rfl (fun k hk => secondProduct_linear hp hP hx hk)]
    simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,hZ,hPow,hHX,mul_zero,add_zero,sub_zero,
      Finset.sum_const,Nat.card_Ico,Nat.cast_sub (Nat.one_le_of_lt hp),Nat.cast_one,nsmul_eq_mul]
    ring
  have htarget : 2*(secondProductSum p x-(-2-(p:R)))=0 := by
    linear_combination 2*hSum+(1+2*(p:R))*hJ-hHJ+(1+2*(p:R))*hP
  exact sub_eq_zero.mp (cancel_two h2 htarget)

end SecondCongruence

private theorem plus_binomial {K : Type*} [Field K] [CharZero K] (p k : ℕ) :
    (((p+k).choose k : ℕ):K) = ∏ j∈Ico 1 (k+1),(1+(p:K)/(j:K)) := by
  have hn (j : ℕ) (hj : j∈Ico 1 (k+1)) : (j:K)≠0 :=
    Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hj).1; omega)
  have hh : (∏ j∈Ico 1 (k+1), ((p:K)+(j:K))) = ((p+1).ascFactorial k : ℕ) := by
    rw [Nat.ascFactorial_eq_prod_range,Nat.cast_prod,Finset.prod_Ico_eq_prod_range,
      Nat.add_sub_cancel]
    simp only [Nat.cast_add,Nat.cast_one,add_comm,add_left_comm]
  symm
  calc
    _ = ∏ j∈Ico 1 (k+1), ((p:K)+(j:K))/(j:K) := by
      apply prod_congr rfl
      intro j hj
      field_simp [hn j hj]
      ring
    _ = _ := by
      rw [prod_div_distrib,hh,← Nat.cast_prod,Finset.prod_Ico_id_eq_factorial,
        Nat.ascFactorial_eq_factorial_mul_choose,Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]

private theorem lowerProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (x : ℕ → R) (k : ℕ) :
    f (lowerProduct p x k) = lowerProduct p (f ∘ x) k := by simp [lowerProduct]

private theorem plusProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (x : ℕ → R) (k : ℕ) :
    f (plusProduct p x k) = plusProduct p (f ∘ x) k := by simp [plusProduct]

private theorem firstProductSum_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (x : ℕ → R) :
    f (firstProductSum p x)=firstProductSum p (f ∘ x) := by
  simp [firstProductSum,lowerProduct_map]

private theorem secondProductSum_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (x : ℕ → R) :
    f (secondProductSum p x)=secondProductSum p (f ∘ x) := by
  simp [secondProductSum,secondProductTerm,lowerProduct_map,plusProduct_map]

section ModelIdentities

variable {p : ℕ} [hp : Fact p.Prime]

private theorem lower_padic (k : ℕ) (hk : k<p) :
    PadicInt.Coe.ringHom (lowerProduct p (pinv p) k) =
      ((p-1).choose k : ℚ_[p])*(-1)^k := by
  rw [lowerProduct_map,lower_binomial p k hk,lowerProduct]
  apply prod_congr rfl
  intro j hj
  have hj0 := (mem_Ico.mp hj).1
  have hj1 := (mem_Ico.mp hj).2
  have hx : (PadicInt.Coe.ringHom ∘ pinv p) j = (j:ℚ_[p])⁻¹ :=
    pinv_coe j (mem_Ico.mpr ⟨hj0,by omega⟩)
  rw [hx,div_eq_mul_inv]

private theorem upper_padic (k : ℕ) (hk : k<p) :
    PadicInt.Coe.ringHom (plusProduct p (pinv p) k) =
      ((p+k).choose k : ℚ_[p]) := by
  rw [plusProduct_map,plus_binomial p k,plusProduct]
  apply prod_congr rfl
  intro j hj
  have hj0 := (mem_Ico.mp hj).1
  have hj1 := (mem_Ico.mp hj).2
  have hx : (PadicInt.Coe.ringHom ∘ pinv p) j = (j:ℚ_[p])⁻¹ :=
    pinv_coe j (mem_Ico.mpr ⟨hj0,by omega⟩)
  rw [hx,div_eq_mul_inv]

private theorem upper_padic_prefix (k : ℕ) (hk : k∈Ico 1 p) :
    (p:ℚ_[p]) * ((pinv p k : ℤ_[p]) : ℚ_[p]) *
        PadicInt.Coe.ringHom (plusProduct p (pinv p) (k-1)) =
      ((p-1+k).choose k : ℚ_[p]) := by
  have hk0 := (mem_Ico.mp hk).1
  have hk1 := (mem_Ico.mp hk).2
  rw [upper_binomial p k hp.out.pos hk0, pinv_coe k hk, plusProduct_map,plusProduct,
    show k-1+1=k by omega, div_eq_mul_inv]
  congr 1
  apply prod_congr rfl
  intro j hj
  have hx : (PadicInt.Coe.ringHom ∘ pinv p) j = (j:ℚ_[p])⁻¹ :=
    pinv_coe j (mem_Ico.mpr ⟨(mem_Ico.mp hj).1,(mem_Ico.mp hj).2.trans hk1⟩)
  rw [hx,div_eq_mul_inv]

private theorem sign_sq {K : Type*} [Ring K] (k : ℕ) : (((-1:K)^k)^2)=1 := by
  rw [←pow_mul,mul_comm,pow_mul]
  simp

private theorem model_first :
    (a p : ℤ_[p]) = firstProductSum p (pinv p) := by
  apply Subtype.coe_injective
  change (a p : ℚ_[p])=PadicInt.Coe.ringHom (firstProductSum p (pinv p))
  unfold a firstProductSum
  rw [Int.cast_sum,map_sum]
  apply sum_congr rfl
  intro k hk
  have hprod : (∏ j∈Ico 1 (k+1), (1-(p:ℤ_[p])^2*pinv p j^2)) =
      lowerProduct p (pinv p) k * plusProduct p (pinv p) k := by
    rw [lowerProduct,plusProduct,←prod_mul_distrib]
    exact prod_congr rfl (fun _ _ => by ring)
  rw [hprod,map_mul,map_mul,lower_padic k (mem_range.mp hk),upper_padic k (mem_range.mp hk)]
  push_cast
  linear_combination -((p-1).choose k : ℚ_[p])^2*((p+k).choose k : ℚ_[p])*
    sign_sq (K:=ℚ_[p]) k

omit hp in
private theorem a_pred_sum (hp1 : 1 < p) :
    a (p-1) = 1 + ∑ k∈Ico 1 p, ((p-2).choose k:ℤ)^2*((p-1+k).choose k:ℤ) := by
  let f := fun k : ℕ => ((p-2).choose k:ℤ)^2*((p-1+k).choose k:ℤ)
  have ha : a (p-1)=∑ k∈range (p-1), f k := by
    unfold a f
    rw [show p-1-1=p-2 by omega]
  rw [ha]
  have hzero : f (p-1)=0 := by
    simp [f, Nat.choose_eq_zero_of_lt (show p-2<p-1 by omega)]
  calc
    _=∑ k∈range p,f k := by
      conv_rhs => rw [show p=p-1+1 by omega,sum_range_succ]
      rw [hzero,add_zero]
    _=_ := by
      rw [← Finset.sum_range_add_sum_Ico _ (show 1≤p by omega),sum_range_one]
      simp [f]

private theorem model_second (hp1 : 1 < p) :
    (a (p-1) : ℤ_[p]) = 1+(p:ℤ_[p])*secondProductSum p (pinv p) := by
  apply Subtype.coe_injective
  change (a (p-1):ℚ_[p])=PadicInt.Coe.ringHom (1+(p:ℤ_[p])*secondProductSum p (pinv p))
  rw [a_pred_sum hp1,Int.cast_add,Int.cast_one,Int.cast_sum,map_add,map_one,map_mul,map_natCast,
    secondProductSum,map_sum,mul_sum]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk1 := (mem_Ico.mp hk).2
  have hk0 := (mem_Ico.mp hk).1
  have hl : p-1∈Ico 1 p := mem_Ico.mpr ⟨by omega,by omega⟩
  have hc := congrArg (fun n : ℕ => (n:ℚ_[p])) (Nat.choose_mul_succ_eq (p-2) k)
  rw [show p-2+1=p-1 by omega] at hc
  push_cast at hc
  have hdiv : ((p-2).choose k : ℚ_[p]) =
      (((p-1-k:ℕ):ℚ_[p])*((pinv p (p-1) : ℤ_[p]):ℚ_[p])) *
       ((p-1).choose k : ℚ_[p]) := by
    have hunit : ((p-1:ℕ):ℚ_[p])*((pinv p (p-1):ℤ_[p]):ℚ_[p])=1 := by
      rw [pinv_coe _ hl,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))]
    calc
      _=((p-2).choose k:ℚ_[p]) * (((p-1:ℕ):ℚ_[p])*((pinv p (p-1):ℤ_[p]):ℚ_[p])) := by
        rw [hunit,mul_one]
      _=_ := by
        rw [←mul_assoc,hc]
        ring
  have hup := upper_padic_prefix k hk
  have hlower := lower_padic k hk1
  unfold secondProductTerm
  simp only [map_mul,map_pow,map_natCast,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [hdiv,hlower,← hup]
  let C := ((p-1).choose k : ℚ_[p])
  let D := (((p-1-k:ℕ):ℚ_[p])*((pinv p (p-1):ℤ_[p]):ℚ_[p]))
  let U := PadicInt.Coe.ringHom (plusProduct p (pinv p) (k-1))
  let V := ((pinv p k:ℤ_[p]):ℚ_[p])
  change (D*C)^2*((p:ℚ_[p])*V*U) = (p:ℚ_[p])*(V*D^2*(C*(-1)^k)^2*U)
  linear_combination -((p:ℚ_[p])*V*D^2*C^2*U)*sign_sq (K:=ℚ_[p]) k

end ModelIdentities

private noncomputable def fromFour (p : ℕ) : ZMod (p^4) →+* ZMod (p^2) :=
  ZMod.castHom (pow_dvd_pow p (by decide)) (ZMod (p^2))

private theorem modFour_mul_of_zero {p : ℕ} [hp : Fact p.Prime] (a : ZMod (p^4)) (ha : fromFour p a=0) :
    (p:ZMod (p^4))^2*a=0 := by
  let : NeZero (p^4) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hcast := ZMod.natCast_zmod_val a
  have hmod : (a.val:ZMod (p^2))=0 := by
    calc
      _=fromFour p (a.val:ZMod (p^4)) := (map_natCast (fromFour p) _).symm
      _=fromFour p a := congrArg (fromFour p) hcast
      _=0 := ha
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff a.val (p^2)).mp hmod
  rw [←Nat.cast_pow,←hcast,←Nat.cast_mul,ZMod.natCast_eq_zero_iff]
  refine ⟨k,?_⟩
  rw [hk,←mul_assoc,←pow_add]

section Final
variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
private theorem nil_in_two : (p:ZMod (p^2))^2=0 := by
  rw [←Nat.cast_pow,ZMod.natCast_self]

omit hp in
private theorem nil_in_four : (p:ZMod (p^4))^4=0 := by
  rw [←Nat.cast_pow,ZMod.natCast_self]

omit hp in
private theorem unit_two {R : Type*} [CommRing R] (hp2 : 2<p) {x : ℕ → R}
    (hx : ∀ j∈Ico 1 p,(j:R)*x j=1) : IsUnit (2:R) := by
  refine isUnit_iff_dvd_one.mpr ⟨x 2,?_⟩
  exact (hx 2 (mem_Ico.mpr ⟨by decide,hp2⟩)).symm

private theorem first_mod (hp5 : 5≤p) :
    PadicInt.toZModPow 4 (firstProductSum p (pinv p))=0 := by
  rw [firstProductSum_map]
  let x4 := PadicInt.toZModPow 4 ∘ pinv p
  let x2 := fromFour p ∘ x4
  have hx4 : ∀ j∈Ico 1 p,(j:ZMod (p^4))*x4 j=1 := by
    intro j hj
    simpa [x4] using congrArg (PadicInt.toZModPow 4) (pinv_spec j hj)
  have hx2 : ∀ j∈Ico 1 p,(j:ZMod (p^2))*x2 j=1 := by
    intro j hj
    simpa [x2] using congrArg (fromFour p) (hx4 j hj)
  have h2 := unit_two (by omega : 2<p) hx2
  have hPow := inverse_power_sum_mod (p:=p) 2 (by decide) (by omega) hx2
  have hH := harm_zero (by omega) nil_in_two h2 hx2 hPow
  have hHH := weighted_reciprocal_harm (by omega) nil_in_two h2 hx2 hPow
  have hSum : (∑ k∈Ico 1 p,lowerProduct p x2 k*x2 k)=0 := by
    have h (k : ℕ) : lowerProduct p x2 k*x2 k =
        x2 k-(p:ZMod (p^2))*x2 k*harmon x2 k := by
      rw [lowerProduct_linear _ _ nil_in_two]
      ring
    rw [sum_congr rfl (fun k _=>h k),sum_sub_distrib,hH,hHH,sub_zero]
  have hReduction : fromFour p (∑ k∈Ico 1 p,lowerProduct p x4 k*x4 k)=0 := by
    simp only [map_sum,map_mul,lowerProduct_map]
    exact hSum
  exact firstProductSum_zero (by omega) nil_in_four hx4
    (modFour_mul_of_zero _ hReduction)

private theorem first_congruence (hp5 : 5≤p) :
    ((p:ℤ)^4) ∣ a p := by
  have h := congrArg (PadicInt.toZModPow 4) (model_first (p:=p))
  rw [map_intCast,first_mod hp5] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

private theorem second_congruence (hp5 : 5≤p) :
    ((p:ℤ)^3) ∣ (a (p-1)-(1-2*(p:ℤ)-(p:ℤ)^2)) := by
  let x := PadicInt.toZModPow 2 ∘ pinv p
  have hx : ∀ j∈Ico 1 p,(j:ZMod (p^2))*x j=1 := by
    intro j hj
    simpa [x] using congrArg (PadicInt.toZModPow 2) (pinv_spec j hj)
  have h2 := unit_two (by omega : 2<p) hx
  have hPow := inverse_power_sum_mod (p:=p) 2 (by decide) (by omega) hx
  have h := secondProductSum_value (by omega) nil_in_two h2 hx hPow
  let y := secondProductSum p (pinv p)+2+(p:ℤ_[p])
  have hy : y∈RingHom.ker (PadicInt.toZModPow 2 : ℤ_[p] →+* ZMod (p^2)) := by
    rw [RingHom.mem_ker]
    change PadicInt.toZModPow 2 (secondProductSum p (pinv p)+((2:ℕ):ℤ_[p])+(p:ℤ_[p]))=0
    rw [map_add,map_add,map_natCast,map_natCast,secondProductSum_map,h]
    ring
  rw [PadicInt.ker_toZModPow,Ideal.mem_span_singleton] at hy
  obtain ⟨z,hz⟩ := hy
  have hdiff : ((a (p-1)-(1-2*(p:ℤ)-(p:ℤ)^2):ℤ):ℤ_[p]) = (p:ℤ_[p])^3*z := by
    push_cast
    rw [model_second (by omega)]
    have hLeft : 1+(p:ℤ_[p])*secondProductSum p (pinv p)-
        (1-2*(p:ℤ_[p])-(p:ℤ_[p])^2)=(p:ℤ_[p])*y := by dsimp [y]; ring
    rw [hLeft,hz]
    ring
  have hmap := congrArg (PadicInt.toZModPow 3) hdiff
  simp only [map_intCast,map_mul,map_natCast,←Nat.cast_pow,ZMod.natCast_self,zero_mul] at hmap
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmap

end Final
end A361717Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a361717.main := by
  constructor
  · intro p hp hp5
    let : Fact p.Prime := ⟨hp⟩
    exact A361717Proof.first_congruence hp5
  · intro p hp hp3
    by_cases h2 : p=2
    · subst p
      norm_num [OMA.S_oeis_a361717.a]
    have hp5 : 5≤p := by
      by_contra! h
      have hcases : p=2 ∨ p=3 ∨ p=4 := by have := hp.two_le; omega
      rcases hcases with rfl|rfl|rfl
      · exact h2 rfl
      · exact hp3 rfl
      · exact (by decide : ¬Nat.Prime 4) hp
    let : Fact p.Prime := ⟨hp⟩
    exact A361717Proof.second_congruence hp5
