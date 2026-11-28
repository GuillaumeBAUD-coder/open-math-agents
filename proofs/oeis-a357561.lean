import OMAStatements.S_oeis_a357561

/-! After extracting the common factor p² from the binomial squares, work
with the image of p in a ring where p² vanishes. The reflection k ↦ p-k
turns the normalized harmonic sum into an ordinary finite field power sum. -/

namespace A357561Proof

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

private theorem pow_linearize (t : R) {P : R} (hP : P^2=0) (r : ℕ) :
    (1+P*t)^r = 1+(r:R)*P*t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination ((r:R)*t^2)*hP

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

private theorem pow_inv_reflect {p r : ℕ} {x : ℕ → R} (hP : (p:R)^2=0)
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1) (hr : Odd r) {j : ℕ} (hj : j ∈ Ico 1 p) :
    x (p-j)^r = -x j^r-(r:R)*(p:R)*x j^(r+1) := by
  rw [inv_reflect hP hx hj]
  rw [show -x j-(p:R)*x j^2 = (-x j)*(1+(p:R)*x j) by ring,
    mul_pow, hr.neg_pow, pow_linearize _ hP, pow_succ]
  ring

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

private def reducedTerm (p r : ℕ) (x : ℕ → R) (k : ℕ) : R :=
  x k^r * (1 + (p:R)*harmon x (k-1) - (p:R)*x k)

private theorem reduced_sum_zero {p r : ℕ} (hp : 1 < p) {x : ℕ → R}
    (hP : (p:R)^2=0) (h2 : IsUnit (2 : R))
    (hx : ∀ j ∈ Ico 1 p, (j:R)*x j=1) (hr : Odd r)
    (hPow : (p:R)*(∑ j ∈ Ico 1 p, x j^(r+1))=0) :
    ∑ k ∈ Ico 1 p, reducedTerm p r x k = 0 := by
  have hterm (k : ℕ) (hk : k ∈ Ico 1 p) :
      reducedTerm p r x k + reducedTerm p r x (p-k) =
        -((r:R)+3)*(p:R)*x k^(r+1) := by
    have hkn := (mem_Ico.mp hk).1
    simp only [reducedTerm]
    rw [pow_inv_reflect hP hx hr hk,
      weighted_harmon_reflect hp hP h2 hx hk, harmon_step x hkn]
    have hi : (p:R)*x (p-k) = -(p:R)*x k := by
      rw [inv_reflect hP hx hk]
      linear_combination -(x k)^2*hP
    rw [hi, pow_succ]
    linear_combination (-(r:R)*x k^r*x k*(harmon x (k-1)+2*x k))*hP
  have hreflect := reflect_sum (R:=R) (p:=p) (k:=p-1) (by omega) (reducedTerm p r x)
  rw [show p-1+1=p by omega, show p-(p-1)=1 by omega] at hreflect
  apply cancel_two h2
  calc
    _ = ∑ k ∈ Ico 1 p, (reducedTerm p r x k + reducedTerm p r x (p-k)) := by
      rw [sum_add_distrib, hreflect]
      ring
    _ = -((r:R)+3) * ((p:R)*∑ k ∈ Ico 1 p, x k^(r+1)) := by
      rw [← mul_assoc, mul_sum]
      exact sum_congr rfl (fun k hk => hterm k hk)
    _ = 0 := by rw [hPow,mul_zero]

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

private def rawModel {R : Type*} [CommRing R] (p r : ℕ) (x : ℕ → R) : R :=
  ∑ k ∈ Ico 1 p, x k^r * (∏ j ∈ Ico 1 (k+1), (1-(p:R)*x j)) *
    (∏ j ∈ Ico 1 k, (1+(p:R)*x j))^2

private theorem rawModel_map {R S : Type*} [CommRing R] [CommRing S] (p r : ℕ)
    (f : R →+* S) (x : ℕ → R) : f (rawModel p r x) = rawModel p r (f ∘ x) := by
  simp [rawModel]

private theorem rawModel_congr {R : Type*} [CommRing R] {p r : ℕ}
    {x y : ℕ → R} (h : ∀ j ∈ Ico 1 p, x j = y j) :
    rawModel p r x = rawModel p r y := by
  unfold rawModel
  apply sum_congr rfl
  intro k hk
  have hh (j : ℕ) (hj : j ∈ Ico 1 (k+1)) : x j = y j := by
    have hj' := mem_Ico.mp hj
    have hk' := mem_Ico.mp hk
    exact h j (mem_Ico.mpr ⟨hj'.1, by omega⟩)
  have hu (j : ℕ) (hj : j ∈ Ico 1 k) : x j = y j :=
    h j (mem_Ico.mpr ⟨(mem_Ico.mp hj).1,(mem_Ico.mp hj).2.trans (mem_Ico.mp hk).2⟩)
  have hlow : (∏ j ∈ Ico 1 (k+1), (1-(p:R)*x j)) =
      ∏ j ∈ Ico 1 (k+1), (1-(p:R)*y j) :=
    prod_congr rfl fun j hj => by rw [hh j hj]
  have hup : (∏ j ∈ Ico 1 k, (1+(p:R)*x j)) =
      ∏ j ∈ Ico 1 k, (1+(p:R)*y j) :=
    prod_congr rfl fun j hj => by rw [hu j hj]
  rw [h k hk, hlow, hup]

private theorem rawModel_reduces {R : Type*} [CommRing R] {p r : ℕ} (x : ℕ → R)
    (hP : (p:R)^2=0) :
    rawModel p r x = ∑ k ∈ Ico 1 p, reducedTerm p r x k := by
  unfold rawModel
  apply sum_congr rfl
  intro k hk
  have hk0 := (mem_Ico.mp hk).1
  have hN : (-(p:R))^2=0 := by rwa [neg_sq]
  have hminus : (∏ j ∈ Ico 1 (k+1), (1-(p:R)*x j)) = 1-(p:R)*harmon x k := by
    simpa only [neg_mul, sub_eq_add_neg, harmon] using
      prod_linearize (Ico 1 (k+1)) x hN
  have hplus : (∏ j ∈ Ico 1 k, (1+(p:R)*x j)) = 1+(p:R)*harmon x (k-1) := by
    rw [prod_linearize _ _ hP, harmon, show k-1+1=k by omega]
  rw [hminus,hplus,harmon_step x hk0,reducedTerm]
  linear_combination x k^r * (harmon x (k-1)^2 -
    2*harmon x (k-1)*(harmon x (k-1)+x k) -
    (p:R)*(harmon x (k-1)+x k)*harmon x (k-1)^2) * hP

open scoped Padic
open OMA.S_oeis_a357561

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

private theorem normalized_mod_zero (m : ℕ) (hm : Odd m) (hmp : m+4<p) :
    PadicInt.toZModPow 2 (rawModel p (m+2) (pinv p)) = 0 := by
  let x := PadicInt.toZModPow 2 ∘ pinv p
  have hP : (p:ZMod (p^2))^2=0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have h2 : IsUnit (2:ZMod (p^2)) := by
    have hh := (padicNat_isUnit (p:=p) 2 (mem_Ico.mpr ⟨by decide,by omega⟩)).map
      (PadicInt.toZModPow 2)
    change IsUnit (PadicInt.toZModPow 2 ((2:ℕ):ℤ_[p])) at hh
    rw [map_natCast] at hh
    exact hh
  have hx : ∀ j ∈ Ico 1 p, (j:ZMod (p^2))*x j=1 := by
    intro j hj
    simpa [x] using congrArg (PadicInt.toZModPow 2) (pinv_spec j hj)
  have hPow := inverse_power_sum_mod (p:=p) (m+2+1) (by omega) (by omega) hx
  rw [rawModel_map, rawModel_reduces _ hP]
  have hmOdd : Odd (m+2) := by
    obtain ⟨k,hk⟩ := hm
    refine ⟨k+1,?_⟩
    omega
  exact reduced_sum_zero (by omega) hP h2 hx hmOdd hPow

private theorem s_padic_model (m : ℕ) (hp2 : 2 < p) :
    ((s m (p-1) : ℚ) : ℚ_[p]) =
      (p:ℚ_[p])^2 * ((rawModel p (m+2) (pinv p) : ℤ_[p]) : ℚ_[p]) := by
  have hpEven : Even (p-1) := by
    obtain ⟨k,hk⟩ := hp.out.odd_iff.2 (by omega)
    exact ⟨k,by omega⟩
  have hi : Icc 1 (p-1) = Ico 1 p := by
    ext k
    simp only [mem_Icc,mem_Ico]
    omega
  change ((s m (p-1) : ℚ) : ℚ_[p]) =
      (p:ℚ_[p])^2 * PadicInt.Coe.ringHom (rawModel p (m+2) (pinv p))
  rw [rawModel_map]
  have hraw :
      rawModel p (m+2) (PadicInt.Coe.ringHom ∘ pinv p) =
        rawModel p (m+2) (fun j => (j:ℚ_[p])⁻¹) :=
    rawModel_congr (fun j hj => pinv_coe j hj)
  rw [hraw]
  simp only [s, hi, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_div, Rat.cast_natCast, rawModel, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk0 := (mem_Ico.mp hk).1
  have hk1 := (mem_Ico.mp hk).2
  have hs : (-1:ℚ_[p])^(p-1+k)=(-1)^k := by
    rw [pow_add, hpEven.neg_one_pow, one_mul]
  rw [hs]
  let lower := ((p-1).choose k : ℚ_[p])
  let upper := ((p-1+k).choose k : ℚ_[p])
  change (-1:ℚ_[p])^k * (1/(k:ℚ_[p])^m) * lower * upper^2 = _
  calc
    _ = (lower*(-1)^k)*upper^2*(1/(k:ℚ_[p])^m) := by ring
    _ = _ := by
      rw [show lower*(-1)^k = _ from lower_binomial (K:=ℚ_[p]) p k hk1,
        show upper = _ from upper_binomial (K:=ℚ_[p]) p k (by omega) hk0]
      simp only [div_eq_mul_inv,one_mul, inv_pow, pow_add]
      ring

private theorem numerator_divisibility (m : ℕ) (hm : Odd m) (hmp : m+4<p) :
    ((p:ℤ)^4) ∣ S m (p-1) := by
  let y := rawModel p (m+2) (pinv p)
  have hy : y ∈ RingHom.ker (PadicInt.toZModPow 2 : ℤ_[p] →+* ZMod (p^2)) := by
    rw [RingHom.mem_ker]
    exact normalized_mod_zero m hm hmp
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hy
  obtain ⟨z,hz⟩ := hy
  let q := s m (p-1)
  have heq : (q.num : ℤ_[p]) = (p:ℤ_[p])^4*(z*(q.den:ℤ_[p])) := by
    apply Subtype.coe_injective
    have hq := congrArg (fun r : ℚ => (r:ℚ_[p])) (Rat.mul_den_eq_num q)
    push_cast at hq ⊢
    rw [← hq]
    have hm := s_padic_model (p:=p) m (by omega)
    change (q:ℚ_[p]) = (p:ℚ_[p])^2 * (y:ℚ_[p]) at hm
    rw [hm,hz]
    push_cast
    ring
  have hmod := congrArg (PadicInt.toZModPow 4) heq
  simp only [map_intCast,map_mul,map_natCast, ← Nat.cast_pow, ZMod.natCast_self,
    zero_mul] at hmod
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod

end PadicModel
end A357561Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a357561.main := by
  constructor
  · intro m p hm hp hmp
    let : Fact p.Prime := ⟨hp⟩
    exact A357561Proof.numerator_divisibility m hm hmp
  · intro p hp h
    rcases h with rfl | h11
    · have hS : OMA.S_oeis_a357561.s 3 4 = (-15625 : ℚ) / 432 := by
        have hi : Finset.Icc (1:ℕ) 4 = {1,2,3,4} := by decide
        norm_num [OMA.S_oeis_a357561.s, hi, Nat.choose]
      change ((5:ℤ)^4) ∣ (OMA.S_oeis_a357561.s 3 4).num
      rw [hS]
      have hnum : ((-15625 : ℚ) / 432).num = -15625 := by
        exact Rat.num_div_eq_of_coprime (a := -15625) (b := 432) (by decide) (by decide)
      rw [hnum]
      exact ⟨-25, by norm_num⟩
    · let : Fact p.Prime := ⟨hp⟩
      exact A357561Proof.numerator_divisibility 3 (by decide) (by omega)
