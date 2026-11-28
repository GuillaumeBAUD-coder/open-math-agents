import OMAStatements.S_oeis_a220956

-- Problem: A220956: (C(2n,n) - C(2n-2,n-1)) mod n^2 = n + 2 exactly for odd primes
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a220956.main)
-- Credit: @weizj99 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
import Mathlib

namespace A220956

private def residueBlocks (m s w : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => residueBlocks m s w k * (s + k*w).ascFactorial w % m

private theorem residueBlocks_spec (m s w k : ℕ) :
    (residueBlocks m s w k : ZMod m) = (s.ascFactorial (k*w) : ℕ) := by
  induction k with
  | zero => simp [residueBlocks]
  | succ k ih =>
    rw [residueBlocks, ZMod.natCast_mod, Nat.cast_mul, ih,
      ← Nat.cast_mul, Nat.ascFactorial_mul_ascFactorial, Nat.succ_mul]

private def segmentedResidue (m s : ℕ) : ℕ :=
  residueBlocks m s 256 65 * (s + 65*256).ascFactorial 202 % m

private theorem segmentedResidue_spec (m s : ℕ) :
    (segmentedResidue m s : ZMod m) = (s.ascFactorial 16842 : ℕ) := by
  rw [segmentedResidue, ZMod.natCast_mod, Nat.cast_mul, residueBlocks_spec,
    ← Nat.cast_mul, Nat.ascFactorial_mul_ascFactorial]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
private theorem residue_one : segmentedResidue (16843^4) 1 = 57610133467800119 := by
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
private theorem residue_shifted : segmentedResidue (16843^4) 16844 = 57610133467800119 := by
  decide +kernel

private theorem central_twice (k : ℕ) :
    (k+1).centralBinom = 2 * (k+1+k).choose k := by
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, ← add_assoc,
      Nat.choose_succ_succ' (k+1+k) k, Nat.choose_symm_add, ← two_mul]

private theorem central_from_residues (k m : ℕ) {a : ZMod m} (hu : IsUnit a)
    (hd : ((k.factorial : ℕ) : ZMod m) = a)
    (hn : (((k+1+1).ascFactorial k : ℕ) : ZMod m) = a) :
    ((k+1).centralBinom : ZMod m) = 2 := by
  have he := congrArg (Nat.cast : ℕ → ZMod m) (Nat.ascFactorial_eq_factorial_mul_choose (k+1) k)
  change (((k+1+1).ascFactorial k : ℕ) : ZMod m) =
    ((k.factorial * (k+1+k).choose k : ℕ) : ZMod m) at he
  rw [Nat.cast_mul, hd, hn] at he
  have hc : ((k+1+k).choose k : ZMod m) = 1 := by
    apply hu.mul_left_cancel
    simpa only [mul_one] using he.symm
  rw [central_twice, Nat.cast_mul, hc, mul_one, Nat.cast_ofNat]

theorem finiteCentral : (Nat.centralBinom 16843 : ZMod (16843^4)) = 2 := by
  let M := 16843^4
  have hd : ((Nat.factorial 16842 : ℕ) : ZMod M) = (57610133467800119 : ℕ) := by
    rw [← Nat.one_ascFactorial, ← segmentedResidue_spec, residue_one]
  have hn : ((Nat.ascFactorial 16844 16842 : ℕ) : ZMod M) = (57610133467800119 : ℕ) := by
    rw [← segmentedResidue_spec, residue_shifted]
  have hu : IsUnit ((57610133467800119 : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).2 (by decide)
  exact central_from_residues 16842 M hu hd hn

end A220956

namespace A220956

open Finset

def intervalProd (a m : ℕ) : ℕ := ∏ i ∈ range m, (a + (i+1))

def kept (p a k : ℕ) : ℕ := if p ∣ k then 1 else a+k

def keptProd (p a m : ℕ) : ℕ := ∏ i ∈ range m, kept p a (i+1)

def multipleTerm (p a k : ℕ) : ℕ := if p ∣ k then a+k else 1

theorem multipleBlock (q a m : ℕ) :
    (∏ i ∈ range (q+1), multipleTerm (q+1) ((q+1)*a) ((q+1)*m+i+1)) =
      (q+1)*(a+(m+1)) := by
  rw [prod_range_succ]
  have hfirst : (∏ i ∈ range q, multipleTerm (q+1) ((q+1)*a) ((q+1)*m+i+1)) = 1 := by
    apply prod_eq_one
    intro i hi
    have hlt := mem_range.mp hi
    have hn : ¬ q+1 ∣ i+1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hx : ¬ q+1 ∣ (q+1)*m+i+1 := by
      simpa [Nat.add_assoc, Nat.dvd_add_right (dvd_mul_right (q+1) m)] using hn
    simp [multipleTerm, hx]
  have he : (q+1)*m+q+1 = (q+1)*(m+1) := by ring
  rw [hfirst, one_mul, he]
  simp [multipleTerm, Nat.mul_add]

theorem multipleProduct (q a m : ℕ) :
    (∏ i ∈ range ((q+1)*m), multipleTerm (q+1) ((q+1)*a) (i+1)) =
      (q+1)^m * intervalProd a m := by
  induction m with
  | zero => simp [intervalProd]
  | succ m ih =>
    rw [Nat.mul_succ, prod_range_add, ih]
    change _ * (∏ i ∈ range (q+1), multipleTerm (q+1) ((q+1)*a) ((q+1)*m+i+1)) = _
    rw [multipleBlock, pow_succ]
    simp only [intervalProd, prod_range_succ]
    ring

theorem splitInterval (p a m : ℕ) (hp : 0 < p) :
    intervalProd (p*a) (p*m) = (p^m * intervalProd a m) * keptProd p (p*a) (p*m) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [← multipleProduct, keptProd, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases h : q+1 ∣ i+1 <;> simp [kept, multipleTerm, h]

theorem intervalZero (m : ℕ) : intervalProd 0 m = m.factorial := by
  simp [intervalProd]

theorem intervalCentral (m : ℕ) :
    intervalProd m m = Nat.centralBinom m * intervalProd 0 m := by
  rw [intervalZero, mul_comm, Nat.centralBinom, two_mul, ← Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.ascFactorial_eq_prod_range]
  apply prod_congr rfl
  intro i _
  omega

theorem chooseSplit (p : ℕ) (hp : 0 < p) :
    Nat.centralBinom (p*p) * keptProd p 0 (p*p) =
      Nat.centralBinom p * keptProd p (p*p) (p*p) := by
  have hz := splitInterval p 0 p hp
  simp only [mul_zero] at hz
  have hn := splitInterval p p p hp
  rw [intervalCentral (p*p), hz, intervalCentral p] at hn
  apply Nat.mul_left_cancel (n := p^p * intervalProd 0 p)
  · rw [intervalZero]
    positivity
  · calc
      _ = Nat.centralBinom (p*p) * (p^p * intervalProd 0 p * keptProd p 0 (p*p)) := by ac_rfl
      _ = _ := hn
      _ = _ := by ac_rfl

theorem reflectHalf {R : Type*} [CommMonoid R] (f : ℕ → R) (h : ℕ) :
    (∏ i ∈ range (h+h), f (i+1)) =
    ∏ i ∈ range h, (f (i+1) * f (h+h+1-(i+1))) := by
  rw [prod_range_add, prod_mul_distrib]
  congr 1
  rw [← prod_range_reflect (fun i => f (h+i+1)) h]
  apply prod_congr rfl
  intro i hi
  congr 1
  have := mem_range.mp hi
  omega

theorem keptPair (p n k : ℕ) (hpk : p ∣ n) (hk : k ≤ n) :
    (kept p n k : ZMod (n^2)) * (kept p n (n-k) : ℕ) =
      (kept p 0 k : ZMod (n^2)) * (kept p 0 (n-k) : ℕ) := by
  have hd : p ∣ n-k ↔ p ∣ k := by
    constructor
    · intro hh
      have := Nat.dvd_sub hpk hh
      rwa [Nat.sub_sub_self hk] at this
    · exact Nat.dvd_sub hpk
  by_cases h : p ∣ k
  · simp [kept, h, hd]
  · simp only [kept, if_neg h, if_neg (mt hd.mp h), Nat.zero_add, Nat.cast_add,
      Nat.cast_sub hk]
    have hz : (n : ZMod (n^2))^2 = 0 := by simp [← Nat.cast_pow]
    linear_combination 2 * hz

theorem keptReflect (p n h : ℕ) (he : n = h+h+1) (hd : p ∣ n) :
    (keptProd p n n : ZMod (n^2)) = (keptProd p 0 n : ZMod (n^2)) := by
  have expand (a : ℕ) : (keptProd p a n : ZMod (n^2)) =
      ∏ i ∈ range h, ((kept p a (i+1) : ZMod (n^2)) * (kept p a (n-(i+1)) : ℕ)) := by
    unfold keptProd
    rw [Nat.cast_prod]
    conv_lhs => arg 1; rw [he]
    rw [prod_range_succ, ← he]
    simp only [kept, if_pos hd, Nat.cast_one, mul_one]
    simpa only [← he, kept] using (reflectHalf (fun k => (kept p a k : ZMod (n^2))) h)
  rw [expand, expand]
  apply prod_congr rfl
  intro i hi
  have := mem_range.mp hi
  exact keptPair p n (i+1) hd (by omega)

theorem keptUnit (p m : ℕ) (hp : p.Prime) :
    IsUnit (keptProd p 0 m : ZMod (p^4)) := by
  rw [keptProd, Nat.cast_prod, IsUnit.prod_iff]
  intro i _
  by_cases h : p ∣ i+1
  · simp [kept, h]
  · simpa [kept, h] using (ZMod.isUnit_natCast_iff_not_dvd_pow (a := i+1) hp (by decide : 0 < 4)).mpr h


theorem liftCentral (p h : ℕ) (hp : p.Prime) (hh : p*p = h+h+1) :
    (Nat.centralBinom (p*p) : ZMod ((p*p)^2)) = (Nat.centralBinom p : ℕ) := by
  have hm : (p*p)^2 = p^4 := by ring
  have hu : IsUnit (keptProd p 0 (p*p) : ZMod ((p*p)^2)) := by
    rw [hm]
    exact keptUnit p (p*p) hp
  apply hu.mul_right_cancel
  have hs := congrArg (fun v : ℕ => (v : ZMod ((p*p)^2))) (chooseSplit p hp.pos)
  simp only [Nat.cast_mul] at hs
  rw [keptReflect p (p*p) h hh (dvd_mul_right p p)] at hs
  exact hs

theorem previousCentral (n : ℕ) (hn : 0 < n)
    (htwo : IsUnit (2 : ZMod (n^2)))
    (hc : (Nat.centralBinom n : ZMod (n^2)) = 2) :
    (Nat.centralBinom (n-1) : ZMod (n^2)) = -(n : ZMod (n^2)) := by
  have hprev : n-1+1 = n := by omega
  have hrec := Nat.succ_mul_centralBinom_succ (n-1)
  rw [hprev] at hrec
  have e := congrArg (fun v : ℕ => (v : ZMod (n^2))) hrec
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hn, hc] at e
  have he : (n : ZMod (n^2)) = (2*(n : ZMod (n^2))-1) * (Nat.centralBinom (n-1) : ℕ) := by
    apply htwo.mul_left_cancel
    linear_combination e
  have hz : (n : ZMod (n^2))^2 = 0 := by simp [← Nat.cast_pow]
  linear_combination (2*(n : ZMod (n^2))+1)*he + (4*(Nat.centralBinom (n-1) : ZMod (n^2))-2)*hz

theorem residueFromCentral (n : ℕ) (hn : 0 < n) (hb : n+2 < n^2)
    (htwo : IsUnit (2 : ZMod (n^2)))
    (hc : (Nat.centralBinom n : ZMod (n^2)) = 2) :
    ((2*n).choose n - (2*n-2).choose (n-1)) % n^2 = n+2 := by
  have hp := previousCentral n hn htwo hc
  have hl := Nat.centralBinom_strictMono.monotone (Nat.sub_le n 1)
  have eqn : 2*n-2 = 2*(n-1) := by omega
  rw [eqn]
  change (Nat.centralBinom n - Nat.centralBinom (n-1)) % n^2 = n+2
  have he : ((Nat.centralBinom n - Nat.centralBinom (n-1) : ℕ) : ZMod (n^2)) = ((n+2 : ℕ) : ZMod (n^2)) := by
    rw [Nat.cast_sub hl, hc, hp, Nat.cast_add, Nat.cast_ofNat]
    ring
  simpa only [Nat.mod_eq_of_lt hb] using (ZMod.natCast_eq_natCast_iff' _ _ _).mp he

theorem atSquare (hc : (Nat.centralBinom 16843 : ZMod (16843^4)) = 2) :
    ((2*283686649).choose 283686649 - (2*283686649-2).choose (283686649-1)) %
      283686649^2 = 283686649+2 := by
  apply residueFromCentral
  · decide
  · decide
  · exact (ZMod.isUnit_iff_coprime 2 _).mpr (by decide)
  · have h := liftCentral 16843 141843324 (by norm_num) (by decide)
    exact h.trans hc

theorem compositeSquare : ¬ Nat.Prime 283686649 := by
  change ¬ Nat.Prime (16843*16843)
  exact Nat.not_prime_mul (by decide) (by decide)

end A220956

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a220956.main) := by
  intro h
  have hp := ((h 283686649 (by decide)).mp (A220956.atSquare A220956.finiteCentral)).1
  exact A220956.compositeSquare hp
