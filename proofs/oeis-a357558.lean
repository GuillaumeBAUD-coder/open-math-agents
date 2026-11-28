import OMAStatements.S_oeis_a357558

-- Problem: A357558: a supercongruence for Sum_k (-1)^(n+k) * k * C(n,k) * C(n+k,k)^2
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a357558.main)
-- Credit: @weizj99 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
import Mathlib

namespace A357558

open Finset

theorem index_dvd (n : ℕ) : (n : ℤ) ∣ OMA.S_oeis_a357558.a n := by
  unfold OMA.S_oeis_a357558.a
  apply Finset.dvd_sum
  intro k _
  cases k with
  | zero => simp
  | succ k =>
    cases n with
    | zero => simp
    | succ n =>
      have h := Nat.add_one_mul_choose_eq n k
      refine ⟨(-1 : ℤ) ^ (((n+1) + (k+1))) * n.choose k *
        ((((n+1) + (k+1))).choose (k+1) : ℤ) ^ 2, ?_⟩
      have he : ((n+1 : ℕ) : ℤ) * n.choose k =
          ((n+1).choose (k+1) : ℤ) * ((k+1 : ℕ) : ℤ) := by exact_mod_cast h
      linear_combination - ((-1 : ℤ) ^ (((n+1) + (k+1))) *
          ((((n+1) + (k+1))).choose (k+1) : ℤ)^2) * he

abbrev Residue (p : ℕ) := ZMod (p^4)

noncomputable def recip (p k : ℕ) : Residue p := ((k+1 : ℕ) : Residue p)⁻¹

noncomputable def prefixSum (p k : ℕ) : Residue p := ∑ i ∈ range k, recip p i

theorem recip_cancel {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    ((k+1 : ℕ) : Residue p) * recip p k = 1 := by
  apply ZMod.mul_inv_of_unit
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 4)).2
  exact Nat.not_dvd_of_pos_of_lt (by omega) hk

def signedChoose (p k : ℕ) : Residue p :=
  (-1 : Residue p)^k * ((p-1).choose k : Residue p)

def upperChoose (p k : ℕ) : Residue p := ((p+k).choose k : Residue p)

theorem signed_step {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    signedChoose p (k+1) = signedChoose p k * (1 - (p : Residue p) * recip p k) := by
  have h := Nat.choose_succ_right_eq (p-1) k
  have he : (((p-1).choose (k+1) : ℕ) : Residue p) * ((k+1 : ℕ) : Residue p) =
      (((p-1).choose k : ℕ) : Residue p) * ((p-1-k : ℕ) : Residue p) := by
    simpa only [Nat.cast_mul] using congrArg (fun m : ℕ => (m : Residue p)) h
  have he' : ((p-1-k : ℕ) : Residue p) = (p : Residue p) - ((k+1 : ℕ) : Residue p) := by
    rw [show p-1-k = p-(k+1) by omega, Nat.cast_sub (by omega)]
  rw [he'] at he
  unfold signedChoose
  rw [pow_succ (-1 : Residue p) k]
  have hu := recip_cancel hp hk
  linear_combination (-1 : Residue p)^k *
    ((((p-1).choose (k+1) : ℕ) : Residue p) + (((p-1).choose k : ℕ) : Residue p)) * hu -
    (-1 : Residue p)^k * recip p k * he

theorem upper_step {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    upperChoose p (k+1) = upperChoose p k * (1 + (p : Residue p) * recip p k) := by
  have h := (Nat.add_one_mul_choose_eq (p+k) k).symm
  have he : (((p+(k+1)).choose (k+1) : ℕ) : Residue p) * ((k+1 : ℕ) : Residue p) =
      ((p : Residue p) + ((k+1 : ℕ) : Residue p)) * upperChoose p k := by
    unfold upperChoose
    simpa only [Nat.add_assoc, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun m : ℕ => (m : Residue p)) h
  unfold upperChoose at *
  linear_combination recip p k * he +
    ((((p+k).choose k : ℕ) : Residue p) - (((p+(k+1)).choose (k+1) : ℕ) : Residue p)) *
    recip_cancel hp hk

theorem lower_step {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    (((p+k).choose (k+1) : ℕ) : Residue p) =
      (p : Residue p) * recip p k * upperChoose p k := by
  have h := Nat.choose_succ_right_eq (p+k) k
  rw [Nat.add_sub_cancel] at h
  have he : (((p+k).choose (k+1) : ℕ) : Residue p) * ((k+1 : ℕ) : Residue p) =
      upperChoose p k * (p : Residue p) := by
    unfold upperChoose
    simpa only [Nat.cast_mul] using congrArg (fun m : ℕ => (m : Residue p)) h
  linear_combination recip p k * he - (((p+k).choose (k+1) : ℕ) : Residue p) *
    recip_cancel hp hk

theorem fourth_zero (p : ℕ) : (p : Residue p)^4 = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

theorem scaled_product {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (p : Residue p)^2 * (signedChoose p k * upperChoose p k ^ 2) =
    (p : Residue p)^2 + (p : Residue p)^3 * prefixSum p k := by
  induction k with
  | zero => simp [signedChoose, upperChoose, prefixSum]
  | succ k ih =>
    specialize ih (by omega)
    rw [signed_step hp hk, upper_step hp hk]
    have hs : prefixSum p (k+1) = prefixSum p k + recip p k := sum_range_succ _ _
    rw [hs]
    have h4 := fourth_zero p
    generalize (p : Residue p) = t at ih h4 ⊢
    generalize signedChoose p k = a, upperChoose p k = b, recip p k = u,
      prefixSum p k = H at ih ⊢
    linear_combination (1-t*u)*(1+t*u)^2 * ih +
      (-u^2 - t*u^3 + H*u - t*H*u^2 - t^2*H*u^3) * h4

theorem summand_expand {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    signedChoose p (k+1) * ((k+1 : ℕ) : Residue p) *
      (((p+k).choose (k+1) : ℕ) : Residue p)^2 =
    (p : Residue p)^2 * recip p k +
      (p : Residue p)^3 * recip p k * (prefixSum p k - recip p k) := by
  rw [signed_step hp hk, lower_step hp hk]
  have hc := scaled_product hp k (by omega : k < p)
  have hu := recip_cancel hp hk
  have h4 := fourth_zero p
  generalize (p : Residue p) = t, signedChoose p k = a, upperChoose p k = b,
    ((k+1 : ℕ) : Residue p) = m, recip p k = u, prefixSum p k = H at hc hu h4 ⊢
  linear_combination a*(1-t*u)*t^2*u*b^2 * hu + u*(1-t*u)*hc - H*u^2*h4

theorem twice_expanded {R : Type*} [CommRing R] (t : R) (u : ℕ → R) (n : ℕ) :
    2 * (∑ k ∈ range n, (t^2 * u k + t^3 * u k * ((∑ i ∈ range k, u i) - u k))) =
    2 * t^2 * (∑ i ∈ range n, u i) + t^3 * (∑ i ∈ range n, u i)^2 -
      3 * t^3 * ∑ i ∈ range n, (u i)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ] at ⊢
    linear_combination ih

theorem reduce_sum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (h1 : (p : Residue p)^2 * prefixSum p (p-1) = 0)
    (h2 : (p : Residue p)^3 * (∑ k ∈ range (p-1), (recip p k)^2) = 0) :
    ((OMA.S_oeis_a357558.a (p-1) : ℤ) : Residue p) = 0 := by
  have hd := twice_expanded (p : Residue p) (recip p) (p-1)
  have hf (m : ℕ) : (∑ i ∈ range m, recip p i) = prefixSum p m := rfl
  simp only [hf] at hd
  have ht : (2 : Residue p) * (∑ k ∈ range (p-1), ((p : Residue p)^2 * recip p k +
      (p : Residue p)^3 * recip p k * (prefixSum p k - recip p k))) = 0 := by
    linear_combination hd + (2 + (p : Residue p) * prefixSum p (p-1)) * h1 - 3 * h2
  have hunit : IsUnit (2 : Residue p) := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow (a := 2) hp (by decide : 0 < 4)).2
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hs := congrArg (fun z : Residue p => (2 : Residue p)⁻¹ * z) ht
  rw [← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul, mul_zero] at hs
  unfold OMA.S_oeis_a357558.a
  push_cast
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [← mul_zero ((-1 : Residue p)^(p-1)), ← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [← summand_expand hp (by omega : k+1 < p), pow_add]
  rw [show p-1+(k+1) = p+k by omega]
  unfold signedChoose
  push_cast
  ring

theorem combine_factors {p : ℕ} (hp : p.Prime)
    (h : ((OMA.S_oeis_a357558.a (p-1) : ℤ) : Residue p) = 0) :
    (((p-1)*p^4 : ℕ) : ℤ) ∣ OMA.S_oeis_a357558.a (p-1) := by
  have hc : (p-1).Coprime p := (Nat.coprime_self_sub_left hp.pos).2 (Nat.coprime_one_left _)
  rw [Nat.cast_mul]
  exact (hc.pow_right 4).isCoprime.mul_dvd (index_dvd _) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

private theorem harm_unit {p i : ℕ} (hp : p.Prime) (hi : 0 < i) (hlt : i < p) :
    IsUnit (i : ZMod (p^4)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2 (Nat.not_dvd_of_pos_of_lt hi hlt)

private theorem harm_field_sum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ range (p-1), (((k+1 : ℕ) : ZMod p)⁻¹)^2 = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let e : Fin p ≃ ZMod p :=
    { toFun := fun i => (i.val : ZMod p)
      invFun := fun x => ⟨x.val, x.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := ZMod.natCast_zmod_val }
  have hfield : ∑ x : ZMod p, x^2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have hinv : ∑ x : ZMod p, x⁻¹^2 = 0 := by
    rw [← hfield]
    exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x^2)
  have hall : ∑ k ∈ range p, ((k : ZMod p)⁻¹)^2 = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact (e.sum_comp (fun x => x⁻¹^2)).trans hinv
  conv at hall => lhs; arg 1; rw [show p = (p-1)+1 by omega]
  simpa [Finset.sum_range_succ'] using hall

private theorem harm_kernel {p : ℕ} (hp : p.Prime)
    (f : ZMod (p^4) →+* ZMod p) (x : ZMod (p^4)) (hx : f x = 0) :
    (p : ZMod (p^4))^3 * x = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hv := ZMod.natCast_zmod_val x
  rw [← hv, map_natCast] at hx
  obtain ⟨a,ha⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hx
  rw [← hv, ha, Nat.cast_mul]
  calc
    _ = (p : ZMod (p^4))^4 * (a : ZMod (p^4)) := by ring
    _ = 0 := by rw [fourth_zero, zero_mul]

theorem harmonic_two_vanish {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ZMod (p^4))^3 * (∑ k ∈ range (p-1), (((k+1 : ℕ) : ZMod (p^4))⁻¹)^2) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (show p ∣ p^4 from dvd_pow_self _ (by decide)) (ZMod p)
  apply harm_kernel hp f
  rw [map_sum]
  refine (Finset.sum_congr rfl ?_).trans (harm_field_sum hp h5)
  intro k hk
  rw [Finset.mem_range] at hk
  have hu := harm_unit hp (i := k+1) (by omega) (by omega)
  have hm := congrArg f (ZMod.mul_inv_of_unit _ hu)
  rw [map_mul, map_natCast, map_one] at hm
  rw [map_pow, ← ZMod.inv_eq_of_mul_eq_one _ _ _ hm]

theorem harmonic_one_vanish {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ZMod (p^4))^2 * (∑ k ∈ range (p-1), ((k+1 : ℕ) : ZMod (p^4))⁻¹) = 0 := by
  let u := fun k : ℕ => ((k+1 : ℕ) : ZMod (p^4))⁻¹
  let t : ZMod (p^4) := p
  have pair (k : ℕ) (hk : k ∈ range (p-1)) :
      t^2 * (u k + u (p-1-1-k)) + t^3 * (u k)^2 = 0 := by
    rw [Finset.mem_range] at hk
    let j := p-1-1-k
    have h1 := ZMod.mul_inv_of_unit _ (harm_unit hp (i := k+1) (by omega) (by omega))
    have h2 := ZMod.mul_inv_of_unit _ (harm_unit hp (i := j+1) (by omega) (by dsimp [j]; omega))
    have hnat : (k+1)+(j+1) = p := by dsimp [j]; omega
    have ht : ((k+1 : ℕ) : ZMod (p^4)) + ((j+1 : ℕ) : ZMod (p^4)) = t := by
      rw [← Nat.cast_add, hnat]
    change ((k+1 : ℕ) : ZMod (p^4)) * u k = 1 at h1
    change ((j+1 : ℕ) : ZMod (p^4)) * u j = 1 at h2
    have hs : u k + u j = t * u k * u j := by
      rw [← ht]
      linear_combination -u j * h1 - u k * h2
    change t^2 * (u k + u j) + t^3 * (u k)^2 = 0
    calc
      _ = t^3 * u k * (u k + u j) := by linear_combination t^2 * hs
      _ = t^4 * ((u k)^2 * u j) := by rw [hs]; ring
      _ = 0 := by rw [show t^4 = 0 from fourth_zero p, zero_mul]
  have hsum := Finset.sum_congr (s₁ := range (p-1)) rfl pair
  rw [Finset.sum_const_zero, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_range_reflect, harmonic_two_vanish hp h5, add_zero] at hsum
  have hu := ZMod.mul_inv_of_unit _ (harm_unit hp (i := 2) (by decide) (by omega))
  change (2 : ZMod (p^4)) * (2 : ZMod (p^4))⁻¹ = 1 at hu
  change t^2 * (∑ k ∈ range (p-1), u k) = 0
  linear_combination (2 : ZMod (p^4))⁻¹ * hsum - (t^2 * (∑ k ∈ range (p-1), u k)) * hu

end A357558

theorem OMA.solution : type_of% @OMA.S_oeis_a357558.main := by
  intro p hp h5
  exact A357558.combine_factors hp (A357558.reduce_sum hp h5
    (A357558.harmonic_one_vanish hp h5) (A357558.harmonic_two_vanish hp h5))
