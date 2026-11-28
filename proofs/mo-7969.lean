import OMAStatements.S_mo_7969
import Mathlib

-- Problem: Irreducible polynomials with constrained coefficients
-- Credit: @xor2k
-- Let d = 2^n - 1 and let f have coefficients s_i in {1, -1}. Modulo 2, f is
-- 1 + X + ... + X^d = (X+1)^d, so g(X) = f(X+1) is X^d modulo 2. Its constant term is
-- f(1) = sum of the s_i, which is 2 modulo 4 when the product of the s_i is -1 and n ≥ 2.
-- Then g is Eisenstein at 2, hence irreducible over the integers, hence f is irreducible
-- over the integers and (Gauss) over the rationals. For n = 1 all f have degree 1.
-- Multiplying the sign vector by a vector with one entry -1 swaps the sign vectors with
-- product 1 and those with product -1, so the latter are exactly half of all of them.

open OMA.S_mo_7969 Polynomial

namespace OMA.P_mo_7969

noncomputable def P (d : ℕ) (s : Fin (d + 1) → ℤˣ) : ℤ[X] :=
  ∑ i : Fin (d + 1), C ((s i : ℤ)) * X ^ (i : ℕ)

lemma map_P (d : ℕ) (s : Fin (d + 1) → ℤˣ) :
    (P d s).map (Int.castRingHom ℚ) = signPoly d s := by
  simp [P, signPoly, Polynomial.map_sum]

lemma P_split (d : ℕ) (s : Fin (d + 1) → ℤˣ) :
    P d s = (∑ i : Fin d, C ((s (Fin.castSucc i) : ℤ)) * X ^ (i : ℕ))
      + C ((s (Fin.last d) : ℤ)) * X ^ d := by
  simp [P, Fin.sum_univ_castSucc]

lemma natDegree_P (d : ℕ) (s : Fin (d + 1) → ℤˣ) : (P d s).natDegree = d := by
  rw [P_split]
  have h1 : (C ((s (Fin.last d) : ℤ)) * X ^ d).natDegree = d :=
    natDegree_C_mul_X_pow d _ (Units.ne_zero _)
  have h2 := degree_sum_fin_lt (fun i : Fin d => ((s (Fin.castSucc i) : ℤ)))
  rw [natDegree_add_eq_right_of_degree_lt, h1]
  rw [degree_C_mul_X_pow d (Units.ne_zero _)]
  exact h2

lemma leadingCoeff_P (d : ℕ) (s : Fin (d + 1) → ℤˣ) :
    (P d s).leadingCoeff = (s (Fin.last d) : ℤ) := by
  rw [P_split, leadingCoeff_add_of_degree_lt, leadingCoeff_C_mul_X_pow]
  · rw [degree_C_mul_X_pow d (Units.ne_zero _)]
    exact degree_sum_fin_lt (fun i : Fin d => ((s (Fin.castSucc i) : ℤ)))

lemma isPrimitive_of_unit {g : ℤ[X]} (h : IsUnit g.leadingCoeff) : g.IsPrimitive := by
  intro r ⟨q, hq⟩
  apply isUnit_of_dvd_unit _ h
  rw [leadingCoeff, hq, coeff_C_mul]
  exact dvd_mul_right _ _

lemma sum_mod_four : ∀ (m : ℕ) (s : Fin m → ℤˣ),
    (4 : ℤ) ∣ (∑ i, (s i : ℤ)) - m - ((∏ i, s i : ℤˣ) : ℤ) + 1 := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
    intro s
    have h := ih (fun i => s i.succ)
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, Units.val_mul]
    generalize (∏ i : Fin m, s i.succ) = p at h ⊢
    generalize (∑ i : Fin m, (s i.succ : ℤ)) = S at h ⊢
    generalize s 0 = a
    rcases Int.units_eq_one_or a with h0 | h0 <;>
    rcases Int.units_eq_one_or p with h1 | h1 <;>
    · subst h0 h1
      simp only [Units.val_one, Units.val_neg, Nat.cast_succ] at *
      omega

lemma map_P_two (d : ℕ) (s : Fin (d + 1) → ℤˣ) :
    (P d s).map (Int.castRingHom (ZMod 2)) = ∑ i ∈ Finset.range (d + 1), (X : (ZMod 2)[X]) ^ i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (X : (ZMod 2)[X]) ^ i)]
  simp only [P, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Int.units_eq_one_or (s i) with h | h <;> simp [h]

lemma geom_two (n : ℕ) :
    ∑ i ∈ Finset.range (2 ^ n), (X : (ZMod 2)[X]) ^ i = (X + 1) ^ (2 ^ n - 1) := by
  have hX : (X + 1 : (ZMod 2)[X]) ≠ 0 := X_add_C_ne_zero 1
  apply mul_left_cancel₀ hX
  have h1 : (X - 1 : (ZMod 2)[X]) = X + 1 := by
    rw [sub_eq_add_neg]; congr 1; exact (ZModModule.neg_eq_self (1 : (ZMod 2)[X]))
  rw [← h1, mul_geom_sum, h1, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_two_pow), add_pow_char_pow,
    one_pow, sub_eq_add_neg]
  congr 1
  exact (ZModModule.neg_eq_self (1 : (ZMod 2)[X]))

lemma taylor_mod_two (n : ℕ) (s : Fin (2 ^ n - 1 + 1) → ℤˣ) :
    (taylor 1 (P (2 ^ n - 1) s)).map (Int.castRingHom (ZMod 2)) = X ^ (2 ^ n - 1) := by
  rw [map_taylor, map_P_two, Nat.sub_add_cancel (Nat.one_le_two_pow), geom_two, taylor_apply,
    pow_comp, add_comp, X_comp, one_comp]
  congr 1
  rw [map_one, map_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma irreducible_of_prod (n : ℕ) (hn : 1 ≤ n) (s : Fin (2 ^ n - 1 + 1) → ℤˣ)
    (hs : (∏ i, s i) = -1) : Irreducible (signPoly (2 ^ n - 1) s) := by
  have hlead : IsUnit (P (2 ^ n - 1) s).leadingCoeff := by rw [leadingCoeff_P]; exact Units.isUnit _
  have hprim : (P (2 ^ n - 1) s).IsPrimitive := isPrimitive_of_unit hlead
  have hP0 : P (2 ^ n - 1) s ≠ 0 := fun h => by
    rw [h, leadingCoeff_zero] at hlead; exact not_isUnit_zero hlead
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    apply Polynomial.irreducible_of_degree_eq_one
    rw [← map_P, degree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)),
      degree_eq_natDegree hP0, natDegree_P]
    rfl
  rw [← map_P]
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
  · set g := taylor 1 (P (2 ^ n - 1) s) with hg
    have hgdeg : g.natDegree = 2 ^ n - 1 := by rw [hg, natDegree_taylor, natDegree_P]
    have hglead : g.leadingCoeff = (s (Fin.last (2 ^ n - 1)) : ℤ) := by
      rw [hg, leadingCoeff_taylor, leadingCoeff_P]
    have hprime : (Ideal.span {(2 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
    have heis : g.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hglead, Ideal.mem_span_singleton]
        rcases Int.units_eq_one_or (s (Fin.last (2 ^ n - 1))) with h | h <;> rw [h] <;> decide
      · intro k hk
        rw [Ideal.mem_span_singleton]
        have h2' := (ZMod.intCast_zmod_eq_zero_iff_dvd (g.coeff k) 2).mp
        have := congrArg (fun q => q.coeff k) (taylor_mod_two n s)
        simp only [coeff_map, eq_intCast] at this
        rw [this, coeff_X_pow, if_neg (by omega)] at h2'
        exact_mod_cast h2' rfl
      · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hg, taylor_coeff_zero]
        have hev : (P (2 ^ n - 1) s).eval 1 = ∑ i, (s i : ℤ) := by simp [P, eval_finsetSum]
        rw [hev]
        have h4 := sum_mod_four (2 ^ n - 1 + 1) s
        rw [hs] at h4
        have hpow : (4 : ℤ) ∣ ((2 ^ n - 1 + 1 : ℕ) : ℤ) := by
          rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
          refine ⟨2 ^ k, ?_⟩
          push_cast; ring
        intro h
        simp only [Units.val_neg, Units.val_one] at h4
        omega
    have hgirr : Irreducible g := heis.irreducible hprime
      (isPrimitive_of_unit (by rw [hglead]; exact Units.isUnit _)) (by have := Nat.one_lt_two_pow (n := n) (by omega); rw [hgdeg]; omega)
    have := (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ)) (x := P (2 ^ n - 1) s)).mp
    exact this hgirr

lemma card_half (m : ℕ) (p : (Fin (m + 1) → ℤˣ) → Prop)
    (hp : ∀ s, (∏ i, s i) = -1 → p s) :
    Fintype.card (Fin (m + 1) → ℤˣ) ≤ 2 * Nat.card {s // p s} := by
  classical
  set e : Fin (m + 1) → ℤˣ := Pi.mulSingle 0 (-1) with he
  have hee : e * e = 1 := by
    rw [he, ← Pi.mulSingle_mul]; simp
  have hpe : (∏ i, e i) = -1 := by
    rw [he, Finset.prod_pi_mulSingle']; simp
  have hprod : ∀ s : Fin (m + 1) → ℤˣ, (∏ i, (e * s) i) = - ∏ i, s i := by
    intro s; simp only [Pi.mul_apply]; rw [Finset.prod_mul_distrib, hpe]; simp
  have hAB := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (m + 1) → ℤˣ))) (fun s => (∏ i, s i) = -1)
  have hBA : (Finset.univ.filter (fun s : Fin (m + 1) → ℤˣ => ¬ (∏ i, s i) = -1)).card =
      (Finset.univ.filter (fun s : Fin (m + 1) → ℤˣ => (∏ i, s i) = -1)).card := by
    apply Finset.card_nbij' (e * ·) (e * ·)
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      rw [hprod]
      rcases Int.units_eq_one_or (∏ i, s i) with h | h
      · rw [h]
      · exact absurd h hs
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      rw [hprod, hs]; decide
    · intro s _; simp [← mul_assoc, hee]
    · intro s _; simp [← mul_assoc, hee]
  have hA : (Finset.univ.filter (fun s : Fin (m + 1) → ℤˣ => (∏ i, s i) = -1)).card ≤
      Nat.card {s // p s} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hp s hs
  rw [Finset.card_univ] at hAB
  omega

end OMA.P_mo_7969

open OMA.P_mo_7969 in
theorem OMA.solution : type_of% @OMA.S_mo_7969.main := by
  intro n hn
  exact card_half _ _ (fun s hs => irreducible_of_prod n hn s hs)
