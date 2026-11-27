import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib.Tactic

/-!
# Step Proof for OEIS A217785 (`OeisA217785.conjecture_3.R1.H1`)
-/

namespace A217785Step

open Polynomial

lemma coeff_polyS (n j : ℕ) :
    (OeisA217785.polyS n).coeff j = if j ≤ n then (j + 1 : ℤ) else 0 := by
  unfold OeisA217785.polyS
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j ≤ n
  · rw [if_pos hj, Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      exact if_neg hbj.symm
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_range] at hb
    exact if_neg (by omega)

lemma natDegree_polyS (n : ℕ) : (OeisA217785.polyS n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_polyS, if_neg (by omega)]
  · apply le_natDegree_of_ne_zero
    rw [coeff_polyS, if_pos le_rfl]
    positivity

lemma isPrimitive_polyS (n : ℕ) : (OeisA217785.polyS n).IsPrimitive := by
  rintro r ⟨q, hq⟩
  refine IsUnit.of_mul_eq_one (q.coeff 0) ?_
  have h0 := congr_arg (fun f => coeff f 0) hq
  rw [coeff_polyS, if_pos (Nat.zero_le n), coeff_C_mul] at h0
  simp at h0
  exact h0.symm

lemma eq_C_of_natDegree_zero {R : Type*} [Semiring R] {f : R[X]} (hf : f.natDegree = 0) :
    f = C (f.coeff 0) := by
  ext k
  rcases k with _ | k
  · simp
  · rw [coeff_C_of_ne_zero (Nat.succ_ne_zero k), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma mul_sq_sub_one_polyS (n : ℕ) :
    (X - 1 : ℤ[X]) ^ 2 * OeisA217785.polyS n =
      C (n + 1 : ℤ) * X ^ (n + 2) - C (n + 2 : ℤ) * X ^ (n + 1) + 1 := by
  induction n with
  | zero =>
    unfold OeisA217785.polyS
    simp [Finset.range_one]
    ring
  | succ n ih =>
    have hstep : OeisA217785.polyS (n + 1) =
        OeisA217785.polyS n + C ((n + 1 : ℕ) + 1 : ℤ) * X ^ (n + 1) := by
      unfold OeisA217785.polyS
      rw [Finset.sum_range_succ]
    rw [hstep, mul_add, ih]
    simp only [map_add, map_natCast, map_one, map_ofNat]
    push_cast
    ring

lemma two_mul_eval_one_polyS (n : ℕ) :
    2 * (OeisA217785.polyS n).eval 1 = (n + 1 : ℤ) * (n + 2 : ℤ) := by
  induction n with
  | zero =>
    unfold OeisA217785.polyS
    simp
  | succ n ih =>
    have hstep : OeisA217785.polyS (n + 1) =
        OeisA217785.polyS n + C ((n + 1 : ℕ) + 1 : ℤ) * X ^ (n + 1) := by
      unfold OeisA217785.polyS
      rw [Finset.sum_range_succ]
    rw [hstep, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, mul_add, ih]
    push_cast
    ring

lemma two_mul_shifted_coeff_zero (n : ℕ) :
    2 * ((OeisA217785.polyS n).comp (X + 1)).coeff 0 = (n + 1 : ℤ) * (n + 2 : ℤ) := by
  rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
    two_mul_eval_one_polyS]

lemma X_add_one_pow_prime (p : ℕ) (hp : p.Prime) :
    (X + 1 : (ZMod p)[X]) ^ p = X ^ p + 1 := by
  rw [add_pow, Finset.sum_range_succ]
  rw [Finset.sum_eq_single 0]
  · simp [Nat.choose_self]
    ring
  · intro m hm hm0
    rw [Finset.mem_range] at hm
    have hdvd : p ∣ p.choose m := hp.dvd_choose_self hm0 hm
    rw [← map_natCast C, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, map_zero, mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr hp.pos) h0

lemma shifted_map_zmod (n : ℕ) (hp : (n + 2).Prime) :
    (((OeisA217785.polyS n).comp (X + 1)).map (Int.castRingHom (ZMod (n + 2)))) = - X ^ n := by
  set p := n + 2
  have : Fact p.Prime := ⟨hp⟩
  set φ := Int.castRingHom (ZMod p)
  set g := (OeisA217785.polyS n).comp (X + 1)
  have hcomp := congr_arg (fun f : ℤ[X] => f.comp (X + 1)) (mul_sq_sub_one_polyS n)
  simp only [mul_comp, pow_comp, sub_comp, add_comp, X_comp, one_comp, C_comp,
    add_sub_cancel_right] at hcomp
  have hmap := congr_arg (Polynomial.map φ) hcomp
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one, map_C] at hmap
  have hφp : φ (n + 2 : ℤ) = 0 := by
    change ((p : ℤ) : ZMod p) = 0
    exact_mod_cast ZMod.natCast_self p
  have hφn1 : φ (n + 1 : ℤ) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    have hsum : (n + 1 : ℤ) + 1 = (n + 2 : ℤ) := by ring
    rw [← map_one φ, ← map_add φ, hsum, hφp]
  change X ^ 2 * g.map φ = _ at hmap
  rw [hφp, hφn1, show n + 2 = p from rfl, X_add_one_pow_prime p hp] at hmap
  simp only [map_neg, map_one, map_zero, zero_mul, sub_zero] at hmap
  have hrhs : (-1 : (ZMod p)[X]) * (X ^ p + 1) + 1 = X ^ 2 * (- X ^ n) := by
    have hp_eq : X ^ p = (X : (ZMod p)[X]) ^ 2 * X ^ n := by
      simp only [p]
      ring
    rw [hp_eq]
    ring
  rw [hrhs] at hmap
  exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) hmap

lemma coeff_zero_eq_zero_of_mul_eq_neg_X_pow {F : Type*} [Field F] {n : ℕ} {P Q : F[X]}
    (hPQ : P * Q = - X ^ n) (hP : 1 ≤ P.natDegree) (_hQ : 1 ≤ Q.natDegree) :
    P.coeff 0 = 0 := by
  by_contra hP0
  have hPQ_ne : P * Q ≠ 0 := by
    rw [hPQ]
    exact neg_ne_zero.mpr (pow_ne_zero n X_ne_zero)
  have hP_ne : P ≠ 0 := left_ne_zero_of_mul hPQ_ne
  have hQ_ne : Q ≠ 0 := right_ne_zero_of_mul hPQ_ne
  have hdeg : P.natDegree + Q.natDegree = n := by
    rw [← natDegree_mul hP_ne hQ_ne, hPQ, natDegree_neg, natDegree_X_pow]
  have hQ_coeff : ∀ k < n, Q.coeff k = 0 := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hck := congr_arg (fun f => coeff f k) hPQ
      rw [coeff_neg, coeff_X_pow, if_neg hk.ne, neg_zero, coeff_mul,
        Finset.sum_eq_single (0, k)] at hck
      · exact (mul_eq_zero.mp hck).resolve_left hP0
      · rintro ⟨i, j⟩ hij hne
        simp at hij
        simp only [ne_eq, Prod.mk.injEq] at hne
        have hj_lt : j < k := by omega
        rw [ih j hj_lt (lt_trans hj_lt hk), mul_zero]
      · intro hnot
        simp at hnot
  apply hQ_ne
  ext k
  rw [coeff_zero]
  by_cases hk : k < n
  · exact hQ_coeff k hk
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end A217785Step

theorem prove_A217785_H1 :
    ∀ n : ℕ, 1 ≤ n → (n + 2).Prime →
      Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  intro n hn hp
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (A217785Step.isPrimitive_polyS n)).mp
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have hs0 : OeisA217785.polyS n ≠ 0 := (A217785Step.isPrimitive_polyS n).ne_zero
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
    have hd := congr_arg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hs0 hq0, A217785Step.natDegree_polyS,
      Polynomial.natDegree_one] at hd
    omega
  · intro A B hab
    by_cases hA0 : A.natDegree = 0
    · left
      have hAC := A217785Step.eq_C_of_natDegree_zero hA0
      rw [hAC] at hab ⊢
      exact (A217785Step.isPrimitive_polyS n (A.coeff 0) ⟨B, hab⟩).map Polynomial.C
    by_cases hB0 : B.natDegree = 0
    · right
      have hBC := A217785Step.eq_C_of_natDegree_zero hB0
      rw [hBC, mul_comm] at hab
      rw [hBC]
      exact (A217785Step.isPrimitive_polyS n (B.coeff 0) ⟨A, hab⟩).map Polynomial.C
    exfalso
    have hs0 : OeisA217785.polyS n ≠ 0 := (A217785Step.isPrimitive_polyS n).ne_zero
    have hAB0 : A * B ≠ 0 := hab ▸ hs0
    have hA_ne : A ≠ 0 := left_ne_zero_of_mul hAB0
    have hB_ne : B ≠ 0 := right_ne_zero_of_mul hAB0
    have hdegAB : A.natDegree + B.natDegree = n := by
      rw [← Polynomial.natDegree_mul hA_ne hB_ne, ← hab, A217785Step.natDegree_polyS]
    set X1 : Polynomial ℤ := Polynomial.X + 1
    have hX1_deg : X1.natDegree = 1 := by
      simpa [X1] using (Polynomial.natDegree_X_add_C (1 : ℤ))
    set A' := A.comp X1
    set B' := B.comp X1
    set g := (OeisA217785.polyS n).comp X1
    have hg_eq : g = A' * B' := by
      simp only [g, A', B', hab, Polynomial.mul_comp]
    have hA'_deg : A'.natDegree = A.natDegree := by
      rw [Polynomial.natDegree_comp, hX1_deg, mul_one]
    have hB'_deg : B'.natDegree = B.natDegree := by
      rw [Polynomial.natDegree_comp, hX1_deg, mul_one]
    set p := n + 2
    have : Fact p.Prime := ⟨hp⟩
    set φ := Int.castRingHom (ZMod p)
    set P := A'.map φ
    set Q := B'.map φ
    have hPQ : P * Q = - Polynomial.X ^ n := by
      calc P * Q = (A' * B').map φ := (Polynomial.map_mul φ).symm
        _ = g.map φ := by rw [← hg_eq]
        _ = - Polynomial.X ^ n := A217785Step.shifted_map_zmod n hp
    have hPQ_ne : P * Q ≠ 0 := by
      rw [hPQ]
      exact neg_ne_zero.mpr (pow_ne_zero n Polynomial.X_ne_zero)
    have hdegPQ : P.natDegree + Q.natDegree = n := by
      rw [← Polynomial.natDegree_mul (left_ne_zero_of_mul hPQ_ne) (right_ne_zero_of_mul hPQ_ne),
        hPQ, Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
    have hPle : P.natDegree ≤ A.natDegree := hA'_deg ▸ Polynomial.natDegree_map_le
    have hQle : Q.natDegree ≤ B.natDegree := hB'_deg ▸ Polynomial.natDegree_map_le
    have hP1 : 1 ≤ P.natDegree := by omega
    have hQ1 : 1 ≤ Q.natDegree := by omega
    have hP0 : P.coeff 0 = 0 :=
      A217785Step.coeff_zero_eq_zero_of_mul_eq_neg_X_pow hPQ hP1 hQ1
    have hQ0 : Q.coeff 0 = 0 :=
      A217785Step.coeff_zero_eq_zero_of_mul_eq_neg_X_pow (mul_comm P Q ▸ hPQ) hQ1 hP1
    rw [Polynomial.coeff_map] at hP0 hQ0
    have hpA : (p : ℤ) ∣ A'.coeff 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hP0
    have hpB : (p : ℤ) ∣ B'.coeff 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hQ0
    have hp2_g : (p : ℤ) * (p : ℤ) ∣ g.coeff 0 := by
      rw [hg_eq, Polynomial.mul_coeff_zero]
      exact mul_dvd_mul hpA hpB
    have hp2_2g : (p : ℤ) * (p : ℤ) ∣ 2 * g.coeff 0 := dvd_mul_of_dvd_right hp2_g 2
    rw [A217785Step.two_mul_shifted_coeff_zero n] at hp2_2g
    obtain ⟨c, hc⟩ := hp2_2g
    have hp_ne : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hc' : (p : ℤ) * (n + 1 : ℤ) = (p : ℤ) * ((p : ℤ) * c) := by
      have : (n + 2 : ℤ) = (p : ℤ) := by simp [p]
      linear_combination hc - (n + 1 : ℤ) * this
    have hdvd_z : (p : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
      refine ⟨c, ?_⟩
      have := mul_left_cancel₀ hp_ne hc'
      simpa using this
    have hdvd_nat : p ∣ n + 1 := Int.ofNat_dvd.mp hdvd_z
    have hle : p ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd_nat
    omega


theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 :=
  prove_A217785_H1
