import OMAReductions.R_oeis_a054767_R1
import Mathlib

/-! Touchard's congruence and the Bell period (p^p - 1)/(p - 1) modulo a prime p.

Let L be the linear functional on (ZMod p)[X] sending X^i to the Bell number B(i). The Bell
recurrence B(n + 1) = sum C(n, i) B(i) says L (X f) = L (f (X + 1)). Iterating along the falling
product X (X - 1) ... (X - j + 1) gives L ((X - 0) ... (X - j + 1) g) = L (g (X + j)); for j = p
the product is X^p - X and X + p = X, so L ((X^p - X) g) = L g, which is Touchard's congruence
B(n + p) = B(n) + B(n + 1) mod p. Hence L kills every multiple of X^p - X - 1. In the ring
obtained by adjoining a root x of X^p - X - 1 (characteristic p), Frobenius gives
x^(p^k) = x + k, so x^(1 + p + ... + p^(p-1)) = x (x + 1) ... (x + p - 1) = x^p - x = 1. So
X^p - X - 1 divides X^N - 1 with N = (p^p - 1)/(p - 1), and L (X^n (X^N - 1)) = 0 is
B(n + N) = B(n) mod p. -/

open Polynomial

namespace A054767

/-- The Bell recurrence in the form `B(n+1) = ∑ C(n,i) B(i)`. -/
lemma bell_succ_sym (n : ℕ) :
    (n + 1).bell = ∑ i ∈ Finset.range (n + 1), n.choose i * i.bell := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : n + 1 - 1 - i = n - i := by omega
  rw [h1, Nat.choose_symm hi, Nat.sub_sub_self hi]

variable (p : ℕ)

/-- The linear functional sending `X ^ i` to the Bell number `B(i)` modulo `p`. -/
noncomputable def L : (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  Polynomial.lsum (fun i => ((i.bell : ℕ) : ZMod p) • LinearMap.id)

lemma L_monomial (n : ℕ) (c : ZMod p) : L p (monomial n c) = c * (n.bell : ZMod p) := by
  simp [L, Polynomial.lsum_apply, mul_comm]

lemma L_X_pow (n : ℕ) : L p (X ^ n) = (n.bell : ZMod p) := by
  rw [← monomial_one_right_eq_X_pow, L_monomial, one_mul]

/-- The Bell recurrence as an umbral shift: `L (X * f) = L (f (X + 1))`. -/
lemma L_X_mul (f : (ZMod p)[X]) : L p (X * f) = L p (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_comp, map_add]
  | monomial n c =>
    rw [X_mul_monomial, L_monomial, monomial_comp, add_pow]
    simp only [one_pow, mul_one, Finset.mul_sum, map_sum]
    have key : ∀ m ∈ Finset.range (n + 1),
        L p (C c * (X ^ m * (n.choose m : (ZMod p)[X]))) =
          c * ((n.choose m * m.bell : ℕ) : ZMod p) := by
      intro m _
      have : C c * (X ^ m * (n.choose m : (ZMod p)[X])) =
          monomial m (c * (n.choose m : ZMod p)) := by
        rw [← C_mul_X_pow_eq_monomial, ← Polynomial.C_eq_natCast, map_mul]
        ring
      rw [this, L_monomial]
      push_cast
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Nat.cast_sum, ← bell_succ_sym]

/-- `L (∏_{i<j} (X - i) * g) = L (g (X + j))`. -/
lemma L_desc_mul (j : ℕ) (g : (ZMod p)[X]) :
    L p ((∏ i ∈ Finset.range j, (X - C (i : ZMod p))) * g) = L p (g.comp (X + C (j : ZMod p))) := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ']
    have hprod : (∏ i ∈ Finset.range j, (X - C ((i + 1 : ℕ) : ZMod p))) =
        (∏ i ∈ Finset.range j, (X - C (i : ZMod p))).comp (X - 1) := by
      rw [Polynomial.prod_comp]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sub_comp, X_comp, C_comp]
      push_cast
      rw [map_add, map_one]
      ring
    have e : (∏ i ∈ Finset.range j, (X - C ((i + 1 : ℕ) : ZMod p))) * (X - C ((0 : ℕ) : ZMod p)) * g
        = X * ((∏ i ∈ Finset.range j, (X - C ((i + 1 : ℕ) : ZMod p))) * g) := by
      simp only [Nat.cast_zero, map_zero, sub_zero]
      ring
    rw [e, L_X_mul, mul_comp, hprod, comp_assoc]
    have h2 : (X - 1 : (ZMod p)[X]).comp (X + 1) = X := by simp
    rw [h2, comp_X, ih, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, one_comp]
    push_cast
    rw [map_add, map_one]
    ring

variable [hp : Fact p.Prime]

lemma prod_X_sub_C_univ : (∏ a : ZMod p, (X - C a)) = (X ^ p - X : (ZMod p)[X]) := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [hcard] at hroots
  have hp1 : 1 < p := hp.out.one_lt
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hp1
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp1
  have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    (by rw [hroots, hdeg]; simp [hcard])
  rw [hroots] at this
  exact this

lemma prod_range_eq_univ {M : Type*} [CommMonoid M] (f : ZMod p → M) :
    ∏ i ∈ Finset.range p, f (i : ZMod p) = ∏ a : ZMod p, f a := by
  have hp0 : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.prod_nbij' (fun i => (i : ZMod p)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro a _; simpa using ZMod.val_lt a
  · intro i hi
    have hi' : i < p := by simpa using hi
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi']
  · intro a _; simp
  · intro i _; rfl

lemma desc_eq : (∏ i ∈ Finset.range p, (X - C (i : ZMod p))) = (X ^ p - X : (ZMod p)[X]) := by
  rw [prod_range_eq_univ p (fun a => X - C a), prod_X_sub_C_univ]

lemma asc_eq : (∏ i ∈ Finset.range p, (X + C (i : ZMod p))) = (X ^ p - X : (ZMod p)[X]) := by
  rw [prod_range_eq_univ p (fun a => X + C a), ← prod_X_sub_C_univ p]
  exact Fintype.prod_equiv (Equiv.neg _) _ _ (fun a => by simp [sub_eq_add_neg])

/-- Touchard's congruence in umbral form: `L ((X^p - X) g) = L g`. -/
lemma touchard (g : (ZMod p)[X]) : L p ((X ^ p - X) * g) = L p g := by
  rw [← desc_eq, L_desc_mul]
  simp

lemma touchard' (g : (ZMod p)[X]) : L p ((X ^ p - X - 1) * g) = 0 := by
  rw [sub_mul, map_sub, touchard, one_mul, sub_self]

/-- In characteristic `p`, `X^p - X - 1` divides `X^N - 1` for `N = 1 + p + ... + p^(p-1)`. -/
lemma dvd_X_pow_sub_one :
    (X ^ p - X - 1 : (ZMod p)[X]) ∣ X ^ (∑ k ∈ Finset.range p, p ^ k) - 1 := by
  set f : (ZMod p)[X] := X ^ p - X - 1 with hf
  have hp1 : 1 < p := hp.out.one_lt
  have hdeg : f.degree ≠ 0 := by
    have : f = X ^ p - (X + 1) := by rw [hf]; ring
    rw [this, degree_sub_eq_left_of_degree_lt]
    · rw [degree_X_pow]; exact_mod_cast hp.out.ne_zero
    · rw [degree_X_pow]
      calc (X + 1 : (ZMod p)[X]).degree ≤ 1 := by
            have := degree_add_le (X : (ZMod p)[X]) 1
            refine this.trans ?_
            simp
        _ < p := by exact_mod_cast hp1
  have : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdeg
  have : CharP (AdjoinRoot f) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot f)).injective p
  set x := AdjoinRoot.root f
  have hx : x ^ p = x + 1 := by
    have h := AdjoinRoot.eval₂_root f
    rw [hf] at h
    simp only [eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_one] at h
    linear_combination h
  have hpow : ∀ k : ℕ, x ^ p ^ k = x + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, add_pow_char, hx]
      have : ((k : AdjoinRoot f)) ^ p = k := by
        have h := congrArg (algebraMap (ZMod p) (AdjoinRoot f)) (ZMod.pow_card (k : ZMod p))
        rw [map_pow, map_natCast] at h
        exact h
      rw [this]
      push_cast
      ring
  have hprod : x ^ (∑ k ∈ Finset.range p, p ^ k) = x ^ p - x := by
    rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_congr rfl (fun k _ => hpow k)]
    have := congrArg (aeval x) (asc_eq p)
    simp only [map_prod, map_add, aeval_X, aeval_C, map_sub, map_pow] at this
    rw [← this]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, map_one]
  change x ^ _ - 1 = 0
  rw [hprod, hx]
  ring

theorem period (n : ℕ) :
    ((n + ∑ k ∈ Finset.range p, p ^ k).bell : ZMod p) = (n.bell : ZMod p) := by
  obtain ⟨g, hg⟩ := dvd_X_pow_sub_one p
  have h := touchard' p (X ^ n * g)
  have e : (X ^ p - X - 1) * (X ^ n * g) = X ^ n * (X ^ (∑ k ∈ Finset.range p, p ^ k) - 1) := by
    rw [hg]; ring
  rw [e, mul_sub, ← pow_add, mul_one, map_sub, L_X_pow, L_X_pow, sub_eq_zero] at h
  exact h

theorem solution (q : ℕ) (hq : q.Prime) : (q ^ q - 1) / (q - 1) ∈ OMA.S_oeis_a054767.positiveBellPeriods q := by
  have : Fact q.Prime := ⟨hq⟩
  rw [← Nat.geomSum_eq hq.two_le]
  refine ⟨?_, fun n => ?_⟩
  · exact lt_of_lt_of_le (by simp) (Finset.single_le_sum (fun i _ => Nat.zero_le (q ^ i))
      (Finset.mem_range.mpr hq.pos))
  · exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (period q n)

end A054767

theorem OMA.solution : OMA.R_oeis_a054767_R1.H1 := fun q hq => A054767.solution q hq
