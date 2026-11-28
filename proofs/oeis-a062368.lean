import OMAStatements.S_oeis_a062368
import Mathlib

namespace OMA.S_oeis_a062368

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable def F : ArithmeticFunction ℕ :=
  ⟨fun m => if m = 0 then 0 else 4 ^ m.primeFactors.card, by simp⟩

lemma F_mult : F.IsMultiplicative := by
  refine ⟨by simp [F], ?_⟩
  intro m n h
  by_cases hm : m = 0
  · subst hm; simp [F]
  by_cases hn : n = 0
  · subst hn; simp [F]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [F, ArithmeticFunction.coe_mk, hm, hn, hmn, if_false]
  rw [Nat.Coprime.primeFactors_mul h, Finset.card_union_of_disjoint h.disjoint_primeFactors, pow_add]

noncomputable def G : ArithmeticFunction ℕ := ((F * ζ) * ζ) * ζ

lemma mulzeta (f : ArithmeticFunction ℕ) (x : ℕ) :
    (f * ζ) x = ∑ d ∈ x.divisors, f d := by
  have := ArithmeticFunction.coe_mul_zeta_apply (f := f) (x := x)
  simpa using this

lemma mulzeta_pp (f : ArithmeticFunction ℕ) (p k : ℕ) (hp : p.Prime) :
    (f * ζ) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) := by
  rw [mulzeta, Nat.sum_divisors_prime_pow hp]

lemma G_pp (p k : ℕ) (hp : p.Prime) : 6 * G (p ^ k) = (k + 1) * (k + 2) * (4 * k + 3) := by
  have h0 : ∀ i, F (p ^ i) = if i = 0 then 1 else 4 := by
    intro i
    have : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    simp only [F, ArithmeticFunction.coe_mk, this, if_false]
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · rw [Nat.primeFactors_prime_pow h.ne' hp]; simp [h.ne']
  have h1 : ∀ k, (F * ζ) (p ^ k) = 1 + 4 * k := by
    intro k
    rw [mulzeta_pp _ _ _ hp]
    induction k with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, ih, h0]; simp; ring
  have h2 : ∀ k, ((F * ζ) * ζ) (p ^ k) = (k + 1) * (2 * k + 1) := by
    intro k
    rw [mulzeta_pp _ _ _ hp]
    induction k with
    | zero => simp [h1]
    | succ n ih => rw [Finset.sum_range_succ, ih, h1]; ring
  have h3 : G (p ^ k) = ∑ i ∈ Finset.range (k + 1), (i + 1) * (2 * i + 1) := by
    rw [G, mulzeta_pp _ _ _ hp]
    exact Finset.sum_congr rfl (fun i _ => h2 i)
  rw [h3]
  clear h3
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma G_mult : G.IsMultiplicative :=
  (((F_mult.mul isMultiplicative_zeta.natCast).mul isMultiplicative_zeta.natCast).mul
    isMultiplicative_zeta.natCast)

lemma inv_eq (f : ArithmeticFunction ℕ) : invMobius (fun m => f m) = fun n => (f * ζ) n := by
  funext n
  rw [mulzeta]; rfl

lemma inv0 : invMobius (fun m : ℕ => 4 ^ m.primeFactors.card) = fun n => (F * ζ) n := by
  funext n
  rw [mulzeta]
  unfold invMobius
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp [F, this]

theorem solution_aux : type_of% @OMA.S_oeis_a062368.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [inv0, inv_eq (F * ζ), inv_eq ((F * ζ) * ζ)]
  show _ = G n
  rw [Nat.multiplicative_factorization G (fun x y h => G_mult.map_mul_of_coprime h) G_mult.map_one hn0]
  unfold a
  refine Finsupp.prod_congr (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hp)
  have := G_pp p (n.factorization p) hpp
  omega

end OMA.S_oeis_a062368

theorem OMA.solution : type_of% @OMA.S_oeis_a062368.main := OMA.S_oeis_a062368.solution_aux
