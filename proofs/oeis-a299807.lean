import OMAStatements.S_oeis_a299807
import Mathlib

namespace A299807Proof

open Polynomial Finset

/-- The only rational relations among 1, ζ, ..., ζ^(p-1) have all coefficients equal. -/
theorem key (p : ℕ) [hp : Fact p.Prime] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (a : ℕ → ℚ)
    (h : ∑ i ∈ range p, (a i : ℂ) * ζ ^ i = 0) : ∃ c : ℚ, ∀ i < p, a i = c := by
  set f : ℚ[X] := ∑ i ∈ range p, C (a i) * X ^ i with hf
  have hf0 : aeval ζ f = 0 := by
    rw [hf, map_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hdvd : cyclotomic p ℚ ∣ f := by
    rw [cyclotomic_eq_minpoly_rat hζ hp.out.pos]
    exact minpoly.dvd ℚ ζ hf0
  obtain ⟨g, hg⟩ := hdvd
  have hcoef : ∀ i < p, f.coeff i = a i := by
    intro i hi
    rw [hf, finsetSum_coeff]
    simp [coeff_X_pow, hi]
  have hcyc : ∀ i < p, (cyclotomic p ℚ).coeff i = 1 := by
    intro i hi
    rw [cyclotomic_prime, finsetSum_coeff]
    simp [coeff_X_pow, hi]
  have hgc : ∃ c : ℚ, g = C c := by
    by_cases hg0 : g = 0
    · exact ⟨0, by simp [hg0]⟩
    · have h1 : f.natDegree ≤ p - 1 := by
        rw [hf]
        refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
        refine (natDegree_C_mul_X_pow_le _ _).trans ?_
        have := Finset.mem_range.mp hi
        omega
      have h2 : f.natDegree = (cyclotomic p ℚ).natDegree + g.natDegree := by
        rw [hg]; exact natDegree_mul (cyclotomic_ne_zero p ℚ) hg0
      rw [natDegree_cyclotomic, Nat.totient_prime hp.out] at h2
      exact ⟨g.coeff 0, eq_C_of_natDegree_eq_zero (by omega)⟩
  obtain ⟨c, rfl⟩ := hgc
  refine ⟨c, fun i hi => ?_⟩
  rw [← hcoef i hi, hg, coeff_mul_C, hcyc i hi, one_mul]

theorem sum_eq (p : ℕ) (ζ : ℂ) (m : Multiset (Fin p)) :
    (m.map (fun i : Fin p => ζ ^ (i : ℕ))).sum = ∑ i : Fin p, (m.count i : ℂ) * ζ ^ (i : ℕ) := by
  rw [Finset.sum_multiset_map_count]
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp
  · intro i _ hi
    have : m.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
    simp [this]

theorem inj (p k : ℕ) [hp : Fact p.Prime] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (fun m : Sym (Fin p) k =>
      ((m : Multiset (Fin p)).map (fun i : Fin p => ζ ^ (i : ℕ))).sum) := by
  intro m m' hmm
  simp only [sum_eq] at hmm
  set a : ℕ → ℚ := fun j => if hj : j < p then
    ((m : Multiset (Fin p)).count ⟨j, hj⟩ : ℚ) - ((m' : Multiset (Fin p)).count ⟨j, hj⟩ : ℚ)
    else 0 with ha
  have hval : ∀ i : Fin p, a i =
      ((m : Multiset (Fin p)).count i : ℚ) - ((m' : Multiset (Fin p)).count i : ℚ) := by
    intro i; simp [ha, i.2]
  have h0 : ∑ i ∈ range p, (a i : ℂ) * ζ ^ i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (a i : ℂ) * ζ ^ i)]
    simp only [hval]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hmm, sub_self]
  obtain ⟨c, hc⟩ := key p ζ hζ a h0
  have hsum : ∑ i ∈ range p, a i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range a]
    simp only [hval, Finset.sum_sub_distrib]
    rw [← Nat.cast_sum, ← Nat.cast_sum, Multiset.sum_count_eq_card (by simp),
      Multiset.sum_count_eq_card (by simp)]
    simp
  have hc0 : c = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => hc i (Finset.mem_range.mp hi))] at hsum
    simp at hsum
    rcases hsum with h | h
    · exact absurd h hp.out.ne_zero
    · exact h
  apply Sym.coe_injective
  ext i
  have := hc i i.2
  rw [hval, hc0, sub_eq_zero] at this
  exact_mod_cast this

theorem T_eq (p k : ℕ) (hp : p.Prime) :
    OMA.S_oeis_a299807.T p k = Nat.choose (k + p - 1) (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p := ⟨_, Complex.isPrimitiveRoot_exp p hp.ne_zero⟩
  have hset : {z : ℂ | ∃ s : Multiset ℂ, Multiset.card s = k ∧ (∀ x ∈ s, x ^ p = 1) ∧ s.sum = z}
      = Set.range (fun m : Sym (Fin p) k =>
        ((m : Multiset (Fin p)).map (fun i : Fin p => ζ ^ (i : ℕ))).sum) := by
    ext z
    constructor
    · rintro ⟨s, hs, hroot, rfl⟩
      have hex : ∀ x : ℂ, ∃ i : Fin p, x ^ p = 1 → ζ ^ (i : ℕ) = x := by
        intro x
        by_cases hx : x ^ p = 1
        · obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx
          exact ⟨⟨i, hi⟩, fun _ => hix⟩
        · exact ⟨⟨0, hp.pos⟩, fun h => absurd h hx⟩
      choose e he using hex
      refine ⟨⟨s.map e, by simpa using hs⟩, ?_⟩
      simp only [Sym.coe_mk, Multiset.map_map]
      congr 1
      conv_rhs => rw [← Multiset.map_id s]
      exact Multiset.map_congr rfl fun x hx => he x (hroot x hx)
    · rintro ⟨m, rfl⟩
      refine ⟨_, by simp, ?_, rfl⟩
      intro x hx
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  unfold OMA.S_oeis_a299807.T
  rw [hset, Set.ncard_range_of_injective (inj p k ζ hζ), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin]
  have h1 : 1 ≤ p := hp.pos
  rw [show k + p - 1 = p + k - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

end A299807Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a299807.main := by
  intro p hp
  refine ⟨fun k => A299807Proof.T_eq p k hp, ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hfun : (fun k => (OMA.S_oeis_a299807.T (d + 1) k : ℚ)) =
      fun n => ((Nat.choose (d + n) d : ℕ) : ℚ) := by
    funext k
    rw [A299807Proof.T_eq (d + 1) k hp]
    congr 2
    omega
  rw [hfun]
  exact PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℚ d
