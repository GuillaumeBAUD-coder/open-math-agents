import FormalConjectures.Paper.IrvingLeatherStableMatchings

/-! Reduction of the Irving-Leather conjecture at powers of two.

Proved here, inside `main`: the cases k = 0 and k = 1, and the lower bound at k = 2
(an explicit profile of size 4 with ten stable matchings).

Left as hypotheses:
* H1, a known result: the Irving-Leather lower bound (used here only for k ≥ 3). Source: Irving and Leather,
  The complexity of counting stable marriages, SIAM J. Comput. 15 (1986); see also Thurber,
  Concerning the maximum number of stable matchings in the stable marriage problem,
  Discrete Math. 248 (2002), Section 2, and Thomas, A recurrence giving a lower bound for
  stable matchings (OEIS A005154), Proposition 1.
* H2, a known result: M(4) ≤ 10. Source: the exhaustive computer search of Eilers (1999),
  as reported by Thurber (2002).
* H3, open: the upper bound for k ≥ 3. The value M(8) is not known. -/

open StableMarriage IrvingLeather

namespace OMA.R_IrvingLeather_irving_leather_pow_two_R1

/-- Known (Irving and Leather 1986; Thurber 2002, Section 2). The Irving-Leather construction:
at size 2^k some profile has at least a_k stable matchings. This is the same statement as H2
of the reduction R1 of the growth-rate problem, so one proof serves both. -/
def H1 : Prop :=
  ∀ k : ℕ, irvingLeatherCount k ≤ maxStableMatchings (2 ^ k)

/-- Known (Eilers 1999, exhaustive computer search; reported in Thurber 2002). No profile of
size 4 has more than 10 stable matchings. -/
def H2 : Prop :=
  ∀ p : StableMarriage.Profile 4, StableMarriage.numStableMatchings p ≤ 10

/-- Open. Upper bound for sizes 8 and above: no profile of size 2^k has more than a_k stable
matchings. -/
def H3 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ p : StableMarriage.Profile (2 ^ k),
    StableMarriage.numStableMatchings p ≤ IrvingLeather.irvingLeatherCount k

/-- A family of distinct stable matchings bounds the count from below. -/
theorem le_num {n N : ℕ} (p : Profile n) (F : Fin N → Matching n)
    (hF : ∀ i, IsStable p (F i)) (hinj : Function.Injective F) :
    N ≤ numStableMatchings p := by
  classical
  unfold numStableMatchings
  have h := Fintype.card_le_of_injective
    (fun i : Fin N => (⟨F i, hF i⟩ : {μ : Matching n // IsStable p μ}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  rw [Fintype.card_fin] at h
  convert h

/-- There are at most n! stable matchings. -/
theorem num_le_factorial {n : ℕ} (p : Profile n) :
    numStableMatchings p ≤ n.factorial := by
  classical
  unfold numStableMatchings
  calc Fintype.card {μ : Matching n // IsStable p μ}
      ≤ Fintype.card (Matching n) := Fintype.card_subtype_le _
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

theorem lower_one : ∃ p : Profile 1, 1 ≤ numStableMatchings p := by
  refine ⟨default, le_num default (fun _ : Fin 1 => 1) ?_ ?_⟩
  · intro i m w h
    exact h.1 (Subsingleton.elim _ _)
  · intro i j _
    exact Subsingleton.elim _ _

theorem lower_two : ∃ p : Profile 2, 2 ≤ numStableMatchings p := by
  refine ⟨⟨![1, Equiv.swap 0 1], ![Equiv.swap 0 1, 1]⟩,
    le_num _ ![1, Equiv.swap 0 1] ?_ ?_⟩
  · intro i m w
    unfold IsBlockingPair
    revert i m w
    decide
  · decide

/-- The profile with `manRank m w = m xor w` and `womanRank w m = 3 - (m xor w)` has ten
stable matchings. -/
theorem lower_four : ∃ p : Profile 4, 10 ≤ numStableMatchings p := by
  refine ⟨⟨![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
        Equiv.swap 0 3 * Equiv.swap 1 2],
      ![Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.swap 0 2 * Equiv.swap 1 3,
        Equiv.swap 0 1 * Equiv.swap 2 3, 1]⟩,
    le_num _ ![1, Equiv.swap 2 3, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2,
      Equiv.swap 3 2 * Equiv.swap 1 3 * Equiv.swap 0 1,
      Equiv.swap 0 2 * Equiv.swap 1 3,
      Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3,
      Equiv.swap 1 3 * Equiv.swap 2 1 * Equiv.swap 0 2,
      Equiv.swap 0 3 * Equiv.swap 1 2] ?_ ?_⟩
  · intro i m w
    unfold IsBlockingPair
    revert i m w
    decide
  · decide

theorem le_max {n : ℕ} (p : Profile n) :
    numStableMatchings p ≤ maxStableMatchings n :=
  Finset.le_sup (f := fun p : Profile n => numStableMatchings p) (Finset.mem_univ p)

theorem main : H1 → H2 → H3 → type_of% @IrvingLeather.irving_leather_pow_two := by
  intro h1 h2 h3 k
  apply le_antisymm
  · refine Finset.sup_le fun p _ => ?_
    rcases k with _ | _ | _ | k
    · exact num_le_factorial p
    · exact num_le_factorial p
    · exact h2 p
    · exact h3 (k + 3) (by omega) p
  · rcases k with _ | _ | _ | k
    · obtain ⟨p, hp⟩ := lower_one
      exact hp.trans (le_max p)
    · obtain ⟨p, hp⟩ := lower_two
      exact hp.trans (le_max p)
    · obtain ⟨p, hp⟩ := lower_four
      exact hp.trans (le_max p)
    · exact h1 (k + 3)

end OMA.R_IrvingLeather_irving_leather_pow_two_R1
