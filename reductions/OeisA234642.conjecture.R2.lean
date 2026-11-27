import FormalConjectures.OEIS.«234642»

/-! For distinct primes at least five, the product is its totient plus their
sum minus one, and that remainder is smaller than half the totient.
Consequently the product realizes both an odd remainder and, after doubling,
twice that remainder. Every further doubling scales the remainder exactly.

The two remaining prime-sum questions distinguish an even number with composite
half, where a diagonal partition is impossible, from one with prime half, where
a partition other than the diagonal is needed. A sieve checked both
hypotheses for all 8 ≤ t ≤ 1,000,000, finding p ≤ 601 in every case.
This finite numerical check is independent of the proof below.

The argument for repeated doubling is adapted from the first reduction
of this problem, open-math-agents PR 623. -/

namespace OMA.R_OeisA234642_conjecture_R2

open OeisA234642

/-- Goldbach with summands at least five, when the half is composite. -/
def H1 : Prop := ∀ t : ℕ, 8 ≤ t → ¬ t.Prime →
  ∃ p q : ℕ, 5 ≤ p ∧ p ≤ q ∧ p.Prime ∧ q.Prime ∧ p + q = 2*t

/-- A non-diagonal Goldbach partition of twice an odd prime, avoiding three. -/
def H2 : Prop := ∀ t : ℕ, 11 ≤ t → t.Prime →
  ∃ p : ℕ, 5 ≤ p ∧ p < t ∧ p.Prime ∧ (2*t-p).Prime

theorem product_witness {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h5 : 5 ≤ p) (hlt : p < q) (hs : p+q=m+1) :
    Odd (p*q) ∧ 2 < p*q ∧ ModTotientEq m (p*q) ∧
      (p*q) % ((p*q).totient/2) = m := by
  have hop := hp.odd_of_ne_two (by omega)
  have hoq := hq.odd_of_ne_two (by omega)
  have h7 : 7 ≤ q := by obtain ⟨a, ha⟩ := hoq; omega
  have ht := Nat.totient_mul (hp.coprime_iff_not_dvd.mpr
    (fun h => (Nat.dvd_prime hq).mp h |>.elim hp.ne_one (Nat.ne_of_lt hlt)))
  rw [Nat.totient_prime hp, Nat.totient_prime hq] at ht
  have hp1 : p-1+1=p := by omega
  have hq1 : q-1+1=q := by omega
  have heq : p*q = (p*q).totient + m := by rw [ht]; nlinarith [congrArg₂ Nat.mul hp1 hq1]
  have hbound : 2*m < (p*q).totient := by
    rw [ht]
    nlinarith [Nat.mul_le_mul (show 2 ≤ p-3 by omega) (show 4 ≤ q-3 by omega),
      congrArg₂ Nat.mul (show p-3+2=p-1 by omega) (show q-3+2=q-1 by omega)]
  have hlarge : 2 < p*q := by nlinarith [Nat.mul_le_mul h5 h7]
  have hhalf := (Nat.totient_even hlarge).two_dvd
  refine ⟨hop.mul hoq, hlarge, ⟨by omega, ?_⟩, ?_⟩
  · nth_rw 1 [heq]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · have hrepr : p*q = m + 2*((p*q).totient/2) := by omega
    nth_rw 1 [hrepr]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 8000 in
private theorem odd_witness (hc : H1) (hp : H2) {m : ℕ} (hm : Odd m) :
    ∃ u : ℕ, Odd u ∧ 2 < u ∧ ModTotientEq m u ∧ u % (u.totient/2) = m := by
  obtain ⟨k, rfl⟩ := hm
  by_cases hk : k < 7
  · interval_cases k
    · exact ⟨5, by decide⟩
    · exact ⟨195, by decide⟩
    · exact ⟨25, by decide⟩
    · exact ⟨49, by decide⟩
    · exact ⟨105, by decide⟩
    · exact ⟨35, by decide⟩
    · exact ⟨169, by decide⟩
  have ht : 8 ≤ k+1 := by omega
  by_cases h : (k+1).Prime
  · have h11 : 11 ≤ k+1 := by
      by_contra! hsmall
      have hk9 : k ≤ 9 := by omega
      interval_cases k <;> revert h <;> decide
    obtain ⟨p,h5,plt,pp,qp⟩ := hp (k+1) h11 h
    exact ⟨_, product_witness pp qp h5 (by omega) (by omega)⟩
  · obtain ⟨p,q,h5,hpq,pp,qp,hs⟩ := hc (k+1) ht h
    have hlt : p < q := by
      by_contra! hn
      have : p = k+1 := by omega
      exact h (this ▸ pp)
    exact ⟨_, product_witness pp qp h5 hlt (by omega)⟩

private theorem even_witness (hc : H1) (hp : H2) (m : ℕ) (hm : 0 < m) :
    ∃ u : ℕ, Even u ∧ ModTotientEq (2*m) u := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨k, rfl⟩ := he
      obtain ⟨u, hu, hpos, hrem⟩ := ih k (by omega) (by omega)
      refine ⟨2*u, even_two_mul _, ?_⟩
      unfold ModTotientEq
      rw [Nat.totient_two_mul_of_even hu, Nat.mul_mod_mul_left, hrem]
      constructor <;> omega
    · obtain ⟨u,hu,hlarge,hpos,hrem⟩ := odd_witness hc hp ho
      have he := (Nat.totient_even hlarge).two_dvd
      have heq : u.totient = 2 * (u.totient / 2) := by omega
      refine ⟨2*u, even_two_mul _, ?_⟩
      unfold ModTotientEq
      rw [Nat.totient_two_mul_of_odd hu]
      refine ⟨hpos.1, ?_⟩
      conv_lhs => rw [heq, Nat.mul_mod_mul_left, hrem]

theorem main : H1 → H2 → type_of% @OeisA234642.conjecture := by
  intro hc hp n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_0]
  have h : ∃ u, ModTotientEq n u := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k,rfl⟩ := he
      obtain ⟨u,_,hu⟩ := even_witness hc hp k (by omega)
      exact ⟨u, by simpa [two_mul] using hu⟩
    · obtain ⟨u,_,_,hu,_⟩ := odd_witness hc hp ho
      exact ⟨u, hu⟩
  exact Nat.totient_pos.mp (Nat.sInf_mem h).1

end OMA.R_OeisA234642_conjecture_R2
