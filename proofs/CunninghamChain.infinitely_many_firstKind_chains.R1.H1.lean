import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1

-- Infinitely many primes p start a Cunningham chain of exact length one (first kind): p is prime and 2p + 1
-- is composite. Original Lean proof of a classical consequence of Dirichlet's theorem (in Mathlib as
-- Nat.forall_exists_prime_gt_and_modEq): take primes p > 3 with p = 1 mod 3; then 3 divides 2p + 1.
-- The easy case of Jones's conjecture, not progress on exact length k >= 2.

namespace OMA.CunninghamFirst

theorem length_one : Set.Infinite {p : ℕ | CunninghamChain.IsFirstKindChainOfLength p 1} := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨p, hpn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max n 3) (q := 3) (a := 1) (by norm_num) (by decide)
  have hp3 : p % 3 = 1 := hmod
  have hgt : 3 < p := lt_of_le_of_lt (le_max_right n 3) hpn
  refine ⟨p, ⟨Nat.one_pos, ?_, ?_⟩, lt_of_le_of_lt (le_max_left n 3) hpn⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact hp
  · have hterm : CunninghamChain.firstKindTerm p 1 = 2 * p + 1 := rfl
    rw [hterm]
    intro hprime
    have hdvd : 3 ∣ 2 * p + 1 := by omega
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · omega
    · omega

end OMA.CunninghamFirst

theorem OMA.solution : OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H1 :=
  OMA.CunninghamFirst.length_one
