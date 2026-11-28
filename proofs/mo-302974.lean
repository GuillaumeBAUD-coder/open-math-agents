import OMAStatements.S_mo_302974
import Mathlib

-- Problem mo-302974: for every prime p there is a commutative ring R such that the ring W(R) of p-typical Witt
-- vectors has a nonzero element killed by p.
-- Upstream: statements/mo-302974.lean (declaration OMA.S_mo_302974.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let R be the dual numbers over Z/p, that is (Z/p)[e] with e^2 = 0; it has characteristic p. Let x be
-- the Teichmueller lift of e, with coefficients (e, 0, 0, ...). It is nonzero because its first coefficient is
-- e. In characteristic p the coefficients of x * p are 0 and then the p-th powers of the coefficients of x,
-- that is (0, e^p, 0, 0, ...), and e^p = 0 because e^2 = 0. So p * x = 0.

theorem OMA.solution : type_of% @OMA.S_mo_302974.main := by
  intro p hp
  refine ⟨DualNumber (ZMod p), inferInstance, ?_⟩
  show ∃ x : WittVector p (DualNumber (ZMod p)), x ≠ 0 ∧ (p : WittVector p (DualNumber (ZMod p))) * x = 0
  have hchar : CharP (DualNumber (ZMod p)) p :=
    charP_of_injective_ringHom (f := TrivSqZeroExt.inlHom (ZMod p) (ZMod p)) TrivSqZeroExt.inl_injective p
  have heps : (DualNumber.eps : DualNumber (ZMod p)) ^ p = 0 :=
    pow_eq_zero_of_le hp.out.two_le (by rw [pow_two, DualNumber.eps_mul_eps])
  refine ⟨WittVector.teichmuller p (DualNumber.eps : DualNumber (ZMod p)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun w : WittVector p (DualNumber (ZMod p)) => w.coeff 0) h0
    simp only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] at h1
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp at h2
  · rw [mul_comm]
    apply WittVector.ext
    intro n
    cases n with
    | zero => rw [WittVector.mul_charP_coeff_zero, WittVector.zero_coeff]
    | succ i =>
      rw [WittVector.mul_charP_coeff_succ, WittVector.zero_coeff]
      cases i with
      | zero => rw [WittVector.teichmuller_coeff_zero, heps]
      | succ j =>
        rw [WittVector.teichmuller_coeff_pos p _ (j + 1) (Nat.succ_pos j), zero_pow hp.out.ne_zero]
