import OMAStatements.S_mo_514827
import Mathlib

/-
MathOverflow 514827: there is a homomorphism from the additive group of the reals to the
permutations of the natural numbers with countable kernel. In fact an injective one.

As rational vector spaces, the reals and the space of all sequences of rationals both have
dimension continuum (the second by the Erdos-Kaplansky theorem), so they are isomorphic. A
sequence v acts on pairs (n, q), n natural and q rational, by (n, q) -> (n, q + v n). This
action is faithful, and the set of such pairs is countable, so it can be moved to the naturals.
-/

namespace OMA.PMO514827

open Cardinal

lemma main' : ∃ f : Multiplicative ℝ →* Equiv.Perm ℕ,
    (f.ker : Set (Multiplicative ℝ)).Countable := by
  have hrank : Module.rank ℚ ℝ = Module.rank ℚ (ℕ → ℚ) := by
    rw [Real.rank_rat_real, rank_fun_infinite]
    simp
  obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hrank
  let σ : ℕ × ℚ ≃ ℕ := Denumerable.eqv (ℕ × ℚ)
  let F : Multiplicative ℝ →* Equiv.Perm ℕ :=
    { toFun := fun x => σ.symm.trans ((Equiv.prodShear (Equiv.refl ℕ) fun n =>
        Equiv.addRight (e (Multiplicative.toAdd x) n)).trans σ)
      map_one' := by
        ext k
        simp [Equiv.prodShear]
      map_mul' := by
        intro x y
        ext k
        simp [Equiv.prodShear]
        ring }
  refine ⟨F, ?_⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 : ∀ n : ℕ, e (Multiplicative.toAdd x) n = e (Multiplicative.toAdd y) n := by
      intro n
      have := congrArg (fun π : Equiv.Perm ℕ => (σ.symm (π (σ (n, 0)))).2) hxy
      simpa [F, Equiv.prodShear] using this
    exact Multiplicative.toAdd.injective (e.injective (funext h1))
  rw [(MonoidHom.ker_eq_bot_iff F).2 hinj]
  simp

end OMA.PMO514827

theorem OMA.solution : type_of% @OMA.S_mo_514827.main := OMA.PMO514827.main'
