import FormalConjectures.Arxiv.«2605.12342».Conjecture1

-- Problem: Fernandes' conjecture on the 2-generation of even direct product permutation groups — rank 4 3
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2605.12342/Conjecture1.lean:137 (declaration Arxiv.«2605.12342».conjecture_1.variants.rank_4_3)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof idea. The map S4 → S3 given by the action on the three pair partitions of {0,1,2,3}
is a sign preserving surjective homomorphism, so Γ(4,3) maps onto Γ(3,3) inside S3 × S3.
Any two elements of S3 × S3 with equal signs on each element lie in one of 13 proper
subgroups (even first coordinate, a point stabiliser in one coordinate, or a twisted
diagonal), checked by decide. The pullback of that subgroup contains both generators but
misses an explicit element of Γ(4,3), so the closure is not everything.
-/

namespace OMAQ

open Equiv Equiv.Perm Arxiv.«2605.12342»

/-- Index of the pair partition of `Fin 4` containing the pair `{a, b}`; partition `j` pairs
`0` with `j + 1`. -/
def pidx (a b : Fin 4) : Fin 3 :=
  if a = 0 then ⟨(b.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  else if b = 0 then ⟨(a.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  else ⟨(5 - a.val - b.val) % 3, Nat.mod_lt _ (by decide)⟩

def psiF (σ : Perm (Fin 4)) (j : Fin 3) : Fin 3 := pidx (σ 0) (σ j.succ)

set_option maxRecDepth 100000 in
theorem psiF_inv : ∀ σ : Perm (Fin 4), ∀ j, psiF σ⁻¹ (psiF σ j) = j := by decide

set_option maxRecDepth 100000 in
theorem psiF_inv' : ∀ σ : Perm (Fin 4), ∀ j, psiF σ (psiF σ⁻¹ j) = j := by decide

set_option maxRecDepth 100000 in
theorem psiF_one : ∀ j, psiF 1 j = j := by decide

set_option maxRecDepth 100000 in
theorem psiF_mul : ∀ σ τ : Perm (Fin 4), ∀ j, psiF (σ * τ) j = psiF σ (psiF τ j) := by
  decide

def psiP (σ : Perm (Fin 4)) : Perm (Fin 3) :=
  ⟨psiF σ, psiF σ⁻¹, psiF_inv σ, psiF_inv' σ⟩

def psi : Perm (Fin 4) →* Perm (Fin 3) where
  toFun := psiP
  map_one' := Equiv.ext psiF_one
  map_mul' σ τ := Equiv.ext (psiF_mul σ τ)

set_option maxRecDepth 100000 in
theorem psi_sign : ∀ σ : Perm (Fin 4), sign (psi σ) = sign σ := by decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
theorem cover : ∀ a1 b1 a2 b2 : Perm (Fin 3), sign a1 = sign b1 → sign a2 = sign b2 →
    (sign a1 = 1 ∧ sign a2 = 1) ∨ (∃ i : Fin 3, a1 i = i ∧ a2 i = i) ∨ (∃ i : Fin 3, b1 i = i ∧ b2 i = i) ∨
    (∃ p : Perm (Fin 3), p * a1 * p⁻¹ = b1 ∧ p * a2 * p⁻¹ = b2) := by
  decide

theorem rot_fix : ∀ i : Fin 3, finRotate 3 i ≠ i := by decide

theorem rot_conj : ∀ p : Perm (Fin 3), p * finRotate 3 * p⁻¹ ≠ 1 := by decide

theorem swap_sign : sign (swap (0 : Fin 3) 1) ≠ 1 := by decide

theorem mem_gamma {m n : ℕ} (x : Perm (Fin m) × Perm (Fin n)) :
    x ∈ gammaSubgroup m n ↔ sign x.1 = sign x.2 := by
  simp only [gammaSubgroup, signDiffHom, MonoidHom.mem_ker, MonoidHom.mul_apply,
    MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  rw [mul_inv_eq_one]

theorem notTop {G Q : Type*} [Group G] [Group Q] (Φ : G →* Q) (M : Subgroup Q)
    (h1 h2 w : G) (h1M : Φ h1 ∈ M) (h2M : Φ h2 ∈ M) (wM : Φ w ∉ M) :
    Subgroup.closure {h1, h2} ≠ ⊤ := by
  intro htop
  have hle : Subgroup.closure {h1, h2} ≤ M.comap Φ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1M
    · exact h2M
  exact wM (hle (htop ▸ Subgroup.mem_top w))

theorem key {m n : ℕ} (f : Perm (Fin m) →* Perm (Fin 3)) (g : Perm (Fin n) →* Perm (Fin 3))
    (hf : ∀ σ, sign (f σ) = sign σ) (hg : ∀ σ, sign (g σ) = sign σ)
    (w1 w2 w3 : gammaSubgroup m n)
    (hw1 : f w1.1.1 = finRotate 3 ∧ g w1.1.2 = 1)
    (hw2 : f w2.1.1 = 1 ∧ g w2.1.2 = finRotate 3)
    (hw3 : f w3.1.1 = swap 0 1 ∧ g w3.1.2 = swap 0 1) :
    ∀ h₁ h₂ : gammaSubgroup m n, Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  intro h1 h2
  let Φ : gammaSubgroup m n →* Perm (Fin 3) × Perm (Fin 3) :=
    (MonoidHom.prodMap f g).comp (gammaSubgroup m n).subtype
  have hs : ∀ x : gammaSubgroup m n, sign (f x.1.1) = sign (g x.1.2) := by
    intro x; rw [hf, hg]; exact (mem_gamma _).1 x.2
  rcases cover (f h1.1.1) (g h1.1.2) (f h2.1.1) (g h2.1.2) (hs h1) (hs h2) with
    ⟨e1, e2⟩ | ⟨i, e1, e2⟩ | ⟨i, e1, e2⟩ | ⟨p, e1, e2⟩
  · refine notTop Φ (sign.comp (MonoidHom.fst _ _)).ker h1 h2 w3 ?_ ?_ ?_
    · exact MonoidHom.mem_ker.2 e1
    · exact MonoidHom.mem_ker.2 e2
    · intro h
      have h' : sign (f w3.1.1) = 1 := MonoidHom.mem_ker.1 h
      rw [hw3.1] at h'
      exact swap_sign h'
  · refine notTop Φ ((MulAction.stabilizer (Perm (Fin 3)) i).comap (MonoidHom.fst _ _))
      h1 h2 w1 ?_ ?_ ?_
    · exact e1
    · exact e2
    · intro h
      have h' : f w1.1.1 i = i := h
      rw [hw1.1] at h'
      exact rot_fix i h'
  · refine notTop Φ ((MulAction.stabilizer (Perm (Fin 3)) i).comap (MonoidHom.snd _ _))
      h1 h2 w2 ?_ ?_ ?_
    · exact e1
    · exact e2
    · intro h
      have h' : g w2.1.2 i = i := h
      rw [hw2.2] at h'
      exact rot_fix i h'
  · refine notTop Φ (((MulAut.conj p).toMonoidHom.comp (MonoidHom.fst _ _)).eqLocus
      (MonoidHom.snd _ _)) h1 h2 w1 ?_ ?_ ?_
    · exact e1
    · exact e2
    · intro h
      have h' : p * f w1.1.1 * p⁻¹ = g w1.1.2 := h
      rw [hw1.1, hw1.2] at h'
      exact rot_conj p h'

def c4 : Perm (Fin 4) := swap 1 2 * swap 2 3

end OMAQ

open Equiv Equiv.Perm OMAQ in
theorem OMA.solution : type_of% @Arxiv.«2605.12342».conjecture_1.variants.rank_4_3 := by
  refine key psi (MonoidHom.id _) psi_sign (fun _ => rfl)
    ⟨(c4, 1), (mem_gamma _).2 (by decide)⟩
    ⟨(1, finRotate 3), (mem_gamma _).2 (by decide)⟩
    ⟨(swap 1 2, swap 0 1), (mem_gamma _).2 (by decide)⟩ ?_ ?_ ?_
  · exact ⟨by decide, rfl⟩
  · exact ⟨map_one _, rfl⟩
  · exact ⟨by decide, rfl⟩
