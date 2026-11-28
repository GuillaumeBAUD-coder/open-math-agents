import OMAReductions.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0, Copyright OpenAI. -/
namespace OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H2_R1
open OMA.S_wpc_vp_vs_vnp
open scoped Classical
def H1 : Prop := ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (X I J : Type) [Fintype X] [Fintype I] [Fintype J]
  (T : X → I → J → Type) [∀ x i j, Fintype (T x i j)] (Y : ℕ) (f : R →ₗ[k] k)
  (l : J → R) (c : X → I → J → ℕ) (g : ∀ x i j, T x i j → R),
  f 1 = 1 →
  (∀ x i j, ∑ z, g x i j z = (c x i j : R)) →
  (∑ x, ∏ i, ∑ j, l j * (c x i j : R)) = (Y : R) →
  (Y : k) = 1 + ∑ x, ∑ h : I → J, ∑ z : (i : I) → T x i (h i), f (∏ i, l (h i) * g x i (h i) (z i)) → False
def H2 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K],
  ∃ u : (n : ℕ) → (Fin n → Bool) → ℕ, let p : Family K (fun n => Fin n × Bool) := (fun n => ∑ x : Fin n → Bool, MvPolynomial.C (u n x : K) * ∏ i, MvPolynomial.X (i, x i))
  IsVNP p ∧ ∀ C : ℕ, 1 ≤ C → (∀ N, ∃ n ≥ N, ∃ s ≤ n^C, Computes s (p n)) →
  ∃ (k R : Type) (_ : Field k) (_ : CommRing R) (_ : Algebra k R) (X I J : Type) (_ : Fintype X) (_ : Fintype I) (_ : Fintype J)
  (T : X → I → J → Type) (_ : ∀ x i j, Fintype (T x i j)) (Y : ℕ) (f : R →ₗ[k] k)
  (l : J → R) (c : X → I → J → ℕ) (g : ∀ x i j, T x i j → R),
   f 1 = 1 ∧
   (∀ x i j, ∑ z, g x i j z = (c x i j : R)) ∧
   (∑ x, ∏ i, ∑ j, l j * (c x i j : R)) = (Y : R) ∧
   (Y : k) = 1 + ∑ x, ∑ h : I → J, ∑ z : (i : I) → T x i (h i), f (∏ i, l (h i) * g x i (h i) (z i))
theorem main : H1 → H2 → OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1.H2 := by
  intro rule build K _ _ _
  obtain ⟨u,mem,localCert⟩ := build K
  refine ⟨_,mem,?_⟩
  intro A d N
  by_contra! bad
  apply False.elim
  apply (fun h => ?_) (localCert (d+1) (by omega) (fun M => by
    let n := max M (max A N)
    obtain ⟨s,hs,hcomp⟩ := bad n (by dsimp [n]; omega)
    refine ⟨n,le_max_left ..,s,hs.trans ?_,hcomp⟩
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ ((le_max_left A N).trans (le_max_right M (max A N)))))
  obtain ⟨k,R,_,_,_,X,I,J,_,_,_,T,_,Y,f,l,c,g,unit,sim,primed,live⟩ := h
  exact rule k R X I J T Y f l c g unit sim primed live
end OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H2_R1
