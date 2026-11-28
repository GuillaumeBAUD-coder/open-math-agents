import Mathlib

/-!
# Negative association of threshold events in sampling without replacement

Source: Lwins, https://mathoverflow.net/questions/311217 (CC BY-SA 4.0).
Credit: @connoranderson

A uniformly random permutation gives the order of the draws. The labels
are zero-based, so the first m labels are the successful draws. Increasing
functions are tested on disjoint subsets of the first k positions. The
inequality is the usual covariance inequality with the uniform denominators
cleared.
-/

namespace OMA.S_mo_311217

def successSet {n : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (σ i).val < m)

theorem main : ∀ (n k m : ℕ), k ≤ n → m ≤ n → ∀ A B : Finset (Fin n),
    (∀ i ∈ A ∪ B, i.val<k) → Disjoint A B →
    ∀ f g : Finset (Fin n) → ℝ, Monotone f → Monotone g →
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        (∑ σ : Equiv.Perm (Fin n), f (successSet m σ ∩ A) * g (successSet m σ ∩ B)) ≤
      (∑ σ : Equiv.Perm (Fin n), f (successSet m σ ∩ A)) *
      (∑ σ : Equiv.Perm (Fin n), g (successSet m σ ∩ B)) := by
  sorry

end OMA.S_mo_311217
