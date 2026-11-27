import OMAReductions.R_Erdos389_erdos_389_R1_H2_R1
import Mathlib

/-! Compare large-prime valuations by translating divisible entries between blocks. -/
open Finset
namespace ConsecutiveValuations

theorem divides (n k : ℕ) (hn : 1 ≤ n) (_hk : 1 ≤ k)
    (he : ∀ p : ℕ, p.Prime →
      padicValNat p (∏ i ∈ range k, (n+i)) ≤ padicValNat p (∏ i ∈ range k, (n+k+i))) :
    (∏ i ∈ range k, (n+i)) ∣ ∏ i ∈ range k, (n+k+i) := by
  have pos (b : ℕ) : (∏ i ∈ range k, (n+b+i)) ≠ 0 :=
    (prod_pos (s := range k) (f := fun i => n+b+i) (fun _ _ => by omega)).ne'
  apply (Nat.factorization_le_iff_dvd (by simpa using pos 0) (pos k)).mp
  intro p
  by_cases hp : p.Prime
  · simp only [Nat.factorization_def _ hp]
    exact he p hp
  · simp [Nat.factorization,hp]

end ConsecutiveValuations

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1_H2_R1.H2 := ConsecutiveValuations.divides