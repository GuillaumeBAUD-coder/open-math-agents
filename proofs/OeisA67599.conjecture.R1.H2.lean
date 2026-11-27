import OMAReductions.R_OeisA67599_conjecture_R1
import Mathlib.Tactic

/-!
# Decimal encoding of `2401 * q = 7 ^ 4 * q` for prime `q > 7`
-/

private lemma primeFactorsList_2401_mul_prime (q : ℕ) (hq7 : 7 < q) (hq : q.Prime) :
    (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
  have h7 : Nat.Prime 7 := by decide
  have hperm : ([7, 7, 7, 7, q] : List ℕ).Perm (2401 * q).primeFactorsList := by
    refine Nat.primeFactorsList_unique ?_ ?_
    · simp only [List.prod_cons, List.prod_nil]
      ring
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h7
      · exact h7
      · exact h7
      · exact h7
      · exact hq
  refine (hperm.symm).eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
    (Nat.primeFactorsList_sorted (2401 * q)).pairwise ?_
  simp
  omega

theorem prove_OeisA67599_H2 :
    ∀ q : ℕ, 7 < q → q.Prime →
      OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1 := by
  intro q hq7 hq
  have hlt : ¬ (2401 * q < 2) := by omega
  have hne : (7 : ℕ) ≠ q := by omega
  have hne' : q ≠ 7 := by omega
  unfold OeisA67599.a
  rw [if_neg hlt, primeFactorsList_2401_mul_prime q hq7 hq]
  have hdedup : ([7, 7, 7, 7, q] : List ℕ).dedup = [7, q] := by
    have h7_mem : (7 : ℕ) ∈ ([7, q] : List ℕ) := by simp
    have h7_mem2 : (7 : ℕ) ∈ ([7, 7, q] : List ℕ) := by simp
    have h7_mem3 : (7 : ℕ) ∈ ([7, 7, 7, q] : List ℕ) := by simp
    rw [List.dedup_cons_of_mem h7_mem3, List.dedup_cons_of_mem h7_mem2,
      List.dedup_cons_of_mem h7_mem]
    exact List.Nodup.dedup (by simp [hne])
  have hc7 : ([7, 7, 7, 7, q] : List ℕ).count 7 = 4 := by
    simp [hne']
  have hcq : ([7, 7, 7, 7, q] : List ℕ).count q = 1 := by
    simp [hne]
  rw [hdedup]
  simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, hc7, hcq, List.foldl_cons, List.foldl_nil, OeisA67599.concatenateNats]
  have hd7 : (Nat.digits 10 7).length = 1 := by decide
  have hd4 : (Nat.digits 10 4).length = 1 := by decide
  have hd1 : (Nat.digits 10 1).length = 1 := by decide
  rw [hd7, hd4, hd1]
  ring

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 :=
  prove_OeisA67599_H2
