import FormalConjectures.Paper.ManickamMiklosSinghiConjecture
import Mathlib.Tactic

/-! # Permutation averaging for the Manickam–Miklós–Singhi bound

We isolate the nonnegative-edge estimate for the explicit cyclic double
intervals in Pokrovskiy's paper (arXiv:1308.2176, Theorem 1.5).
The averaging argument below allows an arbitrary indexed family of k-sets. -/

namespace OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1

open Finset ManickamMiklosSinghiConjecture

-- The independent quadratic-range theorem of Chowdhury, Sarkis and Shahriari.
def H1 : Prop := ∀ (n k : ℕ), 1 ≤ k → 8*k^2 ≤ n → ∀ x : Fin n → ℝ,
    ∑ v, x v = 0 → (n-1).choose (k-1) ≤ nonnegSubsetCount n k x

-- Only the remaining range needs the sparse cyclic estimate. It involves
-- n(k-1)^2 indexed double intervals and no arbitrary k-subsets.
def H2 : Prop := ∀ (n k : ℕ), 2 ≤ k → 10^46*k ≤ n → n < 8*k^2 → ∀ (hn : 2*k ≤ n)
    (x : Fin n → ℝ), ∑ v, x v = 0 →
    let E := fun a : Fin n × Fin (k-1) × Fin (k-1) =>
      univ.image (fun t : Fin k => a.1 + (⟨if t.val ≤ a.2.1.val then t.val else t.val+a.2.2.val+1,
        by have := t.isLt; have := a.2.2.isLt; split <;> omega⟩ : Fin n))
    k*(k-1)^2 ≤ (univ.filter (fun a => 0 ≤ ∑ v ∈ E a, x v)).card

-- Averaging over permutations transfers the edge frequency to all k-sets.
lemma average {n k : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (E : ι → Finset (Fin n)) (hE : ∀ a, (E a).card = k)
    (x : Fin n → ℝ) (d : ℕ)
    (lower : ∀ σ : Equiv.Perm (Fin n),
      d ≤ (univ.filter (fun a : ι => 0 ≤ ∑ v ∈ E a, x (σ v))).card) :
    d * n.choose k ≤ Fintype.card ι * nonnegSubsetCount n k x := by
  classical
  let U := (univ : Finset (Fin n)).powersetCard k
  let good (s : Finset (Fin n)) : ℕ := if 0 ≤ ∑ v ∈ s, x v then 1 else 0
  let mass (s : Finset (Fin n)) := ∑ σ : Equiv.Perm (Fin n), good (s.map σ.toEmbedding)
  let a₀ : ι := Classical.choice ‹Nonempty ι›
  let M := mass (E a₀)
  have same (s : Finset (Fin n)) (hs : s.card = k) : mass s = M := by
    obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq (E a₀) s ((hE a₀).trans hs.symm)
    rw [← hp]
    calc
      mass ((E a₀).map p.toEmbedding) =
          ∑ σ : Equiv.Perm (Fin n), good ((E a₀).map ((σ * p).toEmbedding)) := by
            apply sum_congr rfl
            intro σ _
            rw [map_map]
            rfl
      _ = M := Equiv.sum_comp (Equiv.mulRight p) (fun σ : Equiv.Perm (Fin n) => good ((E a₀).map σ.toEmbedding))
  have total (σ : Equiv.Perm (Fin n)) :
      ∑ s ∈ U, good (s.map σ.toEmbedding) = nonnegSubsetCount n k x := by
    have permutes : U.map (mapEmbedding σ.toEmbedding).toEmbedding = U := by
      dsimp [U]
      rw [← powersetCard_map]
      simp
    calc
      _ = ∑ s ∈ U.map (mapEmbedding σ.toEmbedding).toEmbedding, good s := (sum_map ..).symm
      _ = _ := by rw [permutes]; simp [U, good, nonnegSubsetCount]
  let N := Fintype.card (Equiv.Perm (Fin n))
  have complete : U.card * M = N * nonnegSubsetCount n k x := by
    calc
      U.card * M = ∑ s ∈ U, mass s := by
        rw [sum_congr rfl (fun s h => same s (mem_powersetCard.mp h).2)]
        exact (sum_const_nat (fun _ _ => rfl)).symm
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ s ∈ U, good (s.map σ.toEmbedding) := sum_comm
      _ = _ := by simp [total, N]
  have sparse : N*d ≤ Fintype.card ι * M := by
    calc
      N*d = ∑ _σ : Equiv.Perm (Fin n), d := by simp [N]
      _ ≤ ∑ σ : Equiv.Perm (Fin n), ∑ a : ι, good ((E a).map σ.toEmbedding) := by
        apply sum_le_sum
        intro σ _
        simpa [good, sum_map] using lower σ
      _ = ∑ a : ι, mass (E a) := sum_comm
      _ = _ := by simp [same _ (hE _)]
  have cU : U.card = n.choose k := by simp [U]
  have h := Nat.mul_le_mul_right U.card sparse
  rw [Nat.mul_assoc (Fintype.card ι), Nat.mul_comm M U.card, complete] at h
  apply Nat.le_of_mul_le_mul_left (c := N)
  · simpa only [cU, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · exact Fintype.card_pos

theorem main : H1 → H2 → type_of% @ManickamMiklosSinghiConjecture.manickam_miklos_singhi_conjecture.variants.pokrovskiy := by
  classical
  intro quadratic localBound
  refine ⟨10^46, ?_⟩
  intro n k hk hn x hx
  by_cases large : 8*k^2 ≤ n
  · exact quadratic n k hk large x hx
  have hnk : 2*k ≤ n := by omega
  by_cases one : k = 1
  · subst k
    exact manickam_miklos_singhi_conjecture.variants.one n (by omega) x hx
  have hk₂ : 2 ≤ k := by omega
  let : NeZero n := ⟨by omega⟩
  let : NeZero (k-1) := ⟨by omega⟩
  -- Offsets t < i stay put. All other offsets skip the j-vertex gap.
  let E := fun a : Fin n × Fin (k-1) × Fin (k-1) =>
      univ.image (fun t : Fin k => a.1 + (⟨if t.val ≤ a.2.1.val then t.val else t.val+a.2.2.val+1,
        by have := t.isLt; have := a.2.2.isLt; split <;> omega⟩ : Fin n))
  have cardE (a) : (E a).card = k := by
    dsimp only [E]
    rw [card_image_of_injective]
    · simp
    · intro s t h
      have ho := congrArg Fin.val (add_left_cancel h)
      apply Fin.ext
      change (if s.val ≤ a.2.1.val then s.val else s.val+a.2.2.val+1) =
          (if t.val ≤ a.2.1.val then t.val else t.val+a.2.2.val+1) at ho
      split at ho <;> split at ho <;> omega
  have lower (σ : Equiv.Perm (Fin n)) :=
    localBound n k hk₂ hn (Nat.lt_of_not_ge large) hnk (fun v => x (σ v)) ((Equiv.sum_comp σ x).trans hx)
  have avg := average E cardE x _ lower
  have size : Fintype.card (Fin n × Fin (k-1) × Fin (k-1)) = n*(k-1)^2 := by
    simp [pow_two]
  rw [size] at avg
  have bin : n * (n-1).choose (k-1) = n.choose k * k := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    exact Nat.add_one_mul_choose_eq n' k'
  have positive : 0 < n*(k-1)^2 := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left (c := n*(k-1)^2) _ positive
  calc
    n*(k-1)^2 * (n-1).choose (k-1) = (n * (n-1).choose (k-1)) * (k-1)^2 := by ring
    _ = k*(k-1)^2 * n.choose k := by rw [bin]; ring
    _ ≤ _ := avg

end OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1
