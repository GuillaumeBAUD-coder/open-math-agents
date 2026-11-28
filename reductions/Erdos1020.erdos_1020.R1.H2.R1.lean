import OMAReductions.R_Erdos1020_erdos_1020_R1
import Mathlib

/-! The cases k = 2 and n = r * k of the matching bound.

For k = 2 an r-uniform family with no two disjoint edges is intersecting, so for 2r at most n
the Erdős–Ko–Rado theorem (Mathlib `Finset.erdos_ko_rado`) bounds it by C(n-1, r-1), which by
Pascal's rule is C(n, r) - C(n-1, r).

For n = r * k (perfect matchings) Kleitman's averaging argument applies: fix k disjoint blocks
of size r and average over all permutations of the ground set; each permutation sends at most
k - 1 blocks into the family, so k times the family size is at most (k - 1) C(rk, r), and
(k - 1) C(rk, r) = k C(rk - 1, r). In fact k f(n, r, k) is at most (k - 1) C(n, r) for every
n at least r * k.

What remains open is k at least 3 with n strictly above r * k, split into triple systems
(r = 3) and r at least 4.
-/

namespace OMA.R_Erdos1020_erdos_1020_R1_H2_R1

open Finset Erdos1020

def H1 : Prop :=
  ∀ n k : ℕ, 3 ≤ k → 3 * k < n →
    f n 3 k ≤ max ((3 * k - 1).choose 3) (n.choose 3 - (n - k + 1).choose 3)

def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ n k : ℕ, 3 ≤ k → r * k < n →
    f n r k ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r)

section Kleitman

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem map_mul (A : Finset α) (τ σ : Equiv.Perm α) :
    A.map (τ * σ).toEmbedding = (A.map σ.toEmbedding).map τ.toEmbedding := by
  rw [Finset.map_map]
  rfl

theorem perm_shift (A B : Finset α) (τ : Equiv.Perm α) :
    ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = (B.map τ.toEmbedding))).card = ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = B)).card := by
  symm
  refine card_bij' (fun σ _ => τ * σ) (fun σ _ => τ⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [map_mul, hσ]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [map_mul, hσ, ← map_mul, inv_mul_cancel]
    rw [show (1 : Equiv.Perm α).toEmbedding = Function.Embedding.refl α from rfl, map_refl]
  · intro σ _
    simp
  · intro σ _
    simp

theorem exists_perm (A B : Finset α) (h : A.card = B.card) :
    ∃ τ : Equiv.Perm α, A.map τ.toEmbedding = B := by
  have hc : Fintype.card {x // x ∈ A} = Fintype.card {x // x ∈ B} := by simpa using h
  let e : {x // x ∈ A} ≃ {x // x ∈ B} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  apply eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact Equiv.extendSubtype_mem e x hx
  · rw [card_map, h]

theorem perm_const (A B : Finset α) (h : A.card = B.card) : ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = B)).card = ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = A)).card := by
  obtain ⟨τ, hτ⟩ := exists_perm A B h
  rw [← hτ, perm_shift]

theorem choose_mul_perm (A : Finset α) (r : ℕ) (hA : A.card = r) :
    (Fintype.card α).choose r * ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = A)).card = (Fintype.card α).factorial := by
  rw [← Fintype.card_perm, ← Finset.card_univ (α := Equiv.Perm α)]
  rw [card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => A.map σ.toEmbedding)
    (s := univ) (t := (univ : Finset α).powersetCard r)]
  · have : ∀ B ∈ (univ : Finset α).powersetCard r,
        (((univ : Finset (Equiv.Perm α))).filter (fun σ => A.map σ.toEmbedding = B)).card = ((univ : Finset (Equiv.Perm α)).filter (fun σ => A.map σ.toEmbedding = A)).card := by
      intro B hB
      rw [← perm_const A B (by rw [hA, (mem_powersetCard.mp hB).2])]
    rw [sum_congr rfl this, sum_const, card_powersetCard, card_univ, smul_eq_mul]
  · intro σ _
    simp [mem_powersetCard, hA]

theorem kleitman_bound (r k : ℕ) (hr : 1 ≤ r) (A : Fin k → Finset α)
    (hAc : ∀ i, (A i).card = r) (hAd : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (F : Finset (Finset α)) (hF : ∀ e ∈ F, e.card = r) (hM : ¬ F.HasHypergraphMatching k) :
    k * F.card ≤ (k - 1) * (Fintype.card α).choose r := by
  set n := Fintype.card α
  -- per permutation at most k - 1 blocks land in F
  have hper : ∀ σ : Equiv.Perm α,
      (((univ : Finset (Fin k))).filter (fun i => (A i).map σ.toEmbedding ∈ F)).card ≤ k - 1 := by
    intro σ
    by_contra hcon
    have hall : {i ∈ (univ : Finset (Fin k)) | (A i).map σ.toEmbedding ∈ F} = univ := by
      apply eq_of_subset_of_card_le (filter_subset _ _)
      rw [card_univ, Fintype.card_fin]
      omega
    have hmem : ∀ i, (A i).map σ.toEmbedding ∈ F := by
      intro i
      have : i ∈ {i ∈ (univ : Finset (Fin k)) | (A i).map σ.toEmbedding ∈ F} := by
        rw [hall]; exact mem_univ i
      exact (mem_filter.mp this).2
    have hdisj : ∀ i j, i ≠ j →
        Disjoint ((A i).map σ.toEmbedding) ((A j).map σ.toEmbedding) := by
      intro i j hij
      rw [disjoint_map]
      exact hAd i j hij
    have hinj : Function.Injective (fun i => (A i).map σ.toEmbedding) := by
      intro i j hij
      by_contra hne
      have hd := hdisj i j hne
      simp only at hij
      rw [hij, disjoint_self] at hd
      have hc := hAc j
      rw [← card_map σ.toEmbedding, hd] at hc
      simp at hc
      omega
    apply hM
    refine ⟨univ.image (fun i => (A i).map σ.toEmbedding), ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨i, -, rfl⟩ := mem_image.mp he
      exact hmem i
    · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    · intro x hx y hy hxy
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hdisj i j (fun h => hxy (by rw [h]))
  -- the double count
  have hcount : ∀ i : Fin k,
      (((univ : Finset (Equiv.Perm α))).filter (fun σ => (A i).map σ.toEmbedding ∈ F)).card =
        F.card * ((univ : Finset (Equiv.Perm α)).filter (fun σ => (A i).map σ.toEmbedding = (A i))).card := by
    intro i
    rw [card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => (A i).map σ.toEmbedding)
      (t := F)]
    · rw [← smul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro B hB
      have hBc : B.card = (A i).card := by rw [hF B hB, hAc i]
      rw [← perm_const (A i) B hBc.symm]
      congr 1
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h ▸ hB, h⟩
    · intro σ hσ
      exact (mem_filter.mp hσ).2
  have hS1 : ∑ σ : Equiv.Perm α,
      (((univ : Finset (Fin k))).filter (fun i => (A i).map σ.toEmbedding ∈ F)).card ≤ n.factorial * (k - 1) := by
    calc _ ≤ ∑ _σ : Equiv.Perm α, (k - 1) := sum_le_sum (fun σ _ => hper σ)
      _ = n.factorial * (k - 1) := by
        rw [sum_const, card_univ, Fintype.card_perm, smul_eq_mul]
  have hS2 : ∑ σ : Equiv.Perm α,
      (((univ : Finset (Fin k))).filter (fun i => (A i).map σ.toEmbedding ∈ F)).card =
      ∑ i : Fin k, (((univ : Finset (Equiv.Perm α))).filter (fun σ => (A i).map σ.toEmbedding ∈ F)).card := by
    simp only [card_filter]
    exact sum_comm
  rw [hS2] at hS1
  simp only [hcount] at hS1
  have hkey : n.choose r * ∑ i : Fin k, F.card * ((univ : Finset (Equiv.Perm α)).filter (fun σ => (A i).map σ.toEmbedding = (A i))).card = k * F.card * n.factorial := by
    rw [mul_sum]
    have : ∀ i : Fin k, n.choose r * (F.card * ((univ : Finset (Equiv.Perm α)).filter (fun σ => (A i).map σ.toEmbedding = (A i))).card) = F.card * n.factorial := by
      intro i
      rw [mul_left_comm, choose_mul_perm (A i) r (hAc i)]
    rw [sum_congr rfl (fun i _ => this i), sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      mul_assoc]
  have h3 : k * F.card * n.factorial ≤ (k - 1) * n.choose r * n.factorial := by
    rw [← hkey]
    calc n.choose r * ∑ i : Fin k, F.card * ((univ : Finset (Equiv.Perm α)).filter (fun σ => (A i).map σ.toEmbedding = (A i))).card
        ≤ n.choose r * (n.factorial * (k - 1)) := Nat.mul_le_mul_left _ hS1
      _ = (k - 1) * n.choose r * n.factorial := by ring
  exact Nat.le_of_mul_le_mul_right h3 (Nat.factorial_pos n)

end Kleitman

section Proof

private theorem ekr_case (n r : ℕ) (hr : 1 ≤ r) (hn : 2 * r ≤ n) :
    f n r 2 ≤ (n - 1).choose (r - 1) := by
  classical
  unfold f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching 2)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching 2))] at hH
  obtain ⟨hsub, hno⟩ := hH
  have hsized : (H : Set (Finset (Fin n))).Sized r := by
    intro a ha
    exact (mem_powersetCard.mp (mem_powerset.mp hsub ha)).2
  have hint : (H : Set (Finset (Fin n))).Intersecting := by
    intro a ha b hb hdisj
    by_cases hab : a = b
    · subst hab
      have h0 : a = ∅ := disjoint_self.mp hdisj
      have hc := hsized ha
      rw [h0, card_empty] at hc
      omega
    · apply hno
      refine ⟨{a, b}, ?_, card_pair hab, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact ha
        · rw [mem_singleton.mp hx]; exact hb
      · rw [coe_pair]
        exact Set.pairwise_pair_of_symm.mpr (fun _ => hdisj)
  exact erdos_ko_rado hint hsized (by omega)

private theorem pascal_gap (n r : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
    (n - 1).choose (r - 1) = n.choose r - (n - 2 + 1).choose r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [show m + 1 - 2 + 1 = m by omega, Nat.choose_succ_succ]
  simp


private theorem f_le_of_forall (n r k B : ℕ)
    (h : ∀ H : Finset (Finset (Fin n)), H ⊆ (univ : Finset (Fin n)).powersetCard r →
      ¬ H.HasHypergraphMatching k → H.card ≤ B) : f n r k ≤ B := by
  classical
  unfold f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))] at hH
  exact h H (mem_powerset.mp hH.1) hH.2

private theorem blocks_exist (n r k : ℕ) (h : r * k ≤ n) :
    ∃ A : Fin k → Finset (Fin n), (∀ i, (A i).card = r) ∧
      ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
  have h' : k * r ≤ n := by rw [mul_comm]; exact h
  let g : Fin k × Fin r → Fin n := fun p => Fin.castLE h' (finProdFinEquiv p)
  have hg : Function.Injective g := by
    intro p q hpq
    have := Fin.castLE_injective h' hpq
    exact finProdFinEquiv.injective this
  refine ⟨fun i => (univ : Finset (Fin r)).map ⟨fun j => g (i, j), ?_⟩, ?_, ?_⟩
  · intro a b hab
    have := hg hab
    simpa using this
  · intro i
    simp
  · intro i j hij
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨a, -, rfl⟩ := mem_map.mp hx
    obtain ⟨b, -, hb⟩ := mem_map.mp hy
    have := hg hb
    simp only [Prod.mk.injEq] at this
    exact hij this.1.symm

/-- Kleitman bound for the extremal number, valid whenever r * k is at most n. -/
theorem kleitman_f (n r k : ℕ) (hr : 1 ≤ r) (h : r * k ≤ n) (H : Finset (Finset (Fin n)))
    (hH : H ⊆ (univ : Finset (Fin n)).powersetCard r) (hM : ¬ H.HasHypergraphMatching k) :
    k * H.card ≤ (k - 1) * n.choose r := by
  obtain ⟨A, hAc, hAd⟩ := blocks_exist n r k h
  have := kleitman_bound r k hr A hAc hAd H
    (fun e he => (mem_powersetCard.mp (hH he)).2) hM
  simpa using this

private theorem choose_identity (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    k * (r * k - 1).choose r = (k - 1) * (r * k).choose r := by
  obtain ⟨m, hm⟩ : ∃ m, r * k = m + 1 := ⟨r * k - 1, by
    have : 1 ≤ r * k := Nat.mul_pos hr hk
    omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hm, show m + 1 - 1 = m by omega, show j + 1 - 1 = j by omega]
  have h1 : (m + 1).choose (s + 1) = m.choose s + m.choose (s + 1) := Nat.choose_succ_succ m s
  have h2 : (m + 1) * m.choose s = (m + 1).choose (s + 1) * (s + 1) := Nat.add_one_mul_choose_eq m s
  have h3 : (j + 1) * m.choose s = (m + 1).choose (s + 1) := by
    have h2' : (s + 1) * (j + 1) * m.choose s = (m + 1).choose (s + 1) * (s + 1) := by
      rw [hm]; exact h2
    have h4 : (s + 1) * ((j + 1) * m.choose s) = (s + 1) * (m + 1).choose (s + 1) := by
      rw [← mul_assoc, h2', mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  rw [h1] at h3 ⊢
  nlinarith [h3]

/-- Kleitman 1968: the perfect matching case n = r * k. -/
theorem perfect_case (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    f (r * k) r k ≤ (r * k - 1).choose r := by
  apply f_le_of_forall
  intro H hH hM
  have h1 := kleitman_f (r * k) r k hr le_rfl H hH hM
  rw [← choose_identity r k hr hk] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by omega)

theorem main : H1 → H2 → OMA.R_Erdos1020_erdos_1020_R1.H2 := by
  intro h1 h2 r hr n k hk hn
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · refine le_trans ?_ (le_max_right _ _)
    rw [← pascal_gap n r (by omega) (by omega)]
    exact ekr_case n r (by omega) (by omega)
  · rcases (show n = r * k ∨ r * k < n by omega) with rfl | hlt
    · exact le_trans (perfect_case r k (by omega) (by omega)) (le_max_left _ _)
    · rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr4
      · exact h1 n k hk3 hlt
      · exact h2 r hr4 n k hk3 hlt

end Proof

end OMA.R_Erdos1020_erdos_1020_R1_H2_R1
