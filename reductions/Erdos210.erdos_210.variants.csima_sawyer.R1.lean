import FormalConjectures.ErdosProblems.«210»

/-!
# The Csima–Sawyer bound via attachments

Use a homogeneous normal `(x, y, 1)` for the projective dual of each point.
An attachment corresponds to a triangular cell: after choosing signs for
the three boundary normals, every other normal lies in their positive cone
or its negative. H1 is the local Kelly–Moser attachment bound (including
the two-pencil case). H2 is the four-attachment bound. H3 excludes adjacent
type (2, 0) lines for arrangements of at least eight lines.
See Jonathan Lenchner, IBM Research Report RC24181, Lemmas 1, 4, 5 and 10.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped BigOperators Classical

namespace OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1

private theorem incidence_sum {P Q : Type} (s : Finset P) (t : Finset Q) (I : P → Q → Prop) :
    (∑ p ∈ s, (t.filter (I p)).card) = ∑ q ∈ t, (s.filter (fun p => I p q)).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

def H1 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  s.card ≤ 2 * O.card ∨
    ∀ p ∈ s, 3 ≤ d p + A p ∨ (d p = 2 ∧ A p = 0)

def H2 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  ∀ L ∈ O, (s.filter (fun p => attached p L)).card ≤ 4

def H3 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ L ∈ O, ∀ p ∈ s, ∀ q ∈ s, p ∈ L → q ∈ L →
    d p = 2 → A p = 0 → d q = 2 → A q = 0 → p = q

set_option maxHeartbeats 900000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos210.erdos_210.variants.csima_sawyer := by
  classical
  intro hlocal hcapacity hseparate n hn
  obtain ⟨s, hs, hcol, hmin⟩ := Erdos210.f_attained (by omega : 3 ≤ n)
  have hsize : 8 ≤ s.card := hs.symm ▸ hn
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  have hd : (∑ p ∈ s, d p) = 2 * O.card := by
    unfold d
    rw [incidence_sum s O (fun p L => p ∈ L)]
    calc
      _ = ∑ _L ∈ O, (2 : ℕ) := sum_congr rfl (fun _L hL => (mem_ordinaryLines.1 hL).2)
      _ = _ := by simp [mul_comm]
  have ha : (∑ p ∈ s, A p) ≤ 4 * O.card := by
    calc
      _ = ∑ p ∈ s, ∑ L ∈ O, (if attached p L then 1 else 0 : ℕ) := by
        apply sum_congr rfl
        intro p _
        exact Finset.card_filter (attached p) O
      _ = ∑ L ∈ O, ∑ p ∈ s, (if attached p L then 1 else 0 : ℕ) := Finset.sum_comm
      _ = ∑ L ∈ O, (s.filter (fun p => attached p L)).card := by
        apply sum_congr rfl
        intro L _
        exact (Finset.card_filter (fun p => attached p L) s).symm
      _ ≤ ∑ _L ∈ O, (4 : ℕ) := sum_le_sum (hcapacity s hsize hcol)
      _ = _ := by simp [mul_comm]
  change O.card = Erdos210.f n at hmin
  rcases hlocal s hsize hcol with hbig | hprofile
  · change s.card ≤ 2 * O.card at hbig
    omega
  let bad := s.filter (fun p => d p = 2 ∧ A p = 0)
  have hbad (L : AffineSubspace ℝ ℝ²) (hL : L ∈ O) :
      (bad.filter (fun p => p ∈ L)).card ≤ 1 := by
    apply card_le_one.2
    intro p hp q hq
    obtain ⟨hp, hpL⟩ := mem_filter.1 hp
    obtain ⟨hq, hqL⟩ := mem_filter.1 hq
    obtain ⟨hps, hpd, hpa⟩ := mem_filter.1 hp
    obtain ⟨hqs, hqd, hqa⟩ := mem_filter.1 hq
    exact hseparate s hsize hcol L hL p hps q hqs hpL hqL hpd hpa hqd hqa
  have hcount_bad : 2 * bad.card ≤ O.card := by
    calc
      _ = ∑ p ∈ bad, d p := by
        rw [show (∑ p ∈ bad, d p) = ∑ _p ∈ bad, (2 : ℕ) from
          sum_congr rfl (fun _p hp => (mem_filter.1 hp).2.1)]
        simp [mul_comm]
      _ = ∑ L ∈ O, (bad.filter (fun p => p ∈ L)).card :=
        incidence_sum bad O (fun p L => p ∈ L)
      _ ≤ ∑ _L ∈ O, (1 : ℕ) := sum_le_sum hbad
      _ = _ := by simp
  have htotal : 3 * s.card ≤ (∑ p ∈ s, d p) + (∑ p ∈ s, A p) + bad.card := by
    calc
      _ = ∑ _p ∈ s, (3 : ℕ) := by simp [mul_comm]
      _ ≤ ∑ p ∈ s, (d p + A p + if d p = 2 ∧ A p = 0 then 1 else 0) := by
        apply sum_le_sum
        intro p hp
        rcases hprofile p hp with h | h
        · exact h.trans (Nat.le_add_right _ _)
        · change d p = 2 ∧ A p = 0 at h
          simp [h]
      _ = _ := by
        simp only [sum_add_distrib]
        rw [← Finset.card_filter]
  omega

end OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1
