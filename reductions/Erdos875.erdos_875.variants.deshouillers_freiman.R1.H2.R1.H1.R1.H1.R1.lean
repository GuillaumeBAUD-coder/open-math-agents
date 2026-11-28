import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1
import Mathlib

/-!
# Reduction of the ordering step (`H1`) of `Erdos875.erdos_875.variants.deshouillers_freiman.R1.H2.R1.H1.R1`

Credit: @schulzee (agent: Claude Code, model claude-fable-5-2); the lemmas in the namespaces
`OMA.DF.Merge`, `OMA.DF.Count`, `OMA.DF.Heavy` were written by helper agents of the same team.

`H1` (first absorber): a large admissible set `A` has a subset `C` with `|A| / (4 * 10^6)`
elements such that the sums of `2 (|C| / 10^6)` distinct elements of `C` contain an arithmetic
progression with at least `|C|^2 / 10^8` terms (Propositions 2 and 4 of Deshouillers and
Freiman, Israel J. Math. 92 (1995)).

`H2` (small sum set): for some `s` between `|A| / 10` and `3 |A| / 4` there are fewer than `2 N`
sums of `s` distinct elements of `A` (their Proposition 1 and the bound of Straus).

`main` replaces section 5 of that paper, whose step (β) is not justified as written.
An absorber is a set `C` with a progression `x0 + j δ`, `j < J`, among the sums of `t` distinct
elements of `C`. `sep`: sums of different numbers of elements outside `C` do not differ by a
multiple of `δ` smaller than `J δ`. `ord_class`: a set in one class mod `δ` and of diameter at
most `J δ` has the ordering property. `count`, `few_classes`, `small_order`: the elements outside
`C` are in few classes, and two large classes differ by an element of small order. `merge`: two
classes give an absorber with the modulus `gcd`. `localize`, `heavy`: for a small modulus almost
all elements are in a short interval. `main_lemma`: strong induction on the modulus.
`ord_final`: the constants (`ρ = 10^21`, `|A| ≥ 10^210`).
-/

namespace OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1_H1_R1

open Finset

/-- The first absorber. -/
def H1 : Prop :=
  ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    Erdos875.IsAdmissible (A : Set ℕ) → 4 * N ≤ A.card * (A.card + 3) →
    ∃ C : Finset ℕ, C ⊆ A ∧ ∃ x0 δ : ℕ, C.card = A.card / (4 * 10 ^ 6) ∧ 1 ≤ δ ∧
      ∀ j : ℕ, 10 ^ 8 * j < C.card ^ 2 →
        ∃ T : Finset ℕ, T ⊆ C ∧ T.card = 2 * (C.card / 10 ^ 6) ∧ ∑ x ∈ T, x = x0 + j * δ

/-- A number of summands with a small sum set. -/
def H2 : Prop :=
  ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    Erdos875.IsAdmissible (A : Set ℕ) → 4 * N ≤ A.card * (A.card + 3) →
    ∃ s : ℕ, A.card ≤ 10 * s ∧ 4 * s ≤ 3 * A.card ∧
      ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card < 2 * N

lemma sum_mod {q β : ℕ} {T : Finset ℕ} (h : ∀ x ∈ T, x % q = β % q) :
    (∑ x ∈ T, x) % q = (T.card * β) % q := by
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, ← Nat.mul_mod_mod,
    Nat.mod_mod]
  rw [Nat.mul_mod_mod]

/-- L1 (separation). -/
lemma sep {A C : Finset ℕ} {t x0 δ J : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (ht : 1 ≤ t)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T ⊆ A ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    {X Y : Finset ℕ} (hX : X ⊆ A \ C) (hY : Y ⊆ A \ C) (hne : X.card ≠ Y.card)
    {i : ℕ} (hi : i < J) : ∑ x ∈ Y, x ≠ ∑ x ∈ X, x + i * δ := by
  intro heq
  obtain ⟨T, hTC, hTA, hTc, hTs⟩ := habs i hi
  obtain ⟨T', hT'C, hT'A, hT'c, hT's⟩ := habs 0 (by omega)
  have hd : ∀ {T Z : Finset ℕ}, T ⊆ C → Z ⊆ A \ C → Disjoint T Z := by
    intro T Z h1 h2
    exact Finset.disjoint_left.mpr fun z hz hz2 => (Finset.mem_sdiff.mp (h2 hz2)).2 (h1 hz)
  have hsubA : ∀ {Z : Finset ℕ}, Z ⊆ A \ C → Z ⊆ A := fun h z hz => (Finset.mem_sdiff.mp (h hz)).1
  refine hadm (T ∪ X) (T' ∪ Y) (Finset.union_subset hTA (hsubA hX))
    (Finset.union_subset hT'A (hsubA hY)) ?_ ?_ ?_ ?_
  · rw [Finset.card_union_of_disjoint (hd hTC hX)]; omega
  · rw [Finset.card_union_of_disjoint (hd hT'C hY)]; omega
  · rw [Finset.card_union_of_disjoint (hd hTC hX), Finset.card_union_of_disjoint (hd hT'C hY)]
    omega
  · rw [Finset.sum_union (hd hTC hX), Finset.sum_union (hd hT'C hY), hTs, hT's, heq]
    ring

/-- L2 (ordering in one class), with the diameter of `B` at most `J * δ`. -/
lemma ord_class {A C : Finset ℕ} {t x0 δ J : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hpos : ∀ x ∈ A, 1 ≤ x) (ht : 1 ≤ t) (hδ : 1 ≤ δ)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T ⊆ A ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    {B : Finset ℕ} (hB : B ⊆ A \ C) {c : ℕ} (hcl : ∀ y ∈ B, y % δ = c % δ)
    (hdiam : ∀ y ∈ B, ∀ y' ∈ B, y' ≤ y + J * δ)
    {κ x : ℕ} (hκ : 1 ≤ κ) (hx : 1 ≤ x) (hxc : δ ∣ x * c)
    {U V : Finset ℕ} (hU : U ⊆ B) (hV : V ⊆ B) (hUc : U.card = κ) (hVc : V.card = κ + x) :
    ∑ y ∈ U, y < ∑ y ∈ V, y := by
  have hBA : ∀ y ∈ B, 1 ≤ y := fun y hy => hpos y (Finset.mem_sdiff.mp (hB hy)).1
  have hresV : (∑ y ∈ V, y) % δ = (κ * c) % δ := by
    rw [sum_mod (fun y hy => hcl y (hV hy)), hVc, Nat.add_mul, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hxc, Nat.add_zero, Nat.mod_mod]
  have key : ∀ n, ∀ W : Finset ℕ, W ⊆ B → W.card = κ → (U \ W).card = n →
      ∑ y ∈ W, y < ∑ y ∈ V, y → ∑ y ∈ U, y < ∑ y ∈ V, y := by
    intro n
    induction n with
    | zero =>
      intro W hW hWc hn hlt
      have hUW : U ⊆ W := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hn)
      have : U = W := Finset.eq_of_subset_of_card_le hUW (by omega)
      rw [this]; exact hlt
    | succ n ih =>
      intro W hW hWc hn hlt
      obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (U \ W).card by omega)
      obtain ⟨hbU, hbW⟩ := Finset.mem_sdiff.mp hb
      have hWU : (W \ U).card = (U \ W).card := by
        have h1 := Finset.card_sdiff_add_card_inter W U
        have h2 := Finset.card_sdiff_add_card_inter U W
        rw [Finset.inter_comm] at h2
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (W \ U).card by omega)
      obtain ⟨haW, haU⟩ := Finset.mem_sdiff.mp ha
      have hbe : b ∉ W.erase a := fun h => hbW (Finset.mem_of_mem_erase h)
      have hW'sub : insert b (W.erase a) ⊆ B := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hU hbU
        · exact hW (Finset.mem_of_mem_erase hz)
      have hW'c : (insert b (W.erase a)).card = κ := by
        rw [Finset.card_insert_of_notMem hbe, Finset.card_erase_of_mem haW]; omega
      have hW's : ∑ y ∈ insert b (W.erase a), y + a = ∑ y ∈ W, y + b := by
        rw [Finset.sum_insert hbe]
        have := Finset.sum_erase_add W (fun y => y) haW
        omega
      have hn' : (U \ insert b (W.erase a)).card = n := by
        have : U \ insert b (W.erase a) = (U \ W).erase b := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or, not_and]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨h2, h1, fun h4 => ?_⟩
            exact h3 (fun h5 => haU (h5 ▸ h1)) h4
          · rintro ⟨h1, h2, h3⟩
            exact ⟨h2, h1, fun _ h5 => h3 h5⟩
        rw [this, Finset.card_erase_of_mem hb]; omega
      by_cases hlt' : ∑ y ∈ insert b (W.erase a), y < ∑ y ∈ V, y
      · exact ih _ hW'sub hW'c hn' hlt'
      · exfalso
        have hba := hdiam a (hW haW) b (hU hbU)
        have hres : (∑ y ∈ insert b (W.erase a), y) % δ = (κ * c) % δ := by
          rw [sum_mod (fun y hy => hcl y (hW'sub hy)), hW'c]
        have hdvd : δ ∣ ∑ y ∈ insert b (W.erase a), y - ∑ y ∈ V, y :=
          (Nat.modEq_iff_dvd' (by omega)).mp (hresV.trans hres.symm)
        obtain ⟨i, hi⟩ := hdvd
        have hiJ : i < J := by
          by_contra hcon
          have := Nat.mul_le_mul_left δ (Nat.le_of_not_lt hcon)
          rw [Nat.mul_comm δ J] at this
          omega
        refine sep hadm ht habs (X := V) (Y := insert b (W.erase a)) (hV.trans hB)
          (hW'sub.trans hB) (by omega) hiJ ?_
        rw [Nat.mul_comm i δ, ← hi]; omega
  obtain ⟨W, hWV, hWc⟩ := Finset.exists_subset_card_eq (show κ ≤ V.card by omega)
  have hlt : ∑ y ∈ W, y < ∑ y ∈ V, y := by
    have h1 := Finset.sum_sdiff (f := fun y => y) hWV
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (V \ W).card by
      have := Finset.card_sdiff_add_card_eq_card hWV; omega)
    have h2 : 1 ≤ ∑ y ∈ V \ W, y :=
      (hBA z (hV (Finset.mem_sdiff.mp hz).1)).trans
        (Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hz)
    omega
  exact key _ W (hWV.trans hV) hWc rfl hlt


lemma log_half {h δ : ℕ} (hh : 1 ≤ h) (h2 : 2 * h ≤ δ) : Nat.log 2 h + 1 ≤ Nat.log 2 δ := by
  rw [← Nat.log_mul_base (by norm_num) (by omega)]
  exact Nat.log_mono_right (by omega)

section L7

variable {A : Finset ℕ} {N s ρ η Jst nst Cmax tmax : ℕ}

/-- L7: the main lemma, by strong induction on the modulus. The statements of the work packages
(count, merge, heavy) are hypotheses here. -/
lemma main_lemma
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hAN : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) (hρ : 1 ≤ ρ) (hNJ : N ≤ ρ * Jst) (hJ8 : 8 ≤ Jst)
    (hη1 : 1 ≤ η) (hη : 8 * (16 * ρ * ρ + 1) * η ≤ Jst)
    (hn1 : (N / η + 1) * (2 * ρ) * (4 * (2 * ρ) * ρ * (16 * ρ * ρ + 1)) + 2 * ρ ≤ nst)
    (hts : tmax + 2 * ρ ≤ s) (hsk : s + 4 * ρ + Cmax ≤ A.card)
    (hkn : 2 * ρ * nst + Cmax < A.card)
    -- work package C
    (hFew : ∀ (C : Finset ℕ) (t x0 δ J : ℕ), C ⊆ A → 1 ≤ δ →
      (∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ) →
      N ≤ ρ * J → t + 1 ≤ s → s + 2 * ρ ≤ (A \ C).card →
      ((A \ C).image (· % δ)).card < 2 * ρ)
    (hSmall : ∀ (C : Finset ℕ) (t x0 δ J e₁ e₂ : ℕ), C ⊆ A → 1 ≤ δ →
      (∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ) →
      N ≤ ρ * J → t + 2 * ρ ≤ s → s + 4 * ρ ≤ (A \ C).card →
      e₁ ∈ A \ C → e₂ ∈ A \ C → e₁ % δ ≠ e₂ % δ →
      2 * ρ - 1 ≤ ((A \ C).filter (fun y => y % δ = e₁ % δ)).card →
      2 * ρ - 1 ≤ ((A \ C).filter (fun y => y % δ = e₂ % δ)).card →
      δ < 2 * ρ * Nat.gcd δ (max e₁ e₂ - min e₁ e₂))
    -- work package A
    (hMerge : ∀ (C : Finset ℕ) (t x0 δ J : ℕ) (E₁ E₂ : Finset ℕ) (e₁ e₂ h o w : ℕ), 1 ≤ δ →
      (∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ) →
      E₁ ⊆ A \ C → E₂ ⊆ A \ C → (∀ y ∈ E₁, y % δ = e₁ % δ) → (∀ y ∈ E₂, y % δ = e₂ % δ) →
      e₁ % δ ≠ e₂ % δ → h = Nat.gcd δ (max e₁ e₂ - min e₁ e₂) → δ = o * h →
      E₁.card = o - 1 → E₂.card = o - 1 →
      (∀ y ∈ E₁ ∪ E₂, ∀ y' ∈ E₁ ∪ E₂, y' ≤ y + w) → (o - 1) * w ≤ (J - 1) * δ →
      ∃ x0' : ℕ, ∀ j, j < ((J - 1) * δ - (o - 1) * w) / h →
        ∃ T : Finset ℕ, T ⊆ C ∪ E₁ ∪ E₂ ∧ T.card = t + (o - 1) ∧ ∑ x ∈ T, x = x0' + j * h)
    (hMsize : ∀ (δ J h o w : ℕ), δ = o * h → 1 ≤ h → 4 * ((o - 1) * w) ≤ J * δ → 8 ≤ J →
      2 ≤ o → J ≤ ((J - 1) * δ - (o - 1) * w) / h)
    -- work package D
    (hHeavy : ∀ (C : Finset ℕ) (t x0 δ J nc : ℕ), C ⊆ A → 1 ≤ t → 1 ≤ δ →
      (∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ) →
      N ≤ ρ * J → 8 * (16 * ρ * ρ + 1) * η ≤ J → ((A \ C).image (· % δ)).card ≤ nc →
      ∃ H : Finset ℕ, H ⊆ A \ C ∧ (∀ y ∈ H, ∀ y' ∈ H, 4 * y' ≤ 4 * y + J) ∧
        ((A \ C) \ H).card ≤ (N / η + 1) * nc * (δ * (16 * ρ * ρ + 1))) :
    ∀ δ : ℕ, ∀ (C : Finset ℕ) (t x0 J : ℕ), C ⊆ A → 1 ≤ t → 1 ≤ δ →
      (∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ) →
      Jst ≤ J → C.card + 2 * (2 * ρ) * Nat.log 2 δ ≤ Cmax → t + 2 * ρ * Nat.log 2 δ ≤ tmax →
      ∃ q : ℕ, 1 ≤ q ∧ ∃ B : Finset ℕ, B ⊆ A ∧
        (A \ B).card ≤ Cmax + 2 * ρ * nst +
          (N / η + 1) * (2 * ρ) * (4 * (2 * ρ) * ρ * (16 * ρ * ρ + 1)) ∧
        (∀ a ∈ B, ∀ b ∈ B, a % q = b % q) ∧
        ∀ κ : ℕ, 1 ≤ κ → ∀ U V : Finset ℕ, U ⊆ B → V ⊆ B → U.card = κ → V.card = κ + q →
          ∑ y ∈ U, y < ∑ y ∈ V, y := by
  intro δ
  induction δ using Nat.strong_induction_on with
  | _ δ ih =>
    intro C t x0 J hC ht hδ habs hJ hCm htm
    have hNJ' : N ≤ ρ * J := hNJ.trans (Nat.mul_le_mul_left ρ hJ)
    have hηJ : 8 * (16 * ρ * ρ + 1) * η ≤ J := hη.trans hJ
    have hDcard : (A \ C).card + C.card = A.card := Finset.card_sdiff_add_card_eq_card hC
    have habs' : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T ⊆ A ∧ T.card = t ∧
        ∑ x ∈ T, x = x0 + j * δ := fun j hj => by
      obtain ⟨T, h1, h2, h3⟩ := habs j hj
      exact ⟨T, h1, h1.trans hC, h2, h3⟩
    have hfew := hFew C t x0 δ J hC hδ habs hNJ' (by omega) (by omega)
    obtain ⟨H, hHD, hHdiam, hHc⟩ := hHeavy C t x0 δ J (2 * ρ) hC ht hδ habs hNJ' hηJ hfew.le
    -- bound for the non-heavy elements when δ is small
    have hK3 : δ ≤ 4 * (2 * ρ) * ρ → ((A \ C) \ H).card ≤
        (N / η + 1) * (2 * ρ) * (4 * (2 * ρ) * ρ * (16 * ρ * ρ + 1)) := fun hδΔ =>
      hHc.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hδΔ))
    by_cases hcase : ∃ e₁ ∈ A \ C, ∃ e₂ ∈ A \ C, e₁ % δ ≠ e₂ % δ ∧
        nst ≤ ((A \ C).filter (fun y => y % δ = e₁ % δ)).card ∧
        nst ≤ ((A \ C).filter (fun y => y % δ = e₂ % δ)).card
    · -- Case 1: two big classes: merge
      obtain ⟨e₁, he₁, e₂, he₂, hne, hb₁, hb₂⟩ := hcase
      obtain ⟨h, hh⟩ : ∃ h, h = Nat.gcd δ (max e₁ e₂ - min e₁ e₂) := ⟨_, rfl⟩
      have hhδ : h ∣ δ := hh ▸ Nat.gcd_dvd_left _ _
      have hh1 : 1 ≤ h := Nat.pos_of_dvd_of_pos hhδ hδ
      obtain ⟨o, ho⟩ : ∃ o, δ = o * h := by
        obtain ⟨o, ho⟩ := hhδ
        exact ⟨o, by rw [ho, Nat.mul_comm]⟩
      have hsm := hSmall C t x0 δ J e₁ e₂ hC hδ habs hNJ' (by omega) (by omega) he₁ he₂ hne
        (by omega) (by omega)
      rw [← hh] at hsm
      have hoK : o < 2 * ρ := by
        rw [ho] at hsm
        exact Nat.lt_of_mul_lt_mul_right hsm
      have ho2 : 2 ≤ o := by
        by_contra hcon
        have ho1 : o = 1 := by
          rcases Nat.lt_or_ge o 1 with h0 | h0
          · have : o = 0 := by omega
            rw [this] at ho; omega
          · omega
        rw [ho1, Nat.one_mul] at ho
        have hdvd : δ ∣ max e₁ e₂ - min e₁ e₂ := by
          rw [ho, hh]; exact Nat.gcd_dvd_right _ _
        rcases Nat.le_total e₁ e₂ with hle | hle
        · rw [max_eq_right hle, min_eq_left hle] at hdvd
          exact hne ((Nat.modEq_iff_dvd' hle).mpr hdvd)
        · rw [max_eq_left hle, min_eq_right hle] at hdvd
          exact hne ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
      -- the elements for the merge and the window
      have hsel : ∃ (E₁ E₂ : Finset ℕ) (w : ℕ), E₁ ⊆ A \ C ∧ E₂ ⊆ A \ C ∧
          (∀ y ∈ E₁, y % δ = e₁ % δ) ∧ (∀ y ∈ E₂, y % δ = e₂ % δ) ∧
          E₁.card = o - 1 ∧ E₂.card = o - 1 ∧
          (∀ y ∈ E₁ ∪ E₂, ∀ y' ∈ E₁ ∪ E₂, y' ≤ y + w) ∧ 4 * ((o - 1) * w) ≤ J * δ := by
        by_cases hbig : 4 * ((2 * ρ) * N) ≤ J * δ
        · obtain ⟨E₁, hE₁, hc₁⟩ := Finset.exists_subset_card_eq
            (show o - 1 ≤ ((A \ C).filter (fun y => y % δ = e₁ % δ)).card by omega)
          obtain ⟨E₂, hE₂, hc₂⟩ := Finset.exists_subset_card_eq
            (show o - 1 ≤ ((A \ C).filter (fun y => y % δ = e₂ % δ)).card by omega)
          refine ⟨E₁, E₂, N, fun y hy => (Finset.mem_filter.mp (hE₁ hy)).1,
            fun y hy => (Finset.mem_filter.mp (hE₂ hy)).1,
            fun y hy => (Finset.mem_filter.mp (hE₁ hy)).2,
            fun y hy => (Finset.mem_filter.mp (hE₂ hy)).2, hc₁, hc₂, ?_, ?_⟩
          · intro y _ y' hy'
            have hy'A : y' ∈ A := by
              rcases Finset.mem_union.mp hy' with h' | h'
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hE₁ h')).1).1
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hE₂ h')).1).1
            have := (hAN y' hy'A).2
            omega
          · have : (o - 1) * N ≤ (2 * ρ) * N := Nat.mul_le_mul_right N (by omega)
            omega
        · -- small modulus: take heavy elements
          have hδΔ : δ ≤ 4 * (2 * ρ) * ρ := by
            by_contra hcon
            have h1 : 4 * (2 * ρ) * ρ * J ≤ δ * J := Nat.mul_le_mul_right J (by omega)
            have h2 : 4 * (2 * ρ) * N ≤ 4 * (2 * ρ) * (ρ * J) := Nat.mul_le_mul_left _ hNJ'
            have h3 : 4 * (2 * ρ) * (ρ * J) = 4 * (2 * ρ) * ρ * J := by ring
            have h4 : δ * J = J * δ := Nat.mul_comm _ _
            have h5 : 4 * ((2 * ρ) * N) = 4 * (2 * ρ) * N := by ring
            omega
          have hk3 := hK3 hδΔ
          have hcl : ∀ e : ℕ, nst ≤ ((A \ C).filter (fun y => y % δ = e % δ)).card →
              o - 1 ≤ (((A \ C).filter (fun y => y % δ = e % δ)) ∩ H).card := by
            intro e hbe
            have h1 := Finset.card_sdiff_add_card_inter ((A \ C).filter (fun y => y % δ = e % δ)) H
            have h2 : (((A \ C).filter (fun y => y % δ = e % δ)) \ H).card ≤ ((A \ C) \ H).card :=
              Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) subset_rfl)
            omega
          obtain ⟨E₁, hE₁, hc₁⟩ := Finset.exists_subset_card_eq (hcl e₁ hb₁)
          obtain ⟨E₂, hE₂, hc₂⟩ := Finset.exists_subset_card_eq (hcl e₂ hb₂)
          have hEH : ∀ y ∈ E₁ ∪ E₂, y ∈ H := by
            intro y hy
            rcases Finset.mem_union.mp hy with h' | h'
            · exact (Finset.mem_inter.mp (hE₁ h')).2
            · exact (Finset.mem_inter.mp (hE₂ h')).2
          refine ⟨E₁, E₂, J / 4,
            fun y hy => (Finset.mem_filter.mp (Finset.mem_inter.mp (hE₁ hy)).1).1,
            fun y hy => (Finset.mem_filter.mp (Finset.mem_inter.mp (hE₂ hy)).1).1,
            fun y hy => (Finset.mem_filter.mp (Finset.mem_inter.mp (hE₁ hy)).1).2,
            fun y hy => (Finset.mem_filter.mp (Finset.mem_inter.mp (hE₂ hy)).1).2, hc₁, hc₂, ?_, ?_⟩
          · intro y hy y' hy'
            have := hHdiam y (hEH y hy) y' (hEH y' hy')
            omega
          · have hoδ : o ≤ δ := by rw [ho]; exact Nat.le_mul_of_pos_right o hh1
            have h1 : (o - 1) * (J / 4) ≤ δ * (J / 4) := Nat.mul_le_mul_right _ (by omega)
            have h2 : 4 * (δ * (J / 4)) ≤ J * δ := by
              have e1 := Nat.mul_le_mul_left δ (Nat.mul_div_le J 4)
              have e2 : 4 * (δ * (J / 4)) = δ * (4 * (J / 4)) := by ring
              have e3 : δ * J = J * δ := Nat.mul_comm _ _
              omega
            omega
      obtain ⟨E₁, E₂, w, hE₁, hE₂, hr₁, hr₂, hc₁, hc₂, hw, hw4⟩ := hsel
      have hJ1 : (o - 1) * w ≤ (J - 1) * δ := by
        have h1 : 8 * ((J - 1) * δ) ≥ 7 * (J * δ) := by
          obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          have e1 : 7 * δ ≤ J' * δ := Nat.mul_le_mul_right δ (by omega)
          have e2 : (J' + 1) * δ = J' * δ + δ := by ring
          omega
        omega
      obtain ⟨x0', habsN⟩ := hMerge C t x0 δ J E₁ E₂ e₁ e₂ h o w hδ habs hE₁ hE₂ hr₁ hr₂ hne hh ho
        hc₁ hc₂ hw hJ1
      have hsize := hMsize δ J h o w ho hh1 hw4 (by omega) ho2
      have hsubA : ∀ {Z : Finset ℕ}, Z ⊆ A \ C → Z ⊆ A :=
        fun hZ z hz => (Finset.mem_sdiff.mp (hZ hz)).1
      have hC' : C ∪ E₁ ∪ E₂ ⊆ A :=
        Finset.union_subset (Finset.union_subset hC (hsubA hE₁)) (hsubA hE₂)
      have hC'card : (C ∪ E₁ ∪ E₂).card ≤ C.card + 2 * (o - 1) := by
        have h1 := Finset.card_union_le (C ∪ E₁) E₂
        have h2 := Finset.card_union_le C E₁
        omega
      have h2h : 2 * h ≤ δ := by rw [ho]; exact Nat.mul_le_mul_right h ho2
      have hlog := log_half hh1 h2h
      have hmul1 : 2 * (2 * ρ) * (Nat.log 2 h + 1) ≤ 2 * (2 * ρ) * Nat.log 2 δ :=
        Nat.mul_le_mul_left _ hlog
      have hmul2 : 2 * ρ * (Nat.log 2 h + 1) ≤ 2 * ρ * Nat.log 2 δ := Nat.mul_le_mul_left _ hlog
      exact ih h (by omega) (C ∪ E₁ ∪ E₂) (t + (o - 1)) x0'
        (((J - 1) * δ - (o - 1) * w) / h) hC' (by omega) hh1 habsN (by omega)
        (by rw [Nat.mul_add] at hmul1; omega) (by rw [Nat.mul_add] at hmul2; omega)
    · -- Case 2: at most one big class
      push Not at hcase
      have hex : ∃ e ∈ A \ C, nst ≤ ((A \ C).filter (fun y => y % δ = e % δ)).card := by
        by_contra hcon
        push Not at hcon
        have h1 := Finset.card_le_mul_card_image (f := fun y => y % δ) (A \ C) nst (by
          intro r hr
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
          exact (hcon e he).le)
        have h2 : nst * ((A \ C).image (· % δ)).card ≤ nst * (2 * ρ) :=
          Nat.mul_le_mul_left _ hfew.le
        have h3 : nst * (2 * ρ) = 2 * ρ * nst := Nat.mul_comm _ _
        omega
      obtain ⟨e, he, hbe⟩ := hex
      -- the other classes are small
      have hother : ((A \ C).filter (fun y => ¬ y % δ = e % δ)).card ≤ nst * (2 * ρ) := by
        have h1 := Finset.card_le_mul_card_image (f := fun y => y % δ)
          ((A \ C).filter (fun y => ¬ y % δ = e % δ)) nst (by
          intro r hr
          obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hr
          obtain ⟨he'D, he'ne⟩ := Finset.mem_filter.mp he'
          by_contra hcon
          have hbig' : nst ≤ ((A \ C).filter (fun y => y % δ = e' % δ)).card := by
            refine le_trans (Nat.le_of_not_le hcon) (Finset.card_le_card ?_)
            intro y hy
            obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy1).1, hy2⟩
          have := hcase e he e' he'D (fun h => he'ne h.symm) hbe
          omega)
        have h2 : (((A \ C).filter (fun y => ¬ y % δ = e % δ)).image (fun y => y % δ)).card ≤
            ((A \ C).image (· % δ)).card :=
          Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
        have h3 : nst * (((A \ C).filter (fun y => ¬ y % δ = e % δ)).image
            (fun y => y % δ)).card ≤ nst * (2 * ρ) := Nat.mul_le_mul_left _ (by omega)
        omega
      -- the set B
      have hfin : ∃ B : Finset ℕ, B ⊆ (A \ C).filter (fun y => y % δ = e % δ) ∧
          (∀ y ∈ B, ∀ y' ∈ B, y' ≤ y + J * δ) ∧
          (((A \ C).filter (fun y => y % δ = e % δ)) \ B).card ≤
            (N / η + 1) * (2 * ρ) * (4 * (2 * ρ) * ρ * (16 * ρ * ρ + 1)) := by
        by_cases hbig : N ≤ J * δ
        · refine ⟨_, subset_rfl, ?_, by simp⟩
          intro y _ y' hy'
          have := (hAN y' (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy').1).1).2
          omega
        · have hδΔ : δ ≤ 4 * (2 * ρ) * ρ := by
            by_contra hcon
            have h0 : ρ ≤ 4 * (2 * ρ) * ρ := Nat.le_mul_of_pos_left ρ (by omega)
            have h1 : ρ * J ≤ δ * J := Nat.mul_le_mul_right J (by omega)
            have h4 : δ * J = J * δ := Nat.mul_comm _ _
            omega
          refine ⟨((A \ C).filter (fun y => y % δ = e % δ)) ∩ H, Finset.inter_subset_left, ?_, ?_⟩
          · intro y hy y' hy'
            have := hHdiam y (Finset.mem_inter.mp hy).2 y' (Finset.mem_inter.mp hy').2
            have h1 : J ≤ J * δ := Nat.le_mul_of_pos_right J hδ
            omega
          · rw [Finset.sdiff_inter_self_left]
            exact (Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.filter_subset _ _)
              subset_rfl)).trans (hK3 hδΔ)
      obtain ⟨B, hB1, hBdiam, hBc⟩ := hfin
      have hBD : B ⊆ A \ C := hB1.trans (Finset.filter_subset _ _)
      refine ⟨δ, hδ, B, fun y hy => (Finset.mem_sdiff.mp (hBD hy)).1, ?_, ?_, ?_⟩
      · have hsub : A \ B ⊆ C ∪ ((A \ C).filter (fun y => ¬ y % δ = e % δ)) ∪
            (((A \ C).filter (fun y => y % δ = e % δ)) \ B) := by
          intro y hy
          obtain ⟨hyA, hyB⟩ := Finset.mem_sdiff.mp hy
          by_cases hyC : y ∈ C
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hyC)
          · by_cases hye : y % δ = e % δ
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyA, hyC⟩, hye⟩, hyB⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyA, hyC⟩, hye⟩))
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (C ∪ ((A \ C).filter (fun y => ¬ y % δ = e % δ)))
          (((A \ C).filter (fun y => y % δ = e % δ)) \ B)
        have h3 := Finset.card_union_le C ((A \ C).filter (fun y => ¬ y % δ = e % δ))
        have h4 : nst * (2 * ρ) = 2 * ρ * nst := Nat.mul_comm _ _
        omega
      · intro a ha b hb
        rw [(Finset.mem_filter.mp (hB1 ha)).2, (Finset.mem_filter.mp (hB1 hb)).2]
      · intro κ hκ U V hU hV hUc hVc
        exact ord_class hadm (fun x hx => (hAN x hx).1) ht hδ habs' hBD
          (fun y hy => (Finset.mem_filter.mp (hB1 hy)).2) hBdiam hκ hδ (Dvd.intro _ rfl)
          hU hV hUc hVc

end L7


lemma sq_le_two_pow : ∀ m : ℕ, 4 ≤ m → m * m ≤ 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith

lemma log_small {Q k : ℕ} (hQ : Q * Q ≤ k) (hk : 16 ≤ k) : Q * Nat.log 2 k ≤ k := by
  have hm : Nat.log 2 k * Nat.log 2 k ≤ k := by
    rcases Nat.lt_or_ge (Nat.log 2 k) 4 with h | h
    · have : Nat.log 2 k * Nat.log 2 k ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
      omega
    · exact (sq_le_two_pow _ h).trans (Nat.pow_log_le_self 2 (by omega))
  have h1 : (Q * Nat.log 2 k) * (Q * Nat.log 2 k) ≤ k * k := by
    calc (Q * Nat.log 2 k) * (Q * Nat.log 2 k)
        = (Q * Q) * (Nat.log 2 k * Nat.log 2 k) := by ring
      _ ≤ k * k := Nat.mul_le_mul hQ hm
  exact Nat.mul_self_le_mul_self_iff.mp h1


namespace OMA.DF.Merge

/-- A set inside one residue class: its sum is congruent to `card * e`. -/
lemma sum_mod (R : Finset ℕ) (δ e : ℕ) (h : ∀ y ∈ R, y % δ = e % δ) :
    (δ : ℤ) ∣ ((∑ y ∈ R, y : ℕ) : ℤ) - R.card * e := by
  have hrw : ((∑ y ∈ R, y : ℕ) : ℤ) - R.card * e = ∑ y ∈ R, ((y : ℤ) - e) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hrw]
  refine Finset.dvd_sum fun y hy => ?_
  have h1 : (δ : ℤ) ∣ (e : ℤ) - y := (Nat.modEq_iff_dvd).mp (h y hy)
  exact (dvd_sub_comm).mp h1

/-- A mixed set: `n - r` elements of the class of `e₁` and `r` elements of the class of `e₂`. -/
lemma mix {E₁ E₂ : Finset ℕ} {δ e₁ e₂ n r : ℕ}
    (h₁ : ∀ y ∈ E₁, y % δ = e₁ % δ) (h₂ : ∀ y ∈ E₂, y % δ = e₂ % δ) (hne : e₁ % δ ≠ e₂ % δ)
    (hr : r ≤ n) (hc₁ : n - r ≤ E₁.card) (hc₂ : r ≤ E₂.card) :
    ∃ Z : Finset ℕ, Z ⊆ E₁ ∪ E₂ ∧ Z.card = n ∧
      (δ : ℤ) ∣ ((∑ y ∈ Z, y : ℕ) : ℤ) - (n * e₁ + r * ((e₂ : ℤ) - e₁)) := by
  obtain ⟨R₁, hR₁, hR₁c⟩ := Finset.exists_subset_card_eq hc₁
  obtain ⟨R₂, hR₂, hR₂c⟩ := Finset.exists_subset_card_eq hc₂
  have hdisj : Disjoint R₁ R₂ := by
    refine Finset.disjoint_left.mpr fun y hy1 hy2 => hne ?_
    rw [← h₁ y (hR₁ hy1), ← h₂ y (hR₂ hy2)]
  refine ⟨R₁ ∪ R₂, Finset.union_subset_union hR₁ hR₂, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hR₁c, hR₂c]
    omega
  · have d1 := sum_mod R₁ δ e₁ (fun y hy => h₁ y (hR₁ hy))
    have d2 := sum_mod R₂ δ e₂ (fun y hy => h₂ y (hR₂ hy))
    rw [hR₁c, Nat.cast_sub hr] at d1
    rw [hR₂c] at d2
    have d3 := dvd_add d1 d2
    rw [Finset.sum_union hdisj]
    have e : ((∑ y ∈ R₁, y + ∑ y ∈ R₂, y : ℕ) : ℤ) - (n * e₁ + r * ((e₂ : ℤ) - e₁)) =
        ((∑ y ∈ R₁, y : ℕ) : ℤ) - ((n : ℤ) - r) * e₁ + (((∑ y ∈ R₂, y : ℕ) : ℤ) - r * e₂) := by
      push_cast
      ring
    rw [e]
    exact d3

lemma natAbs_sub (e₁ e₂ : ℕ) : ((e₂ : ℤ) - e₁).natAbs = max e₁ e₂ - min e₁ e₂ := by
  rcases le_total e₁ e₂ with h | h
  · rw [max_eq_right h, min_eq_left h]
    omega
  · rw [max_eq_left h, min_eq_right h]
    omega

/-- Bézout: every multiple of `h = gcd(δ, |g|)` is congruent mod `δ` to `r g` with `r < δ / h`. -/
lemma bez {δ o h : ℕ} {g : ℤ} (ho : δ = o * h) (hh : h = Nat.gcd δ g.natAbs) (hδ : 1 ≤ δ)
    {m : ℤ} (hm : (h : ℤ) ∣ m) : ∃ r : ℕ, r < o ∧ (δ : ℤ) ∣ m - r * g := by
  have ho0 : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · rw [h0, Nat.zero_mul] at ho
      omega
    · exact h0
  obtain ⟨m', rfl⟩ := hm
  have hgd : (h : ℤ) ∣ g := by
    rw [hh]
    exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨g'', hg⟩ := hgd
  have hbez : (h : ℤ) = δ * Int.gcdA δ g + g * Int.gcdB δ g := by
    rw [← Int.gcd_eq_gcd_ab (δ : ℤ) g, hh]
    simp [Int.gcd]
  have hδ' : (δ : ℤ) = o * h := by exact_mod_cast ho
  have hoZ : (0 : ℤ) < o := by exact_mod_cast ho0
  have hq := Int.emod_add_mul_ediv (m' * Int.gcdB δ g) (o : ℤ)
  have hr0 := Int.emod_nonneg (m' * Int.gcdB δ g) (ne_of_gt hoZ)
  have hr1 := Int.emod_lt_of_pos (m' * Int.gcdB δ g) hoZ
  refine ⟨((m' * Int.gcdB δ g) % (o : ℤ)).toNat, by omega,
    ⟨Int.gcdA δ g * m' + g'' * ((m' * Int.gcdB δ g) / (o : ℤ)), ?_⟩⟩
  rw [Int.toNat_of_nonneg hr0]
  linear_combination m' * hbez - g * hq + (o * ((m' * Int.gcdB δ g) / (o : ℤ))) * hg -
    (g'' * ((m' * Int.gcdB δ g) / (o : ℤ))) * hδ'

/-- **L5 (merge)**, interface statement of the project plan (WP-A). -/
theorem merge {A C : Finset ℕ} {t x0 δ J : ℕ} (hδ : 1 ≤ δ)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    {E₁ E₂ : Finset ℕ} (hE₁ : E₁ ⊆ A \ C) (hE₂ : E₂ ⊆ A \ C) {e₁ e₂ : ℕ}
    (h₁ : ∀ y ∈ E₁, y % δ = e₁ % δ) (h₂ : ∀ y ∈ E₂, y % δ = e₂ % δ) (hne : e₁ % δ ≠ e₂ % δ)
    {h o w : ℕ} (hh : h = Nat.gcd δ (max e₁ e₂ - min e₁ e₂)) (ho : δ = o * h)
    (hc₁ : E₁.card = o - 1) (hc₂ : E₂.card = o - 1)
    (hw : ∀ y ∈ E₁ ∪ E₂, ∀ y' ∈ E₁ ∪ E₂, y' ≤ y + w) (hJ : (o - 1) * w ≤ (J - 1) * δ) :
    ∃ x0' : ℕ, ∀ j, j < ((J - 1) * δ - (o - 1) * w) / h →
      ∃ T : Finset ℕ, T ⊆ C ∪ E₁ ∪ E₂ ∧ T.card = t + (o - 1) ∧ ∑ x ∈ T, x = x0' + j * h := by
  have hh' : h = Nat.gcd δ ((e₂ : ℤ) - e₁).natAbs := by rw [natAbs_sub]; exact hh
  have hh0 : 0 < h := by
    rw [hh]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨n, hn⟩ : ∃ n, o - 1 = n := ⟨_, rfl⟩
  rw [hn] at hc₁ hc₂ hJ ⊢
  obtain ⟨m, hm⟩ : ∃ m, ∀ y ∈ E₁ ∪ E₂, m ≤ y ∧ y ≤ m + w := by
    rcases (E₁ ∪ E₂).eq_empty_or_nonempty with he | hne'
    · exact ⟨0, by simp [he]⟩
    · exact ⟨(E₁ ∪ E₂).min' hne', fun y hy =>
        ⟨Finset.min'_le _ _ hy, hw _ (Finset.min'_mem _ _) y hy⟩⟩
  have hwin : ∀ Z : Finset ℕ, Z ⊆ E₁ ∪ E₂ → Z.card = n →
      n * m ≤ ∑ y ∈ Z, y ∧ ∑ y ∈ Z, y ≤ n * m + n * w := by
    intro Z hZ hc
    constructor
    · have := Finset.card_nsmul_le_sum Z (fun y => y) m (fun y hy => (hm y (hZ hy)).1)
      rw [hc, smul_eq_mul] at this
      exact this
    · have := Finset.sum_le_card_nsmul Z (fun y => y) (m + w) (fun y hy => (hm y (hZ hy)).2)
      rw [hc, smul_eq_mul, Nat.mul_add] at this
      exact this
  obtain ⟨lo, hlo⟩ : ∃ lo, x0 + n * m + n * w = lo := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ((x0 : ℤ) + n * e₁ - lo) % (h : ℤ) = ε := ⟨_, rfl⟩
  have hhZ : (0 : ℤ) < h := by exact_mod_cast hh0
  have hε0 : 0 ≤ ε := by rw [← hε]; exact Int.emod_nonneg _ (ne_of_gt hhZ)
  have hε1 : ε < h := by rw [← hε]; exact Int.emod_lt_of_pos _ hhZ
  have hεdiv := Int.emod_add_mul_ediv ((x0 : ℤ) + n * e₁ - lo) (h : ℤ)
  rw [hε] at hεdiv
  refine ⟨lo + ε.toNat, fun j hj => ?_⟩
  have hεn : ((ε.toNat : ℕ) : ℤ) = ε := Int.toNat_of_nonneg hε0
  have hεlt : ε.toNat < h := by omega
  -- the class of `y` modulo `h`
  have hcls : (h : ℤ) ∣ ((lo + ε.toNat + j * h : ℕ) : ℤ) - ((x0 : ℤ) + n * e₁) :=
    ⟨(j : ℤ) - ((x0 : ℤ) + n * e₁ - lo) / (h : ℤ), by
      push_cast
      rw [hεn]
      linear_combination hεdiv⟩
  obtain ⟨r, hr, hrdvd⟩ := bez ho hh' hδ hcls
  obtain ⟨Z, hZ, hZc, hZdvd⟩ := mix (n := n) (r := r) h₁ h₂ hne (by omega) (by omega) (by omega)
  have hZw := hwin Z hZ hZc
  have hdvdZ : (δ : ℤ) ∣ ((lo + ε.toNat + j * h : ℕ) : ℤ) - ((x0 + ∑ y ∈ Z, y : ℕ) : ℤ) := by
    have := dvd_sub hrdvd hZdvd
    have e : ((lo + ε.toNat + j * h : ℕ) : ℤ) - ((x0 + ∑ y ∈ Z, y : ℕ) : ℤ) =
        ((lo + ε.toNat + j * h : ℕ) : ℤ) - ((x0 : ℤ) + n * e₁) - r * ((e₂ : ℤ) - e₁) -
          (((∑ y ∈ Z, y : ℕ) : ℤ) - (n * e₁ + r * ((e₂ : ℤ) - e₁))) := by
      push_cast
      ring
    rw [e]
    exact this
  have hlow : x0 + ∑ y ∈ Z, y ≤ lo + ε.toNat + j * h := by
    have := hZw.2
    have : 0 ≤ j * h := Nat.zero_le _
    omega
  have hJ' : ((J - 1) * δ - n * w) / h * h ≤ (J - 1) * δ - n * w := Nat.div_mul_le_self _ _
  have hjh : (j + 1) * h ≤ ((J - 1) * δ - n * w) / h * h := Nat.mul_le_mul_right h hj
  rw [Nat.succ_mul] at hjh
  have hup : lo + ε.toNat + j * h ≤ x0 + ∑ y ∈ Z, y + (J - 1) * δ := by
    have := hZw.1
    omega
  have hdvdN : δ ∣ lo + ε.toNat + j * h - (x0 + ∑ y ∈ Z, y) := by
    have := hdvdZ
    rw [← Nat.cast_sub hlow] at this
    exact Int.natCast_dvd_natCast.mp this
  obtain ⟨i, hi⟩ := hdvdN
  have hJpos : 1 ≤ J := by
    by_contra hJ0
    have hJz : J - 1 = 0 := by omega
    rw [hJz, Nat.zero_mul, Nat.zero_sub, Nat.zero_div] at hj
    omega
  have hiJ : i < J := by
    have h1 : δ * i ≤ (J - 1) * δ := by omega
    rw [Nat.mul_comm] at h1
    have := Nat.le_of_mul_le_mul_right h1 (by omega : 0 < δ)
    omega
  obtain ⟨T, hTC, hTc, hTs⟩ := habs i hiJ
  have hdisj : Disjoint T Z := by
    refine Finset.disjoint_left.mpr fun y hyT hyZ => ?_
    have hyE : y ∈ A \ C := Finset.union_subset hE₁ hE₂ (hZ hyZ)
    exact (Finset.mem_sdiff.mp hyE).2 (hTC hyT)
  refine ⟨T ∪ Z, ?_, ?_, ?_⟩
  · intro y hy
    rw [Finset.union_assoc, Finset.mem_union]
    rcases Finset.mem_union.mp hy with hy' | hy'
    · exact Or.inl (hTC hy')
    · exact Or.inr (hZ hy')
  · rw [Finset.card_union_of_disjoint hdisj, hTc, hZc]
  · rw [Finset.sum_union hdisj, hTs]
    have : i * δ = δ * i := Nat.mul_comm _ _
    omega

/-- Size of the merged progression (WP-A, `merge_size`): `J' ≥ J`. -/
theorem merge_size {δ J h o w : ℕ} (hδ : 1 ≤ δ) (ho : δ = o * h)
    (hw : 4 * ((o - 1) * w) ≤ J * δ) (hJ : 8 ≤ J) (ho2 : 2 ≤ o) :
    J ≤ ((J - 1) * δ - (o - 1) * w) / h := by
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, Nat.mul_zero] at ho
      omega
    · exact h0
  rw [Nat.le_div_iff_mul_le hh0]
  obtain ⟨W, hW⟩ : ∃ W, (o - 1) * w = W := ⟨_, rfl⟩
  rw [hW] at hw ⊢
  have h1 : (J - 1) * δ + δ = J * δ := by
    have : J = (J - 1) + 1 := by omega
    conv_rhs => rw [this, Nat.succ_mul]
  have h2 : 2 * h ≤ δ := by
    rw [ho]
    exact Nat.mul_le_mul_right h ho2
  have h3 : 8 * δ ≤ J * δ := Nat.mul_le_mul_right δ hJ
  have h4 : J * (2 * h) ≤ J * δ := Nat.mul_le_mul_left J h2
  have h5 : J * (2 * h) = 2 * (J * h) := by ring
  omega

end OMA.DF.Merge

namespace OMA.DF.Count

/-- A set inside one residue class: its sum is congruent to `card * e`. -/
lemma sum_mod (R : Finset ℕ) (δ e : ℕ) (h : ∀ y ∈ R, y % δ = e % δ) :
    (δ : ℤ) ∣ ((∑ y ∈ R, y : ℕ) : ℤ) - R.card * e := by
  have hrw : ((∑ y ∈ R, y : ℕ) : ℤ) - R.card * e = ∑ y ∈ R, ((y : ℤ) - e) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hrw]
  refine Finset.dvd_sum fun y hy => ?_
  have h1 : (δ : ℤ) ∣ (e : ℤ) - y := (Nat.modEq_iff_dvd).mp (h y hy)
  exact (dvd_sub_comm).mp h1

/-- A mixed set: `n - r` elements of the class of `e₁` and `r` elements of the class of `e₂`. -/
lemma mix {E₁ E₂ : Finset ℕ} {δ e₁ e₂ n r : ℕ}
    (h₁ : ∀ y ∈ E₁, y % δ = e₁ % δ) (h₂ : ∀ y ∈ E₂, y % δ = e₂ % δ) (hne : e₁ % δ ≠ e₂ % δ)
    (hr : r ≤ n) (hc₁ : n - r ≤ E₁.card) (hc₂ : r ≤ E₂.card) :
    ∃ Z : Finset ℕ, Z ⊆ E₁ ∪ E₂ ∧ Z.card = n ∧
      (δ : ℤ) ∣ ((∑ y ∈ Z, y : ℕ) : ℤ) - (n * e₁ + r * ((e₂ : ℤ) - e₁)) := by
  obtain ⟨R₁, hR₁, hR₁c⟩ := Finset.exists_subset_card_eq hc₁
  obtain ⟨R₂, hR₂, hR₂c⟩ := Finset.exists_subset_card_eq hc₂
  have hdisj : Disjoint R₁ R₂ := by
    refine Finset.disjoint_left.mpr fun y hy1 hy2 => hne ?_
    rw [← h₁ y (hR₁ hy1), ← h₂ y (hR₂ hy2)]
  refine ⟨R₁ ∪ R₂, Finset.union_subset_union hR₁ hR₂, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hR₁c, hR₂c]
    omega
  · have d1 := sum_mod R₁ δ e₁ (fun y hy => h₁ y (hR₁ hy))
    have d2 := sum_mod R₂ δ e₂ (fun y hy => h₂ y (hR₂ hy))
    rw [hR₁c, Nat.cast_sub hr] at d1
    rw [hR₂c] at d2
    have d3 := dvd_add d1 d2
    rw [Finset.sum_union hdisj]
    have e : ((∑ y ∈ R₁, y + ∑ y ∈ R₂, y : ℕ) : ℤ) - (n * e₁ + r * ((e₂ : ℤ) - e₁)) =
        ((∑ y ∈ R₁, y : ℕ) : ℤ) - ((n : ℤ) - r) * e₁ + (((∑ y ∈ R₂, y : ℕ) : ℤ) - r * e₂) := by
      push_cast
      ring
    rw [e]
    exact d3

lemma natAbs_sub (e₁ e₂ : ℕ) : ((e₂ : ℤ) - e₁).natAbs = max e₁ e₂ - min e₁ e₂ := by
  rcases le_total e₁ e₂ with h | h
  · rw [max_eq_right h, min_eq_left h]
    omega
  · rw [max_eq_left h, min_eq_right h]
    omega

/-- **L3 (counting)**, WP-C. The hypothesis `hδ : 1 ≤ δ` is necessary (see the README). -/
theorem count {A C : Finset ℕ} {t x0 δ J N s ρ z : ℕ} (hδ : 1 ≤ δ) (hC : C ⊆ A)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    (hs : ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card < 2 * N) (hN : N ≤ ρ * J)
    (𝒵 : Finset (Finset ℕ)) (hZ : ∀ Z ∈ 𝒵, Z ⊆ A \ C ∧ Z.card = z)
    (hsep : ∀ Z ∈ 𝒵, ∀ Z' ∈ 𝒵, Z ≠ Z' → ∀ i, i < J → ∑ x ∈ Z, x ≠ ∑ x ∈ Z', x + i * δ)
    (htz : t + z ≤ s) (hpad : s - t - z + (𝒵.biUnion id).card ≤ (A \ C).card) :
    𝒵.card < 2 * ρ := by
  have hU : 𝒵.biUnion id ⊆ A \ C := Finset.biUnion_subset.mpr fun Z hZm => (hZ Z hZm).1
  obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq (s := (A \ C) \ 𝒵.biUnion id)
    (n := s - t - z) (by rw [Finset.card_sdiff_of_subset hU]; omega)
  choose! Tf hTf using habs
  have hcard : 𝒵.card * J ≤ ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card := by
    have h := Finset.card_le_card_of_injOn (s := 𝒵 ×ˢ Finset.range J)
      (t := (A.powersetCard s).image (fun T => ∑ x ∈ T, x))
      (fun p : Finset ℕ × ℕ => x0 + p.2 * δ + ∑ x ∈ p.1, x + ∑ x ∈ W, x) (by
        intro p hp
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
        obtain ⟨hT1, hT2, hT3⟩ := hTf p.2 hp.2
        obtain ⟨hZ1, hZ2⟩ := hZ p.1 hp.1
        have hd1 : Disjoint (Tf p.2) p.1 := by
          refine Finset.disjoint_left.mpr fun y hyT hyZ => ?_
          exact (Finset.mem_sdiff.mp (hZ1 hyZ)).2 (hT1 hyT)
        have hd2 : Disjoint (Tf p.2 ∪ p.1) W := by
          refine Finset.disjoint_left.mpr fun y hy hyW => ?_
          have hyW' := Finset.mem_sdiff.mp (hW hyW)
          rcases Finset.mem_union.mp hy with hy' | hy'
          · exact (Finset.mem_sdiff.mp hyW'.1).2 (hT1 hy')
          · exact hyW'.2 (Finset.mem_biUnion.mpr ⟨p.1, hp.1, hy'⟩)
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Tf p.2 ∪ p.1 ∪ W,
          Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩)
        · refine Finset.union_subset (Finset.union_subset (hT1.trans hC)
            (hZ1.trans Finset.sdiff_subset)) ?_
          exact (hW.trans Finset.sdiff_subset).trans Finset.sdiff_subset
        · rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hT2, hZ2,
            hWc]
          omega
        · rw [Finset.sum_union hd2, Finset.sum_union hd1, hT3]) (by
        intro p hp p' hp' hpp
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hp'
        dsimp only at hpp
        by_cases hZZ : p.1 = p'.1
        · refine Prod.ext hZZ ?_
          rw [hZZ] at hpp
          exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < δ) (by omega)
        · exfalso
          rcases le_total p.2 p'.2 with hle | hle
          · have h1 : p.2 * δ ≤ p'.2 * δ := Nat.mul_le_mul_right δ hle
            refine hsep p.1 hp.1 p'.1 hp'.1 hZZ (p'.2 - p.2) (by omega) ?_
            rw [Nat.sub_mul]
            omega
          · have h1 : p'.2 * δ ≤ p.2 * δ := Nat.mul_le_mul_right δ hle
            refine hsep p'.1 hp'.1 p.1 hp.1 (Ne.symm hZZ) (p.2 - p'.2) (by omega) ?_
            rw [Nat.sub_mul]
            omega)
    rw [Finset.card_product, Finset.card_range] at h
    exact h
  by_contra hcon
  have h1 : 2 * ρ * J ≤ 𝒵.card * J := Nat.mul_le_mul_right J (by omega)
  have h2 : 2 * N ≤ 2 * (ρ * J) := Nat.mul_le_mul_left 2 hN
  have h3 : 2 * ρ * J = 2 * (ρ * J) := Nat.mul_assoc _ _ _
  omega

/-- **L4 (a)**, WP-C: the complement of an absorber meets fewer than `2 ρ` classes. -/
theorem few_classes {A C : Finset ℕ} {t x0 δ J N s ρ : ℕ} (hC : C ⊆ A)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    (hs : ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card < 2 * N) (hN : N ≤ ρ * J)
    (hδ : 1 ≤ δ) (ht1 : t + 1 ≤ s) (hbig : s + 2 * ρ ≤ (A \ C).card) :
    ((A \ C).image (· % δ)).card < 2 * ρ := by
  by_contra hcon
  obtain ⟨I, hI, hIc⟩ := Finset.exists_subset_card_eq (by omega :
    2 * ρ ≤ ((A \ C).image (· % δ)).card)
  have hrep : ∀ c ∈ I, ∃ a, a ∈ A \ C ∧ a % δ = c := by
    intro c hc
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp (hI hc)
    exact ⟨a, ha, hac⟩
  choose! a ha using hrep
  have hinj : Set.InjOn (fun c => ({a c} : Finset ℕ)) (I : Set ℕ) := by
    intro c hc c' hc' hcc
    have h1 : a c = a c' := Finset.singleton_inj.mp hcc
    rw [← (ha c hc).2, ← (ha c' hc').2, h1]
  have hcard : (I.image (fun c => ({a c} : Finset ℕ))).card = 2 * ρ := by
    rw [Finset.card_image_of_injOn hinj, hIc]
  have hunion : ((I.image (fun c => ({a c} : Finset ℕ))).biUnion id).card ≤ 2 * ρ := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← hcard]
    refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans (by simp)
    intro Z hZ
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hZ
    simp
  have hlt := count (z := 1) hδ hC habs hs hN (I.image (fun c => ({a c} : Finset ℕ))) (by
      intro Z hZ
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hZ
      exact ⟨Finset.singleton_subset_iff.mpr (ha c hc).1, Finset.card_singleton _⟩) (by
      intro Z hZ Z' hZ' hne i _ heq
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hZ
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hZ'
      rw [Finset.sum_singleton, Finset.sum_singleton] at heq
      apply hne
      have h1 : a c % δ = a c' % δ := by rw [heq, Nat.add_mul_mod_self_right]
      rw [(ha c hc).2, (ha c' hc').2] at h1
      rw [h1]) (by omega) (by omega)
  omega

/-- Multiples `r g`, `r < K`, are pairwise incongruent mod `δ` when `K gcd(δ, |g|) ≤ δ`. -/
lemma incong {δ K : ℕ} {g : ℤ} (hδ : 1 ≤ δ) (hK : K * Nat.gcd δ g.natAbs ≤ δ) {r r' : ℕ}
    (hr : r < K) (hr' : r' < K) (hd : (δ : ℤ) ∣ ((r : ℤ) - r') * g) : r = r' := by
  by_contra hne
  have h1 : δ ∣ ((r : ℤ) - r').natAbs * g.natAbs := by
    rw [← Int.natAbs_mul]
    exact Int.natCast_dvd.mp hd
  have h2 : δ ∣ ((r : ℤ) - r').natAbs * δ := Dvd.intro_left _ rfl
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left, Nat.gcd_comm] at h3
  have hd0 : 0 < ((r : ℤ) - r').natAbs := by omega
  have hdK : ((r : ℤ) - r').natAbs < K := by omega
  have hh0 : 0 < Nat.gcd δ g.natAbs := Nat.gcd_pos_of_pos_left _ (by omega)
  have h4 := Nat.le_of_dvd (Nat.mul_pos hd0 hh0) h3
  have h5 : ((r : ℤ) - r').natAbs * Nat.gcd δ g.natAbs < K * Nat.gcd δ g.natAbs :=
    Nat.mul_lt_mul_of_pos_right hdK hh0
  omega

/-- **L4 (c)**, WP-C: two classes with many elements differ by an element of small order. -/
theorem small_order {A C : Finset ℕ} {t x0 δ J N s ρ : ℕ} (hC : C ⊆ A)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    (hs : ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card < 2 * N) (hN : N ≤ ρ * J)
    (hδ : 1 ≤ δ) (htK : t + 2 * ρ ≤ s) (hbig : s + 4 * ρ ≤ (A \ C).card)
    {e₁ e₂ : ℕ} (he₁ : e₁ ∈ A \ C) (he₂ : e₂ ∈ A \ C) (hne : e₁ % δ ≠ e₂ % δ)
    (hn₁ : 2 * ρ - 1 ≤ ((A \ C).filter (fun y => y % δ = e₁ % δ)).card)
    (hn₂ : 2 * ρ - 1 ≤ ((A \ C).filter (fun y => y % δ = e₂ % δ)).card) :
    δ < 2 * ρ * Nat.gcd δ (max e₁ e₂ - min e₁ e₂) := by
  have _h1 := he₁
  have _h2 := he₂
  by_contra hcon
  rw [← natAbs_sub] at hcon
  have hK : 2 * ρ * Nat.gcd δ ((e₂ : ℤ) - e₁).natAbs ≤ δ := by omega
  obtain ⟨F₁, hF₁, hF₁c⟩ := Finset.exists_subset_card_eq hn₁
  obtain ⟨F₂, hF₂, hF₂c⟩ := Finset.exists_subset_card_eq hn₂
  have hF₁A : F₁ ⊆ A \ C := hF₁.trans (Finset.filter_subset _ _)
  have hF₂A : F₂ ⊆ A \ C := hF₂.trans (Finset.filter_subset _ _)
  have hm₁ : ∀ y ∈ F₁, y % δ = e₁ % δ := fun y hy => (Finset.mem_filter.mp (hF₁ hy)).2
  have hm₂ : ∀ y ∈ F₂, y % δ = e₂ % δ := fun y hy => (Finset.mem_filter.mp (hF₂ hy)).2
  have key : ∀ r, r < 2 * ρ → ∃ Z : Finset ℕ, Z ⊆ F₁ ∪ F₂ ∧ Z.card = 2 * ρ - 1 ∧
      (δ : ℤ) ∣ ((∑ y ∈ Z, y : ℕ) : ℤ) -
        (((2 * ρ - 1 : ℕ) : ℤ) * e₁ + r * ((e₂ : ℤ) - e₁)) := by
    intro r hr
    exact mix (n := 2 * ρ - 1) (r := r) hm₁ hm₂ hne (by omega) (by omega) (by omega)
  choose! Zf hZf using key
  have hdiff : ∀ r, r < 2 * ρ → ∀ r', r' < 2 * ρ →
      (δ : ℤ) ∣ ((∑ y ∈ Zf r, y : ℕ) : ℤ) - ((∑ y ∈ Zf r', y : ℕ) : ℤ) → r = r' := by
    intro r hr r' hr' hd
    refine incong hδ hK hr hr' ?_
    have h3 := dvd_sub (dvd_sub hd (hZf r hr).2.2) (dvd_neg.mpr (hZf r' hr').2.2)
    have e : ((r : ℤ) - r') * ((e₂ : ℤ) - e₁) =
        ((∑ y ∈ Zf r, y : ℕ) : ℤ) - ((∑ y ∈ Zf r', y : ℕ) : ℤ) -
          (((∑ y ∈ Zf r, y : ℕ) : ℤ) -
            (((2 * ρ - 1 : ℕ) : ℤ) * e₁ + r * ((e₂ : ℤ) - e₁))) -
          -(((∑ y ∈ Zf r', y : ℕ) : ℤ) -
            (((2 * ρ - 1 : ℕ) : ℤ) * e₁ + r' * ((e₂ : ℤ) - e₁))) := by ring
    rw [e]
    exact h3
  have hinj : Set.InjOn Zf ((Finset.range (2 * ρ) : Finset ℕ) : Set ℕ) := by
    intro r hr r' hr' hrr
    rw [Finset.mem_coe, Finset.mem_range] at hr hr'
    refine hdiff r hr r' hr' ?_
    rw [hrr, sub_self]
    exact dvd_zero _
  have hcard : ((Finset.range (2 * ρ)).image Zf).card = 2 * ρ := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hunion : (((Finset.range (2 * ρ)).image Zf).biUnion id).card ≤ 2 * (2 * ρ - 1) := by
    have hsub : ((Finset.range (2 * ρ)).image Zf).biUnion id ⊆ F₁ ∪ F₂ := by
      refine Finset.biUnion_subset.mpr fun Z hZ => ?_
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hZ
      exact (hZf r (Finset.mem_range.mp hr)).1
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le F₁ F₂)
    omega
  have hlt := count (z := 2 * ρ - 1) hδ hC habs hs hN ((Finset.range (2 * ρ)).image Zf) (by
      intro Z hZ
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hZ
      have h := hZf r (Finset.mem_range.mp hr)
      exact ⟨h.1.trans (Finset.union_subset hF₁A hF₂A), h.2.1⟩) (by
      intro Z hZ Z' hZ' hneZ i _ heq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hZ
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hZ'
      apply hneZ
      have hrr : r = r' := by
        refine hdiff r (Finset.mem_range.mp hr) r' (Finset.mem_range.mp hr') ⟨(i : ℤ), ?_⟩
        rw [heq]
        push_cast
        ring
      rw [hrr]) (by omega) (by omega)
  omega

end OMA.DF.Count

namespace OMA.DF.Heavy

/-- Residue of a sum of elements of one class.  (Copied from the lead's file `ord/L1_L2.lean`.) -/
lemma sum_mod {q β : ℕ} {T : Finset ℕ} (h : ∀ x ∈ T, x % q = β % q) :
    (∑ x ∈ T, x) % q = (T.card * β) % q := by
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, ← Nat.mul_mod_mod,
    Nat.mod_mod]
  rw [Nat.mul_mod_mod]

lemma sum_dvd {δ c : ℕ} {T : Finset ℕ} (h : ∀ x ∈ T, x % δ = c % δ) (hT : δ ∣ T.card) :
    δ ∣ ∑ x ∈ T, x := by
  apply Nat.dvd_of_mod_eq_zero
  rw [sum_mod h]
  exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hT c)

lemma sum_ge {T : Finset ℕ} {p : ℕ} (h : ∀ x ∈ T, p ≤ x) : T.card * p ≤ ∑ x ∈ T, x := by
  have h1 := Finset.card_nsmul_le_sum T (fun x => x) p h
  rw [smul_eq_mul] at h1
  exact h1

lemma sum_le {T : Finset ℕ} {q : ℕ} (h : ∀ x ∈ T, x ≤ q) : ∑ x ∈ T, x ≤ T.card * q := by
  have h1 := Finset.sum_le_card_nsmul T (fun x => x) q h
  rw [smul_eq_mul] at h1
  exact h1

/-- L1 (separation).  (Adapted from `sep` of the lead's file `ord/L1_L2.lean`.) -/
lemma sep {A C : Finset ℕ} {t x0 δ J : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hC : C ⊆ A) (ht : 1 ≤ t)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    {X Y : Finset ℕ} (hX : X ⊆ A \ C) (hY : Y ⊆ A \ C) (hne : X.card ≠ Y.card)
    {i : ℕ} (hi : i < J) : ∑ x ∈ Y, x ≠ ∑ x ∈ X, x + i * δ := by
  intro heq
  obtain ⟨T, hTC, hTc, hTs⟩ := habs i hi
  obtain ⟨T', hT'C, hT'c, hT's⟩ := habs 0 (by omega)
  have hd : ∀ {T Z : Finset ℕ}, T ⊆ C → Z ⊆ A \ C → Disjoint T Z := by
    intro T Z h1 h2
    exact Finset.disjoint_left.mpr fun z hz hz2 => (Finset.mem_sdiff.mp (h2 hz2)).2 (h1 hz)
  have hsubA : ∀ {Z : Finset ℕ}, Z ⊆ A \ C → Z ⊆ A := fun h z hz => (Finset.mem_sdiff.mp (h hz)).1
  refine hadm (T ∪ X) (T' ∪ Y) (Finset.union_subset (hTC.trans hC) (hsubA hX))
    (Finset.union_subset (hT'C.trans hC) (hsubA hY)) ?_ ?_ ?_ ?_
  · rw [Finset.card_union_of_disjoint (hd hTC hX)]; omega
  · rw [Finset.card_union_of_disjoint (hd hT'C hY)]; omega
  · rw [Finset.card_union_of_disjoint (hd hTC hX), Finset.card_union_of_disjoint (hd hT'C hY)]
    omega
  · rw [Finset.sum_union (hd hTC hX), Finset.sum_union (hd hT'C hY), hTs, hT's, heq]
    ring

/-- L1 for two sums that are multiples of `δ`: the sums differ by at least `J * δ`. -/
lemma sep_mult {A C : Finset ℕ} {t x0 δ J : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hC : C ⊆ A) (ht : 1 ≤ t)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    {X Y : Finset ℕ} (hX : X ⊆ A \ C) (hY : Y ⊆ A \ C) (hne : X.card ≠ Y.card)
    (hdX : δ ∣ ∑ x ∈ X, x) (hdY : δ ∣ ∑ x ∈ Y, x) :
    ∑ x ∈ X, x + J * δ ≤ ∑ x ∈ Y, x ∨ ∑ x ∈ Y, x + J * δ ≤ ∑ x ∈ X, x := by
  obtain ⟨u, hu⟩ := hdX
  obtain ⟨v, hv⟩ := hdY
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  rw [hu, hv] at hc1 hc2
  rcases le_total u v with h | h
  · obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le h
    have hi : w < J := by
      by_contra hge
      rw [not_lt] at hge
      have h1 := Nat.mul_le_mul_left δ hge
      rw [hw] at hc1
      nlinarith
    refine sep hadm hC ht habs hX hY hne hi ?_
    rw [hu, hv, hw]
    ring
  · obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le h
    have hi : w < J := by
      by_contra hge
      rw [not_lt] at hge
      have h1 := Nat.mul_le_mul_left δ hge
      rw [hw] at hc2
      nlinarith
    refine sep hadm hC ht habs hY hX (Ne.symm hne) hi ?_
    rw [hu, hv, hw]
    ring

/-- Dirichlet's approximation theorem in integer form. -/
lemma dirichlet (p₁ p₂ M : ℕ) (hp : 0 < p₁) (hM : 0 < M) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ M ∧ ((M : ℤ) + 1) * |b * p₂ - a * p₁| ≤ p₁ := by
  obtain ⟨j, k, hk0, hkM, hle⟩ := Real.exists_int_int_abs_mul_sub_le ((p₂ : ℝ) / p₁) hM
  refine ⟨j, k, by omega, hkM, ?_⟩
  have hp' : (0 : ℝ) < p₁ := by exact_mod_cast hp
  have hM' : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have e : (k : ℝ) * p₂ - j * p₁ = (k * ((p₂ : ℝ) / p₁) - j) * p₁ := by
    field_simp
  have h1 : ((M : ℝ) + 1) * |(k : ℝ) * p₂ - j * p₁| ≤ p₁ := by
    rw [e, abs_mul, abs_of_pos hp']
    have h2 : |(k : ℝ) * ((p₂ : ℝ) / p₁) - j| * p₁ ≤ 1 / ((M : ℝ) + 1) * p₁ :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hp')
    have h3 : ((M : ℝ) + 1) * (|(k : ℝ) * ((p₂ : ℝ) / p₁) - j| * p₁) ≤
        ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1) * p₁) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hM')
    have h4 : ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1) * p₁) = p₁ := by
      field_simp
    linarith
  exact_mod_cast h1

/-- WP-B (L6, localization); copy of `OMA.DF.Localize.localize` in `WPB.lean`. -/
theorem localize {A C : Finset ℕ} {t x0 δ J N ρ η : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card → T₁.card ≠ T₂.card →
      ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hC : C ⊆ A) (hAN : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) (ht : 1 ≤ t) (hδ : 1 ≤ δ)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    (hρ : 1 ≤ ρ) (hN : N ≤ ρ * J) (hη : 8 * (16 * ρ * ρ + 1) * η ≤ J)
    {F₁ F₂ : Finset ℕ} (hF₁ : F₁ ⊆ A \ C) (hF₂ : F₂ ⊆ A \ C) {c₁ c₂ : ℕ}
    (h₁ : ∀ y ∈ F₁, y % δ = c₁ % δ) (h₂ : ∀ y ∈ F₂, y % δ = c₂ % δ)
    (hd₁ : ∀ y ∈ F₁, ∀ y' ∈ F₁, y' ≤ y + η) (hd₂ : ∀ y ∈ F₂, ∀ y' ∈ F₂, y' ≤ y + η)
    (hn₁ : δ * (16 * ρ * ρ + 1) ≤ F₁.card) (hn₂ : δ * (16 * ρ * ρ + 1) ≤ F₂.card) :
    ∀ y₁ ∈ F₁, ∀ y₂ ∈ F₂, 8 * y₂ ≤ 8 * y₁ + J + 8 * η := by
  intro y₁ hy₁ y₂ hy₂
  classical
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = 16 * ρ * ρ + 1 := ⟨_, rfl⟩
  rw [← hAm] at hη hn₁ hn₂
  have hAm17 : 17 ≤ Am := by
    rw [hAm]
    nlinarith [Nat.mul_le_mul hρ hρ]
  have hne₁ : F₁.Nonempty := ⟨y₁, hy₁⟩
  have hne₂ : F₂.Nonempty := ⟨y₂, hy₂⟩
  obtain ⟨p₁, hp₁e⟩ : ∃ p, p = F₁.min' hne₁ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂e⟩ : ∃ p, p = F₂.min' hne₂ := ⟨_, rfl⟩
  have hp₁F : p₁ ∈ F₁ := by rw [hp₁e]; exact Finset.min'_mem _ _
  have hp₂F : p₂ ∈ F₂ := by rw [hp₂e]; exact Finset.min'_mem _ _
  have hp₁min : ∀ y ∈ F₁, p₁ ≤ y := by
    intro y hy
    have h := Finset.min'_le F₁ y hy
    rw [← hp₁e] at h
    exact h
  have hp₂min : ∀ y ∈ F₂, p₂ ≤ y := by
    intro y hy
    have h := Finset.min'_le F₂ y hy
    rw [← hp₂e] at h
    exact h
  have hy1 := hp₁min y₁ hy₁
  have hy2 := hd₂ p₂ hp₂F y₂ hy₂
  by_cases hle : p₂ ≤ p₁
  · omega
  rw [not_le] at hle
  suffices hs : 8 * p₂ ≤ 8 * p₁ + J by omega
  by_contra hfar
  rw [not_le] at hfar
  have hp₁pos := (hAN p₁ (Finset.mem_sdiff.1 (hF₁ hp₁F)).1).1
  have hp₁N := (hAN p₁ (Finset.mem_sdiff.1 (hF₁ hp₁F)).1).2
  have hp₂N := (hAN p₂ (Finset.mem_sdiff.1 (hF₂ hp₂F)).1).2
  have hJ1 : 1 ≤ J := by
    by_contra h0
    have hJ0 : J = 0 := by omega
    rw [hJ0, Nat.mul_zero] at hN
    omega
  have hη17 : 8 * 17 * η ≤ J :=
    le_trans (Nat.mul_le_mul_right η (Nat.mul_le_mul_left 8 hAm17)) hη
  have hAmη : 8 * (Am * η) ≤ J := by
    rw [← Nat.mul_assoc]
    exact hη
  have hδAm : δ ≤ δ * Am := Nat.le_mul_of_pos_right δ (by omega)
  -- (i) the position of `F₁` is at least `J - η`
  have hF1 : J ≤ p₁ + η := by
    obtain ⟨Y, hYF, hYc⟩ := Finset.exists_subset_card_eq (le_trans hδAm hn₁)
    have hdY : δ ∣ ∑ x ∈ Y, x :=
      sum_dvd (fun x hx => h₁ x (hYF hx)) (by rw [hYc])
    have hsep := sep_mult hadm hC ht habs (X := ∅) (Y := Y) (Finset.empty_subset _)
      (hYF.trans hF₁) (by rw [Finset.card_empty, hYc]; omega)
      (by rw [Finset.sum_empty]; exact dvd_zero _) hdY
    have hub : ∑ x ∈ Y, x ≤ Y.card * (p₁ + η) :=
      sum_le (fun x hx => hd₁ p₁ hp₁F x (hYF hx))
    rw [hYc] at hub
    rw [Finset.sum_empty] at hsep
    have hJδ : 1 * 1 ≤ J * δ := Nat.mul_le_mul hJ1 hδ
    rcases hsep with h | h
    · have h3 : δ * J ≤ δ * (p₁ + η) := by
        rw [Nat.mul_comm δ J]
        linarith only [h, hub]
      exact Nat.le_of_mul_le_mul_left h3 (by omega)
    · exfalso
      have h5 : J * δ ≤ 0 := le_trans (Nat.le_add_left _ _) h
      omega
  -- (ii) Dirichlet
  obtain ⟨a, b, hb1, hbM, hD⟩ := dirichlet p₁ p₂ (8 * ρ) hp₁pos (by omega)
  obtain ⟨D, hDe⟩ : ∃ D : ℤ, D = b * p₂ - a * p₁ := ⟨_, rfl⟩
  rw [← hDe] at hD
  push_cast at hD hbM
  have habsD := abs_nonneg D
  have hDle := le_abs_self D
  have hDneg := neg_abs_le D
  have zρ : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have zp₁ : (1 : ℤ) ≤ p₁ := by exact_mod_cast hp₁pos
  have zle : (p₁ : ℤ) < p₂ := by exact_mod_cast hle
  have zp₁N : (p₁ : ℤ) ≤ N := by exact_mod_cast hp₁N
  have zp₂N : (p₂ : ℤ) ≤ N := by exact_mod_cast hp₂N
  have zN : (N : ℤ) ≤ ρ * J := by exact_mod_cast hN
  have zF1 : (J : ℤ) ≤ p₁ + η := by exact_mod_cast hF1
  have zη : 8 * 17 * (η : ℤ) ≤ J := by exact_mod_cast hη17
  have zAmη : 8 * ((Am : ℤ) * η) ≤ J := by exact_mod_cast hAmη
  have zfar : 8 * (p₁ : ℤ) + J < 8 * p₂ := by exact_mod_cast hfar
  have zAm : (Am : ℤ) = 16 * ρ * ρ + 1 := by exact_mod_cast hAm
  have zJ : (1 : ℤ) ≤ J := by exact_mod_cast hJ1
  have zη0 : (0 : ℤ) ≤ η := by positivity
  have zδ : (0 : ℤ) < δ := by exact_mod_cast hδ
  have hρD : (0 : ℤ) ≤ ρ * |D| := mul_nonneg (by linarith only [zρ]) habsD
  have hF3 : 8 * |D| ≤ J := by
    have h1 : (ρ : ℤ) * (8 * |D|) ≤ ρ * J := by linarith only [hD, zp₁N, zN, habsD, hρD]
    exact le_of_mul_le_mul_left h1 (by linarith only [zρ])
  have hF4 : b ≤ a := by
    by_contra hlt
    rw [not_le] at hlt
    have ha1 : a ≤ b - 1 := by omega
    have hp0 : (0 : ℤ) ≤ p₁ := by linarith only [zp₁]
    have hb0 : (0 : ℤ) ≤ b := by linarith only [hb1]
    have hp12 : (p₁ : ℤ) ≤ p₂ := le_of_lt zle
    have h1 : a * (p₁ : ℤ) ≤ (b - 1) * p₁ := mul_le_mul_of_nonneg_right ha1 hp0
    have h2 : b * (p₁ : ℤ) ≤ b * p₂ := mul_le_mul_of_nonneg_left hp12 hb0
    have h3 : (p₁ : ℤ) ≤ D := by rw [hDe]; linarith only [h1, h2]
    have h3' : (p₁ : ℤ) ≤ |D| := le_trans h3 hDle
    have hρ0 : (0 : ℤ) ≤ ρ := by linarith only [zρ]
    have h4 : (ρ : ℤ) * p₁ ≤ ρ * |D| := mul_le_mul_of_nonneg_left h3' hρ0
    have h5 : (1 : ℤ) * 1 ≤ ρ * p₁ := mul_le_mul zρ zp₁ (by norm_num) hρ0
    linarith only [hD, h4, h5, h3', habsD]
  have hF5 : a ≤ Am := by
    have h1 : b * (p₂ : ℤ) ≤ (8 * ρ) * N := mul_le_mul hbM zp₂N (by positivity) (by positivity)
    have h2 : (ρ : ℤ) * N ≤ ρ * (ρ * J) := mul_le_mul_of_nonneg_left zN (by positivity)
    have h3 : (J : ℤ) ≤ 2 * p₁ := by linarith only [zF1, zη, zη0]
    have h4 : (ρ : ℤ) * ρ * J ≤ ρ * ρ * (2 * p₁) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : |D| ≤ p₁ := by linarith only [hD, hρD, habsD]
    have h6 : a * (p₁ : ℤ) ≤ Am * p₁ := by
      rw [zAm]
      have h7 : a * (p₁ : ℤ) = b * p₂ - D := by rw [hDe]; ring
      linarith only [h7, hDneg, h1, h2, h4, h5]
    exact le_of_mul_le_mul_right h6 (by linarith only [zp₁])
  by_cases hab : a = b
  · -- (iv)
    have h1 : D = b * ((p₂ : ℤ) - p₁) := by rw [hDe, hab]; ring
    have h2 : (p₂ : ℤ) - p₁ ≤ D := by
      rw [h1]
      have h3 : 1 * ((p₂ : ℤ) - p₁) ≤ b * ((p₂ : ℤ) - p₁) :=
        mul_le_mul_of_nonneg_right hb1 (by linarith only [zle])
      linarith only [h3]
    linarith only [h2, hDle, hF3, zfar]
  · -- (iii)
    have hlt : b < a := lt_of_le_of_ne hF4 (Ne.symm hab)
    obtain ⟨a', ha'⟩ : ∃ a' : ℕ, (a' : ℤ) = a := ⟨a.toNat, Int.toNat_of_nonneg (by linarith only [hb1, hF4])⟩
    obtain ⟨b', hb'⟩ : ∃ b' : ℕ, (b' : ℤ) = b := ⟨b.toNat, Int.toNat_of_nonneg (by linarith only [hb1])⟩
    have ha'Am : a' ≤ Am := by
      have h : (a' : ℤ) ≤ Am := by rw [ha']; exact hF5
      exact_mod_cast h
    have hb'Am : b' ≤ Am := by
      have h : (b' : ℤ) ≤ Am := by rw [hb']; linarith only [hlt, hF5]
      exact_mod_cast h
    obtain ⟨X, hXF, hXc⟩ :=
      Finset.exists_subset_card_eq (le_trans (Nat.mul_le_mul_left δ ha'Am) hn₁)
    obtain ⟨Y, hYF, hYc⟩ :=
      Finset.exists_subset_card_eq (le_trans (Nat.mul_le_mul_left δ hb'Am) hn₂)
    have hdX : δ ∣ ∑ x ∈ X, x :=
      sum_dvd (fun x hx => h₁ x (hXF hx)) (by rw [hXc]; exact Dvd.intro _ rfl)
    have hdY : δ ∣ ∑ x ∈ Y, x :=
      sum_dvd (fun x hx => h₂ x (hYF hx)) (by rw [hYc]; exact Dvd.intro _ rfl)
    have hne : X.card ≠ Y.card := by
      rw [hXc, hYc]
      intro h
      have h1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < δ) h
      apply hab
      rw [← ha', ← hb', h1]
    have hbη : b * (η : ℤ) ≤ Am * η := mul_le_mul_of_nonneg_right (by linarith only [hlt, hF5]) zη0
    have haη : a * (η : ℤ) ≤ Am * η := mul_le_mul_of_nonneg_right hF5 zη0
    rcases sep_mult hadm hC ht habs (hXF.trans hF₁) (hYF.trans hF₂) hne hdX hdY with h | h
    · have hlb : X.card * p₁ ≤ ∑ x ∈ X, x := sum_ge (fun x hx => hp₁min x (hXF hx))
      have hub : ∑ x ∈ Y, x ≤ Y.card * (p₂ + η) :=
        sum_le (fun x hx => hd₂ p₂ hp₂F x (hYF hx))
      rw [hXc] at hlb
      rw [hYc] at hub
      have hnat : δ * a' * p₁ + J * δ ≤ δ * b' * (p₂ + η) := by linarith only [h, hlb, hub]
      have hz : (δ : ℤ) * a * p₁ + J * δ ≤ δ * b * (p₂ + η) := by
        rw [← ha', ← hb']
        exact_mod_cast hnat
      have hz2 : (δ : ℤ) * J ≤ δ * (D + b * η) := by
        rw [hDe]
        linarith only [hz]
      have hz3 : (J : ℤ) ≤ D + b * η := le_of_mul_le_mul_left hz2 zδ
      linarith only [hz3, hbη, zAmη, hF3, hDle, zJ]
    · have hlb : Y.card * p₂ ≤ ∑ x ∈ Y, x := sum_ge (fun x hx => hp₂min x (hYF hx))
      have hub : ∑ x ∈ X, x ≤ X.card * (p₁ + η) :=
        sum_le (fun x hx => hd₁ p₁ hp₁F x (hXF hx))
      rw [hYc] at hlb
      rw [hXc] at hub
      have hnat : δ * b' * p₂ + J * δ ≤ δ * a' * (p₁ + η) := by linarith only [h, hlb, hub]
      have hz : (δ : ℤ) * b * p₂ + J * δ ≤ δ * a * (p₁ + η) := by
        rw [← ha', ← hb']
        exact_mod_cast hnat
      have hz2 : (δ : ℤ) * J ≤ δ * (-D + a * η) := by
        rw [hDe]
        linarith only [hz]
      have hz3 : (J : ℤ) ≤ -D + a * η := le_of_mul_le_mul_left hz2 zδ
      linarith only [hz3, haη, zAmη, hF3, hDneg, zJ]

/-- **WP-D (L6', heavy elements).**  `H` is the set of the elements of `A \ C` whose fiber
(same cell `y / η`, same class `y % δ`) has at least `δ * (16 * ρ * ρ + 1)` elements. -/
theorem heavy {A C : Finset ℕ} {t x0 δ J N ρ η nc : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card → T₁.card ≠ T₂.card →
      ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hC : C ⊆ A) (hAN : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) (ht : 1 ≤ t) (hδ : 1 ≤ δ)
    (habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C ∧ T.card = t ∧ ∑ x ∈ T, x = x0 + j * δ)
    (hρ : 1 ≤ ρ) (hN : N ≤ ρ * J) (hη1 : 1 ≤ η) (hη : 8 * (16 * ρ * ρ + 1) * η ≤ J)
    (hnc : ((A \ C).image (· % δ)).card ≤ nc) :
    ∃ H : Finset ℕ, H ⊆ A \ C ∧ (∀ y ∈ H, ∀ y' ∈ H, 4 * y' ≤ 4 * y + J) ∧
      ((A \ C) \ H).card ≤ (N / η + 1) * nc * (δ * (16 * ρ * ρ + 1)) := by
  classical
  obtain ⟨fib, hfib⟩ : ∃ fib : ℕ → Finset ℕ, ∀ y, fib y =
      (A \ C).filter (fun y' => y' / η = y / η ∧ y' % δ = y % δ) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H =
      (A \ C).filter (fun y => δ * (16 * ρ * ρ + 1) ≤ (fib y).card) := ⟨_, rfl⟩
  have hfibsub : ∀ y, fib y ⊆ A \ C := by
    intro y
    rw [hfib]
    exact Finset.filter_subset _ _
  have hfibcl : ∀ y, ∀ z ∈ fib y, z % δ = y % δ := by
    intro y z hz
    rw [hfib] at hz
    exact (Finset.mem_filter.1 hz).2.2
  have hfibself : ∀ y ∈ A \ C, y ∈ fib y := by
    intro y hy
    rw [hfib]
    exact Finset.mem_filter.2 ⟨hy, rfl, rfl⟩
  have hfibdiam : ∀ y, ∀ z ∈ fib y, ∀ z' ∈ fib y, z' ≤ z + η := by
    intro y z hz z' hz'
    rw [hfib] at hz hz'
    have h1 := (Finset.mem_filter.1 hz).2.1
    have h2 := (Finset.mem_filter.1 hz').2.1
    have e1 := Nat.div_add_mod z η
    have e2 := Nat.div_add_mod z' η
    rw [h1] at e1
    rw [h2] at e2
    have hm := Nat.mod_lt z' (show 0 < η by omega)
    have hz0 := Nat.zero_le (z % η)
    linarith only [e1, e2, hm, hz0]
  refine ⟨H, by rw [hH]; exact Finset.filter_subset _ _, ?_, ?_⟩
  · intro y hy y' hy'
    rw [hH] at hy hy'
    obtain ⟨hyD, hyc⟩ := Finset.mem_filter.1 hy
    obtain ⟨hy'D, hy'c⟩ := Finset.mem_filter.1 hy'
    have hloc := localize hadm hC hAN ht hδ habs hρ hN hη (hfibsub y) (hfibsub y')
      (hfibcl y) (hfibcl y') (hfibdiam y) (hfibdiam y') hyc hy'c
      y (hfibself y hyD) y' (hfibself y' hy'D)
    have h8 : 8 * 1 * η ≤ 8 * (16 * ρ * ρ + 1) * η :=
      Nat.mul_le_mul_right η (Nat.mul_le_mul_left 8 (Nat.le_add_left 1 _))
    omega
  · obtain ⟨g, hg⟩ : ∃ g : ℕ × ℕ → Finset ℕ, ∀ p, g p =
        ((A \ C) \ H).filter (fun y => y / η = p.1 ∧ y % δ = p.2) := ⟨_, fun _ => rfl⟩
    have hsub : (A \ C) \ H ⊆
        (Finset.range (N / η + 1) ×ˢ (A \ C).image (· % δ)).biUnion g := by
      intro y hy
      have hyD := (Finset.mem_sdiff.1 hy).1
      have hyN := (hAN y (Finset.mem_sdiff.1 hyD).1).2
      refine Finset.mem_biUnion.2 ⟨(y / η, y % δ), Finset.mem_product.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hyN)),
          Finset.mem_image_of_mem _ hyD⟩, ?_⟩
      rw [hg]
      exact Finset.mem_filter.2 ⟨hy, rfl, rfl⟩
    have hgcard : ∀ p ∈ Finset.range (N / η + 1) ×ˢ (A \ C).image (· % δ),
        (g p).card ≤ δ * (16 * ρ * ρ + 1) := by
      intro p _
      by_cases hemp : g p = ∅
      · rw [hemp, Finset.card_empty]
        exact Nat.zero_le _
      · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hemp
        rw [hg] at hy
        obtain ⟨hyDH, hy1, hy2⟩ := Finset.mem_filter.1 hy
        obtain ⟨hyD, hyH⟩ := Finset.mem_sdiff.1 hyDH
        have hlt : (fib y).card < δ * (16 * ρ * ρ + 1) := by
          by_contra h
          apply hyH
          rw [hH]
          exact Finset.mem_filter.2 ⟨hyD, not_lt.1 h⟩
        have hgsub : g p ⊆ fib y := by
          intro z hz
          rw [hg] at hz
          obtain ⟨hzDH, hz1, hz2⟩ := Finset.mem_filter.1 hz
          rw [hfib]
          exact Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hzDH).1, by rw [hz1, hy1],
            by rw [hz2, hy2]⟩
        exact le_trans (Finset.card_le_card hgsub) (le_of_lt hlt)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le_card_mul _ g _ hgcard
    have h3 : (Finset.range (N / η + 1) ×ˢ (A \ C).image (· % δ)).card ≤ (N / η + 1) * nc := by
      rw [Finset.card_product, Finset.card_range]
      exact Nat.mul_le_mul_left _ hnc
    exact le_trans h1 (le_trans h2 (Nat.mul_le_mul_right _ h3))

end OMA.DF.Heavy


set_option maxRecDepth 8000 in
/-- L8: the ordering property from the first absorber and a small sum set. -/
lemma ord_final {A : Finset ℕ} {N : ℕ}
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hAN : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) (h4N : 4 * N ≤ A.card * (A.card + 3))
    (hk : 10 ^ 210 ≤ A.card)
    {C₀ : Finset ℕ} {x0 δ₀ : ℕ} (hC₀ : C₀ ⊆ A) (hC₀c : C₀.card = A.card / (4 * 10 ^ 6))
    (hδ₀ : 1 ≤ δ₀)
    (habs₀ : ∀ j : ℕ, 10 ^ 8 * j < C₀.card ^ 2 →
      ∃ T : Finset ℕ, T ⊆ C₀ ∧ T.card = 2 * (C₀.card / 10 ^ 6) ∧ ∑ x ∈ T, x = x0 + j * δ₀)
    {s : ℕ} (hs1 : A.card ≤ 10 * s) (hs2 : 4 * s ≤ 3 * A.card)
    (hs : ((A.powersetCard s).image (fun T => ∑ x ∈ T, x)).card < 2 * N) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ B : Finset ℕ, B ⊆ A ∧ 10 ^ 6 * (A.card - B.card) ≤ A.card ∧
      (∀ a ∈ B, ∀ b ∈ B, a % q = b % q) ∧
      ∀ κ : ℕ, 1 ≤ κ → κ + q ≤ B.card → ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ B → T₂ ⊆ B →
        T₁.card = κ → T₂.card = κ + q → ∑ x ∈ T₁, x < ∑ x ∈ T₂, x := by
  obtain ⟨L, hL⟩ : ∃ L, L = C₀.card := ⟨_, rfl⟩
  rw [← hL] at hC₀c habs₀
  have hL1 : 4 * 10 ^ 6 * L ≤ A.card := by rw [hC₀c]; exact Nat.mul_div_le _ _
  have hL2 : A.card < 4 * 10 ^ 6 * (L + 1) := by
    rw [hC₀c]; exact Nat.lt_mul_div_succ _ (by norm_num)
  have hL3 : 10 ^ 203 ≤ L := by omega
  obtain ⟨J, hJdef⟩ : ∃ J, J = L ^ 2 / 10 ^ 8 := ⟨_, rfl⟩
  have hLL : 10 ^ 203 * 10 ^ 203 ≤ L * L := Nat.mul_le_mul hL3 hL3
  have hsqL : L ^ 2 = L * L := sq L
  have hJ1 : 10 ^ 8 * J ≤ L * L := by rw [hJdef, hsqL]; exact Nat.mul_div_le _ _
  have hJ2 : L * L < 10 ^ 8 * (J + 1) := by
    rw [hJdef, hsqL]; exact Nat.lt_mul_div_succ _ (by norm_num)
  have hJbig : 10 ^ 397 ≤ J := by omega
  have habs : ∀ j, j < J → ∃ T : Finset ℕ, T ⊆ C₀ ∧ T.card = 2 * (L / 10 ^ 6) ∧
      ∑ x ∈ T, x = x0 + j * δ₀ := fun j hj => habs₀ j (by rw [hsqL]; omega)
  have hk5 : A.card ≤ 4010000 * L := by omega
  have hk6 : A.card + 3 ≤ 4020000 * L := by omega
  have hmul : A.card * (A.card + 3) ≤ (4010000 * L) * (4020000 * L) := Nat.mul_le_mul hk5 hk6
  have hmul2 : (4010000 * L) * (4020000 * L) = 16120200000000 * (L * L) := by ring
  have hNJ : N ≤ 10 ^ 21 * J := by omega
  obtain ⟨η, hηdef⟩ : ∃ η, η = J / (8 * (16 * 10 ^ 21 * 10 ^ 21 + 1)) := ⟨_, rfl⟩
  have hη : 8 * (16 * 10 ^ 21 * 10 ^ 21 + 1) * η ≤ J := by rw [hηdef]; exact Nat.mul_div_le _ _
  have hη2 : J < 8 * (16 * 10 ^ 21 * 10 ^ 21 + 1) * (η + 1) := by
    rw [hηdef]; exact Nat.lt_mul_div_succ _ (by norm_num)
  have hη1 : 1 ≤ η := by omega
  have hX : N / η ≤ 16 * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1) := by
    apply Nat.div_le_of_le_mul
    omega
  have hK3 : (N / η + 1) * (2 * 10 ^ 21) *
      (4 * (2 * 10 ^ 21) * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1)) + 2 * 10 ^ 21 ≤ 10 ^ 175 := by
    have h1 : (N / η + 1) * (2 * 10 ^ 21) *
        (4 * (2 * 10 ^ 21) * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1)) ≤
        (16 * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1) + 1) * (2 * 10 ^ 21) *
        (4 * (2 * 10 ^ 21) * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h2 : (16 * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1) + 1) * (2 * 10 ^ 21) *
        (4 * (2 * 10 ^ 21) * 10 ^ 21 * (16 * 10 ^ 21 * 10 ^ 21 + 1)) + 2 * 10 ^ 21 ≤ 10 ^ 175 := by
      norm_num
    exact le_trans (Nat.add_le_add_right h1 _) h2
  have hlog := log_small (Q := 10 ^ 40) (k := A.card)
    (le_trans (by norm_num) hk) (le_trans (by norm_num) hk)
  -- the modulus of the first absorber is at most k^3
  have hlogδ : Nat.log 2 δ₀ < 3 * (Nat.log 2 A.card + 1) := by
    obtain ⟨T, hTC, hTc, hTs⟩ := habs (J - 1) (by omega)
    have h1 : ∑ x ∈ T, x ≤ T.card * N := by
      calc ∑ x ∈ T, x ≤ ∑ _x ∈ T, N := Finset.sum_le_sum fun x hx => (hAN x (hC₀ (hTC hx))).2
        _ = T.card * N := by simp
    have h2 : δ₀ ≤ (J - 1) * δ₀ := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : T.card ≤ A.card := Finset.card_le_card (hTC.trans hC₀)
    have h4 : N ≤ A.card * A.card := by
      have : A.card * (A.card + 3) ≤ A.card * (4 * A.card) := Nat.mul_le_mul_left _ (by omega)
      have e : A.card * (4 * A.card) = 4 * (A.card * A.card) := by ring
      omega
    have h5 : δ₀ ≤ A.card ^ 3 := by
      calc δ₀ ≤ ∑ x ∈ T, x := by omega
        _ ≤ T.card * N := h1
        _ ≤ A.card * (A.card * A.card) := Nat.mul_le_mul h3 h4
        _ = A.card ^ 3 := by ring
    obtain ⟨m, hm⟩ : ∃ m, m = Nat.log 2 A.card + 1 := ⟨_, rfl⟩
    have e1 : A.card < 2 ^ m := by rw [hm]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have e2 : A.card ^ 3 < (2 ^ m) ^ 3 := Nat.pow_lt_pow_left e1 (by norm_num)
    have e3 : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, Nat.mul_comm]
    rw [e3] at e2
    rw [← hm]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hδ₀) (lt_of_le_of_lt h5 e2)
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Nat.log 2 A.card + 1 := ⟨_, rfl⟩
  rw [← hlam] at hlogδ
  have hnum : (2 : ℕ) * 10 ^ 21 * 10 ^ 175 = 2 * 10 ^ 196 := by norm_num
  obtain ⟨q, hq, B, hBA, hBc, hBcl, hBord⟩ := main_lemma (A := A) (N := N) (s := s)
    (ρ := 10 ^ 21) (η := η) (Jst := J) (nst := 10 ^ 175)
    (Cmax := L + 12 * 10 ^ 21 * lam) (tmax := 2 * (L / 10 ^ 6) + 6 * 10 ^ 21 * lam)
    hadm hAN (by norm_num) hNJ (by omega) hη1 hη hK3 (by omega) (by omega) (by omega)
    (fun C t x0 δ J hC hδ habs hN ht1 hbig =>
      OMA.DF.Count.few_classes hC habs hs hN hδ ht1 hbig)
    (fun C t x0 δ J e₁ e₂ hC hδ habs hN htK hbig he₁ he₂ hne hn₁ hn₂ =>
      OMA.DF.Count.small_order hC habs hs hN hδ htK hbig he₁ he₂ hne hn₁ hn₂)
    (fun C t x0 δ J E₁ E₂ e₁ e₂ h o w hδ habs hE₁ hE₂ h₁ h₂ hne hh ho hc₁ hc₂ hw hJ =>
      OMA.DF.Merge.merge hδ habs hE₁ hE₂ h₁ h₂ hne hh ho hc₁ hc₂ hw hJ)
    (fun δ J h o w ho hh1 hw hJ ho2 =>
      OMA.DF.Merge.merge_size (by rw [ho]; exact Nat.mul_pos (by omega) hh1) ho hw hJ ho2)
    (fun C t x0 δ J nc hC ht hδ habs hN hη' hnc =>
      OMA.DF.Heavy.heavy hadm hC hAN ht hδ habs (by norm_num) hN hη1 hη' hnc)
    δ₀ C₀ (2 * (L / 10 ^ 6)) x0 J hC₀ (by omega) hδ₀ habs le_rfl (by omega) (by omega)
  refine ⟨q, hq, B, hBA, ?_, hBcl, fun κ hκ _ T₁ T₂ h1 h2 c1 c2 => hBord κ hκ T₁ T₂ h1 h2 c1 c2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hBA
  omega

theorem main : H1 → H2 → OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1.H1 := by
  intro hAbs hSS
  obtain ⟨N₁, hN₁⟩ := hAbs
  obtain ⟨N₂, hN₂⟩ := hSS
  refine ⟨max (max N₁ N₂) (10 ^ 210 * 10 ^ 210), fun N hN A hA hadm h4N => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 10 ^ 210 * 10 ^ 210 ≤ N := le_trans (le_max_right _ _) hN
  have hk : 10 ^ 210 ≤ A.card := by
    have hQ : 4 ≤ 10 ^ 210 := by norm_num
    generalize (10 : ℕ) ^ 210 = Q at hN3 hQ ⊢
    by_contra hc
    have h1 : A.card * (A.card + 3) ≤ Q * (2 * Q) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : Q * (2 * Q) = 2 * (Q * Q) := by ring
    have h3 : 1 ≤ Q * Q := Nat.mul_pos (by omega) (by omega)
    omega
  have hA' : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N := fun x hx => hA (Finset.mem_coe.mpr hx)
  have hadmF : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x := by
    intro T₁ T₂ h1 h2 c1 c2 hne heq
    exact Set.disjoint_left.mp (hadm (show T₁.card ∈ Set.Ici 1 from c1)
      (show T₂.card ∈ Set.Ici 1 from c2) hne)
      ⟨T₁, Finset.coe_subset.mpr h1, rfl, rfl⟩ ⟨T₂, Finset.coe_subset.mpr h2, rfl, heq.symm⟩
  obtain ⟨C, hC, x0, δ, hCc, hδ, habs⟩ := hN₁ N hN1 A hA hadm h4N
  obtain ⟨s, hs1, hs2, hs⟩ := hN₂ N hN2 A hA hadm h4N
  exact ord_final hadmF hA' h4N hk hC hCc hδ habs hs1 hs2 hs

end OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1_H1_R1
