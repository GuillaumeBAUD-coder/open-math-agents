import OMAReductions.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1

/-!
# Proof of `WilfNumericalSemigroupConjecture.wilf_numerical_semigroup_conjecture.R1.H1`

Eliahou's theorem (J. Eur. Math. Soc. 2018): Wilf's conjecture `c(S) ≤ e(S) * |S ∩ [0, c(S))|`
holds for every numerical semigroup `S` with `2 * m(S) < c(S) ≤ 3 * m(S)`.

We give a completely elementary, self-contained proof without graded algebras or Macaulay's theorem:
1. `sumset_two_to_three`: for any finite `A, B, C ⊆ ℕ` with `C ⊆ 3A` and
   `(∀ u v w ∈ A, u + v + w ∈ C → u + v ∈ B)`, if `|B| = x(x-1)/2` (`x ≥ 1`) then
   `|C| ≤ (x+1)x(x-1)/6`. Proved by direct induction on `|A|` removing `a = max A`.
2. Reduction to profile `(k, 0)` (Eliahou Prop. 6.2) via `W₀(S) = (p₁ + p₂)|L| - 3 d₃ + ρ`.
3. Profile `(k, 0)` bound (Eliahou Thm. 6.4) via `sumset_two_to_three` on `(X₁, X₂, C)`.
-/

-- Step WilfNumericalSemigroupConjecture.wilf_numerical_semigroup_conjecture.R1.H1: hypothesis H1 of reduction WilfNumericalSemigroupConjecture.wilf_numerical_semigroup_conjecture.R1
-- Credit: @LiJiaHua1024

namespace OMA.WilfH1

open Finset AddSubmonoid WilfNumericalSemigroupConjecture

/-- Pairwise sum of a `Finset ℕ` via `Sym2`. -/
private lemma card_filter_add_neg {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1; ext x; simp only [mem_union, mem_filter]; tauto

private lemma profile_k0_arith (k x1 d2 d3' x2 r32 c3 r3 : ℕ) (x : ℝ)
    (hk1 : 1 ≤ k) (hx1_eq : x1 + 1 = k) (hd2_eq : d2 = k + x2)
    (hd3'_eq : d3' = d2 + r3) (hr3_eq : r32 + c3 = r3)
    (hsum2 : 2 * (x2 + r32) ≤ x1 * (x1 + 1))
    (hx_ge1 : (1 : ℝ) ≤ x) (hx2_eq : (x2 : ℝ) = x * (x - 1) / 2)
    (hc3_le : (c3 : ℝ) ≤ (x + 1) * x * (x - 1) / 6) :
    3 * d3' ≤ k * (1 + k + d2) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hx1R : (x1 : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hx1_eq
  have hd2R : (d2 : ℝ) = (k : ℝ) + (x2 : ℝ) := by exact_mod_cast hd2_eq
  have hd3'R : (d3' : ℝ) = (d2 : ℝ) + (r3 : ℝ) := by exact_mod_cast hd3'_eq
  have hr3R : (r32 : ℝ) + (c3 : ℝ) = (r3 : ℝ) := by exact_mod_cast hr3_eq
  have hsum2R : 2 * ((x2 : ℝ) + (r32 : ℝ)) ≤ (x1 : ℝ) * ((x1 : ℝ) + 1) := by exact_mod_cast hsum2
  have hx_le_k : x ≤ (k : ℝ) := by
    have hr32nn : (0 : ℝ) ≤ (r32 : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hdiff : x * (x - 1) / 2 ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  have hnonneg : 0 ≤ ((k : ℝ) - x) * (x * (x - 1) / 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hfinalR : (3 * d3' : ℝ) ≤ (k : ℝ) * (1 + (k : ℝ) + (d2 : ℝ)) := by nlinarith
  exact_mod_cast hfinalR

private lemma wilf_combine_arith (c m ρ p1 p2 p3 d2 d3 d3' p2p2 L : ℕ)
    (hL_eq : L = 1 + p1 + p2 + d2) (hL_ge3 : 3 ≤ L)
    (hI3 : p3 + d3 = m) (hρ : c + ρ = 3 * m) (hd2_ge : p1 ≤ d2)
    (hD3_le : d3 ≤ d3' + p1 * p2 + p2p2)
    (hP2_rho : p2p2 ≤ ρ) (hP2_sq : 2 * p2p2 ≤ p2 * (p2 + 1))
    (hk0 : 3 * d3' ≤ p1 * (1 + p1 + d2)) :
    c ≤ (p1 + p2 + p3) * L := by
  have hP2_trick : 3 * p2p2 ≤ p2 * (p2 + 1) + ρ := by omega
  have hmul : p2 * p1 ≤ p2 * d2 := Nat.mul_le_mul_left _ hd2_ge
  have hW0 : 3 * d3 ≤ (p1 + p2) * L + ρ := by
    rw [hL_eq]; nlinarith
  have hP3mul : 3 * p3 ≤ p3 * L := by
    rw [Nat.mul_comm 3 p3]; exact Nat.mul_le_mul_left p3 hL_ge3
  nlinarith

private def sym2Add : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨fun a b => a + b, fun a b => Nat.add_comm a b⟩

private lemma card_image_sym2Add_le (S : Finset ℕ) :
    2 * (S.sym2.image sym2Add).card ≤ S.card * (S.card + 1) := by
  have h1 : (S.sym2.image sym2Add).card ≤ S.sym2.card := Finset.card_image_le
  rw [Finset.card_sym2, Nat.choose_two_right] at h1
  have h2 := Nat.mul_div_le ((S.card + 1) * (S.card + 1 - 1)) 2
  simp only [Nat.add_sub_cancel] at h1 h2
  have hcomm : S.card * (S.card + 1) = (S.card + 1) * S.card := Nat.mul_comm _ _
  omega

/-- Elementary sumset `2 → 3` inequality (avoiding Macaulay's theorem and graded algebras):
if `C ⊆ 3A` and every triple sum in `C` has all pairwise sums in `B`, then
`|B| = x(x - 1)/2` (`x ≥ 1`) implies `|C| ≤ (x + 1)x(x - 1)/6`. -/
private lemma sumset_two_to_three :
    ∀ n : ℕ, ∀ (A B C : Finset ℕ), A.card = n →
      (∀ c ∈ C, ∃ u ∈ A, ∃ v ∈ A, ∃ w ∈ A, c = u + v + w) →
      (∀ u ∈ A, ∀ v ∈ A, ∀ w ∈ A, u + v + w ∈ C → u + v ∈ B) →
      ∀ x : ℝ, 1 ≤ x → (B.card : ℝ) = x * (x - 1) / 2 →
        (C.card : ℝ) ≤ (x + 1) * x * (x - 1) / 6 := by
  intro n
  induction n with
  | zero =>
    intro A B C hA hC _ x hx _
    have hA0 : A = ∅ := Finset.card_eq_zero.mp hA
    have hC0 : C = ∅ := by
      ext c; simp only [notMem_empty, iff_false]; intro hc
      obtain ⟨u, hu, _⟩ := hC c hc
      rw [hA0] at hu; exact notMem_empty u hu
    rw [hC0, card_empty, Nat.cast_zero]
    have : 0 ≤ (x + 1) * x * (x - 1) := by nlinarith
    linarith
  | succ n ih =>
    intro A B C hA hC hclosed x hx hBx
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    let a : ℕ := A.max' hAne
    have haA : a ∈ A := Finset.max'_mem A hAne
    let A' : Finset ℕ := A.erase a
    have hA'card : A'.card = n := by rw [card_erase_of_mem haA, hA]; omega
    have hA'lt : ∀ u ∈ A', u < a := fun u hu =>
      lt_of_le_of_ne (Finset.le_max' A u (erase_subset _ _ hu)) (mem_erase.mp hu).1
    let S2 : Finset ℕ := (A' ×ˢ A').image (fun p => p.1 + p.2)
    let S3 : Finset ℕ := ((A' ×ˢ A') ×ˢ A').image (fun p => p.1.1 + p.1.2 + p.2)
    let B0 : Finset ℕ := B.filter (· ∈ S2)
    let B1 : Finset ℕ := B.filter (· ∉ S2)
    let C0 : Finset ℕ := C.filter (· ∈ S3)
    let C1 : Finset ℕ := C.filter (· ∉ S3)
    have hBsplit : B0.card + B1.card = B.card :=
      card_filter_add_neg B (· ∈ S2)
    have hCsplit : C0.card + C1.card = C.card :=
      card_filter_add_neg C (· ∈ S3)
    have hC0 : ∀ c ∈ C0, ∃ u ∈ A', ∃ v ∈ A', ∃ w ∈ A', c = u + v + w := by
      intro c hc
      obtain ⟨_, hcS3⟩ := mem_filter.mp hc
      obtain ⟨⟨⟨u, v⟩, w⟩, hmem, rfl⟩ := mem_image.mp hcS3
      rw [mem_product, mem_product] at hmem
      exact ⟨u, hmem.1.1, v, hmem.1.2, w, hmem.2, rfl⟩
    have hclosed0 : ∀ u ∈ A', ∀ v ∈ A', ∀ w ∈ A', u + v + w ∈ C0 → u + v ∈ B0 := by
      intro u hu v hv w hw hc0
      refine mem_filter.mpr ⟨hclosed u (erase_subset _ _ hu) v (erase_subset _ _ hv)
        w (erase_subset _ _ hw) (mem_filter.mp hc0).1, ?_⟩
      exact mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hu, hv⟩, rfl⟩
    -- Define y ≥ 1 with y(y - 1)/2 = B0.card
    let y : ℝ := (1 + Real.sqrt (1 + 8 * (B0.card : ℝ))) / 2
    have hD1 : (1 : ℝ) ≤ 1 + 8 * (B0.card : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) B0.card]
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + 8 * (B0.card : ℝ)) :=
      Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt hD1)
    have hy1 : (1 : ℝ) ≤ y := by dsimp only [y]; linarith
    have hB0y : (B0.card : ℝ) = y * (y - 1) / 2 := by
      have hsq : Real.sqrt (1 + 8 * (B0.card : ℝ)) ^ 2 = 1 + 8 * (B0.card : ℝ) :=
        Real.sq_sqrt (by linarith)
      dsimp only [y]
      nlinarith
    have hC0_bound : (C0.card : ℝ) ≤ (y + 1) * y * (y - 1) / 6 :=
      ih A' B0 C0 hA'card hC0 hclosed0 y hy1 hB0y
    -- Bound C1.card ≤ B.card
    have hC1_le_B : C1.card ≤ B.card := by
      have hsub : C1 ⊆ B.image (a + ·) := by
        intro c hc
        obtain ⟨hcC, hcS3⟩ := mem_filter.mp hc
        obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := hC c hcC
        by_cases hua : u = a
        · subst hua
          have hvw : v + w ∈ B := by
            have := hclosed v hv w hw a haA (by rwa [show v + w + a = a + v + w by omega])
            exact this
          exact mem_image.mpr ⟨v + w, hvw, by omega⟩
        · by_cases hva : v = a
          · subst hva
            have huw : u + w ∈ B := by
              have := hclosed u hu w hw a haA (by rwa [show u + w + a = u + a + w by omega])
              exact this
            exact mem_image.mpr ⟨u + w, huw, by omega⟩
          · by_cases hwa : w = a
            · subst hwa
              have huv : u + v ∈ B := hclosed u hu v hv a haA hcC
              exact mem_image.mpr ⟨u + v, huv, by omega⟩
            · exfalso; apply hcS3
              refine mem_image.mpr ⟨((u, v), w), ?_, rfl⟩
              exact mem_product.mpr ⟨mem_product.mpr ⟨mem_erase.mpr ⟨hua, hu⟩,
                mem_erase.mpr ⟨hva, hv⟩⟩, mem_erase.mpr ⟨hwa, hw⟩⟩
      exact (card_le_card hsub).trans card_image_le
    -- Bound 2 * C1.card ≤ B1.card * (B1.card + 1) via A1 := {u ∈ A | a + u ∈ B1}
    let A1 : Finset ℕ := A.filter (fun u => a + u ∈ B1)
    have hA1_le_B1 : A1.card ≤ B1.card := by
      have hsub : A1.image (a + ·) ⊆ B1 := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := mem_image.mp hz
        exact (mem_filter.mp hu).2
      have hinj : Function.Injective (a + ·) := fun _ _ h => Nat.add_left_cancel h
      calc A1.card = (A1.image (a + ·)).card := (card_image_of_injective A1 hinj).symm
        _ ≤ B1.card := card_le_card hsub
    have haa_notS2 : a + a ∉ S2 := by
      intro h
      obtain ⟨⟨p, q⟩, hpq, heq⟩ := mem_image.mp h
      rw [mem_product] at hpq
      have hp := hA'lt p hpq.1
      have hq := hA'lt q hpq.2
      omega
    have hC1_sub_A1 : C1 ⊆ (A1.sym2.image sym2Add).image (a + ·) := by
      intro c hc
      obtain ⟨hcC, hcS3⟩ := mem_filter.mp hc
      obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := hC c hcC
      -- First express c = a + x1 + x2 with x1, x2 ∈ A
      have hrep : ∃ x1 ∈ A, ∃ x2 ∈ A, u + v + w = a + x1 + x2 := by
        by_cases hua : u = a
        · subst hua; exact ⟨v, hv, w, hw, rfl⟩
        · by_cases hva : v = a
          · subst hva; exact ⟨u, hu, w, hw, by omega⟩
          · by_cases hwa : w = a
            · subst hwa; exact ⟨u, hu, v, hv, by omega⟩
            · exfalso; apply hcS3
              exact mem_image.mpr ⟨((u, v), w), mem_product.mpr ⟨mem_product.mpr
                ⟨mem_erase.mpr ⟨hua, hu⟩, mem_erase.mpr ⟨hva, hv⟩⟩, mem_erase.mpr ⟨hwa, hw⟩⟩, rfl⟩
      obtain ⟨x1, hx1, x2, hx2, hceq⟩ := hrep
      -- Helper for the case x1, x2 ∈ A'
      have hboth_A' : ∀ p ∈ A', ∀ q ∈ A', u + v + w = a + p + q →
          u + v + w ∈ (A1.sym2.image sym2Add).image (a + ·) := by
        intro p hp q hq heq
        have hpA : p ∈ A := erase_subset _ _ hp
        have hqA : q ∈ A := erase_subset _ _ hq
        have hapB : a + p ∈ B := hclosed a haA p hpA q hqA (heq ▸ hcC)
        have haqB : a + q ∈ B := hclosed a haA q hqA p hpA (by rwa [show a + q + p = u + v + w by omega])
        have hap_notS2 : a + p ∉ S2 := by
          intro hS2
          obtain ⟨⟨r, s⟩, hrs, heqrs⟩ := mem_image.mp hS2
          rw [mem_product] at hrs
          apply hcS3
          refine mem_image.mpr ⟨((r, s), q), mem_product.mpr ⟨mem_product.mpr hrs, hq⟩, ?_⟩
          dsimp only; omega
        have haq_notS2 : a + q ∉ S2 := by
          intro hS2
          obtain ⟨⟨r, s⟩, hrs, heqrs⟩ := mem_image.mp hS2
          rw [mem_product] at hrs
          apply hcS3
          refine mem_image.mpr ⟨((r, s), p), mem_product.mpr ⟨mem_product.mpr hrs, hp⟩, ?_⟩
          dsimp only; omega
        have hpA1 : p ∈ A1 := mem_filter.mpr ⟨hpA, mem_filter.mpr ⟨hapB, hap_notS2⟩⟩
        have hqA1 : q ∈ A1 := mem_filter.mpr ⟨hqA, mem_filter.mpr ⟨haqB, haq_notS2⟩⟩
        refine mem_image.mpr ⟨p + q, mem_image.mpr ⟨s(p, q), Finset.mk_mem_sym2_iff.mpr ⟨hpA1, hqA1⟩, rfl⟩, ?_⟩
        omega
      -- Helper for the case x1 = a, x2 ∈ A'
      have hone_a : ∀ p ∈ A', u + v + w = a + a + p →
          u + v + w ∈ (A1.sym2.image sym2Add).image (a + ·) := by
        intro p hp heq
        have hpA : p ∈ A := erase_subset _ _ hp
        have haaB : a + a ∈ B := hclosed a haA a haA p hpA (heq ▸ hcC)
        have haA1 : a ∈ A1 := mem_filter.mpr ⟨haA, mem_filter.mpr ⟨haaB, haa_notS2⟩⟩
        have hapB : a + p ∈ B := hclosed a haA p hpA a haA (by rwa [show a + p + a = u + v + w by omega])
        by_cases hapS2 : a + p ∈ S2
        · obtain ⟨⟨r, s⟩, hrs, heqrs⟩ := mem_image.mp hapS2
          rw [mem_product] at hrs
          exact hboth_A' r hrs.1 s hrs.2 (by omega)
        · have hpA1 : p ∈ A1 := mem_filter.mpr ⟨hpA, mem_filter.mpr ⟨hapB, hapS2⟩⟩
          refine mem_image.mpr ⟨a + p, mem_image.mpr ⟨s(a, p), Finset.mk_mem_sym2_iff.mpr ⟨haA1, hpA1⟩, rfl⟩, ?_⟩
          omega
      by_cases h1 : x1 = a
      · subst h1
        by_cases h2 : x2 = a
        · subst h2
          have haaB : a + a ∈ B := hclosed a haA a haA a haA (hceq ▸ hcC)
          have haA1 : a ∈ A1 := mem_filter.mpr ⟨haA, mem_filter.mpr ⟨haaB, haa_notS2⟩⟩
          refine mem_image.mpr ⟨a + a, mem_image.mpr ⟨s(a, a), Finset.mk_mem_sym2_iff.mpr ⟨haA1, haA1⟩, rfl⟩, ?_⟩
          omega
        · exact hone_a x2 (mem_erase.mpr ⟨h2, hx2⟩) hceq
      · by_cases h2 : x2 = a
        · subst h2
          exact hone_a x1 (mem_erase.mpr ⟨h1, hx1⟩) (by omega)
        · exact hboth_A' x1 (mem_erase.mpr ⟨h1, hx1⟩) x2 (mem_erase.mpr ⟨h2, hx2⟩) hceq
    have hC1_le_sq : 2 * C1.card ≤ B1.card * (B1.card + 1) := by
      have h1 : C1.card ≤ (A1.sym2.image sym2Add).card := (card_le_card hC1_sub_A1).trans card_image_le
      have h2 := card_image_sym2Add_le A1
      have h3 : A1.card * (A1.card + 1) ≤ B1.card * (B1.card + 1) :=
        Nat.mul_le_mul hA1_le_B1 (Nat.add_le_add_right hA1_le_B1 1)
      omega
    -- Combine bounds in ℝ
    have hBsplitR : (B0.card : ℝ) + (B1.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hBsplit
    have hCsplitR : (C0.card : ℝ) + (C1.card : ℝ) = (C.card : ℝ) := by exact_mod_cast hCsplit
    have hC1_le_BR : (C1.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hC1_le_B
    have hC1_le_sqR : 2 * (C1.card : ℝ) ≤ (B1.card : ℝ) * ((B1.card : ℝ) + 1) := by exact_mod_cast hC1_le_sq
    have hxy_eq : x * (x - 1) = y * (y - 1) + 2 * (B1.card : ℝ) := by linarith
    have hyx : y ≤ x := by
      have hB1nn : (0 : ℝ) ≤ (B1.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    by_cases hcase : (B1.card : ℝ) ≤ y
    · -- Case A: b1 ≤ y, so d := x - y ∈ [0, 1]
      set d : ℝ := x - y
      have hd0 : 0 ≤ d := by linarith
      have h2b1 : 2 * (B1.card : ℝ) = d * (2 * y + d - 1) := by
        have : x = y + d := by ring
        rw [this] at hxy_eq; linarith
      have hd1 : d ≤ 1 := by nlinarith
      have hpoly : 4 * ((x + 1) * x * (x - 1) - (y + 1) * y * (y - 1) -
          3 * (B1.card : ℝ) * ((B1.card : ℝ) + 1)) =
          d * (1 - d) * (3 * d ^ 2 + 12 * d * y - 7 * d + 12 * y ^ 2 - 12 * y + 2) := by
        have hx_eq : x = y + d := by ring
        have hb1_eq : (B1.card : ℝ) = d * (2 * y + d - 1) / 2 := by linarith
        rw [hx_eq, hb1_eq]; ring
      have hQpos : 0 ≤ 3 * d ^ 2 + 12 * d * y - 7 * d + 12 * y ^ 2 - 12 * y + 2 := by nlinarith
      have hprod : 0 ≤ d * (1 - d) * (3 * d ^ 2 + 12 * d * y - 7 * d + 12 * y ^ 2 - 12 * y + 2) :=
        mul_nonneg (mul_nonneg hd0 (by linarith)) hQpos
      linarith
    · -- Case B: y < b1, so y + 1 ≤ x and C1.card ≤ B.card = x(x - 1)/2
      push Not at hcase
      have hy1_le_x : y + 1 ≤ x := by nlinarith
      have hcub : (y + 1) * y * (y - 1) ≤ x * (x - 1) * (x - 2) := by
        have h1 : (y + 1) * y ≤ x * (x - 1) := by nlinarith
        have h2 : (y + 1) * y * (y - 1) ≤ x * (x - 1) * (y - 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        have h3 : x * (x - 1) * (y - 1) ≤ x * (x - 1) * (x - 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
        exact h2.trans h3
      linarith

end OMA.WilfH1

theorem OMA.solution :
    OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1.H1 := by
  open Finset AddSubmonoid WilfNumericalSemigroupConjecture OMA.WilfH1 in
  intro S hS h2m h3m
  classical
  set c := S.conductor with hc
  set m := sInf {x : ℕ | 0 < x ∧ x ∈ S} with hm
  have hcpos : 0 < c := by omega
  have hmem : ∀ y, c ≤ y → y ∈ S := fun y hy => hS.mem_of_conductor_le hy
  have hne : {x : ℕ | 0 < x ∧ x ∈ S}.Nonempty := ⟨c, hcpos, hmem c le_rfl⟩
  obtain ⟨hmpos, hmS⟩ : 0 < m ∧ m ∈ S := Nat.sInf_mem hne
  have hmin : ∀ x, 0 < x → x ∈ S → m ≤ x := fun x hx hxS => Nat.sInf_le ⟨hx, hxS⟩
  set ρ := 3 * m - c with hρ
  -- Intervals I1 = [c - 2m, c - m), I2 = [c - m, c), I3 = [c, c + m)
  let I1 : Finset ℕ := Finset.Ico (c - 2 * m) (c - m)
  let I2 : Finset ℕ := Finset.Ico (c - m) c
  let I3 : Finset ℕ := Finset.Ico c (c + m)
  -- Primitive elements G (definition matches embeddingDim)
  let G : Set ℕ := {x : ℕ | 0 < x ∧ x ∈ S ∧
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ x = a + b}
  have hGfin : G.Finite := by
    apply (Set.finite_Iio (c + m)).subset
    rintro x ⟨hx, hxS, hnot⟩
    simp only [Set.mem_Iio]
    by_contra hge
    exact hnot ⟨m, x - m, hmpos, by omega, hmS, hmem _ (by omega), by omega⟩
  -- Define P1, P2, D2, P3, D3
  let P1 : Finset ℕ := I1.filter (· ∈ S)
  let S2 : Finset ℕ := I2.filter (· ∈ S)
  let D2 : Finset ℕ := S2.filter (fun x => ∃ a ∈ P1, ∃ b ∈ P1, x = a + b)
  let P2 : Finset ℕ := S2.filter (fun x => ¬ ∃ a ∈ P1, ∃ b ∈ P1, x = a + b)
  let D3 : Finset ℕ := I3.filter (fun z => ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ z = a + b)
  let P3 : Finset ℕ := I3.filter (fun z => ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ z = a + b)
  have hP1_bounds : ∀ x ∈ P1, m ≤ x ∧ x < c - m ∧ x ∈ S := by
    intro x hx
    obtain ⟨hxI1, hxS⟩ := mem_filter.mp hx
    rw [mem_Ico] at hxI1
    have hxpos : 0 < x := by omega
    exact ⟨hmin x hxpos hxS, hxI1.2, hxS⟩
  have hmP1 : m ∈ P1 := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hmS⟩
  have h2mS2 : 2 * m ∈ S2 := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩,
    by rw [two_mul]; exact S.add_mem hmS hmS⟩
  -- Every element of P1 is primitive
  have hP1_G : ∀ x ∈ P1, x ∈ G := by
    intro x hx
    obtain ⟨hxm, hxlt, hxS⟩ := hP1_bounds x hx
    refine ⟨by omega, hxS, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, rfl⟩
    have := hmin a ha haS; have := hmin b hb hbS; omega
  -- Every element of P2 is primitive
  have hP2_G : ∀ x ∈ P2, x ∈ G := by
    intro x hx
    obtain ⟨hxS2, hnot⟩ := mem_filter.mp hx
    obtain ⟨hxI2, hxS⟩ := mem_filter.mp hxS2
    rw [mem_Ico] at hxI2
    refine ⟨by omega, hxS, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, rfl⟩
    have hma := hmin a ha haS; have hmb := hmin b hb hbS
    apply hnot
    exact ⟨a, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, haS⟩,
      b, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hbS⟩, rfl⟩
  -- Every element of P3 is primitive
  have hP3_G : ∀ z ∈ P3, z ∈ G := by
    intro z hz
    obtain ⟨hzI3, hnot⟩ := mem_filter.mp hz
    rw [mem_Ico] at hzI3
    exact ⟨by omega, hmem z hzI3.1, hnot⟩
  -- Disjointness of P1, P2, P3
  have hdisj12 : Disjoint P1 P2 := Finset.disjoint_left.mpr fun x h1 h2 => by
    have h1' := (mem_Ico.mp (mem_filter.mp h1).1).2
    have h2' := (mem_Ico.mp (mem_filter.mp (mem_filter.mp h2).1).1).1
    omega
  have hdisj13 : Disjoint P1 P3 := Finset.disjoint_left.mpr fun x h1 h3 => by
    have h1' := (mem_Ico.mp (mem_filter.mp h1).1).2
    have h3' := (mem_Ico.mp (mem_filter.mp h3).1).1
    omega
  have hdisj23 : Disjoint P2 P3 := Finset.disjoint_left.mpr fun x h2 h3 => by
    have h2' := (mem_Ico.mp (mem_filter.mp (mem_filter.mp h2).1).1).2
    have h3' := (mem_Ico.mp (mem_filter.mp h3).1).1
    omega
  have he_ge : P1.card + P2.card + P3.card ≤ S.embeddingDim := by
    have hsub : ((P1 ∪ P2 ∪ P3 : Finset ℕ) : Set ℕ) ⊆ G := by
      intro x hx
      simp only [coe_union, Set.mem_union, mem_coe] at hx
      rcases hx with (hx | hx) | hx
      · exact hP1_G x hx
      · exact hP2_G x hx
      · exact hP3_G x hx
    have hcard := Set.ncard_le_ncard hsub hGfin
    rw [Set.ncard_coe_finset, card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩),
      card_union_of_disjoint hdisj12] at hcard
    simpa [embeddingDim, G] using hcard
  -- Cardinality relations: P3 + D3 = m, P2 + D2 = S2, sporadicCount S = 1 + P1 + P2 + D2
  have hI3_split : P3.card + D3.card = m := by
    have h : D3.card + P3.card = I3.card := card_filter_add_neg I3
      (fun z => ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ z = a + b)
    have hI3c : I3.card = m := by simp [I3]
    omega
  have hS2_split : D2.card + P2.card = S2.card :=
    card_filter_add_neg S2 (fun x => ∃ a ∈ P1, ∃ b ∈ P1, x = a + b)
  have hL_eq : sporadicCount S = 1 + P1.card + P2.card + D2.card := by
    unfold sporadicCount
    have hset : (Finset.range c).filter (· ∈ S) = insert 0 (P1 ∪ S2) := by
      ext x
      simp only [mem_filter, mem_range, mem_insert, mem_union, P1, S2, I1, I2, mem_Ico]
      constructor
      · rintro ⟨hxc, hxS⟩
        rcases Nat.eq_zero_or_pos x with rfl | hxpos
        · exact Or.inl rfl
        · have hxm := hmin x hxpos hxS
          by_cases hlt : x < c - m
          · exact Or.inr (Or.inl ⟨⟨by omega, hlt⟩, hxS⟩)
          · exact Or.inr (Or.inr ⟨⟨by omega, hxc⟩, hxS⟩)
      · rintro (rfl | ⟨⟨_, _⟩, hxS⟩ | ⟨⟨_, _⟩, hxS⟩)
        · exact ⟨hcpos, S.zero_mem⟩
        · exact ⟨by omega, hxS⟩
        · exact ⟨by omega, hxS⟩
    have h0_not : (0 : ℕ) ∉ P1 ∪ S2 := by
      simp only [mem_union, P1, S2, I1, I2, mem_filter, mem_Ico]
      rintro (⟨⟨_, _⟩, _⟩ | ⟨⟨_, _⟩, _⟩) <;> omega
    have hdisj_P1_S2 : Disjoint P1 S2 := Finset.disjoint_left.mpr fun x h1 h2 => by
      have := (mem_Ico.mp (mem_filter.mp h1).1).2
      have := (mem_Ico.mp (mem_filter.mp h2).1).1
      omega
    rw [← hc, hset, card_insert_of_notMem h0_not, card_union_of_disjoint hdisj_P1_S2]
    omega
  have hL_ge3 : 3 ≤ sporadicCount S := by
    have h1 : 1 ≤ P1.card := card_pos.mpr ⟨m, hmP1⟩
    have h2 : 1 ≤ S2.card := card_pos.mpr ⟨2 * m, h2mS2⟩
    omega
  -- Show m + P1 ⊆ D2, so P1.card ≤ D2.card
  have hmP1_sub_D2 : P1.image (m + ·) ⊆ D2 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hxm, hxlt, hxS⟩ := hP1_bounds x hx
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, S.add_mem hmS hxS⟩,
      ⟨m, hmP1, x, hx, rfl⟩⟩
  have hd2_ge_p1 : P1.card ≤ D2.card := by
    have hinj : Function.Injective (m + ·) := fun _ _ h => Nat.add_left_cancel h
    calc P1.card = (P1.image (m + ·)).card := (card_image_of_injective P1 hinj).symm
      _ ≤ D2.card := card_le_card hmP1_sub_D2
  -- Define D3' = I3 ∩ ((P1 + P1) ∪ (P1 + D2))
  let D3' : Finset ℕ := I3.filter (fun z =>
    (∃ a ∈ P1, ∃ b ∈ P1, z = a + b) ∨ (∃ a ∈ P1, ∃ b ∈ D2, z = a + b))
  let P1P2 : Finset ℕ := (P1 ×ˢ P2).image (fun p => p.1 + p.2)
  let P2P2 : Finset ℕ := (P2.sym2.image sym2Add).filter (· ∈ I3)
  -- Cover D3 ⊆ D3' ∪ P1P2 ∪ P2P2
  have hD3_cover : D3 ⊆ D3' ∪ P1P2 ∪ P2P2 := by
    intro z hz
    obtain ⟨hzI3, a, b, ha, hb, haS, hbS, rfl⟩ := mem_filter.mp hz
    have hI3b := mem_Ico.mp hzI3
    have hma := hmin a ha haS; have hmb := hmin b hb hbS
    have ha_lt : a < c := by omega
    have hb_lt : b < c := by omega
    -- Classify a and b into P1, P2, D2
    have hclass : ∀ x, 0 < x → x < c → x ∈ S → x ∈ P1 ∨ x ∈ P2 ∨ x ∈ D2 := by
      intro x hx hxc hxS
      have hxm := hmin x hx hxS
      by_cases hlt : x < c - m
      · exact Or.inl (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hlt⟩, hxS⟩)
      · have hxS2 : x ∈ S2 := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hxc⟩, hxS⟩
        by_cases hdec : ∃ u ∈ P1, ∃ v ∈ P1, x = u + v
        · exact Or.inr (Or.inr (mem_filter.mpr ⟨hxS2, hdec⟩))
        · exact Or.inr (Or.inl (mem_filter.mpr ⟨hxS2, hdec⟩))
    have hno_D2_S2 : ∀ u ∈ D2, ∀ v ∈ S2, u + v ≠ a + b → True := fun _ _ _ _ _ => trivial
    -- Helper: u ∈ D2 and v ∈ S2 implies u + v ≥ c + m (impossible for a + b < c + m)
    have hD2_add_S2_ge : ∀ u ∈ D2, ∀ v ∈ S2, c + m ≤ u + v := by
      intro u hu v hv
      obtain ⟨_, p, hp, q, hq, rfl⟩ := mem_filter.mp hu
      have hpm := (hP1_bounds p hp).1; have hqm := (hP1_bounds q hq).1
      have hv1 := (mem_Ico.mp (mem_filter.mp hv).1).1
      omega
    rcases hclass a ha ha_lt haS with ha1 | ha2 | ha3 <;>
    rcases hclass b hb hb_lt hbS with hb1 | hb2 | hb3
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hzI3, Or.inl ⟨a, ha1, b, hb1, rfl⟩⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(a, b), mem_product.mpr ⟨ha1, hb2⟩, rfl⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hzI3, Or.inr ⟨a, ha1, b, hb3, rfl⟩⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(b, a), mem_product.mpr ⟨hb1, ha2⟩, by omega⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨ha2, hb2⟩, rfl⟩, hzI3⟩)
    · exfalso; have := hD2_add_S2_ge b hb3 a (mem_filter.mp ha2).1; omega
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hzI3, Or.inr ⟨b, hb1, a, ha3, by omega⟩⟩))
    · exfalso; have := hD2_add_S2_ge a ha3 b (mem_filter.mp hb2).1; omega
    · exfalso; have := hD2_add_S2_ge a ha3 b (mem_filter.mp hb3).1; omega
  have hP1P2_card : P1P2.card ≤ P1.card * P2.card := by
    calc P1P2.card ≤ (P1 ×ˢ P2).card := card_image_le
      _ = P1.card * P2.card := card_product P1 P2
  have hP2P2_le_rho : P2P2.card ≤ ρ := by
    have hsub : P2P2 ⊆ Finset.Ico (c + m - ρ) (c + m) := by
      intro z hz
      obtain ⟨hzimg, hzI3⟩ := mem_filter.mp hz
      obtain ⟨e, he, rfl⟩ := mem_image.mp hzimg
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨hu, hv⟩ := Finset.mk_mem_sym2_iff.mp he
        have hu1 := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hu).1).1).1
        have hv1 := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hv).1).1).1
        have hz2 := (mem_Ico.mp hzI3).2
        have : sym2Add s(u, v) = u + v := rfl
        rw [this, mem_Ico]; omega
    calc P2P2.card ≤ (Finset.Ico (c + m - ρ) (c + m)).card := card_le_card hsub
      _ = ρ := by simp only [Nat.card_Ico]; omega
  have hP2P2_le_sq : 2 * P2P2.card ≤ P2.card * (P2.card + 1) := by
    have h1 : P2P2.card ≤ (P2.sym2.image sym2Add).card := card_filter_le _ _
    have h2 := card_image_sym2Add_le P2
    omega
  have hD3_le : D3.card ≤ D3'.card + P1.card * P2.card + P2P2.card := by
    calc D3.card ≤ (D3' ∪ P1P2 ∪ P2P2).card := card_le_card hD3_cover
      _ ≤ (D3' ∪ P1P2).card + P2P2.card := card_union_le _ _
      _ ≤ D3'.card + P1P2.card + P2P2.card := Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ D3'.card + P1.card * P2.card + P2P2.card := by omega
  -- Key Profile (k, 0) bound: 3 * D3'.card ≤ P1.card * (1 + P1.card + D2.card)
  have hprofile_k0 : 3 * D3'.card ≤ P1.card * (1 + P1.card + D2.card) := by
    let X1 : Finset ℕ := P1.erase m
    have hX1_card : X1.card + 1 = P1.card := by
      have h1 : X1.card = P1.card - 1 := card_erase_of_mem hmP1
      have h2 : 1 ≤ P1.card := card_pos.mpr ⟨m, hmP1⟩
      omega
    let X2 : Finset ℕ := D2 \ (P1.image (m + ·))
    have hD2_eq : D2.card = P1.card + X2.card := by
      have hcard : X2.card = D2.card - (P1.image (m + ·)).card := Finset.card_sdiff_of_subset hmP1_sub_D2
      have hinj : Function.Injective (m + ·) := fun _ _ h => Nat.add_left_cancel h
      rw [card_image_of_injective P1 hinj] at hcard
      have := hd2_ge_p1
      omega
    -- m + D2 ⊆ D3'
    have hmD2_sub : D2.image (m + ·) ⊆ D3' := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
      have hyI2 := mem_Ico.mp (mem_filter.mp (mem_filter.mp hy).1).1
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, Or.inr ⟨m, hmP1, y, hy, rfl⟩⟩
    let R3 : Finset ℕ := D3' \ (D2.image (m + ·))
    have hD3'_eq : D3'.card = D2.card + R3.card := by
      have hcard : R3.card = D3'.card - (D2.image (m + ·)).card := Finset.card_sdiff_of_subset hmD2_sub
      have hinj : Function.Injective (m + ·) := fun _ _ h => Nat.add_left_cancel h
      rw [card_image_of_injective D2 hinj] at hcard
      have hle : D2.card ≤ D3'.card := by
        calc D2.card = (D2.image (m + ·)).card := (card_image_of_injective D2 hinj).symm
          _ ≤ D3'.card := card_le_card hmD2_sub
      omega
    -- Split R3 into R32 = R3 ∩ (X1 + X1) and C3 = R3 \ (X1 + X1)
    let X1sum2 : Finset ℕ := X1.sym2.image sym2Add
    let R32 : Finset ℕ := R3.filter (· ∈ X1sum2)
    let C3 : Finset ℕ := R3.filter (· ∉ X1sum2)
    have hR3_split : R32.card + C3.card = R3.card :=
      card_filter_add_neg R3 (· ∈ X1sum2)
    -- X2 ⊆ X1sum2
    have hX2_sub : X2 ⊆ X1sum2 := by
      intro y hy
      obtain ⟨hyD2, hyNot⟩ := mem_sdiff.mp hy
      obtain ⟨_, a, ha, b, hb, rfl⟩ := mem_filter.mp hyD2
      have ham : a ≠ m := fun h => hyNot (mem_image.mpr ⟨b, hb, by omega⟩)
      have hbm : b ≠ m := fun h => hyNot (mem_image.mpr ⟨a, ha, by omega⟩)
      exact mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr
        ⟨mem_erase.mpr ⟨ham, ha⟩, mem_erase.mpr ⟨hbm, hb⟩⟩, rfl⟩
    -- X2 and R32 are disjoint subsets of X1sum2 (I2 vs I3)
    have hX2_R32_disj : Disjoint X2 R32 := Finset.disjoint_left.mpr fun z h1 h2 => by
      have h1' := (mem_Ico.mp (mem_filter.mp (mem_filter.mp (mem_sdiff.mp h1).1).1).1).2
      have h2' := (mem_Ico.mp (mem_filter.mp (mem_sdiff.mp (mem_filter.mp h2).1).1).1).1
      omega
    have hX2_R32_le : 2 * (X2.card + R32.card) ≤ X1.card * (X1.card + 1) := by
      have hsub : X2 ∪ R32 ⊆ X1sum2 := union_subset hX2_sub (fun z hz => (mem_filter.mp hz).2)
      have h1 : X2.card + R32.card ≤ X1sum2.card := by
        rw [← card_union_of_disjoint hX2_R32_disj]; exact card_le_card hsub
      have h2 := card_image_sym2Add_le X1
      dsimp only [X1sum2] at h1
      omega
    -- Every element of C3 is a triple sum in 3 * X1
    have hC3_3X1 : ∀ z ∈ C3, ∃ u ∈ X1, ∃ v ∈ X1, ∃ w ∈ X1, z = u + v + w := by
      intro z hz
      obtain ⟨hzR3, hzNot2⟩ := mem_filter.mp hz
      obtain ⟨hzD3', hzNotmD2⟩ := mem_sdiff.mp hzR3
      obtain ⟨hzI3, hcase⟩ := mem_filter.mp hzD3'
      have hzI3b := mem_Ico.mp hzI3
      rcases hcase with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, y, hy, rfl⟩
      · exfalso
        have ham : a ≠ m := fun h => by
          have := (hP1_bounds b hb).2; omega
        have hbm : b ≠ m := fun h => by
          have := (hP1_bounds a ha).2; omega
        exact hzNot2 (mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr
          ⟨mem_erase.mpr ⟨ham, ha⟩, mem_erase.mpr ⟨hbm, hb⟩⟩, rfl⟩)
      · have ham : a ≠ m := fun h => hzNotmD2 (mem_image.mpr ⟨y, hy, by omega⟩)
        have hyNotmP1 : y ∉ P1.image (m + ·) := by
          intro hym
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hym
          have habD2 : a + b ∈ D2 := by
            have haS := (hP1_bounds a ha).2.2; have hbS := (hP1_bounds b hb).2.2
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, S.add_mem haS hbS⟩,
              ⟨a, ha, b, hb, rfl⟩⟩
          exact hzNotmD2 (mem_image.mpr ⟨a + b, habD2, by omega⟩)
        have hyX2 : y ∈ X2 := mem_sdiff.mpr ⟨hy, hyNotmP1⟩
        obtain ⟨e, he, heq⟩ := mem_image.mp (hX2_sub hyX2)
        induction e using Sym2.ind with
        | _ u v =>
          obtain ⟨hu, hv⟩ := Finset.mk_mem_sym2_iff.mp he
          have : sym2Add s(u, v) = u + v := rfl
          rw [this] at heq
          exact ⟨a, mem_erase.mpr ⟨ham, ha⟩, u, hu, v, hv, by omega⟩
    -- Closedness: u, v, w ∈ X1 and u + v + w ∈ C3 → u + v ∈ X2
    have hC3_closed : ∀ u ∈ X1, ∀ v ∈ X1, ∀ w ∈ X1, u + v + w ∈ C3 → u + v ∈ X2 := by
      intro u hu v hv w hw hzc
      have huP1 : u ∈ P1 := erase_subset _ _ hu
      have hvP1 : v ∈ P1 := erase_subset _ _ hv
      have hwP1 : w ∈ P1 := erase_subset _ _ hw
      have hum := (hP1_bounds u huP1).1; have hvm := (hP1_bounds v hvP1).1
      have hwm := (hP1_bounds w hwP1).1; have hwm_ne := (mem_erase.mp hw).1
      have hzR3 := (mem_filter.mp hzc).1
      have hzD3' := (mem_sdiff.mp hzR3).1
      have hzNotmD2 := (mem_sdiff.mp hzR3).2
      have hzI3b := mem_Ico.mp (mem_filter.mp hzD3').1
      have huvD2 : u + v ∈ D2 := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩,
          S.add_mem (hP1_bounds u huP1).2.2 (hP1_bounds v hvP1).2.2⟩, ⟨u, huP1, v, hvP1, rfl⟩⟩
      refine mem_sdiff.mpr ⟨huvD2, ?_⟩
      intro huv_mP1
      obtain ⟨a, ha, heq⟩ := mem_image.mp huv_mP1
      have hawD2 : a + w ∈ D2 := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩,
          S.add_mem (hP1_bounds a ha).2.2 (hP1_bounds w hwP1).2.2⟩, ⟨a, ha, w, hwP1, rfl⟩⟩
      exact hzNotmD2 (mem_image.mpr ⟨a + w, hawD2, by omega⟩)
    -- Apply sumset_two_to_three to (X1, X2, C3)
    let x : ℝ := (1 + Real.sqrt (1 + 8 * (X2.card : ℝ))) / 2
    have hD1 : (1 : ℝ) ≤ 1 + 8 * (X2.card : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) X2.card]
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + 8 * (X2.card : ℝ)) :=
      Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt hD1)
    have hx1 : (1 : ℝ) ≤ x := by dsimp only [x]; linarith
    have hX2_eq : (X2.card : ℝ) = x * (x - 1) / 2 := by
      have hsq : Real.sqrt (1 + 8 * (X2.card : ℝ)) ^ 2 = 1 + 8 * (X2.card : ℝ) :=
        Real.sq_sqrt (by linarith)
      dsimp only [x]; nlinarith
    have hC3_le : (C3.card : ℝ) ≤ (x + 1) * x * (x - 1) / 6 :=
      sumset_two_to_three X1.card X1 X2 C3 rfl hC3_3X1 hC3_closed x hx1 hX2_eq
    exact profile_k0_arith P1.card X1.card D2.card D3'.card X2.card R32.card C3.card R3.card x
      (card_pos.mpr ⟨m, hmP1⟩) hX1_card hD2_eq hD3'_eq hR3_split hX2_R32_le hx1 hX2_eq hC3_le
  have hW : c ≤ (P1.card + P2.card + P3.card) * sporadicCount S :=
    wilf_combine_arith c m ρ P1.card P2.card P3.card D2.card D3.card D3'.card P2P2.card
      (sporadicCount S) hL_eq hL_ge3 hI3_split (by omega) hd2_ge_p1 hD3_le
      hP2P2_le_rho hP2P2_le_sq hprofile_k0
  exact hW.trans (Nat.mul_le_mul_right _ he_ge)
