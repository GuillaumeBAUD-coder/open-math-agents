import FormalConjectures.ErdosProblems.«588»
import Mathlib.Tactic

-- Problem: Erdős Problem 588 — three not isLittleO
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/588.lean:110 (declaration Erdos588.erdos_588.variants.three_not_isLittleO)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open EuclideanGeometry Filter Asymptotics

namespace OMA588

noncomputable def P (x : ℝ) : ℝ² := !₂[x, x ^ 3]

lemma P_zero (x : ℝ) : P x 0 = x := by simp [P]

lemma P_inj : Function.Injective P := by
  intro x y h
  have := congrArg (fun p : ℝ² => p 0) h
  simpa [P] using this

lemma mem_line {a b x : ℝ} (hab : a ≠ b) :
    P x ∈ line[ℝ, P a, P b] ↔ x = a ∨ x = b ∨ x = -(a + b) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, hr⟩
    have h0 := congrArg (fun p : ℝ² => p 0) hr
    have h1 := congrArg (fun p : ℝ² => p 1) hr
    simp [P, AffineMap.lineMap_apply] at h0 h1
    have : (x - a) * (x - b) * (x + a + b) = 0 := by
      linear_combination -h1 + (a^2 + a*b + b^2) * h0
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · intro h
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    refine ⟨(x - a) / (b - a), ?_⟩
    ext i
    fin_cases i
    · simp [P, AffineMap.lineMap_apply]
      field_simp; ring
    · simp [P, AffineMap.lineMap_apply]
      field_simp
      rcases h with rfl | rfl | rfl <;> ring


lemma lines_sub (k : ℕ) (S : Set ℝ²) :
    linesWithPointsFor k S ⊆
      (fun pq : ℝ² × ℝ² => line[ℝ, pq.1, pq.2]) '' (S ×ˢ S) := by
  rintro L ⟨⟨p, hp, q, hq, _, rfl⟩, _⟩
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

lemma lines_finite (k : ℕ) {S : Set ℝ²} (hS : S.Finite) :
    (linesWithPointsFor k S).Finite :=
  ((hS.prod hS).image _).subset (lines_sub k S)

lemma lines_le (k : ℕ) {S : Set ℝ²} (hS : S.Finite) :
    (linesWithPointsFor k S).ncard ≤ S.ncard * S.ncard := by
  calc (linesWithPointsFor k S).ncard
      ≤ ((fun pq : ℝ² × ℝ² => line[ℝ, pq.1, pq.2]) '' (S ×ˢ S)).ncard :=
        Set.ncard_le_ncard (lines_sub k S) ((hS.prod hS).image _)
    _ ≤ (S ×ˢ S).ncard := Set.ncard_image_le (hS.prod hS)
    _ = S.ncard * S.ncard := Set.ncard_prod

lemma bdd (n : ℕ) : BddAbove {((linesWithPointsFor 3 S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (3 + 1) S)} := by
  refine ⟨n * n, ?_⟩
  rintro _ ⟨S, hn, hS, _, rfl⟩
  rw [← hn]; exact lines_le 3 hS


noncomputable def S (M : ℕ) : Set ℝ² :=
  (fun z : ℤ => P z) '' Set.Icc (-(3 * M : ℤ)) (3 * M)

lemma S_finite (M : ℕ) : (S M).Finite := (Set.finite_Icc _ _).image _

lemma S_ncard (M : ℕ) : (S M).ncard = 6 * M + 1 := by
  rw [S, Set.ncard_image_of_injective _
    (show Function.Injective (fun z : ℤ => P z) from P_inj.comp Int.cast_injective),
    ← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
  omega

lemma S_noncol (M : ℕ) : NonCollinearFor (3 + 1) (S M) := by
  intro A hA hfin hcard hcol
  have h1 : 1 < A.ncard := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := (Set.one_lt_ncard_iff hfin).1 h1
  obtain ⟨a, -, rfl⟩ := hA hp
  obtain ⟨b, -, rfl⟩ := hA hq
  simp only at hp hq hpq
  have hab : (a : ℝ) ≠ b := fun h => hpq (by rw [h])
  have hsub : A ⊆ P '' {(a : ℝ), (b : ℝ), -((a : ℝ) + b)} := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := hA hy
    have := hcol.mem_affineSpan_of_mem_of_ne hp hq hy hpq
    rw [mem_line hab] at this
    exact ⟨z, by simpa using this, rfl⟩
  have : A.ncard ≤ 3 := by
    calc A.ncard ≤ (P '' {(a : ℝ), (b : ℝ), -((a : ℝ) + b)}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({(a : ℝ), (b : ℝ), -((a : ℝ) + b)} : Set ℝ).ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        have := Set.ncard_insert_le (b : ℝ) {-((a : ℝ) + b)}
        rw [Set.ncard_singleton] at this
        omega
  omega


lemma S_mem (M : ℕ) (z : ℤ) (h1 : -(3 * M : ℤ) ≤ z) (h2 : z ≤ 3 * M) : P z ∈ S M :=
  ⟨z, ⟨h1, h2⟩, rfl⟩

lemma S_lines (M : ℕ) : M * M ≤ (linesWithPointsFor 3 (S M)).ncard := by
  let D : Finset (ℤ × ℤ) := Finset.Icc 1 (M : ℤ) ×ˢ Finset.Icc ((M : ℤ) + 1) (2 * M)
  let f := fun ab : ℤ × ℤ => line[ℝ, P ab.1, P ab.2]
  have hD : D.card = M * M := by
    simp only [D, Finset.card_product, Int.card_Icc]
    have e1 : ((M : ℤ) + 1 - 1).toNat = M := by omega
    have e2 : (2 * (M : ℤ) + 1 - (M + 1)).toNat = M := by omega
    rw [e1, e2]
  have hmemD : ∀ a b : ℤ, (a, b) ∈ D → 1 ≤ a ∧ a ≤ M ∧ M + 1 ≤ b ∧ b ≤ 2 * M := by
    intro a b h
    simp only [D, Finset.mem_product, Finset.mem_Icc] at h
    omega
  have hsub : f '' (D : Set (ℤ × ℤ)) ⊆ linesWithPointsFor 3 (S M) := by
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha1, ha2, hb1, hb2⟩ := hmemD a b hab
    have hne : (a : ℝ) ≠ b := by
      intro h; have : a = b := by exact_mod_cast h
      omega
    have hc : ((-(a + b) : ℤ) : ℝ) = -((a : ℝ) + b) := by push_cast; ring
    have hne2 : (a : ℝ) ≠ -((a : ℝ) + b) := by
      rw [← hc]; intro h; have : a = -(a + b) := by exact_mod_cast h
      omega
    have hne3 : (b : ℝ) ≠ -((a : ℝ) + b) := by
      rw [← hc]; intro h; have : b = -(a + b) := by exact_mod_cast h
      omega
    have hPa : P a ∈ S M := S_mem M a (by omega) (by omega)
    have hPb : P b ∈ S M := S_mem M b (by omega) (by omega)
    have hPc : P (-((a : ℝ) + b)) ∈ S M := by
      rw [← hc]; exact S_mem M _ (by omega) (by omega)
    refine ⟨⟨P a, hPa, P b, hPb, P_inj.ne hne, rfl⟩, ?_⟩
    have heq : (↑(f (a, b)) ∩ S M : Set ℝ²) = {P a, P b, P (-((a : ℝ) + b))} := by
      ext y
      constructor
      · rintro ⟨hy, ⟨z, -, rfl⟩⟩
        have := (mem_line hne).1 hy
        rcases this with h | h | h <;> simp only at h ⊢ <;> rw [h] <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨(mem_line hne).2 (Or.inl rfl), hPa⟩
        · exact ⟨(mem_line hne).2 (Or.inr (Or.inl rfl)), hPb⟩
        · exact ⟨(mem_line hne).2 (Or.inr (Or.inr rfl)), hPc⟩
    rw [heq]
    exact Set.ncard_eq_three.2 ⟨_, _, _, P_inj.ne hne, P_inj.ne hne2, P_inj.ne hne3, rfl⟩
  have hinj : Set.InjOn f (D : Set (ℤ × ℤ)) := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    obtain ⟨ha1, ha2, hb1, hb2⟩ := hmemD a b hab
    obtain ⟨ha1', ha2', hb1', hb2'⟩ := hmemD a' b' hab'
    have hne : (a : ℝ) ≠ b := by
      intro h; have : a = b := by exact_mod_cast h
      omega
    have h1 : P a' ∈ f (a, b) := heq ▸ left_mem_affineSpan_pair _ _ _
    have h2 : P b' ∈ f (a, b) := heq ▸ right_mem_affineSpan_pair _ _ _
    have h1' := (mem_line hne).1 h1
    have h2' := (mem_line hne).1 h2
    have g1 : a' = a ∨ a' = b ∨ a' = -(a + b) := by exact_mod_cast h1'
    have g2 : b' = a ∨ b' = b ∨ b' = -(a + b) := by exact_mod_cast h2'
    simp only [Prod.mk.injEq]
    omega
  calc M * M = D.card := hD.symm
    _ = (f '' (D : Set (ℤ × ℤ))).ncard := by
        rw [hinj.ncard_image, Set.ncard_coe_finset]
    _ ≤ _ := Set.ncard_le_ncard hsub (lines_finite 3 (S_finite M))

theorem three_main : ¬ (fun n : ℕ ↦ (Erdos588.numLinesWithPointsMax 3 n : ℝ)) =o[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  intro h
  have hc := h.def (c := 1 / 100) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  have h1 := hN (6 * (N + 1) + 1) (by omega)
  have h2 : (N + 1) * (N + 1) ≤ Erdos588.numLinesWithPointsMax 3 (6 * (N + 1) + 1) :=
    (S_lines (N + 1)).trans (le_csSup (bdd _)
      ⟨S (N + 1), S_ncard (N + 1), S_finite (N + 1), S_noncol (N + 1), rfl⟩)
  have h3 : (((N + 1) * (N + 1) : ℕ) : ℝ) ≤
      (Erdos588.numLinesWithPointsMax 3 (6 * (N + 1) + 1) : ℝ) := by exact_mod_cast h2
  simp only [norm_pow, Real.norm_natCast] at h1
  push_cast at h1 h3
  nlinarith

end OMA588

theorem OMA.solution : type_of% @Erdos588.erdos_588.variants.three_not_isLittleO :=
  OMA588.three_main
