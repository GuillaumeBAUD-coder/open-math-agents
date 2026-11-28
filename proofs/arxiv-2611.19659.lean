import OMAStatements.S_arxiv_2611_19659

namespace OMA.P_arxiv_2611_19659

open OMA.S_arxiv_2611_19659

/-! ### Part 1: 8-Colouring of Ordered Full Binary Trees (`thm:main` on trees) -/

private def Q (a b : Bool × Bool) : Bool × Bool :=
  (xor (xor a.1 a.2) b.1, xor (xor (xor a.2 b.1) b.2) true)

private def D (a b : Bool × Bool) : Bool :=
  xor a.2 b.1

private def lab : FullBinTree → Bool × Bool
  | .leaf => (false, false)
  | .node l r => Q (lab l) (lab r)

/-- Recursive computation of `d(T)` given the path-depth parity `p` of the root of `T`. -/
private def dAux : FullBinTree → Bool → Bool
  | .leaf, _ => false
  | .node l r, p =>
    if D (lab l) (lab r) = false then
      xor (!p) (xor (dAux l (!p)) (dAux r false))
    else
      xor (dAux l false) (dAux r (!p))

private lemma Q_left_inj (a b c : Bool × Bool) (h : Q a c = Q b c) : a = b := by
  revert a b c h; decide

private lemma Q_right_inj (a b c : Bool × Bool) (h : Q c a = Q c b) : a = b := by
  revert a b c h; decide

private lemma Q_assoc_D (a b c : Bool × Bool) (h : Q (Q a b) c = Q a (Q b c)) :
    D (Q a b) c = false ∧ D a b = true ∧ D a (Q b c) = true ∧ D b c = false := by
  revert a b c h; decide

private lemma dAux_flip_of_rotAdj {T₁ T₂ : FullBinTree} (h : RotAdj T₁ T₂)
    (hlab : lab T₁ = lab T₂) (p : Bool) : dAux T₂ p = !(dAux T₁ p) := by
  induction h generalizing p with
  | rotRight u v w =>
    obtain ⟨h1, h2, h3, h4⟩ := Q_assoc_D (lab u) (lab v) (lab w) hlab
    simp only [dAux, lab, h1, h2, h3, h4, Bool.true_eq_false, ↓reduceIte, Bool.not_not]
    cases p <;> cases dAux u false <;> cases dAux v false <;> cases dAux v true <;> cases dAux w false <;> decide
  | rotLeft u v w =>
    obtain ⟨h1, h2, h3, h4⟩ := Q_assoc_D (lab u) (lab v) (lab w) hlab.symm
    simp only [dAux, lab, h1, h2, h3, h4, Bool.true_eq_false, ↓reduceIte, Bool.not_not]
    cases p <;> cases dAux u false <;> cases dAux v false <;> cases dAux v true <;> cases dAux w false <;> decide
  | inLeft h ih =>
    rename_i l₁ l₂ r
    have hl : lab l₁ = lab l₂ := Q_left_inj _ _ _ hlab
    simp only [dAux, hl]
    split_ifs
    · rw [ih hl (!p)]
      generalize dAux l₁ (!p) = a; generalize dAux r false = b; revert p a b; decide
    · rw [ih hl false]
      generalize dAux l₁ false = a; generalize dAux r (!p) = b; revert a b; decide
  | inRight h ih =>
    rename_i l r₁ r₂
    have hr : lab r₁ = lab r₂ := Q_right_inj _ _ _ hlab
    simp only [dAux, hr]
    split_ifs
    · rw [ih hr false]
      generalize dAux l (!p) = a; generalize dAux r₁ false = b; revert p a b; decide
    · rw [ih hr (!p)]
      generalize dAux l false = a; generalize dAux r₁ (!p) = b; revert a b; decide

private def treeColor (T : FullBinTree) : Fin 8 :=
  ⟨(if (lab T).1 then 4 else 0) + (if (lab T).2 then 2 else 0) + (if dAux T false then 1 else 0),
    by split_ifs <;> omega⟩

private lemma treeColor_ne_of_rotAdj {T₁ T₂ : FullBinTree} (h : RotAdj T₁ T₂) :
    treeColor T₁ ≠ treeColor T₂ := by
  intro heq
  have hv : ((if (lab T₁).1 then 4 else 0) + (if (lab T₁).2 then 2 else 0) + (if dAux T₁ false then 1 else 0)) =
            ((if (lab T₂).1 then 4 else 0) + (if (lab T₂).2 then 2 else 0) + (if dAux T₂ false then 1 else 0)) :=
    congrArg Fin.val heq
  have h1 : (lab T₁).1 = (lab T₂).1 := by
    cases ha : (lab T₁).1 <;> cases hb : (lab T₂).1 <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    all_goals split_ifs at hv <;> omega
  have h2 : (lab T₁).2 = (lab T₂).2 := by
    cases ha : (lab T₁).1 <;> cases hb : (lab T₂).1 <;>
    cases hc : (lab T₁).2 <;> cases hd : (lab T₂).2 <;>
    simp only [ha, hb, hc, hd, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    all_goals split_ifs at hv <;> omega
  have h3 : dAux T₁ false = dAux T₂ false := by
    cases ha : (lab T₁).1 <;> cases hb : (lab T₂).1 <;>
    cases hc : (lab T₁).2 <;> cases hd : (lab T₂).2 <;>
    cases he : dAux T₁ false <;> cases hf : dAux T₂ false <;>
    simp only [ha, hb, hc, hd, he, hf, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    all_goals omega
  have hlab : lab T₁ = lab T₂ := Prod.ext h1 h2
  have hflip := dAux_flip_of_rotAdj h hlab false
  rw [← h3] at hflip
  cases h4 : dAux T₁ false <;> simp [h4] at hflip

/-! ### Part 2: Triangulation-to-Tree Homomorphism (`FlipAdj → RotAdj`) -/

private def NCross (p q : ℕ × ℕ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

private lemma nCross_symm {p q : ℕ × ℕ} (h : NCross p q) : NCross q p :=
  h.symm

private abbrev InSpan (a b : ℕ) (p : ℕ × ℕ) : Prop :=
  a ≤ p.1 ∧ p.1 + 1 < p.2 ∧ p.2 ≤ b ∧ ¬ (p.1 = a ∧ p.2 = b)

private def IsChord (D : Finset (ℕ × ℕ)) (u v : ℕ) : Prop :=
  v = u + 1 ∨ (u, v) ∈ D

private def IsTriOn (a b : ℕ) (D : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ D, InSpan a b p) ∧ (∀ p ∈ D, ∀ q ∈ D, ¬ NCross p q) ∧ D.card = b - a - 2

private lemma noncrossing_card_le_and_apex :
    ∀ (m : ℕ), 2 ≤ m → ∀ (a b : ℕ) (D : Finset (ℕ × ℕ)),
      b - a = m →
      (∀ p ∈ D, InSpan a b p) →
      (∀ p ∈ D, ∀ q ∈ D, ¬ NCross p q) →
      D.card ≤ m - 2 ∧
        (D.card = m - 2 → ∃ k : ℕ, a < k ∧ k < b ∧ IsChord D a k ∧ IsChord D k b) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm a b D hba hspan hnc
    by_cases hm2 : m = 2
    · subst hm2
      have hDemp : D = ∅ := by
        ext p; simp only [Finset.notMem_empty, iff_false]
        intro hp; have := hspan p hp; unfold InSpan at this; omega
      rw [hDemp]; simp only [Finset.card_empty, Nat.sub_self, le_refl, true_and]
      intro _
      exact ⟨a + 1, by omega, by omega, Or.inl rfl, Or.inl (by omega)⟩
    · have hm3 : 3 ≤ m := by omega
      by_cases hDne : D.Nonempty
      · -- Choose `p₀ = (u, v) ∈ D` maximizing `p.2 - p.1`.
        obtain ⟨p₀, hp₀, hmax⟩ := Finset.exists_max_image D (fun p => p.2 - p.1) hDne
        rcases p₀ with ⟨u, v⟩
        have huv_sp : InSpan a b (u, v) := hspan (u, v) hp₀
        rcases huv_sp with ⟨hau, huv2, hvb, huv_ne⟩
        have huv_len : 2 ≤ v - u := by omega
        have huv_lt : v - u < m := by
          by_cases h1 : u = a
          · have : v < b := by by_contra hc; exact huv_ne ⟨h1, by omega⟩
            omega
          · omega
        let D_in : Finset (ℕ × ℕ) := D.filter fun p => u ≤ p.1 ∧ p.2 ≤ v ∧ p ≠ (u, v)
        let D_out : Finset (ℕ × ℕ) := (D.erase (u, v)) \ D_in
        have hpart : D.card = 1 + D_in.card + D_out.card := by
          have hsub : D_in ⊆ D.erase (u, v) := fun p hp => by
            have := Finset.mem_filter.mp hp
            exact Finset.mem_erase.mpr ⟨this.2.2.2, this.1⟩
          have h1 := Finset.card_sdiff_add_card_eq_card hsub
          have h2 := Finset.card_erase_add_one hp₀
          change D_out.card + D_in.card = (D.erase (u, v)).card at h1
          omega
        have hDin_sp : ∀ p ∈ D_in, InSpan u v p := fun p hp => by
          have hf := Finset.mem_filter.mp hp
          have hsp := hspan p hf.1
          exact ⟨hf.2.1, hsp.2.1, hf.2.2.1, fun ⟨h1, h2⟩ => hf.2.2.2 (Prod.ext h1 h2)⟩
        have hDin_nc : ∀ p ∈ D_in, ∀ q ∈ D_in, ¬ NCross p q := fun p hp q hq =>
          hnc p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
        have hDin_le : D_in.card ≤ v - u - 2 :=
          (ih (v - u) huv_lt huv_len u v D_in rfl hDin_sp hDin_nc).1
        -- Every `p ∈ D_out` satisfies `p.2 ≤ u ∨ v ≤ p.1`.
        have hDout_side : ∀ p ∈ D_out, p.2 ≤ u ∨ v ≤ p.1 := by
          intro p hp
          have hp_er : p ∈ D.erase (u, v) := (Finset.mem_sdiff.mp hp).1
          have hpD : p ∈ D := Finset.mem_of_mem_erase hp_er
          have hpne : p ≠ (u, v) := Finset.ne_of_mem_erase hp_er
          have hp_nin : p ∉ D_in := (Finset.mem_sdiff.mp hp).2
          have hsp := hspan p hpD
          have hnc' := hnc p hpD (u, v) hp₀
          have hmx := hmax p hpD
          dsimp only at hmx
          by_contra hcon; push Not at hcon
          rcases hcon with ⟨h1, h2⟩
          -- `u < p.2` and `p.1 < v`.
          by_cases hpu : p.1 < u
          · by_cases hpv : p.2 < v
            · exact hnc' (Or.inl ⟨hpu, h1, hpv⟩)
            · -- `p.1 < u` and `v ≤ p.2` contradicts maximality of `v - u`!
              omega
          · by_cases hpv : p.2 ≤ v
            · exact hp_nin (Finset.mem_filter.mpr ⟨hpD, by omega, hpv, hpne⟩)
            · by_cases hpu_eq : p.1 = u
              · omega
              · exact hnc' (Or.inr ⟨by omega, h2, by omega⟩)
        -- Contraction map `φ`: collapses `[u, v]` to `[u, u + 1]`.
        obtain ⟨d_shift, hd_shift⟩ : ∃ d_s : ℕ, d_s = v - u - 1 := ⟨v - u - 1, rfl⟩
        obtain ⟨b', hb'_def⟩ : ∃ x : ℕ, x = b - d_shift := ⟨b - d_shift, rfl⟩
        let φ : ℕ → ℕ := fun t => if t ≤ u then t else t - d_shift
        have ha_eq : φ a = a := if_pos hau
        have hb'_eq : φ b = b' := by dsimp [φ]; rw [if_neg (by omega), ← hb'_def]
        have hm'_eq : b' - a = m - (v - u) + 1 := by omega
        have hm'_lt : b' - a < m := by omega
        have hm'_ge : 2 ≤ b' - a := by omega
        have hφ_mono : ∀ x y : ℕ, (x ≤ u ∨ v ≤ x) → (y ≤ u ∨ v ≤ y) → (x < y → φ x < φ y) := by
          intro x y hx hy hxy
          dsimp only [φ]
          split_ifs with h1 h2 h2 <;> omega
        have hφ_inj : ∀ x y : ℕ, (x ≤ u ∨ v ≤ x) → (y ≤ u ∨ v ≤ y) → φ x = φ y → x = y := by
          intro x y hx hy heq
          rcases lt_trichotomy x y with hlt | rfl | hgt
          · exact absurd heq (ne_of_lt (hφ_mono x y hx hy hlt))
          · rfl
          · exact absurd heq.symm (ne_of_lt (hφ_mono y x hy hx hgt))
        let D_out' : Finset (ℕ × ℕ) := D_out.image fun p => (φ p.1, φ p.2)
        have hDout'_card : D_out'.card = D_out.card := by
          apply Finset.card_image_of_injOn
          intro p hp q hq heq
          have hp_s := hDout_side p hp
          have hq_s := hDout_side q hq
          have hp_lt : p.1 < p.2 := by have := hspan p (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp).1); omega
          have hq_lt : q.1 < q.2 := by have := hspan q (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hq).1); omega
          have hp1 : p.1 ≤ u ∨ v ≤ p.1 := by rcases hp_s with h | h; exact Or.inl (by omega); exact Or.inr h
          have hp2 : p.2 ≤ u ∨ v ≤ p.2 := by rcases hp_s with h | h; exact Or.inl h; exact Or.inr (by omega)
          have hq1 : q.1 ≤ u ∨ v ≤ q.1 := by rcases hq_s with h | h; exact Or.inl (by omega); exact Or.inr h
          have hq2 : q.2 ≤ u ∨ v ≤ q.2 := by rcases hq_s with h | h; exact Or.inl h; exact Or.inr (by omega)
          exact Prod.ext (hφ_inj p.1 q.1 hp1 hq1 (congrArg Prod.fst heq))
            (hφ_inj p.2 q.2 hp2 hq2 (congrArg Prod.snd heq))
        have hDout'_sp : ∀ q ∈ D_out', InSpan a b' q := by
          intro q hq
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
          have hpD : p ∈ D := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp).1
          have hsp := hspan p hpD
          have hside := hDout_side p hp
          rcases hsp with ⟨hp1a, hp12, hp2b, hpne⟩
          rcases hside with hle | hge
          · have h1 : φ p.1 = p.1 := if_pos (by omega)
            have h2 : φ p.2 = p.2 := if_pos hle
            rw [h1, h2]
            refine ⟨hp1a, hp12, by omega, fun ⟨_, h2'⟩ => by omega⟩
          · have h1 : φ p.1 = p.1 - d_shift := if_neg (by omega)
            have h2 : φ p.2 = p.2 - d_shift := if_neg (by omega)
            rw [h1, h2]
            refine ⟨by omega, by omega, by omega, fun ⟨h1', _⟩ => by omega⟩
        have hDout'_nc : ∀ q₁ ∈ D_out', ∀ q₂ ∈ D_out', ¬ NCross q₁ q₂ := by
          intro q₁ hq₁ q₂ hq₂ hcr
          obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
          obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
          have hp₁D : p₁ ∈ D := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp₁).1
          have hp₂D : p₂ ∈ D := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp₂).1
          have hsp1 := hspan p₁ hp₁D; have hsp2 := hspan p₂ hp₂D
          have hs1 := hDout_side p₁ hp₁; have hs2 := hDout_side p₂ hp₂
          have h11 : p₁.1 ≤ u ∨ v ≤ p₁.1 := by rcases hs1 with h | h; exact Or.inl (by omega); exact Or.inr h
          have h12 : p₁.2 ≤ u ∨ v ≤ p₁.2 := by rcases hs1 with h | h; exact Or.inl h; exact Or.inr (by omega)
          have h21 : p₂.1 ≤ u ∨ v ≤ p₂.1 := by rcases hs2 with h | h; exact Or.inl (by omega); exact Or.inr h
          have h22 : p₂.2 ≤ u ∨ v ≤ p₂.2 := by rcases hs2 with h | h; exact Or.inl h; exact Or.inr (by omega)
          have hlt_of_φ : ∀ x y, (x ≤ u ∨ v ≤ x) → (y ≤ u ∨ v ≤ y) → φ x < φ y → x < y := by
            intro x y hx hy hlt
            rcases lt_trichotomy x y with h | rfl | h
            · exact h
            · exact absurd hlt (lt_irrefl _)
            · exact absurd hlt (not_lt.mpr (le_of_lt (hφ_mono y x hy hx h)))
          apply hnc p₁ hp₁D p₂ hp₂D
          rcases hcr with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
          · exact Or.inl ⟨hlt_of_φ _ _ h11 h21 c1, hlt_of_φ _ _ h21 h12 c2, hlt_of_φ _ _ h12 h22 c3⟩
          · exact Or.inr ⟨hlt_of_φ _ _ h21 h11 c1, hlt_of_φ _ _ h11 h22 c2, hlt_of_φ _ _ h22 h12 c3⟩
        have hih_out := ih (b' - a) hm'_lt hm'_ge a b' D_out' rfl hDout'_sp hDout'_nc
        have hDout_le : D_out.card ≤ b' - a - 2 := hDout'_card ▸ hih_out.1
        refine ⟨by clear hih_out; omega, fun hcard_eq => ?_⟩
        have hDout'_eq : D_out'.card = b' - a - 2 := by clear hih_out; omega
        obtain ⟨k', hk'a, hk'b, hch_L, hch_R⟩ := hih_out.2 hDout'_eq
        clear hih_out
        let k : ℕ := if k' ≤ u then k' else k' + d_shift
        have hk_side : k ≤ u ∨ v ≤ k := by dsimp only [k]; split_ifs <;> omega
        have hφk : φ k = k' := by dsimp only [k, φ]; split_ifs <;> omega
        have hka : a < k := by dsimp only [k]; split_ifs <;> omega
        have hkb : k < b := by dsimp only [k]; split_ifs <;> omega
        have hchL : IsChord D a k := by
          rcases hch_L with h1 | h2
          · by_cases hku : k' ≤ u
            · left; dsimp only [k]; rw [if_pos hku]; exact h1
            · right
              have hua : u = a := by omega
              have hkv : k = v := by dsimp only [k]; rw [if_neg hku]; omega
              rw [← hua, hkv]; exact hp₀
          · right
            obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp h2
            have hpD : p ∈ D := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp).1
            have hsp := hspan p hpD
            have hs := hDout_side p hp
            have hp1 : p.1 ≤ u ∨ v ≤ p.1 := by rcases hs with h | h; exact Or.inl (by omega); exact Or.inr h
            have hp2 : p.2 ≤ u ∨ v ≤ p.2 := by rcases hs with h | h; exact Or.inl h; exact Or.inr (by omega)
            have h1 : p.1 = a := hφ_inj p.1 a hp1 (Or.inl hau) ((congrArg Prod.fst hpeq).trans ha_eq.symm)
            have h2 : p.2 = k := hφ_inj p.2 k hp2 hk_side ((congrArg Prod.snd hpeq).trans hφk.symm)
            have : (a, k) = p := Prod.ext h1.symm h2.symm
            rw [this]; exact hpD
        have hchR : IsChord D k b := by
          rcases hch_R with h1 | h2
          · by_cases hku : k' ≤ u
            · right
              have hku_eq : k = u := by dsimp only [k]; rw [if_pos hku]; omega
              have hvb_eq : v = b := by omega
              rw [hku_eq, ← hvb_eq]; exact hp₀
            · left; dsimp only [k]; rw [if_neg hku]; omega
          · right
            obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp h2
            have hpD : p ∈ D := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp).1
            have hsp := hspan p hpD
            have hs := hDout_side p hp
            have hp1 : p.1 ≤ u ∨ v ≤ p.1 := by rcases hs with h | h; exact Or.inl (by omega); exact Or.inr h
            have hp2 : p.2 ≤ u ∨ v ≤ p.2 := by rcases hs with h | h; exact Or.inl h; exact Or.inr (by omega)
            have h1 : p.1 = k := hφ_inj p.1 k hp1 hk_side ((congrArg Prod.fst hpeq).trans hφk.symm)
            have h2 : p.2 = b := hφ_inj p.2 b hp2 (Or.inr hvb) ((congrArg Prod.snd hpeq).trans hb'_eq.symm)
            have : (k, b) = p := Prod.ext h1.symm h2.symm
            rw [this]; exact hpD
        exact ⟨k, hka, hkb, hchL, hchR⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hDne
        rw [hDne, Finset.card_empty]
        exact ⟨Nat.zero_le _, fun h => by omega⟩

private lemma apex_unique {a b : ℕ} {D : Finset (ℕ × ℕ)}
    (hnc : ∀ p ∈ D, ∀ q ∈ D, ¬ NCross p q)
    {k₁ k₂ : ℕ} (h1 : a < k₁ ∧ k₁ < b ∧ IsChord D a k₁ ∧ IsChord D k₁ b)
    (h2 : a < k₂ ∧ k₂ < b ∧ IsChord D a k₂ ∧ IsChord D k₂ b) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · exfalso
    have hak₂ : (a, k₂) ∈ D := by rcases h2.2.2.1 with h | h; omega; exact h
    have hk₁b : (k₁, b) ∈ D := by rcases h1.2.2.2 with h | h; omega; exact h
    exact hnc (a, k₂) hak₂ (k₁, b) hk₁b (Or.inl ⟨h1.1, hlt, h2.2.1⟩)
  · rfl
  · exfalso
    have hak₁ : (a, k₁) ∈ D := by rcases h1.2.2.1 with h | h; omega; exact h
    have hk₂b : (k₂, b) ∈ D := by rcases h2.2.2.2 with h | h; omega; exact h
    exact hnc (a, k₁) hak₁ (k₂, b) hk₂b (Or.inl ⟨h2.1, hgt, h1.2.1⟩)

private lemma split_isTriOn {a b k : ℕ} {D : Finset (ℕ × ℕ)}
    (htri : IsTriOn a b D) (hka : a < k) (hkb : k < b)
    (hL : IsChord D a k) (hR : IsChord D k b) :
    (∀ p ∈ D, InSpan a k p ∨ InSpan k b p ∨ p = (a, k) ∨ p = (k, b)) ∧
    (2 ≤ k - a → IsTriOn a k (D.filter (InSpan a k))) ∧
    (2 ≤ b - k → IsTriOn k b (D.filter (InSpan k b))) := by
  have hdisj : ∀ p ∈ D, InSpan a k p ∨ InSpan k b p ∨ p = (a, k) ∨ p = (k, b) := by
    intro p hp
    rcases htri.1 p hp with ⟨hp1a, hp12, hp2b, hpne⟩
    by_cases h1 : p = (a, k)
    · exact Or.inr (Or.inr (Or.inl h1))
    · by_cases h2 : p = (k, b)
      · exact Or.inr (Or.inr (Or.inr h2))
      · by_cases hpk : p.2 ≤ k
        · exact Or.inl ⟨hp1a, hp12, hpk, fun ⟨c1, c2⟩ => h1 (Prod.ext c1 c2)⟩
        · by_cases hp1k : k ≤ p.1
          · exact Or.inr (Or.inl ⟨hp1k, hp12, hp2b, fun ⟨c1, c2⟩ => h2 (Prod.ext c1 c2)⟩)
          · -- `p.1 < k < p.2`
            exfalso
            by_cases hpa : p.1 = a
            · -- `p = (a, p.2)` with `k < p.2 < b` crosses `(k, b)`!
              have hkb_mem : (k, b) ∈ D := by rcases hR with h | h; omega; exact h
              have hp2b_lt : p.2 < b := by by_contra hc; exact hpne ⟨hpa, by omega⟩
              exact htri.2.1 p hp (k, b) hkb_mem (Or.inl ⟨by omega, by omega, hp2b_lt⟩)
            · -- `a < p.1 < k < p.2` crosses `(a, k)`!
              have hak_mem : (a, k) ∈ D := by rcases hL with h | h; omega; exact h
              exact htri.2.1 (a, k) hak_mem p hp (Or.inl ⟨by omega, by omega, by omega⟩)
  let DL := D.filter (InSpan a k)
  let DR := D.filter (InSpan k b)
  let cL : ℕ := if a + 1 < k then 1 else 0
  let cR : ℕ := if k + 1 < b then 1 else 0
  have hDL_le : DL.card ≤ k - a - 2 := by
    by_cases h2 : 2 ≤ k - a
    · exact (noncrossing_card_le_and_apex (k - a) h2 a k DL rfl
        (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p hp q hq => htri.2.1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)).1
    · have : DL = ∅ := by
        ext p; simp only [DL, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hsp; omega
      rw [this]; simp
  have hDR_le : DR.card ≤ b - k - 2 := by
    by_cases h2 : 2 ≤ b - k
    · exact (noncrossing_card_le_and_apex (b - k) h2 k b DR rfl
        (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p hp q hq => htri.2.1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)).1
    · have : DR = ∅ := by
        ext p; simp only [DR, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hsp; omega
      rw [this]; simp
  have hD_le : D.card ≤ DL.card + DR.card + cL + cR := by
    let S1 : Finset (ℕ × ℕ) := if a + 1 < k then {(a, k)} else ∅
    let S2 : Finset (ℕ × ℕ) := if k + 1 < b then {(k, b)} else ∅
    have hsub : D ⊆ DL ∪ DR ∪ S1 ∪ S2 := by
      intro p hp
      rcases hdisj p hp with h | h | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)))
      · have hsp := htri.1 (a, k) hp
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [S1, hsp.2.1]))
      · have hsp := htri.1 (k, b) hp
        exact Finset.mem_union_right _ (by simp [S2, hsp.2.1])
    have hS1 : S1.card = cL := by dsimp [S1, cL]; split_ifs <;> simp
    have hS2 : S2.card = cR := by dsimp [S2, cR]; split_ifs <;> simp
    calc D.card ≤ (DL ∪ DR ∪ S1 ∪ S2).card := Finset.card_le_card hsub
      _ ≤ (DL ∪ DR ∪ S1).card + S2.card := Finset.card_union_le _ _
      _ ≤ (DL ∪ DR).card + S1.card + S2.card := by have := Finset.card_union_le (DL ∪ DR) S1; omega
      _ ≤ DL.card + DR.card + S1.card + S2.card := by have := Finset.card_union_le DL DR; omega
      _ = DL.card + DR.card + cL + cR := by rw [hS1, hS2]
  have htot := htri.2.2
  refine ⟨hdisj, fun h2 => ?_, fun h2 => ?_⟩
  · refine ⟨fun p hp => (Finset.mem_filter.mp hp).2,
      fun p hp q hq => htri.2.1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1, ?_⟩
    change DL.card = k - a - 2
    dsimp [cL, cR] at hD_le; split_ifs at hD_le <;> omega
  · refine ⟨fun p hp => (Finset.mem_filter.mp hp).2,
      fun p hp q hq => htri.2.1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1, ?_⟩
    change DR.card = b - k - 2
    dsimp [cL, cR] at hD_le; split_ifs at hD_le <;> omega

open scoped Classical in
/-- Recursively build the ordered full binary tree of a triangulation on interval `[a, b]`. -/
private noncomputable def triTree (a b : ℕ) (D : Finset (ℕ × ℕ)) : FullBinTree :=
  if _ : 2 ≤ b - a then
    if hex : ∃ k : ℕ, a < k ∧ k < b ∧ IsChord D a k ∧ IsChord D k b then
      .node (triTree a (Classical.choose hex) D) (triTree (Classical.choose hex) b D)
    else .leaf
  else .leaf
termination_by b - a
decreasing_by
  · have hspec := Classical.choose_spec hex; omega
  · have hspec := Classical.choose_spec hex; omega

private lemma triTree_eq_leaf {a b : ℕ} (D : Finset (ℕ × ℕ)) (h : b - a < 2) :
    triTree a b D = .leaf := by
  unfold triTree; rw [dif_neg (by omega)]

open scoped Classical in
private lemma triTree_eq_node {a b k : ℕ} {D : Finset (ℕ × ℕ)}
    (hnc : ∀ p ∈ D, ∀ q ∈ D, ¬ NCross p q)
    (hka : a < k) (hkb : k < b) (hL : IsChord D a k) (hR : IsChord D k b) :
    triTree a b D = .node (triTree a k D) (triTree k b D) := by
  have h2 : 2 ≤ b - a := by omega
  have hex : ∃ k' : ℕ, a < k' ∧ k' < b ∧ IsChord D a k' ∧ IsChord D k' b := ⟨k, hka, hkb, hL, hR⟩
  conv_lhs => unfold triTree
  rw [dif_pos h2, dif_pos hex]
  have hk_eq : Classical.choose hex = k := apex_unique hnc (Classical.choose_spec hex) ⟨hka, hkb, hL, hR⟩
  rw [hk_eq]

open scoped Classical in
private lemma triTree_congr {a b : ℕ} {D₁ D₂ : Finset (ℕ × ℕ)}
    (hagree : ∀ p, InSpan a b p → (p ∈ D₁ ↔ p ∈ D₂)) :
    triTree a b D₁ = triTree a b D₂ := by
  generalize hm : b - a = m
  induction m using Nat.strong_induction_on generalizing a b with
  | h m ih =>
    by_cases h2 : 2 ≤ b - a
    · have hch_eq : ∀ k, a < k → k < b → (IsChord D₁ a k ↔ IsChord D₂ a k) ∧ (IsChord D₁ k b ↔ IsChord D₂ k b) := by
        intro k hka hkb
        constructor
        · unfold IsChord
          by_cases h1 : k = a + 1
          · simp [h1]
          · simp only [h1, false_or]
            exact hagree (a, k) ⟨le_refl a, by omega, le_of_lt hkb, fun ⟨_, hb⟩ => ne_of_lt hkb hb⟩
        · unfold IsChord
          by_cases h1 : b = k + 1
          · simp [h1]
          · simp only [h1, false_or]
            exact hagree (k, b) ⟨le_of_lt hka, by omega, le_refl b, fun ⟨ha, _⟩ => ne_of_gt hka ha⟩
      have hex_iff : (∃ k, a < k ∧ k < b ∧ IsChord D₁ a k ∧ IsChord D₁ k b) ↔
          (∃ k, a < k ∧ k < b ∧ IsChord D₂ a k ∧ IsChord D₂ k b) :=
        ⟨fun ⟨k, h1, h2', h3, h4⟩ => ⟨k, h1, h2', (hch_eq k h1 h2').1.mp h3, (hch_eq k h1 h2').2.mp h4⟩,
         fun ⟨k, h1, h2', h3, h4⟩ => ⟨k, h1, h2', (hch_eq k h1 h2').1.mpr h3, (hch_eq k h1 h2').2.mpr h4⟩⟩
      conv_lhs => unfold triTree
      conv_rhs => unfold triTree
      rw [dif_pos h2, dif_pos h2]
      by_cases hex1 : ∃ k, a < k ∧ k < b ∧ IsChord D₁ a k ∧ IsChord D₁ k b
      · have hex2 : ∃ k, a < k ∧ k < b ∧ IsChord D₂ a k ∧ IsChord D₂ k b := hex_iff.mp hex1
        rw [dif_pos hex1, dif_pos hex2]
        have hch_same : Classical.choose hex1 = Classical.choose hex2 := by
          congr 1; funext k; apply propext
          constructor
          · rintro ⟨h1, h2', h3, h4⟩; exact ⟨h1, h2', (hch_eq k h1 h2').1.mp h3, (hch_eq k h1 h2').2.mp h4⟩
          · rintro ⟨h1, h2', h3, h4⟩; exact ⟨h1, h2', (hch_eq k h1 h2').1.mpr h3, (hch_eq k h1 h2').2.mpr h4⟩
        rw [hch_same]
        set k := Classical.choose hex2
        have hk := Classical.choose_spec hex2
        congr 1
        · exact ih (k - a) (by omega) (fun p hp => hagree p ⟨hp.1, hp.2.1, le_trans hp.2.2.1 (le_of_lt hk.2.1),
            fun ⟨_, hb⟩ => by omega⟩) rfl
        · exact ih (b - k) (by omega) (fun p hp => hagree p ⟨le_trans (le_of_lt hk.1) hp.1, hp.2.1, hp.2.2.1,
            fun ⟨ha, _⟩ => by omega⟩) rfl
      · have hex2 : ¬ ∃ k, a < k ∧ k < b ∧ IsChord D₂ a k ∧ IsChord D₂ k b := fun h => hex1 (hex_iff.mpr h)
        rw [dif_neg hex1, dif_neg hex2]
    · rw [triTree_eq_leaf D₁ (by omega), triTree_eq_leaf D₂ (by omega)]

private lemma rotAdj_symm {T₁ T₂ : FullBinTree} (h : RotAdj T₁ T₂) : RotAdj T₂ T₁ := by
  induction h with
  | rotRight u v w => exact .rotLeft u v w
  | rotLeft u v w => exact .rotRight u v w
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

private lemma triTree_rotAdj_of_flip :
    ∀ (m : ℕ), 2 ≤ m → ∀ (a b : ℕ) (D₁ D₂ : Finset (ℕ × ℕ)) (d₁ d₂ : ℕ × ℕ),
      b - a = m →
      IsTriOn a b D₁ → IsTriOn a b D₂ →
      D₁ \ D₂ = {d₁} → D₂ \ D₁ = {d₂} →
      RotAdj (triTree a b D₁) (triTree a b D₂) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm a b D₁ D₂ d₁ d₂ hba htri1 htri2 hs1 hs2
    have hd1_mem : d₁ ∈ D₁ := (Finset.mem_sdiff.mp (hs1 ▸ Finset.mem_singleton_self d₁)).1
    have hd1_nmem : d₁ ∉ D₂ := (Finset.mem_sdiff.mp (hs1 ▸ Finset.mem_singleton_self d₁)).2
    have hd2_mem : d₂ ∈ D₂ := (Finset.mem_sdiff.mp (hs2 ▸ Finset.mem_singleton_self d₂)).1
    have hd2_nmem : d₂ ∉ D₁ := (Finset.mem_sdiff.mp (hs2 ▸ Finset.mem_singleton_self d₂)).2
    have hmem_other : ∀ p, p ≠ d₁ → p ≠ d₂ → (p ∈ D₁ ↔ p ∈ D₂) := fun p hne1 hne2 => by
      constructor
      · intro hp1; by_contra hp2
        have : p ∈ D₁ \ D₂ := Finset.mem_sdiff.mpr ⟨hp1, hp2⟩
        rw [hs1, Finset.mem_singleton] at this; exact hne1 this
      · intro hp2; by_contra hp1
        have : p ∈ D₂ \ D₁ := Finset.mem_sdiff.mpr ⟨hp2, hp1⟩
        rw [hs2, Finset.mem_singleton] at this; exact hne2 this
    have hcross : NCross d₁ d₂ := by
      by_contra hnc12
      let D' := insert d₂ D₁
      have hsp' : ∀ p ∈ D', InSpan a b p := fun p hp => by
        rcases Finset.mem_insert.mp hp with hp2 | hp1
        · rw [hp2]; exact htri2.1 d₂ hd2_mem
        · exact htri1.1 p hp1
      have hnc' : ∀ p ∈ D', ∀ q ∈ D', ¬ NCross p q := by
        intro p hp q hq
        rcases Finset.mem_insert.mp hp with hp2 | hp1 <;>
        rcases Finset.mem_insert.mp hq with hq2 | hq1
        · rw [hp2, hq2]; unfold NCross; omega
        · rw [hp2]
          by_cases hqd1 : q = d₁
          · subst hqd1; exact fun h => hnc12 (nCross_symm h)
          · have hq2' : q ∈ D₂ := (hmem_other q hqd1 (fun h => hd2_nmem (h ▸ hq1))).mp hq1
            exact htri2.2.1 d₂ hd2_mem q hq2'
        · rw [hq2]
          by_cases hpd1 : p = d₁
          · subst hpd1; exact hnc12
          · have hp2' : p ∈ D₂ := (hmem_other p hpd1 (fun h => hd2_nmem (h ▸ hp1))).mp hp1
            exact htri2.2.1 p hp2' d₂ hd2_mem
        · exact htri1.2.1 p hp1 q hq1
      have hle := (noncrossing_card_le_and_apex m hm a b D' hba hsp' hnc').1
      rw [Finset.card_insert_of_notMem hd2_nmem, htri1.2.2, hba] at hle
      omega
    obtain ⟨k₁, hk1a, hk1b, hch1L, hch1R⟩ := (noncrossing_card_le_and_apex m hm a b D₁ hba htri1.1 htri1.2.1).2 (hba ▸ htri1.2.2)
    obtain ⟨k₂, hk2a, hk2b, hch2L, hch2R⟩ := (noncrossing_card_le_and_apex m hm a b D₂ hba htri2.1 htri2.2.1).2 (hba ▸ htri2.2.2)
    rw [triTree_eq_node htri1.2.1 hk1a hk1b hch1L hch1R,
        triTree_eq_node htri2.2.1 hk2a hk2b hch2L hch2R]
    by_cases hkeq : k₁ = k₂
    · subst hkeq
      -- Neither `(a, k₁)` nor `(k₁, b)` is `d₁` or `d₂`.
      have hneL1 : d₁ ≠ (a, k₁) := fun h => by
        have : (a, k₁) ∉ D₂ := h ▸ hd1_nmem
        rcases hch2L with h' | h'
        · have := htri1.1 d₁ hd1_mem; rw [h] at this; unfold InSpan at this; omega
        · exact this h'
      have hneR1 : d₁ ≠ (k₁, b) := fun h => by
        have : (k₁, b) ∉ D₂ := h ▸ hd1_nmem
        rcases hch2R with h' | h'
        · have := htri1.1 d₁ hd1_mem; rw [h] at this; unfold InSpan at this; omega
        · exact this h'
      have hneL2 : d₂ ≠ (a, k₁) := fun h => by
        have : (a, k₁) ∉ D₁ := h ▸ hd2_nmem
        rcases hch1L with h' | h'
        · have := htri2.1 d₂ hd2_mem; rw [h] at this; unfold InSpan at this; omega
        · exact this h'
      have hneR2 : d₂ ≠ (k₁, b) := fun h => by
        have : (k₁, b) ∉ D₁ := h ▸ hd2_nmem
        rcases hch1R with h' | h'
        · have := htri2.1 d₂ hd2_mem; rw [h] at this; unfold InSpan at this; omega
        · exact this h'
      obtain ⟨hdisj1, htri1L, htri1R⟩ := split_isTriOn htri1 hk1a hk1b hch1L hch1R
      obtain ⟨hdisj2, htri2L, htri2R⟩ := split_isTriOn htri2 hk1a hk1b hch2L hch2R
      rcases hdisj1 d₁ hd1_mem with hd1L | hd1R | h | h
      · -- `d₁` lies in `InSpan a k₁`; since `NCross d₁ d₂`, `d₂` also lies in `InSpan a k₁`.
        have hd2L : InSpan a k₁ d₂ := by
          rcases hdisj2 d₂ hd2_mem with h | h | h | h
          · exact h
          · exfalso; unfold InSpan at hd1L h; unfold NCross at hcross; omega
          · exact absurd h hneL2
          · exact absurd h hneR2
        have hright_eq : triTree k₁ b D₁ = triTree k₁ b D₂ := triTree_congr fun p hp =>
          hmem_other p (fun h => by rw [h] at hp; unfold InSpan at hp hd1L; omega)
            (fun h => by rw [h] at hp; unfold InSpan at hp hd2L; omega)
        rw [hright_eq]
        apply RotAdj.inLeft
        have h2L : 2 ≤ k₁ - a := by unfold InSpan at hd1L; omega
        have hflt1 : triTree a k₁ D₁ = triTree a k₁ (D₁.filter (InSpan a k₁)) :=
          triTree_congr fun p hp => ⟨fun h => Finset.mem_filter.mpr ⟨h, hp⟩, fun h => (Finset.mem_filter.mp h).1⟩
        have hflt2 : triTree a k₁ D₂ = triTree a k₁ (D₂.filter (InSpan a k₁)) :=
          triTree_congr fun p hp => ⟨fun h => Finset.mem_filter.mpr ⟨h, hp⟩, fun h => (Finset.mem_filter.mp h).1⟩
        rw [hflt1, hflt2]
        refine ih (k₁ - a) (by omega) h2L a k₁ (D₁.filter (InSpan a k₁)) (D₂.filter (InSpan a k₁))
          d₁ d₂ rfl (htri1L h2L) (htri2L h2L) ?_ ?_
        · ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hp1, _⟩, hp2⟩
            have hnp2 : p ∉ D₂ := fun h => hp2 ⟨h, ‹_›⟩
            have : p ∈ D₁ \ D₂ := Finset.mem_sdiff.mpr ⟨hp1, hnp2⟩
            rwa [hs1, Finset.mem_singleton] at this
          · rintro rfl; exact ⟨⟨hd1_mem, hd1L⟩, fun h => hd1_nmem h.1⟩
        · ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hp2, _⟩, hp1⟩
            have hnp1 : p ∉ D₁ := fun h => hp1 ⟨h, ‹_›⟩
            have : p ∈ D₂ \ D₁ := Finset.mem_sdiff.mpr ⟨hp2, hnp1⟩
            rwa [hs2, Finset.mem_singleton] at this
          · rintro rfl; exact ⟨⟨hd2_mem, hd2L⟩, fun h => hd2_nmem h.1⟩
      · -- `d₁` lies in `InSpan k₁ b`; symmetrically `d₂` lies in `InSpan k₁ b`.
        have hd2R : InSpan k₁ b d₂ := by
          rcases hdisj2 d₂ hd2_mem with h | h | h | h
          · exfalso; unfold InSpan at hd1R h; unfold NCross at hcross; omega
          · exact h
          · exact absurd h hneL2
          · exact absurd h hneR2
        have hleft_eq : triTree a k₁ D₁ = triTree a k₁ D₂ := triTree_congr fun p hp =>
          hmem_other p (fun h => by rw [h] at hp; unfold InSpan at hp hd1R; omega)
            (fun h => by rw [h] at hp; unfold InSpan at hp hd2R; omega)
        rw [hleft_eq]
        apply RotAdj.inRight
        have h2R : 2 ≤ b - k₁ := by unfold InSpan at hd1R; omega
        have hflt1 : triTree k₁ b D₁ = triTree k₁ b (D₁.filter (InSpan k₁ b)) :=
          triTree_congr fun p hp => ⟨fun h => Finset.mem_filter.mpr ⟨h, hp⟩, fun h => (Finset.mem_filter.mp h).1⟩
        have hflt2 : triTree k₁ b D₂ = triTree k₁ b (D₂.filter (InSpan k₁ b)) :=
          triTree_congr fun p hp => ⟨fun h => Finset.mem_filter.mpr ⟨h, hp⟩, fun h => (Finset.mem_filter.mp h).1⟩
        rw [hflt1, hflt2]
        refine ih (b - k₁) (by omega) h2R k₁ b (D₁.filter (InSpan k₁ b)) (D₂.filter (InSpan k₁ b))
          d₁ d₂ rfl (htri1R h2R) (htri2R h2R) ?_ ?_
        · ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hp1, _⟩, hp2⟩
            have hnp2 : p ∉ D₂ := fun h => hp2 ⟨h, ‹_›⟩
            have : p ∈ D₁ \ D₂ := Finset.mem_sdiff.mpr ⟨hp1, hnp2⟩
            rwa [hs1, Finset.mem_singleton] at this
          · rintro rfl; exact ⟨⟨hd1_mem, hd1R⟩, fun h => hd1_nmem h.1⟩
        · ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hp2, _⟩, hp1⟩
            have hnp1 : p ∉ D₁ := fun h => hp1 ⟨h, ‹_›⟩
            have : p ∈ D₂ \ D₁ := Finset.mem_sdiff.mpr ⟨hp2, hnp1⟩
            rwa [hs2, Finset.mem_singleton] at this
          · rintro rfl; exact ⟨⟨hd2_mem, hd2R⟩, fun h => hd2_nmem h.1⟩
      · exact absurd h hneL1
      · exact absurd h hneR1
    · -- `k₁ ≠ k₂`: direct root rotation!
      have hroot_rot : ∀ (A B : Finset (ℕ × ℕ)) (da db : ℕ × ℕ) (ka kb : ℕ),
          IsTriOn a b A → IsTriOn a b B →
          A \ B = {da} → B \ A = {db} →
          a < ka → ka < kb → kb < b →
          IsChord A a ka → IsChord A ka b →
          IsChord B a kb → IsChord B kb b →
          RotAdj (.node (triTree a ka A) (triTree ka b A))
                 (.node (triTree a kb B) (triTree kb b B)) := by
        intro A B da db ka kb htA htB hsA hsB haka hakb hkbb hAL hAR hBL hBR
        have hka_b : (ka, b) ∈ A := by rcases hAR with h | h; omega; exact h
        have ha_kb : (a, kb) ∈ B := by rcases hBL with h | h; omega; exact h
        have hcr_ab : NCross (a, kb) (ka, b) := Or.inl ⟨haka, hakb, hkbb⟩
        have hka_b_nB : (ka, b) ∉ B := fun h => htB.2.1 (a, kb) ha_kb (ka, b) h hcr_ab
        have ha_kb_nA : (a, kb) ∉ A := fun h => htA.2.1 (a, kb) h (ka, b) hka_b hcr_ab
        have hda_eq : da = (ka, b) := by
          have : (ka, b) ∈ A \ B := Finset.mem_sdiff.mpr ⟨hka_b, hka_b_nB⟩
          rw [hsA, Finset.mem_singleton] at this; exact this.symm
        have hdb_eq : db = (a, kb) := by
          have : (a, kb) ∈ B \ A := Finset.mem_sdiff.mpr ⟨ha_kb, ha_kb_nA⟩
          rw [hsB, Finset.mem_singleton] at this; exact this.symm
        have hsame : ∀ p, p ≠ (ka, b) → p ≠ (a, kb) → (p ∈ A ↔ p ∈ B) := fun p h1 h2 => by
          constructor
          · intro hpA; by_contra hpB
            have : p ∈ A \ B := Finset.mem_sdiff.mpr ⟨hpA, hpB⟩
            rw [hsA, Finset.mem_singleton, hda_eq] at this; exact h1 this
          · intro hpB; by_contra hpA
            have : p ∈ B \ A := Finset.mem_sdiff.mpr ⟨hpB, hpA⟩
            rw [hsB, Finset.mem_singleton, hdb_eq] at this; exact h2 this
        -- Find apex `r` of `[ka, b]` in `A`, and prove `r = kb`!
        obtain ⟨_, _, htAR⟩ := split_isTriOn htA haka (by omega) hAL hAR
        have h2AR : 2 ≤ b - ka := by omega
        have htAR' := htAR h2AR
        obtain ⟨r, hra, hrb, hrL, hrR⟩ :=
          (noncrossing_card_le_and_apex (b - ka) h2AR ka b (A.filter (InSpan ka b)) rfl htAR'.1 htAR'.2.1).2 htAR'.2.2
        have hrL_A : IsChord A ka r := by rcases hrL with h | h; exact Or.inl h; exact Or.inr (Finset.mem_filter.mp h).1
        have hrR_A : IsChord A r b := by rcases hrR with h | h; exact Or.inl h; exact Or.inr (Finset.mem_filter.mp h).1
        have hr_eq : r = kb := by
          rcases lt_trichotomy r kb with hlt | rfl | hgt
          · exfalso
            have hrb_A : (r, b) ∈ A := by rcases hrR_A with h | h; omega; exact h
            have hrb_B : (r, b) ∈ B := (hsame (r, b) (by intro h; have := congrArg Prod.fst h; omega)
              (by intro h; have := congrArg Prod.fst h; omega)).mp hrb_A
            exact htB.2.1 (a, kb) ha_kb (r, b) hrb_B (Or.inl ⟨by omega, hlt, hkbb⟩)
          · rfl
          · exfalso
            have hkr_A : (ka, r) ∈ A := by rcases hrL_A with h | h; omega; exact h
            have hkr_B : (ka, r) ∈ B := (hsame (ka, r) (by intro h; have := congrArg Prod.snd h; omega)
              (by intro h; have := congrArg Prod.fst h; omega)).mp hkr_A
            exact htB.2.1 (a, kb) ha_kb (ka, r) hkr_B (Or.inl ⟨haka, hakb, hgt⟩)
        rcases hr_eq with rfl
        have hAL_B : IsChord B a ka := by
          rcases hAL with h | h
          · exact Or.inl h
          · exact Or.inr ((hsame (a, ka) (by intro h'; have := congrArg Prod.fst h'; omega)
              (by intro h'; have := congrArg Prod.snd h'; omega)).mp h)
        have hmid_B : IsChord B ka r := by
          rcases hrL_A with h | h
          · exact Or.inl h
          · exact Or.inr ((hsame (ka, r) (by intro h'; have := congrArg Prod.snd h'; omega)
              (by intro h'; have := congrArg Prod.fst h'; omega)).mp h)
        rw [triTree_eq_node htA.2.1 hakb hkbb hrL_A hrR_A,
            triTree_eq_node htB.2.1 haka hakb hAL_B hmid_B]
        have hU : triTree a ka A = triTree a ka B := triTree_congr fun p hp =>
          hsame p (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
            (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
        have hV : triTree ka r A = triTree ka r B := triTree_congr fun p hp =>
          hsame p (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
            (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
        have hW : triTree r b A = triTree r b B := triTree_congr fun p hp =>
          hsame p (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
            (fun h => by rw [h] at hp; unfold InSpan at hp; omega)
        rw [hU, hV, hW]
        exact .rotLeft _ _ _
      rcases lt_or_gt_of_ne hkeq with hlt | hgt
      · exact hroot_rot D₁ D₂ d₁ d₂ k₁ k₂ htri1 htri2 hs1 hs2 hk1a hlt hk2b hch1L hch1R hch2L hch2R
      · exact rotAdj_symm (hroot_rot D₂ D₁ d₂ d₁ k₂ k₁ htri2 htri1 hs2 hs1 hk2a hgt hk1b hch2L hch2R hch1L hch1R)

private def triToNatDiags {n : ℕ} (T : Triangulation n) : Finset (ℕ × ℕ) :=
  T.val.image fun d => (d.val.1.val, d.val.2.val)

private lemma triToNatDiags_isTriOn {n : ℕ} (hn : 3 ≤ n) (T : Triangulation n) :
    IsTriOn 0 (n - 1) (triToNatDiags T) := by
  have hinj : Function.Injective (fun d : TriDiag n => (d.val.1.val, d.val.2.val)) := fun d₁ d₂ h =>
    Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Nat.zero_le _, d.prop.1, by have := d.val.2.isLt; omega, d.prop.2⟩
  · intro p hp q hq
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp hq
    intro hcr; apply T.prop.2 d₁ hd₁ d₂ hd₂
    exact hcr
  · rw [triToNatDiags, Finset.card_image_of_injective _ hinj, T.prop.1]; omega

private lemma triangulation_8_colorable (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : Triangulation n → Fin 8,
      ∀ T₁ T₂ : Triangulation n, FlipAdj T₁ T₂ → c T₁ ≠ c T₂ := by
  refine ⟨fun T => treeColor (triTree 0 (n - 1) (triToNatDiags T)), fun T₁ T₂ hadj => ?_⟩
  apply treeColor_ne_of_rotAdj
  have hinj : Function.Injective (fun d : TriDiag n => (d.val.1.val, d.val.2.val)) := fun d₁ d₂ h =>
    Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))
  obtain ⟨d₁, hd1⟩ := Finset.card_eq_one.mp hadj.1
  obtain ⟨d₂, hd2⟩ := Finset.card_eq_one.mp hadj.2
  have hs1 : triToNatDiags T₁ \ triToNatDiags T₂ = {(d₁.val.1.val, d₁.val.2.val)} := by
    rw [triToNatDiags, triToNatDiags, ← Finset.image_sdiff T₁.val T₂.val hinj, hd1, Finset.image_singleton]
  have hs2 : triToNatDiags T₂ \ triToNatDiags T₁ = {(d₂.val.1.val, d₂.val.2.val)} := by
    rw [triToNatDiags, triToNatDiags, ← Finset.image_sdiff T₂.val T₁.val hinj, hd2, Finset.image_singleton]
  exact triTree_rotAdj_of_flip (n - 1) (by omega) 0 (n - 1)
    (triToNatDiags T₁) (triToNatDiags T₂) (d₁.val.1.val, d₁.val.2.val) (d₂.val.1.val, d₂.val.2.val)
    (by omega) (triToNatDiags_isTriOn hn T₁) (triToNatDiags_isTriOn hn T₂) hs1 hs2

/-! ### Part 3: Lower Bound for Quasigroup Label–Parity Colourings (`thm:lower`) -/

private lemma leaves_pos (T : FullBinTree) : 1 ≤ T.leaves := by
  induction T with
  | leaf => exact le_refl 1
  | node l r ihl ihr => simp only [FullBinTree.leaves]; omega

private lemma rotAdj_leaves {T₁ T₂ : FullBinTree} (h : RotAdj T₁ T₂) :
    T₁.leaves = T₂.leaves := by
  induction h with
  | rotRight u v w => simp only [FullBinTree.leaves]; omega
  | rotLeft u v w => simp only [FullBinTree.leaves]; omega
  | inLeft _ ih => simp only [FullBinTree.leaves]; omega
  | inRight _ ih => simp only [FullBinTree.leaves]; omega

private lemma no_odd_cycle_same_label {S : Type*} (op : S → S → S) (x : S) (β : FullBinTree → Bool)
    (hcol : ∀ n : ℕ, 3 ≤ n →
      ∀ T₁ T₂ : FullBinTree, T₁.leaves = n - 1 → T₂.leaves = n - 1 →
        RotAdj T₁ T₂ → (evalBinTree op x T₁, β T₁) ≠ (evalBinTree op x T₂, β T₂))
    {m : ℕ} (c : Fin (2 * m + 1) → FullBinTree)
    (hlv : 2 ≤ (c 0).leaves)
    (hstep : ∀ i : Fin (2 * m + 1),
      RotAdj (c i) (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩) ∧
      evalBinTree op x (c i) = evalBinTree op x (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩)) :
    False := by
  have hleaves_eq : ∀ k (hk : k < 2 * m + 1), (c ⟨k, hk⟩).leaves = (c 0).leaves := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have h1 := rotAdj_leaves (hstep ⟨k, by omega⟩).1
      have hmod : (k + 1) % (2 * m + 1) = k + 1 := Nat.mod_eq_of_lt hk
      simp only [hmod] at h1
      rw [← h1, ih (by omega)]
  have hflip : ∀ i : Fin (2 * m + 1),
      β (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩) = !(β (c i)) := by
    intro i
    have hlv_i : (c i).leaves = (c 0).leaves := hleaves_eq i.val i.isLt
    have hlv_n : (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩).leaves = (c 0).leaves :=
      hleaves_eq _ (Nat.mod_lt _ (by omega))
    have hne := hcol ((c 0).leaves + 1) (by omega) (c i) _ (by omega) (by omega) (hstep i).1
    have hβne : β (c i) ≠ β (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩) := fun heq =>
      hne (Prod.ext (hstep i).2 heq)
    cases h1 : β (c i) <;> cases h2 : β (c ⟨(i.val + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩)
    · exact absurd (h1.trans h2.symm) hβne
    · rfl
    · rfl
    · exact absurd (h1.trans h2.symm) hβne
  have hpar : ∀ k (hk : k < 2 * m + 1),
      β (c ⟨k, hk⟩) = if k % 2 = 0 then β (c 0) else !(β (c 0)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hflip ⟨k, by omega⟩
      have hmod : (k + 1) % (2 * m + 1) = k + 1 := Nat.mod_eq_of_lt hk
      simp only [hmod] at h1
      rw [h1, ih (by omega)]
      by_cases hev : k % 2 = 0
      · have : (k + 1) % 2 ≠ 0 := by omega
        simp [hev, this]
      · have : (k + 1) % 2 = 0 := by omega
        simp [hev, this]
  have hlast := hflip ⟨2 * m, by omega⟩
  have hmod0 : (2 * m + 1) % (2 * m + 1) = 0 := Nat.mod_self _
  simp only [hmod0] at hlast
  have h2m := hpar (2 * m) (by omega)
  have h2mev : (2 * m) % 2 = 0 := by omega
  simp only [h2mev, ↓reduceIte] at h2m
  rw [h2m] at hlast
  change β (c 0) = !(β (c 0)) at hlast
  cases h0 : β (c 0) <;> simp [h0] at hlast

private lemma pentagon_contra {S : Type*} (op : S → S → S) (x : S) (β : FullBinTree → Bool)
    (hcol : ∀ n : ℕ, 3 ≤ n →
      ∀ T₁ T₂ : FullBinTree, T₁.leaves = n - 1 → T₂.leaves = n - 1 →
        RotAdj T₁ T₂ → (evalBinTree op x T₁, β T₁) ≠ (evalBinTree op x T₂, β T₂))
    (A B C E : FullBinTree)
    (h1 : op (op (evalBinTree op x A) (evalBinTree op x B)) (evalBinTree op x C) =
          op (evalBinTree op x A) (op (evalBinTree op x B) (evalBinTree op x C)))
    (h2 : op (op (evalBinTree op x A) (op (evalBinTree op x B) (evalBinTree op x C))) (evalBinTree op x E) =
          op (evalBinTree op x A) (op (op (evalBinTree op x B) (evalBinTree op x C)) (evalBinTree op x E)))
    (h3 : op (op (evalBinTree op x B) (evalBinTree op x C)) (evalBinTree op x E) =
          op (evalBinTree op x B) (op (evalBinTree op x C) (evalBinTree op x E)))
    (h4 : op (evalBinTree op x A) (op (evalBinTree op x B) (op (evalBinTree op x C) (evalBinTree op x E))) =
          op (op (evalBinTree op x A) (evalBinTree op x B)) (op (evalBinTree op x C) (evalBinTree op x E)))
    (h5 : op (op (evalBinTree op x A) (evalBinTree op x B)) (op (evalBinTree op x C) (evalBinTree op x E)) =
          op (op (op (evalBinTree op x A) (evalBinTree op x B)) (evalBinTree op x C)) (evalBinTree op x E)) :
    False := by
  let c : Fin 5 → FullBinTree :=
    ![.node (.node (.node A B) C) E,
      .node (.node A (.node B C)) E,
      .node A (.node (.node B C) E),
      .node A (.node B (.node C E)),
      .node (.node A B) (.node C E)]
  refine no_odd_cycle_same_label op x β hcol (m := 2) c ?_ ?_
  · have := leaves_pos A; have := leaves_pos B; have := leaves_pos C; have := leaves_pos E
    simp only [c, Matrix.cons_val_zero, FullBinTree.leaves]; omega
  · intro i
    fin_cases i
    · exact ⟨.inLeft (.rotRight A B C), by simp [c, evalBinTree, h1]⟩
    · exact ⟨.rotRight A (.node B C) E, by simp [c, evalBinTree, h2]⟩
    · exact ⟨.inRight (.rotRight B C E), by simp [c, evalBinTree, h3]⟩
    · exact ⟨.rotLeft A B (.node C E), by simp [c, evalBinTree, h4]⟩
    · exact ⟨.rotLeft (.node A B) C E, by simp [c, evalBinTree, h5]⟩

/-- Classification of quasigroup operations on `ZMod 3`: every Latin square of order 3 is affine
    `f a b = u * a + v * b + w` with `u, v ∈ {1, 2}`. -/
private lemma quasigroup_zmod3_affine (f : ZMod 3 → ZMod 3 → ZMod 3) (hq : IsQuasigroup f) :
    ∃ u v w : ZMod 3, (u = 1 ∨ u = 2) ∧ (v = 1 ∨ v = 2) ∧ ∀ a b : ZMod 3, f a b = u * a + v * b + w := by
  obtain ⟨w, hw⟩ : ∃ w : ZMod 3, w = f 0 0 := ⟨f 0 0, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ZMod 3, u = f 1 0 - w := ⟨f 1 0 - w, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ZMod 3, v = f 0 1 - w := ⟨f 0 1 - w, rfl⟩
  have h00 : f 0 0 = w := hw.symm
  have h10 : f 1 0 = u + w := by rw [hu]; ring
  have h01 : f 0 1 = v + w := by rw [hv]; ring
  have hu0 : u ≠ 0 := fun h => by
    have h1 : f 1 0 = f 0 0 := by rw [h10, h00, h, zero_add]
    exact absurd ((hq.2 0).1 h1) (by decide)
  have hv0 : v ≠ 0 := fun h => by
    have h1 : f 0 1 = f 0 0 := by rw [h01, h00, h, zero_add]
    exact absurd ((hq.1 0).1 h1) (by decide)
  have h20 : f 2 0 = 2 * u + w := by
    have hne0 : f 2 0 ≠ w := fun h => absurd ((hq.2 0).1 (h.trans h00.symm)) (by decide)
    have hne1 : f 2 0 ≠ u + w := fun h => absurd ((hq.2 0).1 (h.trans h10.symm)) (by decide)
    generalize f 2 0 = y at hne0 hne1 ⊢
    clear hq hw hu hv h00 h10 h01 hv0 f
    revert y u w hu0 hne0 hne1; decide
  have h02 : f 0 2 = 2 * v + w := by
    have hne0 : f 0 2 ≠ w := fun h => absurd ((hq.1 0).1 (h.trans h00.symm)) (by decide)
    have hne1 : f 0 2 ≠ v + w := fun h => absurd ((hq.1 0).1 (h.trans h01.symm)) (by decide)
    generalize f 0 2 = y at hne0 hne1 ⊢
    clear hq hw hu hv h00 h10 h01 h20 hu0 f
    revert y v w hv0 hne0 hne1; decide
  have hneq : ∀ a₁ a₂ b : ZMod 3, a₁ ≠ a₂ → f a₁ b ≠ f a₂ b := fun a₁ a₂ b hne h => hne ((hq.2 b).1 h)
  have hneq' : ∀ a b₁ b₂ : ZMod 3, b₁ ≠ b₂ → f a b₁ ≠ f a b₂ := fun a b₁ b₂ hne h => hne ((hq.1 a).1 h)
  have h11 : f 1 1 = u + v + w := by
    have c1 := hneq 1 0 1 (by decide)
    have c2 := hneq' 1 1 0 (by decide)
    have c3 := hneq 1 2 1 (by decide)
    have c4 := hneq 2 0 1 (by decide)
    have c5 := hneq' 2 1 0 (by decide)
    have c6 := hneq' 1 1 2 (by decide)
    have c7 := hneq' 1 2 0 (by decide)
    have c8 := hneq 1 0 2 (by decide)
    have c9 := hneq 2 0 2 (by decide)
    have c10 := hneq 1 2 2 (by decide)
    have c11 := hneq' 2 2 0 (by decide)
    have c12 := hneq' 2 1 2 (by decide)
    simp only [h10, h20, h01, h02] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    generalize f 1 1 = x11 at c1 c2 c3 c6 ⊢
    generalize f 1 2 = x12 at c6 c7 c8 c10
    generalize f 2 1 = x21 at c3 c4 c5 c12
    generalize f 2 2 = x22 at c9 c10 c11 c12
    clear hq hw hu hv h00 h10 h01 h20 h02 hneq hneq' f
    revert u v w x11 x12 x21 x22 hu0 hv0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12; decide
  have h12 : f 1 2 = u + 2 * v + w := by
    have c1 := hneq' 1 2 0 (by decide)
    have c2 := hneq' 1 2 1 (by decide)
    rw [h10] at c1; rw [h11] at c2
    generalize f 1 2 = y at c1 c2 ⊢
    clear hq hw hu hv h00 h10 h01 h20 h02 h11 hneq hneq' f
    revert u v w y hu0 hv0 c1 c2; decide
  have h21 : f 2 1 = 2 * u + v + w := by
    have c1 := hneq 2 0 1 (by decide)
    have c2 := hneq 2 1 1 (by decide)
    rw [h01] at c1; rw [h11] at c2
    generalize f 2 1 = y at c1 c2 ⊢
    clear hq hw hu hv h00 h10 h01 h20 h02 h11 h12 hneq hneq' f
    revert u v w y hu0 hv0 c1 c2; decide
  have h22 : f 2 2 = 2 * u + 2 * v + w := by
    have c1 := hneq' 2 2 0 (by decide)
    have c2 := hneq' 2 2 1 (by decide)
    rw [h20] at c1; rw [h21] at c2
    generalize f 2 2 = y at c1 c2 ⊢
    clear hq hw hu hv h00 h10 h01 h20 h02 h11 h12 h21 hneq hneq' f
    revert u v w y hu0 hv0 c1 c2; decide
  have hall : ∀ a b : ZMod 3, f a b = u * a + v * b + w := by
    intro a b; fin_cases a <;> fin_cases b
    · change f 0 0 = u * 0 + v * 0 + w; rw [h00]; ring
    · change f 0 1 = u * 0 + v * 1 + w; rw [h01]; ring
    · change f 0 2 = u * 0 + v * 2 + w; rw [h02]; ring
    · change f 1 0 = u * 1 + v * 0 + w; rw [h10]; ring
    · change f 1 1 = u * 1 + v * 1 + w; rw [h11]; ring
    · change f 1 2 = u * 1 + v * 2 + w; rw [h12]; ring
    · change f 2 0 = u * 2 + v * 0 + w; rw [h20]; ring
    · change f 2 1 = u * 2 + v * 1 + w; rw [h21]; ring
    · change f 2 2 = u * 2 + v * 2 + w; rw [h22]; ring
  have hu12 : u = 1 ∨ u = 2 := by clear hq hw hu hv h00 h10 h01 h20 h02 h11 h12 h21 h22 hall hv0 hneq hneq' f; revert u hu0; decide
  have hv12 : v = 1 ∨ v = 2 := by clear hq hw hu hv h00 h10 h01 h20 h02 h11 h12 h21 h22 hall hu0 hu12 hneq hneq' f; revert v hv0; decide
  exact ⟨u, v, w, hu12, hv12, hall⟩

private lemma quasigroup_lower_bound (S : Type) [Fintype S] (op : S → S → S) (x : S)
    (β : FullBinTree → Bool) (hq : IsQuasigroup op)
    (hcol : ∀ n : ℕ, 3 ≤ n →
      ∀ T₁ T₂ : FullBinTree, T₁.leaves = n - 1 → T₂.leaves = n - 1 →
        RotAdj T₁ T₂ → (evalBinTree op x T₁, β T₁) ≠ (evalBinTree op x T₂, β T₂)) :
    4 ≤ (Set.range (evalBinTree op x)).ncard := by
  classical
  let S' := Set.range (evalBinTree op x)
  have hS'_fin : S'.Finite := Set.toFinite S'
  let _ : Fintype S' := hS'_fin.fintype
  have hncard : S'.ncard = Fintype.card S' := by
    rw [Set.ncard_eq_toFinset_card S' hS'_fin, Set.Finite.card_toFinset]
  rw [hncard]
  -- `S'` is closed under `op`, and `op` restricted to `S'` is a quasigroup!
  have hclosed : ∀ a b : S', op a.val b.val ∈ S' := fun ⟨_, ⟨Ta, rfl⟩⟩ ⟨_, ⟨Tb, rfl⟩⟩ =>
    ⟨.node Ta Tb, rfl⟩
  let op' : S' → S' → S' := fun a b => ⟨op a.val b.val, hclosed a b⟩
  have hq' : IsQuasigroup op' := by
    constructor
    · intro a
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun b₁ b₂ h => ?_, rfl⟩
      exact Subtype.ext ((hq.1 a.val).1 (congrArg Subtype.val h))
    · intro b
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a₁ a₂ h => ?_, rfl⟩
      exact Subtype.ext ((hq.2 b.val).1 (congrArg Subtype.val h))
  by_contra hlt
  have hle3 : Fintype.card S' ≤ 3 := by omega
  have hpos : 0 < Fintype.card S' := Fintype.card_pos_iff.mpr ⟨⟨x, .leaf, rfl⟩⟩
  have hcases : Fintype.card S' = 1 ∨ Fintype.card S' = 2 ∨ Fintype.card S' = 3 := by omega
  rcases hcases with hc1 | hc2 | hc3
  · -- `|S'| = 1`: every triple is associative!
    have hsub : Subsingleton S' := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hall_eq : ∀ T₁ T₂ : FullBinTree, evalBinTree op x T₁ = evalBinTree op x T₂ := fun T₁ T₂ =>
      congrArg Subtype.val (Subsingleton.elim (⟨_, T₁, rfl⟩ : S') ⟨_, T₂, rfl⟩)
    exact pentagon_contra op x β hcol .leaf .leaf .leaf .leaf
      (by simpa [evalBinTree] using hall_eq (.node (.node .leaf .leaf) .leaf) (.node .leaf (.node .leaf .leaf)))
      (by simpa [evalBinTree] using hall_eq (.node (.node .leaf (.node .leaf .leaf)) .leaf) (.node .leaf (.node (.node .leaf .leaf) .leaf)))
      (by simpa [evalBinTree] using hall_eq (.node (.node .leaf .leaf) .leaf) (.node .leaf (.node .leaf .leaf)))
      (by simpa [evalBinTree] using hall_eq (.node .leaf (.node .leaf (.node .leaf .leaf))) (.node (.node .leaf .leaf) (.node .leaf .leaf)))
      (by simpa [evalBinTree] using hall_eq (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node (.node .leaf .leaf) .leaf) .leaf))
  · -- `|S'| = 2`: every quasigroup of order 2 is associative!
    let e2 : Fin 2 ≃ Bool :=
      { toFun := fun i => i.val == 1
        invFun := fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
        left_inv := fun i => by fin_cases i <;> rfl
        right_inv := fun b => by cases b <;> rfl }
    let e : S' ≃ Bool := (Fintype.equivFinOfCardEq hc2).trans e2
    let f : Bool → Bool → Bool := fun a b => e (op' (e.symm a) (e.symm b))
    have hqf : IsQuasigroup f := by
      constructor
      · intro a
        have := (hq'.1 (e.symm a))
        exact e.bijective.comp (this.comp e.symm.bijective)
      · intro b
        have := (hq'.2 (e.symm b))
        exact e.bijective.comp (this.comp e.symm.bijective)
    have hfass : ∀ a b c : Bool, f (f a b) c = f a (f b c) := by
      have hne0 : f false false ≠ f false true := fun h => by have := (hqf.1 false).1 h; cases this
      have hne1 : f true false ≠ f true true := fun h => by have := (hqf.1 true).1 h; cases this
      have hnec0 : f false false ≠ f true false := fun h => by have := (hqf.2 false).1 h; cases this
      have hnec1 : f false true ≠ f true true := fun h => by have := (hqf.2 true).1 h; cases this
      have htable : (f false false = false ∧ f false true = true ∧ f true false = true ∧ f true true = false) ∨
                    (f false false = true ∧ f false true = false ∧ f true false = false ∧ f true true = true) := by
        cases h00 : f false false <;> cases h01 : f false true <;>
        cases h10 : f true false <;> cases h11 : f true true <;>
        simp_all
      intro a b c
      rcases htable with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ <;>
        (cases a <;> cases b <;> cases c <;> simp [h00, h01, h10, h11])
    have hop_ass : ∀ a b c : S', op' (op' a b) c = op' a (op' b c) := fun a b c => by
      apply e.injective
      have := hfass (e a) (e b) (e c)
      simpa [f] using this
    have hass : ∀ T₁ T₂ T₃ : FullBinTree,
        op (op (evalBinTree op x T₁) (evalBinTree op x T₂)) (evalBinTree op x T₃) =
        op (evalBinTree op x T₁) (op (evalBinTree op x T₂) (evalBinTree op x T₃)) := fun T₁ T₂ T₃ =>
      congrArg Subtype.val (hop_ass ⟨_, T₁, rfl⟩ ⟨_, T₂, rfl⟩ ⟨_, T₃, rfl⟩)
    exact pentagon_contra op x β hcol .leaf .leaf .leaf .leaf
      (hass .leaf .leaf .leaf)
      (hass .leaf (.node .leaf .leaf) .leaf)
      (hass .leaf .leaf .leaf)
      (hass .leaf .leaf (.node .leaf .leaf)).symm
      (hass (.node .leaf .leaf) .leaf .leaf).symm
  · -- `|S'| = 3`: identify `S'` with `ZMod 3` and use `quasigroup_zmod3_affine`!
    let e : S' ≃ ZMod 3 := Fintype.equivFinOfCardEq hc3
    let f : ZMod 3 → ZMod 3 → ZMod 3 := fun a b => e (op' (e.symm a) (e.symm b))
    have hqf : IsQuasigroup f := by
      constructor
      · intro a; exact e.bijective.comp ((hq'.1 (e.symm a)).comp e.symm.bijective)
      · intro b; exact e.bijective.comp ((hq'.2 (e.symm b)).comp e.symm.bijective)
    obtain ⟨u, v, w, hu, hv, hf⟩ := quasigroup_zmod3_affine f hqf
    have heval_f : ∀ T : FullBinTree,
        e ⟨evalBinTree op x T, T, rfl⟩ = evalBinTree f (e ⟨x, .leaf, rfl⟩) T := by
      intro T; induction T with
      | leaf => rfl
      | node l r ihl ihr =>
        simp only [evalBinTree, f]
        rw [← ihl, ← ihr, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have heval_eq : ∀ T₁ T₂ : FullBinTree,
        evalBinTree f (e ⟨x, .leaf, rfl⟩) T₁ = evalBinTree f (e ⟨x, .leaf, rfl⟩) T₂ →
        evalBinTree op x T₁ = evalBinTree op x T₂ := fun T₁ T₂ h => by
      have h1 : (⟨evalBinTree op x T₁, T₁, rfl⟩ : S') = ⟨evalBinTree op x T₂, T₂, rfl⟩ :=
        e.injective (by rw [heval_f, heval_f, h])
      exact congrArg Subtype.val h1
    have hreal : ∀ z : ZMod 3, ∃ T : FullBinTree, evalBinTree f (e ⟨x, .leaf, rfl⟩) T = z := fun z => by
      obtain ⟨T, hT⟩ := (e.symm z).prop
      refine ⟨T, ?_⟩
      rw [← heval_f]
      have : (⟨evalBinTree op x T, T, rfl⟩ : S') = e.symm z := Subtype.ext hT
      rw [this, e.apply_symm_apply]
    obtain ⟨Tw, hTw⟩ := hreal w
    have hpass : ∀ a b c : ZMod 3,
        f (f a b) c - f a (f b c) = (1 - u) * a + (v - 1) * c + (u - v) * w := by
      intro a b c
      rw [hf, hf, hf, hf]
      have hu2 : u * u = 1 := by rcases hu with rfl | rfl <;> decide
      have hv2 : v * v = 1 := by rcases hv with rfl | rfl <;> decide
      calc u * (u * a + v * b + w) + v * c + w - (u * a + v * (u * b + v * c + w) + w)
          = (u * u - u) * a + (v - v * v) * c + (u - v) * w := by ring
        _ = (1 - u) * a + (v - 1) * c + (u - v) * w := by rw [hu2, hv2]
    have htri_eq : ∀ T₁ T₂ T₃ : FullBinTree,
        f (f (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₁) (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₂))
          (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₃) =
        f (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₁)
          (f (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₂) (evalBinTree f (e ⟨x, .leaf, rfl⟩) T₃)) →
        op (op (evalBinTree op x T₁) (evalBinTree op x T₂)) (evalBinTree op x T₃) =
        op (evalBinTree op x T₁) (op (evalBinTree op x T₂) (evalBinTree op x T₃)) := fun T₁ T₂ T₃ h =>
      heval_eq (.node (.node T₁ T₂) T₃) (.node T₁ (.node T₂ T₃)) h
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · -- `u = 1, v = 1`: associative everywhere!
      have hass : ∀ a b c : ZMod 3, f (f a b) c = f a (f b c) := fun a b c =>
        sub_eq_zero.mp (by rw [hpass]; ring)
      exact pentagon_contra op x β hcol .leaf .leaf .leaf .leaf
        (htri_eq .leaf .leaf .leaf (hass _ _ _))
        (htri_eq .leaf (.node .leaf .leaf) .leaf (hass _ _ _))
        (htri_eq .leaf .leaf .leaf (hass _ _ _))
        (htri_eq .leaf .leaf (.node .leaf .leaf) (hass _ _ _)).symm
        (htri_eq (.node .leaf .leaf) .leaf .leaf (hass _ _ _)).symm
    · -- `u = 1, v = 2`: associative whenever 3rd entry = `w`; choose `C = E = Tw`!
      have hfww : f w w = w := by rw [hf]; exact (by decide : ∀ z : ZMod 3, 1 * z + 2 * z + z = z) w
      have hass : ∀ a b : ZMod 3, f (f a b) w = f a (f b w) := fun a b =>
        sub_eq_zero.mp (by rw [hpass]; ring)
      exact pentagon_contra op x β hcol .leaf .leaf Tw Tw
        (htri_eq .leaf .leaf Tw (by rw [hTw]; exact hass _ _))
        (htri_eq .leaf (.node .leaf Tw) Tw (by rw [hTw]; exact hass _ _))
        (htri_eq .leaf Tw Tw (by rw [hTw]; exact hass _ _))
        (htri_eq .leaf .leaf (.node Tw Tw) (by change f (f _ _) (f _ _) = f _ (f _ (f _ _)); rw [hTw, hfww]; exact hass _ _)).symm
        (htri_eq (.node .leaf .leaf) Tw Tw (by rw [hTw]; exact hass _ _)).symm
    · -- `u = 2, v = 1`: associative whenever 1st entry = `w`; choose `A = B = Tw`!
      have hfww : f w w = w := by rw [hf]; exact (by decide : ∀ z : ZMod 3, 2 * z + 1 * z + z = z) w
      have hass : ∀ b c : ZMod 3, f (f w b) c = f w (f b c) := fun b c =>
        sub_eq_zero.mp (by rw [hpass]; ring)
      exact pentagon_contra op x β hcol Tw Tw .leaf .leaf
        (htri_eq Tw Tw .leaf (by rw [hTw]; exact hass _ _))
        (htri_eq Tw (.node Tw .leaf) .leaf (by rw [hTw]; exact hass _ _))
        (htri_eq Tw .leaf .leaf (by rw [hTw]; exact hass _ _))
        (htri_eq Tw Tw (.node .leaf .leaf) (by rw [hTw]; exact hass _ _)).symm
        (htri_eq (.node Tw Tw) .leaf .leaf (by change f (f (f _ _) _) _ = f (f _ _) (f _ _); rw [hTw, hfww]; exact hass _ _)).symm
    · -- `u = 2, v = 2`: `f a b = 2 * a + 2 * b + w = -a - b + w`; 9-cycle in `𝒜_6`!
      let t : FullBinTree := .leaf
      let c9 : Fin 9 → FullBinTree
        | ⟨0, _⟩ => .node t (.node t (.node t (.node t t)))
        | ⟨1, _⟩ => .node (.node t t) (.node t (.node t t))
        | ⟨2, _⟩ => .node (.node (.node t t) t) (.node t t)
        | ⟨3, _⟩ => .node (.node (.node (.node t t) t) t) t
        | ⟨4, _⟩ => .node (.node (.node t (.node t t)) t) t
        | ⟨5, _⟩ => .node (.node t (.node (.node t t) t)) t
        | ⟨6, _⟩ => .node t (.node (.node (.node t t) t) t)
        | ⟨7, _⟩ => .node t (.node (.node t (.node t t)) t)
        | ⟨8, _⟩ => .node t (.node t (.node (.node t t) t))
      have hf2 : ∀ a b : ZMod 3, f a b = 2 * a + 2 * b + w := hf
      have heval_c9 : ∀ i : Fin 9, evalBinTree f (e ⟨x, .leaf, rfl⟩) (c9 i) =
          e ⟨x, .leaf, rfl⟩ := by
        have hstep1 : ∀ a w : ZMod 3,
            2 * a + 2 * (2 * a + 2 * (2 * a + 2 * (2 * a + 2 * a + w) + w) + w) + w = a := by decide
        have hstep2 : ∀ a w : ZMod 3,
            2 * (2 * a + 2 * a + w) + 2 * (2 * a + 2 * (2 * a + 2 * a + w) + w) + w = a := by decide
        have hstep3 : ∀ a w : ZMod 3,
            2 * (2 * (2 * a + 2 * a + w) + 2 * a + w) + 2 * (2 * a + 2 * a + w) + w = a := by decide
        have hstep4 : ∀ a w : ZMod 3,
            2 * (2 * (2 * (2 * a + 2 * a + w) + 2 * a + w) + 2 * a + w) + 2 * a + w = a := by decide
        have hstep5 : ∀ a w : ZMod 3,
            2 * (2 * (2 * a + 2 * (2 * a + 2 * a + w) + w) + 2 * a + w) + 2 * a + w = a := by decide
        have hstep6 : ∀ a w : ZMod 3,
            2 * (2 * a + 2 * (2 * (2 * a + 2 * a + w) + 2 * a + w) + w) + 2 * a + w = a := by decide
        have hstep7 : ∀ a w : ZMod 3,
            2 * a + 2 * (2 * (2 * (2 * a + 2 * a + w) + 2 * a + w) + 2 * a + w) + w = a := by decide
        have hstep8 : ∀ a w : ZMod 3,
            2 * a + 2 * (2 * (2 * a + 2 * (2 * a + 2 * a + w) + w) + 2 * a + w) + w = a := by decide
        have hstep9 : ∀ a w : ZMod 3,
            2 * a + 2 * (2 * a + 2 * (2 * (2 * a + 2 * a + w) + 2 * a + w) + w) + w = a := by decide
        intro i
        rcases i with ⟨i, hi⟩
        interval_cases i
        · simp only [c9, t, evalBinTree, hf2]; exact hstep1 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep2 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep3 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep4 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep5 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep6 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep7 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep8 _ _
        · simp only [c9, t, evalBinTree, hf2]; exact hstep9 _ _
      refine no_odd_cycle_same_label op x β hcol (m := 4) c9 (by simp [c9, t, FullBinTree.leaves]) ?_
      intro i
      refine ⟨?_, heval_eq _ _ (by rw [heval_c9, heval_c9])⟩
      fin_cases i
      · exact .rotLeft t t (.node t (.node t t))
      · exact .rotLeft (.node t t) t (.node t t)
      · exact .rotLeft (.node (.node t t) t) t t
      · exact .inLeft (.inLeft (.rotRight t t t))
      · exact .inLeft (.rotRight t (.node t t) t)
      · exact .rotRight t (.node (.node t t) t) t
      · exact .inRight (.inLeft (.rotRight t t t))
      · exact .inRight (.rotRight t (.node t t) t)
      · exact .inRight (.inRight (.rotRight t t t))

theorem main_proof : type_of% @OMA.S_arxiv_2611_19659.main := by
  refine ⟨triangulation_8_colorable, ?_, quasigroup_lower_bound⟩
  intro n _
  exact ⟨fun T => treeColor T.val, fun T₁ T₂ hadj => treeColor_ne_of_rotAdj hadj⟩

end OMA.P_arxiv_2611_19659

theorem OMA.solution : type_of% @OMA.S_arxiv_2611_19659.main :=
  OMA.P_arxiv_2611_19659.main_proof
