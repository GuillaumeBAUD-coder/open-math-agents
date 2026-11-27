import OMAReductions.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic

/-!
# Wolf (1968): Finitely Generated Nilpotent Groups Have Polynomial Growth

Elementary inductive proof along the upper central series of `G` establishing
`OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1.H2`.
-/

open scoped commutatorElement

private def delta {G : Type*} [Group G] (y u : G) : G := ⁅u⁻¹, y⁻¹⁆

private lemma mul_delta {G : Type*} [Group G] (y u : G) :
    y⁻¹ * u * y = u * delta y u := by
  unfold delta
  rw [commutatorElement_def]
  group

private lemma delta_mem_upperCentralSeries {G : Type*} [Group G] {k : ℕ} {y u : G}
    (hu : u ∈ Subgroup.upperCentralSeries G (k + 1)) :
    delta y u ∈ Subgroup.upperCentralSeries G k :=
  Subgroup.mem_upperCentralSeries_succ_iff.mp (inv_mem hu) y⁻¹

private lemma conj_succ_eq {G : Type*} [Group G] (y u : G) (t : ℕ) :
    (y⁻¹) ^ (t + 1) * u * y ^ (t + 1) =
      ((y⁻¹) ^ t * u * y ^ t) * ((y⁻¹) ^ t * delta y u * y ^ t) := by
  have hip : (y⁻¹) ^ t = (y ^ t)⁻¹ := by simp
  rw [pow_succ (y⁻¹) t, pow_succ' y t, hip]
  calc (y ^ t)⁻¹ * y⁻¹ * u * (y * y ^ t)
      = (y ^ t)⁻¹ * (y⁻¹ * u * y) * y ^ t := by group
    _ = (y ^ t)⁻¹ * (u * delta y u) * y ^ t := by rw [mul_delta y u]
    _ = ((y ^ t)⁻¹ * u * y ^ t) * ((y ^ t)⁻¹ * delta y u * y ^ t) := by group

private lemma conj_pow_word {G : Type*} [Group G] [DecidableEq G] (y : G) :
    ∀ (k : ℕ) (U : Finset G),
      (∀ u ∈ U, u ∈ Subgroup.upperCentralSeries G k) →
      ∃ W : Finset G,
        (∀ w ∈ W, w ∈ Subgroup.upperCentralSeries G (k - 1)) ∧
        ∀ u ∈ U, ∀ t : ℕ,
          ∃ l : List G,
            l.length ≤ t * (t + 1) ^ k ∧
            (∀ x ∈ l, x ∈ W) ∧
            (y⁻¹) ^ t * u * y ^ t = u * l.prod := by
  intro k
  induction k with
  | zero =>
    intro U hU
    refine ⟨∅, by simp, ?_⟩
    intro u hu t
    have hu0 : u ∈ Subgroup.upperCentralSeries G 0 := hU u hu
    rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hu0
    subst hu0
    refine ⟨[], by simp, by simp, ?_⟩
    have hip : (y⁻¹) ^ t = (y ^ t)⁻¹ := by simp
    rw [List.prod_nil, hip]
    group
  | succ k ih =>
    intro U hU
    let U₁ : Finset G := U.image (delta y)
    have hU₁ : ∀ w ∈ U₁, w ∈ Subgroup.upperCentralSeries G k := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact delta_mem_upperCentralSeries (hU u hu)
    obtain ⟨W₁, hW₁_mem, hW₁_conj⟩ := ih U₁ hU₁
    let W : Finset G := U₁ ∪ W₁
    have hW_mem : ∀ w ∈ W, w ∈ Subgroup.upperCentralSeries G k := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw1 | hw2
      · exact hU₁ w hw1
      · exact Subgroup.upperCentralSeries_mono G (Nat.sub_le k 1) (hW₁_mem w hw2)
    refine ⟨W, hW_mem, ?_⟩
    intro u hu t
    induction t with
    | zero =>
      exact ⟨[], by simp, by simp, by simp⟩
    | succ t iht =>
      obtain ⟨l₁, hl₁_len, hl₁_mem, hl₁_prod⟩ := iht
      have hdu_mem : delta y u ∈ U₁ := Finset.mem_image_of_mem (delta y) hu
      obtain ⟨l₂, hl₂_len, hl₂_mem, hl₂_prod⟩ := hW₁_conj (delta y u) hdu_mem t
      refine ⟨l₁ ++ (delta y u :: l₂), ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_cons]
        have h1_le : 1 ≤ (t + 1) ^ k := Nat.one_le_pow k (t + 1) (by omega)
        have hstep1 : l₁.length + (l₂.length + 1) ≤
            t * (t + 1) ^ (k + 1) + (t + 1) * (t + 1) ^ k := by
          have hexp1 : (t + 1) * (t + 1) ^ k = t * (t + 1) ^ k + 1 * (t + 1) ^ k := by ring
          omega
        have hstep2 : t * (t + 1) ^ (k + 1) + (t + 1) * (t + 1) ^ k =
            (t + 1) * (t + 1) ^ (k + 1) := by ring
        have hstep3 : (t + 1) * (t + 1) ^ (k + 1) ≤ (t + 1) * (t + 1 + 1) ^ (k + 1) :=
          Nat.mul_le_mul_left (t + 1) (Nat.pow_le_pow_left (by omega) (k + 1))
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hl₁_mem x hx1
        · rcases List.mem_cons.mp hx2 with rfl | hx3
          · exact Finset.mem_union_left W₁ hdu_mem
          · exact Finset.mem_union_right U₁ (hl₂_mem x hx3)
      · rw [conj_succ_eq y u t, hl₁_prod, hl₂_prod, List.prod_append, List.prod_cons]
        group

private lemma pull_letter_front {G : Type*} [Group G] {y : G} {U₀ B : Finset G} {K : ℕ}
    (hcomm : ∀ z ∈ U₀, ∀ t : ℕ,
      ∃ wz : List G, wz.length ≤ (t + 1) ^ K ∧ (∀ x ∈ wz, x ∈ B) ∧ z * y ^ t = y ^ t * wz.prod) :
    ∀ l : List G, (∀ x ∈ l, x = y ∨ x ∈ U₀) →
      ∃ (t : ℕ) (w : List G),
        t ≤ l.length ∧
        w.length ≤ l.length * (l.length + 1) ^ K ∧
        (∀ x ∈ w, x ∈ B) ∧
        l.prod = y ^ t * w.prod := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨0, [], le_rfl, by simp, by simp, by simp⟩
  | cons a l' ih =>
    intro hl
    obtain ⟨t, w', ht_le, hw'_len, hw'_mem, hw'_prod⟩ :=
      ih (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
    rcases hl a (List.mem_cons.mpr (Or.inl rfl)) with rfl | haU
    · refine ⟨t + 1, w', ?_, ?_, hw'_mem, ?_⟩
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        calc w'.length
            ≤ l'.length * (l'.length + 1) ^ K := hw'_len
          _ ≤ (l'.length + 1) * (l'.length + 1 + 1) ^ K :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) K)
      · rw [List.prod_cons, hw'_prod, ← mul_assoc, ← pow_succ' a t]
    · obtain ⟨wa, hwa_len, hwa_mem, hwa_prod⟩ := hcomm a haU t
      refine ⟨t, wa ++ w', ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons, List.length_append]
        have hwa_le : wa.length ≤ (l'.length + 1 + 1) ^ K :=
          hwa_len.trans (Nat.pow_le_pow_left (by omega) K)
        have hw'_le : w'.length ≤ l'.length * (l'.length + 1 + 1) ^ K :=
          hw'_len.trans (Nat.mul_le_mul_left l'.length (Nat.pow_le_pow_left (by omega) K))
        have hsum_eq : (l'.length + 1 + 1) ^ K + l'.length * (l'.length + 1 + 1) ^ K =
            (l'.length + 1) * (l'.length + 1 + 1) ^ K := by ring
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hwa_mem x hx1
        · exact hw'_mem x hx2
      · rw [List.prod_cons, hw'_prod, ← mul_assoc, hwa_prod, mul_assoc, List.prod_append]

private def wordBall {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => wordBall A n ∪ (A ×ˢ wordBall A n).image (fun p => p.1 * p.2)

private lemma one_mem_wordBall {G : Type*} [Group G] [DecidableEq G] (A : Finset G) :
    ∀ n : ℕ, (1 : G) ∈ wordBall A n
  | 0 => Finset.mem_singleton_self 1
  | n + 1 => Finset.mem_union_left _ (one_mem_wordBall A n)

private lemma mem_wordBall_iff {G : Type*} [Group G] [DecidableEq G] (A : Finset G) :
    ∀ (n : ℕ) (g : G),
      g ∈ wordBall A n ↔ ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ A) ∧ l.prod = g := by
  intro n
  induction n with
  | zero =>
    intro g
    constructor
    · intro hg
      rw [wordBall, Finset.mem_singleton] at hg
      exact ⟨[], le_rfl, by simp, hg.symm⟩
    · rintro ⟨l, hl_len, _, rfl⟩
      cases l with
      | nil => exact Finset.mem_singleton_self 1
      | cons _ _ => simp at hl_len
  | succ n ih =>
    intro g
    constructor
    · intro hg
      rw [wordBall] at hg
      rcases Finset.mem_union.mp hg with hg1 | hg2
      · obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := (ih g).mp hg1
        exact ⟨l, Nat.le_succ_of_le hl_len, hl_mem, hl_prod⟩
      · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hg2
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        obtain ⟨l, hl_len, hl_mem, rfl⟩ := (ih b).mp hb
        refine ⟨a :: l, Nat.succ_le_succ hl_len, ?_, List.prod_cons⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact ha
        · exact hl_mem x hxl
    · rintro ⟨l, hl_len, hl_mem, rfl⟩
      cases l with
      | nil =>
        simpa using one_mem_wordBall A (n + 1)
      | cons a l' =>
        rw [wordBall]
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(a, l'.prod), Finset.mem_product.mpr ⟨hl_mem a (List.mem_cons.mpr (Or.inl rfl)), ?_⟩,
          List.prod_cons.symm⟩
        apply (ih l'.prod).mpr
        refine ⟨l', ?_, fun x hx => hl_mem x (List.mem_cons.mpr (Or.inr hx)), rfl⟩
        simp only [List.length_cons] at hl_len
        omega

private lemma list_prod_eq_one {G : Type*} [Group G] :
    ∀ l : List G, (∀ x ∈ l, x = (1 : G)) → l.prod = 1
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons, hl a (List.mem_cons.mpr (Or.inl rfl)),
      list_prod_eq_one l (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx))), mul_one]

private lemma wordBall_poly_upperCentralSeries {G : Type*} [Group G] [DecidableEq G] :
    ∀ (r : ℕ) (T : Finset G),
      (∀ x ∈ T, x ∈ Subgroup.upperCentralSeries G r) →
      ∃ C d : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (wordBall T n).card ≤ C * n ^ d := by
  intro r
  induction r with
  | zero =>
    intro T hT
    refine ⟨1, 0, le_rfl, ?_⟩
    intro n _
    have hsub : wordBall T n ⊆ {1} := by
      intro g hg
      obtain ⟨l, _, hl_mem, rfl⟩ := (mem_wordBall_iff T n g).mp hg
      have hl1 : ∀ x ∈ l, x = (1 : G) := by
        intro x hx
        have hx0 := hT x (hl_mem x hx)
        rwa [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hx0
      rw [list_prod_eq_one l hl1]
      exact Finset.mem_singleton_self 1
    calc (wordBall T n).card
        ≤ ({1} : Finset G).card := Finset.card_le_card hsub
      _ = 1 * n ^ 0 := by simp
  | succ r ih_r =>
    have h_inner : ∀ s : Finset G,
        (∀ x ∈ s, x ∈ Subgroup.upperCentralSeries G (r + 1)) →
        ∀ V : Finset G, (∀ v ∈ V, v ∈ Subgroup.upperCentralSeries G r) →
        ∃ C d : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (wordBall (s ∪ V) n).card ≤ C * n ^ d := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ V hV
        simpa using ih_r V hV
      | insert y s' _ ih_s =>
        intro hs V hV
        have hs' : ∀ x ∈ s', x ∈ Subgroup.upperCentralSeries G (r + 1) :=
          fun x hx => hs x (Finset.mem_insert_of_mem hx)
        let U₀ : Finset G := s' ∪ V
        have hU₀ : ∀ z ∈ U₀, z ∈ Subgroup.upperCentralSeries G (r + 1) := by
          intro z hz
          rcases Finset.mem_union.mp hz with hzs | hzv
          · exact hs' z hzs
          · exact Subgroup.upperCentralSeries_mono G (Nat.le_succ r) (hV z hzv)
        obtain ⟨W, hW_mem, hW_conj⟩ := conj_pow_word y (r + 1) U₀ hU₀
        let V' : Finset G := V ∪ W
        have hV' : ∀ v ∈ V', v ∈ Subgroup.upperCentralSeries G r := by
          intro v hv
          rcases Finset.mem_union.mp hv with hvv | hvw
          · exact hV v hvv
          · exact hW_mem v hvw
        obtain ⟨C', d', hC'1, hBound'⟩ := ih_s hs' V' hV'
        let B : Finset G := s' ∪ V'
        let K : ℕ := r + 2
        have hcomm : ∀ z ∈ U₀, ∀ t : ℕ,
            ∃ wz : List G, wz.length ≤ (t + 1) ^ K ∧ (∀ x ∈ wz, x ∈ B) ∧
              z * y ^ t = y ^ t * wz.prod := by
          intro z hz t
          obtain ⟨lz, hlz_len, hlz_mem, hlz_prod⟩ := hW_conj z hz t
          refine ⟨z :: lz, ?_, ?_, ?_⟩
          · simp only [List.length_cons]
            have h1_le : 1 ≤ (t + 1) ^ (r + 1) := Nat.one_le_pow (r + 1) (t + 1) (by omega)
            have hexp : (t + 1) ^ K = t * (t + 1) ^ (r + 1) + 1 * (t + 1) ^ (r + 1) := by
              dsimp [K]
              ring
            omega
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hxl
            · rcases Finset.mem_union.mp hz with hzs | hzv
              · exact Finset.mem_union_left V' hzs
              · exact Finset.mem_union_right s' (Finset.mem_union_left W hzv)
            · exact Finset.mem_union_right s' (Finset.mem_union_right V (hlz_mem x hxl))
          · rw [List.prod_cons, ← hlz_prod]
            have hip : (y⁻¹) ^ t = (y ^ t)⁻¹ := by simp
            rw [hip]
            group
        let C : ℕ := 2 * C' * (2 ^ K) ^ d'
        let d : ℕ := (K + 1) * d' + 1
        have hC1 : 1 ≤ C := by
          dsimp [C]
          have hpow1 : 1 ≤ (2 ^ K) ^ d' :=
            Nat.one_le_pow d' (2 ^ K) (Nat.one_le_pow K 2 (by omega))
          exact Nat.mul_pos (by omega) hpow1
        refine ⟨C, d, hC1, ?_⟩
        intro n hn
        let R_n : ℕ := 2 ^ K * n ^ (K + 1)
        have hRn1 : 1 ≤ R_n :=
          Nat.mul_pos (Nat.one_le_pow K 2 (by omega)) (Nat.one_le_pow (K + 1) n hn)
        have hsub : wordBall (insert y s' ∪ V) n ⊆
            (Finset.range (n + 1) ×ˢ wordBall B R_n).image (fun p => y ^ p.1 * p.2) := by
          intro g hg
          obtain ⟨l, hl_len, hl_mem, rfl⟩ := (mem_wordBall_iff _ n g).mp hg
          have hl_split : ∀ x ∈ l, x = y ∨ x ∈ U₀ := by
            intro x hx
            rcases Finset.mem_union.mp (hl_mem x hx) with hxs | hxv
            · rcases Finset.mem_insert.mp hxs with rfl | hxs'
              · exact Or.inl rfl
              · exact Or.inr (Finset.mem_union_left V hxs')
            · exact Or.inr (Finset.mem_union_right s' hxv)
          obtain ⟨t, w, ht_le, hw_len, hw_mem, hw_prod⟩ := pull_letter_front hcomm l hl_split
          rw [hw_prod]
          apply Finset.mem_image.mpr
          refine ⟨(t, w.prod), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, rfl⟩
          apply (mem_wordBall_iff B R_n w.prod).mpr
          refine ⟨w, ?_, hw_mem, rfl⟩
          have hw_le_n : w.length ≤ n * (n + 1) ^ K :=
            hw_len.trans (Nat.mul_le_mul hl_len (Nat.pow_le_pow_left (by omega) K))
          have hn1_le : (n + 1) ^ K ≤ (2 * n) ^ K :=
            Nat.pow_le_pow_left (by omega) K
          have h2n_eq : n * (2 * n) ^ K = R_n := by
            dsimp [R_n]
            rw [mul_pow 2 n K]
            ring
          exact hw_le_n.trans ((Nat.mul_le_mul_left n hn1_le).trans h2n_eq.le)
        calc (wordBall (insert y s' ∪ V) n).card
            ≤ ((Finset.range (n + 1) ×ˢ wordBall B R_n).image (fun p => y ^ p.1 * p.2)).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.range (n + 1) ×ˢ wordBall B R_n).card := Finset.card_image_le
          _ = (n + 1) * (wordBall B R_n).card := by
              rw [Finset.card_product, Finset.card_range]
          _ ≤ (2 * n) * (C' * R_n ^ d') :=
              Nat.mul_le_mul (by omega) (hBound' R_n hRn1)
          _ = C * n ^ d := by
              dsimp [C, d, R_n]
              rw [mul_pow (2 ^ K) (n ^ (K + 1)) d', ← pow_mul n (K + 1) d',
                pow_succ n ((K + 1) * d')]
              ring
    intro T hT
    simpa using h_inner T hT ∅ (by simp)

theorem prove_gromov_H2 : OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1.H2 := by
  intro G _ hfg hnil
  classical
  obtain ⟨S, hS_cl, hS_fin⟩ := Group.fg_iff.mp hfg
  obtain ⟨c, hc_top⟩ := hnil.nilpotent'
  let S_fin : Finset G := hS_fin.toFinset
  let A₀ : Finset G := S_fin ∪ S_fin.image (·⁻¹)
  have hA₀_mem : ∀ x ∈ A₀, x ∈ Subgroup.upperCentralSeries G c := by
    intro x _
    rw [hc_top]
    exact Subgroup.mem_top x
  obtain ⟨C, d, hC1, hCard⟩ := wordBall_poly_upperCentralSeries c A₀ hA₀_mem
  have hC_pos : 0 < C := by omega
  refine ⟨S, hS_fin, hS_cl, (C : ℝ), d, by exact_mod_cast hC_pos, ?_⟩
  intro n hn
  have hsub : GromovPolynomialGrowth.CayleyBall S n ⊆ (wordBall A₀ n : Set G) := by
    intro g hg
    obtain ⟨l, hl_len, hl_S, rfl⟩ := hg
    rw [Finset.mem_coe, mem_wordBall_iff]
    refine ⟨l, hl_len, ?_, rfl⟩
    intro x hx
    rcases hl_S x hx with hxS | hxinvS
    · exact Finset.mem_union_left _ (hS_fin.mem_toFinset.mpr hxS)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x⁻¹, hS_fin.mem_toFinset.mpr hxinvS, inv_inv x⟩
  have hncard : GromovPolynomialGrowth.GrowthFunction S n ≤ C * n ^ d := by
    calc GromovPolynomialGrowth.GrowthFunction S n
        = (GromovPolynomialGrowth.CayleyBall S n).ncard := rfl
      _ ≤ (wordBall A₀ n : Set G).ncard :=
          Set.ncard_le_ncard hsub (wordBall A₀ n).finite_toSet
      _ = (wordBall A₀ n).card := Set.ncard_coe_finset (wordBall A₀ n)
      _ ≤ C * n ^ d := hCard n (by omega)
  exact_mod_cast hncard

theorem OMA.solution : OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1.H2 :=
  prove_gromov_H2
