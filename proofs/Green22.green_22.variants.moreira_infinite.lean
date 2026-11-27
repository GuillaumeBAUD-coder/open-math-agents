import FormalConjectures.GreensOpenProblems.«22»
import Mathlib.Combinatorics.HalesJewett

/-!
Elementary proof of Moreira's theorem on monochromatic `{x, x + y, x * y}`
(Green's Open Problem 22, variant `moreira_infinite`), following Section 4 of
Moreira (2017) using piecewise syndetic sets and the Hales-Jewett theorem.

Credit: @kDylanHayes.
-/

open Finset Filter

namespace OMA

/-- A subset of `ℕ` is piecewise syndetic if there is a gap bound `b > 0` such that
arbitrarily long intervals are covered by `⋃_{t < b} (E - t)`. -/
private def IsPWS (E : Set ℕ) : Prop :=
  ∃ b > 0, ∀ L : ℕ, ∃ a : ℕ, ∀ j < L, ∃ t < b, a + j + t ∈ E

private lemma IsPWS.not_empty : ¬ IsPWS (∅ : Set ℕ) := by
  rintro ⟨b, _, h⟩
  obtain ⟨a, ha⟩ := h 1
  obtain ⟨t, _, ht⟩ := ha 0 (by omega)
  exact ht

private lemma IsPWS.infinite {E : Set ℕ} (hE : IsPWS E) : E.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro K
  obtain ⟨b, _, h⟩ := hE
  obtain ⟨a, ha⟩ := h (K + 2)
  obtain ⟨t, _, ht⟩ := ha (K + 1) (by omega)
  exact ⟨a + (K + 1) + t, ht, by omega⟩

private lemma IsPWS.mono {E H : Set ℕ} (hE : IsPWS E) (hEH : E ⊆ H) : IsPWS H := by
  obtain ⟨b, hb, h⟩ := hE
  exact ⟨b, hb, fun L => by
    obtain ⟨a, ha⟩ := h L
    exact ⟨a, fun j hj => by
      obtain ⟨t, ht, hmem⟩ := ha j hj
      exact ⟨t, ht, hEH hmem⟩⟩⟩

private lemma IsPWS.Ici (k : ℕ) : IsPWS (Set.Ici k) := by
  refine ⟨1, by omega, fun L => ⟨k, fun j _ => ⟨0, by omega, ?_⟩⟩⟩
  change k ≤ k + j + 0
  omega

private lemma IsPWS.union {E₁ E₂ : Set ℕ} (h : IsPWS (E₁ ∪ E₂)) : IsPWS E₁ ∨ IsPWS E₂ := by
  by_cases h₁ : IsPWS E₁
  · exact Or.inl h₁
  · right
    obtain ⟨b, hb, hU⟩ := h
    refine ⟨b, hb, fun L => ?_⟩
    have hnot : ¬ ∀ K : ℕ, ∃ a : ℕ, ∀ j < K, ∃ t < L + b, a + j + t ∈ E₁ :=
      fun h' => h₁ ⟨L + b, by omega, h'⟩
    push Not at hnot
    obtain ⟨K, hK⟩ := hnot
    obtain ⟨a, ha⟩ := hU (K + L)
    obtain ⟨j, hj, hE₁⟩ := hK a
    refine ⟨a + j, fun i hi => ?_⟩
    obtain ⟨t, ht, hmem⟩ := ha (j + i) (by omega)
    rcases hmem with h1 | h2
    · exfalso
      have := hE₁ (i + t) (by omega)
      have heq : a + j + (i + t) = a + (j + i) + t := by omega
      rw [heq] at this
      exact this h1
    · refine ⟨t, ht, ?_⟩
      have heq : a + j + i + t = a + (j + i) + t := by omega
      rw [heq]
      exact h2

private lemma IsPWS.iUnion_fin : ∀ {r : ℕ} {E : Fin r → Set ℕ},
    IsPWS (⋃ i : Fin r, E i) → ∃ i : Fin r, IsPWS (E i)
  | 0, _, h => by
    exfalso
    exact IsPWS.not_empty (by simpa using h)
  | r + 1, E, h => by
    have hunion : (⋃ i : Fin (r + 1), E i) = E 0 ∪ (⋃ i : Fin r, E i.succ) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        exact Fin.cases Or.inl (fun j hj => Or.inr ⟨j, hj⟩) i hi
      · rintro (h0 | ⟨j, hj⟩)
        · exact ⟨0, h0⟩
        · exact ⟨j.succ, hj⟩
    rw [hunion] at h
    rcases IsPWS.union h with h0 | hrest
    · exact ⟨0, h0⟩
    · obtain ⟨j, hj⟩ := IsPWS.iUnion_fin hrest
      exact ⟨j.succ, hj⟩

private lemma IsPWS.partition {E : Set ℕ} {r : ℕ} (hE : IsPWS E) (c : ℕ → Fin r) :
    ∃ t : Fin r, IsPWS (E ∩ c ⁻¹' {t}) := by
  have hcov : E = ⋃ t : Fin r, (E ∩ c ⁻¹' {t}) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨c x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  rw [hcov] at hE
  exact IsPWS.iUnion_fin hE

private lemma IsPWS.mul_left {E : Set ℕ} {d : ℕ} (hE : IsPWS E) (hd : 0 < d) :
    IsPWS ((d * ·) '' E) := by
  obtain ⟨b, hb, h⟩ := hE
  refine ⟨d * (b + 1), Nat.mul_pos hd (Nat.succ_pos b), fun L => ?_⟩
  obtain ⟨a, ha⟩ := h (L + 2)
  refine ⟨d * a, fun j hj => ?_⟩
  have hq : j / d + 1 < L + 2 := by
    have := Nat.div_le_self j d
    omega
  obtain ⟨t, ht, hmem⟩ := ha (j / d + 1) hq
  refine ⟨(d - j % d) + d * t, ?_, ?_⟩
  · have hmul : d * t + d ≤ d * b := by
      calc d * t + d = d * (t + 1) := by ring
        _ ≤ d * b := Nat.mul_le_mul_left d ht
    have hmul2 : d * b + d = d * (b + 1) := by ring
    omega
  · refine ⟨a + (j / d + 1) + t, hmem, ?_⟩
    have hdiv := Nat.div_add_mod j d
    have hmod : j % d < d := Nat.mod_lt j hd
    zify [le_of_lt hmod]
    zify at hdiv
    linarith

/-- Finitary Van der Waerden theorem deduced from Mathlib's Hales-Jewett theorem. -/
private lemma finitary_vdw (b M : ℕ) (_hb : 0 < b) :
    ∃ W > 0, ∀ C : ℕ → Fin b, ∃ a n : ℕ, ∃ c : Fin b,
      0 < n ∧ n < W ∧ a + M * n < W ∧ ∀ m ≤ M, C (a + m * n) = c := by
  classical
  obtain ⟨ι, hfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin (M + 1)) (Fin b)
  refine ⟨(M + 1) * Fintype.card ι + 1, by omega, fun C => ?_⟩
  obtain ⟨l, c, hl⟩ := hι (fun v : ι → Fin (M + 1) => C (∑ i : ι, (v i : ℕ)))
  let s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  have hs_pos : 0 < s.card :=
    Finset.card_pos.mpr ⟨l.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  let a : ℕ := ∑ i ∈ sᶜ, ((l.idxFun i).map (fun x : Fin (M + 1) => (x : ℕ))).getD 0
  have hsum_eq : ∀ m : Fin (M + 1), a + (m : ℕ) * s.card = ∑ i : ι, (l m i : ℕ) := by
    intro m
    rw [← Finset.sum_add_sum_compl s, add_comm (∑ i ∈ s, (l m i : ℕ))]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hne : l.idxFun i ≠ none := by
        simpa [s, Finset.mem_compl, Finset.mem_filter] using hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hne
      have hli : l m i = y := by
        change (l.idxFun i).getD m = y
        rw [hy]
        rfl
      rw [hy, hli]
      rfl
    · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro i hi
      have hnone : l.idxFun i = none := (Finset.mem_filter.mp hi).2
      rw [l.apply_none m i hnone]
  have hbound : ∀ m : Fin (M + 1), a + (m : ℕ) * s.card ≤ M * Fintype.card ι := by
    intro m
    rw [hsum_eq m]
    calc ∑ i : ι, (l m i : ℕ)
        ≤ ∑ _i : ι, M := Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (l m i).isLt
      _ = Fintype.card ι * M := by simp
      _ = M * Fintype.card ι := mul_comm _ _
  refine ⟨a, s.card, c, hs_pos, ?_, ?_, ?_⟩
  · have hle : s.card ≤ Fintype.card ι := Finset.card_le_univ s
    have hmul : Fintype.card ι ≤ (M + 1) * Fintype.card ι := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hM := hbound ⟨M, Nat.lt_succ_self M⟩
    dsimp only at hM
    have hmul : M * Fintype.card ι ≤ (M + 1) * Fintype.card ι :=
      Nat.mul_le_mul_right _ (Nat.le_succ M)
    omega
  · intro m hm
    have h1 := hsum_eq ⟨m, Nat.lt_succ_of_le hm⟩
    have h2 := hl ⟨m, Nat.lt_succ_of_le hm⟩
    change C (∑ i : ι, (l ⟨m, Nat.lt_succ_of_le hm⟩ i : ℕ)) = c at h2
    rw [← h1] at h2
    exact h2

/-- Piecewise syndetic Van der Waerden theorem (Bergelson-Hindman 2001, Theorem 4.5). -/
private lemma IsPWS.vdw_shift {E : Set ℕ} (hE : IsPWS E) (M : ℕ) :
    ∃ n > 0, IsPWS {x : ℕ | ∀ m ≤ M, x + m * n ∈ E} := by
  classical
  obtain ⟨b, hb, hEb⟩ := hE
  obtain ⟨W, hW, hvdw⟩ := finitary_vdw b M hb
  let S : ℕ → Set ℕ := fun n => {x : ℕ | ∀ m ≤ M, x + m * n ∈ E}
  let T : Fin W → Set ℕ := fun n => if 0 < (n : ℕ) then S n else ∅
  have hU : IsPWS (⋃ n : Fin W, T n) := by
    refine ⟨W + b, by omega, fun L => ?_⟩
    obtain ⟨a₀, ha₀⟩ := hEb (L + W)
    refine ⟨a₀, fun j hj => ?_⟩
    let P : ℕ → Prop := fun u => ∃ t < b, a₀ + j + u + t ∈ E
    let C : ℕ → Fin b := fun u =>
      if h : P u then ⟨Nat.find h, (Nat.find_spec h).1⟩ else ⟨0, hb⟩
    have hC_mem : ∀ u < W, a₀ + j + u + (C u : ℕ) ∈ E := by
      intro u hu
      have hPu : P u := by
        obtain ⟨t, ht, hmem⟩ := ha₀ (j + u) (by omega)
        refine ⟨t, ht, ?_⟩
        have heq : a₀ + j + u + t = a₀ + (j + u) + t := by omega
        rw [heq]
        exact hmem
      simp only [C, dif_pos hPu]
      exact (Nat.find_spec hPu).2
    obtain ⟨a, n, c, hn_pos, hn_lt, hamn_lt, hmono⟩ := hvdw C
    refine ⟨a + (c : ℕ), ?_, ?_⟩
    · have ha_lt : a < W := by
        have : a ≤ a + M * n := Nat.le_add_right _ _
        omega
      have hc_lt : (c : ℕ) < b := c.isLt
      omega
    · rw [Set.mem_iUnion]
      refine ⟨⟨n, hn_lt⟩, ?_⟩
      simp only [T, if_pos hn_pos, S]
      intro m hm
      have hmu : a + m * n < W := by
        have : m * n ≤ M * n := Nat.mul_le_mul_right n hm
        omega
      have hmem := hC_mem (a + m * n) hmu
      rw [hmono m hm] at hmem
      have heq : a₀ + j + (a + (c : ℕ)) + m * n = a₀ + j + (a + m * n) + (c : ℕ) := by omega
      rw [heq]
      exact hmem
  obtain ⟨n, hn⟩ := IsPWS.iUnion_fin hU
  by_cases hpos : 0 < (n : ℕ)
  · simp only [T, if_pos hpos] at hn
    exact ⟨n, hpos, hn⟩
  · simp only [T, if_neg hpos] at hn
    exact absurd hn IsPWS.not_empty

private structure MoreiraState (r : ℕ) (c : ℕ → Fin r) (k : ℕ) where
  B : Fin (k + 1) → Set ℕ
  t : Fin (k + 1) → Fin r
  y : Fin k → ℕ
  hy : ∀ i, 0 < y i
  hB_pws : ∀ i, IsPWS (B i)
  hB_pos : ∀ i x, x ∈ B i → 0 < x
  hB_col : ∀ i x, x ∈ B i → c x = t i
  hB_step : ∀ (i : Fin k) x, x ∈ B i.succ →
    ∃ d ∈ B i.castSucc, x = y i * d ∧
      ∀ j : Fin (i.1 + 1),
        d + (∏ l : Fin k with j.1 ≤ l.1 ∧ l.1 < i.1, y l) ^ 2 * y i ∈ B i.castSucc

private lemma moreira_state_exists (r : ℕ) (hr : 0 < r) (c : ℕ → Fin r) :
    ∀ k : ℕ, Nonempty (MoreiraState r c k)
  | 0 => by
    obtain ⟨t₀, ht₀⟩ := IsPWS.partition (IsPWS.Ici 1) c
    refine ⟨{
      B := fun _ => Set.Ici 1 ∩ c ⁻¹' {t₀}
      t := fun _ => t₀
      y := fun i => i.elim0
      hy := fun i => i.elim0
      hB_pws := fun _ => ht₀
      hB_pos := fun _ x hx => hx.1
      hB_col := fun _ x hx => hx.2
      hB_step := fun i => i.elim0
    }⟩
  | k + 1 => by
    obtain ⟨st⟩ := moreira_state_exists r hr c k
    let M : ℕ := ∑ j : Fin (k + 1), (∏ l : Fin k with j.1 ≤ l.1, st.y l) ^ 2
    obtain ⟨yk, hyk_pos, hD_pws⟩ := IsPWS.vdw_shift (st.hB_pws (Fin.last k)) M
    let D : Set ℕ := {x : ℕ | ∀ m ≤ M, x + m * yk ∈ st.B (Fin.last k)}
    have hD_sub : D ⊆ st.B (Fin.last k) := fun x hx => by
      have := hx 0 (Nat.zero_le M)
      simpa using this
    obtain ⟨tk1, hBk1_pws⟩ := IsPWS.partition (IsPWS.mul_left hD_pws hyk_pos) c
    let Bk1 : Set ℕ := (yk * ·) '' D ∩ c ⁻¹' {tk1}
    refine ⟨{
      B := Fin.snoc st.B Bk1
      t := Fin.snoc st.t tk1
      y := Fin.snoc st.y yk
      hy := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · simpa using hyk_pos
        · intro j; simpa using st.hy j
      hB_pws := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · simpa using hBk1_pws
        · intro j; simpa using st.hB_pws j
      hB_pos := fun i x hx => by
        refine Fin.lastCases ?_ ?_ i hx
        · intro hx'
          simp only [Fin.snoc_last] at hx'
          obtain ⟨⟨d, hd, rfl⟩, _⟩ := hx'
          exact Nat.mul_pos hyk_pos (st.hB_pos (Fin.last k) d (hD_sub hd))
        · intro j hx'
          simp only [Fin.snoc_castSucc] at hx'
          exact st.hB_pos j x hx'
      hB_col := fun i x hx => by
        refine Fin.lastCases ?_ ?_ i hx
        · intro hx'
          simp only [Fin.snoc_last] at hx' ⊢
          exact hx'.2
        · intro j hx'
          simp only [Fin.snoc_castSucc] at hx' ⊢
          exact st.hB_col j x hx'
      hB_step := fun i x hx => by
        refine Fin.lastCases ?_ ?_ i hx
        · intro hx'
          have hlast_succ : (Fin.last k).succ = Fin.last (k + 1) := rfl
          have hlast_cast : (Fin.last k).castSucc = (Fin.last k).castSucc := rfl
          rw [hlast_succ, Fin.snoc_last] at hx'
          obtain ⟨⟨d, hd, rfl⟩, _⟩ := hx'
          refine ⟨d, ?_, ?_, ?_⟩
          · simp only [Fin.snoc_castSucc]
            exact hD_sub hd
          · simp only [Fin.snoc_last]
          · intro j
            simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last]
            have hprod_eq :
                ∏ l : Fin (k + 1) with j.1 ≤ l.1 ∧ l.1 < k, Fin.snoc st.y yk l =
                ∏ l : Fin k with j.1 ≤ l.1, st.y l := by
              symm
              refine Finset.prod_bij (fun l _ => l.castSucc) ?_ ?_ ?_ ?_
              · intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                exact ⟨hl, l.isLt⟩
              · intro l₁ _ l₂ _ h
                exact Fin.castSucc_injective k h
              · intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
                refine ⟨⟨l.1, hl.2⟩, ?_, ?_⟩
                · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hl.1
                · ext; rfl
              · intro l _
                simp only [Fin.snoc_castSucc]
            rw [hprod_eq]
            have hle : (∏ l : Fin k with j.1 ≤ l.1, st.y l) ^ 2 ≤ M :=
              Finset.single_le_sum (f := fun j : Fin (k + 1) => (∏ l : Fin k with j.1 ≤ l.1, st.y l) ^ 2)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
            exact hd _ hle
        · intro i₀ hx'
          have hcs : i₀.castSucc.succ = i₀.succ.castSucc := rfl
          rw [hcs, Fin.snoc_castSucc] at hx'
          obtain ⟨d, hd, hxd, hshift⟩ := st.hB_step i₀ x hx'
          refine ⟨d, ?_, ?_, ?_⟩
          · simp only [Fin.snoc_castSucc]
            exact hd
          · simp only [Fin.snoc_castSucc]
            exact hxd
          · intro j
            simp only [Fin.snoc_castSucc, Fin.val_castSucc]
            have hprod_eq :
                ∏ l : Fin (k + 1) with j.1 ≤ l.1 ∧ l.1 < i₀.1, Fin.snoc st.y yk l =
                ∏ l : Fin k with j.1 ≤ l.1 ∧ l.1 < i₀.1, st.y l := by
              symm
              refine Finset.prod_bij (fun l _ => l.castSucc) ?_ ?_ ?_ ?_
              · intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                exact hl
              · intro l₁ _ l₂ _ h
                exact Fin.castSucc_injective k h
              · intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
                refine ⟨⟨l.1, lt_trans hl.2 i₀.isLt⟩, ?_, ?_⟩
                · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hl
                · ext; rfl
              · intro l _
                simp only [Fin.snoc_castSucc]
            rw [hprod_eq]
            exact hshift j
    }⟩

private lemma moreira_state_inclusion {r k : ℕ} {c : ℕ → Fin r} (st : MoreiraState r c k)
    (j i : Fin (k + 1)) (hji : j.1 ≤ i.1) :
    ∀ x ∈ st.B i, ∃ u ∈ st.B j, x = (∏ l : Fin k with j.1 ≤ l.1 ∧ l.1 < i.1, st.y l) * u := by
  induction hn : i.1 - j.1 generalizing i with
  | zero =>
    have hij : i = j := Fin.ext (by omega)
    subst hij
    intro x hx
    refine ⟨x, hx, ?_⟩
    have hempty : (Finset.univ.filter (fun l : Fin k => i.1 ≤ l.1 ∧ l.1 < i.1)) = ∅ := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.prod_empty, one_mul]
  | succ m ih =>
    have hlt : j.1 < i.1 := by omega
    have hi_pos : 0 < i.1 := by omega
    let i' : Fin k := ⟨i.1 - 1, by omega⟩
    have hi_eq : i = i'.succ := Fin.ext (by dsimp [i']; omega)
    intro x hx
    rw [hi_eq] at hx
    obtain ⟨d, hd, rfl, _⟩ := st.hB_step i' x hx
    obtain ⟨u, hu, rfl⟩ := ih i'.castSucc (by dsimp [i']; omega) (by dsimp [i']; omega) d hd
    refine ⟨u, hu, ?_⟩
    have hsplit : (Finset.univ.filter (fun l : Fin k => j.1 ≤ l.1 ∧ l.1 < i.1)) =
        insert i' (Finset.univ.filter (fun l : Fin k => j.1 ≤ l.1 ∧ l.1 < i'.1)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hl
        by_cases h : l = i'
        · exact Or.inl h
        · right
          have hne : l.1 ≠ i'.1 := fun heq => h (Fin.ext heq)
          dsimp [i'] at hne ⊢
          omega
      · rintro (rfl | hl)
        · dsimp [i']; omega
        · dsimp [i'] at hl; omega
    have hnotmem : i' ∉ Finset.univ.filter (fun l : Fin k => j.1 ≤ l.1 ∧ l.1 < i'.1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
      intro _; exact le_rfl
    rw [hsplit, Finset.prod_insert hnotmem]
    simp only [Fin.val_castSucc]
    ring

private theorem moreira_infinite_proof :
    ∀ (r : ℕ) (coloring : ℕ → Fin r),
    Set.Infinite { p : ℕ × ℕ |
      0 < p.1 ∧ 0 < p.2 ∧
      coloring p.1 = coloring (p.1 * p.2) ∧
      coloring p.1 = coloring (p.1 + p.2) } := by
  intro r coloring
  by_cases hr : r = 0
  · subst hr
    exact (coloring 0).elim0
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨st⟩ := moreira_state_exists r hr_pos coloring r
  have hcard : Fintype.card (Fin r) < Fintype.card (Fin (r + 1)) := by simp
  obtain ⟨a, b, hab, htab⟩ := Fintype.exists_ne_map_eq_of_card_lt st.t hcard
  have hpair : ∃ j i : Fin (r + 1), j.1 < i.1 ∧ st.t j = st.t i := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · exact ⟨a, b, hlt, htab⟩
    · exact ⟨b, a, hgt, htab.symm⟩
  obtain ⟨j, i, hji, htji⟩ := hpair
  let i' : Fin r := ⟨i.1 - 1, by omega⟩
  have hi_eq : i = i'.succ := Fin.ext (by dsimp [i']; omega)
  let P_prev : ℕ := ∏ l : Fin r with j.1 ≤ l.1 ∧ l.1 < i'.1, st.y l
  let y : ℕ := ∏ l : Fin r with j.1 ≤ l.1 ∧ l.1 < i.1, st.y l
  have hy_eq : y = st.y i' * P_prev := by
    dsimp [y, P_prev]
    have hsplit : (Finset.univ.filter (fun l : Fin r => j.1 ≤ l.1 ∧ l.1 < i.1)) =
        insert i' (Finset.univ.filter (fun l : Fin r => j.1 ≤ l.1 ∧ l.1 < i'.1)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hl
        by_cases h : l = i'
        · exact Or.inl h
        · right
          have hne : l.1 ≠ i'.1 := fun heq => h (Fin.ext heq)
          dsimp [i'] at hne ⊢
          omega
      · rintro (rfl | hl)
        · dsimp [i']; omega
        · dsimp [i'] at hl; omega
    have hnotmem : i' ∉ Finset.univ.filter (fun l : Fin r => j.1 ≤ l.1 ∧ l.1 < i'.1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
      intro _; exact le_rfl
    rw [hsplit, Finset.prod_insert hnotmem]
  have hy_pos : 0 < y := Finset.prod_pos fun l _ => st.hy l
  let S : Set (ℕ × ℕ) := { p : ℕ × ℕ |
    0 < p.1 ∧ 0 < p.2 ∧
    coloring p.1 = coloring (p.1 * p.2) ∧
    coloring p.1 = coloring (p.1 + p.2) }
  have hsub : (fun x : ℕ => (x / y, y)) '' st.B i ⊆ S := by
    rintro _ ⟨xtilde, hxtilde, rfl⟩
    obtain ⟨x, hxBj, hx_eq⟩ := moreira_state_inclusion st j i (le_of_lt hji) xtilde hxtilde
    have hdiv : xtilde / y = x := by
      rw [hx_eq, Nat.mul_div_cancel_left x hy_pos]
    dsimp only
    rw [hdiv]
    have hx_pos : 0 < x := st.hB_pos j x hxBj
    have hcx : coloring x = st.t j := st.hB_col j x hxBj
    have hcxy : coloring (x * y) = st.t i := by
      rw [mul_comm, ← hx_eq]
      exact st.hB_col i xtilde hxtilde
    have hxtilde' : xtilde ∈ st.B i'.succ := hi_eq ▸ hxtilde
    obtain ⟨d, _, hxd, hshift⟩ := st.hB_step i' xtilde hxtilde'
    have hj_fin : j.1 < i'.1 + 1 := by dsimp [i']; omega
    have hmem_prev : d + P_prev ^ 2 * st.y i' ∈ st.B i'.castSucc := hshift ⟨j.1, hj_fin⟩
    obtain ⟨w, hwBj, hw_eq⟩ := moreira_state_inclusion st j i'.castSucc (by dsimp [i']; omega)
      (d + P_prev ^ 2 * st.y i') hmem_prev
    have hxy_sum : y * (x + y) = y * w := by
      have h1 : st.y i' * (d + P_prev ^ 2 * st.y i') = st.y i' * (P_prev * w) :=
        congrArg (st.y i' * ·) hw_eq
      have h2 : y * x = st.y i' * d := hx_eq.symm.trans hxd
      calc y * (x + y) = y * x + y * y := by ring
        _ = st.y i' * d + (st.y i' * P_prev) * (st.y i' * P_prev) := by rw [h2, hy_eq]
        _ = st.y i' * (d + P_prev ^ 2 * st.y i') := by ring
        _ = st.y i' * (P_prev * w) := h1
        _ = (st.y i' * P_prev) * w := by ring
        _ = y * w := by rw [hy_eq]
    have hxw : x + y = w := Nat.eq_of_mul_eq_mul_left hy_pos hxy_sum
    have hcadd : coloring (x + y) = st.t j := by
      rw [hxw]
      exact st.hB_col j w hwBj
    exact ⟨hx_pos, hy_pos, by rw [hcx, hcxy, htji], by rw [hcx, hcadd]⟩
  have hinj : Set.InjOn (fun x : ℕ => (x / y, y)) (st.B i) := by
    intro x₁ hx₁ x₂ hx₂ heq
    obtain ⟨u₁, _, rfl⟩ := moreira_state_inclusion st j i (le_of_lt hji) x₁ hx₁
    obtain ⟨u₂, _, rfl⟩ := moreira_state_inclusion st j i (le_of_lt hji) x₂ hx₂
    have h1 := congrArg Prod.fst heq
    dsimp only at h1
    rw [Nat.mul_div_cancel_left u₁ hy_pos, Nat.mul_div_cancel_left u₂ hy_pos] at h1
    rw [h1]
  exact ((st.hB_pws i).infinite.image hinj).mono hsub

end OMA

theorem OMA.solution : type_of% @Green22.green_22.variants.moreira_infinite :=
  OMA.moreira_infinite_proof
