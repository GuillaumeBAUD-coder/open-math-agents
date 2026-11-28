import OMAStatements.S_oeis_a166826

namespace OMA.S_oeis_a166826.Proof

open OMA.S_oeis_a166826

/-! ### Part 1: Encoding rows as `Fin 16` -/

private def rowKey (r : Fin 2 → Fin 4) : Fin 16 :=
  ⟨4 * (r 0).val + (r 1).val, by omega⟩

private def keyPair (k : Fin 16) : Fin 4 × Fin 4 :=
  (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩)

private def keyRow (k : Fin 16) : Fin 2 → Fin 4 :=
  fun j => if j = 0 then (keyPair k).1 else (keyPair k).2

private lemma keyRow_zero (k : Fin 16) : keyRow k 0 = (keyPair k).1 := rfl

private lemma keyRow_one (k : Fin 16) : keyRow k 1 = (keyPair k).2 := rfl

private lemma keyRow_rowKey (r : Fin 2 → Fin 4) : keyRow (rowKey r) = r := by
  funext j
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  fin_cases j
  · apply Fin.ext
    change (4 * (r 0).val + (r 1).val) / 4 = (r 0).val
    omega
  · apply Fin.ext
    change (4 * (r 0).val + (r 1).val) % 4 = (r 1).val
    omega

private lemma rowKey_keyRow (k : Fin 16) : rowKey (keyRow k) = k := by
  apply Fin.ext
  change 4 * (k.val / 4) + k.val % 4 = k.val
  omega

private lemma rowLe_iff_rowKey_le (r₁ r₂ : Fin 2 → Fin 4) :
    RowLe r₁ r₂ ↔ rowKey r₁ ≤ rowKey r₂ := by
  have h01 := (r₁ 0).isLt
  have h11 := (r₁ 1).isLt
  have h02 := (r₂ 0).isLt
  have h12 := (r₂ 1).isLt
  simp only [RowLe, rowKey, Fin.lt_def, Fin.le_def, Fin.ext_iff]
  omega

private lemma rowsNondecreasing_iff_monotone {n : ℕ} (A : Fin n → Fin 2 → Fin 4) :
    RowsNondecreasing A ↔ Monotone (fun i => rowKey (A i)) := by
  constructor
  · intro h i j hij
    exact (rowLe_iff_rowKey_le (A i) (A j)).mp (h i j hij)
  · intro h i j hij
    exact (rowLe_iff_rowKey_le (A i) (A j)).mpr (h hij)

/-! ### Part 2: 2-column 4-connectivity characterization -/

private def HasRowVal {m : ℕ} (M : Fin m → Fin 2 → Fin 4) (v : Fin 4) (i : Fin m) : Prop :=
  M i 0 = v ∨ M i 1 = v

private def HasVertBridge {m : ℕ} (M : Fin m → Fin 2 → Fin 4) (v : Fin 4) (r : ℕ) (hr : r + 1 < m) :
    Prop :=
  (M ⟨r, by omega⟩ 0 = v ∧ M ⟨r + 1, hr⟩ 0 = v) ∨
  (M ⟨r, by omega⟩ 1 = v ∧ M ⟨r + 1, hr⟩ 1 = v)

private def ValueChain {m : ℕ} (M : Fin m → Fin 2 → Fin 4) (v : Fin 4) : Prop :=
  ∀ (i j : Fin m), i < j → HasRowVal M v i → HasRowVal M v j →
    ∀ (r : ℕ) (hr : r + 1 < m), i.val ≤ r → r < j.val → HasVertBridge M v r hr

private lemma gridAdj_symm {m : ℕ} {p q : Fin m × Fin 2} (h : GridAdj p q) : GridAdj q p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

private lemma valueAdj_symm {m : ℕ} {M : Fin m → Fin 2 → Fin 4} {v : Fin 4}
    {p q : Fin m × Fin 2} (h : ValueAdj M v p q) : ValueAdj M v q p :=
  ⟨gridAdj_symm h.1, h.2.2, h.2.1⟩

private lemma reflTransGen_valueAdj_symm {m : ℕ} {M : Fin m → Fin 2 → Fin 4} {v : Fin 4}
    {p q : Fin m × Fin 2} (h : Relation.ReflTransGen (ValueAdj M v) p q) :
    Relation.ReflTransGen (ValueAdj M v) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact Relation.ReflTransGen.head (valueAdj_symm hyz) ih

private lemma path_crosses_row {m : ℕ} {M : Fin m → Fin 2 → Fin 4} {v : Fin 4}
    {p q : Fin m × Fin 2} (h : Relation.ReflTransGen (ValueAdj M v) p q)
    {r : ℕ} (hr : r + 1 < m) (hp : p.1.val ≤ r) (hq : r < q.1.val) :
    HasVertBridge M v r hr := by
  induction h with
  | refl => omega
  | @tail y z _ hyz ih =>
    by_cases hy : y.1.val ≤ r
    · rcases y with ⟨y1, y2⟩
      rcases z with ⟨z1, z2⟩
      rcases hyz with ⟨hadj, hvy, hvz⟩
      rcases hadj with ⟨h1, _⟩ | ⟨h2, hstep | hstep⟩
      · simp only at h1 hy hq; subst h1; omega
      · have hyr : y1 = ⟨r, by omega⟩ := Fin.ext (by simp only at hy hq hstep ⊢; omega)
        have hzr : z1 = ⟨r + 1, hr⟩ := Fin.ext (by simp only at hy hq hstep ⊢; omega)
        simp only at h2 hvy hvz
        rw [hyr] at hvy
        rw [hzr, ← h2] at hvz
        fin_cases y2
        · exact Or.inl ⟨hvy, hvz⟩
        · exact Or.inr ⟨hvy, hvz⟩
      · simp only at hy hq hstep; omega
    · exact ih (by omega)

private lemma same_row_connected {m : ℕ} {M : Fin m → Fin 2 → Fin 4} {v : Fin 4}
    (i : Fin m) (c₁ c₂ : Fin 2) (h₁ : M i c₁ = v) (h₂ : M i c₂ = v) :
    Relation.ReflTransGen (ValueAdj M v) (i, c₁) (i, c₂) := by
  by_cases hc : c₁ = c₂
  · subst hc; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨Or.inl ⟨rfl, hc⟩, h₁, h₂⟩

private lemma chain_connects_le {m : ℕ} {M : Fin m → Fin 2 → Fin 4} {v : Fin 4}
    (hchain : ValueChain M v) :
    ∀ (d : ℕ) (i j : Fin m) (c₁ c₂ : Fin 2),
      i.val + d = j.val → M i c₁ = v → M j c₂ = v →
      Relation.ReflTransGen (ValueAdj M v) (i, c₁) (j, c₂)
  | 0, i, j, c₁, c₂, hd, h₁, h₂ => by
    have hij : i = j := Fin.ext (by omega)
    subst hij
    exact same_row_connected i c₁ c₂ h₁ h₂
  | d + 1, i, j, c₁, c₂, hd, h₁, h₂ => by
    have hij : i < j := Fin.lt_def.mpr (by omega)
    have hri : HasRowVal M v i := by fin_cases c₁; exact Or.inl h₁; exact Or.inr h₁
    have hrj : HasRowVal M v j := by fin_cases c₂; exact Or.inl h₂; exact Or.inr h₂
    have hjlt := j.isLt
    have hi1 : i.val + 1 < m := by omega
    have hbr := hchain i j hij hri hrj i.val hi1 le_rfl (by omega)
    let i' : Fin m := ⟨i.val + 1, hi1⟩
    rcases hbr with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · have hstep1 := same_row_connected i c₁ 0 h₁ hb0
      have hstep2 : Relation.ReflTransGen (ValueAdj M v) (i, 0) (i', 0) :=
        Relation.ReflTransGen.single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, hb0, hb1⟩
      have hstep3 := chain_connects_le hchain d i' j 0 c₂ (by simp [i']; omega) hb1 h₂
      exact (hstep1.trans hstep2).trans hstep3
    · have hstep1 := same_row_connected i c₁ 1 h₁ hb0
      have hstep2 : Relation.ReflTransGen (ValueAdj M v) (i, 1) (i', 1) :=
        Relation.ReflTransGen.single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, hb0, hb1⟩
      have hstep3 := chain_connects_le hchain d i' j 1 c₂ (by simp [i']; omega) hb1 h₂
      exact (hstep1.trans hstep2).trans hstep3

private lemma valueConnected_iff_valueChain {m : ℕ} (M : Fin m → Fin 2 → Fin 4) (v : Fin 4) :
    ValueConnected M v ↔ ValueChain M v := by
  constructor
  · intro hconn i j hij hri hrj r hr hir hrj'
    rcases hri with h0 | h1
    · rcases hrj with h0' | h1'
      · exact path_crosses_row (hconn (i, 0) (j, 0) h0 h0') hr hir hrj'
      · exact path_crosses_row (hconn (i, 0) (j, 1) h0 h1') hr hir hrj'
    · rcases hrj with h0' | h1'
      · exact path_crosses_row (hconn (i, 1) (j, 0) h1 h0') hr hir hrj'
      · exact path_crosses_row (hconn (i, 1) (j, 1) h1 h1') hr hir hrj'
  · intro hchain p q hp hq
    by_cases hle : p.1.val ≤ q.1.val
    · exact chain_connects_le hchain (q.1.val - p.1.val) p.1 q.1 p.2 q.2 (by omega) hp hq
    · exact reflTransGen_valueAdj_symm
        (chain_connects_le hchain (p.1.val - q.1.val) q.1 p.1 q.2 p.2 (by omega) hq hp)

/-! ### Part 3: Compression invariance under surjective step-≤-1 monotone maps -/

private structure CompMap (n k : ℕ) where
  fn : Fin n → Fin k
  mono : Monotone fn
  surj : Function.Surjective fn
  step : ∀ (r : ℕ) (hr : r + 1 < n),
    (fn ⟨r + 1, hr⟩).val = (fn ⟨r, by omega⟩).val ∨
    (fn ⟨r + 1, hr⟩).val = (fn ⟨r, by omega⟩).val + 1

private lemma hasAllValues_comp {n k : ℕ} (f : CompMap n k) (R : Fin k → Fin 2 → Fin 4) :
    (∀ v : Fin 4, ∃ i : Fin n, ∃ j : Fin 2, R (f.fn i) j = v) ↔
    (∀ v : Fin 4, ∃ t : Fin k, ∃ j : Fin 2, R t j = v) := by
  constructor
  · intro h v
    rcases h v with ⟨i, j, hij⟩
    exact ⟨f.fn i, j, hij⟩
  · intro h v
    rcases h v with ⟨t, j, htj⟩
    rcases f.surj t with ⟨i, rfl⟩
    exact ⟨i, j, htj⟩

private lemma colsNonincreasing_comp {n k : ℕ} (f : CompMap n k) (R : Fin k → Fin 2 → Fin 4) :
    ColsNonincreasing (fun i => R (f.fn i)) ↔ ColsNonincreasing R := by
  constructor
  · rintro (heq | ⟨i, hprev, hlt⟩)
    · left
      intro t
      rcases f.surj t with ⟨i, rfl⟩
      exact heq i
    · right
      refine ⟨f.fn i, ?_, hlt⟩
      intro t' ht'
      rcases f.surj t' with ⟨i', rfl⟩
      have hi' : i' < i := by
        by_contra hge
        have hge' : i ≤ i' := not_lt.mp hge
        exact not_le_of_gt ht' (f.mono hge')
      exact hprev i' hi'
  · rintro (heq | ⟨t, hprev, hlt⟩)
    · left
      intro i
      exact heq (f.fn i)
    · right
      let S : Finset (Fin n) := Finset.univ.filter (fun i => f.fn i = t)
      have hSne : S.Nonempty := by
        rcases f.surj t with ⟨i, hi⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      let i₀ := S.min' hSne
      have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hSne
      have hi₀_eq : f.fn i₀ = t := (Finset.mem_filter.mp hi₀_mem).2
      refine ⟨i₀, ?_, by dsimp only; rwa [hi₀_eq]⟩
      intro i' hi'
      have hle : f.fn i' ≤ t := by
        rw [← hi₀_eq]
        exact f.mono (le_of_lt hi')
      have hne : f.fn i' ≠ t := by
        intro heq
        have hmem : i' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        exact not_le_of_gt hi' (Finset.min'_le S i' hmem)
      exact hprev (f.fn i') (lt_of_le_of_ne hle hne)

private lemma valueChain_comp {n k : ℕ} (f : CompMap n k) (R : Fin k → Fin 2 → Fin 4) (v : Fin 4) :
    ValueChain (fun i => R (f.fn i)) v ↔ ValueChain R v := by
  constructor
  · intro hA t₁ t₂ ht₁₂ hrt₁ hrt₂ r hr ht₁r hrt₂'
    let S : Finset (Fin n) := Finset.univ.filter (fun i => (f.fn i).val = r)
    have hSne : S.Nonempty := by
      rcases f.surj ⟨r, by omega⟩ with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hi]⟩⟩
    let i₁ := S.max' hSne
    have hi₁_eq : (f.fn i₁).val = r := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    rcases f.surj t₁ with ⟨i₀, hi₀⟩
    rcases f.surj t₂ with ⟨i₂, hi₂⟩
    have hi₁_lt_i₂ : i₁ < i₂ := by
      by_contra hge
      have hge' : i₂ ≤ i₁ := not_lt.mp hge
      have hle : (f.fn i₂).val ≤ (f.fn i₁).val := f.mono hge'
      rw [hi₂, hi₁_eq] at hle
      omega
    have hi₁_lt_val : i₁.val < i₂.val := hi₁_lt_i₂
    have hi₂_lt := i₂.isLt
    have hi₁_succ : i₁.val + 1 < n := by omega
    have hfn_succ : (f.fn ⟨i₁.val + 1, hi₁_succ⟩).val = r + 1 := by
      have hstep := f.step i₁.val hi₁_succ
      have hi₁_cast : (⟨i₁.val, by omega⟩ : Fin n) = i₁ := Fin.ext rfl
      rw [hi₁_cast, hi₁_eq] at hstep
      rcases hstep with heq | heq
      · have hmem : (⟨i₁.val + 1, hi₁_succ⟩ : Fin n) ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        have hle : i₁.val + 1 ≤ i₁.val := Finset.le_max' S ⟨i₁.val + 1, hi₁_succ⟩ hmem
        omega
      · exact heq
    have hi₀_le_i₁ : i₀.val ≤ i₁.val := by
      by_contra hgt
      have hgt' : i₁ < i₀ := Fin.lt_def.mpr (by omega)
      by_cases heq : (f.fn i₀).val = r
      · have hmem : i₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        have hle : i₀.val ≤ i₁.val := Finset.le_max' S i₀ hmem
        omega
      · have hle : (f.fn i₁).val ≤ (f.fn i₀).val := f.mono (le_of_lt hgt')
        rw [hi₁_eq, hi₀] at hle
        rw [hi₀] at heq
        omega
    have hA_i₀ : HasRowVal (fun i => R (f.fn i)) v i₀ := by simpa [HasRowVal, hi₀] using hrt₁
    have hA_i₂ : HasRowVal (fun i => R (f.fn i)) v i₂ := by simpa [HasRowVal, hi₂] using hrt₂
    have hbr := hA i₀ i₂ (Fin.lt_def.mpr (by omega)) hA_i₀ hA_i₂ i₁.val hi₁_succ hi₀_le_i₁
      hi₁_lt_val
    have h1 : f.fn ⟨i₁.val, by omega⟩ = ⟨r, by omega⟩ := Fin.ext hi₁_eq
    have h2 : f.fn ⟨i₁.val + 1, hi₁_succ⟩ = ⟨r + 1, hr⟩ := Fin.ext hfn_succ
    simpa [HasVertBridge, h1, h2] using hbr
  · intro hR i₁ i₂ hi₁₂ hri₁ hri₂ r hr hi₁r hrlt
    have hle1 : (f.fn i₁).val ≤ (f.fn ⟨r, by omega⟩).val :=
      f.mono (Fin.le_def.mpr (show i₁.val ≤ r by omega))
    have hle2 : (f.fn ⟨r + 1, hr⟩).val ≤ (f.fn i₂).val :=
      f.mono (Fin.le_def.mpr (show r + 1 ≤ i₂.val by omega))
    rcases f.step r hr with heq | hsucc
    · have hfeq : f.fn ⟨r + 1, hr⟩ = f.fn ⟨r, by omega⟩ := Fin.ext heq
      have hrv : HasRowVal R v (f.fn ⟨r, by omega⟩) := by
        by_cases h1 : f.fn i₁ = f.fn ⟨r, by omega⟩
        · simpa [HasRowVal, h1] using hri₁
        · by_cases h2 : f.fn ⟨r, by omega⟩ = f.fn i₂
          · simpa [HasRowVal, h2] using hri₂
          · have hlt1 : f.fn i₁ < f.fn ⟨r, by omega⟩ :=
              lt_of_le_of_ne (f.mono (Fin.le_def.mpr (show i₁.val ≤ r by omega))) h1
            have hlt2 : f.fn ⟨r, by omega⟩ < f.fn i₂ := by
              rw [← hfeq]
              exact lt_of_le_of_ne
                (f.mono (Fin.le_def.mpr (show r + 1 ≤ i₂.val by omega))) (by rwa [hfeq])
            have hlt2_val : (f.fn ⟨r, by omega⟩).val < (f.fn i₂).val := hlt2
            have hi2_k := (f.fn i₂).isLt
            have hbr := hR (f.fn i₁) (f.fn i₂) (lt_trans hlt1 hlt2) hri₁ hri₂
              (f.fn ⟨r, by omega⟩).val (by omega) (Fin.le_def.mp (le_of_lt hlt1)) hlt2_val
            have hcast : (⟨(f.fn ⟨r, by omega⟩).val, by omega⟩ : Fin k) = f.fn ⟨r, by omega⟩ :=
              Fin.ext rfl
            rcases hbr with ⟨ha, _⟩ | ⟨ha, _⟩
            · left; rwa [hcast] at ha
            · right; rwa [hcast] at ha
      rcases hrv with h0 | h1
      · exact Or.inl ⟨h0, by dsimp only; rwa [hfeq]⟩
      · exact Or.inr ⟨h1, by dsimp only; rwa [hfeq]⟩
    · have hlt : f.fn i₁ < f.fn i₂ := Fin.lt_def.mpr (by omega)
      have hsucc_lt := (f.fn ⟨r + 1, hr⟩).isLt
      have hrt : (f.fn ⟨r, by omega⟩).val + 1 < k := by omega
      have hbr := hR (f.fn i₁) (f.fn i₂) hlt hri₁ hri₂ (f.fn ⟨r, by omega⟩).val hrt
        hle1 (by omega)
      have h1 : (⟨(f.fn ⟨r, by omega⟩).val, by omega⟩ : Fin k) = f.fn ⟨r, by omega⟩ :=
        Fin.ext rfl
      have h2 : (⟨(f.fn ⟨r, by omega⟩).val + 1, hrt⟩ : Fin k) = f.fn ⟨r + 1, hr⟩ :=
        Fin.ext hsucc.symm
      simpa [HasVertBridge, h1, h2] using hbr

private lemma isValid_comp {n k : ℕ} (f : CompMap n k) (R : Fin k → Fin 2 → Fin 4)
    (hRmono : RowsNondecreasing R) :
    IsValid (fun i => R (f.fn i)) ↔ IsValid R := by
  have hAmono : RowsNondecreasing (fun i => R (f.fn i)) := by
    intro i j hij
    exact hRmono (f.fn i) (f.fn j) (f.mono hij)
  simp only [IsValid, hasAllValues_comp, valueConnected_iff_valueChain, valueChain_comp,
    colsNonincreasing_comp, hAmono, hRmono, true_and]

/-! ### Part 4: Row-compression bijection for `n ≥ 1` -/

private def listArr (L : List (Fin 16)) : Fin L.length → Fin 2 → Fin 4 :=
  fun t => keyRow (L.get t)

private def IsValidSubset (S : Finset (Fin 16)) : Prop :=
  IsValid (listArr (S.sort (· ≤ ·)))

private lemma list_sort_get_strictMono (S : Finset (Fin 16)) :
    StrictMono (fun t : Fin (S.sort (· ≤ ·)).length => (S.sort (· ≤ ·)).get t) := by
  have hle := List.pairwise_iff_get.mp (S.pairwise_sort (· ≤ ·))
  have hnd := List.nodup_iff_injective_get.mp (S.sort_nodup (· ≤ ·))
  intro i j hij
  exact lt_of_le_of_ne (hle i j hij) (fun heq => ne_of_lt hij (hnd heq))

private lemma list_sort_rowsNondecreasing (S : Finset (Fin 16)) :
    RowsNondecreasing (listArr (S.sort (· ≤ ·))) := by
  rw [rowsNondecreasing_iff_monotone]
  intro i j hij
  simp only [listArr, rowKey_keyRow]
  exact (list_sort_get_strictMono S).monotone hij

private lemma list_sort_get_rank (S : Finset (Fin 16)) {x : Fin 16} (hx : x ∈ S) :
    let L := S.sort (· ≤ ·)
    ∃ (h : (S.filter (· < x)).card < L.length), L.get ⟨(S.filter (· < x)).card, h⟩ = x := by
  intro L
  have hxL : x ∈ L := (Finset.mem_sort (· ≤ ·)).mpr hx
  rcases List.mem_iff_get.mp hxL with ⟨idx, hidx⟩
  have hmono : StrictMono L.get := list_sort_get_strictMono S
  have himg : Finset.image L.get (Finset.univ.filter (fun t : Fin L.length => t < idx)) =
      S.filter (· < x) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(Finset.mem_sort (· ≤ ·)).mp (List.get_mem L t), by rw [← hidx]; exact hmono ht⟩
    · rintro ⟨hyS, hyx⟩
      rcases List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hyS) with ⟨t, rfl⟩
      refine ⟨t, ?_, rfl⟩
      by_contra hge
      have hge' : idx ≤ t := not_lt.mp hge
      have : x ≤ L.get t := by rw [← hidx]; exact hmono.monotone hge'
      exact not_le_of_gt hyx this
  have hcard : (S.filter (· < x)).card = idx.val := by
    rw [← himg, Finset.card_image_of_injective _ hmono.injective]
    have hbi : (Finset.univ.filter (fun t : Fin L.length => t < idx)) =
        (Finset.range idx.val).attach.map
          ⟨fun r => ⟨r.1, lt_trans (Finset.mem_range.mp r.2) idx.2⟩,
           fun a b hab => Subtype.ext (by simpa [Fin.ext_iff] using hab)⟩ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, Subtype.exists, Finset.mem_range]
      constructor
      · intro ht
        exact ⟨t.val, ht, Fin.ext rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ha
    rw [hbi, Finset.card_map, Finset.card_attach, Finset.card_range]
  refine ⟨by rw [hcard]; exact idx.2, ?_⟩
  have heq : (⟨(S.filter (· < x)).card, by rw [hcard]; exact idx.2⟩ : Fin L.length) = idx :=
    Fin.ext hcard
  rw [heq, hidx]

private def jumpIndex {n k : ℕ} (J : Finset (Fin (n - 1))) (hJk : J.card + 1 = k) (i : Fin n) :
    Fin k :=
  ⟨(J.filter (fun j : Fin (n - 1) => j.val < i.val)).card, by
    have hle : (J.filter (fun j : Fin (n - 1) => j.val < i.val)).card ≤ J.card :=
      Finset.card_filter_le _ _
    omega⟩

private lemma jumpIndex_step {n k : ℕ} (J : Finset (Fin (n - 1))) (hJk : J.card + 1 = k)
    (r : ℕ) (hr : r + 1 < n) :
    (jumpIndex J hJk ⟨r + 1, hr⟩).val =
      (jumpIndex J hJk ⟨r, by omega⟩).val + if (⟨r, by omega⟩ : Fin (n - 1)) ∈ J then 1 else 0 := by
  let r' : Fin (n - 1) := ⟨r, by omega⟩
  change (jumpIndex J hJk ⟨r + 1, hr⟩).val =
    (jumpIndex J hJk ⟨r, by omega⟩).val + if r' ∈ J then 1 else 0
  simp only [jumpIndex]
  by_cases hmem : r' ∈ J
  · simp only [hmem, ↓reduceIte]
    have hset : J.filter (fun j : Fin (n - 1) => j.val < r + 1) =
        insert r' (J.filter (fun j : Fin (n - 1) => j.val < r)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff, r']
      constructor
      · rintro ⟨hjJ, hjlt⟩
        by_cases heq : j.val = r
        · exact Or.inl heq
        · exact Or.inr ⟨hjJ, by omega⟩
      · rintro (heq | ⟨hjJ, hjlt⟩)
        · have hjr : j = r' := Fin.ext heq
          exact ⟨hjr ▸ hmem, by omega⟩
        · exact ⟨hjJ, by omega⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp [r']
  · simp only [hmem, ↓reduceIte, add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hjJ, hjlt⟩
      refine ⟨hjJ, ?_⟩
      by_contra hge
      have heq : j = r' := Fin.ext (show j.val = r by omega)
      exact hmem (heq ▸ hjJ)
    · rintro ⟨hjJ, hjlt⟩
      exact ⟨hjJ, by omega⟩

private lemma jumpIndex_mono {n k : ℕ} (J : Finset (Fin (n - 1))) (hJk : J.card + 1 = k) :
    Monotone (jumpIndex J hJk) := by
  intro i₁ i₂ hij
  simp only [jumpIndex, Fin.le_def]
  exact Finset.card_le_card (fun j hj => by
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, lt_of_lt_of_le hj.2 hij⟩)

private lemma jumpIndex_surj {n k : ℕ} (hn : 1 ≤ n) (J : Finset (Fin (n - 1)))
    (hJk : J.card + 1 = k) : Function.Surjective (jumpIndex J hJk) := by
  have hzero : (jumpIndex J hJk ⟨0, by omega⟩).val = 0 := by
    simp [jumpIndex]
  have hlast : (jumpIndex J hJk ⟨n - 1, by omega⟩).val = k - 1 := by
    simp only [jumpIndex]
    have hfilt : J.filter (fun j : Fin (n - 1) => j.val < n - 1) = J :=
      Finset.filter_true_of_mem (fun j _ => j.isLt)
    rw [hfilt]; omega
  intro t
  suffices ∀ (m : ℕ) (hm : m < n), t.val ≤ (jumpIndex J hJk ⟨m, hm⟩).val →
      ∃ i : Fin n, (jumpIndex J hJk i).val = t.val by
    have htlt := t.isLt
    rcases this (n - 1) (by omega) (by rw [hlast]; omega) with ⟨i, hi⟩
    exact ⟨i, Fin.ext hi⟩
  intro m
  induction m with
  | zero =>
    intro hm ht
    rw [hzero] at ht
    exact ⟨⟨0, hm⟩, by omega⟩
  | succ r ih =>
    intro hr ht
    have hstep := jumpIndex_step J hJk r hr
    by_cases hle : t.val ≤ (jumpIndex J hJk ⟨r, by omega⟩).val
    · exact ih (by omega) hle
    · refine ⟨⟨r + 1, hr⟩, ?_⟩
      split_ifs at hstep <;> omega

private def jumpCompMap {n k : ℕ} (hn : 1 ≤ n) (J : Finset (Fin (n - 1)))
    (hJk : J.card + 1 = k) : CompMap n k where
  fn := jumpIndex J hJk
  mono := jumpIndex_mono J hJk
  surj := jumpIndex_surj hn J hJk
  step := fun r hr => by
    have h := jumpIndex_step J hJk r hr
    split_ifs at h
    · exact Or.inr h
    · exact Or.inl (by omega)

private lemma mono_rank_eq_jumps {n : ℕ} (g : Fin n → Fin 16) (hg : Monotone g) :
    let S := Finset.image g Finset.univ
    let J := Finset.univ.filter (fun j : Fin (n - 1) => g ⟨j.val, by omega⟩ < g ⟨j.val + 1, by omega⟩)
    ∀ i : Fin n, (S.filter (· < g i)).card = (J.filter (fun j : Fin (n - 1) => j.val < i.val)).card := by
  intro S J i
  rcases i with ⟨m, hm⟩
  induction m with
  | zero =>
    have h1 : S.filter (· < g ⟨0, hm⟩) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt, S,
        Finset.mem_image, Finset.mem_univ, true_and]
      rintro ⟨j, rfl⟩
      exact hg (Fin.le_def.mpr (Nat.zero_le j.val))
    have h2 : J.filter (fun j : Fin (n - 1) => j.val < 0) = ∅ := by
      ext j; simp
    rw [h1, h2]
    rfl
  | succ r ih =>
    have hr : r < n := by omega
    have hih := ih hr
    let r' : Fin (n - 1) := ⟨r, by omega⟩
    by_cases hlt : g ⟨r, hr⟩ < g ⟨r + 1, hm⟩
    · have hS : S.filter (· < g ⟨r + 1, hm⟩) =
          insert (g ⟨r, hr⟩) (S.filter (· < g ⟨r, hr⟩)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, S, Finset.mem_image, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨⟨j, rfl⟩, hjlt⟩
          have hjr : j.val ≤ r := by
            by_contra hgt
            have : g ⟨r + 1, hm⟩ ≤ g j := hg (Fin.le_def.mpr (show r + 1 ≤ j.val by omega))
            exact not_le_of_gt hjlt this
          have hle : g j ≤ g ⟨r, hr⟩ := hg (Fin.le_def.mpr hjr)
          rcases lt_or_eq_of_le hle with hlt' | heq'
          · exact Or.inr ⟨⟨j, rfl⟩, hlt'⟩
          · exact Or.inl heq'
        · rintro (rfl | ⟨⟨j, rfl⟩, hjlt⟩)
          · exact ⟨⟨⟨r, hr⟩, rfl⟩, hlt⟩
          · exact ⟨⟨j, rfl⟩, lt_trans hjlt hlt⟩
      have hJ : J.filter (fun j : Fin (n - 1) => j.val < r + 1) =
          insert r' (J.filter (fun j : Fin (n - 1) => j.val < r)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff, r', J, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨hjlt, hjval⟩
          by_cases heq : j.val = r
          · exact Or.inl heq
          · exact Or.inr ⟨hjlt, by omega⟩
        · rintro (heq | ⟨hjlt, hjval⟩)
          · refine ⟨?_, by omega⟩
            have h1 : (⟨j.val, by omega⟩ : Fin n) = ⟨r, hr⟩ := Fin.ext heq
            have h2 : (⟨j.val + 1, by omega⟩ : Fin n) = ⟨r + 1, hm⟩ :=
              Fin.ext (show j.val + 1 = r + 1 by omega)
            rwa [h1, h2]
          · exact ⟨hjlt, by omega⟩
      rw [hS, hJ, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hih]
      · simp only [Finset.mem_filter, not_and, not_lt]
        intro _
        exact le_rfl
      · simp
    · have heq : g ⟨r, hr⟩ = g ⟨r + 1, hm⟩ :=
        le_antisymm (hg (Fin.le_def.mpr (show r ≤ r + 1 by omega))) (not_lt.mp hlt)
      have hJ : J.filter (fun j : Fin (n - 1) => j.val < r + 1) =
          J.filter (fun j : Fin (n - 1) => j.val < r) := by
        ext j
        simp only [Finset.mem_filter, J, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hjlt, hjval⟩
          refine ⟨hjlt, ?_⟩
          by_contra hge
          have hjr : j.val = r := by omega
          have h1 : (⟨j.val, by omega⟩ : Fin n) = ⟨r, hr⟩ := Fin.ext hjr
          have h2 : (⟨j.val + 1, by omega⟩ : Fin n) = ⟨r + 1, hm⟩ :=
            Fin.ext (show j.val + 1 = r + 1 by omega)
          rw [h1, h2] at hjlt
          exact hlt hjlt
        · rintro ⟨hjlt, hjval⟩
          exact ⟨hjlt, by omega⟩
      rw [← heq, hJ, hih]

private lemma mono_jumps_card {n : ℕ} (hn : 1 ≤ n) (g : Fin n → Fin 16) (hg : Monotone g) :
    let S := Finset.image g Finset.univ
    let J := Finset.univ.filter (fun j : Fin (n - 1) => g ⟨j.val, by omega⟩ < g ⟨j.val + 1, by omega⟩)
    J.card + 1 = S.card := by
  intro S J
  have h := mono_rank_eq_jumps g hg ⟨n - 1, by omega⟩
  have hJ : J.filter (fun j : Fin (n - 1) => j.val < n - 1) = J :=
    Finset.filter_true_of_mem (fun j _ => j.isLt)
  have hS : S.filter (· < g ⟨n - 1, by omega⟩) = S.erase (g ⟨n - 1, by omega⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, hjlt⟩
      exact ⟨ne_of_lt hjlt, ⟨j, rfl⟩⟩
    · rintro ⟨hne, ⟨j, rfl⟩⟩
      have hjlt := j.isLt
      exact ⟨⟨j, rfl⟩, lt_of_le_of_ne (hg (Fin.le_def.mpr (show j.val ≤ n - 1 by omega))) hne⟩
  rw [hJ, hS] at h
  have hmem : g ⟨n - 1, by omega⟩ ∈ S :=
    Finset.mem_image.mpr ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, rfl⟩
  have herase : (S.erase (g ⟨n - 1, by omega⟩)).card + 1 = S.card :=
    Finset.card_erase_add_one hmem
  omega

private lemma validSigma_ext {n : ℕ}
    {S₁ S₂ : {S : Finset (Fin 16) // IsValidSubset S}}
    {J₁ : {J : Finset (Fin (n - 1)) // J.card + 1 = S₁.val.card}}
    {J₂ : {J : Finset (Fin (n - 1)) // J.card + 1 = S₂.val.card}}
    (hS : S₁.val = S₂.val) (hJ : J₁.val = J₂.val) :
    (⟨S₁, J₁⟩ : Σ S : {S : Finset (Fin 16) // IsValidSubset S},
      {J : Finset (Fin (n - 1)) // J.card + 1 = S.val.card}) = ⟨S₂, J₂⟩ := by
  have hS' : S₁ = S₂ := Subtype.ext hS
  subst hS'
  congr 1
  exact Subtype.ext hJ

private noncomputable def validEquiv {n : ℕ} (hn : 1 ≤ n) :
    {A : Fin n → Fin 2 → Fin 4 // IsValid A} ≃
      Σ (S : {S : Finset (Fin 16) // IsValidSubset S}),
        {J : Finset (Fin (n - 1)) // J.card + 1 = S.val.card} where
  toFun := fun ⟨A, hA⟩ =>
    let g : Fin n → Fin 16 := fun i => rowKey (A i)
    let hg : Monotone g := (rowsNondecreasing_iff_monotone A).mp hA.2.2.1
    let S : Finset (Fin 16) := Finset.image g Finset.univ
    let J : Finset (Fin (n - 1)) :=
      Finset.univ.filter (fun j : Fin (n - 1) => g ⟨j.val, by omega⟩ < g ⟨j.val + 1, by omega⟩)
    let hJk : J.card + 1 = S.card := mono_jumps_card hn g hg
    let hJkL : J.card + 1 = (S.sort (· ≤ ·)).length := hJk.trans (S.length_sort (· ≤ ·)).symm
    let f := jumpCompMap hn J hJkL
    have hAeq : A = fun i => listArr (S.sort (· ≤ ·)) (f.fn i) := by
      funext i
      have hmem : g i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rcases list_sort_get_rank S hmem with ⟨hcard, hget⟩
      have hrank := mono_rank_eq_jumps g hg i
      have hidx : f.fn i = ⟨(S.filter (· < g i)).card, hcard⟩ := Fin.ext hrank.symm
      simp only [listArr, hidx, hget, g, keyRow_rowKey]
    have hSval : IsValidSubset S := by
      rw [IsValidSubset, ← isValid_comp f (listArr (S.sort (· ≤ ·))) (list_sort_rowsNondecreasing S)]
      rwa [← hAeq]
    ⟨⟨S, hSval⟩, ⟨J, hJk⟩⟩
  invFun := fun ⟨⟨S, hS⟩, ⟨J, hJk⟩⟩ =>
    let hJkL : J.card + 1 = (S.sort (· ≤ ·)).length := hJk.trans (S.length_sort (· ≤ ·)).symm
    let f := jumpCompMap hn J hJkL
    ⟨fun i => listArr (S.sort (· ≤ ·)) (f.fn i),
     (isValid_comp f (listArr (S.sort (· ≤ ·))) (list_sort_rowsNondecreasing S)).mpr hS⟩
  left_inv := fun ⟨A, hA⟩ => by
    apply Subtype.ext
    funext i
    let g : Fin n → Fin 16 := fun j => rowKey (A j)
    let hg : Monotone g := (rowsNondecreasing_iff_monotone A).mp hA.2.2.1
    let S : Finset (Fin 16) := Finset.image g Finset.univ
    let J : Finset (Fin (n - 1)) :=
      Finset.univ.filter (fun j : Fin (n - 1) => g ⟨j.val, by omega⟩ < g ⟨j.val + 1, by omega⟩)
    have hmem : g i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rcases list_sort_get_rank S hmem with ⟨hcard, hget⟩
    have hrank := mono_rank_eq_jumps g hg i
    have hJk : J.card + 1 = S.card := mono_jumps_card hn g hg
    have hle : (J.filter (fun j : Fin (n - 1) => j.val < i.val)).card ≤ J.card :=
      Finset.card_filter_le _ _
    have hltL : (J.filter (fun j : Fin (n - 1) => j.val < i.val)).card < (S.sort (· ≤ ·)).length := by
      rw [S.length_sort (· ≤ ·)]
      omega
    simp only [listArr, jumpCompMap, jumpIndex]
    have hidx : (⟨(J.filter (fun j : Fin (n - 1) => j.val < i.val)).card, hltL⟩ :
        Fin (S.sort (· ≤ ·)).length) = ⟨(S.filter (· < g i)).card, hcard⟩ :=
      Fin.ext hrank.symm
    rw [hidx, hget]
    exact keyRow_rowKey (A i)
  right_inv := fun ⟨⟨S, hS⟩, ⟨J, hJk⟩⟩ => by
    dsimp only
    let hJkL : J.card + 1 = (S.sort (· ≤ ·)).length := hJk.trans (S.length_sort (· ≤ ·)).symm
    let f := jumpCompMap hn J hJkL
    have hSeq : Finset.image (fun i => rowKey (listArr (S.sort (· ≤ ·)) (f.fn i))) Finset.univ = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, listArr, rowKey_keyRow]
      constructor
      · rintro ⟨i, rfl⟩
        exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
      · intro hx
        rcases List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hx) with ⟨t, rfl⟩
        rcases f.surj t with ⟨i, hi⟩
        exact ⟨i, by rw [hi]⟩
    have hJeq : Finset.univ.filter (fun j : Fin (n - 1) =>
        rowKey (listArr (S.sort (· ≤ ·)) (f.fn ⟨j.val, by omega⟩)) <
        rowKey (listArr (S.sort (· ≤ ·)) (f.fn ⟨j.val + 1, by omega⟩))) = J := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, listArr, rowKey_keyRow]
      rw [(list_sort_get_strictMono S).lt_iff_lt]
      have hjlt := j.isLt
      have hstep := jumpIndex_step J hJkL j.val (by omega)
      simp only [f, jumpCompMap, Fin.lt_def]
      have hjcast : (⟨j.val, by omega⟩ : Fin (n - 1)) = j := Fin.ext rfl
      rw [hjcast] at hstep
      split_ifs at hstep with hmem
      · simp only [hmem, iff_true]; omega
      · simp only [hmem, iff_false]; omega
    exact validSigma_ext hSeq hJeq

private lemma validSubset_card_pos {S : Finset (Fin 16)} (hS : IsValidSubset S) :
    1 ≤ S.card := by
  rcases hS.1 0 with ⟨t, _, _⟩
  have hpos : 0 < (S.sort (· ≤ ·)).length := Fin.pos t
  rw [S.length_sort (· ≤ ·)] at hpos
  omega

private lemma card_finset_card_eq (m k : ℕ) :
    Nat.card {J : Finset (Fin m) // J.card = k} = m.choose k := by
  rw [Nat.card_eq_fintype_card]
  have heq : Fintype.card {J : Finset (Fin m) // J.card = k} =
      ((Finset.univ : Finset (Fin m)).powersetCard k).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun ⟨J, hJ⟩ => ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJ⟩⟩
        invFun := fun ⟨J, hJ⟩ => ⟨J, (Finset.mem_powersetCard.mp hJ).2⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
private lemma a_eq_sum_validSubsets {n : ℕ} (hn : 1 ≤ n) :
    a n = ∑ S : Finset (Fin 16), if IsValidSubset S then (n - 1).choose (S.card - 1) else 0 := by
  rw [a, Nat.card_congr (validEquiv hn), Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h1 : ∑ S : {S : Finset (Fin 16) // IsValidSubset S},
      Fintype.card {J : Finset (Fin (n - 1)) // J.card + 1 = S.val.card} =
      ∑ S : {S : Finset (Fin 16) // IsValidSubset S}, (n - 1).choose (S.val.card - 1) := by
    apply Finset.sum_congr rfl
    intro S _
    have hpos := validSubset_card_pos S.2
    have heqv : {J : Finset (Fin (n - 1)) // J.card + 1 = S.val.card} ≃
        {J : Finset (Fin (n - 1)) // J.card = S.val.card - 1} :=
      { toFun := fun ⟨J, hJ⟩ => ⟨J, by omega⟩
        invFun := fun ⟨J, hJ⟩ => ⟨J, by omega⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [Fintype.card_congr heqv, ← Nat.card_eq_fintype_card, card_finset_card_eq]
  rw [h1, ← Finset.sum_filter]
  have hsub : ∑ S ∈ Finset.univ.filter IsValidSubset, (n - 1).choose (S.card - 1) =
      ∑ S : {S : Finset (Fin 16) // IsValidSubset S}, (n - 1).choose (S.val.card - 1) :=
    Finset.sum_subtype (Finset.univ.filter IsValidSubset) (by intro x; simp) _
  exact hsub.symm

/-! ### Part 5: Exact DFS automaton for valid compressed row lists -/

private def hasSeen (s0 s1 s2 s3 : Bool) : Fin 4 → Bool
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2
  | ⟨3, _⟩ => s3

private def setSeen (s0 s1 s2 s3 : Bool) (r : Fin 4 × Fin 4) : Bool × Bool × Bool × Bool :=
  (s0 || decide (r.1 = 0) || decide (r.2 = 0),
   s1 || decide (r.1 = 1) || decide (r.2 = 1),
   s2 || decide (r.1 = 2) || decide (r.2 = 2),
   s3 || decide (r.1 = 3) || decide (r.2 = 3))

private lemma hasSeen_setSeen (s0 s1 s2 s3 : Bool) (r : Fin 4 × Fin 4) (v : Fin 4) :
    let ns := setSeen s0 s1 s2 s3 r
    hasSeen ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 v =
      (hasSeen s0 s1 s2 s3 v || decide (r.1 = v) || decide (r.2 = v)) := by
  fin_cases v <;> rfl

private def vertBridgeBool (last : Option (Fin 4 × Fin 4)) (r : Fin 4 × Fin 4) (v : Fin 4) : Bool :=
  match last with
  | none => false
  | some p => (decide (p.1 = v) && decide (r.1 = v)) || (decide (p.2 = v) && decide (r.2 = v))

private def stepOk (last : Option (Fin 4 × Fin 4)) (s0 s1 s2 s3 cmpGt : Bool)
    (r : Fin 4 × Fin 4) : Bool :=
  (cmpGt || decide (r.2 ≤ r.1)) &&
  (!hasSeen s0 s1 s2 s3 r.1 || vertBridgeBool last r r.1) &&
  (!hasSeen s0 s1 s2 s3 r.2 || vertBridgeBool last r r.2)

private def validFrom :
    Option (Fin 4 × Fin 4) → Bool → Bool → Bool → Bool → Bool → List (Fin 16) → Bool
  | _, s0, s1, s2, s3, _, [] => s0 && s1 && s2 && s3
  | last, s0, s1, s2, s3, cmpGt, k :: ks =>
    let r := keyPair k
    let ns := setSeen s0 s1 s2 s3 r
    stepOk last s0 s1 s2 s3 cmpGt r &&
    validFrom (some r) ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 (cmpGt || decide (r.2 < r.1)) ks

private def PrefixInv (P : List (Fin 16)) (last : Option (Fin 4 × Fin 4))
    (s0 s1 s2 s3 cmpGt : Bool) : Prop :=
  (last = P.getLast?.map keyPair) ∧
  (∀ v : Fin 4, hasSeen s0 s1 s2 s3 v = true ↔ ∃ t : Fin P.length, HasRowVal (listArr P) v t) ∧
  (if cmpGt then
    ∃ t : Fin P.length, (∀ t' : Fin P.length, t' < t → listArr P t' 0 = listArr P t' 1) ∧
      listArr P t 1 < listArr P t 0
   else ∀ t : Fin P.length, listArr P t 0 = listArr P t 1) ∧
  (∀ v : Fin 4, ValueChain (listArr P) v)

private lemma listArr_append_left (P Q : List (Fin 16)) (i : ℕ) (hi : i < P.length) :
    listArr (P ++ Q) ⟨i, by rw [List.length_append]; omega⟩ = listArr P ⟨i, hi⟩ := by
  simp only [listArr, List.get_eq_getElem]
  rw [List.getElem_append_left hi]

private lemma listArr_append_left' (P Q : List (Fin 16)) (t : Fin (P ++ Q).length)
    (ht : t.val < P.length) :
    listArr (P ++ Q) t = listArr P ⟨t.val, ht⟩ := by
  simp only [listArr, List.get_eq_getElem]
  rw [List.getElem_append_left ht]

private lemma listArr_append_cons_mid (P Q : List (Fin 16)) (k : Fin 16) :
    listArr (P ++ k :: Q) ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ =
      keyRow k := by
  simp only [listArr, List.get_eq_getElem]
  rw [List.getElem_append_right (le_refl P.length)]
  simp

private lemma validFrom_iff (Q : List (Fin 16)) :
    ∀ (P : List (Fin 16)) (last : Option (Fin 4 × Fin 4)) (s0 s1 s2 s3 cmpGt : Bool),
      PrefixInv P last s0 s1 s2 s3 cmpGt →
      (validFrom last s0 s1 s2 s3 cmpGt Q = true ↔
        (∀ v : Fin 4, ∃ t : Fin (P ++ Q).length, HasRowVal (listArr (P ++ Q)) v t) ∧
        (∀ v : Fin 4, ValueChain (listArr (P ++ Q)) v) ∧
        ColsNonincreasing (listArr (P ++ Q))) := by
  induction Q with
  | nil =>
    intro P last s0 s1 s2 s3 cmpGt ⟨_, hseen, hcmp, hchain⟩
    rw [List.append_nil]
    simp only [validFrom]
    have hall : (s0 && s1 && s2 && s3) = true ↔
        ∀ v : Fin 4, ∃ t : Fin P.length, HasRowVal (listArr P) v t := by
      constructor
      · intro h v
        rw [← hseen v]
        fin_cases v <;> simp_all [hasSeen]
      · intro h
        have h0 := (hseen 0).mpr (h 0)
        have h1 := (hseen 1).mpr (h 1)
        have h2 := (hseen 2).mpr (h 2)
        have h3 := (hseen 3).mpr (h 3)
        simp_all [hasSeen]
    have hcols : ColsNonincreasing (listArr P) := by
      cases cmpGt
      · exact Or.inl (by simpa using hcmp)
      · exact Or.inr (by simpa using hcmp)
    rw [hall]
    exact ⟨fun h => ⟨h, hchain, hcols⟩, fun h => h.1⟩
  | cons k Q ih =>
    intro P last s0 s1 s2 s3 cmpGt hinv
    rcases hinv with ⟨hlast, hseen, hcmp, hchain⟩
    let r := keyPair k
    let ns := setSeen s0 s1 s2 s3 r
    let cmpGt' := cmpGt || decide (r.2 < r.1)
    have hcat : P ++ k :: Q = (P ++ [k]) ++ Q := by simp
    by_cases hstep : stepOk last s0 s1 s2 s3 cmpGt r = true
    · have hstep' := hstep
      simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at hstep'
      rcases hstep' with ⟨⟨hcmpOk, hconn1⟩, hconn2⟩
      have hlast' : some r = (P ++ [k]).getLast?.map keyPair := by
        simp [r]
      have hseen' : ∀ v : Fin 4, hasSeen ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 v = true ↔
          ∃ t : Fin (P ++ [k]).length, HasRowVal (listArr (P ++ [k])) v t := by
        intro v
        rw [hasSeen_setSeen]
        simp only [Bool.or_eq_true, decide_eq_true_eq, hseen v]
        constructor
        · rintro ((⟨t, ht⟩ | hr1) | hr2)
          · refine ⟨⟨t.val, by rw [List.length_append]; omega⟩, ?_⟩
            simpa [HasRowVal, listArr_append_left P [k] t.val t.isLt] using ht
          · refine ⟨⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩, ?_⟩
            left; simpa [listArr_append_cons_mid P [] k, keyRow_zero] using hr1
          · refine ⟨⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩, ?_⟩
            right; simpa [listArr_append_cons_mid P [] k, keyRow_one] using hr2
        · rintro ⟨t, ht⟩
          by_cases htl : t.val < P.length
          · left; left
            refine ⟨⟨t.val, htl⟩, ?_⟩
            simpa [HasRowVal, listArr_append_left' P [k] t htl] using ht
          · have htlt : t.val < P.length + 1 := by simpa using t.isLt
            have hteq : t = ⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩ :=
              Fin.ext (show t.val = P.length by omega)
            rw [hteq] at ht
            simp only [HasRowVal, listArr_append_cons_mid P [] k, keyRow_zero, keyRow_one] at ht
            rcases ht with h0 | h1
            · left; right; exact h0
            · right; exact h1
      have hcmp' : (if cmpGt' then
          ∃ t : Fin (P ++ [k]).length,
            (∀ t' : Fin (P ++ [k]).length, t' < t →
              listArr (P ++ [k]) t' 0 = listArr (P ++ [k]) t' 1) ∧
            listArr (P ++ [k]) t 1 < listArr (P ++ [k]) t 0
         else ∀ t : Fin (P ++ [k]).length, listArr (P ++ [k]) t 0 = listArr (P ++ [k]) t 1) := by
        cases hcg : cmpGt
        · simp only [hcg, Bool.false_eq_true, ↓reduceIte, false_or] at hcmp hcmpOk
          simp only [cmpGt', hcg, Bool.false_or]
          by_cases hlt : r.2 < r.1
          · simp only [decide_eq_true hlt, ↓reduceIte]
            refine ⟨⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩, ?_, ?_⟩
            · intro t' ht'
              have htl : t'.val < P.length := ht'
              rw [listArr_append_left' P [k] t' htl]
              exact hcmp ⟨t'.val, htl⟩
            · simpa [listArr_append_cons_mid P [] k, keyRow_zero, keyRow_one] using hlt
          · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte]
            intro t
            by_cases htl : t.val < P.length
            · rw [listArr_append_left' P [k] t htl]
              exact hcmp ⟨t.val, htl⟩
            · have htlt : t.val < P.length + 1 := by simpa using t.isLt
              have hteq : t = ⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩ :=
                Fin.ext (show t.val = P.length by omega)
              rw [hteq, listArr_append_cons_mid P [] k, keyRow_zero, keyRow_one]
              exact le_antisymm (not_lt.mp hlt) hcmpOk
        · simp only [hcg, ↓reduceIte] at hcmp
          simp only [cmpGt', hcg, Bool.true_or, ↓reduceIte]
          rcases hcmp with ⟨t, hprev, hlt⟩
          refine ⟨⟨t.val, by rw [List.length_append]; omega⟩, ?_, ?_⟩
          · intro t' ht'
            have htl : t'.val < P.length := lt_trans ht' t.isLt
            rw [listArr_append_left' P [k] t' htl]
            exact hprev ⟨t'.val, htl⟩ (Fin.lt_def.mpr ht')
          · simpa [listArr_append_left P [k] t.val t.isLt] using hlt
      have hchain' : ∀ v : Fin 4, ValueChain (listArr (P ++ [k])) v := by
        intro v i j hij hri hrj m hm him hmj
        have hij_val : i.val < j.val := hij
        by_cases hjP : j.val < P.length
        · have hiP : i.val < P.length := lt_trans hij_val hjP
          have hmP : m + 1 < P.length := by omega
          have hriP : HasRowVal (listArr P) v ⟨i.val, hiP⟩ := by
            simpa [HasRowVal, listArr_append_left' P [k] i hiP] using hri
          have hrjP : HasRowVal (listArr P) v ⟨j.val, hjP⟩ := by
            simpa [HasRowVal, listArr_append_left' P [k] j hjP] using hrj
          have hbr := hchain v ⟨i.val, hiP⟩ ⟨j.val, hjP⟩ (Fin.lt_def.mpr hij_val) hriP hrjP m hmP him hmj
          simpa [HasVertBridge, listArr_append_left P [k] m (by omega),
            listArr_append_left P [k] (m + 1) hmP] using hbr
        · have hjlt : j.val < P.length + 1 := by simpa using j.isLt
          have hjEq : j.val = P.length := by omega
          have hiP : i.val < P.length := by omega
          have hPlen : 1 ≤ P.length := by omega
          have hriP : HasRowVal (listArr P) v ⟨i.val, hiP⟩ := by
            simpa [HasRowVal, listArr_append_left' P [k] i hiP] using hri
          have hvSeen : hasSeen s0 s1 s2 s3 v = true := (hseen v).mpr ⟨⟨i.val, hiP⟩, hriP⟩
          have hrj_k : r.1 = v ∨ r.2 = v := by
            have hjeq : j = ⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩ :=
              Fin.ext hjEq
            rw [hjeq] at hrj
            simpa [HasRowVal, listArr_append_cons_mid P [] k, keyRow_zero, keyRow_one] using hrj
          have hvb : vertBridgeBool last r v = true := by
            rcases hrj_k with rfl | rfl
            · rcases hconn1 with hfalse | hvb
              · rw [hvSeen] at hfalse; cases hfalse
              · exact hvb
            · rcases hconn2 with hfalse | hvb
              · rw [hvSeen] at hfalse; cases hfalse
              · exact hvb
          have hPne : P ≠ [] := by intro hnil; subst hnil; simp at hiP
          have hlastP : P.getLast? = some (P.get ⟨P.length - 1, by omega⟩) := by
            rw [List.getLast?_eq_some_getLast hPne, List.getLast_eq_getElem, List.get_eq_getElem]
          rw [hlast, hlastP] at hvb
          simp only [Option.map_some, vertBridgeBool, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at hvb
          have hbrLast : HasVertBridge (listArr (P ++ [k])) v (P.length - 1)
              (by rw [List.length_append, List.length_singleton]; omega) := by
            have h1 : listArr (P ++ [k]) ⟨P.length - 1, by rw [List.length_append]; omega⟩ =
                keyRow (P.get ⟨P.length - 1, by omega⟩) := by
              rw [listArr_append_left P [k] (P.length - 1) (by omega)]; rfl
            have h2 : listArr (P ++ [k])
                ⟨P.length - 1 + 1, by rw [List.length_append, List.length_singleton]; omega⟩ =
                keyRow k := by
              have hc : (⟨P.length - 1 + 1, by rw [List.length_append, List.length_singleton]; omega⟩ :
                  Fin (P ++ [k]).length) =
                  ⟨P.length, by rw [List.length_append, List.length_singleton]; omega⟩ :=
                Fin.ext (show P.length - 1 + 1 = P.length by omega)
              rw [hc, listArr_append_cons_mid P [] k]
            rcases hvb with ⟨hp0, hr0⟩ | ⟨hp1, hr1⟩
            · exact Or.inl ⟨by rw [h1, keyRow_zero]; exact hp0, by rw [h2, keyRow_zero]; exact hr0⟩
            · exact Or.inr ⟨by rw [h1, keyRow_one]; exact hp1, by rw [h2, keyRow_one]; exact hr1⟩
          by_cases hmLast : m = P.length - 1
          · subst hmLast; exact hbrLast
          · have hmP : m + 1 < P.length := by omega
            have hrvLast : HasRowVal (listArr P) v ⟨P.length - 1, by omega⟩ := by
              rcases hvb with ⟨hp0, _⟩ | ⟨hp1, _⟩
              · exact Or.inl (by rw [listArr, keyRow_zero]; exact hp0)
              · exact Or.inr (by rw [listArr, keyRow_one]; exact hp1)
            have hbr := hchain v ⟨i.val, hiP⟩ ⟨P.length - 1, by omega⟩
              (Fin.lt_def.mpr (show i.val < P.length - 1 by omega))
              hriP hrvLast m hmP him (show m < P.length - 1 by omega)
            simpa [HasVertBridge, listArr_append_left P [k] m (by omega),
              listArr_append_left P [k] (m + 1) hmP] using hbr
      have hih := ih (P ++ [k]) (some r) ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 cmpGt'
        ⟨hlast', hseen', hcmp', hchain'⟩
      rw [hcat]
      simpa [validFrom, r, ns, cmpGt', hstep] using hih
    · have hstepF : stepOk last s0 s1 s2 s3 cmpGt r = false := Bool.eq_false_iff.mpr hstep
      simp only [validFrom, r, hstepF, Bool.false_and, Bool.false_eq_true, false_iff, not_and]
      intro _ hchainAll hcolsAll
      simp only [stepOk, Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_eq_false',
        decide_eq_false_iff_not] at hstepF
      rcases hstepF with (⟨hcgF, hrlt⟩ | ⟨hs1, hvb1⟩) | ⟨hs2, hvb2⟩
      · simp only [hcgF, Bool.false_eq_true, ↓reduceIte] at hcmp
        have hrlt' : r.1 < r.2 := not_le.mp hrlt
        rcases hcolsAll with heq | ⟨t, hprev, hlt⟩
        · have hk := heq ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩
          rw [listArr_append_cons_mid P Q k, keyRow_zero, keyRow_one] at hk
          exact ne_of_lt hrlt' hk
        · by_cases htP : t.val < P.length
          · have h1 := hcmp ⟨t.val, htP⟩
            rw [listArr_append_left' P (k :: Q) t htP] at hlt
            exact ne_of_lt hlt h1.symm
          · by_cases htEq : t.val = P.length
            · have hteq : t = ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ :=
                Fin.ext htEq
              rw [hteq, listArr_append_cons_mid P Q k, keyRow_zero, keyRow_one] at hlt
              exact not_lt_of_gt hrlt' hlt
            · have h1 := hprev ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩
                (Fin.lt_def.mpr (show P.length < t.val by omega))
              rw [listArr_append_cons_mid P Q k, keyRow_zero, keyRow_one] at h1
              exact ne_of_lt hrlt' h1
      · rcases (hseen r.1).mp hs1 with ⟨i, hri⟩
        have hPne : P ≠ [] := by intro hnil; subst hnil; exact Fin.elim0 i
        have hPlen : 1 ≤ P.length := by have := i.isLt; omega
        have hlastP : P.getLast? = some (P.get ⟨P.length - 1, by omega⟩) := by
          rw [List.getLast?_eq_some_getLast hPne, List.getLast_eq_getElem, List.get_eq_getElem]
        have hriAll : HasRowVal (listArr (P ++ k :: Q)) r.1
            ⟨i.val, by rw [List.length_append]; omega⟩ := by
          simpa [HasRowVal, listArr_append_left P (k :: Q) i.val i.isLt] using hri
        have hrkAll : HasRowVal (listArr (P ++ k :: Q)) r.1
            ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ := by
          left; rw [listArr_append_cons_mid P Q k, keyRow_zero]
        have hbr := hchainAll r.1
          ⟨i.val, by rw [List.length_append]; omega⟩
          ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩
          (Fin.lt_def.mpr (show i.val < P.length from i.isLt))
          hriAll hrkAll (P.length - 1) (by rw [List.length_append, List.length_cons]; omega)
          (show i.val ≤ P.length - 1 by have := i.isLt; omega)
          (show P.length - 1 < P.length by omega)
        have h1 : listArr (P ++ k :: Q)
            ⟨P.length - 1, by rw [List.length_append]; omega⟩ =
            keyRow (P.get ⟨P.length - 1, by omega⟩) := by
          rw [listArr_append_left P (k :: Q) (P.length - 1) (by omega)]; rfl
        have h2 : listArr (P ++ k :: Q)
            ⟨P.length - 1 + 1, by rw [List.length_append, List.length_cons]; omega⟩ =
            keyRow k := by
          have hc : (⟨P.length - 1 + 1, by rw [List.length_append, List.length_cons]; omega⟩ :
              Fin (P ++ k :: Q).length) =
              ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ :=
            Fin.ext (show P.length - 1 + 1 = P.length by omega)
          rw [hc, listArr_append_cons_mid P Q k]
        rw [hlast, hlastP] at hvb1
        simp only [Option.map_some, vertBridgeBool, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
          decide_eq_false_iff_not] at hvb1
        rcases hbr with ⟨hb0, _⟩ | ⟨hb1, hb1'⟩
        · rw [h1, keyRow_zero] at hb0
          rcases hvb1.1 with hn | hn
          · exact hn hb0
          · exact hn trivial
        · rw [h1, keyRow_one] at hb1; rw [h2, keyRow_one] at hb1'
          rcases hvb1.2 with hn | hn
          · exact hn hb1
          · exact hn hb1'
      · rcases (hseen r.2).mp hs2 with ⟨i, hri⟩
        have hPne : P ≠ [] := by intro hnil; subst hnil; exact Fin.elim0 i
        have hPlen : 1 ≤ P.length := by have := i.isLt; omega
        have hlastP : P.getLast? = some (P.get ⟨P.length - 1, by omega⟩) := by
          rw [List.getLast?_eq_some_getLast hPne, List.getLast_eq_getElem, List.get_eq_getElem]
        have hriAll : HasRowVal (listArr (P ++ k :: Q)) r.2
            ⟨i.val, by rw [List.length_append]; omega⟩ := by
          simpa [HasRowVal, listArr_append_left P (k :: Q) i.val i.isLt] using hri
        have hrkAll : HasRowVal (listArr (P ++ k :: Q)) r.2
            ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ := by
          right; rw [listArr_append_cons_mid P Q k, keyRow_one]
        have hbr := hchainAll r.2
          ⟨i.val, by rw [List.length_append]; omega⟩
          ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩
          (Fin.lt_def.mpr (show i.val < P.length from i.isLt))
          hriAll hrkAll (P.length - 1) (by rw [List.length_append, List.length_cons]; omega)
          (show i.val ≤ P.length - 1 by have := i.isLt; omega)
          (show P.length - 1 < P.length by omega)
        have h1 : listArr (P ++ k :: Q)
            ⟨P.length - 1, by rw [List.length_append]; omega⟩ =
            keyRow (P.get ⟨P.length - 1, by omega⟩) := by
          rw [listArr_append_left P (k :: Q) (P.length - 1) (by omega)]; rfl
        have h2 : listArr (P ++ k :: Q)
            ⟨P.length - 1 + 1, by rw [List.length_append, List.length_cons]; omega⟩ =
            keyRow k := by
          have hc : (⟨P.length - 1 + 1, by rw [List.length_append, List.length_cons]; omega⟩ :
              Fin (P ++ k :: Q).length) =
              ⟨P.length, by rw [List.length_append, List.length_cons]; omega⟩ :=
            Fin.ext (show P.length - 1 + 1 = P.length by omega)
          rw [hc, listArr_append_cons_mid P Q k]
        rw [hlast, hlastP] at hvb2
        simp only [Option.map_some, vertBridgeBool, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
          decide_eq_false_iff_not] at hvb2
        rcases hbr with ⟨hb0, hb0'⟩ | ⟨hb1, _⟩
        · rw [h1, keyRow_zero] at hb0; rw [h2, keyRow_zero] at hb0'
          rcases hvb2.1 with hn | hn
          · exact hn hb0
          · exact hn hb0'
        · rw [h1, keyRow_one] at hb1
          rcases hvb2.2 with hn | hn
          · exact hn hb1
          · exact hn trivial

private lemma isValidSubset_iff_validFrom (S : Finset (Fin 16)) :
    IsValidSubset S ↔ validFrom none false false false false false (S.sort (· ≤ ·)) = true := by
  have hinv0 : PrefixInv [] none false false false false false := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro v
      constructor
      · intro h; fin_cases v <;> simp [hasSeen] at h
      · rintro ⟨t, _⟩; exact Fin.elim0 t
    · intro t; exact Fin.elim0 t
    · intro v i; exact Fin.elim0 i
  have hiff := validFrom_iff (S.sort (· ≤ ·)) [] none false false false false false hinv0
  simp only [List.nil_append] at hiff
  rw [hiff]
  simp only [IsValidSubset, IsValid, list_sort_rowsNondecreasing, true_and,
    valueConnected_iff_valueChain]
  have hall : (∀ v : Fin 4, ∃ t : Fin (S.sort (· ≤ ·)).length,
      ∃ j : Fin 2, listArr (S.sort (· ≤ ·)) t j = v) ↔
      (∀ v : Fin 4, ∃ t : Fin (S.sort (· ≤ ·)).length, HasRowVal (listArr (S.sort (· ≤ ·))) v t) := by
    constructor
    · intro h v; rcases h v with ⟨t, j, hj⟩
      refine ⟨t, ?_⟩; fin_cases j; exact Or.inl hj; exact Or.inr hj
    · intro h v; rcases h v with ⟨t, h0 | h1⟩
      · exact ⟨t, 0, h0⟩
      · exact ⟨t, 1, h1⟩
  rw [hall]

/-! ### Part 6: Single-pass fast DFS summation over `Finset (Fin 16)` -/

private def dfsSum (f : ℕ → ℕ) :
    List (Fin 16) → Option (Fin 4 × Fin 4) → Bool → Bool → Bool → Bool → Bool → ℕ → ℕ
  | [], _, s0, s1, s2, s3, _, len =>
    if s0 && s1 && s2 && s3 then f len else 0
  | k :: rem, last, s0, s1, s2, s3, cmpGt, len =>
    let r := keyPair k
    let ns := setSeen s0 s1 s2 s3 r
    dfsSum f rem last s0 s1 s2 s3 cmpGt len +
    if stepOk last s0 s1 s2 s3 cmpGt r then
      dfsSum f rem (some r) ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 (cmpGt || decide (r.2 < r.1)) (len + 1)
    else 0

private lemma sort_insert_of_lt {k : Fin 16} {S : Finset (Fin 16)} (hk : ∀ x ∈ S, k < x) :
    (insert k S).sort (· ≤ ·) = k :: S.sort (· ≤ ·) := by
  have hkNot : k ∉ S := fun h => lt_irrefl k (hk k h)
  have hperm : ((insert k S).sort (· ≤ ·)).Perm (k :: S.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup ((insert k S).sort_nodup (· ≤ ·))
      (List.nodup_cons.mpr ⟨by simp [Finset.mem_sort, hkNot], S.sort_nodup (· ≤ ·)⟩)]
    intro x
    simp [Finset.mem_sort]
  have hpw1 : ((insert k S).sort (· ≤ ·)).Pairwise (· ≤ ·) := (insert k S).pairwise_sort (· ≤ ·)
  have hpw2 : (k :: S.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_cons]
    exact ⟨fun x hx => le_of_lt (hk x ((Finset.mem_sort (· ≤ ·)).mp hx)), S.pairwise_sort (· ≤ ·)⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hpw1 hpw2

private lemma dfsSum_eq (f : ℕ → ℕ) (rem : List (Fin 16)) :
    rem.Pairwise (· < ·) →
    ∀ (last : Option (Fin 4 × Fin 4)) (s0 s1 s2 s3 cmpGt : Bool) (len : ℕ),
      dfsSum f rem last s0 s1 s2 s3 cmpGt len =
        ∑ S ∈ rem.toFinset.powerset,
          if validFrom last s0 s1 s2 s3 cmpGt (S.sort (· ≤ ·)) then f (len + S.card) else 0 := by
  induction rem with
  | nil =>
    intro _ last s0 s1 s2 s3 cmpGt len
    simp [dfsSum, validFrom]
  | cons k rem ih =>
    intro hpw last s0 s1 s2 s3 cmpGt len
    rw [List.pairwise_cons] at hpw
    rcases hpw with ⟨hklt, hpw'⟩
    have hkNot : k ∉ rem.toFinset := by
      intro hmem
      exact lt_irrefl k (hklt k (List.mem_toFinset.mp hmem))
    have hpow : (k :: rem).toFinset.powerset =
        rem.toFinset.powerset ∪ rem.toFinset.powerset.image (insert k) := by
      rw [List.toFinset_cons, Finset.powerset_insert]
    have hdisj : Disjoint rem.toFinset.powerset (rem.toFinset.powerset.image (insert k)) := by
      rw [Finset.disjoint_left]
      intro S hS1 hS2
      rcases Finset.mem_image.mp hS2 with ⟨S', _, rfl⟩
      have hsub := Finset.mem_powerset.mp hS1
      exact hkNot (hsub (Finset.mem_insert_self k S'))
    have hinj : Set.InjOn (insert k) (rem.toFinset.powerset : Set (Finset (Fin 16))) := by
      intro S₁ hS₁ S₂ hS₂ heq
      have hk1 : k ∉ S₁ := fun h => hkNot (Finset.mem_powerset.mp hS₁ h)
      have hk2 : k ∉ S₂ := fun h => hkNot (Finset.mem_powerset.mp hS₂ h)
      have := congrArg (fun T => T.erase k) heq
      simpa [Finset.erase_insert hk1, Finset.erase_insert hk2] using this
    rw [hpow, Finset.sum_union hdisj, Finset.sum_image hinj]
    simp only [dfsSum]
    rw [ih hpw' last s0 s1 s2 s3 cmpGt len]
    congr 1
    set r := keyPair k
    set ns := setSeen s0 s1 s2 s3 r
    have hsort : ∀ S ∈ rem.toFinset.powerset,
        (insert k S).sort (· ≤ ·) = k :: S.sort (· ≤ ·) ∧ (insert k S).card = S.card + 1 := by
      intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hltS : ∀ x ∈ S, k < x := fun x hx => hklt x (List.mem_toFinset.mp (hsub hx))
      have hkS : k ∉ S := fun h => lt_irrefl k (hltS k h)
      exact ⟨sort_insert_of_lt hltS, Finset.card_insert_of_notMem hkS⟩
    by_cases hstep : stepOk last s0 s1 s2 s3 cmpGt r = true
    · simp only [hstep, ↓reduceIte]
      rw [ih hpw' (some r) ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 (cmpGt || decide (r.2 < r.1)) (len + 1)]
      apply Finset.sum_congr rfl
      intro S hS
      rcases hsort S hS with ⟨hs, hc⟩
      rw [hs, hc]
      have hstep' : stepOk last s0 s1 s2 s3 cmpGt (keyPair k) = true := hstep
      simp only [validFrom, hstep', Bool.true_and, Nat.add_assoc, Nat.add_comm 1 S.card]
      rfl
    · have hstepF : stepOk last s0 s1 s2 s3 cmpGt r = false := Bool.eq_false_iff.mpr hstep
      simp only [hstepF, Bool.false_eq_true, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      rcases hsort S hS with ⟨hs, _⟩
      rw [hs]
      have hstepF' : stepOk last s0 s1 s2 s3 cmpGt (keyPair k) = false := hstepF
      simp [validFrom, hstepF']

/-! Fast single-pass pure `Nat`/`Bool` DFS evaluator (zero `Fin`, zero `div`/`mod`, zero `Decidable`) -/

private structure Counts where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  c7 : ℕ
  c8 : ℕ

private def Counts.zero : Counts := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def Counts.unit : ℕ → Counts
  | 0 => ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩
  | 5 => ⟨0, 0, 0, 0, 0, 1, 0, 0, 0⟩
  | 6 => ⟨0, 0, 0, 0, 0, 0, 1, 0, 0⟩
  | 7 => ⟨0, 0, 0, 0, 0, 0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 1⟩

private def Counts.add (x y : Counts) : Counts :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3,
   x.c4 + y.c4, x.c5 + y.c5, x.c6 + y.c6, x.c7 + y.c7, x.c8 + y.c8⟩

private def Counts.eval (x : Counts) (f : ℕ → ℕ) : ℕ :=
  x.c0 * f 0 + x.c1 * f 1 + x.c2 * f 2 + x.c3 * f 3 +
  x.c4 * f 4 + x.c5 * f 5 + x.c6 * f 6 + x.c7 * f 7

private lemma Counts.eval_zero (f : ℕ → ℕ) : Counts.zero.eval f = 0 := by
  simp [Counts.eval, Counts.zero]

private lemma Counts.eval_add (x y : Counts) (f : ℕ → ℕ) :
    (Counts.add x y).eval f = x.eval f + y.eval f := by
  simp only [Counts.eval, Counts.add]
  ring

private lemma Counts.eval_unit (len : ℕ) (f : ℕ → ℕ) (h8 : (Counts.unit len).c8 = 0) :
    (Counts.unit len).eval f = f len := by
  match len with
  | 0 => simp [Counts.unit, Counts.eval]
  | 1 => simp [Counts.unit, Counts.eval]
  | 2 => simp [Counts.unit, Counts.eval]
  | 3 => simp [Counts.unit, Counts.eval]
  | 4 => simp [Counts.unit, Counts.eval]
  | 5 => simp [Counts.unit, Counts.eval]
  | 6 => simp [Counts.unit, Counts.eval]
  | 7 => simp [Counts.unit, Counts.eval]
  | n + 8 => simp [Counts.unit] at h8

private def hasSeenN (s0 s1 s2 s3 : Bool) : ℕ → Bool
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | _ => s3

private def vertBridgeN (last : Option (ℕ × ℕ)) (a b v : ℕ) : Bool :=
  match last with
  | none => false
  | some (p0, p1) => (Nat.beq p0 v && Nat.beq a v) || (Nat.beq p1 v && Nat.beq b v)

private def stepOkN (last : Option (ℕ × ℕ)) (s0 s1 s2 s3 cmpGt : Bool) (a b : ℕ) : Bool :=
  (cmpGt || Nat.ble b a) &&
  (!hasSeenN s0 s1 s2 s3 a || vertBridgeN last a b a) &&
  (!hasSeenN s0 s1 s2 s3 b || vertBridgeN last a b b)

private def fastDfs :
    List (ℕ × ℕ) → Option (ℕ × ℕ) → Bool → Bool → Bool → Bool → Bool → ℕ → Counts
  | [], _, s0, s1, s2, s3, _, len =>
    if s0 && s1 && s2 && s3 then Counts.unit len else Counts.zero
  | (a, b) :: rem, last, s0, s1, s2, s3, cmpGt, len =>
    let cSkip := fastDfs rem last s0 s1 s2 s3 cmpGt len
    if stepOkN last s0 s1 s2 s3 cmpGt a b then
      let cTake := fastDfs rem (some (a, b))
        (s0 || Nat.beq a 0 || Nat.beq b 0)
        (s1 || Nat.beq a 1 || Nat.beq b 1)
        (s2 || Nat.beq a 2 || Nat.beq b 2)
        (s3 || Nat.beq a 3 || Nat.beq b 3)
        (cmpGt || Nat.ble (b + 1) a)
        (len + 1)
      Counts.add cSkip cTake
    else cSkip

private def pairVal (p : Fin 4 × Fin 4) : ℕ × ℕ := (p.1.val, p.2.val)

private lemma hasSeenN_eq (s0 s1 s2 s3 : Bool) (v : Fin 4) :
    hasSeenN s0 s1 s2 s3 v.val = hasSeen s0 s1 s2 s3 v := by
  fin_cases v <;> rfl

private lemma decide_fin_eq_beq (x y : Fin 4) : decide (x = y) = Nat.beq x.val y.val := by
  fin_cases x <;> fin_cases y <;> rfl

private lemma decide_fin_le_ble (x y : Fin 4) : decide (x ≤ y) = Nat.ble x.val y.val := by
  fin_cases x <;> fin_cases y <;> rfl

private lemma decide_fin_lt_ble (x y : Fin 4) : decide (x < y) = Nat.ble (x.val + 1) y.val := by
  fin_cases x <;> fin_cases y <;> rfl

private lemma vertBridgeN_eq (last : Option (Fin 4 × Fin 4)) (r : Fin 4 × Fin 4) (v : Fin 4) :
    vertBridgeN (last.map pairVal) r.1.val r.2.val v.val = vertBridgeBool last r v := by
  cases last with
  | none => rfl
  | some p =>
    simp only [Option.map_some, pairVal, vertBridgeN, vertBridgeBool, decide_fin_eq_beq]

private lemma stepOkN_eq (last : Option (Fin 4 × Fin 4)) (s0 s1 s2 s3 cmpGt : Bool)
    (r : Fin 4 × Fin 4) :
    stepOkN (last.map pairVal) s0 s1 s2 s3 cmpGt r.1.val r.2.val =
      stepOk last s0 s1 s2 s3 cmpGt r := by
  simp only [stepOkN, stepOk, hasSeenN_eq, vertBridgeN_eq, decide_fin_le_ble]

private lemma dfsSum_eq_fastDfs (f : ℕ → ℕ) (rem : List (Fin 16)) :
    ∀ (last : Option (Fin 4 × Fin 4)) (s0 s1 s2 s3 cmpGt : Bool) (len : ℕ),
      (fastDfs (rem.map (pairVal ∘ keyPair)) (last.map pairVal) s0 s1 s2 s3 cmpGt len).c8 = 0 →
      dfsSum f rem last s0 s1 s2 s3 cmpGt len =
        (fastDfs (rem.map (pairVal ∘ keyPair)) (last.map pairVal) s0 s1 s2 s3 cmpGt len).eval f := by
  induction rem with
  | nil =>
    intro last s0 s1 s2 s3 cmpGt len h8
    simp only [List.map_nil, fastDfs, dfsSum] at h8 ⊢
    split_ifs at h8 ⊢
    · exact (Counts.eval_unit len f h8).symm
    · exact (Counts.eval_zero f).symm
  | cons k rem ih =>
    intro last s0 s1 s2 s3 cmpGt len h8
    simp only [List.map_cons, Function.comp_apply, pairVal, fastDfs, stepOkN_eq] at h8 ⊢
    simp only [dfsSum]
    set r := keyPair k
    set ns := setSeen s0 s1 s2 s3 r
    have hns0 : (s0 || Nat.beq r.1.val 0 || Nat.beq r.2.val 0) = ns.1 := by
      simp [ns, setSeen, decide_fin_eq_beq]
    have hns1 : (s1 || Nat.beq r.1.val 1 || Nat.beq r.2.val 1) = ns.2.1 := by
      simp [ns, setSeen, decide_fin_eq_beq]
    have hns2 : (s2 || Nat.beq r.1.val 2 || Nat.beq r.2.val 2) = ns.2.2.1 := by
      simp [ns, setSeen, decide_fin_eq_beq]
    have hns3 : (s3 || Nat.beq r.1.val 3 || Nat.beq r.2.val 3) = ns.2.2.2 := by
      simp [ns, setSeen, decide_fin_eq_beq]
    have hlt : Nat.ble (r.2.val + 1) r.1.val = decide (r.2 < r.1) :=
      (decide_fin_lt_ble r.2 r.1).symm
    rw [hns0, hns1, hns2, hns3, hlt] at h8 ⊢
    by_cases hstep : stepOk last s0 s1 s2 s3 cmpGt r = true
    · simp only [hstep, ↓reduceIte, Counts.add] at h8
      have h8_skip : (fastDfs (rem.map (pairVal ∘ keyPair)) (last.map pairVal)
          s0 s1 s2 s3 cmpGt len).c8 = 0 := by omega
      have h8_take : (fastDfs (rem.map (pairVal ∘ keyPair)) ((some r).map pairVal)
          ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 (cmpGt || decide (r.2 < r.1)) (len + 1)).c8 = 0 := by
        simp only [Option.map_some, pairVal]
        omega
      simp only [hstep, ↓reduceIte, Counts.eval_add]
      rw [ih last s0 s1 s2 s3 cmpGt len h8_skip]
      rw [ih (some r) ns.1 ns.2.1 ns.2.2.1 ns.2.2.2 (cmpGt || decide (r.2 < r.1)) (len + 1) h8_take]
      rfl
    · simp only [hstep, ↓reduceIte, add_zero] at h8 ⊢
      exact ih last s0 s1 s2 s3 cmpGt len h8

private def fastRows : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3),
   (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3),
   (3, 0), (3, 1), (3, 2), (3, 3)]

private lemma map_finRange16_eq_fastRows :
    (List.finRange 16).map (pairVal ∘ keyPair) = fastRows := rfl

private lemma fastDfs_val :
    fastDfs fastRows none false false false false false 0 =
      ⟨0, 0, 4, 41, 84, 68, 26, 4, 0⟩ := rfl

private lemma finRange16_pairwise_lt : (List.finRange 16).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp [List.getElem_finRange, hij]

private lemma finRange16_toFinset : (List.finRange 16).toFinset = Finset.univ := by
  ext x
  simp

private lemma dfsSum_eval_general (f : ℕ → ℕ) :
    dfsSum f (List.finRange 16) none false false false false false 0 =
      4 * f 2 + 41 * f 3 + 84 * f 4 + 68 * f 5 + 26 * f 6 + 4 * f 7 := by
  have h8 : (fastDfs ((List.finRange 16).map (pairVal ∘ keyPair))
      (none.map pairVal) false false false false false 0).c8 = 0 := by
    rw [map_finRange16_eq_fastRows]
    change (fastDfs fastRows none false false false false false 0).c8 = 0
    rw [fastDfs_val]
  rw [dfsSum_eq_fastDfs f (List.finRange 16) none false false false false false 0 h8,
    map_finRange16_eq_fastRows]
  change (fastDfs fastRows none false false false false false 0).eval f = _
  rw [fastDfs_val]
  simp [Counts.eval]

open Classical in
private lemma a_eq_choose_formula {n : ℕ} (hn : 1 ≤ n) :
    a n =
      4 * (n - 1).choose 1 + 41 * (n - 1).choose 2 + 84 * (n - 1).choose 3 +
      68 * (n - 1).choose 4 + 26 * (n - 1).choose 5 + 4 * (n - 1).choose 6 := by
  rw [a_eq_sum_validSubsets hn]
  have hcongr : (∑ S : Finset (Fin 16), if IsValidSubset S then (n - 1).choose (S.card - 1) else 0) =
      ∑ S ∈ (List.finRange 16).toFinset.powerset,
        if validFrom none false false false false false (S.sort (· ≤ ·)) then
          (n - 1).choose ((0 + S.card) - 1)
        else 0 := by
    rw [finRange16_toFinset, Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro S _
    simp only [zero_add, isValidSubset_iff_validFrom]
  rw [hcongr, ← dfsSum_eq (fun k => (n - 1).choose (k - 1)) (List.finRange 16)
    finRange16_pairwise_lt none false false false false false 0, dfsSum_eval_general]

/-! ### Part 7: Closed-form polynomial, recurrence, and generating function -/

private lemma a_zero : a 0 = 0 := by
  classical
  rw [a, Nat.card_eq_fintype_card]
  have : IsEmpty {A : Fin 0 → Fin 2 → Fin 4 // IsValid A} :=
    ⟨fun ⟨_, hA⟩ => by rcases hA.1 0 with ⟨i, _, _⟩; exact Fin.elim0 i⟩
  exact Fintype.card_eq_zero

private lemma choose_cast_desc (m k : ℕ) :
    ((k.factorial : ℚ) * (m.choose k : ℚ)) = ((m.descFactorial k : ℕ) : ℚ) := by
  exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose m k).symm

private lemma descFactorial_cast (m : ℕ) : ∀ k : ℕ,
    ((m.descFactorial k : ℕ) : ℚ) = ∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ))
  | 0 => by simp
  | k + 1 => by
    rw [Nat.descFactorial_succ, Finset.prod_range_succ]
    by_cases h : k ≤ m
    · rw [Nat.cast_mul, descFactorial_cast m k, Nat.cast_sub h]
      ring
    · have hzero : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have hprod : ∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ)) = 0 := by
        rw [← descFactorial_cast m k, hzero]; simp
      rw [hzero, hprod]; simp

private lemma a_closed_form :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) =
        ((n : ℚ) ^ 6 + 18 * (n : ℚ) ^ 5 + 100 * (n : ℚ) ^ 4 -
          731 * (n : ℚ) ^ 2 + 792 * (n : ℚ) - 180) / 180 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq_choose_formula (by omega)]
  simp only [Nat.add_sub_cancel]
  have hc1 : (m.choose 1 : ℚ) = (m : ℚ) := by simp
  have hc2 : (m.choose 2 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
    calc (m.choose 2 : ℚ) = ((2 : ℕ).factorial : ℚ) * (m.choose 2 : ℚ) / 2 := by
            norm_num [Nat.factorial]
      _ = ((m.descFactorial 2 : ℕ) : ℚ) / 2 := by rw [choose_cast_desc]
      _ = (∏ i ∈ Finset.range 2, ((m : ℚ) - (i : ℚ))) / 2 := by rw [descFactorial_cast]
      _ = (m : ℚ) * ((m : ℚ) - 1) / 2 := by simp [Finset.prod_range_succ]
  have hc3 : (m.choose 3 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
    calc (m.choose 3 : ℚ) = ((3 : ℕ).factorial : ℚ) * (m.choose 3 : ℚ) / 6 := by
            norm_num [Nat.factorial]
      _ = ((m.descFactorial 3 : ℕ) : ℚ) / 6 := by rw [choose_cast_desc]
      _ = (∏ i ∈ Finset.range 3, ((m : ℚ) - (i : ℚ))) / 6 := by rw [descFactorial_cast]
      _ = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by simp [Finset.prod_range_succ]
  have hc4 : (m.choose 4 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) / 24 := by
    calc (m.choose 4 : ℚ) = ((4 : ℕ).factorial : ℚ) * (m.choose 4 : ℚ) / 24 := by
            norm_num [Nat.factorial]
      _ = ((m.descFactorial 4 : ℕ) : ℚ) / 24 := by rw [choose_cast_desc]
      _ = (∏ i ∈ Finset.range 4, ((m : ℚ) - (i : ℚ))) / 24 := by rw [descFactorial_cast]
      _ = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) / 24 := by
            simp [Finset.prod_range_succ]
  have hc5 : (m.choose 5 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) / 120 := by
    calc (m.choose 5 : ℚ) = ((5 : ℕ).factorial : ℚ) * (m.choose 5 : ℚ) / 120 := by
            norm_num [Nat.factorial]
      _ = ((m.descFactorial 5 : ℕ) : ℚ) / 120 := by rw [choose_cast_desc]
      _ = (∏ i ∈ Finset.range 5, ((m : ℚ) - (i : ℚ))) / 120 := by rw [descFactorial_cast]
      _ = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) / 120 := by
            simp [Finset.prod_range_succ]
  have hc6 : (m.choose 6 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) * ((m : ℚ) - 5) /
        720 := by
    calc (m.choose 6 : ℚ) = ((6 : ℕ).factorial : ℚ) * (m.choose 6 : ℚ) / 720 := by
            norm_num [Nat.factorial]
      _ = ((m.descFactorial 6 : ℕ) : ℚ) / 720 := by rw [choose_cast_desc]
      _ = (∏ i ∈ Finset.range 6, ((m : ℚ) - (i : ℚ))) / 720 := by rw [descFactorial_cast]
      _ = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) * ((m : ℚ) - 5) /
            720 := by simp [Finset.prod_range_succ]
  push_cast
  rw [hc1, hc2, hc3, hc4, hc5, hc6]
  ring

private lemma a_recurrence :
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) =
        7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have hq : ((a (k + 8) : ℤ) : ℚ) =
      ((7 * (a (k + 7) : ℤ) - 21 * (a (k + 6) : ℤ) + 35 * (a (k + 5) : ℤ) -
        35 * (a (k + 4) : ℤ) + 21 * (a (k + 3) : ℤ) - 7 * (a (k + 2) : ℤ) +
        (a (k + 1) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [a_closed_form (k + 8) (by omega), a_closed_form (k + 7) (by omega),
      a_closed_form (k + 6) (by omega), a_closed_form (k + 5) (by omega),
      a_closed_form (k + 4) (by omega), a_closed_form (k + 3) (by omega),
      a_closed_form (k + 2) (by omega), a_closed_form (k + 1) (by omega)]
    push_cast
    ring
  have hz : (a (k + 8) : ℤ) =
      7 * (a (k + 7) : ℤ) - 21 * (a (k + 6) : ℤ) + 35 * (a (k + 5) : ℤ) -
      35 * (a (k + 4) : ℤ) + 21 * (a (k + 3) : ℤ) - 7 * (a (k + 2) : ℤ) + (a (k + 1) : ℤ) :=
    Int.cast_injective hq
  simpa [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
    show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
    show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega,
    show k + 8 - 7 = k + 1 by omega] using hz

private lemma a_val_1 : (a 1 : ℤ) = 0 := by
  have h := a_closed_form 1 (by omega); norm_num at h; simp [h]
private lemma a_val_2 : (a 2 : ℤ) = 4 := by
  have h := a_closed_form 2 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) by push_cast; exact h)
private lemma a_val_3 : (a 3 : ℤ) = 49 := by
  have h := a_closed_form 3 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 3 : ℤ) : ℚ) = ((49 : ℤ) : ℚ) by push_cast; exact h)
private lemma a_val_4 : (a 4 : ℤ) = 219 := by
  have h := a_closed_form 4 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 4 : ℤ) : ℚ) = ((219 : ℤ) : ℚ) by push_cast; exact h)
private lemma a_val_5 : (a 5 : ℤ) = 666 := by
  have h := a_closed_form 5 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 5 : ℤ) : ℚ) = ((666 : ℤ) : ℚ) by push_cast; exact h)
private lemma a_val_6 : (a 6 : ℤ) = 1636 := by
  have h := a_closed_form 6 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 6 : ℤ) : ℚ) = ((1636 : ℤ) : ℚ) by push_cast; exact h)
private lemma a_val_7 : (a 7 : ℤ) = 3499 := by
  have h := a_closed_form 7 (by omega); norm_num at h
  exact Int.cast_injective (show ((a 7 : ℤ) : ℚ) = ((3499 : ℤ) : ℚ) by push_cast; exact h)

private lemma a_gf :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X ^ 2 *
        (4 + 21 * PowerSeries.X - 40 * PowerSeries.X ^ 2 + 22 * PowerSeries.X ^ 3 -
          2 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) := by
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hF : ∀ n, PowerSeries.coeff n F = (a n : ℤ) := fun n => PowerSeries.coeff_mk n _
  have hL : F * (1 - PowerSeries.X) ^ 7 =
      F - PowerSeries.C 7 * (PowerSeries.X * F) +
      PowerSeries.C 21 * (PowerSeries.X ^ 2 * F) -
      PowerSeries.C 35 * (PowerSeries.X ^ 3 * F) +
      PowerSeries.C 35 * (PowerSeries.X ^ 4 * F) -
      PowerSeries.C 21 * (PowerSeries.X ^ 5 * F) +
      PowerSeries.C 7 * (PowerSeries.X ^ 6 * F) -
      PowerSeries.X ^ 7 * F := by
    simp only [map_ofNat]
    ring
  have hR : PowerSeries.X ^ 2 *
      (4 + 21 * PowerSeries.X - 40 * PowerSeries.X ^ 2 + 22 * PowerSeries.X ^ 3 -
        2 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) =
      PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2 +
      PowerSeries.C (21 : ℤ) * PowerSeries.X ^ 3 -
      PowerSeries.C (40 : ℤ) * PowerSeries.X ^ 4 +
      PowerSeries.C (22 : ℤ) * PowerSeries.X ^ 5 -
      PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 6 -
      PowerSeries.X ^ 7 := by
    simp only [map_ofNat]
    ring
  change F * (1 - PowerSeries.X) ^ 7 = _
  rw [hL, hR]
  ext n
  have hX1G : ∀ (G : PowerSeries ℤ) (m : ℕ),
      PowerSeries.coeff m (PowerSeries.X * G) =
        if 1 ≤ m then PowerSeries.coeff (m - 1) G else 0 := by
    intro G m
    cases m with
    | zero => simp [PowerSeries.coeff_zero_X_mul]
    | succ m => simp [PowerSeries.coeff_succ_X_mul]
  have hXp : ∀ (k m : ℕ), PowerSeries.coeff m (PowerSeries.X ^ k * F) =
      if k ≤ m then (a (m - k) : ℤ) else 0 := by
    intro k
    induction k with
    | zero => intro m; simp [hF]
    | succ k ih =>
      intro m
      rw [pow_succ', mul_assoc, hX1G]
      cases m with
      | zero => simp
      | succ m =>
        simp only [Nat.succ_le_succ_iff, Nat.zero_le, ↓reduceIte, Nat.add_sub_cancel, ih]
        split_ifs <;> simp [Nat.succ_sub_succ]
  have hX1 : ∀ m : ℕ, PowerSeries.coeff m (PowerSeries.X * F) =
      if 1 ≤ m then (a (m - 1) : ℤ) else 0 := by
    intro m
    simpa [pow_one] using hXp 1 m
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hF, hXp, hX1]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]
  · simp [a_zero, a_val_1, a_val_2, a_val_3]
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]
  · have hrec := a_recurrence (k + 8) (by omega)
    simp only [show ¬(k + 8 = 2) by omega, show ¬(k + 8 = 3) by omega,
      show ¬(k + 8 = 4) by omega, show ¬(k + 8 = 5) by omega,
      show ¬(k + 8 = 6) by omega, show ¬(k + 8 = 7) by omega,
      show 1 ≤ k + 8 by omega, show 2 ≤ k + 8 by omega, show 3 ≤ k + 8 by omega,
      show 4 ≤ k + 8 by omega, show 5 ≤ k + 8 by omega, show 6 ≤ k + 8 by omega,
      show 7 ≤ k + 8 by omega, ↓reduceIte]
    linarith

end OMA.S_oeis_a166826.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a166826.main :=
  ⟨OMA.S_oeis_a166826.Proof.a_closed_form,
   OMA.S_oeis_a166826.Proof.a_gf,
   OMA.S_oeis_a166826.Proof.a_recurrence⟩
