import OMAStatements.S_oeis_a233078

namespace A233078Proof

open OMA.S_oeis_a233078 PowerSeries Finset

def swap12 : Fin 4 → Fin 4
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3

lemma swap12_invol (v : Fin 4) : swap12 (swap12 v) = v := by
  fin_cases v <;> rfl

lemma swap12_sum_ne3 (a b : Fin 4) :
    (swap12 a).val + (swap12 b).val ≠ 3 ↔ a.val + b.val ≠ 3 := by
  fin_cases a <;> fin_cases b <;> decide

def swapArr {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : Fin n → Fin 4 → Fin 4 :=
  fun i j => swap12 (x i j)

lemma swapArr_invol {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : swapArr (swapArr x) = x := by
  funext i j; exact swap12_invol (x i j)

lemma cond_swapArr {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : Cond (swapArr x) ↔ Cond x := by
  unfold Cond swapArr
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j j' hj => (swap12_sum_ne3 _ _).mp (h1 i j j' hj),
           fun i i' j j' hi hj => (swap12_sum_ne3 _ _).mp (h2 i i' j j' hi hj)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j j' hj => (swap12_sum_ne3 _ _).mpr (h1 i j j' hj),
           fun i i' j j' hi hj => (swap12_sum_ne3 _ _).mpr (h2 i i' j j' hi hj)⟩

def TopZero {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : Prop :=
  ∀ i j, i.val = 0 → j.val = 0 → x i j = 0

instance {n : ℕ} : DecidablePred (@TopZero n) := fun x => by unfold TopZero; infer_instance

lemma topZero_swapArr {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : TopZero (swapArr x) ↔ TopZero x := by
  unfold TopZero swapArr
  constructor
  · intro h i j hi hj
    have hv := congrArg swap12 (h i j hi hj)
    rwa [swap12_invol] at hv
  · intro h i j hi hj
    rw [h i j hi hj]; rfl

lemma eq_zero_of_no_12 {n : ℕ} (x : Fin n → Fin 4 → Fin 4)
    (hc : Cond x) (htz : TopZero x) (hno : ∀ i j, x i j ≠ 1 ∧ x i j ≠ 2) :
    x = fun _ _ => 0 := by
  have h03 : ∀ i j, x i j = 0 ∨ x i j = 3 := by
    intro i j
    have h := hno i j
    generalize hv : x i j = v at h
    fin_cases v <;> simp_all
  have hrow : ∀ (i : ℕ) (hi : i < n), ∀ j : Fin 4, x ⟨i, hi⟩ j = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi j
      have h0 : x ⟨0, hi⟩ 0 = 0 := htz ⟨0, hi⟩ 0 rfl rfl
      have h1 : x ⟨0, hi⟩ 1 = 0 := by
        rcases h03 ⟨0, hi⟩ 1 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨0, hi⟩ 0 1 rfl; rw [h0, h] at this; exact this rfl
      have h2 : x ⟨0, hi⟩ 2 = 0 := by
        rcases h03 ⟨0, hi⟩ 2 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨0, hi⟩ 1 2 rfl; rw [h1, h] at this; exact this rfl
      have h3 : x ⟨0, hi⟩ 3 = 0 := by
        rcases h03 ⟨0, hi⟩ 3 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨0, hi⟩ 2 3 rfl; rw [h2, h] at this; exact this rfl
      fin_cases j <;> assumption
    | succ i ih =>
      intro hi j
      have hip : x ⟨i, by omega⟩ 1 = 0 := ih (by omega) 1
      have h0 : x ⟨i + 1, hi⟩ 0 = 0 := by
        rcases h03 ⟨i + 1, hi⟩ 0 with h | h
        · exact h
        · exfalso; have := hc.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ 1 0 rfl rfl
          rw [hip, h] at this; exact this rfl
      have h1 : x ⟨i + 1, hi⟩ 1 = 0 := by
        rcases h03 ⟨i + 1, hi⟩ 1 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨i + 1, hi⟩ 0 1 rfl; rw [h0, h] at this; exact this rfl
      have h2 : x ⟨i + 1, hi⟩ 2 = 0 := by
        rcases h03 ⟨i + 1, hi⟩ 2 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨i + 1, hi⟩ 1 2 rfl; rw [h1, h] at this; exact this rfl
      have h3 : x ⟨i + 1, hi⟩ 3 = 0 := by
        rcases h03 ⟨i + 1, hi⟩ 3 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨i + 1, hi⟩ 2 3 rfl; rw [h2, h] at this; exact this rfl
      fin_cases j <;> assumption
  funext i j
  exact hrow i.1 i.2 j

lemma norm_zero (n : ℕ) : Norm (fun (_ : Fin n) (_ : Fin 4) => (0 : Fin 4)) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ h => by simp at h⟩

lemma cond_zero (n : ℕ) : Cond (fun (_ : Fin n) (_ : Fin 4) => (0 : Fin 4)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩

lemma norm_xor_swap {n : ℕ} (x : Fin n → Fin 4 → Fin 4)
    (hc : Cond x) (htz : TopZero x) (hne : x ≠ fun _ _ => 0) :
    Norm x ↔ ¬ Norm (swapArr x) := by
  have hex : ∃ k : ℕ, ∃ (i : Fin n) (j : Fin 4), i.1 * 4 + j.1 = k ∧ (x i j = 1 ∨ x i j = 2) := by
    by_contra hall
    apply hne
    apply eq_zero_of_no_12 x hc htz
    intro i j
    refine ⟨fun h1 => hall ⟨i.1 * 4 + j.1, i, j, rfl, Or.inl h1⟩,
            fun h2 => hall ⟨i.1 * 4 + j.1, i, j, rfl, Or.inr h2⟩⟩
  classical
  let k0 := Nat.find hex
  have hk0 := Nat.find_spec hex
  have hmin : ∀ (i' : Fin n) (j' : Fin 4), i'.1 * 4 + j'.1 < k0 → x i' j' ≠ 1 ∧ x i' j' ≠ 2 := by
    intro i' j' hlt
    have hnot := Nat.find_min hex hlt
    exact ⟨fun h1 => hnot ⟨i', j', rfl, Or.inl h1⟩, fun h2 => hnot ⟨i', j', rfl, Or.inr h2⟩⟩
  rcases hk0 with ⟨i0, j0, hpos, h12⟩
  have hord : ∀ (i' i : Fin n) (j' j : Fin 4),
      (i' < i ∨ (i' = i ∧ j' < j)) ↔ i'.1 * 4 + j'.1 < i.1 * 4 + j.1 := by
    intro i' i j' j
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · have := j'.2; have := j.2; have : i'.1 < i.1 := h; omega
      · have : j'.1 < j.1 := h; omega
    · intro h
      by_cases heq : i'.1 = i.1
      · right; exact ⟨Fin.ext heq, by show j'.1 < j.1; omega⟩
      · left; show i'.1 < i.1; have := j'.2; have := j.2; omega
  rcases h12 with h1 | h2
  · have hnx : Norm x := by
      refine ⟨htz, fun i j h2 => ?_⟩
      have hge : k0 ≤ i.1 * 4 + j.1 := by
        by_contra hlt; exact (hmin i j (by omega)).2 h2
      have hne_pos : i0.1 * 4 + j0.1 ≠ i.1 * 4 + j.1 := by
        intro heq
        have hi : i0 = i := Fin.ext (by have := j0.2; have := j.2; omega)
        have hj : j0 = j := Fin.ext (by have := j0.2; have := j.2; omega)
        rw [hi, hj, h2] at h1; exact absurd h1 (by decide)
      exact ⟨i0, j0, (hord i0 i j0 j).mpr (by omega), h1⟩
    have hns : ¬ Norm (swapArr x) := by
      intro hns
      have hs2 : swapArr x i0 j0 = 2 := by simp [swapArr, h1, swap12]
      rcases hns.2 i0 j0 hs2 with ⟨i', j', hlt, hs1⟩
      have hx2 : x i' j' = 2 := by
        have hv := congrArg swap12 hs1
        dsimp only [swapArr] at hv
        rw [swap12_invol] at hv
        exact hv
      exact (hmin i' j' (by dsimp only [k0]; rw [← hpos]; exact (hord i' i0 j' j0).mp hlt)).2 hx2
    exact ⟨fun _ => hns, fun _ => hnx⟩
  · have hnx : ¬ Norm x := by
      intro hnx
      rcases hnx.2 i0 j0 h2 with ⟨i', j', hlt, hx1⟩
      exact (hmin i' j' (by dsimp only [k0]; rw [← hpos]; exact (hord i' i0 j' j0).mp hlt)).1 hx1
    have hns : Norm (swapArr x) := by
      refine ⟨(topZero_swapArr x).mpr htz, fun i j hs2 => ?_⟩
      have hx1 : x i j = 1 := by
        have hv := congrArg swap12 hs2
        dsimp only [swapArr] at hv
        rw [swap12_invol] at hv
        exact hv
      have hge : k0 ≤ i.1 * 4 + j.1 := by
        by_contra hlt; exact (hmin i j (by omega)).1 hx1
      have hne_pos : i0.1 * 4 + j0.1 ≠ i.1 * 4 + j.1 := by
        intro heq
        have hi : i0 = i := Fin.ext (by have := j0.2; have := j.2; omega)
        have hj : j0 = j := Fin.ext (by have := j0.2; have := j.2; omega)
        rw [hi, hj, hx1] at h2; exact absurd h2 (by decide)
      exact ⟨i0, j0, (hord i0 i j0 j).mpr (by omega), by simp [swapArr, h2, swap12]⟩
    exact ⟨fun h => absurd h hnx, fun h => absurd hns h⟩

def U (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 4 → Fin 4)).filter (fun x => Cond x ∧ TopZero x)).card

lemma two_mul_a_eq_U_add_one (n : ℕ) : 2 * a n = U n + 1 := by
  let S := (univ : Finset (Fin n → Fin 4 → Fin 4)).filter (fun x => Cond x ∧ TopZero x)
  let z : Fin n → Fin 4 → Fin 4 := fun _ _ => 0
  let Spos := S.filter (fun x => Norm x ∧ x ≠ z)
  let Sneg := S.filter (fun x => ¬ Norm x ∧ x ≠ z)
  have hbij : Spos.card = Sneg.card := by
    refine Finset.card_bij (fun x _ => swapArr x) ?_ ?_ ?_
    · intro x hx
      simp only [Spos, S, mem_filter, mem_univ, true_and] at hx
      simp only [Sneg, S, mem_filter, mem_univ, true_and]
      refine ⟨⟨(cond_swapArr x).mpr hx.1.1, (topZero_swapArr x).mpr hx.1.2⟩,
              (norm_xor_swap x hx.1.1 hx.1.2 hx.2.2).mp hx.2.1, ?_⟩
      intro heq; apply hx.2.2
      have := congrArg swapArr heq; rw [swapArr_invol] at this; exact this
    · intro x1 _ x2 _ h
      have := congrArg swapArr h; rwa [swapArr_invol, swapArr_invol] at this
    · intro y hy
      simp only [Sneg, S, mem_filter, mem_univ, true_and] at hy
      refine ⟨swapArr y, ?_, swapArr_invol y⟩
      simp only [Spos, S, mem_filter, mem_univ, true_and]
      have hne : swapArr y ≠ z := by
        intro heq; apply hy.2.2
        have := congrArg swapArr heq; rw [swapArr_invol] at this; exact this
      have hc' : Cond (swapArr y) := (cond_swapArr y).mpr hy.1.1
      have htz' : TopZero (swapArr y) := (topZero_swapArr y).mpr hy.1.2
      refine ⟨⟨hc', htz'⟩, ?_, hne⟩
      have hxor := norm_xor_swap (swapArr y) hc' htz' hne
      rw [swapArr_invol] at hxor
      exact hxor.mpr hy.2.1
  have ha_eq : a n = Spos.card + 1 := by
    have hset : (univ : Finset (Fin n → Fin 4 → Fin 4)).filter (fun x => Cond x ∧ Norm x) =
        insert z Spos := by
      ext x
      simp only [mem_insert, Spos, S, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hc, hn⟩
        by_cases hxz : x = z
        · exact Or.inl hxz
        · exact Or.inr ⟨⟨hc, hn.1⟩, hn, hxz⟩
      · rintro (rfl | ⟨⟨hc, _⟩, hn, _⟩)
        · exact ⟨cond_zero n, norm_zero n⟩
        · exact ⟨hc, hn⟩
    unfold a
    rw [hset, card_insert_of_notMem]
    simp [Spos]
  have hU_eq : U n = Spos.card + Sneg.card + 1 := by
    have hdisj : Disjoint Spos Sneg := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Spos, Sneg, mem_filter] at hx1 hx2
      exact hx2.2.1 hx1.2.1
    have hunion : S = insert z (Spos ∪ Sneg) := by
      ext x
      simp only [mem_insert, mem_union, Spos, Sneg, S, mem_filter, mem_univ, true_and]
      constructor
      · intro hx
        by_cases hxz : x = z
        · exact Or.inl hxz
        · by_cases hn : Norm x
          · exact Or.inr (Or.inl ⟨hx, hn, hxz⟩)
          · exact Or.inr (Or.inr ⟨hx, hn, hxz⟩)
      · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
        · exact ⟨cond_zero n, fun _ _ _ _ => rfl⟩
        · exact hx
        · exact hx
    change S.card = Spos.card + Sneg.card + 1
    rw [hunion, card_insert_of_notMem, card_union_of_disjoint hdisj]
    simp [Spos, Sneg]
  omega

def validRow (r : Fin 4 → Fin 4) : Prop :=
  ∀ j j' : Fin 4, j'.val = j.val + 1 → (r j).val + (r j').val ≠ 3

def validNext (r r' : Fin 4 → Fin 4) : Prop :=
  validRow r' ∧ ∀ j j' : Fin 4, j.val = j'.val + 1 → (r j).val + (r' j').val ≠ 3

instance : DecidablePred validRow := fun r => by unfold validRow; infer_instance
instance (r : Fin 4 → Fin 4) : DecidablePred (validNext r) := fun r' => by unfold validNext; infer_instance

lemma sum_validNext4_same : ∀ x1 x2 x3 : Fin 4,
    x1.val + x2.val ≠ 3 → x2.val + x3.val ≠ 3 →
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      if (a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3 ∧ c.val + d.val ≠ 3 ∧
          x1.val + a.val ≠ 3 ∧ x2.val + b.val ≠ 3 ∧ x3.val + c.val ≠ 3) ∧ b = d
      then 1 else 0) = if x1 = x3 then 17 else 16 := by
  decide

lemma sum_validNext4_diff : ∀ x1 x2 x3 : Fin 4,
    x1.val + x2.val ≠ 3 → x2.val + x3.val ≠ 3 →
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      if (a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3 ∧ c.val + d.val ≠ 3 ∧
          x1.val + a.val ≠ 3 ∧ x2.val + b.val ≠ 3 ∧ x3.val + c.val ≠ 3) ∧ b ≠ d
      then 1 else 0) = if x1 = x3 then 34 else 32 := by
  decide

lemma card_validNext_gen (r : Fin 4 → Fin 4) (P : Fin 4 → Fin 4 → Prop) [∀ b d, Decidable (P b d)] :
    ((univ : Finset (Fin 4 → Fin 4)).filter (fun r' => validNext r r' ∧ P (r' 1) (r' 3))).card =
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      if (a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3 ∧ c.val + d.val ≠ 3 ∧
          (r 1).val + a.val ≠ 3 ∧ (r 2).val + b.val ≠ 3 ∧ (r 3).val + c.val ≠ 3) ∧ P b d
      then 1 else 0 := by
  have hbij : ((univ : Finset (Fin 4 → Fin 4)).filter (fun r' => validNext r r' ∧ P (r' 1) (r' 3))).card =
      ((univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter (fun t =>
        (t.1.val + t.2.1.val ≠ 3 ∧ t.2.1.val + t.2.2.1.val ≠ 3 ∧ t.2.2.1.val + t.2.2.2.val ≠ 3 ∧
         (r 1).val + t.1.val ≠ 3 ∧ (r 2).val + t.2.1.val ≠ 3 ∧ (r 3).val + t.2.2.1.val ≠ 3) ∧
        P t.2.1 t.2.2.2)).card := by
    refine Finset.card_bij (fun r' _ => (r' 0, r' 1, r' 2, r' 3)) ?_ ?_ ?_
    · intro r' hr'
      rcases (mem_filter.mp hr').2 with ⟨hvn, hp⟩
      exact mem_filter.mpr ⟨mem_univ _, ⟨⟨hvn.1 0 1 rfl, hvn.1 1 2 rfl, hvn.1 2 3 rfl,
              hvn.2 1 0 rfl, hvn.2 2 1 rfl, hvn.2 3 2 rfl⟩, hp⟩⟩
    · intro r1 _ r2 _ heq
      funext j; fin_cases j
      · exact congrArg Prod.fst heq
      · exact congrArg (fun p => p.2.1) heq
      · exact congrArg (fun p => p.2.2.1) heq
      · exact congrArg (fun p => p.2.2.2) heq
    · intro ⟨a, b, c, d⟩ ht
      rcases (mem_filter.mp ht).2 with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hp⟩
      let r' : Fin 4 → Fin 4 := fun j => match j with
        | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d
      refine ⟨r', mem_filter.mpr ⟨mem_univ _, ⟨⟨?_, ?_⟩, hp⟩⟩, rfl⟩
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact h1
        · exact h2
        · exact h3
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact h4
        · exact h5
        · exact h6
  rw [hbij, Finset.card_filter]
  simp_rw [Fintype.sum_prod_type]

lemma card_validNext_same (r : Fin 4 → Fin 4) (hr : validRow r) :
    ((univ : Finset (Fin 4 → Fin 4)).filter (fun r' => validNext r r' ∧ r' 1 = r' 3)).card =
      if r 1 = r 3 then 17 else 16 := by
  rw [card_validNext_gen]
  exact sum_validNext4_same (r 1) (r 2) (r 3) (hr 1 2 rfl) (hr 2 3 rfl)

lemma card_validNext_diff (r : Fin 4 → Fin 4) (hr : validRow r) :
    ((univ : Finset (Fin 4 → Fin 4)).filter (fun r' => validNext r r' ∧ r' 1 ≠ r' 3)).card =
      if r 1 = r 3 then 34 else 32 := by
  rw [card_validNext_gen]
  exact sum_validNext4_diff (r 1) (r 2) (r 3) (hr 1 2 rfl) (hr 2 3 rfl)

def Usame (n : ℕ) : ℕ :=
  if hn : 0 < n then
    ((univ : Finset (Fin n → Fin 4 → Fin 4)).filter
      (fun x => Cond x ∧ TopZero x ∧ x ⟨n - 1, by omega⟩ 1 = x ⟨n - 1, by omega⟩ 3)).card
  else 0

def Udiff (n : ℕ) : ℕ :=
  if hn : 0 < n then
    ((univ : Finset (Fin n → Fin 4 → Fin 4)).filter
      (fun x => Cond x ∧ TopZero x ∧ x ⟨n - 1, by omega⟩ 1 ≠ x ⟨n - 1, by omega⟩ 3)).card
  else 0

lemma U_eq_add (n : ℕ) (hn : 1 ≤ n) : U n = Usame n + Udiff n := by
  unfold U Usame Udiff
  have hpos : 0 < n := by omega
  simp only [hpos, ↓reduceDIte]
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro h; by_cases heq : x ⟨n - 1, by omega⟩ 1 = x ⟨n - 1, by omega⟩ 3
      · exact Or.inl ⟨h.1, h.2, heq⟩
      · exact Or.inr ⟨h.1, h.2, heq⟩
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [mem_filter] at h1 h2; exact h2.2.2.2 h1.2.2.2

lemma sum_Usame1 : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    if ((0 : Fin 4).val + a.val ≠ 3 ∧ a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3) ∧ a = c
    then 1 else 0) = 9 := by decide

lemma sum_Udiff1 : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    if ((0 : Fin 4).val + a.val ≠ 3 ∧ a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3) ∧ a ≠ c
    then 1 else 0) = 18 := by decide

lemma U1_gen (P : Fin 4 → Fin 4 → Prop) [∀ a c, Decidable (P a c)] :
    ((univ : Finset (Fin 1 → Fin 4 → Fin 4)).filter
      (fun x => Cond x ∧ TopZero x ∧ P (x 0 1) (x 0 3))).card =
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if ((0 : Fin 4).val + a.val ≠ 3 ∧ a.val + b.val ≠ 3 ∧ b.val + c.val ≠ 3) ∧ P a c
      then 1 else 0 := by
  rw [← Fintype.card_subtype]
  have hbij : Fintype.card { x : Fin 1 → Fin 4 → Fin 4 // Cond x ∧ TopZero x ∧ P (x 0 1) (x 0 3) } =
      Fintype.card { t : Fin 4 × Fin 4 × Fin 4 //
        ((0 : Fin 4).val + t.1.val ≠ 3 ∧ t.1.val + t.2.1.val ≠ 3 ∧ t.2.1.val + t.2.2.val ≠ 3) ∧
        P t.1 t.2.2 } := by
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      have h0 : x 0 0 = 0 := hx.2.1 0 0 rfl rfl
      exact ⟨(x 0 1, x 0 2, x 0 3),
        ⟨⟨by rw [← h0]; exact hx.1.1 0 0 1 rfl, hx.1.1 0 1 2 rfl, hx.1.1 0 2 3 rfl⟩, hx.2.2⟩⟩
    · intro ⟨⟨a, b, c⟩, ht⟩
      let x : Fin 1 → Fin 4 → Fin 4 := fun _ j => match j with
        | ⟨0, _⟩ => 0 | ⟨1, _⟩ => a | ⟨2, _⟩ => b | ⟨3, _⟩ => c
      refine ⟨x, ⟨?_, ?_⟩, ?_, ht.2⟩
      · intro i j j' hj; fin_cases i; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1.1
        · exact ht.1.2.1
        · exact ht.1.2.2
      · intro i i' _ _ hi _; fin_cases i; fin_cases i'; simp at hi
      · intro i j _ hj; fin_cases i; fin_cases j <;> simp at hj ⊢; rfl
    · intro ⟨x, hx⟩
      apply Subtype.ext; funext i j; fin_cases i; fin_cases j
      · exact (hx.2.1 0 0 rfl rfl).symm
      · rfl
      · rfl
      · rfl
    · intro ⟨⟨a, b, c⟩, _⟩; rfl
  rw [hbij, Fintype.card_subtype, Finset.card_filter]
  simp_rw [Fintype.sum_prod_type]

lemma Usame_one : Usame 1 = 9 := by
  unfold Usame; simp only [Nat.one_pos, ↓reduceDIte]
  exact (U1_gen (· = ·)).trans sum_Usame1

lemma Udiff_one : Udiff 1 = 18 := by
  unfold Udiff; simp only [Nat.one_pos, ↓reduceDIte]
  exact (U1_gen (· ≠ ·)).trans sum_Udiff1

lemma U_step (n : ℕ) (hn : 1 ≤ n) :
    Usame (n + 1) = 17 * Usame n + 16 * Udiff n ∧
    Udiff (n + 1) = 34 * Usame n + 32 * Udiff n := by
  let S (m : ℕ) := (univ : Finset (Fin m → Fin 4 → Fin 4)).filter (fun x => Cond x ∧ TopZero x)
  let init : (Fin (n + 1) → Fin 4 → Fin 4) → (Fin n → Fin 4 → Fin 4) :=
    fun x i => x ⟨i.1, by omega⟩
  let snoc : (Fin n → Fin 4 → Fin 4) → (Fin 4 → Fin 4) → (Fin (n + 1) → Fin 4 → Fin 4) :=
    fun x r i => if h : (i : ℕ) < n then x ⟨i.1, h⟩ else r
  have hsnoc_mem : ∀ x ∈ S n, ∀ r : Fin 4 → Fin 4,
      validNext (x ⟨n - 1, by omega⟩) r → snoc x r ∈ S (n + 1) := by
    intro x hx r hr
    simp only [S, mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j j' hj
      dsimp only [snoc]
      split_ifs with hi
      · exact hx.1.1 ⟨i.1, hi⟩ j j' hj
      · exact hr.1 j j' hj
    · intro i i' j j' hi hj
      dsimp only [snoc]
      by_cases hi' : (i' : ℕ) < n
      · have hi1 : (i : ℕ) < n := by omega
        simp only [hi1, hi', ↓reduceDIte]
        exact hx.1.2 ⟨i.1, hi1⟩ ⟨i'.1, hi'⟩ j j' hi hj
      · have hi1 : (i : ℕ) < n := by omega
        have hieq : (⟨i.1, hi1⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        simp only [hi1, hi', ↓reduceDIte, hieq]
        exact hr.2 j j' hj
    · intro i j hi hj
      dsimp only [snoc]
      have h0 : (i : ℕ) < n := by omega
      simp only [h0, ↓reduceDIte]
      exact hx.2 ⟨i.1, h0⟩ j hi hj
  have hgen : ∀ (P : (Fin 4 → Fin 4) → Prop) [DecidablePred P],
      ((S (n + 1)).filter (fun y => P (y ⟨n, Nat.lt_succ_self n⟩))).card =
      ∑ x ∈ S n, ((univ : Finset (Fin 4 → Fin 4)).filter
        (fun r => validNext (x ⟨n - 1, by omega⟩) r ∧ P r)).card := by
    intro P _
    rw [← Finset.card_sigma]
    symm
    refine Finset.card_bij (fun p _ => snoc p.1 p.2) ?_ ?_ ?_
    · intro ⟨x, r⟩ hp
      simp only [mem_sigma, mem_filter, mem_univ, true_and] at hp ⊢
      exact ⟨hsnoc_mem x hp.1 r hp.2.1, by simpa [snoc] using hp.2.2⟩
    · intro ⟨x1, r1⟩ _ ⟨x2, r2⟩ _ heq
      have hx : x1 = x2 := by
        funext i j
        have := congrFun (congrFun heq ⟨i.1, by omega⟩) j
        simpa [snoc, i.2] using this
      have hr : r1 = r2 := by
        funext j
        have := congrFun (congrFun heq ⟨n, Nat.lt_succ_self n⟩) j
        simpa [snoc] using this
      subst hx; subst hr; rfl
    · intro y hy
      simp only [mem_filter, S, mem_univ, true_and] at hy
      refine ⟨⟨init y, y ⟨n, Nat.lt_succ_self n⟩⟩, ?_, ?_⟩
      · simp only [mem_sigma, S, mem_filter, mem_univ, true_and]
        refine ⟨⟨⟨fun i j j' hj => hy.1.1.1 ⟨i.1, by omega⟩ j j' hj,
                  fun i i' j j' hi hj => hy.1.1.2 ⟨i.1, by omega⟩ ⟨i'.1, by omega⟩ j j' hi hj⟩,
                 fun i j hi hj => hy.1.2 ⟨i.1, by omega⟩ j hi hj⟩,
                ⟨⟨fun j j' hj => hy.1.1.1 ⟨n, Nat.lt_succ_self n⟩ j j' hj,
                  fun j j' hj => hy.1.1.2 ⟨n - 1, by omega⟩ ⟨n, Nat.lt_succ_self n⟩ j j' (by dsimp; omega) hj⟩,
                 hy.2⟩⟩
      · funext i j
        dsimp only [snoc, init]
        split_ifs with hi
        · rfl
        · have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega)
          rw [this]
  have hsplit : ∀ (c1 c2 : ℕ),
      (∑ x ∈ S n, if x ⟨n - 1, by omega⟩ 1 = x ⟨n - 1, by omega⟩ 3 then c1 else c2) =
      c1 * Usame n + c2 * Udiff n := by
    intro c1 c2
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        mul_comm _ c1, mul_comm _ c2]
    congr 2
    · unfold Usame; simp only [show 0 < n by omega, ↓reduceDIte, S, Finset.filter_filter]
      congr 1; ext x; simp [and_assoc]
    · unfold Udiff; simp only [show 0 < n by omega, ↓reduceDIte, S, Finset.filter_filter]
      congr 1; ext x; simp [and_assoc]
  constructor
  · have h1 := hgen (fun r => r 1 = r 3)
    have hL : Usame (n + 1) = ((S (n + 1)).filter (fun y => y ⟨n, Nat.lt_succ_self n⟩ 1 = y ⟨n, Nat.lt_succ_self n⟩ 3)).card := by
      unfold Usame; simp only [Nat.succ_pos, ↓reduceDIte, S, Finset.filter_filter]
      congr 1; ext y; simp [and_assoc]
    rw [hL, h1, ← hsplit 17 16]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [S, mem_filter, mem_univ, true_and] at hx
    exact card_validNext_same (x ⟨n - 1, by omega⟩) (fun j j' hj => hx.1.1 ⟨n - 1, by omega⟩ j j' hj)
  · have h1 := hgen (fun r => r 1 ≠ r 3)
    have hL : Udiff (n + 1) = ((S (n + 1)).filter (fun y => y ⟨n, Nat.lt_succ_self n⟩ 1 ≠ y ⟨n, Nat.lt_succ_self n⟩ 3)).card := by
      unfold Udiff; simp only [Nat.succ_pos, ↓reduceDIte, S, Finset.filter_filter]
      congr 1; ext y; simp [and_assoc]
    rw [hL, h1, ← hsplit 34 32]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [S, mem_filter, mem_univ, true_and] at hx
    exact card_validNext_diff (x ⟨n - 1, by omega⟩) (fun j j' hj => hx.1.1 ⟨n - 1, by omega⟩ j j' hj)

lemma U_closed_pair (n : ℕ) (hn : 1 ≤ n) :
    Usame n = 9 * 49 ^ (n - 1) ∧ Udiff n = 18 * 49 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  rw [add_comm 1 k]
  induction k with
  | zero => simp [Usame_one, Udiff_one]
  | succ k ih =>
    have hs := U_step (k + 1) (by omega)
    rcases ih with ⟨h1, h2⟩
    simp only [Nat.add_sub_cancel] at h1 h2 ⊢
    constructor
    · rw [hs.1, h1, h2, pow_succ]; ring
    · rw [hs.2, h1, h2, pow_succ]; ring

lemma a_closed_rat (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (49 + 27 * 49 ^ n) / 98 := by
  have h2 : (2 * a n : ℚ) = (U n : ℚ) + 1 := by exact_mod_cast two_mul_a_eq_U_add_one n
  have hU : U n = 27 * 49 ^ (n - 1) := by
    have := U_eq_add n hn
    rcases U_closed_pair n hn with ⟨h1, h2⟩
    omega
  have hUq : (U n : ℚ) = 27 * (49 : ℚ) ^ (n - 1) := by exact_mod_cast hU
  rw [hUq] at h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 k] at h2 ⊢
  simp only [Nat.add_sub_cancel] at h2
  rw [pow_succ]
  linarith

lemma gf_main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 49 * X)) = 2 * X * (7 - 19 * X) := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs : F * ((1 - X) * (1 - 49 * X)) =
      F - PowerSeries.C (50 : ℚ) * (X ^ 1 * F) + PowerSeries.C (49 : ℚ) * (X ^ 2 * F) := by
    simp only [map_ofNat]; ring
  have hrhs : (2 * X * (7 - 19 * X) : PowerSeries ℚ) =
      PowerSeries.C (14 : ℚ) * (X ^ 1 : PowerSeries ℚ) - PowerSeries.C (38 : ℚ) * (X ^ 2 : PowerSeries ℚ) := by
    simp only [map_ofNat]; ring
  change F * ((1 - X) * (1 - 49 * X)) = 2 * X * (7 - 19 * X)
  rw [hlhs, hrhs]
  have hf : ∀ n : ℕ, (if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      if n = 0 then 0 else (49 + 27 * 49 ^ n) / 98 := by
    intro n; split_ifs with h
    · rfl
    · exact a_closed_rat n (by omega)
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
             PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk, hf]
  rcases k with _ | _ | _ | m
  · norm_num
  · norm_num
  · norm_num
  · have e0 : m + 1 + 1 + 1 = m + 3 := by omega
    have h1 : m + 3 - 1 = m + 2 := by omega
    have h2 : m + 3 - 2 = m + 1 := by omega
    rw [e0, h1, h2]
    have c0 : ¬ (m + 3 = 0) := by omega
    have c1 : ¬ (m + 2 = 0) := by omega
    have c2 : ¬ (m + 1 = 0) := by omega
    have l1 : 1 ≤ m + 3 := by omega
    have l2 : 2 ≤ m + 3 := by omega
    have n1 : ¬ (m + 3 = 1) := by omega
    have n2 : ¬ (m + 3 = 2) := by omega
    simp only [c0, c1, c2, l1, l2, n1, n2, ite_true, ite_false]
    have p1 : (49 : ℚ) ^ (m + 3) = 2401 * (49 : ℚ) ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; ring
    have p2 : (49 : ℚ) ^ (m + 2) = 49 * (49 : ℚ) ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring
    rw [p1, p2]
    ring

end A233078Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a233078.main :=
  ⟨A233078Proof.gf_main, A233078Proof.a_closed_rat⟩
