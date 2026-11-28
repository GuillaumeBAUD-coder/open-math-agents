import OMAStatements.S_oeis_a229472
import Mathlib

-- The result was first settled in writing by Adrian Perez Fontelles and Gaspard Moulinier (OEIS-Settled collection, September 2026); this is an independent Lean formalization.

namespace OMA.Helpers_a229472
open OMA.S_oeis_a229472 Finset

/-- sequences -/
def RGS {n : ℕ} (s : Fin n → Fin 4) : Prop := ∀ i, ∀ u : Fin 4, u < s i → ∃ i', i' < i ∧ s i' = u

instance {n : ℕ} (s : Fin n → Fin 4) : Decidable (RGS s) := by unfold RGS; infer_instance

def defects {n : ℕ} (s : Fin (n + 1) → Fin 4) : ℕ :=
  (univ.filter (fun i : Fin n => s i.castSucc = s i.succ)).card

def toSeq {n : ℕ} (x : Fin n → Fin 1 → Fin 4) : Fin n → Fin 4 := fun i => x i 0

lemma rmn_iff {n : ℕ} (x : Fin n → Fin 1 → Fin 4) : RowMajorNew x ↔ RGS (toSeq x) := by
  unfold RowMajorNew RGS toSeq
  have h0 : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim _ _
  constructor
  · intro h i u hu
    obtain ⟨i', j', hij, he⟩ := h i 0 u hu
    rw [h0 j'] at he
    rcases hij with h1 | ⟨_, h2⟩
    · exact ⟨i', h1, he⟩
    · exact absurd h2 (by rw [h0 j']; exact lt_irrefl _)
  · intro h i j u hu
    rw [h0 j] at hu
    obtain ⟨i', h1, he⟩ := h i u hu
    exact ⟨i', 0, Or.inl h1, he⟩

lemma mistakes_eq {n : ℕ} (x : Fin (n + 1) → Fin 1 → Fin 4) : mistakes x = defects (toSeq x) := by
  unfold mistakes defects toSeq
  have h0 : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim _ _
  symm
  apply Finset.card_bij (fun (i : Fin n) _ => ((i.castSucc, (0 : Fin 1)), (i.succ, (0 : Fin 1))))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    refine ⟨Or.inr (Or.inl ⟨by simp, trivial⟩), hi⟩
  · intro i _ i' _ h
    simp only [Prod.mk.injEq] at h
    exact Fin.castSucc_injective _ h.1.1
  · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨hc, he⟩ := h
    rw [h0 p2, h0 q2] at hc he
    rcases hc with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h3⟩
    · exact absurd h2 (by simp)
    · have hp : p1.val < n := by omega
      refine ⟨⟨p1.val, hp⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have e1 : (⟨p1.val, hp⟩ : Fin n).castSucc = p1 := Fin.ext rfl
        have e2 : (⟨p1.val, hp⟩ : Fin n).succ = q1 := Fin.ext (by simp; omega)
        rw [e1, e2]; exact he
      · simp only [Prod.mk.injEq, h0 p2, h0 q2, and_true]
        exact ⟨Fin.ext rfl, Fin.ext (by simp; omega)⟩
    · exact absurd h3 (by simp)

def mx {n : ℕ} (s : Fin (n + 1) → Fin 4) : ℕ := univ.sup (fun i => (s i).val)

lemma le_mx {n : ℕ} (s : Fin (n + 1) → Fin 4) (i : Fin (n + 1)) : (s i).val ≤ mx s :=
  Finset.le_sup (f := fun i => (s i).val) (Finset.mem_univ i)

lemma mx_lt {n : ℕ} (s : Fin (n + 1) → Fin 4) : mx s < 4 := by
  unfold mx
  apply Nat.lt_of_le_of_lt (Finset.sup_le (fun i _ => Nat.le_of_lt_succ (s i).isLt)) (by norm_num)

lemma exists_mx {n : ℕ} (s : Fin (n + 1) → Fin 4) : ∃ i, (s i).val = mx s := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image univ (fun i => (s i).val) univ_nonempty
  refine ⟨i, le_antisymm (le_mx s i) (Finset.sup_le fun j _ => hi j (mem_univ j))⟩

lemma occurs {n : ℕ} (s : Fin (n + 1) → Fin 4) (h : RGS s) (u : Fin 4) (hu : u.val ≤ mx s) :
    ∃ j, s j = u := by
  obtain ⟨i, hi⟩ := exists_mx s
  rcases Nat.lt_or_ge u.val (mx s) with h1 | h1
  · obtain ⟨j, _, hj⟩ := h i u (by rw [Fin.lt_def, hi]; exact h1)
    exact ⟨j, hj⟩
  · exact ⟨i, Fin.ext (by omega)⟩

lemma snoc_cast {n : ℕ} (s : Fin (n + 1) → Fin 4) (c : Fin 4) (i : Fin (n + 1)) :
    (Fin.snoc s c : Fin (n + 2) → Fin 4) i.castSucc = s i := Fin.snoc_castSucc (α := fun _ => Fin 4) ..

lemma snoc_last {n : ℕ} (s : Fin (n + 1) → Fin 4) (c : Fin 4) :
    (Fin.snoc s c : Fin (n + 2) → Fin 4) (Fin.last (n + 1)) = c := Fin.snoc_last (α := fun _ => Fin 4) ..

lemma mx_snoc {n : ℕ} (s : Fin (n + 1) → Fin 4) (c : Fin 4) :
    mx (Fin.snoc s c : Fin (n + 2) → Fin 4) = max (mx s) c.val := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [snoc_last]; exact le_max_right _ _
    · rw [snoc_cast]; exact le_trans (le_mx s j) (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le; intro j _
      have := le_mx (Fin.snoc s c : Fin (n + 2) → Fin 4) j.castSucc
      rwa [snoc_cast] at this
    · have := le_mx (Fin.snoc s c : Fin (n + 2) → Fin 4) (Fin.last _)
      rwa [snoc_last] at this

lemma rgs_snoc {n : ℕ} (s : Fin (n + 1) → Fin 4) (c : Fin 4) :
    RGS (Fin.snoc s c : Fin (n + 2) → Fin 4) ↔ RGS s ∧ c.val ≤ mx s + 1 := by
  constructor
  · intro h
    have hs : RGS s := by
      intro i u hu
      have := h i.castSucc u (by rwa [snoc_cast])
      obtain ⟨i', hi', he⟩ := this
      have hi'' : i'.val < n + 1 := by rw [Fin.lt_def] at hi'; simp at hi'; omega
      refine ⟨⟨i'.val, hi''⟩, by rw [Fin.lt_def] at hi' ⊢; simpa using hi', ?_⟩
      have e : (⟨i'.val, hi''⟩ : Fin (n + 1)).castSucc = i' := Fin.ext rfl
      rw [← e, snoc_cast] at he; exact he
    refine ⟨hs, ?_⟩
    by_contra hc
    have hm := mx_lt s
    obtain ⟨i', hi', he⟩ := h (Fin.last _) ⟨mx s + 1, by omega⟩ (by
      rw [snoc_last, Fin.lt_def]; simp only; omega)
    have hi'' : i'.val < n + 1 := by rw [Fin.lt_def] at hi'; simp at hi'; omega
    have e : (⟨i'.val, hi''⟩ : Fin (n + 1)).castSucc = i' := Fin.ext rfl
    rw [← e, snoc_cast] at he
    have := le_mx s ⟨i'.val, hi''⟩
    rw [he] at this; simp at this
  · rintro ⟨hs, hc⟩ i u hu
    refine Fin.lastCases ?_ (fun j hu => ?_) i hu
    · intro hu
      rw [snoc_last] at hu
      obtain ⟨j, hj⟩ := occurs s hs u (by rw [Fin.lt_def] at hu; omega)
      exact ⟨j.castSucc, Fin.castSucc_lt_last j, by rw [snoc_cast]; exact hj⟩
    · rw [snoc_cast] at hu
      obtain ⟨j', hj', he⟩ := hs j u hu
      exact ⟨j'.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hj', by rw [snoc_cast]; exact he⟩

lemma defects_snoc {n : ℕ} (s : Fin (n + 1) → Fin 4) (c : Fin 4) :
    defects (Fin.snoc s c : Fin (n + 2) → Fin 4) = defects s + if s (Fin.last n) = c then 1 else 0 := by
  unfold defects
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [snoc_cast, Fin.succ_castSucc, snoc_cast]
  · rw [Fin.succ_last, snoc_last]
    have : (Fin.last n).castSucc = Fin.castSucc (Fin.last n) := rfl
    rw [snoc_cast]

def S (n m v d : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4)).filter (fun s =>
    RGS s ∧ mx s = m ∧ (s (Fin.last n)).val = v ∧ min (defects s) 2 = d)).card

def snocEquiv (n : ℕ) : (Fin (n + 1) → Fin 4) × Fin 4 ≃ (Fin (n + 2) → Fin 4) where
  toFun sc := Fin.snoc sc.1 sc.2
  invFun t := (Fin.init t, t (Fin.last _))
  left_inv sc := by
    obtain ⟨s, c⟩ := sc
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv t := by simp only [Fin.snoc_init_self]

lemma sum_snoc {n : ℕ} (G : (Fin (n + 2) → Fin 4) → ℕ) :
    ∑ t, G t = ∑ s : Fin (n + 1) → Fin 4, ∑ c : Fin 4, G (Fin.snoc s c) := by
  rw [← (snocEquiv n).sum_comp, Fintype.sum_prod_type]; rfl

def cond (m v d m' v' d' : ℕ) : Prop :=
  v' < 4 ∧ v' ≤ m + 1 ∧ m' = max m v' ∧ d' = min (d + if v = v' then 1 else 0) 2

instance (m v d m' v' d' : ℕ) : Decidable (cond m v d m' v' d') := by unfold cond; infer_instance

lemma S_succ (n m' v' d' : ℕ) : S (n + 1) m' v' d' =
    ∑ m ∈ range 4, ∑ v ∈ range 4, ∑ d ∈ range 3, if cond m v d m' v' d' then S n m v d else 0 := by
  unfold S
  rw [Finset.card_filter, sum_snoc]
  -- collapse c
  have h1 : ∀ s : Fin (n + 1) → Fin 4, (∑ c : Fin 4, if RGS (Fin.snoc s c : Fin (n + 2) → Fin 4) ∧
      mx (Fin.snoc s c : Fin (n + 2) → Fin 4) = m' ∧
      ((Fin.snoc s c : Fin (n + 2) → Fin 4) (Fin.last (n + 1))).val = v' ∧
      min (defects (Fin.snoc s c : Fin (n + 2) → Fin 4)) 2 = d' then 1 else 0) =
      if RGS s ∧ cond (mx s) (s (Fin.last n)).val (min (defects s) 2) m' v' d' then 1 else 0 := by
    intro s
    simp only [rgs_snoc, mx_snoc, snoc_last, defects_snoc]
    by_cases hv : v' < 4
    · rw [Finset.sum_eq_single ⟨v', hv⟩]
      · have e1 : (if s (Fin.last n) = (⟨v', hv⟩ : Fin 4) then 1 else 0) =
            (if (s (Fin.last n)).val = v' then 1 else 0) := by
          by_cases h : s (Fin.last n) = ⟨v', hv⟩
          · rw [if_pos h, if_pos (by rw [h])]
          · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]
        simp only [e1, cond, hv, true_and]
        by_cases h2 : RGS s
        · simp only [h2, true_and]
          congr 1; apply propext
          split_ifs <;> omega
        · simp [h2]
      · intro c _ hc
        rw [if_neg]
        rintro ⟨_, _, h, _⟩
        exact hc (Fin.ext h)
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [cond, hv]
      · intro c _
        rw [if_neg]
        rintro ⟨_, _, h, _⟩
        exact hv (h ▸ c.isLt)
  simp only [h1]
  -- fiber over the state
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 4 ×ˢ range 4 ×ˢ range 3)
    (g := fun s : Fin (n + 1) → Fin 4 => (mx s, (s (Fin.last n)).val, min (defects s) 2))
    (fun s _ => by
      have := mx_lt s; have := (s (Fin.last n)).isLt
      simp only [Finset.mem_product, Finset.mem_range]; omega)]
  rw [Finset.sum_product, Finset.sum_congr rfl fun m _ => Finset.sum_product _ _ _]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_filter, Finset.card_filter]
  by_cases hc : cond m v d m' v' d'
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (mx s, (s (Fin.last n)).val, min (defects s) 2) = (m, v, d)
    · rw [if_pos h]
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [h1, h2, h3, hc, and_true]
    · rw [if_neg h, if_neg]
      rintro ⟨_, h1, h2, h3⟩
      exact h (by rw [h1, h2, h3])
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro s _
    by_cases h : (mx s, (s (Fin.last n)).val, min (defects s) 2) = (m, v, d)
    · rw [if_pos h]
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [h1, h2, h3, hc, and_false, if_false]
    · rw [if_neg h]

def Sv : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, m, v, d => if m = 0 ∧ v = 0 ∧ d = 0 then 1 else 0
  | n + 1, m', v', d' => ∑ m ∈ range 4, ∑ v ∈ range 4, ∑ d ∈ range 3,
      if cond m v d m' v' d' then Sv n m v d else 0

lemma S_zero : ∀ m < 4, ∀ v < 4, ∀ d < 3, S 0 m v d = Sv 0 m v d := by decide +kernel

lemma S_eq_Sv (n : ℕ) : ∀ m < 4, ∀ v < 4, ∀ d < 3, S n m v d = Sv n m v d := by
  induction n with
  | zero => exact S_zero
  | succ n ih =>
    intro m' _ v' _ d' _
    rw [S_succ]
    show _ = ∑ m ∈ range 4, ∑ v ∈ range 4, ∑ d ∈ range 3, if cond m v d m' v' d' then Sv n m v d else 0
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_range] at hm hv hd
    rw [ih m hm v hv d hd]

def A (n : ℕ) : ℕ := ∑ m ∈ range 4, ∑ v ∈ range 4, Sv n m v 1

lemma a_eq (n : ℕ) : a (n + 1) = A n := by
  have h1 : a (n + 1) = ((univ : Finset (Fin (n + 1) → Fin 4)).filter (fun s => defects s = 1 ∧ RGS s)).card := by
    unfold a
    apply Finset.card_equiv (Equiv.arrowCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) (Fin 4)))
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e : (Equiv.arrowCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) (Fin 4))) x = toSeq x := by
      funext i; simp [toSeq, Equiv.arrowCongr_apply]
    rw [e, mistakes_eq, rmn_iff]
  rw [h1, Finset.card_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 4 ×ˢ range 4)
    (g := fun s : Fin (n + 1) → Fin 4 => (mx s, (s (Fin.last n)).val))
    (fun s _ => by
      have := mx_lt s; have := (s (Fin.last n)).isLt
      simp only [Finset.mem_product, Finset.mem_range]; omega)]
  rw [A, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_range] at hm hv
  rw [← S_eq_Sv n m hm v hv 1 (by norm_num), S, Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (mx s, (s (Fin.last n)).val) = (m, v)
  · rw [if_pos h]
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [h1, h2, true_and]
    have : min (defects s) 2 = 1 ↔ defects s = 1 := by omega
    simp only [this, and_comm]
  · rw [if_neg h, if_neg]
    rintro ⟨_, h1, h2, _⟩
    exact h (by rw [h1, h2])

def c8 : ℕ → ℤ := fun k => [1, -10, 35, -40, -37, 110, -35, -60, 36].getD k 0

def Wv (m m' v' d' : ℕ) : ℤ := ∑ k ∈ range 9, c8 k * (Sv (m + 8 - k) m' v' d' : ℤ)

lemma W2 : ∀ m < 4, ∀ v < 4, ∀ d < 2, Wv 2 m v d = 0 := by decide +kernel

lemma Wv_succ (m : ℕ) (m' v' d' : ℕ) : Wv (m + 1) m' v' d' =
    ∑ mm ∈ range 4, ∑ v ∈ range 4, ∑ d ∈ range 3, if cond mm v d m' v' d' then Wv m mm v d else 0 := by
  unfold Wv
  have h : ∀ k ∈ range 9, c8 k * (Sv (m + 1 + 8 - k) m' v' d' : ℤ) =
      ∑ mm ∈ range 4, ∑ v ∈ range 4, ∑ d ∈ range 3,
        c8 k * (if cond mm v d m' v' d' then (Sv (m + 8 - k) mm v d : ℤ) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show m + 1 + 8 - k = (m + 8 - k) + 1 by omega]
    simp only [Sv]
    push_cast
    simp only [Finset.mul_sum]
    try (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
         split_ifs <;> simp)
  rw [Finset.sum_congr rfl h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun mm _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

lemma W_zero : ∀ m, 2 ≤ m → ∀ m' < 4, ∀ v' < 4, ∀ d' < 2, Wv m m' v' d' = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact W2
  | succ m hm ih =>
    intro m' _ v' _ d' hd'
    rw [Wv_succ]
    apply Finset.sum_eq_zero; intro mm hmm
    apply Finset.sum_eq_zero; intro v hv
    apply Finset.sum_eq_zero; intro d hd
    rw [Finset.mem_range] at hmm hv hd
    split_ifs with hc
    · by_cases hd2 : d < 2
      · exact ih mm hmm v hv d hd2
      · exfalso; unfold cond at hc; split_ifs at hc <;> omega
    · rfl

lemma A_rec8 (m : ℕ) (hm : 2 ≤ m) : ∑ k ∈ range 9, c8 k * (A (m + 8 - k) : ℤ) = 0 := by
  simp only [A]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro mm hmm
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro v hv
  rw [Finset.mem_range] at hmm hv
  exact W_zero m hm mm hmm v hv 1 (by norm_num)

lemma Avals : A 0 = 0 ∧ A 1 = 1 ∧ A 2 = 2 ∧ A 3 = 6 ∧ A 4 = 20 ∧ A 5 = 70 ∧ A 6 = 246 ∧ A 7 = 854 ∧
    A 8 = 2920 ∧ A 9 = 9846 := by decide +kernel

def B (n : ℕ) : ℤ := (A (n + 4) : ℤ) - 8 * A (n + 3) + 22 * A (n + 2) - 24 * A (n + 1) + 9 * A n

lemma B_zero : ∀ n, 2 ≤ n → B n = 0 := by
  have hrec : ∀ n, 2 ≤ n → B (n + 4) = 2 * B (n + 3) + 3 * B (n + 2) - 4 * B (n + 1) - 4 * B n := by
    intro n hn
    have h := A_rec8 n hn
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, c8, List.getD_cons_zero,
      List.getD_cons_succ, Nat.sub_zero] at h
    rw [show n + 8 - 1 = n + 7 by omega, show n + 8 - 2 = n + 6 by omega, show n + 8 - 3 = n + 5 by omega,
      show n + 8 - 4 = n + 4 by omega, show n + 8 - 5 = n + 3 by omega, show n + 8 - 6 = n + 2 by omega,
      show n + 8 - 7 = n + 1 by omega, show n + 8 - 8 = n by omega] at h
    unfold B
    rw [show n + 4 + 4 = n + 8 by ring, show n + 4 + 3 = n + 7 by ring, show n + 4 + 2 = n + 6 by ring,
      show n + 4 + 1 = n + 5 by ring, show n + 3 + 4 = n + 7 by ring, show n + 3 + 3 = n + 6 by ring,
      show n + 3 + 2 = n + 5 by ring, show n + 3 + 1 = n + 4 by ring, show n + 2 + 4 = n + 6 by ring,
      show n + 2 + 3 = n + 5 by ring, show n + 2 + 2 = n + 4 by ring, show n + 2 + 1 = n + 3 by ring,
      show n + 1 + 4 = n + 5 by ring, show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring]
    linear_combination h
  obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Avals
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | rfl | h6'
    · simp [B, h2, h3, h4, h5, h6]
    · simp [B, h3, h4, h5, h6, h7]
    · simp [B, h4, h5, h6, h7, h8]
    · simp [B, h5, h6, h7, h8, h9]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [hrec k (by omega), ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega),
        ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
      ring

end OMA.Helpers_a229472

open OMA.S_oeis_a229472 OMA.Helpers_a229472 in
theorem OMA.solution : type_of% @OMA.S_oeis_a229472.main := by
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _, _⟩ := Avals
  have v1 : a 1 = 0 := by rw [a_eq 0, h0]
  have v2 : a 2 = 1 := by rw [a_eq 1, h1]
  have v3 : a 3 = 2 := by rw [a_eq 2, h2]
  have v4 : a 4 = 6 := by rw [a_eq 3, h3]
  have v5 : a 5 = 20 := by rw [a_eq 4, h4]
  have v6 : a 6 = 70 := by rw [a_eq 5, h5]
  have hrec : ∀ k : ℕ, 2 ≤ k → (a (k + 5) : ℤ) = 8 * a (k + 4) - 22 * a (k + 3) + 24 * a (k + 2) - 9 * a (k + 1) := by
    intro k hk
    have := B_zero k hk
    unfold B at this
    rw [a_eq, a_eq, a_eq, a_eq, a_eq]
    linear_combination this
  refine ⟨?_, ?_⟩
  · set G : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hG
    have hL : G * ((1 - PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X) ^ 2) = G - 8 * (G * PowerSeries.X ^ 1) +
        22 * (G * PowerSeries.X ^ 2) - 24 * (G * PowerSeries.X ^ 3) + 9 * (G * PowerSeries.X ^ 4) := by ring
    have hR : (PowerSeries.X ^ 2 * (1 - 6 * PowerSeries.X + 12 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 4) : PowerSeries ℚ) = PowerSeries.X ^ 2 - 6 * PowerSeries.X ^ 3 +
          12 * PowerSeries.X ^ 4 - 8 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6 := by ring
    rw [hL, hR]
    ext d
    simp only [map_add, map_sub, ← map_ofNat PowerSeries.C, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul_X_pow', hG, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases (show d ≤ 6 ∨ 7 ≤ d by omega) with hd | hd
    · interval_cases d <;> simp [v1, v2, v3, v4, v5, v6] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
      have h' : (a (k + 5) : ℚ) = 8 * a (k + 4) - 22 * a (k + 3) + 24 * a (k + 2) - 9 * a (k + 1) := by
        exact_mod_cast hrec k (by omega)
      have e1 : k + 5 - 1 = k + 4 := by omega
      have e2 : k + 5 - 2 = k + 3 := by omega
      have e3 : k + 5 - 3 = k + 2 := by omega
      have e4 : k + 5 - 4 = k + 1 := by omega
      have c1 : 1 ≤ k + 5 := by omega
      have c2 : 2 ≤ k + 5 := by omega
      have c3 : 3 ≤ k + 5 := by omega
      have c4 : 4 ≤ k + 5 := by omega
      have n0 : k + 5 ≠ 0 := by omega
      have n1 : k + 4 ≠ 0 := by omega
      have n2 : k + 3 ≠ 0 := by omega
      have n3 : k + 2 ≠ 0 := by omega
      have n4 : k + 1 ≠ 0 := by omega
      have m2 : k + 5 ≠ 2 := by omega
      have m3 : k + 5 ≠ 3 := by omega
      have m4 : k + 5 ≠ 4 := by omega
      have m5 : k + 5 ≠ 5 := by omega
      have m6 : k + 5 ≠ 6 := by omega
      simp only [e1, e2, e3, e4, c1, c2, c3, c4, n0, n1, n2, n3, n4, m2,
        ↓reduceIte, PowerSeries.coeff_C]
      first | (split_ifs <;> first | omega | linear_combination h') | linear_combination h'
  · intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | rfl | rfl | h7
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
        have h' : (a (k + 5) : ℚ) = 8 * a (k + 4) - 22 * a (k + 3) + 24 * a (k + 2) - 9 * a (k + 1) := by
          exact_mod_cast hrec k (by omega)
        rw [h', ih (k + 4) (by omega) (by omega), ih (k + 3) (by omega) (by omega),
          ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
        push_cast
        ring
