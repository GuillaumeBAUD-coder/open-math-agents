import OMAStatements.S_oeis_a187156

/-!
A187156. A 3-step one-space bishop tour visits three distinct squares.
The twelve direction pairs that do not reverse immediately have row/column
spans in `{(2,2), (2,1), (1,2)}`, four pairs each. Each pair of span `(H, W)`
fits on `(n - H) * (n - W)` starts, and the resulting quadratic is Barker's
formula. The recurrence and the generating function are the third difference
of that quadratic, checked directly on the two initial terms where it does not
yet apply.
-/

namespace BishopA187156

open OMA.S_oeis_a187156

def D : Fin 4 → ℤ × ℤ
  | 0 => (1, 1)
  | 1 => (1, -1)
  | 2 => (-1, 1)
  | 3 => (-1, -1)

def opp : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

def stepOf (d : ℤ × ℤ) : Fin 4 :=
  if d.1 = 1 then
    if d.2 = 1 then 0 else 1
  else
    if d.2 = 1 then 2 else 3

def onBoard (n x : ℕ) (d : ℤ) : Prop :=
  0 ≤ (x : ℤ) + d ∧ (x : ℤ) + d < n

instance (n x : ℕ) (d : ℤ) : Decidable (onBoard n x d) := by
  unfold onBoard
  infer_instance

def fits {n : ℕ} (s : Square n) (d : ℤ × ℤ) : Prop :=
  onBoard n s.1.val d.1 ∧ onBoard n s.2.val d.2

instance {n : ℕ} (s : Square n) (d : ℤ × ℤ) : Decidable (fits s d) := by
  unfold fits
  infer_instance

def land (n x : ℕ) (d : ℤ) (h : onBoard n x d) : Fin n :=
  ⟨((x : ℤ) + d).toNat, by
    have hn : n ≠ 0 := by
      have h0 := h.1
      have h1 := h.2
      omega
    rw [Int.toNat_lt_of_ne_zero hn]
    exact h.2⟩

lemma val_land {n x : ℕ} {d : ℤ} (h : onBoard n x d) :
    ((land n x d h).val : ℤ) = (x : ℤ) + d := by
  simp only [land]
  exact Int.toNat_of_nonneg h.1

lemma diag_D (i : Fin 4) : IsDiag (D i) := by
  fin_cases i <;> simp [IsDiag, D]

lemma D_fst_ne_zero (i : Fin 4) : (D i).1 ≠ 0 := by
  fin_cases i <;> simp [D]

lemma D_snd_ne_zero (i : Fin 4) : (D i).2 ≠ 0 := by
  fin_cases i <;> simp [D]

lemma D_pm (i : Fin 4) :
    ((D i).1 = 1 ∨ (D i).1 = -1) ∧ ((D i).2 = 1 ∨ (D i).2 = -1) := by
  fin_cases i <;> simp [D]

lemma stepOf_D (i : Fin 4) : stepOf (D i) = i := by
  fin_cases i <;> simp [stepOf, D]

lemma stepOf_diag (d : ℤ × ℤ) (hd : IsDiag d) : D (stepOf d) = d := by
  rcases hd with ⟨hr | hr, hc | hc⟩ <;>
    (simp [stepOf, D, hr, hc]; exact Prod.ext hr.symm hc.symm)

lemma neg_index (i : Fin 4) : stepOf (-(D i).1, -(D i).2) = opp i := by
  fin_cases i <;> simp [stepOf, D, opp]

lemma add_zero_iff (i j : Fin 4) : D i + D j = (0, 0) ↔ j = opp i := by
  constructor
  · intro h
    have hr : (D j).1 = -(D i).1 := by
      have := congrArg Prod.fst h
      simp only [Prod.fst_add] at this
      linarith
    have hc : (D j).2 = -(D i).2 := by
      have := congrArg Prod.snd h
      simp only [Prod.snd_add] at this
      linarith
    calc
      j = stepOf (D j) := (stepOf_D j).symm
      _ = stepOf (-(D i).1, -(D i).2) := by
        congr 1
        exact Prod.ext hr hc
      _ = opp i := neg_index i
  · intro hj
    fin_cases i <;> simp [hj, D, opp]

lemma delta_add {n : ℕ} (a b c : Square n) : delta a b + delta b c = delta a c := by
  apply Prod.ext
  · simp only [delta, Prod.fst_add]
    ring
  · simp only [delta, Prod.snd_add]
    ring

lemma fits_delta {n : ℕ} (s q : Square n) : fits s (delta s q) := by
  unfold fits onBoard delta
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (0 : ℤ) ≤ q.1.val := Int.natCast_nonneg _
    omega
  · have := q.1.isLt
    omega
  · have : (0 : ℤ) ≤ q.2.val := Int.natCast_nonneg _
    omega
  · have := q.2.isLt
    omega

lemma eq_of_delta_zero {n : ℕ} {p q : Square n} (h : delta p q = (0, 0)) : p = q := by
  apply Prod.ext
  · apply Fin.ext
    have hr := congrArg Prod.fst h
    simp only [delta] at hr
    omega
  · apply Fin.ext
    have hc := congrArg Prod.snd h
    simp only [delta] at hc
    omega

lemma eq_of_same_delta {n : ℕ} {s p q : Square n} (h : delta s p = delta s q) : p = q := by
  apply Prod.ext
  · apply Fin.ext
    have hr := congrArg Prod.fst h
    simp only [delta] at hr
    omega
  · apply Fin.ext
    have hc := congrArg Prod.snd h
    simp only [delta] at hc
    omega

lemma ne_of_delta {n : ℕ} {p q : Square n} (h : delta p q ≠ (0, 0)) : p ≠ q := by
  intro hpq
  apply h
  subst hpq
  simp [delta]

def rebuild {n : ℕ} (i j : Fin 4) (s : Square n)
    (h1 : fits s (D i)) (h2 : fits s (D i + D j)) : Fin 3 → Square n
  | 0 => s
  | 1 => (land n s.1.val (D i).1 h1.1, land n s.2.val (D i).2 h1.2)
  | 2 => (land n s.1.val (D i + D j).1 h2.1, land n s.2.val (D i + D j).2 h2.2)

lemma rebuild_zero {n : ℕ} (i j : Fin 4) (s : Square n) (h1 h2) :
    rebuild i j s h1 h2 0 = s := rfl

lemma delta_rebuild_01 {n : ℕ} (i j : Fin 4) (s : Square n) (h1 h2) :
    delta s (rebuild i j s h1 h2 1) = D i := by
  apply Prod.ext <;> simp only [delta, rebuild, val_land] <;> ring

lemma delta_rebuild_12 {n : ℕ} (i j : Fin 4) (s : Square n) (h1 h2) :
    delta (rebuild i j s h1 h2 1) (rebuild i j s h1 h2 2) = D j := by
  apply Prod.ext
  · simp only [delta, rebuild, val_land, Prod.fst_add]
    ring
  · simp only [delta, rebuild, val_land, Prod.snd_add]
    ring

lemma delta_rebuild_02 {n : ℕ} (i j : Fin 4) (s : Square n) (h1 h2) :
    delta s (rebuild i j s h1 h2 2) = D i + D j := by
  apply Prod.ext <;> simp only [delta, rebuild, val_land] <;> ring

lemma inj_of_ne3 {α : Type*} (p : Fin 3 → α)
    (h01 : p 0 ≠ p 1) (h02 : p 0 ≠ p 2) (h12 : p 1 ≠ p 2) : Function.Injective p := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact (h01 hab).elim
  · exact (h02 hab).elim
  · exact (h01 hab.symm).elim
  · rfl
  · exact (h12 hab).elim
  · exact (h02 hab.symm).elim
  · exact (h12 hab.symm).elim
  · rfl

lemma rebuild_tour {n : ℕ} (i j : Fin 4) (s : Square n) (hne : j ≠ opp i) (h1 h2) :
    IsTour (rebuild i j s h1 h2) := by
  refine ⟨?_, ?_, ?_⟩
  · apply inj_of_ne3
    · exact ne_of_delta (by
        rw [rebuild_zero, delta_rebuild_01]
        intro h
        exact D_fst_ne_zero i (congrArg Prod.fst h))
    · exact ne_of_delta (by
        rw [rebuild_zero, delta_rebuild_02]
        intro h
        exact hne ((add_zero_iff i j).mp h))
    · exact ne_of_delta (by
        rw [delta_rebuild_12]
        intro h
        exact D_fst_ne_zero j (congrArg Prod.fst h))
  · rw [rebuild_zero, delta_rebuild_01]
    exact diag_D i
  · rw [delta_rebuild_12]
    exact diag_D j

def encode {n : ℕ} (p : Fin 3 → Square n) : (Fin 4 × Fin 4) × Square n :=
  ((stepOf (delta (p 0) (p 1)), stepOf (delta (p 1) (p 2))), p 0)

def tourSet (n : ℕ) : Finset (Fin 3 → Square n) :=
  Finset.univ.filter IsTour

def codeSet (n : ℕ) : Finset ((Fin 4 × Fin 4) × Square n) :=
  Finset.univ.filter fun t =>
    t.1.2 ≠ opp t.1.1 ∧ fits t.2 (D t.1.1) ∧ fits t.2 (D t.1.1 + D t.1.2)

lemma a_tour (n : ℕ) : a n = (tourSet n).card := by
  simp [a, tourSet]

lemma encode_mem {n : ℕ} {p : Fin 3 → Square n} (hp : p ∈ tourSet n) :
    encode p ∈ codeSet n := by
  simp only [tourSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [codeSet, encode, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : delta (p 0) (p 1) = D (stepOf (delta (p 0) (p 1))) :=
    (stepOf_diag _ hp.2.1).symm
  have h2 : delta (p 1) (p 2) = D (stepOf (delta (p 1) (p 2))) :=
    (stepOf_diag _ hp.2.2).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hopp
    have hsum : D (stepOf (delta (p 0) (p 1))) + D (stepOf (delta (p 1) (p 2))) = (0, 0) :=
      (add_zero_iff _ _).mpr hopp
    have hzero : delta (p 0) (p 2) = (0, 0) := by
      rw [← delta_add (p 0) (p 1) (p 2), h1, h2]
      exact hsum
    exact hp.1.ne (by decide : (0 : Fin 3) ≠ 2) (eq_of_delta_zero hzero)
  · rw [← h1]
    exact fits_delta (p 0) (p 1)
  · rw [← h1, ← h2, delta_add]
    exact fits_delta (p 0) (p 2)

lemma encode_inj {n : ℕ} {p q : Fin 3 → Square n}
    (hp : p ∈ tourSet n) (hq : q ∈ tourSet n) (h : encode p = encode q) : p = q := by
  simp only [tourSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  simp only [encode, Prod.mk.injEq] at h
  obtain ⟨⟨hi, hj⟩, hs⟩ := h
  have dp : delta (p 0) (p 1) = delta (q 0) (q 1) := by
    rw [(stepOf_diag _ hp.2.1).symm, (stepOf_diag _ hq.2.1).symm, hi]
  have d2 : delta (p 1) (p 2) = delta (q 1) (q 2) := by
    rw [(stepOf_diag _ hp.2.2).symm, (stepOf_diag _ hq.2.2).symm, hj]
  have p1 : p 1 = q 1 := by
    rw [hs] at dp
    exact eq_of_same_delta dp
  have p2 : p 2 = q 2 := by
    rw [p1] at d2
    exact eq_of_same_delta d2
  funext t
  fin_cases t
  · exact hs
  · exact p1
  · exact p2

lemma encode_rebuild {n : ℕ} (i j : Fin 4) (s : Square n) (h1 h2) :
    encode (rebuild i j s h1 h2) = ((i, j), s) := by
  simp only [encode, rebuild_zero, delta_rebuild_01, delta_rebuild_12, stepOf_D]

lemma card_code (n : ℕ) : (tourSet n).card = (codeSet n).card := by
  refine Finset.card_bij (s := tourSet n) (t := codeSet n)
    (fun p _ => encode p) (fun p hp => encode_mem hp)
    (fun p hp q hq h => encode_inj hp hq h) ?_
  intro c hc
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨hne, hf1, hf2⟩ := hc
  refine ⟨rebuild c.1.1 c.1.2 c.2 hf1 hf2, ?_, ?_⟩
  · simp only [tourSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact rebuild_tour c.1.1 c.1.2 c.2 hne hf1 hf2
  · simpa using encode_rebuild c.1.1 c.1.2 c.2 hf1 hf2

lemma card_val_lt (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter fun x : Fin n => x.val < k).card = k := by
  classical
  have hbij := Finset.card_bij
    (s := (Finset.univ : Finset (Fin k)))
    (t := Finset.univ.filter fun x : Fin n => x.val < k)
    (fun (i : Fin k) _ => (⟨i.val, by omega⟩ : Fin n))
    (fun i _ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact i.isLt)
    (fun i _ j _ hij => by
      apply Fin.ext
      simpa using congrArg (fun z : Fin n => (z.val : ℕ)) hij)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨⟨x.val, hx⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [Finset.card_univ, Fintype.card_fin] at hbij
  exact hbij.symm

lemma card_val_ge (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter fun x : Fin n => k ≤ x.val).card = n - k := by
  classical
  have hbij := Finset.card_bij
    (s := (Finset.univ : Finset (Fin (n - k))))
    (t := Finset.univ.filter fun x : Fin n => k ≤ x.val)
    (fun (i : Fin (n - k)) _ => (⟨i.val + k, by have := i.isLt; omega⟩ : Fin n))
    (fun i _ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega)
    (fun i _ j _ hij => by
      apply Fin.ext
      have hval := congrArg (fun z : Fin n => (z.val : ℕ)) hij
      simp only at hval
      omega)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨⟨x.val - k, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      omega)
  rw [Finset.card_univ, Fintype.card_fin] at hbij
  exact hbij.symm

lemma filter_card_iff {n : ℕ} {p q : Fin n → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x ↔ q x) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

lemma card_on_agree (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter fun x : Fin n => onBoard n x.val σ ∧ onBoard n x.val (σ + σ)).card =
      n - 2 := by
  rcases hσ with rfl | rfl
  · have hiff : ∀ x : Fin n, onBoard n x.val 1 ∧ onBoard n x.val (1 + 1) ↔ x.val < n - 2 := by
      intro x
      have hx : x.val < n := x.isLt
      unfold onBoard
      omega
    rw [filter_card_iff hiff, card_val_lt n (n - 2) (by omega)]
  · have hiff : ∀ x : Fin n, onBoard n x.val (-1) ∧ onBoard n x.val (-1 + -1) ↔ 2 ≤ x.val := by
      intro x
      have hx : x.val < n := x.isLt
      unfold onBoard
      omega
    rw [filter_card_iff hiff]
    by_cases hn : 2 ≤ n
    · exact card_val_ge n 2 hn
    · have hempty : (Finset.univ.filter fun x : Fin n => 2 ≤ x.val) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have := x.isLt
        omega
      rw [hempty, Finset.card_empty]
      omega

lemma card_on_turn (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter fun x : Fin n => onBoard n x.val σ ∧ onBoard n x.val 0).card = n - 1 := by
  rcases hσ with rfl | rfl
  · have hiff : ∀ x : Fin n, onBoard n x.val 1 ∧ onBoard n x.val 0 ↔ x.val < n - 1 := by
      intro x
      have hx : x.val < n := x.isLt
      unfold onBoard
      omega
    rw [filter_card_iff hiff, card_val_lt n (n - 1) (by omega)]
  · have hiff : ∀ x : Fin n, onBoard n x.val (-1) ∧ onBoard n x.val 0 ↔ 1 ≤ x.val := by
      intro x
      have hx : x.val < n := x.isLt
      unfold onBoard
      omega
    rw [filter_card_iff hiff]
    by_cases hn : 1 ≤ n
    · exact card_val_ge n 1 hn
    · have hempty : (Finset.univ.filter fun x : Fin n => 1 ≤ x.val) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have := x.isLt
        omega
      rw [hempty, Finset.card_empty]
      omega

lemma card_line (n : ℕ) (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (Finset.univ.filter fun x : Fin n => onBoard n x.val σ ∧ onBoard n x.val (σ + τ)).card =
      if σ = τ then n - 2 else n - 1 := by
  by_cases h : σ = τ
  · rw [if_pos h, h]
    simpa using card_on_agree n τ hτ
  · rw [if_neg h]
    have hsum : σ + τ = 0 := by
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> first | rfl | exact (h rfl).elim
    rw [hsum]
    exact card_on_turn n σ hσ

lemma card_fits (n : ℕ) (i j : Fin 4) :
    (Finset.univ.filter fun s : Square n => fits s (D i) ∧ fits s (D i + D j)).card =
      (if (D i).1 = (D j).1 then n - 2 else n - 1) *
        (if (D i).2 = (D j).2 then n - 2 else n - 1) := by
  classical
  let pr : Fin n → Prop := fun x =>
    onBoard n x.val (D i).1 ∧ onBoard n x.val ((D i).1 + (D j).1)
  let pc : Fin n → Prop := fun x =>
    onBoard n x.val (D i).2 ∧ onBoard n x.val ((D i).2 + (D j).2)
  have hrow : (Finset.univ.filter pr).card =
      if (D i).1 = (D j).1 then n - 2 else n - 1 :=
    card_line n (D i).1 (D j).1 (D_pm i).1 (D_pm j).1
  have hcol : (Finset.univ.filter pc).card =
      if (D i).2 = (D j).2 then n - 2 else n - 1 :=
    card_line n (D i).2 (D j).2 (D_pm i).2 (D_pm j).2
  have heq : (Finset.univ.filter fun s : Square n => fits s (D i) ∧ fits s (D i + D j)) =
      (Finset.univ.filter pr) ×ˢ (Finset.univ.filter pc) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, fits, pr, pc, Prod.fst_add, Prod.snd_add]
    tauto
  rw [heq, Finset.card_product, hrow, hcol]

private def cls22 : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun p =>
    p.2 ≠ opp p.1 ∧ (D p.1).1 = (D p.2).1 ∧ (D p.1).2 = (D p.2).2

private def cls21 : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun p =>
    p.2 ≠ opp p.1 ∧ (D p.1).1 = (D p.2).1 ∧ (D p.1).2 ≠ (D p.2).2

private def cls12 : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun p =>
    p.2 ≠ opp p.1 ∧ (D p.1).1 ≠ (D p.2).1 ∧ (D p.1).2 = (D p.2).2

private def cls00 : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun p => p.2 = opp p.1

lemma cls_card : cls22.card = 4 ∧ cls21.card = 4 ∧ cls12.card = 4 ∧ cls00.card = 4 := by
  decide

lemma cls_cover : cls22 ∪ cls21 ∪ cls12 ∪ cls00 = Finset.univ := by
  decide

lemma cls_disj22 : cls22 ∩ cls21 = ∅ := by decide

lemma cls_disj12 : (cls22 ∪ cls21) ∩ cls12 = ∅ := by decide

lemma cls_disj00 : (cls22 ∪ cls21 ∪ cls12) ∩ cls00 = ∅ := by decide

def factor (n : ℕ) (p : Fin 4 × Fin 4) : ℕ :=
  if p.2 = opp p.1 then 0 else
    (if (D p.1).1 = (D p.2).1 then n - 2 else n - 1) *
      (if (D p.1).2 = (D p.2).2 then n - 2 else n - 1)

lemma factor_cls22 (n : ℕ) {p : Fin 4 × Fin 4} (hp : p ∈ cls22) :
    factor n p = (n - 2) * (n - 2) := by
  simp only [cls22, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hne, hr, hc⟩ := hp
  rw [factor, if_neg hne, if_pos hr, if_pos hc]

lemma factor_cls21 (n : ℕ) {p : Fin 4 × Fin 4} (hp : p ∈ cls21) :
    factor n p = (n - 2) * (n - 1) := by
  simp only [cls21, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hne, hr, hc⟩ := hp
  rw [factor, if_neg hne, if_pos hr, if_neg hc]

lemma factor_cls12 (n : ℕ) {p : Fin 4 × Fin 4} (hp : p ∈ cls12) :
    factor n p = (n - 1) * (n - 2) := by
  simp only [cls12, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hne, hr, hc⟩ := hp
  rw [factor, if_neg hne, if_neg hr, if_pos hc]

lemma factor_cls00 (n : ℕ) {p : Fin 4 × Fin 4} (hp : p ∈ cls00) : factor n p = 0 := by
  simp only [cls00, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp [factor, hp]

lemma sum_factor (n : ℕ) : ∑ p : Fin 4 × Fin 4, factor n p =
    4 * (n - 2) * (n - 2) + 4 * (n - 2) * (n - 1) + 4 * (n - 1) * (n - 2) := by
  have hcov := cls_cover
  have d1 : Disjoint cls22 cls21 := (Finset.disjoint_iff_inter_eq_empty).2 cls_disj22
  have d2 : Disjoint (cls22 ∪ cls21) cls12 :=
    (Finset.disjoint_iff_inter_eq_empty).2 cls_disj12
  have d3 : Disjoint (cls22 ∪ cls21 ∪ cls12) cls00 :=
    (Finset.disjoint_iff_inter_eq_empty).2 cls_disj00
  rw [← hcov, Finset.sum_union d3, Finset.sum_union d2, Finset.sum_union d1]
  have s22 : ∑ p ∈ cls22, factor n p = cls22.card * ((n - 2) * (n - 2)) :=
    Finset.sum_const_nat (fun p hp => factor_cls22 n hp)
  have s21 : ∑ p ∈ cls21, factor n p = cls21.card * ((n - 2) * (n - 1)) :=
    Finset.sum_const_nat (fun p hp => factor_cls21 n hp)
  have s12 : ∑ p ∈ cls12, factor n p = cls12.card * ((n - 1) * (n - 2)) :=
    Finset.sum_const_nat (fun p hp => factor_cls12 n hp)
  have s00 : ∑ p ∈ cls00, factor n p = 0 := by
    rw [Finset.sum_congr rfl (fun p hp => factor_cls00 n hp), Finset.sum_const_zero]
  simp only [s22, s21, s12, s00, cls_card.1, cls_card.2.1, cls_card.2.2.1, add_zero]
  ring

lemma fiber_card (n : ℕ) (p : Fin 4 × Fin 4) :
    (Finset.univ.filter fun s : Square n =>
        p.2 ≠ opp p.1 ∧ fits s (D p.1) ∧ fits s (D p.1 + D p.2)).card =
      factor n p := by
  by_cases h : p.2 = opp p.1
  · simp [factor, h]
  · have heq : (Finset.univ.filter fun s : Square n =>
        p.2 ≠ opp p.1 ∧ fits s (D p.1) ∧ fits s (D p.1 + D p.2)) =
        Finset.univ.filter fun s : Square n => fits s (D p.1) ∧ fits s (D p.1 + D p.2) := by
      ext s
      simp [h]
    rw [heq, card_fits, factor, if_neg h]

lemma code_card_sum (n : ℕ) :
    (codeSet n).card = ∑ p : Fin 4 × Fin 4, factor n p := by
  classical
  let t : (Fin 4 × Fin 4) → Finset (Square n) := fun p =>
    Finset.univ.filter fun s => p.2 ≠ opp p.1 ∧ fits s (D p.1) ∧ fits s (D p.1 + D p.2)
  have hsig : (codeSet n).card = ((Finset.univ : Finset (Fin 4 × Fin 4)).sigma t).card := by
    refine Finset.card_bij (s := codeSet n)
      (t := (Finset.univ : Finset (Fin 4 × Fin 4)).sigma t)
      (fun c _ => ⟨c.1, c.2⟩)
      (fun c hc => by
        simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [t] using hc)
      (fun c _ d _ h => congrArg (fun x : Σ _ : Fin 4 × Fin 4, Square n => (x.1, x.2)) h)
      (fun b hb => by
        refine ⟨(b.1, b.2), ?_, ?_⟩
        · simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
          have hb' := Finset.mem_sigma.mp hb
          simpa [t] using hb'.2
        · exact (Sigma.eta b).symm)
  rw [hsig, Finset.card_sigma]
  refine Finset.sum_congr rfl ?_
  intro p _
  simpa [t] using fiber_card n p

lemma a_count (n : ℕ) : a n =
    4 * (n - 2) * (n - 2) + 4 * (n - 2) * (n - 1) + 4 * (n - 1) * (n - 2) := by
  rw [a_tour, card_code, code_card_sum, sum_factor]

lemma quad_cast (n : ℕ) (hn : 2 ≤ n) :
    ((4 * (n - 2) * (n - 2) + 4 * (n - 2) * (n - 1) + 4 * (n - 1) * (n - 2) : ℕ) : ℤ) =
      12 * (n : ℤ) ^ 2 - 40 * (n : ℤ) + 32 := by
  have h1 : 1 ≤ n := by omega
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn, Nat.cast_sub h1]
  ring

lemma closed_form : ∀ n : ℕ, 1 < n → (a n : ℤ) = 12 * (n : ℤ) ^ 2 - 40 * (n : ℤ) + 32 := by
  intro n hn
  have hcount := a_count n
  have hcast := congrArg (fun k : ℕ => (k : ℤ)) hcount
  rw [quad_cast n (by omega)] at hcast
  exact hcast

lemma recurrence : ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  have h0 := closed_form n (by omega)
  have h1 := closed_form (n - 1) (by omega)
  have h2 := closed_form (n - 2) (by omega)
  have h3 := closed_form (n - 3) (by omega)
  rw [h0, h1, h2, h3, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

lemma a_small (n : ℕ) (hn : n < 2) : a n = 0 := by
  rw [a_count]
  interval_cases n <;> norm_num

open PowerSeries

lemma a_at : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 20 ∧ a 4 = 64 := by
  refine ⟨a_small 0 (by decide), a_small 1 (by decide), ?_, ?_, ?_⟩
  · have h := closed_form 2 (by decide)
    norm_num at h
    exact_mod_cast h
  · have h := closed_form 3 (by decide)
    norm_num at h
    exact_mod_cast h
  · have h := closed_form 4 (by decide)
    norm_num at h
    exact_mod_cast h

lemma generating :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 4 * X ^ 3 * (5 + X) := by
  let f : ℤ⟦X⟧ := mk fun n => (a n : ℤ)
  have poly : f * (1 - X) ^ 3 =
      f - (3 : ℕ) • (f * X ^ 1) + (3 : ℕ) • (f * X ^ 2) - f * X ^ 3 := by
    simp only [pow_one, nsmul_eq_mul]
    ring
  have rhs : (4 * X ^ 3 * (5 + X) : ℤ⟦X⟧) = (20 : ℕ) • X ^ 3 + (4 : ℕ) • X ^ 4 := by
    simp only [nsmul_eq_mul]
    ring
  rw [poly, rhs]
  ext k
  simp only [map_add, map_sub, map_nsmul]
  simp only [coeff_mul_X_pow', coeff_X_pow, coeff_mk, f]
  simp only [nsmul_eq_mul]
  by_cases hk : 5 ≤ k
  · have h1 : 1 ≤ k := by omega
    have h2 : 2 ≤ k := by omega
    have h3 : 3 ≤ k := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_neg (by omega : k ≠ 3),
      if_neg (by omega : k ≠ 4)]
    have c0 := closed_form k (by omega)
    have c1 := closed_form (k - 1) (by omega)
    have c2 := closed_form (k - 2) (by omega)
    have c3 := closed_form (k - 3) (by omega)
    rw [c0, c1, c2, c3, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    ring
  · have hk' : k ≤ 4 := by omega
    interval_cases k <;>
      simp only [a_at.1, a_at.2.1, a_at.2.2.1, a_at.2.2.2.1, a_at.2.2.2.2] <;>
      norm_num

end BishopA187156

theorem OMA.solution : type_of% @OMA.S_oeis_a187156.main :=
  ⟨BishopA187156.closed_form, BishopA187156.recurrence, BishopA187156.generating⟩
