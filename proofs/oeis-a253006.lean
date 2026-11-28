import OMAStatements.S_oeis_a253006

namespace OMA.S_oeis_a253006

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 3 → ℕ) :
    good n x ↔ ((∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i')) ∧
      ∀ i j, i.val + 1 = n → j.val + 1 = 3 → x i j + 3 = max i.val j.val := by
  constructor
  · rintro ⟨h1, h6, h3, h4, h5⟩
    exact ⟨⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩, h6⟩
  · rintro ⟨⟨hA, hB⟩, h6⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, h6, fun i j j' hj => (hA i).2 j j' hj,
      fun i i' j hi => (hB i i' hi).1 j, fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 3), i.val + j.val = s → x i j ≤ max i.val j.val := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro i j hs
    have hi0 := i.isLt
    have hj0 := j.isLt
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · rw [h1 i j hi hj]
      exact Nat.zero_le _
    · have e := h3 i ⟨j.val - 1, by omega⟩ j (by simp only; omega)
      have p := ih (i.val + (j.val - 1)) (by omega) i ⟨j.val - 1, by omega⟩ rfl
      simp only [step01] at e
      simp only at p
      omega
    · have e := h4 ⟨i.val - 1, by omega⟩ i j (by simp only; omega)
      have p := ih ((i.val - 1) + j.val) (by omega) ⟨i.val - 1, by omega⟩ j rfl
      simp only [step01] at e
      simp only at p
      omega
    · have e := h5 ⟨i.val - 1, by omega⟩ i ⟨j.val - 1, by omega⟩ j (by simp only; omega)
        (by simp only; omega)
      have p := ih ((i.val - 1) + (j.val - 1)) (by omega) ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ rfl
      simp only [step01] at e
      simp only at p
      omega

/-- The conditions on a row r of deficits (its values are max i j - r j) at a row index i, with
c = min i 5: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 3 → Fin 6) : Bool :=
  (List.finRange 3).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 3).all (fun j => decide (∀ h : j.val + 1 < 3,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 5, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 3 → Fin 6) : Bool :=
  (List.finRange 3).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 3).all (fun j => decide (∀ h : j.val + 1 < 3,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 3 → Fin 6) : ZA c r = true ↔
    (∀ j : Fin 3, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 3, ∀ h : j.val + 1 < 3,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 3 → Fin 6) : ZB c p r = true ↔
    (∀ j : Fin 3, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 3, ∀ h : j.val + 1 < 3,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 3 → Fin 6) : Fin 3 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 3 → Fin 6) :
    (RA i (vals i r) ∧ ∀ j : Fin 3, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 5) r = true := by
  rw [ZA_iff]
  simp only [RA, vals, step01]
  constructor
  · rintro ⟨⟨-, h3⟩, hb⟩
    refine ⟨fun j => ?_, fun j h => ?_⟩
    · have := hb j
      have := (r j).isLt
      omega
    · have e : max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
          max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1 := h3 j ⟨j.val + 1, h⟩ rfl
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max i (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs <;> omega
  · rintro ⟨hb, hs⟩
    refine ⟨⟨fun j hi hj => ?_, fun j j' hj => ?_⟩, fun j => ?_⟩
    · have := hb j
      omega
    · have h : j.val + 1 < 3 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
        max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1
      have e := hs j h
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (min i 5) (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 3 → Fin 6) (hp : ∀ j : Fin 3, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 3, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 5) p r = true := by
  rw [ZB_iff]
  simp only [RB, vals, step01]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j h => ?_⟩
    · have e := h1 j
      have := hp j
      have := hr j
      have := (p j).isLt
      have := (r j).isLt
      have := j.isLt
      split_ifs <;> omega
    · have e : max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j ∨
          max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j + 1 :=
        h2 j ⟨j.val + 1, h⟩ rfl
      have := hp j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (i + 1) (j.val + 1) := hr ⟨j.val + 1, h⟩
      have := (p j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j j' hj => ?_⟩
    · have e := h1 j
      have := hp j
      have := hr j
      have := (p j).isLt
      have := (r j).isLt
      have := j.isLt
      split_ifs at e <;> omega
    · have h : j.val + 1 < 3 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j ∨
        max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j + 1
      have e := h2 j h
      have := hp j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (i + 1) (j.val + 1) := hr ⟨j.val + 1, h⟩
      have := (p j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      omega

theorem bound_of_ZA {i : ℕ} {r : Fin 3 → Fin 6} (h : ZA (min i 5) r = true) (j : Fin 3) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 3 → Fin 6) : Prop :=
  (∀ i : Fin n, ZA (min i.val 5) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 5) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

/-- In the last row every value is at least the lower right value minus the distance to it. -/
theorem last_row {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) (i : Fin n) :
    ∀ d, ∀ j : Fin 3, j.val + d = 2 → x i (Fin.last 2) ≤ x i j + d := by
  have h3 := h.2.2.1
  intro d
  induction d with
  | zero =>
    intro j hj
    have e : j = Fin.last 2 := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [e]
    omega
  | succ d ih =>
    intro j hj
    have hj1 : j.val + 1 < 3 := by omega
    have e := h3 i j ⟨j.val + 1, hj1⟩ rfl
    have := ih ⟨j.val + 1, hj1⟩ (by simp only; omega)
    simp only [step01] at e
    omega

/-- On and below the diagonal the deficit is at most 3 plus the distance to the last column. -/
theorem below_bound {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) :
    ∀ d, ∀ (i : Fin n) (j : Fin 3), i.val + d + 1 = n → j.val ≤ i.val →
      max i.val j.val ≤ x i j + (3 + (2 - j.val)) := by
  have h6 := h.2.1
  have h4 := h.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro i j hi hj
    have hq := h6 i (Fin.last 2) (by omega) (by simp only [Fin.val_last])
    have hr := last_row h i (2 - j.val) j (by have := j.isLt; omega)
    simp only [Fin.val_last] at hq
    omega
  | succ d ih =>
    intro i j hi hj
    have hi1 : i.val + 1 < n := by omega
    have e := h4 i ⟨i.val + 1, hi1⟩ j rfl
    have := ih ⟨i.val + 1, hi1⟩ j (by simp only; omega) (by simp only; omega)
    simp only [step01] at e
    simp only at this
    omega

/-- The lower right condition bounds every deficit by 3 + 2. -/
theorem deficit_bound {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) (i : Fin n) (j : Fin 3) :
    max i.val j.val ≤ x i j + (3 + 2) := by
  by_cases hj : j.val ≤ i.val
  · have := below_bound h (n - 1 - i.val) i j (by have := i.isLt; omega) hj
    omega
  · have := j.isLt
    omega

/-- The lower right deficit is 3. -/
def LZ (n : ℕ) (z : Fin n → Fin 3 → Fin 6) : Prop :=
  ∀ i j, i.val + 1 = n → j.val + 1 = 3 → (z i j : ℕ) = 3

instance (n : ℕ) : DecidablePred (LZ n) := fun z => by unfold LZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 3 → ℕ | good n x} =
    (fun z : Fin n → Fin 3 → Fin 6 => fun i => vals i.val (z i)) '' {z | GZ n z ∧ LZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hq := hx.2.1
    let z : Fin n → Fin 3 → Fin 6 := fun i j =>
      ⟨max i.val j.val - x i j, by have := hd i j; have := deficit_bound hx i j; omega⟩
    have hv : ∀ i, vals i.val (z i) = x i := fun i => by
      funext j
      simp only [vals, z]
      have := hd i j
      omega
    have hb : ∀ i j, ((z i j : Fin 6) : ℕ) ≤ max i.val j.val := fun i j => by
      simp only [z]
      omega
    rw [good_iff] at hx
    refine ⟨z, ⟨⟨fun i => ?_, fun i i' hi => ?_⟩, fun i j hi hj => ?_⟩, funext hv⟩
    · rw [← rowA]
      exact ⟨by rw [hv]; exact hx.1.1 i, hb i⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      rw [← rowB i.val (z i) (z i') (hb i) (fun j => by rw [← hi]; exact hb i' j), ← e, hv, hv]
      exact hx.1.2 i i' hi
    · have := hq i j hi hj
      have := hd i j
      simp only [z]
      omega
  · rintro ⟨z, ⟨hz, hl⟩, rfl⟩
    rw [good_iff]
    refine ⟨⟨fun i => ((rowA _ _).2 (hz.1 i)).1, fun i i' hi => ?_⟩, fun i j hi hj => ?_⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      show RB (vals i.val (z i)) (vals i'.val (z i'))
      rw [e, rowB i.val (z i) (z i') (bound_of_ZA (hz.1 i))
        (fun j => by rw [← hi]; exact bound_of_ZA (hz.1 i') j)]
      exact hz.2 i i' hi
    · have := hl i j hi hj
      have := bound_of_ZA (hz.1 i) j
      simp only [vals]
      omega

theorem injOn (n : ℕ) :
    Set.InjOn (fun z : Fin n → Fin 3 → Fin 6 => fun i => vals i.val (z i)) {z | GZ n z ∧ LZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1.1 i) j
  have b' := bound_of_ZA (hz'.1.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 3 → Fin 6 => GZ n z ∧ LZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 3 → Fin 6) (t : Fin 3 → Fin 6) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 5) t = true ∧ ZB (min m 5) (y (Fin.last m)) t = true := by
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨⟨fun i => ?_, fun i i' h => ?_⟩, ?_, ?_⟩
    · have := hA (Fin.castSucc i)
      simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this
    · have := hB (Fin.castSucc i) (Fin.castSucc i') (by simpa only [Fin.coe_castSucc] using h)
      simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this
    · have := hA (Fin.last (m + 1))
      simpa only [Fin.snoc_last, Fin.val_last] using this
    · have := hB (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (by simp)
      simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.coe_castSucc, Fin.val_last] using this
  · rintro ⟨⟨hA, hB⟩, ht, hl⟩
    refine ⟨fun i => ?_, fun i i' h => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last, Fin.val_last] using ht
      | cast i => simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using hA i
    · induction i' using Fin.lastCases with
      | last =>
        have hi : i = Fin.castSucc (Fin.last m) := by
          apply Fin.ext
          simp only [Fin.val_last] at h
          simp only [Fin.coe_castSucc, Fin.val_last]
          omega
        subst hi
        simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.coe_castSucc, Fin.val_last] using hl
      | cast i'' =>
        induction i using Fin.lastCases with
        | last =>
          simp only [Fin.val_last, Fin.coe_castSucc] at h
          have := i''.isLt
          omega
        | cast i =>
          have := hB i i'' (by simpa only [Fin.coe_castSucc] using h)
          simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this

theorem GZ_one (z : Fin (0 + 1) → Fin 3 → Fin 6) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
  constructor
  · rintro ⟨hA, -⟩
    simpa using hA 0
  · intro h
    refine ⟨fun i => ?_, fun i i' hi => ?_⟩
    · have hi : i = 0 := by
        ext
        simp only [Fin.val_zero]
        have := i.isLt
        omega
      subst hi
      simpa using h
    · have := i.isLt
      have := i'.isLt
      omega

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 3 → Fin 6) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 3 → Fin 6, f z =
      ∑ t : Fin 3 → Fin 6, ∑ y : Fin (m + 1) → Fin 3 → Fin 6, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 3 → Fin 6).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 3 → Fin 6) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 3 → Fin 6, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem LZ_iff (n : ℕ) (z : Fin (n + 1) → Fin 3 → Fin 6) :
    LZ (n + 1) z ↔ (z (Fin.last n) 2 : ℕ) = 3 := by
  constructor
  · intro h
    exact h _ _ (by simp) rfl
  · intro h i j hi hj
    have e1 : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    have e2 : j = 2 := Fin.ext (by have : ((2 : Fin 3) : ℕ) = 2 := rfl; omega)
    rw [e1, e2]
    exact h

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 6,
    if (r 2 : ℕ) = 3 then Cnt n r else 0 := by
  rw [a_eq, Finset.card_filter]
  simp only [LZ_iff]
  have h : ∀ r : Fin 3 → Fin 6, (if (r 2 : ℕ) = 3 then Cnt n r else 0) =
      ∑ z : Fin (n + 1) → Fin 3 → Fin 6,
        if (r 2 : ℕ) = 3 ∧ GZ (n + 1) z ∧ z (Fin.last n) = r then 1 else 0 := by
    intro r
    unfold Cnt
    by_cases hr : (r 2 : ℕ) = 3
    · rw [if_pos hr]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [hr, true_and]
    · rw [if_neg hr]
      symm
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp only [hr, false_and, if_false]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · by_cases h1 : GZ (n + 1) z <;> by_cases h2 : (z (Fin.last n) 2 : ℕ) = 3 <;> simp [h1, h2]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 3 → Fin 6) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3 → Fin 6)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 3 → Fin 6) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 6,
      if (ZA (min (m + 1) 5) r && ZB (min m 5) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 3 → Fin 6,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 5) r = true ∧ ZB (min m 5) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 3 → Fin 6,
      (if (ZA (min (m + 1) 5) r && ZB (min m 5) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 3 → Fin 6,
          if (ZA (min (m + 1) 5) r && ZB (min m 5) p r) = true ∧ GZ (m + 1) y ∧
            y (Fin.last m) = p then 1 else 0 := by
    intro p
    unfold Cnt
    split_ifs with h
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp [h]
    · symm
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [h]
  rw [lhs, Finset.sum_congr rfl (fun p _ => rhs p), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (y (Fin.last m))]
  · simp only [and_true, Bool.and_eq_true]
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 5) r = true <;>
      by_cases h3 : ZB (min m 5) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 5 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 5 ≤ m) (r : Fin 3 → Fin 6) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 6,
      if (ZA 5 r && ZB 5 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 5 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 3 → Fin 6} (h : ZB c p r = true) (j : Fin 3) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 3 → Fin 6) (e : Fin 3 → Fin 2) : Fin 3 → Fin 6 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 5, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 3 → Fin 6) (e : Fin 3 → Fin 2) : Bool :=
  (List.finRange 3).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 5))

theorem valid_iff (c : ℕ) (r : Fin 3 → Fin 6) (e : Fin 3 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 3, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 5 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 3 → Fin 6) (f : (Fin 3 → Fin 6) → ℕ) :
    ∑ e : Fin 3 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 3 → Fin 6, (if ZB c p r = true then f p else 0) := by
  apply Finset.sum_bij_ne_zero (fun e _ _ => pred c r e)
  · intro e _ _
    exact Finset.mem_univ _
  · intro e₁ _ h₁ e₂ _ h₂ he
    have v₁ : valid c r e₁ = true := by
      by_contra hv
      exact h₁ (by simp [hv])
    have v₂ : valid c r e₂ = true := by
      by_contra hv
      exact h₂ (by simp [hv])
    rw [valid_iff] at v₁ v₂
    funext j
    have hj := congrArg Fin.val (congrFun he j)
    simp only [pred] at hj
    have a1 := v₁ j
    have a2 := v₂ j
    have := (e₁ j).isLt
    have := (e₂ j).isLt
    apply Fin.ext
    split_ifs at a1 a2 hj <;> omega
  · intro p _ hp
    have hz : ZB c p r = true := by
      by_contra h
      exact hp (by simp [h])
    let e : Fin 3 → Fin 2 := fun j =>
      ⟨(p j : ℕ) + (if j.val ≤ c then 1 else 0) - r j, by
        have := ZB_down hz j
        split_ifs at this ⊢ <;> omega⟩
    have hv : valid c r e = true := by
      rw [valid_iff]
      intro j
      have hd := ZB_down hz j
      have := (p j).isLt
      simp only [e]
      split_ifs at hd ⊢ <;> omega
    have hpe : pred c r e = p := by
      funext j
      apply Fin.ext
      have hd := ZB_down hz j
      have := (p j).isLt
      simp only [pred, e]
      split_ifs at hd ⊢ <;> omega
    refine ⟨e, Finset.mem_univ _, ?_, hpe⟩
    rw [hpe]
    simpa [hv, hz] using hp
  · intro e _ h
    have v : valid c r e = true := by
      by_contra hv
      exact h (by simp [hv])
    simp [v]

/-- The contribution of the candidate `pred c r e` to the count of r. -/
def spTerm (c : ℕ) (f : (Fin 3 → Fin 6) → ℕ) (r : Fin 3 → Fin 6) (e : Fin 3 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 3 → Fin 6) :
    Cnt (m + 1) r = if ZA (min (m + 1) 5) r = true then
      ∑ e : Fin 3 → Fin 2, spTerm (min m 5) (Cnt m) r e else 0 := by
  rw [Cnt_succ]
  split_ifs with h
  · simp only [spTerm]
    rw [sum_pred]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [h]
  · refine Finset.sum_eq_zero (fun p _ => ?_)
    simp [h]

/-- The row with base-b digits of n, column j holding the digit of b ^ j (the kernel evaluates it by
arithmetic on numerals). -/
def dig (b : ℕ) (hb : 0 < b) (n : ℕ) : Fin 3 → Fin b := fun j => ⟨n / b ^ j.val % b, Nat.mod_lt _ hb⟩

theorem sum_dig (b : ℕ) (hb : 0 < b) (g : (Fin 3 → Fin b) → ℕ) :
    ∑ f, g f = ∑ n ∈ Finset.range (b ^ 3), g (dig b hb n) := by
  rw [← (finFunctionFinEquiv (m := b) (n := 3)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun n => g (dig b hb n)) _

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 3 → Fin 6) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 6 + (r 2 : ℕ) * 36

theorem code_lt (r : Fin 3 → Fin 6) : code r < 6 ^ 3 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem dig_code (r : Fin 3 → Fin 6) : dig 6 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 3 → Fin 6) → ℕ) (r : Fin 3 → Fin 6) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 3), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 3 → Fin 6) :
    Cnt (m + 1) r = if ZA (min (m + 1) 5) r = true then spSum (min m 5) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- The table of Cnt 0: the 18-bit digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 3 → Fin 6) : ℕ :=
  442704475244129922343871074989998146077315129547001502767058453258313840592979502359567329998533780883670360514655988701886168725967657715282826082903242830942737181459687202303746863384928819146616126389098127972718075364015260965501490891839705340666543481631522119960171647516021737801789914330222607137654993576527459272442660581161364422942484698125081428620537540986161754994344008430209920992535313280804928364740609 >>> (18 * code r) % 262144

/-- The table of Cnt 1: the 18-bit digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 3 → Fin 6) : ℕ :=
  116052321958397194362911739082178074005291697319969161941367771170947423428406018666546418155135639455968882986753979502267247814500065664115101160676587688674652895696568241960713417755178780366469898994050985031129741835486017346440781320008034764345806299880609384603258184318428268802974436784805522787306785355632837555706508640544112035133133553657058355599976053822323695872385753258339974121588792803189909893910712811522 >>> (18 * code r) % 262144

/-- The table of Cnt 2: the 18-bit digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 3 → Fin 6) : ℕ :=
  9872639700668549482824157618291974606487933943585541944769228960011294275960025909940572258743689419421486146686517267611084459945144149299075534798400612972360553838107136920661123391150823422701717482185252442780831038309970191347741034344603174779945324115052432950394261742962259804690811108082188584212402844151518213993868698826647396050871602368983449830237646938848843424040880563327460450244899600981066884750180021573042776345797886900335351284187777990661 >>> (18 * code r) % 262144

/-- The table of Cnt 3: the 18-bit digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 3 → Fin 6) : ℕ :=
  980956912259467426494676932634430002751321885514812848694167717469166306454179719536423587058530127544765992938713092478533810426911560635231736012742474598846184776899596697389589864816912228087114900820274118223744215971898852579347283042433351787153821427686888833076173565027421203161995170473610151169879785361556543339081738448429741556701539414488062391510944364260074330093557214533339427075472824424555098767533131053878857802337907270387288870222448256411060207499533861069414329276212192869881737721978475099370119176222389388486158936553350384079391474435432205409001169546944894343826866016023544198323796164160281588380135410261985917620369432113630442178127723853389848751897333465093 >>> (18 * code r) % 262144

/-- The table of Cnt 4: the 18-bit digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 3 → Fin 6) : ℕ :=
  97469014659216786331535451653798038005079450920478387770840872057931311030944413633004046083717746672031465235105383216949597016961990791210316512105587034991114359915469128840254374664811132785107234613753038474187294694684422307621560281908585339426345403110948896503100696582643106773901631503166396897015509621289713915620607564514837345550008536990442205534538300783557422859189134508194975487199762017242760713387906047568479746174224595231522047562264026007495606893330229408298992332398808053672158020334559129491566249650392631219195148347837042675896234313707285814813807781366114424656527895305341711198789729811287238809686560507243415320673723517688462277856828010155821716491386341636442481004562120140395136326448054836234139157436221527915912474840736871899800603800135897898968528030988798900809596136308819812594307820323512297971013071590809264503780978955819660327800891029355228316709872119840121838731712004101 >>> (18 * code r) % 262144

/-- The table of Cnt 5: the 18-bit digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 3 → Fin 6) : ℕ :=
  9684634156618053052032028833834600751710926524903465042451650771870031613829983332768565255998134116310272451995853280470041668144995088835256910348349765596056962692125597862926638732286049976535761042549631357360315127302204913603451052657047889009838657705213189583341792807368971617756584337338502126585464097934607031230151561377923009519312253101056138582857033568034499398281984705438278918012862477072179585082255446701216967882621924848001765303421317183566586381833164786403705018842514844885003225538390103925011096547615391648121328481748733585650840618052139882398283611083862864491032383841694523916826085125470176871631290557948372078052806983465916838807199292722124886763736364205098549676257240417818348619710348912459569837602393363958692806033430127091428826331976141929418576774571730762489569755420592312325846280648908232158595769414178356117185616077714180927018626158230017484599908030364233494069580436263945308188166512707746307417138724598816348069283228281288395660865043636516135014811394739969133934027317683635631201969851423535720003407162270828697998055599825210458670261959423396446655038813808769289941422173680819953097657024517 >>> (18 * code r) % 262144

/-- The table of Cnt 6: the 18-bit digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 3 → Fin 6) : ℕ :=
  803824634999298403318658393208271862392006901566987598523487014065212623947888616619790916247845131653752613515655822279013458456034592373326323558913030544472727903446424622622911014779742148050428396830523471575051541008997513066823218994271298237463728281767185579335184933563927024369058643180169365920117661202621409789770924253466588630641361346953548055486930002439055591011168325495244797767770011584405663412302329662620994471629317987025428749110983098935994062786104207962028813628300343864359972835367768192262635182216206829122314187178853769215083262916770377863332518077148776608281844192533526621930873205851189662860171256953866466978468223282822935412568994443723171637815780673732058846055253166872876259091387432065094628660189578240179312332909300029222046451522263349954443932196486647358494778518426612776726466856402026337908738376016308748333789292935827027762091582861611811851724778164243637292808657377299910630809646174439624268012990886301964553933638524639881904819914396412600104260810209848344143592456697332794254010634422287906171659503374253193517758411734376131424262830482156000078464128204078598921475548713908077233020532424709 >>> (18 * code r) % 262144

/-- The table of Cnt 7: the 18-bit digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 3 → Fin 6) : ℕ :=
  13151733184687316044659495156347387820823438220818905527649341748199502931581117365899711617645466129949349989810368754878316585340903330638278884253058981679445355335906561897854375398444455868085680347319825719016847125090108537388152868167287722339223737049939092736156249951857709293911889923487001744056316722386011452695049051758259369083237906148054324370069677102239770402358973623526076993440797505553488215205523470127124760263177724183845223629939152898191952445202848576103820298577606708069770981157935553217041168803589741309520524808924576628307587107008356894611620157310829881542429117310277819993288371664165449127199634287962568050614658400429568719915695380159753026883076153235726550254441816745282051352641413253113537977543997087578669910282663745906365767383426512353573117714494375319780699162259979276506909896254453111327982631180520924730208055391385663866020523230720503434735273906804920760397950121835953413348882068519519374676527629180215713303102988128798181923246742777950050532467406266263516171890775560974162726645525172342569672875163944550526763651220621764296929584629858373063937167698576564576398060678801518671595787374559237 >>> (18 * code r) % 262144

/-- The table of Cnt 8: the 18-bit digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 3 → Fin 6) : ℕ :=
  87258553751128657998808579792849752772915447989380220032489373454548984840608149828244772956543188387955554792482638057035075429986405750405664762238631388020473233856051636744969014977897310288215554320435097947986457452774632065400725574265624364806781571024893423975719753460740116410645989872093523837357105350616893406135004068075382789064680954857184975699491084743518621583082156366749447828783426807452669533026928460919408681633812605478716534756687237919954532487369334468257839292970444758118693131104367478143904236130066295919516130125432753307737321129842337538824515858156906657268444326059920630366194830255509003787572146944489946275233223722898907352520707317870739449222001295911537043746650858115551740649853175066554246322600104730907432822175635096642270488676770309087807596359394567488996638827904623365234141486640214413497392698987044508781311904621375934077419297275288627420680402240494157047666827809341446077019471986335882765504138936458195148273482962791691592825853787070513394274598893397455209922898509767705516466946164761053046036431392422940342591553297963138681476448553583923379969290711849210502865191820154061732564818220810245 >>> (18 * code r) % 262144

/-- The table of Cnt 9: the 18-bit digit at position `code r` is Cnt 9 r. -/
def t9 (r : Fin 3 → Fin 6) : ℕ :=
  358050609404326039386676138015699024391504664552206006084479980686806938794908313795786626079507016414107082822738691632257910512988613429328283232488839183851821967690575478590260760571347553680893828622600110162024477691120694938150809428593452013905483207103658794733584883053946807908234987280669194623592835424671469678897188449147421420252356364447406236583812648336964191335372773765520574877420773590509182218749184216556572788913856610609874677644901002547140145645194228818358277032218154375960749443532331858533311633998741718145431019108541800409255536977750811414643400590115848569394039331311924922761035160984373147916557197812971855624721189125651532657608082221796971929712773798705024340925543425456391222583684378895245098422317996945948341389294483354069544372755735364649838582397424485868467577615332192765166597318141723740517361294636899113742580689850092056615893604599529829563165056243189036671678191980416067295789089662302865539323980879284405801309872206163805564581394435022345993343660710110413218283585826918324290467381690935519110392742354123228097681126530761375248318687089539791354169969716978729579756730483069154841529507890069509 >>> (18 * code r) % 262144

/-- The table of Cnt 10: the 18-bit digit at position `code r` is Cnt 10 r. -/
def t10 (r : Fin 3 → Fin 6) : ℕ :=
  1094334605795370140720463162136808381141079564534516839401909182268997962267946626652849568232021160740711856258175433133273298375380010053117525098632478463057648613322116181717121396832126789193538118441498007287823193080846416056693183073146375030085944125102323085986306995250068761073431151872546894105160273835572577997746001008287575412251844626731759625392128898960420160947242648006674940844036319931875717922848319174561322333920669902621736493611249219540520613606205747363767683213706385824855352170316703329252050722673552758061970227689010018258744124078925392853671087800936021777482336143554773761792325442485364516743678645893680003192670998850161747333301074786385315501150282945408491851673492590026277117589365130394086068213873457943085618110114936472644625943142652839704315910918219013902413999623895714777116517117375009581867187140138360201234446177724337316357828257568655274004729626131430937723324780296929041821947259669620135722571959203142071553717368021573114323993794162538017439892351483113500722655928731195219036201208236133547612388642895233975906327906407232384336630690528652132962357138193609826605235475633569990919542544633430021 >>> (18 * code r) % 262144

lemma Cnt0 (r : Fin 3 → Fin 6) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA 0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then 1 else 0) = t0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt1 (r : Fin 3 → Fin 6) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 1 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 0 5) t0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t1 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt2 (r : Fin 3 → Fin 6) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 2 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 1 5) t1 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t2 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt3 (r : Fin 3 → Fin 6) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 3 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 2 5) t2 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t3 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt4 (r : Fin 3 → Fin 6) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 4 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 3 5) t3 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t4 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt5 (r : Fin 3 → Fin 6) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 5 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 4 5) t4 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t5 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt6 (r : Fin 3 → Fin 6) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 6 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 5 5) t5 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt7 (r : Fin 3 → Fin 6) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 7 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 6 5) t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt8 (r : Fin 3 → Fin 6) : Cnt 8 r = t8 r := by
  have hf : Cnt 7 = t7 := funext Cnt7
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 8 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 7 5) t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt9 (r : Fin 3 → Fin 6) : Cnt 9 r = t9 r := by
  have hf : Cnt 8 = t8 := funext Cnt8
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 9 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 8 5) t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t9 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt10 (r : Fin 3 → Fin 6) : Cnt 10 r = t10 r := by
  have hf : Cnt 9 = t9 := funext Cnt9
  have h : ∀ c0 c1 c2 : Fin 6,
      (if ZA (min 10 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) = true then spSum (min 9 5) t9 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) else 0) =
        t10 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

/-- The difference equation of order 4 on the deficit rows ending with at most 3 (the
others never reach the lower right condition), from m = 6 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 3 → Fin 6, (r 2 : ℕ) ≤ 3 → (Cnt (m + 10) r : ℤ) = 4 * Cnt (m + 9) r - 6 * Cnt (m + 8) r + 4 * Cnt (m + 7) r - Cnt (m + 6) r := by
  induction m with
  | zero =>
    intro r hr
    simp only [Nat.zero_add, Cnt6, Cnt7, Cnt8, Cnt9, Cnt10]
    have h : ∀ c0 c1 c2 : Fin 6,
        ((dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) 2 : ℕ) ≤ 3 → (t10 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) : ℤ) = 4 * t9 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) - 6 * t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) + 4 * t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) - t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36)) := by
      decide +kernel
    rw [← dig_code r] at hr ⊢
    exact h (r 0) (r 1) (r 2) hr
  | succ m ih =>
    intro r hr
    rw [show m + 1 + 10 = m + 10 + 1 by omega, show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega, show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega,
      Cnt_hom (m + 10) (by omega), Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega), Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs with hT
    · apply ih p
      rw [Bool.and_eq_true] at hT
      have hd := ZB_down hT.2 2
      have : ((2 : Fin 3) : ℕ) = 2 := rfl
      split_ifs at hd <;> omega
    · simp

/-- The recurrence of a, for n >= 11. -/
theorem a_rec (m : ℕ) : (a (m + 10 + 1) : ℤ) = 4 * a (m + 9 + 1) - 6 * a (m + 8 + 1) + 4 * a (m + 7 + 1) - a (m + 6 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs with hq
  · exact Cnt_rec m r (le_of_eq hq)
  · simp

lemma v1 : a 1 = 0 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 0 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 0 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 1 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 54 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 632 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 2902 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

lemma v8 : a 8 = 8416 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt7]
  decide +kernel

lemma v9 : a 9 = 18770 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt8]
  decide +kernel

lemma v10 : a 10 = 35564 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt9]
  decide +kernel

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) : (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 + 4 + 1 := ⟨n - 11, by omega⟩
  rw [show m + 6 + 4 + 1 - 1 = m + 9 + 1 by omega, show m + 6 + 4 + 1 - 2 = m + 8 + 1 by omega, show m + 6 + 4 + 1 - 3 = m + 7 + 1 by omega, show m + 6 + 4 + 1 - 4 = m + 6 + 1 by omega]
  rw [show m + 6 + 4 + 1 = m + 10 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^4 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
    X ^ 4 * (1 + 50 * X + 422 * X ^ 2 + 694 * X ^ 3 + 385 * X ^ 4 + 44 * X ^ 5 + 4 * X ^ 6) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 4 = A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (X ^ 4 * (1 + 50 * X + 422 * X ^ 2 + 694 * X ^ 3 + 385 * X ^ 4 + 44 * X ^ 5 + 4 * X ^ 6) : ℤ⟦X⟧) =
      X ^ 4 + X ^ 5 * C 50 + X ^ 6 * C 422 + X ^ 7 * C 694 + X ^ 8 * C 385 + X ^ 9 * C 44 + X ^ 10 * C 4 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega] at h ⊢
    simp only [ show ¬ q + 11 = 0 by omega, show 1 ≤ q + 11 by omega, show ¬ q + 10 = 0 by omega,
      show 2 ≤ q + 11 by omega, show ¬ q + 9 = 0 by omega, show 3 ≤ q + 11 by omega,
      show ¬ q + 8 = 0 by omega, show 4 ≤ q + 11 by omega, show ¬ q + 7 = 0 by omega,
      show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega,
      show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega,
      show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega,
      show ¬ q + 11 = 10 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..33). -/
theorem controls : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 1 ∧ a 5 = 54 ∧ a 6 = 632 ∧ a 7 = 2902 ∧
    a 8 = 8416 ∧ a 9 = 18770 ∧ a 10 = 35564 ∧ a 11 = 60398 ∧ a 12 = 94872 ∧ a 13 = 140586 ∧
    a 14 = 199140 ∧ a 15 = 272134 ∧ a 16 = 361168 ∧ a 17 = 467842 ∧ a 18 = 593756 ∧ a 19 = 740510 ∧
    a 20 = 909704 ∧ a 21 = 1102938 ∧ a 22 = 1321812 ∧ a 23 = 1567926 ∧ a 24 = 1842880 ∧
    a 25 = 2148274 ∧ a 26 = 2485708 ∧ a 27 = 2856782 ∧ a 28 = 3263096 ∧ a 29 = 3706250 ∧
    a 30 = 4187844 ∧ a 31 = 4709478 ∧ a 32 = 5272752 ∧ a 33 = 5879266 := by
  have v11 : a 11 = 60398 := by
    have h : (a 11 : ℤ) = 4 * a 10 - 6 * a 9 + 4 * a 8 - a 7 := a_rec 0
    rw [v10, v9, v8, v7] at h
    omega
  have v12 : a 12 = 94872 := by
    have h : (a 12 : ℤ) = 4 * a 11 - 6 * a 10 + 4 * a 9 - a 8 := a_rec 1
    rw [v11, v10, v9, v8] at h
    omega
  have v13 : a 13 = 140586 := by
    have h : (a 13 : ℤ) = 4 * a 12 - 6 * a 11 + 4 * a 10 - a 9 := a_rec 2
    rw [v12, v11, v10, v9] at h
    omega
  have v14 : a 14 = 199140 := by
    have h : (a 14 : ℤ) = 4 * a 13 - 6 * a 12 + 4 * a 11 - a 10 := a_rec 3
    rw [v13, v12, v11, v10] at h
    omega
  have v15 : a 15 = 272134 := by
    have h : (a 15 : ℤ) = 4 * a 14 - 6 * a 13 + 4 * a 12 - a 11 := a_rec 4
    rw [v14, v13, v12, v11] at h
    omega
  have v16 : a 16 = 361168 := by
    have h : (a 16 : ℤ) = 4 * a 15 - 6 * a 14 + 4 * a 13 - a 12 := a_rec 5
    rw [v15, v14, v13, v12] at h
    omega
  have v17 : a 17 = 467842 := by
    have h : (a 17 : ℤ) = 4 * a 16 - 6 * a 15 + 4 * a 14 - a 13 := a_rec 6
    rw [v16, v15, v14, v13] at h
    omega
  have v18 : a 18 = 593756 := by
    have h : (a 18 : ℤ) = 4 * a 17 - 6 * a 16 + 4 * a 15 - a 14 := a_rec 7
    rw [v17, v16, v15, v14] at h
    omega
  have v19 : a 19 = 740510 := by
    have h : (a 19 : ℤ) = 4 * a 18 - 6 * a 17 + 4 * a 16 - a 15 := a_rec 8
    rw [v18, v17, v16, v15] at h
    omega
  have v20 : a 20 = 909704 := by
    have h : (a 20 : ℤ) = 4 * a 19 - 6 * a 18 + 4 * a 17 - a 16 := a_rec 9
    rw [v19, v18, v17, v16] at h
    omega
  have v21 : a 21 = 1102938 := by
    have h : (a 21 : ℤ) = 4 * a 20 - 6 * a 19 + 4 * a 18 - a 17 := a_rec 10
    rw [v20, v19, v18, v17] at h
    omega
  have v22 : a 22 = 1321812 := by
    have h : (a 22 : ℤ) = 4 * a 21 - 6 * a 20 + 4 * a 19 - a 18 := a_rec 11
    rw [v21, v20, v19, v18] at h
    omega
  have v23 : a 23 = 1567926 := by
    have h : (a 23 : ℤ) = 4 * a 22 - 6 * a 21 + 4 * a 20 - a 19 := a_rec 12
    rw [v22, v21, v20, v19] at h
    omega
  have v24 : a 24 = 1842880 := by
    have h : (a 24 : ℤ) = 4 * a 23 - 6 * a 22 + 4 * a 21 - a 20 := a_rec 13
    rw [v23, v22, v21, v20] at h
    omega
  have v25 : a 25 = 2148274 := by
    have h : (a 25 : ℤ) = 4 * a 24 - 6 * a 23 + 4 * a 22 - a 21 := a_rec 14
    rw [v24, v23, v22, v21] at h
    omega
  have v26 : a 26 = 2485708 := by
    have h : (a 26 : ℤ) = 4 * a 25 - 6 * a 24 + 4 * a 23 - a 22 := a_rec 15
    rw [v25, v24, v23, v22] at h
    omega
  have v27 : a 27 = 2856782 := by
    have h : (a 27 : ℤ) = 4 * a 26 - 6 * a 25 + 4 * a 24 - a 23 := a_rec 16
    rw [v26, v25, v24, v23] at h
    omega
  have v28 : a 28 = 3263096 := by
    have h : (a 28 : ℤ) = 4 * a 27 - 6 * a 26 + 4 * a 25 - a 24 := a_rec 17
    rw [v27, v26, v25, v24] at h
    omega
  have v29 : a 29 = 3706250 := by
    have h : (a 29 : ℤ) = 4 * a 28 - 6 * a 27 + 4 * a 26 - a 25 := a_rec 18
    rw [v28, v27, v26, v25] at h
    omega
  have v30 : a 30 = 4187844 := by
    have h : (a 30 : ℤ) = 4 * a 29 - 6 * a 28 + 4 * a 27 - a 26 := a_rec 19
    rw [v29, v28, v27, v26] at h
    omega
  have v31 : a 31 = 4709478 := by
    have h : (a 31 : ℤ) = 4 * a 30 - 6 * a 29 + 4 * a 28 - a 27 := a_rec 20
    rw [v30, v29, v28, v27] at h
    omega
  have v32 : a 32 = 5272752 := by
    have h : (a 32 : ℤ) = 4 * a 31 - 6 * a 30 + 4 * a 29 - a 28 := a_rec 21
    rw [v31, v30, v29, v28] at h
    omega
  have v33 : a 33 = 5879266 := by
    have h : (a 33 : ℤ) = 4 * a 32 - 6 * a 31 + 4 * a 30 - a 29 := a_rec 22
    rw [v32, v31, v30, v29] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X ^ 4 * (1 + 50 * X + 422 * X ^ 2 + 694 * X ^ 3 + 385 * X ^ 4 + 44 * X ^ 5 + 4 * X ^ 6) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a253006

theorem OMA.solution : type_of% @OMA.S_oeis_a253006.main :=
  OMA.S_oeis_a253006.conjecture
