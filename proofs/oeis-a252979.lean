import OMAStatements.S_oeis_a252979

namespace OMA.S_oeis_a252979

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 4 → ℕ) :
    good n x ↔ ((∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i')) ∧
      ∀ i j, i.val + 1 = n → j.val + 1 = 4 → x i j + 2 = max i.val j.val := by
  constructor
  · rintro ⟨h1, h6, h3, h4, h5⟩
    exact ⟨⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩, h6⟩
  · rintro ⟨⟨hA, hB⟩, h6⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, h6, fun i j j' hj => (hA i).2 j j' hj,
      fun i i' j hi => (hB i i' hi).1 j, fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 4 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 4), i.val + j.val = s → x i j ≤ max i.val j.val := by
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
def ZA (c : ℕ) (r : Fin 4 → Fin 6) : Bool :=
  (List.finRange 4).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 4).all (fun j => decide (∀ h : j.val + 1 < 4,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 5, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 4 → Fin 6) : Bool :=
  (List.finRange 4).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 4).all (fun j => decide (∀ h : j.val + 1 < 4,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 4 → Fin 6) : ZA c r = true ↔
    (∀ j : Fin 4, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 4, ∀ h : j.val + 1 < 4,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 4 → Fin 6) : ZB c p r = true ↔
    (∀ j : Fin 4, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 4, ∀ h : j.val + 1 < 4,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 4 → Fin 6) : Fin 4 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 4 → Fin 6) :
    (RA i (vals i r) ∧ ∀ j : Fin 4, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 5) r = true := by
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
    · have h : j.val + 1 < 4 := by have := j'.isLt; omega
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

theorem rowB (i : ℕ) (p r : Fin 4 → Fin 6) (hp : ∀ j : Fin 4, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 4, (r j : ℕ) ≤ max (i + 1) j.val) :
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
    · have h : j.val + 1 < 4 := by have := j'.isLt; omega
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

theorem bound_of_ZA {i : ℕ} {r : Fin 4 → Fin 6} (h : ZA (min i 5) r = true) (j : Fin 4) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 4 → Fin 6) : Prop :=
  (∀ i : Fin n, ZA (min i.val 5) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 5) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

/-- In the last row every value is at least the lower right value minus the distance to it. -/
theorem last_row {n : ℕ} {x : Fin n → Fin 4 → ℕ} (h : good n x) (i : Fin n) :
    ∀ d, ∀ j : Fin 4, j.val + d = 3 → x i (Fin.last 3) ≤ x i j + d := by
  have h3 := h.2.2.1
  intro d
  induction d with
  | zero =>
    intro j hj
    have e : j = Fin.last 3 := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [e]
    omega
  | succ d ih =>
    intro j hj
    have hj1 : j.val + 1 < 4 := by omega
    have e := h3 i j ⟨j.val + 1, hj1⟩ rfl
    have := ih ⟨j.val + 1, hj1⟩ (by simp only; omega)
    simp only [step01] at e
    omega

/-- On and below the diagonal the deficit is at most 2 plus the distance to the last column. -/
theorem below_bound {n : ℕ} {x : Fin n → Fin 4 → ℕ} (h : good n x) :
    ∀ d, ∀ (i : Fin n) (j : Fin 4), i.val + d + 1 = n → j.val ≤ i.val →
      max i.val j.val ≤ x i j + (2 + (3 - j.val)) := by
  have h6 := h.2.1
  have h4 := h.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro i j hi hj
    have hq := h6 i (Fin.last 3) (by omega) (by simp only [Fin.val_last])
    have hr := last_row h i (3 - j.val) j (by have := j.isLt; omega)
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

/-- The lower right condition bounds every deficit by 2 + 3. -/
theorem deficit_bound {n : ℕ} {x : Fin n → Fin 4 → ℕ} (h : good n x) (i : Fin n) (j : Fin 4) :
    max i.val j.val ≤ x i j + (2 + 3) := by
  by_cases hj : j.val ≤ i.val
  · have := below_bound h (n - 1 - i.val) i j (by have := i.isLt; omega) hj
    omega
  · have := j.isLt
    omega

/-- The lower right deficit is 2. -/
def LZ (n : ℕ) (z : Fin n → Fin 4 → Fin 6) : Prop :=
  ∀ i j, i.val + 1 = n → j.val + 1 = 4 → (z i j : ℕ) = 2

instance (n : ℕ) : DecidablePred (LZ n) := fun z => by unfold LZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 4 → ℕ | good n x} =
    (fun z : Fin n → Fin 4 → Fin 6 => fun i => vals i.val (z i)) '' {z | GZ n z ∧ LZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hq := hx.2.1
    let z : Fin n → Fin 4 → Fin 6 := fun i j =>
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
    Set.InjOn (fun z : Fin n → Fin 4 → Fin 6 => fun i => vals i.val (z i)) {z | GZ n z ∧ LZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1.1 i) j
  have b' := bound_of_ZA (hz'.1.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 4 → Fin 6 => GZ n z ∧ LZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 4 → Fin 6) (t : Fin 4 → Fin 6) :
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

theorem GZ_one (z : Fin (0 + 1) → Fin 4 → Fin 6) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 4 → Fin 6) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 4 → Fin 6, f z =
      ∑ t : Fin 4 → Fin 6, ∑ y : Fin (m + 1) → Fin 4 → Fin 6, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 4 → Fin 6).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 4 → Fin 6) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 4 → Fin 6, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem LZ_iff (n : ℕ) (z : Fin (n + 1) → Fin 4 → Fin 6) :
    LZ (n + 1) z ↔ (z (Fin.last n) 3 : ℕ) = 2 := by
  constructor
  · intro h
    exact h _ _ (by simp) rfl
  · intro h i j hi hj
    have e1 : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    have e2 : j = 3 := Fin.ext (by have : ((3 : Fin 4) : ℕ) = 3 := rfl; omega)
    rw [e1, e2]
    exact h

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 4 → Fin 6,
    if (r 3 : ℕ) = 2 then Cnt n r else 0 := by
  rw [a_eq, Finset.card_filter]
  simp only [LZ_iff]
  have h : ∀ r : Fin 4 → Fin 6, (if (r 3 : ℕ) = 2 then Cnt n r else 0) =
      ∑ z : Fin (n + 1) → Fin 4 → Fin 6,
        if (r 3 : ℕ) = 2 ∧ GZ (n + 1) z ∧ z (Fin.last n) = r then 1 else 0 := by
    intro r
    unfold Cnt
    by_cases hr : (r 3 : ℕ) = 2
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
  · by_cases h1 : GZ (n + 1) z <;> by_cases h2 : (z (Fin.last n) 3 : ℕ) = 2 <;> simp [h1, h2]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 4 → Fin 6) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 4 → Fin 6)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 4 → Fin 6) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 6,
      if (ZA (min (m + 1) 5) r && ZB (min m 5) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 4 → Fin 6,
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
  have rhs : ∀ p : Fin 4 → Fin 6,
      (if (ZA (min (m + 1) 5) r && ZB (min m 5) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 4 → Fin 6,
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
theorem Cnt_hom (m : ℕ) (hm : 5 ≤ m) (r : Fin 4 → Fin 6) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 6,
      if (ZA 5 r && ZB 5 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 5 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 4 → Fin 6} (h : ZB c p r = true) (j : Fin 4) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 4 → Fin 6) (e : Fin 4 → Fin 2) : Fin 4 → Fin 6 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 5, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 4 → Fin 6) (e : Fin 4 → Fin 2) : Bool :=
  (List.finRange 4).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 5))

theorem valid_iff (c : ℕ) (r : Fin 4 → Fin 6) (e : Fin 4 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 4, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 5 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 4 → Fin 6) (f : (Fin 4 → Fin 6) → ℕ) :
    ∑ e : Fin 4 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 4 → Fin 6, (if ZB c p r = true then f p else 0) := by
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
    let e : Fin 4 → Fin 2 := fun j =>
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
def spTerm (c : ℕ) (f : (Fin 4 → Fin 6) → ℕ) (r : Fin 4 → Fin 6) (e : Fin 4 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 4 → Fin 6) :
    Cnt (m + 1) r = if ZA (min (m + 1) 5) r = true then
      ∑ e : Fin 4 → Fin 2, spTerm (min m 5) (Cnt m) r e else 0 := by
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
def dig (b : ℕ) (hb : 0 < b) (n : ℕ) : Fin 4 → Fin b := fun j => ⟨n / b ^ j.val % b, Nat.mod_lt _ hb⟩

theorem sum_dig (b : ℕ) (hb : 0 < b) (g : (Fin 4 → Fin b) → ℕ) :
    ∑ f, g f = ∑ n ∈ Finset.range (b ^ 4), g (dig b hb n) := by
  rw [← (finFunctionFinEquiv (m := b) (n := 4)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun n => g (dig b hb n)) _

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 4 → Fin 6) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 6 + (r 2 : ℕ) * 36 + (r 3 : ℕ) * 216

theorem code_lt (r : Fin 4 → Fin 6) : code r < 6 ^ 4 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem dig_code (r : Fin 4 → Fin 6) : dig 6 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 4 → Fin 6) → ℕ) (r : Fin 4 → Fin 6) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 4), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 4 → Fin 6) :
    Cnt (m + 1) r = if ZA (min (m + 1) 5) r = true then spSum (min m 5) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- The table of Cnt 0: the 21-bit digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 4 → Fin 6) : ℕ :=
  318649978165571130111434875919756443898199782746106683878264997445909209863843605715533485231934287319098074059990113536824978834793591015894962061534304272654607574051509767856860277622432034998566631328855371921636786844580017320315557252590523531247097894659003070029574081826565504710058493995388788428589618256610128242560575805569498897868270482908258551950061317252871017673242997029951684045060307412060558629547842621307544253162111302645920697307689706416008731097463186884650992823916885921539982553045889250534707041602485000642878217864821964115311882098991907382878475889414772895519402695307944174795952293354227296556809704795968547011000649675274108291644566542343876413310088893079383305179138241808376869480924638128404468524754022029575381131766330515216276947758617257171699292150184260417329849834259892176915662823226232001063268265537056465833691329620731203354952026116103060240749967372345042069107355758946918857465833301901726656248415862679261485103296524434954689068550021934416493095459595573887851183222696658789120224621934284751426189560068701538031648040577509895178337859638114276919717826392948945029217085425324297496503757405078062667151167935869851946799841276119682515153649136761193407239411929890568188824516809248668262310385129702872299322208241774698334486433332773412530377338769521605492499311630050452018351434713457137489540712468162444196242624382296070807136430721242415701031633810365186424213539107305411547779000335662605282182861328196237756773969406212075631964814220379076453044432624035561015998383536502400462791493581096285602192474262621309471589854093247047440643240295528321145498082823097739392729892518890366080178271787165171394508305688697311101119972513215305370002833222285562013602672543912101507858365646956246819607967395651728500784909444854717214876569388930232652725370370398289003650729986586250016156876711672771491642235612797810658048811176671525392140475785107908689132079579633649897288040413496303372564975381883315625920507417555769833082215194401466940207093046301085030942838504596091706982299388011700168807162834430618493964776957799615952187301917775490000984342932072675358079372411298111562254787617626602404516102179751758252034362256885070245041421084380525955309918755439335385534478625907035287682804617849444893583795307138136559881927080645211859963806809927072036749044644622861621271706711530132232504871629079838285348191871414025039527570788488287136296526816215206124482353779929088111281895061926520465885919990078169600451066559823400618093551227210560906516714323000490488466520975865565074211374635521944841516434712770666615411671546434436338914884186197372035833618191056062540110500033289419115496229539708058336770187534348494497513598365964881621212420118238699841941256510831911672443299785916021517840865974015445294660061708212123139896200665678728349382373099642578505013769113640973401019989319167514221034656321694224021774907556169708975119889155398531451284784509603801351808331098796363952827614487804376528716357716538438612064395511749237397209065707188842121963607038692089843205914013597429367548777166069339583815529012124192175445011934471767077512359916327303279147690809365565711166653858704932645739546381798278176628402890552613676003779078173510836508142257035727847384404624931306204596358107254487322205771243028367102894704894931695734439761820772187793362891561997012385504574171721779732465418894555780152646621478653562297737767734841129898766676455393696733344393520028596337230173089577802382083491979893435210987251719680886983747871035665278662398748794252023533501762793397261464677403301098279098618087249171428910407553821063646001661753068183790131921127083200553669448883197238040597665823174561549871505531547861099262523145545926489701017560262205025734384988589373970442394180462345451276048141188155047237606253746119262724302059714295947699008776499976916274907497263860090777210407385863476066601813614110043968845792033797008548171114413976811969238802980006005958974098248719167580694581971368423022063940114659244464259424190425999910651913167049254121460499635527686402537873429871690293292757981831668035424889681542632057185841178504811618800609151472508757252896079418428267899254887319424698286399834522127388602623127948947151990295868440807363914635877415050773364568650194413411856767422720791440699144826677765828651529756044198275464078240352521962732018625487781954365024502458133737279605531156811501674198739366518236551852702708868571832184858465932211809339476322465490259982425208860298321224095102272720910945462779905 >>> (21 * code r) % 2097152

/-- The table of Cnt 1: the 21-bit digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 4 → Fin 6) : ℕ :=
  668257439009883826655455872904869065833997470785563124308671195923683391284379345413542479621121454519821164211056386583979578013345048986166151477270789274006155583137271812680550244936438587061314008024571700936204430804684672483334411523384721604601913843979917606318661344850745501333708590799417588430593575106086443664142396671801685752662239179772020238739174991599492960455476897707357234098466313809817624651073517248960359045607428042566497882200216083189745542438507117301519598902662945144129417491085292733537361941710734624068213340351647111688354544167665076551818361468437969807384306401270445742061680943912404483428706586032275030301214034467800446752038986013409545107926079542299214857223040122084921168585660066700259687975624946807368069691246023572646845633545879698112143513931343222102724129239617801398603036121054538893493835169607569041436057439296775684578244351473437764990009275574848149665312629344587048775772187240749809860604677823249538582007348512811814096089487815599805417328129281776970054884597844743372921057306338729135022936288277197567886146751593206031693041599015790632070740079055625665965912669133889701143387847849574269278541406139045331749935180731896944426019505594457010276378947207593864858329713075549463143640748795526638048268167658654292161564892636692427634905896755179774001805916383583565551189748012196288163908907241460103371124756319456384715295910358082797103351954666106181531668688833873703726880731014544364585626031115188838177460594182366776628642422917940466428059480794745292928946084008121240597899376684902867557324292807860384926986582348972345041598951926062987764231480431660506721790108251376191168117877070688032300872615384160024187979377791979201989918940583684743757292801041561800729785215860777656613448762587859972158105887488521034747928092731484445693050015076637449411395576811213686129418381497695503959456853831928914398063025865892655781357002007121505839758513954351152147683252439020552641266891300556908555712195336137893183583144378412028414649459293874674275005525204069993978763078873444141864055062818641673046456592807091532660931492217070787741295600060875611134238760387637536177885151183293250435129298473110393230774338848972828234103273803406697794216421094084013096978864036287146947304298271270603041835541530354083309321407709091097741726486974988747627566150610460222118421611054587944197973252357083765989905007712933566077369568084632663251037716824783538580398089969306241820206877579528194391622402457489857283989106955614983427623852159673474303319492786531622277950368779869873178030251788473011675531006062635332755718605428587561153639628186045881903987914060469021788289768396771423206531201414731708342678789524239582407738924134315620674114444605522123508685849105274281108251610748705200782734551889150773862038054881719933804325589713874282077069996028696697106646244197608549310344017169679655354383049421302815976287365874991837533854782732364607168916935469200048749027707864070607125004100345938275096774630174296844881693867766176144295132122646400469635520881296075735402224048693502792721303729397468636246641084435741789782339794995785082748996311136765901708207482919514297376838321581962574675877608085872140418049404177436581738175790826314794114307037559389961451227788754807057093066621206751702643647165791457861567110480464633844258358104430488249838156855552717139216609871745242768062696163559257979666352374224298387661491057446809671960064574851177565267299297443043368966953791155230002937983284744203007487422243946100827063953663961221073062916273955797944354814675167231276086646088078107509504362506933516569271930060583585842880920145254750623827936129517803577421597800227789771757956219596089880630980712832894242628114623775959395077838497841199966888099132008947685588549999359197834656265111096679726604003808707264948709165156544848344926618798605852836619531938338352279852328455640840839607149401326701035018994397181011794391263778416349404666651596871646681789842107852326621333914386863582453916415921125355544606611577980487776037800746912478380287283707710767222381563269212695628252381262119027990634090144115272697500473090736985344840881736762716100026868292747312554069467459677562609255100166151973076842313570361868298026278252495233095899097993236345364110178557763629302100360566926162210353756155344498589474855684222594394151845563955153336203657493187806387781635145354092026140664960019521595487209848434236343738263790948746502230694271450361167838481649088040159332685060436772186134261685367950977828138532330064635232258 >>> (21 * code r) % 2097152

/-- The table of Cnt 2: the 21-bit digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 4 → Fin 6) : ℕ :=
  119221110995056299867732481321919739238876928098612131832268287224592218208397737988621360612432015697503658667617672277047141667753036560713491409519374222995635257856052194279556561324105455844004647647451631811326252038075556463495715125089568122905914872479730890610246439993766082884221962201564704519636070275079254576891245110617170337684064701117976010795590091967534932938391077278332869351625896955543881066046169163712120625407056277077598896852243419232113558614225064036373555904616079103982187863856240543794679780689534924805207329918405034542780708720619745986900354368189135223480195560232445107069505635887943823925179340483277238678035418779983560779365002287862203499065021756902300046845096396495348438506323764814550478940053084005034881348610303197371346779046990105459501511832840294749306665827960844105323546492960035927554028629744842322351203549528259240651429472287447218216387974582796210236504699112802959539890390520305159738766294132960813772689882617528690791806026697556177079375962089272306452087587596979512065661541590307063172591067474263395313505056992071687708162407958953968279259464736288599777428301237582222538922232376097644802255572418492111693527683608367269399349194592888706170231229333368972405949842505971632229491716844975920965185114127154337881507800224219091811407717425204092875601381544758088455876146667627680893851841979508423108862290238238201355158701711121285321129396539187964245168038435145579876739611638373140234804063338750540210089393699907712254186431243262030171985074106594578531743656973276394398597989924133471755800923081832023782363352011289343163623920316699998668845134613452138481624934724711269909229520865893991707590541900344990638355890985255515675710707186686183099444532393615364304048067924136672864240485276232623005150754802362944246019307148691489635762832979151774582210345740634789389037529197879049578018433367823902422188363830468163518886462439454560616661671944875052170053577892893608693619400160758842340903059269382084623422364755558919017223224217286437488464560718552710088519478529350448196177065189426777801551645788837301568190520396533844379925165866590942529704422251749606533118538744944907668584198989627809935638949657614606184354506352134405907419536479894191682625976941347562088895024369660772133109944632899124536734664849673665377985875000420096249699106683937680202129423100450071753799005940540865036816645032904061706633515190654082534936028593838419262974856205838493345594717102658280560612480943428760778950585585852696071710552053318744357672594842769565838937326030830023473488225881254702913882661590596221872669534952771350120839942498994147294154365608830354277605866878468300208081922980122193546409135252406419438447224056541861428816973561772793332754338486286595316609355476261071405208658129894617488439388462921627970536553355372114711842489698780327211903308652538984896584742066476958236328806814337953095448429545035952188505913493878443954727341725023496483024065033367643149901929820277153448826826050347978511989913940632052307314271837863162280497043628659514863409114046721225600973066585844142645467213927729910409095063975719578885343268033105586732467967263933222087332959161698417998396572548834014205255954978797723413477921436961597602127428102378385733075986108682851014502672639885308210782357011226716805676013529102782719840296060708997007417251686101976968038082822095455571020109174152666603410473043912464010179432801290888599318238162203264182720430786412049887500394747151302523323964797181843674180144656375196680211383141632525621899004221321661189669164167459454450364999882717276967876182177141371457728946819582603991525541569188544529829711871255206669733226244045670970977708820871054133019442311745568269589273770085333406871074168097533625976408638883434642411490422222569009038862503663803553560977327389173327496383220392295915567733174091527980780877351131150462230355485891442373445600666366804631011805319084198944326087471946528233303651102678253257933252129607959768736125377384525853942280516525404875524829538031680322314577215941684037001398391279849929666910374250167120927577006459268264191878098178052482585032249351148957595225129724534332232255661527023540020150595368367592774649023794013955830902116627977790397768354474342220816891755328510192840312307377219019939043070029236468566530608005389319039369666224112826595275309217943041883546179401647998884163206810002980922124323461682476491878745870278074228192488113383352996879852734493716095750698180451218673787368336057716065641734050778586129030791781153192961421190319926509648863980391542109848068947973 >>> (21 * code r) % 2097152

/-- The table of Cnt 3: the 21-bit digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 4 → Fin 6) : ℕ :=
  8061934199629615699297670600235754629043885917690544082189120536009788142010394632696217459667966493058778028454799874009549890560977665925909804207378954290028416667071240310052854382836381154090607104082650743227268272660626717415911363149178901468149771933510161522893443205041664927263961235490851842646541141843306508832869670534830939757597542439237411378076421907334092580256893051342169778676128307531638160666509638544907606677395802958716610506350694798109738875252899850667618519578994798838771345641626428534921349533197128579629214393033781181561721920954357833148834001121415910704504974744160054326703140311733878766336019960710127524309431770246045873847342018084612901743234799007790774042299857073776033459008141284386731463681490009297340952394427067290269574401052522760090371815185062496595865627484014094878507309647723318686775345840067697459546758880764110295701525040807801271129830116638659878226655179365931124999575364555873745981644857422905120610317427841903590923825751141196235122702184320736381693727929953645056624593473624047590930586177606541824857596914392974505764371660980442400960525140934757584172911347361373231541900388404196702665504655839670107540015660457810431038669086611739120754100320584440322549070812301731975505028189712888008155260988187845996412045916120847278415924368629609459398333296192889191898051995751109011380418470625986567994482600904845289821145194787330145961119768569237018659242834697187819754539847807654731928422588762890651183764116827771823574235720320951323086974606329555756110262185572031142739880135463668350640129903098053895639321240966772806510591757553354146644396589553092952848849165608726170320416252497847919353087217554248963253654268590555082260459003770724682918338919768408512152340612592569629189210848217465420222164963589924904912881498529512288493917691647878208556741195629647605644624899877602290446114444756309222049891817412888223542722091638474496766195773459604127760769565683912581297269186307940370471763152488216538761839867434814100794529937239729896093819969506330877032883244432270846849946151703842175793150567367617198590960820899170203898058959122280542068162007535102402966586892484319615835840323281289673230499063387214561611609638370172603636924703401129564707475423669960684913813698437288903600734445505139625027382746730235851890093795871144107030603881433364822117199495333740710273044599571218240882513374732040372015082506251024941717314709337975901666811726265085069836581948383388457311372464774186891707590415607240161869433122889273667202887780692187641698713319718707302587317596395670469910463445641575950667015965177393228451629387578133776811603924104720357910643598426954717608191430547166861466755018596479576342289887960316697157718732332217982780086756950551652388417048726344227760158133878416084230472440692885197674738787425765597729270155780721767873341992653120001198558854238462437900240188786199040283725278119363240723615090491421609899583434412322968687747314981207419785078675584448644608635648765604121317353684915362853534368765874942117654324889717786545351737126993759531677969413410855180558813123994570626308919738520662393954172677782508249737324893545185584860390342292967148809913508423256665606139365012897606384585680961268494875678627561274526920941234392448379283713431819898108745076552261986493820144174927020044753583632278194122353458797501173284880531811381283537046616101834117475398868404013382052355758688443822023728550120775474556681525436484549665324077184247189899284660786185161171366598653464939477350938114263063402544408297574097754514073477224338700658513251245047383107782859529616582779351084039852509057884500767011553047224978945166308638788938036836678333439510606289671759371817992596625092339102661920757560091159083384161853807907580164393935549674002068436215940420018285798677768716923482566377334530145447850141279884964365246364007720704583668133110430206935534960069252351729666365713956800888485219727761395529860173550298391390605938001104507632966955424649074919107400154724670684750639450170094825869335295814552480197322500551723509633767324917910988222605179018326674839693212095264114261686759928294361934883109001575850379284456245844081294959163614611371749724333519177877659321935464844230965711677694306810828198813884206446470193587785055389990821705181633154195012973313772844395985534592296048507572480051896206045404908225367416979623661896787773840383038698344569491440752386417235365680451843042511153014944059513803651758923261880069275175855714748762454741468352625258037973254162360624927411694880567481204809937609147288533007430529149842455032471308676399190729416929620808314177568961839159111752462722371364857711509852422330014916438072989080867102295907749614185754068569914012407830604544120810172978684619342186941153518835403904083359324195469372022255306427574892945249692716410920340895558172409872 >>> (21 * code r) % 2097152

/-- The table of Cnt 4: the 21-bit digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 4 → Fin 6) : ℕ :=
  1616537060274102749207856298044623190028362721336019792757735875307201489656135001291355853014298033101431990571784415941219530394428446901478984530347485107179021000876619601311154776533234386371360748202697882003205347788959369090400921160478047466136490195454665998621114703773156084949221452868399519969246082199647399374620785663958299882490037296721626889925415894331441625236014304231143286505761544784458563787210606963058257742084568176972907481744584923995094465272515418874177071534789642476795101673590676134505769699947237276126447490518413425469704775320620422104053461731275515811687576938785713398293248378120841384669599608107221985398010029136587493516807727421429371933561506436314052554633252766938894206645330012102424832894757576185604658761367009071464590473863437576916305666245030959016781869204531110052449563637484768214276820397823391530030804144001692559931752678112743705292974542778715474525620234573985746260542266167192199293520122756294756002622290514321171785781336861694414473888148320217187023474269540896217471222952832416074353714830306151477151496177378425261879863424146890488032893123093707831378081695033807585335014026447249195989081802627275618962133110858996478809898293552262873555560040308475600981203967311660799470538928610249056048723825075139002482028590785535036129463061722247244194856099920620059717887982475563285852643389765739180695585703494490769851262117707659096579647940273456961999634364157780408369278625330587178331167678345532588776870992410455505476901666090754600754025555090915675447290262000023807449634470095667759063043132673550004758526695603530379453388079750826703814770759141750741419435733650326577519347835568466366280223597365120669605872476130246773063746595670730045785522118644883488391954970528417216139332850946037440231108362322265805723047822998378405364776895201056075310272015748262196274554851786350847740236929334391088910110752585061592271156759724643272799503982552351355151064784603912033714399423678843664089029974182220039889390481357283817177518823068281027183478897032023812261177645718376107656603852635806761363661747076793536691829704212730252559117098709074354830692941313101280200877013682877523993083184838874315744761614730994010500382214824106081210018880450537587821975667038439457988605484276387912141179481098492292384941094432225924912407622806422210673769098529877738674427407490296470659028323244040966432599189159125105707730336806176723288121336903374866710817640148250582373269842648700682579772363580928309551600739782932768671824466466706291530679219679227355700107384977125586232589254773298032986362600726299985990143385142347665087918531389016372363488404208179205302844930111178506597421519826910931832600207328837331965023847673955400519857243603184592395916078473669668819915377702557930150366810506836668817414332466332197770467514692296179721494068865541124395999911037553820503624759693506347139627509330016251385039446079662111832264772307414695607226275630945221617341272389168079962130490076817410633821645102701026774493546358109218881275440078931756511849685539699377879833373528824753157101566567865321728400016364756358936043217809283010665666712570747096029065859971137121630991463008311264271428240626011405100178224140886118127069479493769959291138055545948834195200035113764432963798183411321485850355442686531212840837751468031330139262692688075722533549404683397693839648942451600479216211685920813628337482766578894935939785970081046810548624293812174399931770564019727122649025030771565631404708985988122316160238292547706007065679421459679495919995731616258190671088423180360003221415883565646631886701525637797273360460429475968696528740922888729934266823406299804937073122641318285428640980907641510053608124937261893188577739236517146598012377084910002636998402919063688102395201099129416358304667122780310329947420103205534065226400971852474904470454598725316744048954930191380110959597694162475294509919711777029505824321439525971680375701625131446153985621933046336993186881501382410313993759799668050485900573099581763735171695501015407276253749085256851152004508153663992485257572845438331578483592120854122165831078505551085787797306401209915962351948640843035622765321313581095823143230520703801775929030676728323589242348621333374164512775748212666669755863770315936250794796214655277752142460319836145828972500475096100623248165559214833516079232792512801506075245813933752879087627690733224252180230390867850544407126975142996484581283297521327809000982698988203970946023470372125008593882785286348853576246843393993935946615097175322982710068934381694107952804913204892798267770229679939436631615242594887361822699461823691523743094357551060687471858862576971951307860232478206602099556825647900531706688789456281206721092744779990362779220236700843977296841976205846493852816600684092538865980414574824093349140299949770926144336039176867150701289082083659914027578171274944210933507335545203126945051360109701247252632467815547517909054491936772260916521591013994325187609991319076573484126563752634961898878733495432692016771140990931139800977351712510731140288412192861379188263412392242763437426485924038071230536609184195787343478826183450490531255246574584948633139387865071765960298850019530286237355785983023523996240148770203540756024614664915233627491479530576570508856598750901250475010421967662366844078091075221466655933238321325202200040154590772788065514058908294550857609282634865806179256535411937587164566414383565286075567933350629651565110734400551050041175801408292212524747593497178420876413331406703908800470923191540875205699193951062815812899612716259463053681132402170814356889135416981506620598413369914398578435018433609828548734312998479335479031082768736460467730696313448411682707676247026721390121606620518558844410803903017847102089985200906356649878967643477448160650593440873095971689396869045127679508405930549570573881906841583858293880786939745942236209107661747964045116942196768059421313474817652393982588070166062244751964099013689565547626486669633056340641353922613301183460552847176270435168136252756382308713562009353084611547415099746494420761950035982096144971299538253604624749662379899430029558649222772511702214641567407750833704638139071311801250243399951487877672495969206419843561998145611443173308871030805425569600327197223095771373515093122766622247711537818134238748854219687486568853912905356926637656461039192984904393347919061180029132864073815327456987566967698401636089190160199553217899298630474575699813417902400581081902048346128 >>> (21 * code r) % 2097152

/-- The table of Cnt 5: the 21-bit digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 4 → Fin 6) : ℕ :=
  324139592625265326663711772898037624762933007407881155280174487886412127763693016187768035658445213999132799114917997639361816711872410861648846160634703052897834471562613678640122308065186197483900494782882333005377871450037211438806727721654619759144430096440591739159590013558946799159668284146375428029020881695520616720515150593543236494090113533719200273292631520001491564934563651412950220283570165022451750683778843372692419561884708101496322396128677599607140682914500724494513550846709838308230173290849276342345811261156987185772306915182492099590950550367962617740252855439012458577240221737732139495558373718105159005093998106269288058282664761831779969346371334358087451184375231129853794778255319049823665176164058450620675906059489195077891327887568256319288789664187465615069695710989033148233259546809762264909345489430233117420981638838888322046026392254079694017721024934917057730534779602806584394372723257504592539047143359053604863229907399906402925366409273807375222173912586637128726153595728807900040773425857880298075355758456106789113987329885317803142269988867311155432227351827423526321825962711879752879943480051290941792457703584169311033306970700592414245448663291619100462306082719734859553111566374375363046460948614111083388922674379035907411176243250798977977131269387118422831302473385511488362892370759405718867176317423544350002356943752818837542729144855647486454679852875168365611364679587597098362639885034607097952002100369723036552169317637859856699638104813276527441242825028173998083189681066080260247604471095380293929880072990226308635923907782746457021044909300525456026443320650532809822957159965424236479906108794392116615627883204126698450761429500770708960583896269748234972521698853897793350328718800562555072628821611276844133931625097621111255037352543130477385268037583578096890408908860343530734021966838744635670181823196825271767308314381310488813388162302065129386571572599269639388629247138236695702649660814990984990989859539389219500735245981007362559993817937273098679068852656565789593855950472046552788847750529837938546479166620350424338390372974522104939375613470860455640834951094230637838799634536293416797460518563851765982950609356313051285391345986668584374768638237492013407376966879892302655120749821970737446715738406771431887756493925053633111500197744398888781079011650944370753546010119579477106835362094571390858365549382816350698568803635874211862539343042107701803296594752532555190949541275017807284797298382474888201484160846455872263131610151525334202068681208595680998715987669813458806392292627886145638657191964569211241492927360319421354112006306914350109826001654700532486915248568594663780388117013339422404883635097765671515217203964933494539322561114400642286800630516553422280618940325769378374726819175359866754497057025218376183982628803179314194727824688764566560899863064824782701205860102668571699210441602402119779483899728677392470496604817206084815789606218349010506816683083696898649588926303877352079300736540524836532620430142591521716207246892239112693548478145492043325846218919839795633962687127983757343426264310395489277500263508284501976108010314912945048266443074321953603666482161788137070644531299662745481109186015596948886762043649362336769447093048254365960170601219641751775987274171373329354907752807423203985689174736565731759048764695281259752973355968356233143615779538411436981298942626421582984722643894804673723068345298975531411990764335495612270215592182145852825566313525742812338076481392035699660786580932742693117337658003482777838256332751649002805059594454537214251326328273802317803941826438955757003868870721124538434354040723026429102438656597532912989318810410795536882067432655175700264628309363770599756255392854269978998148321071828555810915674964930426233339413696887743009576303075467519118747951097116958073134805405703635028735219454612525399340594164676897306842102595344361814696550743539927692727732701906128864527790467588848620995465220667361569520784929772284855871602782988983496106873101774888165475295189673484173765814782839174536721489140325720899974526028765122842648457182375592176604820319585359581545702745712244156766352959629129088630464360266099177672549635099844730824926545972133628828696401165512536328366410595712534431006855886254913165275531043210532788100561130500804580104805171625677990646571408612167422746556648776091035745236874883448074824930677522064934278373962153685579458275097158076570962542956296346689854045372119706873364458115196551856350883743321807025504574594226828716218374624515350218715046599070480029439576903869060164320759268587166638242696275942244979112769346206295362305159007813507043901666388632327267907761119589828387320262054297402644994613141700140167565097152232547502169484384709649863614647887748574090622641856090515595030116283999491226073072385032131814975589618245251619901714631260179490085901837814680099750751153321512144941463520589298170080528935035157647699270996869903736423543261948654050681146300574431270721720793619715621931123219839225065239676284497686743154640260744589291692020215209558139306795361404503390636359652014170134999523942712969700610288882303373427706907833750085608978960498694733225809243356426599861470993003203047449142844955538768387640977092996819510269449035749294485153245653123491304235557887144972939175735221639328072513768189871960525840698483533501637237397089050315299208928250121217393732319129142172545627301525244235747963194604062492979800062074746111370836224974698299918237849627240457282640487510152800313357587274225483531366628564858697556917920414543892633068411502904538189340601993812302044741314842165426226225589085498343570404951271209047170229026477565436657559410155242303807849411786842113672094172925392436990758186053887150811762337335738449940335919099665355606596107509703771506563079799670578371433298730406650672314879888227744510416225141256348815083686247391086615396579852741639833931942514955566811896394848888386732124265836509814536652501851618317451455815969872491900214259265681163758863164614613733741679375534338801354385911221074407087152766746069979608368976948736885119089588276692917015269500835669272630756536951077280710685616770881055050080840292793928195299320427876358732577428541197300770013177297122555722599140578700422514557277707247065261837175461668208192113701078642901834407388177496234237320304430639096829074045535083829168764152672305217775059344042898492692539521598445216597474664518724809895110285436029059532964381301108030636480060905041496563171603856504854946674251271619848068998199840221163002867019349976088173480422736966688108933874876678744926757060513499346789364058559122144495770700008859225620831791109945185294495762249881044691031154210981682366874621202742314667092672595570796381249079333104721730288005481906866830430663115703539378174003903632332265636196617519104903237068597513727721089105452304768203434278879038521441434518208793161788954554704234727700912784434791034955967585549663582578051507464342879429189056658972138312391418251603064640193053029670158815312900264836904668304458739885921774455698231728437765385928220085234501148690090484648694384134479121324059747679529334703937835089406748966859309774735107223435954688425823524164963217254718918351137188758006432159855336169840686434565812193564476049758858956971565572794609364422809500818003042033141446208333925663067953471752076654031510944896606316997088803260502832529974343346445487831844000030486521438580119239899041520367010727185143352563353545582618787819691147699146713030720805013714399324885482650461084370407720339113934522812577667618387406232513976888525013001961205566779356768963649790534195352587784261417912375728314705812124706487012300540256924674264640849437566502151636815913498081506963570292301384600474803876844668214695313094927115945465062479700653423742147106019928502450740293841578062777706848653191467577031830124349807044305122395754768202760619336144851843720340514641886203228428606241106512026429509012507105126223869734055414153225288954367502001945694471909600643621043751943721343610396065616459593990672836424709299894928299891877610955181626753040 >>> (21 * code r) % 2097152

/-- The table of Cnt 6: the 21-bit digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 4 → Fin 6) : ℕ :=
  67745174858680453272715760535689863575452998548247161453556467968260134702611840383243519452615049725818755015017861506626619692781333870084608847572652938055647404556586258835785562385623915274135203409622407598123975133057777190710606093825815529661185890156083673484354312833819881024370671386592464458065364274363808894587666474050536427264833728547312857118159987680311737071323803145306596039266164489692415892909778264892715688433903993212731380790893618317892402729130651419353332126962356206420106217787498755550274553581810321826412145273140848814508665026904187107712846786753603842643206343186017154571700107083978232064645604210281204181076935222842013593391608880840277297534423306139443108655361681413146021818288216179721264366433241771279287528501765570731357039815180313549566403596707927980751245283240313366053207290918721540985162517327659307619515981102656049703694211397665065681768936986576138423899160818459840660852962042203416415050646580438211401579538225741421434347730607159903766101507320851108521646004296982297749353517326318924823351946031420856734427673268031485335516531931517001261626206782868351908187330719806834623660049091386005961156876423814577298770627948391996621971288424585646600317372244450876710338260349216428284838945218504648935834839416986397220435301907750371742216937571901067844505488715795243239850341520769098350307826216206503527073713987563378086225113693230223015817394121633121153212902547790450808948116366492511578427857639002918930564352394219290092070540093934178914664395627645932560556121441933703512495376430956404752245873372782161766749652332252548032698691661204815590713418192488282620417574762139060944822095645282735702709985827163982454810718479061680068488066744347258886785163049335958748471232810273598249655706043833962889242830428881737386502778783049369621312699676842554827853048636270958858807475735601298059561564326258791130632378696914105704598174574190344833312373974229594755982345746145089134823308448089808918882245729677640418064017763375512212904655727357910517653742039221320226908991466581581946420775217478197809059887637587481341629633622461977041064147010739113999534193700725434181815479051322877172984432976584185833971662425559395285025080253729464056415600703824653547214928321391816273955507052722507001458763593455201785205155100535285882125315693176086076772040926773530061382104403376058950175566035800882383217938422382989010276964196182351439067183045186604818170717199161043872344975879922498773612989559924001227648548677978268076411572408574875395832076521560526819616236994733230481040655901993943543390202174142023755913424972961461172934806383286811401954091097885129392063789710132828659501784255900115317619858851615464128145363966612019729740423175291849868367153413954196640233230464327953491250138192862056469786887359056371871423285421724953402942827020412114374597959819936508206446209243972296998406187379711804623334301726386781770555518545112277999261497760121680405113711946100507343673814017455212613833301646728948351722511132061322033127957435087056122846601149032071698497601581688872605591421266272023474789080341359697978279910515989214703897230236994103264467503596489845797107093380363467115527627634279482084063314351951359812444775882833227741387367317231268617624073461462090906183287656450298151986421152960121633923379521104547643954295245020290955280459776500525771285310475390737332114768829481005206295936105224393422486005726778166559445391026266289878504955027683850592633725026786018335267642925959345066271573841635182465058938173639318496794685878583455362658121177829687721244050106915618719560114450699437678372444820669965336221310257184342512851855971682788976723112621067566141682378180327559457399590808702009539019752214208519728491866058398493515646103905637723610823626950059909662230610945831215222262260975364811980713279428746041241139012704202671122033806407174264861932914608706528719166901757162448926025517556344065804413458752286444460519175090766231181211999857248814543108436546938182950542833806762921193302193080811769269993526777519569572521132470001934836331495812061623363783298982349599891551300879006996571193683639955586394754200110535289921073043598252957960097244917407340090956919152077916480417440793188230119041911952800456237758113521874545540786948546933763974400322218006445600076376885705011856394887133413534532642067000736063598472230099719377065007620038843195925733057888388770461375274730154238264162222768987002546062216118308548057802748364110803758833541340250373173236911354877471615112287629271961888497435602872891206696667247871696069350733104242528408405317776914864444523281423043201963620551588181292255607898452575062709228196894040627983988127009787234087757200620261806078236553080838269400805956554532699766424619638284502260905373341043983403090358954696496302314946299383894048882808956867815937660042952033224736399649202242666088388261262793181731766737440247121644467977875067294500145618209715683840805574834754188699201983558877449752530377161945567651942395582445715009395865226587019371466918076581549803203194791159185630839876560977296066150139496383059223423293203599465647662440421177729463757398280959655086696779898738502266534800353292446023365420018115360292075640215504854486900800388936282780010894617844343893988447811015911270221270459282340217491136623639584605038421085881011533721390900111313693493043776949314615627209574776827218981032400031302961441386782970723804723554249162916946646927075331774675365344359783563972581340798799245603699270079082433629840984164426941314780016719002198457617179638016053399645553382155522381447218562279694855699425080135690518725899808396771935609415895472893143819635603925424332939820254662489509953421964486573796510539178166346310365629060769321241039686316961350518858260968738334869810861843979578458489917698059652739438378028448927853637006292436215796926870957935628180282256888519976109051811991197246672692966555716445409567241233153248603678296048495830032330172432180591857648115721953330905830898488657522874722740615647020448687530451496896695977708835324946504176812562186807375191030327588584441935716396158350829190356210858010569892345778470650360132702851178163209413250794085419068475494158058682738807858945642296886822859214161104020438089799792869393229960002037594094997345272305713104333368397776110395379715192395514387561117698923999100330758666650281386752042656341277748821765431274558595761451857435931513048636158927244437862045734387008384126241556505789074470947786778504113918308978863608152852178364969149066392064973264730430253833200637250936822974266084693386239659807405873094836129434318392127425177394268658943463366714573832579007599328440174232912558751365230686813481755455127645763955077312293265568395728867099183465516043169318824964337269400199316043987206547331757686716572876993509842533221958901951980739389762802313185432996243739281978940192244012799798735492022201063431640431032572444829458214028847976129252812135772315908285589442844905697395089433308572255341800999597909679792973506292940695182277661138257476548957247420617473763141796197209800520594841310054481764785950880879538812374678257786277420213992320891186542069582210990034688737558880186858040501552925967727586215094352330063126126799038639946099180144663585262093235799236058689679291921884394924312216424426270185087301225299409720978870794785270683602059861414644357396801269588666815176414966717024675739047931718034674615555856011321090432906260326016799460340889695587349324824391060575893217813116875190113144966355094641220877299306491324246785053980033826497586644446945226607939406624271061734974419787564728893205216935389373064354070784864123427729317333054056778001835686306056359002668234577834245737027457211398554240948248795726355285957954670369159782197917196698532999775530120740224218851175305008212285687787480260448209747332760930271016040040569221920783292943559333755065737260376530553704479594718210703042162206753422226285320450890386839102892695580478629807441023546096584111768393086185457675089961133611405486399075341541824075969448377365688468070172536000713822744608784 >>> (21 * code r) % 2097152

/-- The table of Cnt 7: the 21-bit digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 4 → Fin 6) : ℕ :=
  2539633708218953834410181740656124790017580113040748851620167112590039021028534781831162559383918251683205481065382511504399833937520339101018709668572898419454533084693078172145358283690733857286360376623883079097135622811041551623050711699163945812896609805612036276315387756234348171416001006286851478607378608084404032005236204900411257931196039536689934141247767959211686411262306208820464975921772242950909466607407237825045107267366687975223685973668188992921947250635113176414513670883971583144983407733804080142279431231164994600526024680454825600295097562132987109994881122364662612952677137315131312947699858081353920804911475162619871936644678408951996059828819404695615180029579935902404482087630424755368416655245397960612995723976097843435278553999097288261627667018908793094071065895599074716407588549254487345564721909685876474993391140302690003230616783310714402628844230365075147318739998187989588729910286722548482543434368218184994103406324478266666920245816660280784865732605116301903569413422535209896819459791596492135420412367503596692708090729651464987619685362775382902811501301567863328731506417847577863814357166201864528943906107581966551945960115439141565613090276889835652122168158109122624598629122543230969469021532391560338352209153759746334566565865870009992450823495648072842883254878975482511323261724899943807324326447013469979054664921613997734785946295879475662339521876555395778152198703129047339387902832058008803602596768114546677847349727082554430784562440362401249972255377304639954726285530508747273630861359916411724118233574334032231423298167413223883557623722066964046264470806916489354806012238376999603064266930044623685720049508470396770728682586329310576673268517933632194286584363793889103673364134551971249355590371777928087650145882990018703068113019879906768007712967250183696751435945371316749770048997005305598578903251818183709833931816487059210777461396747142653969098153537202204707712339733594424550760310626403302963515552407348114589584025047958675841442307482477405801352486926066479413022639290212744315033177924107241746683142303720601340751462050183516689472466357960869357273180411930639307956406700890778427062961598130832026604518108168318494909976154010667978007273950767460266441566208866854474536844105475390424936202691211875312605694501069192209567249347264313114727941739359281068060359085988433142061082137143209484046658854241962920320252638130194894592437734171031988896608183142485680206469335307235795323272140653485721021607143214328111313789322800852785272842384876723062519244906687599695429758329229955180461531443448926014414635796976594609270027659377049907269936099261871966551290280713584779155822916838920037009275131168063817378251803978393810704699326561831787882199075868433322441948012714756503971811581876261245095575369290455842211104288908849000896992582978847255824337031717474110645855503801565934522473536243984895765211964129773774479980645536418560105298272479273171402702794055684450978565832196117138078511515676868937440781734977809819803994770930272989980328804696862117068924618020377632828029302766690845874879362022334760860740949149618322131549138104952521669720471641839413184741817123047517665864828168704225478182345347974030036620487261676233085988154622078280446627814213250990700347805254353723801866861930270007612941730075774059876956852416900293201919463033324489307879054002517871697848338925396686164498266750376618280096227346389733285822836962496194855323960128244504095178466337516534030482505265594632848357125367584360396741341864132593480998489467737131265072006489735272373313621360373120344427368034281062397603508753544472464174196251332031882952163970185327225191994629401784788330879841802349275780903088932729479346069710888208861770661622972120320271040716239374900187925080409827416795796764515686328106970767989606152687448344755662237518016791603613234048407722918622530173876492827487294723339417023728681404258193125006518886758407314813184336416440898647130856005498302057006425568010463961213674118903263795193620286621894196395204597688946480650522306391381270047792419316029618183545490713401837420580243178331917312398425851986955041837640086117484657463073668453733534234911165041568003893272625437339098098938203292574689553085763943547724005499991304855239709518292062711460102719414764151242514563934776493089788258507200276499934153495205906353437502149856701986325826342192960252115400568807432742594859632247704278967521872439991604253690111513594889684472152119824118385679809375575146156234762798494429801104497147047345019918378882658692035184180776866195268107990696914313777478668519375430674115550326355376496751879629558858328265016729521744696579499844877583084846952181086488968264442523800307078121599735054427114494589827481533484792851295594349247180486612434901008458090353523272457141450290867129374163437027563481615015034864040916574233392951020931597006639125001107036465690815730282100427635722497669434363291747301295743057631975015670672910834589637273638884976570551130657238672928113595754388395584743382474707733573584289069100459835395214601377452415597903300489535342489559835917878144208681484239011271291285125781795292992885991132850136489641375299834366758855904025527087678060056873913893744985994511976157166656314992057280208291653955583163930047606580719524922360546635446143794432736031630729321687570894732451575942064617007284662287159588814902782546145508476353597195093789118187665080101254284147076551941260603038797176832441555775679638090084122817224744756203503949567291865855982996695249770553621100751619707939365551312459430506258853184776962221174197835417824535000998071003489463176340178827387114392414360051318871447958067719580465462916342471379435401204000941611786230067768764877777853745140816914849303502581738367751933970711266120464176673643342583712671436801354448934261398847679821657720531885948630329137323955096458874953749787775640451013460460115454982929077527322296190892763907890371103967287535495101608793294919163931269160694599961720290107128158426483718394426656050679891941175779756444751042057570163672497162508914832026327718484437269534304533623014737674901127797825175321331526023213068011345388489202968539779129666250564279164160336585672984603586564282974741107838690016257745552442682542648490716425073716426174351163194423321265500823511820054718251805960267441802788321677005220917259343150182524243985460748488975896839875329096902014823308895855519856472442981006430978814761335433596790167422665126838994029329154673104241361162451485226838788087178512760505334480485404044996749691064353104911025876359985940410404993111525968820088340115566979980605503187893631216922272291517566796104345422161083487559883937363172919267422765232933179469575090463580471129142160469178351528627465401746757023831226529576318676327905054925121411069766885725884036594365590945649706951132588105167660077922204704271151193541888349630217286807979161837396307252267228752778146689704982950808816317569444146293942797668545788297818378969859263791290095994183549289637659783051550887287207910159504180074176681809667535174084788302859694636469689797632734109698922434119760603668158988166536701073838151247658311568580986043061113485530568980484645226609952911589385578206893982347712028435802281330756367079022245407713216833398024101687228854298817548001933080795533486496675486396367533128860190464589913806874128105121489390406678296574787773357079503239132765747619567042541497974973530987391375002799055740943477002004904228471340005188428862269628419068552609998076331884740797554567003326709602847410101412073990725159505489106490573274953421537697891733339606953065720528575406711979656078716892129716747215202501413203909361071837822432761113580032616645598671825628623437622042090560917722734117059232123050064792047640491633147287192830142221909729253319239598806425016217340634303054139425714168664119723469986404965904109446508923371511159614825904808341624736756357197682035883064595500482992811161140927752532363034833857793118403428194476308711859908009861272609628806536816814200420208632251583352956799438873517312719612505823427666988692855908670111760 >>> (21 * code r) % 2097152

/-- The table of Cnt 8: the 21-bit digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 4 → Fin 6) : ℕ :=
  32483000995755714180950547897431044490367805471365994214092125954561018559582968231224798157439770230495095197703277297433365738146869909678415820295685497040050685898704204577562576858136504408454120283676987237467932631622579069917138605170174409923140773254601019956399994028782735584187837759160720769072269617353207563412984786430748358782252547554602216987474482513909474196787427199045980425277416947394957291273529230907625441555152252975250956283243168289430389256910861103768686471001333026382670355995878530095500783914325156847800192891183080776307927504024637811603959402109755511400974341003350895268391305412472299377484832223564164184680683777448166068107910530027017745539795037216038336113300287939978958298928789512049794573939590706340723641596877670524887478617218491682979416285343978883899638964446705853360239532271951396108832972961515417198442846958088376597877071802843106350081868336056241913273715804307732115531377440838904158858710266820356359743972556058493139714302044666581034030288771026086786027325495758311025626622161829657480012289797353006296302394359852819329799608681593843289145201245605675357775966380019149847563849280359166580791454818467608779146894443024914629079467592789480395969401075278256974991043465913999654107967546325389396204864892317980022255899091298507193314765382262783310533150912325304836340297965649896486810585205839233876904796010722685501531664390676441053448866652686572774378296231009015136629494355302310808613634557214026776975493283657718209318057609112676519918400214321429753808134434472431166252638961604454527202387493440555533705313661445355048606176489233869822711772073971748535255754038049228338948093293190936414689942145744782927810336421995871247008020934593907174082230963187647031631206741443327198865926003838215165301586262587904783553892270858431398339863585465546927131111416797777131640213252026771519059402354907376781788847459973961443506598267947049639442683336882409495324911844463571304963439963596232422184369694018718839836507595114364935517113400046611790580171494218812209304115149615252335017011837646630943211145281256025586242219535855343453392012674636869140569276684193455341591913798923538354752104738515792651304762436446325558696831495633102407206998519937711046167052389533169758275417852526745764793934631796652074970325577457770546849858231652877265666777079462354700040415684246279932848157524691516228823406806520146861060546792548762986098630934763349119978845682057272532848157526637663420269305644622771624746100978154981978727096447228060603431723546940442168698120849822823502751079424851052122189702199148216362139251803084514204563243267000484946665810108949453561941146042345842357433005761737009132449473199305815772179717305527878485302365657108534445616028846666366677416649668950081019403167179286711008394607253608168028772197731150894014089162849796720737792112649548813068057284663271060189227584958886788338217794052959601496401815932904062995599536845500632162005980228515161468792734518237972625812044196531109424270572139387935598836520354369379414197757861240970942318205856428976380148401778742714538512401364364806936785306386065522057513070557620584989777880284263717807696208130355217935309936058774688590952610475465829833451446219919566190632317099456804684244276733584057876402523052794660128589912767465243582503548999144826974839860098357284078101102402801630147906194196216404999364940602703580393205457803056841299648515717366909021024895276945174090993290735999001030075611402158334187099810404250173832449074266355131836044447579010339848785015542023601729126608336361078832276850252176584819653349988907395322539198929881202337144012741357289655129707009541388092432264460812678632678428891550545560204278676604121580089872069529613108318297211617629669762329931657910579488276991788413484052344101451188850600515416454814277000815408003419796987975838282320550261482040082165636577574545222617100090902967838427791722756290831716234271184286748380688659611395544317796496095858444719857230997120297145223977679631234158636725458895268975033141164387519810735789010087664448777310962866194294326109771021426479536211524150990539851412499800275375343407826008606166453106244034147278190066238764843005496029193965102287919271512546706409364309123918245236208036975233880373197334550563530850775087983164398324996257862516504880752904202475117362873094205683340663613684974863777856944234675067413126150333994623088046999204047618084689448165863075587578451026882484376451507608954858675529347711464774595635907559416010928448407239906863871431324767744903450618854647721540906420484477575383736333856533699226044518873844370107509739887495953478912346416851452151137639583389593419408279693158140907746391954136772141745866055820324715635355343321855790038880692778414228530663959044844502252745293129184710304957907127111582708043057467249966141890094481254587415097958340347783183832450499148191836326869095578965537781288231851238368281511029527471256097029655377640729508414045233980783662321896762540789172405665534250922109863211865702898440552144531688384314385696535696802982939592378972476438597474010272054576450312657246674829994690596158579784834758168850548002205962690485647816171745032808493009412776030681083356445121108041868531059625503511821465060786132572965130422544099515751328637481137893009547175770261527675223771962333834188801172736631179356762797149025616414230062924557274796750965213695569558822401767499849628524055928994241221368279015681988627363167175131795247658038832427918534025342004723504750477321382302503789474416535282701221585599345363156435231073114308640254683349577678241779108443850065562666873020876554876812682050538344314569825437279339637196521777198591916949950496296760991283478258905865484090160877176288764704035970134049943210465920553003283191332934420988456901000026322892079146284015852308567474019342003639743985076559586850903638484069376572326426673063287397333609895475785908973797908518483515234809290768970743088429101093750631142205622043720439571815631156258396779033726816165571700354988732453003845314563749763289511438398143702994124399289038186826104396570222407546634184779724124171052464426272952695487370917768880284509231380596697117554280964330777757108917316422895937441885470009805329847563886197247563025730759099800525719633027387066844966821619497214140517534023701863868727155114532908993373855106814251716379879335540625336175388462794542942011449584521174210555273712575150303265106051741280080308915133187499204115849236664247057880515986351689380865122529670460933520341937238197814005740504281823340737596390841249846911820673707648362055657982930980567785566006343280473485320934897893005918375715634714952884721524443510740699068455328972471343985765818618062557809768888261872899091278205502879330948338645415728137414121834079691257380559523888405823650570135574997473995115190080330022301937212247540179629069304032853091199979820051912515426812571109907406021234186862001323051593807462304781121170449210724743207278350116040023018222281279794551363733020345757828331574116445132759067605989406693549358233260018093095276928082507717555739107389795243307167848001981998583591892156155309764076145435490801699821415676834058386697614954177352607301009512200278115513758045322117607116563310113454069631704121263264464791106206172673833891790340054283972125020439416047289525402206987508193971897538722130559020574535217864300644718034069810570265447492235598867681722435745181418026187423962074925344939956295290768194493248193157388247205375001743016214687501738199102962943174702873620208674127262100666546451083990957908520802770087638514436679956661949659238566339420115630699368060153468929579404084486777673428353092380448850378613134821820109394405442595565730949660179062480299613348758258174090216323574257123239253925014325195793996963143943945063689244619875372776574781949832990747943845506811952290548507894023495284036694898465890304405752352434174488122657620147544459101032075837342097769300279232136916291574067385253783198406691516216142106617648505968978176125330237665944712062924009446997782450944971282373435476396878380804249485328 >>> (21 * code r) % 2097152

/-- The table of Cnt 9: the 21-bit digit at position `code r` is Cnt 9 r. -/
def t9 (r : Fin 4 → Fin 6) : ℕ :=
  208253529609473092340228203563304111195313961532422892525561785151749950257745252733333395317873539535376839908151630041334819362860498402803012330130744652128853589124019598866384420608028893345653873788601024191628180227091357642415985233336381757474872592791247821166992551501365698470902838866647431375513365092619781351213294468490252125959510233257445510785323191602078302130723389323443670478008443193789823231064915068930798412539249145757458709387148912873195353099591339973959560661544983626110029966078133913706679164879402284102177519173362706637293500550958990608375394815312163399163874902279882715245839504781920662751796997313998460973504738846443826485626001269718383724388582871539595922928255638449758226047060437413222476801006677542838698232532740888272980872236827095835593170091945006110052826893882869721221199394625603513749704302847808036453082521793375892199421821210446167771715733990777148280981611204808119079547712468119106132814136199265657892335996645036240117517532575209101107888337440228426096151418596791787752643048637945976743693692048867480648764717458938453252861229434894614773066349091215510058967006833455573760017856460683121990095842687314896830102640262731284122874331857972300542672275775057625453276726542702966798428757717368829439923940016578169725275087105231419078044403196806554879453257873745663502307594596197181863583828774349135716274539091670349364777326984554102389442972230251074495018723023758519614606537707761855025127592640529451343905715652398322669680073665916917774284442346623533730160808988620326140342829423761596474558307269432639499255199818283726347542072996505800802661971982295846804450030494707325293237326084879148632965039863654649245238069200197499791215479324817727558880280004155171934090515341364948859184083301738139566286400605191283955690968787973783004189884802862565998158789232253220366647462985718387196682323170750965071232905170318458538960044932419086591212210615045792955724041116586797603841642505429835552355769549009298572018839307086412090481848235110445367220413908866493590481569041296645416785829298441262334944822796495033247062965822803867785354373330931008568550292388332669248694178441871612281951816566615023124598083517086768248895269041793855052470387210151493280011006480161394165151245864272805958456396243574622249161810884762286777748912726845556318147808130716774321558373940239402603116021528925080246164159915597959189624062390902898467102395020351011926067090458591693193226406516973296821750802291563519969024387545099709117683909774385011690574475993071293647067679408498030164691502938476377822082247954888588378259545202537813273144151585226523238049786433779020434486856045435045285534005798987049118222324070681168320639300123361930647608024022878235422961908984551689686914831301630037868144270064114551912906419390136460507643243612551224297085920381577490860830935757421811244654883925364764506897504393932464804898691447897573081486686905676842631275562449012014283543077393065989145808757094947207020487032169733672305494718519520954985779246345976608877402476504817590359423190178772976474207890745501172012251410646016029120556339298468587970237090632258593245147409791651189574819889280739730149363550927061122634008026028556789456102382837508504323424082380961911697806960882591183151691458263818107659624156116941103593508164048065983353134270995068760154039596840759843114983021584824609274008362075038449010035233170439202212062511695674574210218377938439339489064459847036534842019477079644080192673760061559569716849887222791140873972001510595100901864679643008523094470153146904186855826388380810365644657573730566310756423530673438417197459928604985040813402626431983821115416176614302732146789396825355605784365256607040166015513963795395495091354042812299463814755748085903033791608071745394855326479985696915209663318848447170391456895304438636787035883077918921676246149209160143961211803340403241055592507354714245300659309463159495204329493260260473081916748051021050430406798449025785353195941407536185759900789783666749942482343592038067987625757313768818004890662696846174401486729213619919273493031692489595006363922887693308080076134686068411275617757160177147206719680794438134304622138768116975973551491044890031862549902358729212619101504962533554447921664555974262816316852450131282678990042695325212031843480708895664583462214881502313137883233400538214337957577768370451699108767104661369495077880564243839006278563189204759227206697134050783102767656067193264438405944273725545224611553165763705838062984184077508189790758667265160830789356999878932024397877508617989397147060414007779599304349539486849448389435087217552254882503210932415035280634598439834221630772176176285127644466902950330944894552936091602884015598625934928587534133228516711981873928171058105027635423215587871492800722404750982788549454461884076767281960408416776047221144574273166077090799426532527161362885261427988514237482673877654643507952218813587526101951395925725249676339937011386774140051586590557214870806658709376879739225688382903675332472305254944196307100893364088384912014586335449728144523430993665745472318365895697608357003606364872604593351435249819652328275539294689442079816678444596620885013661766194692083562118096488296877312976046896836898627997506705108548149395147276431290219386639692027755752480603554603530181863097667244297072255538860616274934333847411836714779239641762571179194126652181557519004879858998552443474018283834679597164906582910516834844840667733019519077023302149021765922073068009826362015311838869396868244406924054252037058569006752595819283013479591361531343527859719797342248914274529527198500174639740203177582987916557203287648074962085774634310087744244526530814757246909661088545674240095624018105352651356916780153605210972173298829110367357693314737778832860273353505908029826092828631287137834722464018590040502816247214849030458899838383073854612044271146546919912959968843361089870239299001694395553389040146455411659531250113052977994003040320533968301809561875223164417886388160659204839889064391124122466954400481921112943935280236842363332805444073982901513541740726273871304617426163841382080203667129205553340636268868662682650657726627141597209919250594287824738908986456435135711596441055530600229807660293639819440856625497369846427451434046177569938582553240121596058529128130854872016345800912553504406210708818714054925016569222066098404059156187374618199143390032812394540712432269531153707016165223773809333969447063006718239880454035696608398412781009047537269943667243159999894458238102434185457696885330927476177134688839397517547306698449968002092248946109354503971124786781310385056324662327361706278194605722735309548067953324231118819164671836158759028680781705920409868070888088860253933913221460598652063689662575487870988156036455525282293839066773734402750084049174733039021265116993706421416867498363603353757199137046069723360587805991199053843295378900401357364045183380122239355964787442560857427816721198181867299136037496661979312175525506113029898223427910481504689560875971082785812832848351737684497625502533992536626626409089513156882382625437362594472821964328860879172174332247921521040223749519913106907227972521928807623749569113415619629722940811992486494322325079949826224263164555506564727530235224903520554335763352521072443433009735792174031164146394815656366297400212136503775686343287084601134843896988591571909270155280461927718482861504929835434914628164173124677594212736786516411560983702726804875413961138575025618720196516839631910593734482344598182744604979173851171210360220296898134980131809684411488660204034668823445022972035220692150869469258821836651780608608287918139049642436541736618775707541994545083640151163413006428660430879445198163552400685396273789453995301287474559230288793622911034344557279503560452220909969151134691475119647579736372838271172286902547896783175272475410920111910264054559098361139990619206848908053645760220706423684970953789515332889366402816114681873415375378296947299919020935192246475289586154609788678378636057624234229796963338064925617136675945114485894468490214516232675549825253884280968192432126558224 >>> (21 * code r) % 2097152

lemma Cnt0 (r : Fin 4 → Fin 6) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA 0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then 1 else 0) = t0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt1 (r : Fin 4 → Fin 6) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 1 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 0 5) t0 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t1 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt2 (r : Fin 4 → Fin 6) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 2 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 1 5) t1 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t2 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt3 (r : Fin 4 → Fin 6) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 3 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 2 5) t2 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t3 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt4 (r : Fin 4 → Fin 6) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 4 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 3 5) t3 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t4 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt5 (r : Fin 4 → Fin 6) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 5 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 4 5) t4 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t5 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt6 (r : Fin 4 → Fin 6) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 6 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 5 5) t5 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt7 (r : Fin 4 → Fin 6) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 7 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 6 5) t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt8 (r : Fin 4 → Fin 6) : Cnt 8 r = t8 r := by
  have hf : Cnt 7 = t7 := funext Cnt7
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 8 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 7 5) t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt9 (r : Fin 4 → Fin 6) : Cnt 9 r = t9 r := by
  have hf : Cnt 8 = t8 := funext Cnt8
  have h : ∀ c0 c1 c2 c3 : Fin 6,
      (if ZA (min 9 5) (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) = true then spSum (min 8 5) t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) else 0) =
        t9 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

/-- The difference equation of order 3 on the deficit rows ending with at most 2 (the
others never reach the lower right condition), from m = 6 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 4 → Fin 6, (r 3 : ℕ) ≤ 2 → (Cnt (m + 9) r : ℤ) = 3 * Cnt (m + 8) r - 3 * Cnt (m + 7) r + Cnt (m + 6) r := by
  induction m with
  | zero =>
    intro r hr
    simp only [Nat.zero_add, Cnt6, Cnt7, Cnt8, Cnt9]
    have h : ∀ c0 c1 c2 c3 : Fin 6,
        ((dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) 3 : ℕ) ≤ 2 → (t9 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) : ℤ) = 3 * t8 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) - 3 * t7 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) + t6 (dig 6 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 6 + (c2 : ℕ) * 36 + (c3 : ℕ) * 216)) := by
      decide +kernel
    rw [← dig_code r] at hr ⊢
    exact h (r 0) (r 1) (r 2) (r 3) hr
  | succ m ih =>
    intro r hr
    rw [show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega, show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega,
      Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega), Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs with hT
    · apply ih p
      rw [Bool.and_eq_true] at hT
      have hd := ZB_down hT.2 3
      have : ((3 : Fin 4) : ℕ) = 3 := rfl
      split_ifs at hd <;> omega
    · simp

/-- The recurrence of a, for n >= 10. -/
theorem a_rec (m : ℕ) : (a (m + 9 + 1) : ℤ) = 3 * a (m + 8 + 1) - 3 * a (m + 7 + 1) + a (m + 6 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs with hq
  · exact Cnt_rec m r (le_of_eq hq)
  · simp

lemma v1 : a 1 = 3 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 13 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 33 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 68 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 1247 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 8487 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 27905 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

lemma v8 : a 8 = 62977 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt7]
  decide +kernel

lemma v9 : a 9 = 114433 := by
  rw [a_succ, sum_dig 6 (by norm_num)]
  simp only [Cnt8]
  decide +kernel

/-- Barker's recurrence, for n > 9. -/
theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 + 3 + 1 := ⟨n - 10, by omega⟩
  rw [show m + 6 + 3 + 1 - 1 = m + 8 + 1 by omega, show m + 6 + 3 + 1 - 2 = m + 7 + 1 by omega, show m + 6 + 3 + 1 - 3 = m + 6 + 1 by omega]
  rw [show m + 6 + 3 + 1 = m + 9 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^3 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
    X * (3 + 4 * X + 3 * X ^ 2 + 5 * X ^ 3 + 1129 * X ^ 4 + 4917 * X ^ 5 + 6117 * X ^ 6 +
        3476 * X ^ 7 + 730 * X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (3 + 4 * X + 3 * X ^ 2 + 5 * X ^ 3 + 1129 * X ^ 4 + 4917 * X ^ 5 + 6117 * X ^ 6 +
        3476 * X ^ 7 + 730 * X ^ 8) : ℤ⟦X⟧) =
      X ^ 1 * C 3 + X ^ 2 * C 4 + X ^ 3 * C 3 + X ^ 4 * C 5 + X ^ 5 * C 1129 + X ^ 6 * C 4917 + X ^ 7 * C 6117 + X ^ 8 * C 3476 + X ^ 9 * C 730 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
    have h := recurrence (q + 10) (by omega)
    simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 = q + 7 by omega] at h ⊢
    simp only [ show ¬ q + 10 = 0 by omega, show 1 ≤ q + 10 by omega, show ¬ q + 9 = 0 by omega,
      show 2 ≤ q + 10 by omega, show ¬ q + 8 = 0 by omega, show 3 ≤ q + 10 by omega,
      show ¬ q + 7 = 0 by omega, show ¬ q + 10 = 1 by omega, show ¬ q + 10 = 2 by omega,
      show ¬ q + 10 = 3 by omega, show ¬ q + 10 = 4 by omega, show ¬ q + 10 = 5 by omega,
      show ¬ q + 10 = 6 by omega, show ¬ q + 10 = 7 by omega, show ¬ q + 10 = 8 by omega,
      show ¬ q + 10 = 9 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..31). -/
theorem controls : a 1 = 3 ∧ a 2 = 13 ∧ a 3 = 33 ∧ a 4 = 68 ∧ a 5 = 1247 ∧ a 6 = 8487 ∧
    a 7 = 27905 ∧ a 8 = 62977 ∧ a 9 = 114433 ∧ a 10 = 182273 ∧ a 11 = 266497 ∧ a 12 = 367105 ∧
    a 13 = 484097 ∧ a 14 = 617473 ∧ a 15 = 767233 ∧ a 16 = 933377 ∧ a 17 = 1115905 ∧
    a 18 = 1314817 ∧ a 19 = 1530113 ∧ a 20 = 1761793 ∧ a 21 = 2009857 ∧ a 22 = 2274305 ∧
    a 23 = 2555137 ∧ a 24 = 2852353 ∧ a 25 = 3165953 ∧ a 26 = 3495937 ∧ a 27 = 3842305 ∧
    a 28 = 4205057 ∧ a 29 = 4584193 ∧ a 30 = 4979713 ∧ a 31 = 5391617 := by
  have v10 : a 10 = 182273 := by
    have h : (a 10 : ℤ) = 3 * a 9 - 3 * a 8 + a 7 := a_rec 0
    rw [v9, v8, v7] at h
    omega
  have v11 : a 11 = 266497 := by
    have h : (a 11 : ℤ) = 3 * a 10 - 3 * a 9 + a 8 := a_rec 1
    rw [v10, v9, v8] at h
    omega
  have v12 : a 12 = 367105 := by
    have h : (a 12 : ℤ) = 3 * a 11 - 3 * a 10 + a 9 := a_rec 2
    rw [v11, v10, v9] at h
    omega
  have v13 : a 13 = 484097 := by
    have h : (a 13 : ℤ) = 3 * a 12 - 3 * a 11 + a 10 := a_rec 3
    rw [v12, v11, v10] at h
    omega
  have v14 : a 14 = 617473 := by
    have h : (a 14 : ℤ) = 3 * a 13 - 3 * a 12 + a 11 := a_rec 4
    rw [v13, v12, v11] at h
    omega
  have v15 : a 15 = 767233 := by
    have h : (a 15 : ℤ) = 3 * a 14 - 3 * a 13 + a 12 := a_rec 5
    rw [v14, v13, v12] at h
    omega
  have v16 : a 16 = 933377 := by
    have h : (a 16 : ℤ) = 3 * a 15 - 3 * a 14 + a 13 := a_rec 6
    rw [v15, v14, v13] at h
    omega
  have v17 : a 17 = 1115905 := by
    have h : (a 17 : ℤ) = 3 * a 16 - 3 * a 15 + a 14 := a_rec 7
    rw [v16, v15, v14] at h
    omega
  have v18 : a 18 = 1314817 := by
    have h : (a 18 : ℤ) = 3 * a 17 - 3 * a 16 + a 15 := a_rec 8
    rw [v17, v16, v15] at h
    omega
  have v19 : a 19 = 1530113 := by
    have h : (a 19 : ℤ) = 3 * a 18 - 3 * a 17 + a 16 := a_rec 9
    rw [v18, v17, v16] at h
    omega
  have v20 : a 20 = 1761793 := by
    have h : (a 20 : ℤ) = 3 * a 19 - 3 * a 18 + a 17 := a_rec 10
    rw [v19, v18, v17] at h
    omega
  have v21 : a 21 = 2009857 := by
    have h : (a 21 : ℤ) = 3 * a 20 - 3 * a 19 + a 18 := a_rec 11
    rw [v20, v19, v18] at h
    omega
  have v22 : a 22 = 2274305 := by
    have h : (a 22 : ℤ) = 3 * a 21 - 3 * a 20 + a 19 := a_rec 12
    rw [v21, v20, v19] at h
    omega
  have v23 : a 23 = 2555137 := by
    have h : (a 23 : ℤ) = 3 * a 22 - 3 * a 21 + a 20 := a_rec 13
    rw [v22, v21, v20] at h
    omega
  have v24 : a 24 = 2852353 := by
    have h : (a 24 : ℤ) = 3 * a 23 - 3 * a 22 + a 21 := a_rec 14
    rw [v23, v22, v21] at h
    omega
  have v25 : a 25 = 3165953 := by
    have h : (a 25 : ℤ) = 3 * a 24 - 3 * a 23 + a 22 := a_rec 15
    rw [v24, v23, v22] at h
    omega
  have v26 : a 26 = 3495937 := by
    have h : (a 26 : ℤ) = 3 * a 25 - 3 * a 24 + a 23 := a_rec 16
    rw [v25, v24, v23] at h
    omega
  have v27 : a 27 = 3842305 := by
    have h : (a 27 : ℤ) = 3 * a 26 - 3 * a 25 + a 24 := a_rec 17
    rw [v26, v25, v24] at h
    omega
  have v28 : a 28 = 4205057 := by
    have h : (a 28 : ℤ) = 3 * a 27 - 3 * a 26 + a 25 := a_rec 18
    rw [v27, v26, v25] at h
    omega
  have v29 : a 29 = 4584193 := by
    have h : (a 29 : ℤ) = 3 * a 28 - 3 * a 27 + a 26 := a_rec 19
    rw [v28, v27, v26] at h
    omega
  have v30 : a 30 = 4979713 := by
    have h : (a 30 : ℤ) = 3 * a 29 - 3 * a 28 + a 27 := a_rec 20
    rw [v29, v28, v27] at h
    omega
  have v31 : a 31 = 5391617 := by
    have h : (a 31 : ℤ) = 3 * a 30 - 3 * a 29 + a 28 := a_rec 21
    rw [v30, v29, v28] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (3 + 4 * X + 3 * X ^ 2 + 5 * X ^ 3 + 1129 * X ^ 4 + 4917 * X ^ 5 + 6117 * X ^ 6 +
        3476 * X ^ 7 + 730 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252979

theorem OMA.solution : type_of% @OMA.S_oeis_a252979.main :=
  OMA.S_oeis_a252979.conjecture
