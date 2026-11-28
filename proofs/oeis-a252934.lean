import OMAStatements.S_oeis_a252934

namespace OMA.S_oeis_a252934

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 4, max i j.val ≤ v j + 3 ∧ v j ≤ max i j.val + 3) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 4 → ℕ) :
    good n x ↔ (∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i') := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j => h2 i j, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩
  · rintro ⟨hA, hB⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, fun i j => (hA i).2.1 j,
      fun i j j' hj => (hA i).2.2 j j' hj, fun i i' j hi => (hB i i' hi).1 j,
      fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

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
c = min i 3: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 4).all (fun j => decide (∀ h : j.val + 1 < 4,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 3, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 4).all (fun j => decide (∀ h : j.val + 1 < 4,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 4 → Fin 4) : ZA c r = true ↔
    (∀ j : Fin 4, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 4, ∀ h : j.val + 1 < 4,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 4 → Fin 4) : ZB c p r = true ↔
    (∀ j : Fin 4, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 4, ∀ h : j.val + 1 < 4,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 4 → Fin 4) : Fin 4 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 4 → Fin 4) :
    (RA i (vals i r) ∧ ∀ j : Fin 4, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 3) r = true := by
  rw [ZA_iff]
  simp only [RA, vals, step01]
  constructor
  · rintro ⟨⟨-, -, h3⟩, hb⟩
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
    refine ⟨⟨fun j hi hj => ?_, fun j => ?_, fun j j' hj => ?_⟩, fun j => ?_⟩
    · have := hb j
      omega
    · have := (r j).isLt
      have := hb j
      omega
    · have h : j.val + 1 < 4 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
        max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1
      have e := hs j h
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (min i 3) (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 4 → Fin 4) (hp : ∀ j : Fin 4, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 4, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 3) p r = true := by
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

theorem bound_of_ZA {i : ℕ} {r : Fin 4 → Fin 4} (h : ZA (min i 3) r = true) (j : Fin 4) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 4 → Fin 4) : Prop :=
  (∀ i : Fin n, ZA (min i.val 3) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 3) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 4 → ℕ | good n x} =
    (fun z : Fin n → Fin 4 → Fin 4 => fun i => vals i.val (z i)) '' {z | GZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.1
    let z : Fin n → Fin 4 → Fin 4 := fun i j =>
      ⟨max i.val j.val - x i j, by have := hd i j; have := (hw i j).1; omega⟩
    have hv : ∀ i, vals i.val (z i) = x i := fun i => by
      funext j
      simp only [vals, z]
      have := hd i j
      omega
    have hb : ∀ i j, ((z i j : Fin 4) : ℕ) ≤ max i.val j.val := fun i j => by
      simp only [z]
      omega
    rw [good_iff] at hx
    refine ⟨z, ⟨fun i => ?_, fun i i' hi => ?_⟩, funext hv⟩
    · rw [← rowA]
      exact ⟨by rw [hv]; exact hx.1 i, hb i⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      rw [← rowB i.val (z i) (z i') (hb i) (fun j => by rw [← hi]; exact hb i' j), ← e, hv, hv]
      exact hx.2 i i' hi
  · rintro ⟨z, hz, rfl⟩
    rw [good_iff]
    refine ⟨fun i => ((rowA _ _).2 (hz.1 i)).1, fun i i' hi => ?_⟩
    have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
    show RB (vals i.val (z i)) (vals i'.val (z i'))
    rw [e, rowB i.val (z i) (z i') (bound_of_ZA (hz.1 i))
      (fun j => by rw [← hi]; exact bound_of_ZA (hz.1 i') j)]
    exact hz.2 i i' hi

theorem injOn (n : ℕ) :
    Set.InjOn (fun z : Fin n → Fin 4 → Fin 4 => fun i => vals i.val (z i)) {z | GZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1 i) j
  have b' := bound_of_ZA (hz'.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 4 → Fin 4 => GZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 4 → Fin 4) (t : Fin 4 → Fin 4) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 3) t = true ∧ ZB (min m 3) (y (Fin.last m)) t = true := by
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

theorem GZ_one (z : Fin (0 + 1) → Fin 4 → Fin 4) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 4 → Fin 4) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 4 → Fin 4, f z =
      ∑ t : Fin 4 → Fin 4, ∑ y : Fin (m + 1) → Fin 4 → Fin 4, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 4 → Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 4 → Fin 4) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 4 → Fin 4, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 4 → Fin 4, Cnt n r := by
  rw [a_eq, Finset.card_filter]
  unfold Cnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 4 → Fin 4) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 4 → Fin 4)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 4 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 4,
      if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 4 → Fin 4,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 3) r = true ∧ ZB (min m 3) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 4 → Fin 4,
      (if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 4 → Fin 4,
          if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true ∧ GZ (m + 1) y ∧
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
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 3) r = true <;>
      by_cases h3 : ZB (min m 3) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 3 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 3 ≤ m) (r : Fin 4 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 4,
      if (ZA 3 r && ZB 3 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 3 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 4 → Fin 4} (h : ZB c p r = true) (j : Fin 4) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 4 → Fin 4) (e : Fin 4 → Fin 2) : Fin 4 → Fin 4 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 3, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 4 → Fin 4) (e : Fin 4 → Fin 2) : Bool :=
  (List.finRange 4).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 3))

theorem valid_iff (c : ℕ) (r : Fin 4 → Fin 4) (e : Fin 4 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 4, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 3 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 4 → Fin 4) (f : (Fin 4 → Fin 4) → ℕ) :
    ∑ e : Fin 4 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 4 → Fin 4, (if ZB c p r = true then f p else 0) := by
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
def spTerm (c : ℕ) (f : (Fin 4 → Fin 4) → ℕ) (r : Fin 4 → Fin 4) (e : Fin 4 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 4 → Fin 4) :
    Cnt (m + 1) r = if ZA (min (m + 1) 3) r = true then
      ∑ e : Fin 4 → Fin 2, spTerm (min m 3) (Cnt m) r e else 0 := by
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
def code (r : Fin 4 → Fin 4) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 4 + (r 2 : ℕ) * 16 + (r 3 : ℕ) * 64

theorem code_lt (r : Fin 4 → Fin 4) : code r < 4 ^ 4 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem dig_code (r : Fin 4 → Fin 4) : dig 4 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 4 → Fin 4) → ℕ) (r : Fin 4 → Fin 4) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 4), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 4 → Fin 4) :
    Cnt (m + 1) r = if ZA (min (m + 1) 3) r = true then spSum (min m 3) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- The table of Cnt 0: the 19-bit digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 4 → Fin 4) : ℕ :=
  115329714350750538544724396248226326994720707987399900848676764855387680755992401179760796543135689940544713447197599989436638987234747249825492324602371889987555965501940887976552732476063171575822042701744731570407060854652749974251998693692015926165950938699372494993291336095885230180784355353907884651331885831594009202760612443902555159292800284646191298352757821387556156487664329544012731416814033783647222948600385868515727923011839474058598745472483442960531890691815392897357840545133632110351237650448416630882067970756301460274624745362070731006593822987296054631693791081417097593205044284723250683735650493480551100351372425087525849755565215917432708715676779416793582326371290981328885310945656838966841921535740702479345623067132794795805757746793102077045327143780678971637268280054464838235155530963978847772154738211857571310684426859206348614931937170726384170859557577706525517070899697598717160047796979783788334101293795869263543520842332790874496273648645152799493474037325094596387764147639364912073626414268362606122292270369538526451240048153384165415638180869678286450570150581789079825954777271107554168439635007308301490266557245392067330552586750481854435706524708383896957396715838528022397877307026775891224470476120274045837328617072325558090140972013466728324097114113 >>> (19 * code r) % 524288

/-- The table of Cnt 1: the 19-bit digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 4 → Fin 4) : ℕ :=
  60465985277526298352536464260190084527408130549297919216151043692501496368197744029734428498007524607548306723804335303261756581339331166116507719881128353457795742041081584275450879004410208099144587124012341825585577121364180978500631891118399645897694085748816606655042728019039475561023068099789657028077491758874759896896955976988782839355303675636582343430770746243796525011731886333037371588474586004370254117022634378922026305005412709893704718128573838772164677091558823168710607802618417457734179057376390024129767203534149233987271248505398397715185568815172193965176290744761792520424029169291751364635002209918882456882828374011600640115429722755061518529751810449704105704664363859647087617012148583833947849902290189934640374583710152113132401355924974466197132430483451163047085169902101173038672133204169484132883750563222427425627336941967551338722895927989767254042803384188582639907588057926815120493236979908196864306334542502043112733746287999956116824258205739887284873103757008208705894254663713058193074207424983761143412418083414516329828417413360457483691492210933411585343807397731281285128258460128213165094432603859833448387506952514893578708625524943221405582926943310642895353427028858313593129118231249178665082386617773681765357270252173074654845042856733478274868618460135426 >>> (19 * code r) % 524288

/-- The table of Cnt 2: the 19-bit digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 4 → Fin 4) : ℕ :=
  2395304454076484195411567343113141817556927941608863813959920808433575739391795769909063526167943573319750633470997773557985124041567577289636422896964243637755558397550527212383646175596088738957695113012091476797956690902538968109553504034706460582740031888679355588646624348538132118379581922327560207902250773099677090971423857976323378645658478702985915823988123807104123334543773618889177703009751219385641761300061061976704520532343288619111797784074882994216147490914060286441353195494751209607997714820917655308584973628848484143676057515859509094520040611607268705597638940596893152935173481417368045949696728238979818503957813424458213927220641690757872318269838203181335947181497039574838959243846026884645219453241524944475828117462980402319431292188010921222038006756632971415238311002418672804127351102295619796806833811860381471135600131063907751789278047306314956418680659067194742527455859480406945159213913299402205133592946686598333177684243502076711946980211511065432097298794699939702715727158700775802039635828655861458462297051414045120050584601046640272031251999408197026220038171869067306817817485614299166690125605471236803421662389294346545937508163774771406522730071487054358272688030859334656592057506167214628558177924944001057218055730802574731233095216788230544799169530388847308427588198333910809825509381 >>> (19 * code r) % 524288

/-- The table of Cnt 3: the 19-bit digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 4 → Fin 4) : ℕ :=
  3092637317260015224085388292629844042387010909885144134049444156075144109757874552085397363644486239563187722430293989774485242227115982220558797765298867749487790439199837248331366474945663843532804302949398055584625131418449544856263072696690056550455631892293537636513921939212573317431726001733020149969820187938488424369768708733486788296320591365183655265857650362737940117131427163269894830091924716504640913200100064216578376996587844380017738613142813519712641669358408112733668182730159249469293268846726165073912343316397602973606995319509085015875263032102661322748239261158595488720911819748722638978866345915131534081075234941609426750075706513752165461520074365031046059502505305323619343422622690330435427065242882574430804119805471819325658572821063228411522437489665711373226392384046211264584308395832776259380241264387855315135932846264521499074922657398634952294035487053598196825742816004822281281115998234288101686768384116601545355532616384714958929418952461108057089966516510523760290272300390145512592544784229333990590272403779193394576580353184423012655921719563901893290390294776731145749961329614898594253872964746290063344296641204044537001506340093090020502652520624076625140678984919571751423326058190256670267483373627471445120677780880904134496115685134934284156187403873717572912777526419832879572310681902764753890539093836876820870184144949948763927545560951486681356854094666169004529417162314798117731307127181477412880 >>> (19 * code r) % 524288

/-- The table of Cnt 4: the 19-bit digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 4 → Fin 4) : ℕ :=
  213391974890941050461891792191459238924703752782074945249411646769184943573293344093892418091469550529859952847690285294439481713671002773218557045805621874714657540304788770134864286771250805203763496903508465835339134067873018595082152016071613901981438600568254096919460613805667558902789094119578390347917592967755701281514040902610588392446120804197672213344177606444792431165970378613358124952091823065488355825020306666883570607519344200238710903939855932297843599293231072700338089437579128395702729397926606174813583611860849422759762576062409582310678919683279928766768823563855529321864335557317669297105070284491800557194750480139221405961465647353698561436213228733602177623761521067886977938373402207631003931085435756436462521043976341129314243422963132465481003365869029325513683676949811205492674071588903371587291160177251114394820235840481445199954295921928207722061155252731477898683730644583175489844576680188306032357025631504892424356521521450906605060663328465293814665203631730936056609088790713244712866437813834541170457114376932673722674818114066653527179368923103664078255444903978585037384729465052318814650836413035754361740397329869720174839178367997004199568433818345145425236934589681773331955512786683072455154533150160323974613574521791728075885211315643818003750549289023130565509275829137427865310234469143772182657788670838983590615546850379206086445485050570236704298265981106945228810315713353121426191575043526470139920 >>> (19 * code r) % 524288

/-- The table of Cnt 5: the 19-bit digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 4 → Fin 4) : ℕ :=
  3500865443138337233664659547256983455982096349989983159743970784677063132245913992960669815645558423185528501791092796424717294201095291873672559070318318292420178777174215765111106849638491470879134470938718598921795648765684884777289798292653144015115775302076284604533759635188632995332713833961778809765836452746368896386578178286307044351434909425387897760950852534046538530939808549617508744335211823698533513871204493742829936310220572587026824170404754911644140382702753870408878157176971711235309705639445602623766001697486735397927961707323121594383664551865260222325116625570072365355728062184420413939855111122013638625392559923155013351657965504741848355402326987463299630952190100584430796060343711664931063924590914955327228088111042813071629872823255397342347802238267937141954875283974667075831577184676540890918371903238412548452238873997353092450764027855250809688207417341084215563351281693206965450919597741230694526707867800475876308896391880749243405022127748745098585668402435945334416022480912346202611606841555669615574270841127773870161848946053319134060443137533521288979037600879611302134968165042117868499158855179490069218283087762683819350645229879920567608122711748673610141456729080367010737474147010694174208593977636006216051803102092465993021880407370331687944620962865630440553690594794154492577572965958167899534152391346412472115018228466334969122729286318830419094529898264174953555752307220106110841219437343012957454352 >>> (19 * code r) % 524288

/-- The table of Cnt 6: the 19-bit digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 4 → Fin 4) : ℕ :=
  22375230990376210146257784297176921646670023933019017809847728469203667634098222384337849925967857943239663171783177016018400727513184131365742901831937308167544163827610822491677436446231877907959839131838894932154762825812482457035063330960552559142546496740743744800178225230202967951618537622538400785031649059734963750315276607686776913323879478527103745848480038430139577102775986159599679877707721205522843719929778223144783883760594727202400173657775263015028355017777801436641151278008273732698322513296355125161301642801769882075700688598172723956617377102071892663602836646140885787260066722355885440041851292362641570689568323312604960334265249145844024728144420265606905258264863219062824253203100248539491399477300384401700100712677133814447626960055926419759716069978672799230696059213877014880758985008161164177504894402910925114504085466638154536967832753126427521027017823771143545181181392526260116499057016102003027189848351315580664154753947481705151701406001083425826732355463394866708130912594525773195943433253617142024709973087771480563244153760103580540360463013124880770328727837770321989254115858398878320818896464552860187046508850021350801182293131168172653307378683254733875233936644819099384596678687746452923919789750005723218712821470785721627512349954984693423712125988527255811102643318799111020984452708964193963370238734687159213044515082014669594614828959071022189241223715938622320648553851424691718422491366830722342977552 >>> (19 * code r) % 524288

/-- The table of Cnt 7: the 19-bit digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 4 → Fin 4) : ℕ :=
  78036517426421964149346602787928854721551446289131841934469624390244111321520448572770831676841321282897915800083608243979586117116817579371360144011786329922825416152329493287145370262303935763863250976322161136566845941081737365358086113355580196937646959538242835182155792292150862518754742201729297444188472802251878412122373827472072129081057481917679173323385855769660383316085045173265068423201403379467653434850199026525983067149279361081852406133807737437706707950604882372747754391143811662403615446012425156781078429113346992053250509109784724972458428203668948254882154990506072984184279146332483695414696023060349134031556359492098677685428843954696268147018103848001946073810620779049682364443884316913720207017260244799236880766354051909686897815298144292501885230698792419389350776187257410146901220922884903529365763277395287377991485426770985117950328017923198785741985380570408263656487611552592609777570718383296314843322826597490139227815114314188845588777324887864518196326549404833503031629318183526657837820305267003889033784902352085426085953826141937157223490834317992483768798039566735425250056842280328898878620862061378002432676198079076062509700839346642791798627596095814348892113361681659105771657809338025089903403829286693396047859920669878664087227555885830884262216380473038329335221885203916359568987632686269742641264503544052821426230530208102715455130222621025501049113783360878645400994234975103420533980264496865604534288 >>> (19 * code r) % 524288

/-- The table of Cnt 8: the 19-bit digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 4 → Fin 4) : ℕ :=
  195253657025211061172630989855185203616103933795598574903211656793804223369563409845911562553694638734821856855636611044412125768008967537494979696912144015363911649378881724673400822395694486761443599666710246239335307672103812014500169094705526720313016319519952498681306461632185816396052021119414227168344597565496466672585347425888688379088200535840870075209922138954901302723801212244052158199013794000169584764976800659687869686236019954389755398589153787390570899514186241349661148201997981032224265401614286255107675903229440825801593831311676309652518445922258734291164713122720685829370045487452597933074215230727745839835583588996999772270595807398391869220072351964698795452773045241771378500921177849553030575300161285222569937169724616392330428679029716874159575053550540068494281266938310667318407788534845506979106451619039091500748487505606704036853368140716592858056372136746179354190623758543904631629016402261861261964317417694745623040052637123851096939162284224905536635007595869807895768896446017243098226777804586729203676941759569556689244641385959004776949356327625856176652321059936998930316400703737916650792222220019599190190262143666838310776360900890180469551424136564796414988338198957468286629686315117306391435566422800853859253077095966591211179656516481433887095072247416155705011234904390121209077092393276622073375839489001762080207558531615370556698774201760273375329248861535408223105524080780680191647248311390153304178704 >>> (19 * code r) % 524288

/-- The table of Cnt 9: the 19-bit digit at position `code r` is Cnt 9 r. -/
def t9 (r : Fin 4 → Fin 4) : ℕ :=
  399361534689737545931818446392169650725561879826198317462206872206451584325363614534443617759503441573513120160591153781548602784514168132087419231826338689094606842785192583388774347009158409106921618052764619111809397095458645075923819366541677072529987113147541395615952281776337230199911073781790091026052790329060825704141342664881349433068766924760260955445994669951650088552539604016596427518063489422690384398348320853460723845223034815154122751843645178931869574470687537853195267164183430570614142035072573125002935614100597304657834123941157699353312952222358766306594778786873006582459651924561450181445663249244835845259460948183826227734705090688985230753008702729341991358974971368863385760761662168471778964606697828515351079666964506854642999232251560259024772616994313115887167375631240172120314583077735275479923990176905135519520179674381901748113376003963757693727106269402162887043216409045171205649276632184450302925211379392957693687422177098296082111200098126110065597153337756345057891994055278779135596369578107059905646677969681185259794075504231600628815346196597586664398424845235665276082455495170722473431672074988767755624252728658055851592811175132813096245722440748026482853302855393289454276063683204246018151011146146915761315377842223372456934916795864036349332851614974904883845757627602480135314195048797009640968726280682517190514698825909495558379016607363511923343839001248809370990596524895849358208250038398035613974544 >>> (19 * code r) % 524288

/-- The table of Cnt 10: the 19-bit digit at position `code r` is Cnt 10 r. -/
def t10 (r : Fin 4 → Fin 4) : ℕ :=
  715695035322995463142616473292105878445159677754710170357588317154753774736057570969050572497243361073473339537096204819621600270956953489499496420047698675718714975649187136171596498265450581006518038984246748625338363287726175221091544020395316196849891876882678186304415301250634504546732599595053790085865818072537052679227504806394779060746214933139436317969509230725694494028915337135533354693269086002091799023003497338674825648312542251402968066717113678119851377582274431369164045731312809006027115001357920471328699110677362349959074855735539115431357469068486559835316619727051317503095384636504262468954294412491623307460999373409096027722695645038530755551528694255576071756239233921961177242092018595684321835217564197521232118002249402888889389155964590541389464999490508930909688946430249310277657499785246509985015409700056217471051649904333168706166774490121841248511115955642064932473892138601367355434233972597815872098383966477736929265879395425127977463529985623039288631518510031000160950202223219991388432659452358737931950227842944262044808115245636541942098747144782298762426237341817287234177529268977827263668941963530127704039633994926146990569589521408568081561476644731850961817699029735885135816089391718793159684471614923590255221667004987735589498288353126172188097712508767582811553865306085747704085723657309191130814687468208548353473851152763500160529113150305487256355094253287680406284664703375038246662939976407962705985552 >>> (19 * code r) % 524288

lemma Cnt0 (r : Fin 4 → Fin 4) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA 0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then 1 else 0) = t0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt1 (r : Fin 4 → Fin 4) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 1 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 0 3) t0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t1 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt2 (r : Fin 4 → Fin 4) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 2 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 1 3) t1 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t2 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt3 (r : Fin 4 → Fin 4) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 3 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 2 3) t2 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t3 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt4 (r : Fin 4 → Fin 4) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 4 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 3 3) t3 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t4 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt5 (r : Fin 4 → Fin 4) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 5 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 4 3) t4 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t5 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt6 (r : Fin 4 → Fin 4) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 6 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 5 3) t5 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t6 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt7 (r : Fin 4 → Fin 4) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 7 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 6 3) t6 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t7 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt8 (r : Fin 4 → Fin 4) : Cnt 8 r = t8 r := by
  have hf : Cnt 7 = t7 := funext Cnt7
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 8 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 7 3) t7 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt9 (r : Fin 4 → Fin 4) : Cnt 9 r = t9 r := by
  have hf : Cnt 8 = t8 := funext Cnt8
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 9 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 8 3) t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

lemma Cnt10 (r : Fin 4 → Fin 4) : Cnt 10 r = t10 r := by
  have hf : Cnt 9 = t9 := funext Cnt9
  have h : ∀ c0 c1 c2 c3 : Fin 4,
      (if ZA (min 10 3) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) = true then spSum (min 9 3) t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) else 0) =
        t10 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3)

/-- The difference equation of order 4 on every deficit row, from m = 6 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 4 → Fin 4, (Cnt (m + 10) r : ℤ) = 4 * Cnt (m + 9) r - 6 * Cnt (m + 8) r + 4 * Cnt (m + 7) r - Cnt (m + 6) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt6, Cnt7, Cnt8, Cnt9, Cnt10]
    have h : ∀ c0 c1 c2 c3 : Fin 4,
        (t10 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) : ℤ) = 4 * t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) - 6 * t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) + 4 * t7 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) - t6 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64)) := by
      decide +kernel
    rw [← dig_code r]
    exact h (r 0) (r 1) (r 2) (r 3)
  | succ m ih =>
    intro r
    rw [show m + 1 + 10 = m + 10 + 1 by omega, show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega, show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega,
      Cnt_hom (m + 10) (by omega), Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega), Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 11. -/
theorem a_rec (m : ℕ) : (a (m + 10 + 1) : ℤ) = 4 * a (m + 9 + 1) - 6 * a (m + 8 + 1) + 4 * a (m + 7 + 1) - a (m + 6 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => Cnt_rec m r)

lemma v1 : a 1 = 8 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 34 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 153 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 711 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 3067 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 10920 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 30818 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

lemma v8 : a 8 = 70640 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt7]
  decide +kernel

lemma v9 : a 9 = 138558 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt8]
  decide +kernel

lemma v10 : a 10 = 242764 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
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
    X * (8 + 2 * X + 65 * X ^ 2 + 271 * X ^ 3 + 1013 * X ^ 4 + 2340 * X ^ 5 + 2849 * X ^ 6 +
        1331 * X ^ 7 + 293 * X ^ 8 + 20 * X ^ 9) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 4 = A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (8 + 2 * X + 65 * X ^ 2 + 271 * X ^ 3 + 1013 * X ^ 4 + 2340 * X ^ 5 + 2849 * X ^ 6 +
        1331 * X ^ 7 + 293 * X ^ 8 + 20 * X ^ 9) : ℤ⟦X⟧) =
      X ^ 1 * C 8 + X ^ 2 * C 2 + X ^ 3 * C 65 + X ^ 4 * C 271 + X ^ 5 * C 1013 + X ^ 6 * C 2340 + X ^ 7 * C 2849 + X ^ 8 * C 1331 + X ^ 9 * C 293 + X ^ 10 * C 20 := by
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

/-- Controls: the entry's data a(1..30). -/
theorem controls : a 1 = 8 ∧ a 2 = 34 ∧ a 3 = 153 ∧ a 4 = 711 ∧ a 5 = 3067 ∧ a 6 = 10920 ∧
    a 7 = 30818 ∧ a 8 = 70640 ∧ a 9 = 138558 ∧ a 10 = 242764 ∧ a 11 = 391450 ∧ a 12 = 592808 ∧
    a 13 = 855030 ∧ a 14 = 1186308 ∧ a 15 = 1594834 ∧ a 16 = 2088800 ∧ a 17 = 2676398 ∧
    a 18 = 3365820 ∧ a 19 = 4165258 ∧ a 20 = 5082904 ∧ a 21 = 6126950 ∧ a 22 = 7305588 ∧
    a 23 = 8627010 ∧ a 24 = 10099408 ∧ a 25 = 11730974 ∧ a 26 = 13529900 ∧ a 27 = 15504378 ∧
    a 28 = 17662600 ∧ a 29 = 20012758 ∧ a 30 = 22563044 := by
  have v11 : a 11 = 391450 := by
    have h : (a 11 : ℤ) = 4 * a 10 - 6 * a 9 + 4 * a 8 - a 7 := a_rec 0
    rw [v10, v9, v8, v7] at h
    omega
  have v12 : a 12 = 592808 := by
    have h : (a 12 : ℤ) = 4 * a 11 - 6 * a 10 + 4 * a 9 - a 8 := a_rec 1
    rw [v11, v10, v9, v8] at h
    omega
  have v13 : a 13 = 855030 := by
    have h : (a 13 : ℤ) = 4 * a 12 - 6 * a 11 + 4 * a 10 - a 9 := a_rec 2
    rw [v12, v11, v10, v9] at h
    omega
  have v14 : a 14 = 1186308 := by
    have h : (a 14 : ℤ) = 4 * a 13 - 6 * a 12 + 4 * a 11 - a 10 := a_rec 3
    rw [v13, v12, v11, v10] at h
    omega
  have v15 : a 15 = 1594834 := by
    have h : (a 15 : ℤ) = 4 * a 14 - 6 * a 13 + 4 * a 12 - a 11 := a_rec 4
    rw [v14, v13, v12, v11] at h
    omega
  have v16 : a 16 = 2088800 := by
    have h : (a 16 : ℤ) = 4 * a 15 - 6 * a 14 + 4 * a 13 - a 12 := a_rec 5
    rw [v15, v14, v13, v12] at h
    omega
  have v17 : a 17 = 2676398 := by
    have h : (a 17 : ℤ) = 4 * a 16 - 6 * a 15 + 4 * a 14 - a 13 := a_rec 6
    rw [v16, v15, v14, v13] at h
    omega
  have v18 : a 18 = 3365820 := by
    have h : (a 18 : ℤ) = 4 * a 17 - 6 * a 16 + 4 * a 15 - a 14 := a_rec 7
    rw [v17, v16, v15, v14] at h
    omega
  have v19 : a 19 = 4165258 := by
    have h : (a 19 : ℤ) = 4 * a 18 - 6 * a 17 + 4 * a 16 - a 15 := a_rec 8
    rw [v18, v17, v16, v15] at h
    omega
  have v20 : a 20 = 5082904 := by
    have h : (a 20 : ℤ) = 4 * a 19 - 6 * a 18 + 4 * a 17 - a 16 := a_rec 9
    rw [v19, v18, v17, v16] at h
    omega
  have v21 : a 21 = 6126950 := by
    have h : (a 21 : ℤ) = 4 * a 20 - 6 * a 19 + 4 * a 18 - a 17 := a_rec 10
    rw [v20, v19, v18, v17] at h
    omega
  have v22 : a 22 = 7305588 := by
    have h : (a 22 : ℤ) = 4 * a 21 - 6 * a 20 + 4 * a 19 - a 18 := a_rec 11
    rw [v21, v20, v19, v18] at h
    omega
  have v23 : a 23 = 8627010 := by
    have h : (a 23 : ℤ) = 4 * a 22 - 6 * a 21 + 4 * a 20 - a 19 := a_rec 12
    rw [v22, v21, v20, v19] at h
    omega
  have v24 : a 24 = 10099408 := by
    have h : (a 24 : ℤ) = 4 * a 23 - 6 * a 22 + 4 * a 21 - a 20 := a_rec 13
    rw [v23, v22, v21, v20] at h
    omega
  have v25 : a 25 = 11730974 := by
    have h : (a 25 : ℤ) = 4 * a 24 - 6 * a 23 + 4 * a 22 - a 21 := a_rec 14
    rw [v24, v23, v22, v21] at h
    omega
  have v26 : a 26 = 13529900 := by
    have h : (a 26 : ℤ) = 4 * a 25 - 6 * a 24 + 4 * a 23 - a 22 := a_rec 15
    rw [v25, v24, v23, v22] at h
    omega
  have v27 : a 27 = 15504378 := by
    have h : (a 27 : ℤ) = 4 * a 26 - 6 * a 25 + 4 * a 24 - a 23 := a_rec 16
    rw [v26, v25, v24, v23] at h
    omega
  have v28 : a 28 = 17662600 := by
    have h : (a 28 : ℤ) = 4 * a 27 - 6 * a 26 + 4 * a 25 - a 24 := a_rec 17
    rw [v27, v26, v25, v24] at h
    omega
  have v29 : a 29 = 20012758 := by
    have h : (a 29 : ℤ) = 4 * a 28 - 6 * a 27 + 4 * a 26 - a 25 := a_rec 18
    rw [v28, v27, v26, v25] at h
    omega
  have v30 : a 30 = 22563044 := by
    have h : (a 30 : ℤ) = 4 * a 29 - 6 * a 28 + 4 * a 27 - a 26 := a_rec 19
    rw [v29, v28, v27, v26] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (8 + 2 * X + 65 * X ^ 2 + 271 * X ^ 3 + 1013 * X ^ 4 + 2340 * X ^ 5 + 2849 * X ^ 6 +
        1331 * X ^ 7 + 293 * X ^ 8 + 20 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252934

theorem OMA.solution : type_of% @OMA.S_oeis_a252934.main :=
  OMA.S_oeis_a252934.conjecture
