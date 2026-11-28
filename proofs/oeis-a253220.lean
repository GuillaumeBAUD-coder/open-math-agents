import OMAStatements.S_oeis_a253220

namespace OMA.S_oeis_a253220

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 5 → ℕ) : Prop :=
  (∀ j : Fin 5, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 5, max i j.val ≤ v j + 2 ∧ v j ≤ max i j.val + 2) ∧
  (∀ j j' : Fin 5, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 5 → ℕ) : Prop :=
  (∀ j : Fin 5, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 5, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 5 → ℕ) :
    good n x ↔ ((∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i')) ∧
      ∀ i j, i.val + 1 = n → j.val + 1 = 5 → x i j + 2 = max i.val j.val := by
  constructor
  · rintro ⟨h1, h6, h2, h3, h4, h5⟩
    exact ⟨⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j => h2 i j, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩, h6⟩
  · rintro ⟨⟨hA, hB⟩, h6⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, h6, fun i j => (hA i).2.1 j,
      fun i j j' hj => (hA i).2.2 j j' hj, fun i i' j hi => (hB i i' hi).1 j,
      fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 5 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 5), i.val + j.val = s → x i j ≤ max i.val j.val := by
  obtain ⟨h1, -, -, h3, h4, h5⟩ := h
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
c = min i 4: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 5 → Fin 3) : Bool :=
  (List.finRange 5).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 5).all (fun j => decide (∀ h : j.val + 1 < 5,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 4, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 5 → Fin 3) : Bool :=
  (List.finRange 5).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 5).all (fun j => decide (∀ h : j.val + 1 < 5,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 5 → Fin 3) : ZA c r = true ↔
    (∀ j : Fin 5, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 5, ∀ h : j.val + 1 < 5,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 5 → Fin 3) : ZB c p r = true ↔
    (∀ j : Fin 5, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 5, ∀ h : j.val + 1 < 5,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 5 → Fin 3) : Fin 5 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 5 → Fin 3) :
    (RA i (vals i r) ∧ ∀ j : Fin 5, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 4) r = true := by
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
    · have h : j.val + 1 < 5 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
        max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1
      have e := hs j h
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (min i 4) (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 5 → Fin 3) (hp : ∀ j : Fin 5, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 5, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 4) p r = true := by
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
    · have h : j.val + 1 < 5 := by have := j'.isLt; omega
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

theorem bound_of_ZA {i : ℕ} {r : Fin 5 → Fin 3} (h : ZA (min i 4) r = true) (j : Fin 5) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 5 → Fin 3) : Prop :=
  (∀ i : Fin n, ZA (min i.val 4) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 4) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

/-- The lower right deficit is 2. -/
def LZ (n : ℕ) (z : Fin n → Fin 5 → Fin 3) : Prop :=
  ∀ i j, i.val + 1 = n → j.val + 1 = 5 → (z i j : ℕ) = 2

instance (n : ℕ) : DecidablePred (LZ n) := fun z => by unfold LZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 5 → ℕ | good n x} =
    (fun z : Fin n → Fin 5 → Fin 3 => fun i => vals i.val (z i)) '' {z | GZ n z ∧ LZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.2.1
    have hq := hx.2.1
    let z : Fin n → Fin 5 → Fin 3 := fun i j =>
      ⟨max i.val j.val - x i j, by have := hd i j; have := (hw i j).1; omega⟩
    have hv : ∀ i, vals i.val (z i) = x i := fun i => by
      funext j
      simp only [vals, z]
      have := hd i j
      omega
    have hb : ∀ i j, ((z i j : Fin 3) : ℕ) ≤ max i.val j.val := fun i j => by
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
    Set.InjOn (fun z : Fin n → Fin 5 → Fin 3 => fun i => vals i.val (z i)) {z | GZ n z ∧ LZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1.1 i) j
  have b' := bound_of_ZA (hz'.1.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 5 → Fin 3 => GZ n z ∧ LZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 5 → Fin 3) (t : Fin 5 → Fin 3) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 4) t = true ∧ ZB (min m 4) (y (Fin.last m)) t = true := by
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

theorem GZ_one (z : Fin (0 + 1) → Fin 5 → Fin 3) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 5 → Fin 3) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 5 → Fin 3, f z =
      ∑ t : Fin 5 → Fin 3, ∑ y : Fin (m + 1) → Fin 5 → Fin 3, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 5 → Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 5 → Fin 3) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 5 → Fin 3, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem LZ_iff (n : ℕ) (z : Fin (n + 1) → Fin 5 → Fin 3) :
    LZ (n + 1) z ↔ (z (Fin.last n) 4 : ℕ) = 2 := by
  constructor
  · intro h
    exact h _ _ (by simp) rfl
  · intro h i j hi hj
    have e1 : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    have e2 : j = 4 := Fin.ext (by have : ((4 : Fin 5) : ℕ) = 4 := rfl; omega)
    rw [e1, e2]
    exact h

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 5 → Fin 3,
    if (r 4 : ℕ) = 2 then Cnt n r else 0 := by
  rw [a_eq, Finset.card_filter]
  simp only [LZ_iff]
  have h : ∀ r : Fin 5 → Fin 3, (if (r 4 : ℕ) = 2 then Cnt n r else 0) =
      ∑ z : Fin (n + 1) → Fin 5 → Fin 3,
        if (r 4 : ℕ) = 2 ∧ GZ (n + 1) z ∧ z (Fin.last n) = r then 1 else 0 := by
    intro r
    unfold Cnt
    by_cases hr : (r 4 : ℕ) = 2
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
  · by_cases h1 : GZ (n + 1) z <;> by_cases h2 : (z (Fin.last n) 4 : ℕ) = 2 <;> simp [h1, h2]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 5 → Fin 3) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 5 → Fin 3)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 5 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 5 → Fin 3,
      if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 5 → Fin 3,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 4) r = true ∧ ZB (min m 4) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 5 → Fin 3,
      (if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 5 → Fin 3,
          if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true ∧ GZ (m + 1) y ∧
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
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 4) r = true <;>
      by_cases h3 : ZB (min m 4) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 4 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 4 ≤ m) (r : Fin 5 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 5 → Fin 3,
      if (ZA 4 r && ZB 4 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 4 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 5 → Fin 3} (h : ZB c p r = true) (j : Fin 5) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 5 → Fin 3) (e : Fin 5 → Fin 2) : Fin 5 → Fin 3 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 2, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 5 → Fin 3) (e : Fin 5 → Fin 2) : Bool :=
  (List.finRange 5).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 2))

theorem valid_iff (c : ℕ) (r : Fin 5 → Fin 3) (e : Fin 5 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 5, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 2 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 5 → Fin 3) (f : (Fin 5 → Fin 3) → ℕ) :
    ∑ e : Fin 5 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 5 → Fin 3, (if ZB c p r = true then f p else 0) := by
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
    let e : Fin 5 → Fin 2 := fun j =>
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
def spTerm (c : ℕ) (f : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) (e : Fin 5 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 5 → Fin 3) :
    Cnt (m + 1) r = if ZA (min (m + 1) 4) r = true then
      ∑ e : Fin 5 → Fin 2, spTerm (min m 4) (Cnt m) r e else 0 := by
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
def dig (b : ℕ) (hb : 0 < b) (n : ℕ) : Fin 5 → Fin b := fun j => ⟨n / b ^ j.val % b, Nat.mod_lt _ hb⟩

theorem sum_dig (b : ℕ) (hb : 0 < b) (g : (Fin 5 → Fin b) → ℕ) :
    ∑ f, g f = ∑ n ∈ Finset.range (b ^ 5), g (dig b hb n) := by
  rw [← (finFunctionFinEquiv (m := b) (n := 5)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun n => g (dig b hb n)) _

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 5 → Fin 3) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 3 + (r 2 : ℕ) * 9 + (r 3 : ℕ) * 27 + (r 4 : ℕ) * 81

theorem code_lt (r : Fin 5 → Fin 3) : code r < 3 ^ 5 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  have := (r 4).isLt
  omega

theorem dig_code (r : Fin 5 → Fin 3) : dig 3 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  have := (r 4).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 5), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 5 → Fin 3) :
    Cnt (m + 1) r = if ZA (min (m + 1) 4) r = true then spSum (min m 4) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- The table of Cnt 0: the 20-bit digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 5 → Fin 3) : ℕ :=
  76239396050438033967409310949326430898491119863282755063938239924460065488241842930566627098688506280058749588445770736549072402138615880862218472599399871201359765594652808942633131179403310637672771324673035057713593271780214568480278817937012297292972400868647804134992142565224891144456760825321230432243867466376464879332700611390497953679615641526022740842401784113599280561069530983825201522623832037213265061775136908726090990486198815861932035252456322463734235624356510486977601139931726303989697983405345017896184488503881813896058801206079615669943660751163208887172243611474751697487973748998941352455952957811159991050240197558998979786822213890312342398176986478568287639590829044575641930726302329141012721801212510116994230725734955673481823840397405582029990773533043919180375856172541770023872595217216264959713785636761960026873059789298016117075071268804193606805427617010142945926324131297576870169466444035518959542115667351510277167263014143984915924568164393073289585843227514245523900294327422267219994190465578278802035022286135397325161352955932560551754208373571296316840019031799418783336982904014251693865645778384076864999013789863424544503288594458988048639528336223023608650573799165282095779663499876080619912748138427771566930440124752484719921487747592796544102148915811105835761334261836751512178514833082544209787436380311467542826600493680402315315526386718539269783767367935242859970561 >>> (20 * code r) % 1048576

/-- The table of Cnt 1: the 20-bit digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 5 → Fin 3) : ℕ :=
  79942800952984111905410185638000911605816224501761578226089215491313030708078319407382150324596840699711071051164393079256439844884134133378461654403944397142470607755269511579037936703999500233645550524581751965035154997410512214966758328649710121190192091942905069063728250357312218772480424621542561116162503806089255591985814370909313606891615838196941942026678273240037497820777849185837413955108142925496426197314726811891870684391836687464446856910743765697311002907540722007696056251196382940503395666215136419710595494382803370649111566800996572487943562380944358137924805411104022346759094722508924864516570203579438619652798122101899424037994619049939736440036365295118415767674427028438298822267937697600272727907646023358754348536630280447342961114819479455143413640469782512084030919368677152606053986482183715091585499357022766172434801784246670240523495418636975926702382673929826268939024823534527366142960015150153301037976135965256786503123204259666061745607660733516116238006169932015530157655198151292016552373802364900645416699670563409071587900323675681735994269754640018353586319882757573008794567833373506277387218407132032492371456258204956524888624528212253545403438922245095575723541019561683362832639519306147525665742694872424701805460244200716811550159328948475283045264209353580490714402271050680579315216189802097260982497685035920409541876348539074584723711443963061168817303189592619647411186302978 >>> (20 * code r) % 1048576

/-- The table of Cnt 2: the 20-bit digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 5 → Fin 3) : ℕ :=
  96644916164375475752668384144682626324594090933910754378236380854370888967966434422557293356475433232089921498990294771451072453397285371475180210385059361858864032400173609641774655158034529802768900414594087932545757287349331249232182753827204948011365461724246107210036611963140008174264220204904615319071191053370640969929302641838559113123927064145192156852524679488738748805416277679822677055429408115645141904901949177898987106593293221093414100253303319839532242467120761968640671997844491451666167419111824186336680585122448438699232094527411376982551146823457522155046234356927983863925827908808655259843705047445461956974569176260698772243887325704461922251419607898878604680146896204389843329636402846579936475259497485193304379040663243498343251053355494594663479713691624145221856417128438755772670471552000187702238212270296538857192716131813653898861467177077335321646352752644591783200695492471692166533490051419776340953380856972109770579110647809362042638386909427121951389173360929826597679057199484286637409078323657897451934321627735010870060844489199748121309982485284505072460205349267736637397621783533920894925327770800231874882949470731861769076140496924739562002621167951820272500419158058508914977114119400784768896091265455159417410391162648866070846485838995735359606198942066217316415098721669277812030645216708711487417385602670412088964487749036120803188610947488865851919660775532554527047651202074307924010751091259998213 >>> (20 * code r) % 1048576

/-- The table of Cnt 3: the 20-bit digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 5 → Fin 3) : ℕ :=
  1836253407123134039300699298748969900167287727744304329591857467669616815168738015300704684663913704740642710192987056428600612572350114443456786173146202726258376942741776226007569108529284416145264632989525229476970781575222214088781897481284510335396134321496367389133918523066709330225524979798910763000501507040551380873078239773509866639369519282796129646541757237987341215261260531717268967463310340511027896189592271017153017101383070183691314277728425381625364144934978412389378326135688760426535724589035317114531631376538297085631005439934610114618907426910333247758353030618069768997190824077658360209308380025889189735795858694761975410078149719735470584003181619460081811546418039930920320719774343150160595348621923652572696213325269509797223875538093018607393283276243390739715135472691335810369773841215359092611270349080398122237835209198487235265213564507926297009462333296835978124290393990079032185317278980832769640369763972867650347831725181323776577858656862536476561422630094030183481849522473448503766663829779144117852110075254019765400044737393099300476100820745653251195970374772321529622692061305063574778191001664039733385974519543243586864367886880247664174079417700133481343503175511908243767735363467908579503229567896594017475597122698644008692343645743409568396425031982933961447421427733514700582782464236126273448154353410065935646275507810069182099462019302818525105817021513712025724480064826782934156856157979341225999 >>> (20 * code r) % 1048576

/-- The table of Cnt 4: the 20-bit digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 5 → Fin 3) : ℕ :=
  25900837532052627501715126950774943854991216370288082122664094807129331919222199373715202920522572256341697175353712164361313903652096351097179931284378017401960244928298636954775194227669934689587236037201208715521235475629514938171203233834779223610065917097958377705804096240905301533490705264514043755997244073984840554096812935642951851981684952683413112851557729976009818514758496325539810897301421444536392640664603087854442855553415323453932361677989628996317431626359545677940882937129097182431712059445231245316562999707747246306882839959945185686853611844547277576000659417414323581236610976268473086566027547087036546116789282309939899727836884957981793014701575554230830372500935314603617468678366050208887386817553682714852373679901356556574374282366344026191086563298824219078671679512924212602851726406384619084138598463533398127358394090566067611760344780169153620925446975059448160410674074058989841256073304538145311549806711214575267818370668464469605623724592950140071256589211014067680267404299827539389964688068817583270912798734113116591355354569538319219254799734184400570179764724505351713677156213130973088280785280703016122220578816915827419410622783594084795799487894790560886156407059108334890582563216982445120060878741758784541833726500160394159054789664543434223649167791445130839624685568423870308905584471717985440854497089429637435500195151802614433161771409485639763187928379014587228468203026175078365401196532713775956018 >>> (20 * code r) % 1048576

/-- The table of Cnt 5: the 20-bit digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 5 → Fin 3) : ℕ :=
  344829060874491697485520794628227610726151716452193570946513023402378568238003012557521806046360215711295431050977779859855104508323432017592305950830823754067888633970781853188947361956441518553907679778857883197685702153157124251473332605680941305375802955990729446471302296222201924893637449193231746721634950955141459317229211023783776895039745937217977562143126793113444150972605652572858377916311461619797943813027253050241239211248454754043398009205473866637539537473324100667511445967091835261136044936081033061227690331079837771088954253674443569784303346561929390530933166956707932399202113991196094221932987897233251298388355458609381229005763058131778014275094216368960660938988250898741317055142846155805723752459420734245694602857787471390778108308560520335505313558926104041032785010280437623649994336920621130943087286287035262876754282951200492348381915820344709658693437488860322667415992032071124502259462077201312627607134547655115042660194558850427565107159126271074658756244023031328301175299931467203518724841537034108792336917942443220221687545497155531108574316752494702380449127041147613608097146638514151347305698045579003475472845559789186632430914979833464730145747710983275221043387489504022123540582322137845338871456883214072165816106627485826699786527475698314942778433048052459602103203029974095347353180111056056673339333316498583136788900920720352204292102638741191100099623556131795476631469499878054784729495437801242492978 >>> (20 * code r) % 1048576

/-- The table of Cnt 6: the 20-bit digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 5 → Fin 3) : ℕ :=
  1549024716282610125363768861070973134730594089488721568142015341674137805974975416275773404515432045241211650472273502128295295700506717594722387830694070384024697036234218481757973183138409377629493355239779751090949112699215915779880766536954632074709464624052525663688910651303097660368615761118026467616133686633690389556207901986885195087919576200036363331286445134535393175949810369797582421872937249675482467330493501090041082420933361210147865272294096169973790276519741784052374827511682956465702844481450668799153357015090342063474360024989053259553742128367974968141607178482067727304883381127275863518387444185505659024130246800344098226391465459203976554835187134793878533742484516126348246865607725121991339581605265345657998632196807095539201708123110378724048163037757859448832635691671210603471034879089920908628506722225140222335804377212126285767629883446962190283845216042988758179638931916060410318067031103441741646838916766416369331025995593380101134446391455728090457426227838223329028428056025467958182877916756028469785892632194853966353537717040470708946045229500271113243005553721354669422986482907648785949258571511489779886095569362280382778815617991849601596575306343172410912390952189323440465816399796018116782309241547784593536743308789054698030954736879899424431503758785441749518229047501731853306441777944706414545589364113598212716144236469428048684931473087868573623734909819550741662073372136091841799422908666585062309938 >>> (20 * code r) % 1048576

/-- The table of Cnt 7: the 20-bit digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 5 → Fin 3) : ℕ :=
  3888798136622140393335870441213739518049017030998700927058797936004739021513667382087881847447713665860735861723442798767054286772959152893463903265002995015746553490391345349948672631839488179252280610689933717519192063687986649560197297474044202983663553627565855231813974718438610160838055964304164524827675772570903038118461040688063793358354623604758122518361865443189115960436016325175637727185129089870355847295008578541369670230441514123654217795518457804305301543960654473839497006571259132936583233850409994516656470688290157502701020998967786189473853413396553684046244789413960398153425969488407589438813859302931909339106554924673893677184396569598354563238634384492469335462061038210918541363175476660171462387719611972154987712689086589887132564514149344166530972842935488147149228828049564131353736660423945811572783888578516790737263828926659735780300345124731396446760308991497060094581314475567480764269461952727891881065474301781849837988490715165935715570881012383329711918583105255999808836935361910900702332742555005205228580382533044256610778180632868335184275603470478262655073769771752106615256500986572523744484827370514476441996679121936254734637934997999153862606449766347089996129202860114061981179526473162712379834434858232863051717187323917551158821062680379018991833821499882307380793172594209233676051309218347279498414945135756342233754451101148326900129083426648767451873699526629505505740839323422834533492714438604345049138 >>> (20 * code r) % 1048576

/-- The table of Cnt 8: the 20-bit digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 5 → Fin 3) : ℕ :=
  7447747174375267287927883687341677232452194429639964450070384843738088454070971456479905532329220096233060482926429554187223631929632466808216332255850832668086799831751783058380002958085552899192765562443420698672436453203124289851818786600782057123367573766119277840083511450048079298788784402235991619285132910721991670225233937535271636452479804136723375804774602034109121806726992546026397190965445674553388156968419058803458693199674795042277573089518338728892575497843827121564022991235967567099012363112776506312632358379412291081913472824295164297318536360531483999996624333715049480678951446730370001578130118407516201187965356258853689206657034797990800320917603299437469562150368917421611276405510767009167712651520564248162223404834327352224563000715440543579019757372400152296645119918616150904144360493716935301092009244789592780037151538540422347653636226481956116062096509657079485377845473019519015144662398888499566761217946802683711166802456670416732667324460228960233286875755050445725068671801627465335395837798981988352210097014193370544048019105823623650114777192600125683585244639627128132599029221476682568297882493186058133205623968090923518541678624951669420104699260528866508861755998727833194380058382892387049193157428968125068505214881612768083082196121187198252566999498774091227306101159983592623080257828188281632927412639183807170254692475501243330120805616610148877636081583029498206934082744440284675311475501176469950824498 >>> (20 * code r) % 1048576

/-- The table of Cnt 9: the 20-bit digit at position `code r` is Cnt 9 r. -/
def t9 (r : Fin 5 → Fin 3) : ℕ :=
  12242301465289934640017762224759382324415307280871276965388913736953335306729976348009798132654312669505864948856644705209480284019858212994526393416365733575964589947023780742433724546274752376619716233359659371720975602255289349861794131490869360419245820584140602907191501056433571869969657119297714420535219770835379505630990988793655372933119320937559661359124523616608551271343294794944419648484563278521486809592937563238006865080290221148805873324014851768098947822409860931573900355286009378034452212809304153321658728728150811301072096561347760037169320141981745860560079314481692607335739448426086602894272042886259704622463116859260085533075355337163422199599170192642323317883902201069040392602179780557363795988999760787619981488533385522359602207699822685761053014568436473607901487891743773603479366023637469655357488804588672555205988283880659257946905974235911891307445983969496857556036002767548338426594450746679630329368094508246760884572196894868985325128869425657158230666193110817616926454656747310590225039005320194228932874986511338035426919372429725998821551747139554178433062060369653792033267977782434873202581905918627560609856110888980316175341084064711577805515479554895746292437058228132927480507898284121336082768662878880747442071720757205955497289885162023747987293461504306108267247762079480356699824206479031667818010907964755877080497961679028416230219862083664914098072851310977641472016972291343013633765912846398660804658 >>> (20 * code r) % 1048576

/-- The table of Cnt 10: the 20-bit digit at position `code r` is Cnt 10 r. -/
def t10 (r : Fin 5 → Fin 3) : ℕ :=
  18273910683108608081741796079229025033333224496056647134327220292598639803292131060373849678437199738603944503758977452141531033000930352069059973683000181583637496237975713325819992724442217391459788625455657267003364803874834227814274705459632686335306320159079343028905059438504093768123220237052645281773234706124162710784655523545433824732287074284469409019817500959156210873977913286276283820501659220139084812219347558435752307673904588077014525161042212759368242254503514833664536237578856302663928666752444823029017205959240206585518975607839331429193713394355714534314172368690146391201623454948230061067115839136487786043182114586449586529656710603487137965277882501552476778882222338311951593668315655532042128363622234809677925594897271797585695110045577684109687203329921885219044567005701639746419639875515635892103292131431834265762768777816432811523204183047345594079989216929556127696122361399609645282544205946986277607107073013888452110933522138247223156694959239129531589923170964478335520042203139219156503755046938221489298584321634837309377785413678251063801631316500716795127516587867772848519719041334236050024858053834851480460620775262887617012643087090548042619610709132016116991218298331301924599770864755931266997513374113792244395867273063143495302289897139414376079567796579164394780888272927553371852858751667328513518900318817102542945668669520535301169382921564736913024039219728521446968371763426308936255175198094816148717618 >>> (20 * code r) % 1048576

/-- The table of Cnt 11: the 20-bit digit at position `code r` is Cnt 11 r. -/
def t11 (r : Fin 5 → Fin 3) : ℕ :=
  25542574827831287613099985250750605359205946075196074956885304510674001943757435593572060169677881303527299147633427794983375878872848884031817073055754176691105518704607580808538807492587947943712982738731414384519604058061758923709260508507072034871549072490935498205224186596259644993249473755500784202999177716588341285686227541790606991849983064177452618786853534061752100614630848020021989707016733499406182164847649044396695020980517895826903528600600421702700458794124788827835930638114508340987441724942198515434707790072680476935254109963769878473391716117653390021258903496340410832276603466296800376096661507158200445450122349440422192196401100596961947617953740226167929945145329329150344879603918391933202709775387986314336055723925986177902841707752705538624922323656856387130074357260489749332965182049351434011329419225319077911707493020347743008382530852916257224379726208537257295798104548915702935712511664489419508594434882319608784845886432400551446162022729669377353364646688611427880849434440803191034231985923836070133307225019563868365900617229569198845055015900683613533668608222121485302058382412132086098764710936934729892757917961212645421053584634029178814546984949260227620958099719037340185737847282307816841937391562672859559366601538530580702497196157119370136843822503998666086847022692527811668539361463753172170030080871740847167850204599025763984938294795053364874413980688282129623423147117845182443175703356921722414563378 >>> (20 * code r) % 1048576

lemma Cnt0 (r : Fin 5 → Fin 3) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA 0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then 1 else 0) = t0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt1 (r : Fin 5 → Fin 3) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 1 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 0 4) t0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t1 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt2 (r : Fin 5 → Fin 3) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 2 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 1 4) t1 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t2 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt3 (r : Fin 5 → Fin 3) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 3 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 2 4) t2 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t3 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt4 (r : Fin 5 → Fin 3) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 4 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 3 4) t3 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t4 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt5 (r : Fin 5 → Fin 3) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 5 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 4 4) t4 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t5 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt6 (r : Fin 5 → Fin 3) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 6 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 5 4) t5 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t6 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt7 (r : Fin 5 → Fin 3) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 7 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 6 4) t6 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t7 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt8 (r : Fin 5 → Fin 3) : Cnt 8 r = t8 r := by
  have hf : Cnt 7 = t7 := funext Cnt7
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 8 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 7 4) t7 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t8 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt9 (r : Fin 5 → Fin 3) : Cnt 9 r = t9 r := by
  have hf : Cnt 8 = t8 := funext Cnt8
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 9 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 8 4) t8 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t9 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt10 (r : Fin 5 → Fin 3) : Cnt 10 r = t10 r := by
  have hf : Cnt 9 = t9 := funext Cnt9
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 10 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 9 4) t9 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t10 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt11 (r : Fin 5 → Fin 3) : Cnt 11 r = t11 r := by
  have hf : Cnt 10 = t10 := funext Cnt10
  have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
      (if ZA (min 11 4) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) = true then spSum (min 10 4) t10 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) else 0) =
        t11 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

/-- The difference equation of order 3 on every deficit row, from m = 8 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 5 → Fin 3, (Cnt (m + 11) r : ℤ) = 3 * Cnt (m + 10) r - 3 * Cnt (m + 9) r + Cnt (m + 8) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt8, Cnt9, Cnt10, Cnt11]
    have h : ∀ c0 c1 c2 c3 c4 : Fin 3,
        (t11 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) : ℤ) = 3 * t10 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) - 3 * t9 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) + t8 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9 + (c3 : ℕ) * 27 + (c4 : ℕ) * 81)) := by
      decide +kernel
    rw [← dig_code r]
    exact h (r 0) (r 1) (r 2) (r 3) (r 4)
  | succ m ih =>
    intro r
    rw [show m + 1 + 11 = m + 11 + 1 by omega, show m + 1 + 10 = m + 10 + 1 by omega, show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega,
      Cnt_hom (m + 11) (by omega), Cnt_hom (m + 10) (by omega), Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 12. -/
theorem a_rec (m : ℕ) : (a (m + 11 + 1) : ℤ) = 3 * a (m + 10 + 1) - 3 * a (m + 9 + 1) + a (m + 8 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact Cnt_rec m r
  · simp

lemma v1 : a 1 = 6 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 25 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 102 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 268 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 268 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 3568 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 16028 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

lemma v8 : a 8 = 40238 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt7]
  decide +kernel

lemma v9 : a 9 = 77063 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt8]
  decide +kernel

lemma v10 : a 10 = 126673 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt9]
  decide +kernel

lemma v11 : a 11 = 189083 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt10]
  decide +kernel

/-- Barker's recurrence, for n > 11. -/
theorem recurrence (n : ℕ) (hn : 11 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 + 3 + 1 := ⟨n - 12, by omega⟩
  rw [show m + 8 + 3 + 1 - 1 = m + 10 + 1 by omega, show m + 8 + 3 + 1 - 2 = m + 9 + 1 by omega, show m + 8 + 3 + 1 - 3 = m + 8 + 1 by omega]
  rw [show m + 8 + 3 + 1 = m + 11 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^3 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
    X * (6 + 7 * X + 45 * X ^ 2 + 31 * X ^ 3 - 255 * X ^ 4 + 3466 * X ^ 5 + 5860 * X ^ 6 +
        2590 * X ^ 7 + 865 * X ^ 8 + 170 * X ^ 9 + 15 * X ^ 10) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (6 + 7 * X + 45 * X ^ 2 + 31 * X ^ 3 - 255 * X ^ 4 + 3466 * X ^ 5 + 5860 * X ^ 6 +
        2590 * X ^ 7 + 865 * X ^ 8 + 170 * X ^ 9 + 15 * X ^ 10) : ℤ⟦X⟧) =
      X ^ 1 * C 6 + X ^ 2 * C 7 + X ^ 3 * C 45 + X ^ 4 * C 31 - X ^ 5 * C 255 + X ^ 6 * C 3466 + X ^ 7 * C 5860 + X ^ 8 * C 2590 + X ^ 9 * C 865 + X ^ 10 * C 170 + X ^ 11 * C 15 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 12 := ⟨n - 12, by omega⟩
    have h := recurrence (q + 12) (by omega)
    simp only [show q + 12 - 1 = q + 11 by omega, show q + 12 - 2 = q + 10 by omega, show q + 12 - 3 = q + 9 by omega] at h ⊢
    simp only [ show ¬ q + 12 = 0 by omega, show 1 ≤ q + 12 by omega, show ¬ q + 11 = 0 by omega,
      show 2 ≤ q + 12 by omega, show ¬ q + 10 = 0 by omega, show 3 ≤ q + 12 by omega,
      show ¬ q + 9 = 0 by omega, show ¬ q + 12 = 1 by omega, show ¬ q + 12 = 2 by omega,
      show ¬ q + 12 = 3 by omega, show ¬ q + 12 = 4 by omega, show ¬ q + 12 = 5 by omega,
      show ¬ q + 12 = 6 by omega, show ¬ q + 12 = 7 by omega, show ¬ q + 12 = 8 by omega,
      show ¬ q + 12 = 9 by omega, show ¬ q + 12 = 10 by omega, show ¬ q + 12 = 11 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..31). -/
theorem controls : a 1 = 6 ∧ a 2 = 25 ∧ a 3 = 102 ∧ a 4 = 268 ∧ a 5 = 268 ∧ a 6 = 3568 ∧
    a 7 = 16028 ∧ a 8 = 40238 ∧ a 9 = 77063 ∧ a 10 = 126673 ∧ a 11 = 189083 ∧ a 12 = 264293 ∧
    a 13 = 352303 ∧ a 14 = 453113 ∧ a 15 = 566723 ∧ a 16 = 693133 ∧ a 17 = 832343 ∧ a 18 = 984353 ∧
    a 19 = 1149163 ∧ a 20 = 1326773 ∧ a 21 = 1517183 ∧ a 22 = 1720393 ∧ a 23 = 1936403 ∧
    a 24 = 2165213 ∧ a 25 = 2406823 ∧ a 26 = 2661233 ∧ a 27 = 2928443 ∧ a 28 = 3208453 ∧
    a 29 = 3501263 ∧ a 30 = 3806873 ∧ a 31 = 4125283 := by
  have v12 : a 12 = 264293 := by
    have h : (a 12 : ℤ) = 3 * a 11 - 3 * a 10 + a 9 := a_rec 0
    rw [v11, v10, v9] at h
    omega
  have v13 : a 13 = 352303 := by
    have h : (a 13 : ℤ) = 3 * a 12 - 3 * a 11 + a 10 := a_rec 1
    rw [v12, v11, v10] at h
    omega
  have v14 : a 14 = 453113 := by
    have h : (a 14 : ℤ) = 3 * a 13 - 3 * a 12 + a 11 := a_rec 2
    rw [v13, v12, v11] at h
    omega
  have v15 : a 15 = 566723 := by
    have h : (a 15 : ℤ) = 3 * a 14 - 3 * a 13 + a 12 := a_rec 3
    rw [v14, v13, v12] at h
    omega
  have v16 : a 16 = 693133 := by
    have h : (a 16 : ℤ) = 3 * a 15 - 3 * a 14 + a 13 := a_rec 4
    rw [v15, v14, v13] at h
    omega
  have v17 : a 17 = 832343 := by
    have h : (a 17 : ℤ) = 3 * a 16 - 3 * a 15 + a 14 := a_rec 5
    rw [v16, v15, v14] at h
    omega
  have v18 : a 18 = 984353 := by
    have h : (a 18 : ℤ) = 3 * a 17 - 3 * a 16 + a 15 := a_rec 6
    rw [v17, v16, v15] at h
    omega
  have v19 : a 19 = 1149163 := by
    have h : (a 19 : ℤ) = 3 * a 18 - 3 * a 17 + a 16 := a_rec 7
    rw [v18, v17, v16] at h
    omega
  have v20 : a 20 = 1326773 := by
    have h : (a 20 : ℤ) = 3 * a 19 - 3 * a 18 + a 17 := a_rec 8
    rw [v19, v18, v17] at h
    omega
  have v21 : a 21 = 1517183 := by
    have h : (a 21 : ℤ) = 3 * a 20 - 3 * a 19 + a 18 := a_rec 9
    rw [v20, v19, v18] at h
    omega
  have v22 : a 22 = 1720393 := by
    have h : (a 22 : ℤ) = 3 * a 21 - 3 * a 20 + a 19 := a_rec 10
    rw [v21, v20, v19] at h
    omega
  have v23 : a 23 = 1936403 := by
    have h : (a 23 : ℤ) = 3 * a 22 - 3 * a 21 + a 20 := a_rec 11
    rw [v22, v21, v20] at h
    omega
  have v24 : a 24 = 2165213 := by
    have h : (a 24 : ℤ) = 3 * a 23 - 3 * a 22 + a 21 := a_rec 12
    rw [v23, v22, v21] at h
    omega
  have v25 : a 25 = 2406823 := by
    have h : (a 25 : ℤ) = 3 * a 24 - 3 * a 23 + a 22 := a_rec 13
    rw [v24, v23, v22] at h
    omega
  have v26 : a 26 = 2661233 := by
    have h : (a 26 : ℤ) = 3 * a 25 - 3 * a 24 + a 23 := a_rec 14
    rw [v25, v24, v23] at h
    omega
  have v27 : a 27 = 2928443 := by
    have h : (a 27 : ℤ) = 3 * a 26 - 3 * a 25 + a 24 := a_rec 15
    rw [v26, v25, v24] at h
    omega
  have v28 : a 28 = 3208453 := by
    have h : (a 28 : ℤ) = 3 * a 27 - 3 * a 26 + a 25 := a_rec 16
    rw [v27, v26, v25] at h
    omega
  have v29 : a 29 = 3501263 := by
    have h : (a 29 : ℤ) = 3 * a 28 - 3 * a 27 + a 26 := a_rec 17
    rw [v28, v27, v26] at h
    omega
  have v30 : a 30 = 3806873 := by
    have h : (a 30 : ℤ) = 3 * a 29 - 3 * a 28 + a 27 := a_rec 18
    rw [v29, v28, v27] at h
    omega
  have v31 : a 31 = 4125283 := by
    have h : (a 31 : ℤ) = 3 * a 30 - 3 * a 29 + a 28 := a_rec 19
    rw [v30, v29, v28] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (6 + 7 * X + 45 * X ^ 2 + 31 * X ^ 3 - 255 * X ^ 4 + 3466 * X ^ 5 + 5860 * X ^ 6 +
        2590 * X ^ 7 + 865 * X ^ 8 + 170 * X ^ 9 + 15 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a253220

theorem OMA.solution : type_of% @OMA.S_oeis_a253220.main :=
  OMA.S_oeis_a253220.conjecture
