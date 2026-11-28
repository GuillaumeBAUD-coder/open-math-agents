import OMAStatements.S_oeis_a184065

namespace OMA.S_oeis_a184065_Proof

open OMA.S_oeis_a184065 PowerSeries

/-! ### Part 1: Row encoding (`Fin 4 → Fin 2` ≃ `Fin 16`) and lexicographic order -/

private def encodeRow (r : Fin 4 → Fin 2) : Fin 16 :=
  ⟨(r 0).val * 8 + (r 1).val * 4 + (r 2).val * 2 + (r 3).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt
    omega⟩

private def bit4 (r : Fin 16) (j : Fin 4) : Fin 2 :=
  if j.val = 0 then ⟨(r.val / 8) % 2, by omega⟩
  else if j.val = 1 then ⟨(r.val / 4) % 2, by omega⟩
  else if j.val = 2 then ⟨(r.val / 2) % 2, by omega⟩
  else ⟨r.val % 2, by omega⟩

private lemma bit4_encodeRow (r : Fin 4 → Fin 2) (j : Fin 4) :
    bit4 (encodeRow r) j = r j := by
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt
  fin_cases j <;> apply Fin.ext <;> simp [bit4, encodeRow] <;> omega

private lemma encodeRow_bit4 (x : Fin 16) : encodeRow (bit4 x) = x := by
  apply Fin.ext
  have hx := x.isLt
  simp [encodeRow, bit4]
  omega

private lemma lexLe_row_iff (u v : Fin 4 → Fin 2) :
    LexLe u v ↔ (encodeRow u).val ≤ (encodeRow v).val := by
  have hu0 := (u 0).isLt; have hu1 := (u 1).isLt; have hu2 := (u 2).isLt; have hu3 := (u 3).isLt
  have hv0 := (v 0).isLt; have hv1 := (v 1).isLt; have hv2 := (v 2).isLt; have hv3 := (v 3).isLt
  constructor
  · rintro (rfl | ⟨i, hlt, hgt⟩)
    · exact le_rfl
    · fin_cases i
      · have : (u 0).val < (v 0).val := hgt
        simp [encodeRow]; omega
      · have h0 : (u 0).val = (v 0).val := congrArg Fin.val (hlt 0 (by decide))
        have : (u 1).val < (v 1).val := hgt
        simp [encodeRow]; omega
      · have h0 : (u 0).val = (v 0).val := congrArg Fin.val (hlt 0 (by decide))
        have h1 : (u 1).val = (v 1).val := congrArg Fin.val (hlt 1 (by decide))
        have : (u 2).val < (v 2).val := hgt
        simp [encodeRow]; omega
      · have h0 : (u 0).val = (v 0).val := congrArg Fin.val (hlt 0 (by decide))
        have h1 : (u 1).val = (v 1).val := congrArg Fin.val (hlt 1 (by decide))
        have h2 : (u 2).val = (v 2).val := congrArg Fin.val (hlt 2 (by decide))
        have : (u 3).val < (v 3).val := hgt
        simp [encodeRow]; omega
  · intro hle
    simp only [encodeRow] at hle
    by_cases h0 : u 0 = v 0
    · by_cases h1 : u 1 = v 1
      · by_cases h2 : u 2 = v 2
        · by_cases h3 : u 3 = v 3
          · left; funext j; fin_cases j <;> assumption
          · right; refine ⟨3, ?_, ?_⟩
            · intro j hj; fin_cases j <;> first | exact h0 | exact h1 | exact h2 | contradiction
            · have : (u 0).val = (v 0).val := congrArg Fin.val h0
              have : (u 1).val = (v 1).val := congrArg Fin.val h1
              have : (u 2).val = (v 2).val := congrArg Fin.val h2
              have : (u 3).val ≠ (v 3).val := fun h => h3 (Fin.ext h)
              change (u 3).val < (v 3).val; omega
        · right; refine ⟨2, ?_, ?_⟩
          · intro j hj; fin_cases j <;> first | exact h0 | exact h1 | contradiction
          · have : (u 0).val = (v 0).val := congrArg Fin.val h0
            have : (u 1).val = (v 1).val := congrArg Fin.val h1
            have : (u 2).val ≠ (v 2).val := fun h => h2 (Fin.ext h)
            change (u 2).val < (v 2).val; omega
      · right; refine ⟨1, ?_, ?_⟩
        · intro j hj; fin_cases j <;> first | exact h0 | contradiction
        · have : (u 0).val = (v 0).val := congrArg Fin.val h0
          have : (u 1).val ≠ (v 1).val := fun h => h1 (Fin.ext h)
          change (u 1).val < (v 1).val; omega
    · right; refine ⟨0, ?_, ?_⟩
      · intro j hj; exact absurd hj (Fin.not_lt_zero j)
      · have : (u 0).val ≠ (v 0).val := fun h => h0 (Fin.ext h)
        change (u 0).val < (v 0).val; omega

/-! ### Part 2: Pure-`ℕ` packed state and transition functions -/

private def packState (m r s0 s1 s2 : ℕ) : ℕ :=
  (((m * 16 + r) * 5 + s0) * 5 + s1) * 5 + s2

private def stepBitN (strict : Bool) (a b : ℕ) : Option Bool :=
  if strict then some true
  else if b < a then none
  else some (a < b)

private def stepColMaskN (m r : ℕ) : Option ℕ :=
  let b0 := (m % 2 == 1)
  let b1 := ((m / 2) % 2 == 1)
  let b2 := ((m / 4) % 2 == 1)
  let r0 := (r / 8) % 2; let r1 := (r / 4) % 2; let r2 := (r / 2) % 2; let r3 := r % 2
  match stepBitN b0 r0 r1, stepBitN b1 r1 r2, stepBitN b2 r2 r3 with
  | some n0, some n1, some n2 =>
    some ((if n0 then 1 else 0) + (if n1 then 2 else 0) + (if n2 then 4 else 0))
  | _, _, _ => none

private def diffLe1N (x y : ℕ) : Bool :=
  (x <= y + 1) && (y <= x + 1)

private lemma diffLe1N_iff (x y : ℕ) :
    diffLe1N x y = true ↔ |(x : ℤ) - (y : ℤ)| ≤ 1 := by
  unfold diffLe1N
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, abs_le]
  omega

private def semInitN (r0 r1 : ℕ) : Option ℕ :=
  if r0 ≤ r1 then
    match stepColMaskN 0 r0 with
    | none => none
    | some m0 =>
      match stepColMaskN m0 r1 with
      | none => none
      | some m1 =>
        let a0 := (r0 / 8) % 2; let a1 := (r0 / 4) % 2; let a2 := (r0 / 2) % 2; let a3 := r0 % 2
        let b0 := (r1 / 8) % 2; let b1 := (r1 / 4) % 2; let b2 := (r1 / 2) % 2; let b3 := r1 % 2
        let s0 := a0 + a1 + b0 + b1
        let s1 := a1 + a2 + b1 + b2
        let s2 := a2 + a3 + b2 + b3
        if diffLe1N s0 s1 && diffLe1N s1 s2 then some (packState m1 r1 s0 s1 s2) else none
  else none

private def semStepN (code r2 : ℕ) : Option ℕ :=
  let s2 := code % 5; let t1 := code / 5
  let s1 := t1 % 5; let t2 := t1 / 5
  let s0 := t2 % 5; let t3 := t2 / 5
  let r1 := t3 % 16; let m := t3 / 16
  if r1 ≤ r2 then
    match stepColMaskN m r2 with
    | none => none
    | some m2 =>
      let a0 := (r1 / 8) % 2; let a1 := (r1 / 4) % 2; let a2 := (r1 / 2) % 2; let a3 := r1 % 2
      let b0 := (r2 / 8) % 2; let b1 := (r2 / 4) % 2; let b2 := (r2 / 2) % 2; let b3 := r2 % 2
      let n0 := a0 + a1 + b0 + b1
      let n1 := a1 + a2 + b1 + b2
      let n2 := a2 + a3 + b2 + b3
      if diffLe1N n0 n1 && diffLe1N n1 n2 &&
         diffLe1N s0 n0 && diffLe1N s1 n1 && diffLe1N s2 n2 then
        some (packState m2 r2 n0 n1 n2)
      else none
  else none

/-! ### Part 3: Column lexicographic status under `snocRow` -/

private def snocRow {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2) :
    Fin (n + 2) → Fin 4 → Fin 2 :=
  Fin.snoc (α := fun _ => Fin 4 → Fin 2) M r

private lemma snocRow_castSucc {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2)
    (i : Fin (n + 1)) : snocRow M r i.castSucc = M i := by
  simp [snocRow]

private lemma snocRow_last {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2) :
    snocRow M r (Fin.last (n + 1)) = r := by
  simp [snocRow]

private lemma init_snocRow {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2) :
    Fin.init (snocRow M r) = M := by
  simp [snocRow]

private lemma snocRow_init_self {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2) :
    snocRow (Fin.init M) (M (Fin.last (n + 1))) = M := by
  simp [snocRow]

private def ColLt {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (j : Fin 3) : Prop :=
  ∃ i : Fin (n + 1), (∀ i' : Fin (n + 1), i' < i → M i' j.castSucc = M i' j.succ) ∧
    M i j.castSucc < M i j.succ

private def ColEq {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (j : Fin 3) : Prop :=
  ∀ i : Fin (n + 1), M i j.castSucc = M i j.succ

private lemma lexLe_col_iff {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (j : Fin 3) :
    LexLe (fun i => M i j.castSucc) (fun i => M i j.succ) ↔ ColEq M j ∨ ColLt M j := by
  unfold LexLe ColEq ColLt
  constructor
  · rintro (h | h)
    · left; intro i; exact congrFun h i
    · right; exact h
  · rintro (h | h)
    · left; funext i; exact h i
    · right; exact h

private lemma not_colEq_of_colLt {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (j : Fin 3)
    (h : ColLt M j) : ¬ ColEq M j := by
  rcases h with ⟨i, _, hlt⟩
  intro heq
  exact ne_of_lt hlt (heq i)

private noncomputable def colMaskN {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) : ℕ := by
  classical
  exact (if ColLt M 0 then 1 else 0) + (if ColLt M 1 then 2 else 0) + (if ColLt M 2 then 4 else 0)

private lemma colMaskN_lt {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) : colMaskN M < 8 := by
  classical
  unfold colMaskN
  split_ifs <;> omega

private lemma colMaskN_bit0 {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) :
    (colMaskN M % 2 == 1) = true ↔ ColLt M 0 := by
  classical
  unfold colMaskN
  split_ifs <;> simp_all

private lemma colMaskN_bit1 {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) :
    ((colMaskN M / 2) % 2 == 1) = true ↔ ColLt M 1 := by
  classical
  unfold colMaskN
  split_ifs <;> simp_all

private lemma colMaskN_bit2 {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) :
    ((colMaskN M / 4) % 2 == 1) = true ↔ ColLt M 2 := by
  classical
  unfold colMaskN
  split_ifs <;> simp_all

private lemma col_snoc_iff {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2)
    (j : Fin 3) :
    LexLe (fun i => snocRow M r i j.castSucc) (fun i => snocRow M r i j.succ) ↔
      LexLe (fun i => M i j.castSucc) (fun i => M i j.succ) ∧
        (ColLt M j ∨ (r j.castSucc).val ≤ (r j.succ).val) := by
  rw [lexLe_col_iff, lexLe_col_iff]
  constructor
  · rintro (heq | ⟨i, hpre, hlt⟩)
    · have hM : ColEq M j := fun k => by
        have := heq k.castSucc
        simpa [snocRow_castSucc] using this
      have hr : r j.castSucc = r j.succ := by
        have := heq (Fin.last (n + 1))
        simpa [snocRow_last] using this
      exact ⟨Or.inl hM, Or.inr (le_of_eq (congrArg Fin.val hr))⟩
    · refine Fin.lastCases ?_ ?_ i hpre hlt
      · intro hpre hlt
        have hM : ColEq M j := fun k => by
          have := hpre k.castSucc (Fin.castSucc_lt_last k)
          simpa [snocRow_castSucc] using this
        have hr : (r j.castSucc).val < (r j.succ).val := by
          simpa [snocRow_last] using hlt
        exact ⟨Or.inl hM, Or.inr (le_of_lt hr)⟩
      · intro k hpre hlt
        have hLt : ColLt M j := by
          refine ⟨k, fun k' hk' => ?_, ?_⟩
          · have := hpre k'.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hk')
            simpa [snocRow_castSucc] using this
          · simpa [snocRow_castSucc] using hlt
        exact ⟨Or.inr hLt, Or.inl hLt⟩
  · rintro ⟨hM | hLt, hstep⟩
    · rcases hstep with hLt | hle
      · exact absurd hM (not_colEq_of_colLt M j hLt)
      · rcases eq_or_lt_of_le hle with hr | hr
        · left
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa [snocRow_last] using Fin.ext hr
          · intro k; simpa [snocRow_castSucc] using hM k
        · right
          refine ⟨Fin.last (n + 1), ?_, ?_⟩
          · intro i' hi'
            obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hi')
            simpa [snocRow_castSucc] using hM k
          · simpa [snocRow_last] using hr
    · right
      rcases hLt with ⟨k, hpre, hlt⟩
      refine ⟨k.castSucc, ?_, ?_⟩
      · intro i' hi'
        have hi'_ne : i' ≠ Fin.last (n + 1) := by
          intro heq; rw [heq] at hi'; exact not_lt_of_ge (Fin.le_last _) hi'
        obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hi'_ne
        have hk' : k' < k := Fin.castSucc_lt_castSucc_iff.mp hi'
        simpa [snocRow_castSucc] using hpre k' hk'
      · simpa [snocRow_castSucc] using hlt

private lemma colLt_snoc_iff {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2)
    (j : Fin 3) (hM : LexLe (fun i => M i j.castSucc) (fun i => M i j.succ)) :
    ColLt (snocRow M r) j ↔ ColLt M j ∨ (r j.castSucc).val < (r j.succ).val := by
  rw [lexLe_col_iff] at hM
  constructor
  · rintro ⟨i, hpre, hlt⟩
    refine Fin.lastCases ?_ ?_ i hpre hlt
    · intro _ hlt
      right; simpa [snocRow_last] using hlt
    · intro k hpre hlt
      left
      refine ⟨k, fun k' hk' => ?_, ?_⟩
      · have := hpre k'.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hk')
        simpa [snocRow_castSucc] using this
      · simpa [snocRow_castSucc] using hlt
  · rintro (⟨k, hpre, hlt⟩ | hr)
    · refine ⟨k.castSucc, ?_, ?_⟩
      · intro i' hi'
        have hi'_ne : i' ≠ Fin.last (n + 1) := by
          intro heq; rw [heq] at hi'; exact not_lt_of_ge (Fin.le_last _) hi'
        obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hi'_ne
        have hk' : k' < k := Fin.castSucc_lt_castSucc_iff.mp hi'
        simpa [snocRow_castSucc] using hpre k' hk'
      · simpa [snocRow_castSucc] using hlt
    · rcases hM with hEq | ⟨k, hpre, hlt⟩
      · refine ⟨Fin.last (n + 1), ?_, ?_⟩
        · intro i' hi'
          obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hi')
          simpa [snocRow_castSucc] using hEq k
        · simpa [snocRow_last] using hr
      · refine ⟨k.castSucc, ?_, ?_⟩
        · intro i' hi'
          have hi'_ne : i' ≠ Fin.last (n + 1) := by
            intro heq; rw [heq] at hi'; exact not_lt_of_ge (Fin.le_last _) hi'
          obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hi'_ne
          have hk' : k' < k := Fin.castSucc_lt_castSucc_iff.mp hi'
          simpa [snocRow_castSucc] using hpre k' hk'
        · simpa [snocRow_castSucc] using hlt

private lemma stepBitN_eq_some_iff (strict : Bool) (a b : ℕ) (nb : Bool) :
    stepBitN strict a b = some nb ↔
      (strict = true ∨ a ≤ b) ∧ (nb = true ↔ strict = true ∨ a < b) := by
  unfold stepBitN
  cases strict
  · by_cases hba : b < a
    · simp only [Bool.false_eq_true, ↓reduceIte, hba, reduceCtorEq, false_or, false_iff, not_and]
      intro h; omega
    · simp only [Bool.false_eq_true, ↓reduceIte, hba, Option.some.injEq, false_or]
      constructor
      · intro h; subst h; exact ⟨by omega, by simp⟩
      · rintro ⟨_, hiff⟩
        cases nb <;> simp_all
  · simp

private lemma encodeRow_bits (r : Fin 4 → Fin 2) :
    ((encodeRow r).val / 8) % 2 = (r 0).val ∧
    ((encodeRow r).val / 4) % 2 = (r 1).val ∧
    ((encodeRow r).val / 2) % 2 = (r 2).val ∧
    (encodeRow r).val % 2 = (r 3).val := by
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt
  simp only [encodeRow]
  omega

private lemma stepColMaskN_snoc {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (r : Fin 4 → Fin 2)
    (hM : ∀ j : Fin 3, LexLe (fun i => M i j.castSucc) (fun i => M i j.succ)) :
    (∀ j : Fin 3, LexLe (fun i => snocRow M r i j.castSucc) (fun i => snocRow M r i j.succ)) ↔
      stepColMaskN (colMaskN M) (encodeRow r).val = some (colMaskN (snocRow M r)) := by
  classical
  obtain ⟨hr0, hr1, hr2, hr3⟩ := encodeRow_bits r
  have hb0 : (colMaskN M % 2 == 1) = true ↔ ColLt M 0 := colMaskN_bit0 M
  have hb1 : ((colMaskN M / 2) % 2 == 1) = true ↔ ColLt M 1 := colMaskN_bit1 M
  have hb2 : ((colMaskN M / 4) % 2 == 1) = true ↔ ColLt M 2 := colMaskN_bit2 M
  have hlt0 : ColLt (snocRow M r) 0 ↔ ColLt M 0 ∨ (r 0).val < (r 1).val := colLt_snoc_iff M r 0 (hM 0)
  have hlt1 : ColLt (snocRow M r) 1 ↔ ColLt M 1 ∨ (r 1).val < (r 2).val := colLt_snoc_iff M r 1 (hM 1)
  have hlt2 : ColLt (snocRow M r) 2 ↔ ColLt M 2 ∨ (r 2).val < (r 3).val := colLt_snoc_iff M r 2 (hM 2)
  unfold stepColMaskN
  simp only [hr0, hr1, hr2, hr3]
  constructor
  · intro hsnoc
    have hs0 : stepBitN (colMaskN M % 2 == 1) (r 0).val (r 1).val =
        some (decide (ColLt (snocRow M r) 0)) := by
      rw [stepBitN_eq_some_iff, hb0, decide_eq_true_eq, hlt0]
      exact ⟨((col_snoc_iff M r 0).mp (hsnoc 0)).2, Iff.rfl⟩
    have hs1 : stepBitN ((colMaskN M / 2) % 2 == 1) (r 1).val (r 2).val =
        some (decide (ColLt (snocRow M r) 1)) := by
      rw [stepBitN_eq_some_iff, hb1, decide_eq_true_eq, hlt1]
      exact ⟨((col_snoc_iff M r 1).mp (hsnoc 1)).2, Iff.rfl⟩
    have hs2 : stepBitN ((colMaskN M / 4) % 2 == 1) (r 2).val (r 3).val =
        some (decide (ColLt (snocRow M r) 2)) := by
      rw [stepBitN_eq_some_iff, hb2, decide_eq_true_eq, hlt2]
      exact ⟨((col_snoc_iff M r 2).mp (hsnoc 2)).2, Iff.rfl⟩
    rw [hs0, hs1, hs2]
    congr 1
    unfold colMaskN
    simp only [decide_eq_true_eq]
  · intro hstep
    cases h0 : stepBitN (colMaskN M % 2 == 1) (r 0).val (r 1).val with
    | none => simp [h0] at hstep
    | some n0 =>
      cases h1 : stepBitN ((colMaskN M / 2) % 2 == 1) (r 1).val (r 2).val with
      | none => simp [h0, h1] at hstep
      | some n1 =>
        cases h2 : stepBitN ((colMaskN M / 4) % 2 == 1) (r 2).val (r 3).val with
        | none => simp [h0, h1, h2] at hstep
        | some n2 =>
          intro j
          rw [col_snoc_iff M r j]
          refine ⟨hM j, ?_⟩
          fin_cases j
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h0).1
            rwa [hb0] at this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h1).1
            rwa [hb1] at this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h2).1
            rwa [hb2] at this

private lemma stepColMaskN_snoc_of_some {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2)
    (r : Fin 4 → Fin 2)
    (hM : ∀ j : Fin 3, LexLe (fun i => M i j.castSucc) (fun i => M i j.succ))
    {m' : ℕ} (hstep : stepColMaskN (colMaskN M) (encodeRow r).val = some m') :
    (∀ j : Fin 3, LexLe (fun i => snocRow M r i j.castSucc) (fun i => snocRow M r i j.succ)) ∧
      m' = colMaskN (snocRow M r) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := encodeRow_bits r
  have hb0 := colMaskN_bit0 M
  have hb1 := colMaskN_bit1 M
  have hb2 := colMaskN_bit2 M
  have hsnoc : ∀ j : Fin 3,
      LexLe (fun i => snocRow M r i j.castSucc) (fun i => snocRow M r i j.succ) := by
    unfold stepColMaskN at hstep
    simp only [hr0, hr1, hr2, hr3] at hstep
    cases h0 : stepBitN (colMaskN M % 2 == 1) (r 0).val (r 1).val with
    | none => simp [h0] at hstep
    | some n0 =>
      cases h1 : stepBitN ((colMaskN M / 2) % 2 == 1) (r 1).val (r 2).val with
      | none => simp [h0, h1] at hstep
      | some n1 =>
        cases h2 : stepBitN ((colMaskN M / 4) % 2 == 1) (r 2).val (r 3).val with
        | none => simp [h0, h1, h2] at hstep
        | some n2 =>
          intro j
          rw [col_snoc_iff M r j]
          refine ⟨hM j, ?_⟩
          fin_cases j
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h0).1; rwa [hb0] at this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h1).1; rwa [hb1] at this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h2).1; rwa [hb2] at this
  have hst := (stepColMaskN_snoc M r hM).mp hsnoc
  rw [hstep] at hst
  exact ⟨hsnoc, Option.some.inj hst⟩

/-! ### Part 4: Packed state of a valid `(n + 2) × 4` array -/

private def ssumNat {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (i : Fin n) (j : Fin 3) : ℕ :=
  (M i.castSucc j.castSucc).val + (M i.castSucc j.succ).val +
  (M i.succ j.castSucc).val + (M i.succ j.succ).val

private lemma ssumNat_lt {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (i : Fin n) (j : Fin 3) :
    ssumNat M i j < 5 := by
  unfold ssumNat
  have h1 := (M i.castSucc j.castSucc).isLt; have h2 := (M i.castSucc j.succ).isLt
  have h3 := (M i.succ j.castSucc).isLt; have h4 := (M i.succ j.succ).isLt
  omega

private lemma ssumNat_cast {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (i : Fin n) (j : Fin 3) :
    (ssumNat M i j : ℤ) = subblockSum M i j := by
  simp [ssumNat, subblockSum]

private noncomputable def arrayState {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2) : ℕ :=
  packState (colMaskN M) (encodeRow (M (Fin.last (n + 1)))).val
    (ssumNat M (Fin.last n) 0) (ssumNat M (Fin.last n) 1) (ssumNat M (Fin.last n) 2)

private lemma subblockSum_snoc_castSucc {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2)
    (r : Fin 4 → Fin 2) (i : Fin (n + 1)) (j : Fin 3) :
    subblockSum (snocRow M r) i.castSucc j = subblockSum M i j := by
  unfold subblockSum
  have h2 : (i.castSucc : Fin (n + 2)).succ = (i.succ : Fin (n + 2)).castSucc := by
    apply Fin.ext; simp
  simp only [h2, snocRow_castSucc]

private lemma ssumNat_snoc_last {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2)
    (r : Fin 4 → Fin 2) (j : Fin 3) :
    ssumNat (snocRow M r) (Fin.last (n + 1)) j =
      (M (Fin.last (n + 1)) j.castSucc).val + (M (Fin.last (n + 1)) j.succ).val +
      (r j.castSucc).val + (r j.succ).val := by
  unfold ssumNat
  have h2 : (Fin.last (n + 1) : Fin (n + 2)).succ = Fin.last (n + 2) := by
    apply Fin.ext; simp
  simp [h2, snocRow_castSucc, snocRow_last]

private lemma semStepN_arrayState_unfold {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2)
    (r : Fin 4 → Fin 2) :
    semStepN (arrayState M) (encodeRow r).val =
      if (encodeRow (M (Fin.last (n + 1)))).val ≤ (encodeRow r).val then
        match stepColMaskN (colMaskN M) (encodeRow r).val with
        | none => none
        | some m2 =>
          let n0 := ssumNat (snocRow M r) (Fin.last (n + 1)) 0
          let n1 := ssumNat (snocRow M r) (Fin.last (n + 1)) 1
          let n2 := ssumNat (snocRow M r) (Fin.last (n + 1)) 2
          if diffLe1N n0 n1 && diffLe1N n1 n2 &&
             diffLe1N (ssumNat M (Fin.last n) 0) n0 &&
             diffLe1N (ssumNat M (Fin.last n) 1) n1 &&
             diffLe1N (ssumNat M (Fin.last n) 2) n2 then
            some (packState m2 (encodeRow r).val n0 n1 n2)
          else none
      else none := by
  have hm := colMaskN_lt M
  have hr := (encodeRow (M (Fin.last (n + 1)))).isLt
  have hs0 := ssumNat_lt M (Fin.last n) 0
  have hs1 := ssumNat_lt M (Fin.last n) 1
  have hs2 := ssumNat_lt M (Fin.last n) 2
  have hcode : arrayState M = packState (colMaskN M) (encodeRow (M (Fin.last (n + 1)))).val
      (ssumNat M (Fin.last n) 0) (ssumNat M (Fin.last n) 1) (ssumNat M (Fin.last n) 2) := rfl
  have hu2 : arrayState M % 5 = ssumNat M (Fin.last n) 2 := by
    rw [hcode]; unfold packState; omega
  have hu1 : (arrayState M / 5) % 5 = ssumNat M (Fin.last n) 1 := by
    rw [hcode]; unfold packState; omega
  have hu0 : (arrayState M / 5 / 5) % 5 = ssumNat M (Fin.last n) 0 := by
    rw [hcode]; unfold packState; omega
  have hur : (arrayState M / 5 / 5 / 5) % 16 = (encodeRow (M (Fin.last (n + 1)))).val := by
    rw [hcode]; unfold packState; omega
  have hum : arrayState M / 5 / 5 / 5 / 16 = colMaskN M := by
    rw [hcode]; unfold packState; omega
  obtain ⟨a0, a1, a2, a3⟩ := encodeRow_bits (M (Fin.last (n + 1)))
  obtain ⟨b0, b1, b2, b3⟩ := encodeRow_bits r
  have hn0 : ssumNat (snocRow M r) (Fin.last (n + 1)) 0 =
      (M (Fin.last (n + 1)) 0).val + (M (Fin.last (n + 1)) 1).val + (r 0).val + (r 1).val :=
    ssumNat_snoc_last M r 0
  have hn1 : ssumNat (snocRow M r) (Fin.last (n + 1)) 1 =
      (M (Fin.last (n + 1)) 1).val + (M (Fin.last (n + 1)) 2).val + (r 1).val + (r 2).val :=
    ssumNat_snoc_last M r 1
  have hn2 : ssumNat (snocRow M r) (Fin.last (n + 1)) 2 =
      (M (Fin.last (n + 1)) 2).val + (M (Fin.last (n + 1)) 3).val + (r 2).val + (r 3).val :=
    ssumNat_snoc_last M r 2
  unfold semStepN
  simp only [hu2, hu1, hu0, hur, hum, a0, a1, a2, a3, b0, b1, b2, b3, hn0, hn1, hn2]

private lemma isValidArray_snoc_semStep {n : ℕ} (M : Fin (n + 2) → Fin 4 → Fin 2)
    (r : Fin 4 → Fin 2) (st : ℕ) :
    (IsValidArray (n + 2) (snocRow M r) ∧ arrayState (snocRow M r) = st) ↔
      IsValidArray (n + 1) M ∧ semStepN (arrayState M) (encodeRow r).val = some st := by
  have hrows :
      (∀ i : Fin (n + 2), LexLe (snocRow M r i.castSucc) (snocRow M r i.succ)) ↔
        (∀ i : Fin (n + 1), LexLe (M i.castSucc) (M i.succ)) ∧
          (encodeRow (M (Fin.last (n + 1)))).val ≤ (encodeRow r).val := by
    rw [← lexLe_row_iff]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have hi := h i.castSucc
        have h2 : (i.castSucc : Fin (n + 2)).succ = (i.succ : Fin (n + 2)).castSucc := by
          apply Fin.ext; simp
        simpa only [h2, snocRow_castSucc] using hi
      · have hi := h (Fin.last (n + 1))
        have h2 : (Fin.last (n + 1) : Fin (n + 2)).succ = Fin.last (n + 2) := by
          apply Fin.ext; simp
        simpa [h2, snocRow_castSucc, snocRow_last] using hi
    · rintro ⟨h1, h2⟩ i
      refine Fin.lastCases ?_ ?_ i
      · have hlast : (Fin.last (n + 1) : Fin (n + 2)).succ = Fin.last (n + 2) := by
          apply Fin.ext; simp
        simpa [hlast, snocRow_castSucc, snocRow_last] using h2
      · intro k
        have hsucc : (k.castSucc : Fin (n + 2)).succ = (k.succ : Fin (n + 2)).castSucc := by
          apply Fin.ext; simp
        simpa only [hsucc, snocRow_castSucc] using h1 k
  have hhoriz :
      (∀ (i : Fin (n + 2)) (j : Fin 2),
        |subblockSum (snocRow M r) i j.castSucc - subblockSum (snocRow M r) i j.succ| ≤ 1) ↔
      (∀ (i : Fin (n + 1)) (j : Fin 2),
        |subblockSum M i j.castSucc - subblockSum M i j.succ| ≤ 1) ∧
      (diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 0)
                (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
       diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 1)
                (ssumNat (snocRow M r) (Fin.last (n + 1)) 2)) = true := by
    rw [Bool.and_eq_true, diffLe1N_iff, diffLe1N_iff,
      ssumNat_cast, ssumNat_cast, ssumNat_cast]
    constructor
    · intro h
      refine ⟨fun i j => ?_, h (Fin.last (n + 1)) 0, h (Fin.last (n + 1)) 1⟩
      simpa [subblockSum_snoc_castSucc] using h i.castSucc j
    · rintro ⟨h1, h01, h12⟩ i j
      refine Fin.lastCases ?_ ?_ i
      · fin_cases j; exact h01; exact h12
      · intro k; simpa [subblockSum_snoc_castSucc] using h1 k j
  have hvert :
      (∀ (i₁ i₂ : Fin (n + 2)), i₁.val + 1 = i₂.val →
        ∀ j : Fin 3, |subblockSum (snocRow M r) i₁ j - subblockSum (snocRow M r) i₂ j| ≤ 1) ↔
      (∀ (i₁ i₂ : Fin (n + 1)), i₁.val + 1 = i₂.val →
        ∀ j : Fin 3, |subblockSum M i₁ j - subblockSum M i₂ j| ≤ 1) ∧
      (diffLe1N (ssumNat M (Fin.last n) 0) (ssumNat (snocRow M r) (Fin.last (n + 1)) 0) &&
       diffLe1N (ssumNat M (Fin.last n) 1) (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
       diffLe1N (ssumNat M (Fin.last n) 2) (ssumNat (snocRow M r) (Fin.last (n + 1)) 2)) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, diffLe1N_iff, diffLe1N_iff, diffLe1N_iff]
    have hp : ∀ j : Fin 3, (ssumNat M (Fin.last n) j : ℤ) =
        subblockSum (snocRow M r) (Fin.last n).castSucc j := by
      intro j; rw [subblockSum_snoc_castSucc, ssumNat_cast]
    rw [hp 0, hp 1, hp 2, ssumNat_cast, ssumNat_cast, ssumNat_cast]
    constructor
    · intro h
      refine ⟨fun i₁ i₂ h12 j => ?_, ⟨⟨?_, ?_⟩, ?_⟩⟩
      · simpa [subblockSum_snoc_castSucc] using h i₁.castSucc i₂.castSucc h12 j
      · exact h (Fin.last n).castSucc (Fin.last (n + 1)) (by simp) 0
      · exact h (Fin.last n).castSucc (Fin.last (n + 1)) (by simp) 1
      · exact h (Fin.last n).castSucc (Fin.last (n + 1)) (by simp) 2
    · rintro ⟨h1, ⟨⟨v0, v1⟩, v2⟩⟩ i₁ i₂ h12 j
      have hi1_ne : i₁ ≠ Fin.last (n + 1) := by
        intro heq; rw [heq] at h12; have := i₂.isLt; simp at h12; omega
      obtain ⟨k₁, rfl⟩ := Fin.exists_castSucc_eq.mpr hi1_ne
      refine Fin.lastCases ?_ ?_ i₂ h12
      · intro h12
        have hk1 : k₁ = Fin.last n := by apply Fin.ext; simp at h12 ⊢; omega
        subst hk1
        fin_cases j; exact v0; exact v1; exact v2
      · intro k₂ h12
        simpa [subblockSum_snoc_castSucc] using h1 k₁ k₂ h12 j
  have hst_snoc : arrayState (snocRow M r) =
      packState (colMaskN (snocRow M r)) (encodeRow r).val
        (ssumNat (snocRow M r) (Fin.last (n + 1)) 0)
        (ssumNat (snocRow M r) (Fin.last (n + 1)) 1)
        (ssumNat (snocRow M r) (Fin.last (n + 1)) 2) := by
    unfold arrayState
    simp [snocRow_last]
  rw [semStepN_arrayState_unfold]
  constructor
  · rintro ⟨⟨hr, hc, hh, hv⟩, hst⟩
    have hcM : ∀ j : Fin 3, LexLe (fun i => M i j.castSucc) (fun i => M i j.succ) :=
      fun j => ((col_snoc_iff M r j).mp (hc j)).1
    have hr' := hrows.mp hr
    have hh' := hhoriz.mp hh
    have hv' := hvert.mp hv
    have hcm := (stepColMaskN_snoc M r hcM).mp hc
    refine ⟨⟨hr'.1, hcM, hh'.1, hv'.1⟩, ?_⟩
    have hcond :
        (diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 0)
                  (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
         diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 1)
                  (ssumNat (snocRow M r) (Fin.last (n + 1)) 2) &&
         diffLe1N (ssumNat M (Fin.last n) 0) (ssumNat (snocRow M r) (Fin.last (n + 1)) 0) &&
         diffLe1N (ssumNat M (Fin.last n) 1) (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
         diffLe1N (ssumNat M (Fin.last n) 2) (ssumNat (snocRow M r) (Fin.last (n + 1)) 2)) = true := by
      have h1 := hh'.2; have h2 := hv'.2
      simp only [Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨⟨⟨⟨h1.1, h1.2⟩, h2.1.1⟩, h2.1.2⟩, h2.2⟩
    simp only [hr'.2, ↓reduceIte, hcm, hcond, ← hst_snoc, hst]
  · rintro ⟨⟨hrM, hcM, hhM, hvM⟩, hstep⟩
    by_cases hrle : (encodeRow (M (Fin.last (n + 1)))).val ≤ (encodeRow r).val
    · simp only [hrle, ↓reduceIte] at hstep
      cases hcm : stepColMaskN (colMaskN M) (encodeRow r).val with
      | none => simp [hcm] at hstep
      | some m2 =>
        simp only [hcm] at hstep
        split at hstep
        · rename_i hcond
          simp only [Option.some.injEq] at hstep
          obtain ⟨hcsnoc, hm2⟩ := stepColMaskN_snoc_of_some M r hcM hcm
          have h12 : (diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 0)
                               (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
                      diffLe1N (ssumNat (snocRow M r) (Fin.last (n + 1)) 1)
                               (ssumNat (snocRow M r) (Fin.last (n + 1)) 2)) = true ∧
                     (diffLe1N (ssumNat M (Fin.last n) 0) (ssumNat (snocRow M r) (Fin.last (n + 1)) 0) &&
                      diffLe1N (ssumNat M (Fin.last n) 1) (ssumNat (snocRow M r) (Fin.last (n + 1)) 1) &&
                      diffLe1N (ssumNat M (Fin.last n) 2) (ssumNat (snocRow M r) (Fin.last (n + 1)) 2)) = true := by
            simp only [Bool.and_eq_true] at hcond ⊢
            exact ⟨⟨hcond.1.1.1.1, hcond.1.1.1.2⟩, ⟨⟨hcond.1.1.2, hcond.1.2⟩, hcond.2⟩⟩
          refine ⟨⟨hrows.mpr ⟨hrM, hrle⟩, hcsnoc, hhoriz.mpr ⟨hhM, h12.1⟩, hvert.mpr ⟨hvM, h12.2⟩⟩, ?_⟩
          rw [hst_snoc, ← hm2, hstep]
        · simp at hstep
    · simp [hrle] at hstep

/-! ### Part 5: Base case `n = 1` (`2 × 4` arrays) -/

private lemma stepColMaskN_single (r0 : Fin 4 → Fin 2) :
    (∀ j : Fin 3, LexLe (fun _ : Fin 1 => r0 j.castSucc) (fun _ : Fin 1 => r0 j.succ)) ↔
      stepColMaskN 0 (encodeRow r0).val = some (colMaskN (fun _ : Fin 1 => r0)) := by
  classical
  obtain ⟨hr0, hr1, hr2, hr3⟩ := encodeRow_bits r0
  have hlt : ∀ j : Fin 3, ColLt (fun _ : Fin 1 => r0) j ↔ (r0 j.castSucc).val < (r0 j.succ).val := by
    intro j
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨0, fun i' hi' => absurd hi' (Fin.not_lt_zero i'), h⟩
  have hle : ∀ j : Fin 3,
      LexLe (fun _ : Fin 1 => r0 j.castSucc) (fun _ : Fin 1 => r0 j.succ) ↔
        (r0 j.castSucc).val ≤ (r0 j.succ).val := by
    intro j
    rw [lexLe_col_iff, hlt]
    constructor
    · rintro (heq | hlt); exact le_of_eq (congrArg Fin.val (heq 0)); exact le_of_lt hlt
    · intro h; rcases eq_or_lt_of_le h with heq | hlt
      · left; intro _; exact Fin.ext heq
      · right; exact hlt
  unfold stepColMaskN
  have h01 : (0 == 1) = false := rfl
  simp only [hr0, hr1, hr2, hr3, Nat.zero_mod, Nat.zero_div, h01]
  constructor
  · intro h
    have hs0 : stepBitN false (r0 0).val (r0 1).val = some (decide (ColLt (fun _ : Fin 1 => r0) 0)) := by
      rw [stepBitN_eq_some_iff, decide_eq_true_eq, hlt 0]
      exact ⟨Or.inr ((hle 0).mp (h 0)), by simp⟩
    have hs1 : stepBitN false (r0 1).val (r0 2).val = some (decide (ColLt (fun _ : Fin 1 => r0) 1)) := by
      rw [stepBitN_eq_some_iff, decide_eq_true_eq, hlt 1]
      exact ⟨Or.inr ((hle 1).mp (h 1)), by simp⟩
    have hs2 : stepBitN false (r0 2).val (r0 3).val = some (decide (ColLt (fun _ : Fin 1 => r0) 2)) := by
      rw [stepBitN_eq_some_iff, decide_eq_true_eq, hlt 2]
      exact ⟨Or.inr ((hle 2).mp (h 2)), by simp⟩
    rw [hs0, hs1, hs2]
    congr 1
    unfold colMaskN
    simp only [decide_eq_true_eq]
  · intro hstep
    cases h0 : stepBitN false (r0 0).val (r0 1).val with
    | none => simp [h0] at hstep
    | some n0 =>
      cases h1 : stepBitN false (r0 1).val (r0 2).val with
      | none => simp [h0, h1] at hstep
      | some n1 =>
        cases h2 : stepBitN false (r0 2).val (r0 3).val with
        | none => simp [h0, h1, h2] at hstep
        | some n2 =>
          intro j
          rw [hle j]
          fin_cases j
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h0).1; simpa using this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h1).1; simpa using this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h2).1; simpa using this

private lemma stepColMaskN_single_of_some (r0 : Fin 4 → Fin 2) {m0 : ℕ}
    (hstep : stepColMaskN 0 (encodeRow r0).val = some m0) :
    (∀ j : Fin 3, LexLe (fun _ : Fin 1 => r0 j.castSucc) (fun _ : Fin 1 => r0 j.succ)) ∧
      m0 = colMaskN (fun _ : Fin 1 => r0) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := encodeRow_bits r0
  have hle : ∀ j : Fin 3,
      LexLe (fun _ : Fin 1 => r0 j.castSucc) (fun _ : Fin 1 => r0 j.succ) ↔
        (r0 j.castSucc).val ≤ (r0 j.succ).val := by
    intro j
    rw [lexLe_col_iff]
    constructor
    · rintro (heq | ⟨_, _, hlt⟩); exact le_of_eq (congrArg Fin.val (heq 0)); exact le_of_lt hlt
    · intro h; rcases eq_or_lt_of_le h with heq | hlt
      · left; intro _; exact Fin.ext heq
      · right; exact ⟨0, fun i' hi' => absurd hi' (Fin.not_lt_zero i'), hlt⟩
  have hc0 : ∀ j : Fin 3, LexLe (fun _ : Fin 1 => r0 j.castSucc) (fun _ : Fin 1 => r0 j.succ) := by
    unfold stepColMaskN at hstep
    have h01 : (0 == 1) = false := rfl
    simp only [hr0, hr1, hr2, hr3, Nat.zero_mod, Nat.zero_div, h01] at hstep
    cases h0 : stepBitN false (r0 0).val (r0 1).val with
    | none => simp [h0] at hstep
    | some n0 =>
      cases h1 : stepBitN false (r0 1).val (r0 2).val with
      | none => simp [h0, h1] at hstep
      | some n1 =>
        cases h2 : stepBitN false (r0 2).val (r0 3).val with
        | none => simp [h0, h1, h2] at hstep
        | some n2 =>
          intro j
          rw [hle j]
          fin_cases j
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h0).1; simpa using this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h1).1; simpa using this
          · have := ((stepBitN_eq_some_iff _ _ _ _).mp h2).1; simpa using this
  have hst := (stepColMaskN_single r0).mp hc0
  rw [hstep] at hst
  exact ⟨hc0, Option.some.inj hst⟩

private lemma isValidArray_one_semInit (M : Fin 2 → Fin 4 → Fin 2) (st : ℕ) :
    (IsValidArray 1 M ∧ arrayState M = st) ↔
      semInitN (encodeRow (M 0)).val (encodeRow (M 1)).val = some st := by
  have hM_snoc : M = snocRow (fun _ : Fin 1 => M 0) (M 1) := by
    funext i; fin_cases i
    · exact (snocRow_castSucc (fun _ : Fin 1 => M 0) (M 1) 0).symm
    · exact (snocRow_last (fun _ : Fin 1 => M 0) (M 1)).symm
  obtain ⟨a0, a1, a2, a3⟩ := encodeRow_bits (M 0)
  obtain ⟨b0, b1, b2, b3⟩ := encodeRow_bits (M 1)
  have hs0 : ssumNat M 0 0 = (M 0 0).val + (M 0 1).val + (M 1 0).val + (M 1 1).val := rfl
  have hs1 : ssumNat M 0 1 = (M 0 1).val + (M 0 2).val + (M 1 1).val + (M 1 2).val := rfl
  have hs2 : ssumNat M 0 2 = (M 0 2).val + (M 0 3).val + (M 1 2).val + (M 1 3).val := rfl
  have hrows : (∀ i : Fin 1, LexLe (M i.castSucc) (M i.succ)) ↔
      (encodeRow (M 0)).val ≤ (encodeRow (M 1)).val := by
    rw [← lexLe_row_iff]
    exact ⟨fun h => h 0, fun h i => by fin_cases i; exact h⟩
  have hhoriz :
      (∀ (i : Fin 1) (j : Fin 2), |subblockSum M i j.castSucc - subblockSum M i j.succ| ≤ 1) ↔
        (diffLe1N (ssumNat M 0 0) (ssumNat M 0 1) &&
         diffLe1N (ssumNat M 0 1) (ssumNat M 0 2)) = true := by
    rw [Bool.and_eq_true, diffLe1N_iff, diffLe1N_iff, ssumNat_cast, ssumNat_cast, ssumNat_cast]
    exact ⟨fun h => ⟨h 0 0, h 0 1⟩, fun ⟨h0, h1⟩ i j => by fin_cases i; fin_cases j; exact h0; exact h1⟩
  have hvert : ∀ (i₁ i₂ : Fin 1), i₁.val + 1 = i₂.val →
      ∀ j : Fin 3, |subblockSum M i₁ j - subblockSum M i₂ j| ≤ 1 := by
    intro i₁ i₂ h12; fin_cases i₁; fin_cases i₂; simp at h12
  have hst_M : arrayState M =
      packState (colMaskN M) (encodeRow (M 1)).val
        (ssumNat M 0 0) (ssumNat M 0 1) (ssumNat M 0 2) := rfl
  unfold semInitN
  simp only [a0, a1, a2, a3, b0, b1, b2, b3, ← hs0, ← hs1, ← hs2]
  constructor
  · rintro ⟨⟨hr, hc, hh, _⟩, hst⟩
    have hcsnoc : ∀ j : Fin 3,
        LexLe (fun i => snocRow (fun _ : Fin 1 => M 0) (M 1) i j.castSucc)
          (fun i => snocRow (fun _ : Fin 1 => M 0) (M 1) i j.succ) := by
      simpa [← hM_snoc] using hc
    have hc0 : ∀ j : Fin 3, LexLe (fun _ : Fin 1 => M 0 j.castSucc) (fun _ : Fin 1 => M 0 j.succ) :=
      fun j => ((col_snoc_iff (fun _ : Fin 1 => M 0) (M 1) j).mp (hcsnoc j)).1
    have hm0 := (stepColMaskN_single (M 0)).mp hc0
    have hm1 : stepColMaskN (colMaskN (fun _ : Fin 1 => M 0)) (encodeRow (M 1)).val =
        some (colMaskN M) := by
      have := (stepColMaskN_snoc (fun _ : Fin 1 => M 0) (M 1) hc0).mp hcsnoc
      simpa [← hM_snoc] using this
    simp only [hrows.mp hr, ↓reduceIte, hm0, hm1, hhoriz.mp hh, ← hst_M, hst]
  · intro hinit
    by_cases hrle : (encodeRow (M 0)).val ≤ (encodeRow (M 1)).val
    · simp only [hrle, ↓reduceIte] at hinit
      cases hm0 : stepColMaskN 0 (encodeRow (M 0)).val with
      | none => simp [hm0] at hinit
      | some m0 =>
        simp only [hm0] at hinit
        cases hm1 : stepColMaskN m0 (encodeRow (M 1)).val with
        | none => simp [hm1] at hinit
        | some m1 =>
          simp only [hm1] at hinit
          split at hinit
          · rename_i hok
            simp only [Option.some.injEq] at hinit
            obtain ⟨hc0, hm0_eq⟩ := stepColMaskN_single_of_some (M 0) hm0
            subst hm0_eq
            obtain ⟨hcsnoc, hm1_eq⟩ := stepColMaskN_snoc_of_some (fun _ : Fin 1 => M 0) (M 1) hc0 hm1
            have hc : ∀ j : Fin 3, LexLe (fun i : Fin 2 => M i j.castSucc) (fun i => M i j.succ) := by
              simpa [← hM_snoc] using hcsnoc
            have hm1_M : m1 = colMaskN M := by simpa [← hM_snoc] using hm1_eq
            refine ⟨⟨hrows.mpr hrle, hc, hhoriz.mpr hok, hvert⟩, ?_⟩
            rw [hst_M, ← hm1_M, hinit]
          · simp at hinit
    · simp [hrle] at hinit

/-! ### Part 6: The 88 reachable states, transitions, and cubic polynomials (plain lists + `rfl`) -/

private def stateList : List ℕ := [0, 1937, 1999, 2912, 3062, 3962, 3974, 3999, 4382, 5562, 5944, 6537, 6942, 7062, 7432, 7437, 7444, 7587, 7592, 7962, 7969, 7992, 7999, 8126, 9812, 9938, 10787, 10913, 11061, 11062, 11187, 11188, 11836, 11837, 11962, 11963, 12257, 13688, 14536, 14662, 14663, 14686, 14687, 14817, 14942, 14943, 15055, 15056, 15061, 15062, 15181, 15182, 15187, 15188, 15306, 15307, 15311, 15312, 15317, 15318, 15432, 15437, 15438, 15443, 15444, 15586, 15587, 15592, 15712, 15713, 15717, 15718, 15836, 15837, 15842, 15843, 15848, 15867, 15962, 15963, 15968, 15969, 15973, 15974, 15992, 15993, 15998, 15999]
private def initList : List ℕ := [1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def predsList : List (List ℕ) := [[0], [], [2], [], [3], [4], [], [6, 7], [], [], [], [8], [11], [12], [4, 13], [11], [], [14, 15], [12], [13], [16], [17, 18], [20, 22], [0], [], [], [], [], [26], [27], [26], [3, 27], [28, 29], [30, 31], [28, 29], [30, 31], [23], [], [36], [36], [8], [11, 38], [39, 40, 41, 42], [39, 40, 41, 42], [38], [39, 40, 42], [38], [39, 41, 42], [43], [44, 45], [11, 38], [39, 40, 41, 42], [43], [12, 44, 45], [28, 29, 46, 47, 48, 49], [30, 31, 50, 51, 52, 53], [38], [39, 40, 41, 42, 54, 55, 56, 57, 58, 59], [26, 43], [27, 44, 45], [28, 29, 47, 48, 49], [38], [39, 40, 42, 55, 57, 58, 59], [26, 43], [27, 45], [41, 42, 54, 55, 56, 57, 58], [60, 61, 62, 63], [44, 45], [41, 42, 54, 55, 56, 57, 58, 59], [14, 15, 16, 60, 61, 62, 63, 64], [43], [12, 44, 45], [46, 47, 48, 49], [50, 51, 52, 53], [41, 42, 56, 57, 58, 59], [61, 62, 63, 64], [44, 45], [68, 69, 70, 71], [47, 48, 49], [51, 52, 53], [42, 57, 58, 59], [62, 63, 64], [43], [45], [65, 66, 67], [68, 69, 70, 71], [74, 75, 76, 77], [80, 81, 82, 83, 85, 86, 87]]
private def succsList : List (List ℕ) := [[0, 23], [], [2], [4, 31], [14, 5], [], [7], [7], [11, 40], [], [], [41, 12, 50, 15], [13, 53, 18, 71], [14, 19], [17, 69], [17, 69], [69, 20], [21], [21], [], [22], [], [22], [36], [], [], [28, 30, 58, 63], [29, 31, 59, 64], [54, 60, 32, 34], [54, 60, 32, 34], [55, 33, 35], [55, 33, 35], [], [], [], [], [38, 39], [], [41, 44, 46, 50, 56, 61], [42, 43, 45, 47, 51, 57, 62], [42, 43, 45, 51, 57, 62], [42, 43, 47, 51, 57, 65, 68, 74], [42, 43, 45, 47, 51, 57, 62, 65, 68, 74, 80], [48, 52, 58, 63, 70, 82], [49, 53, 59, 67, 71, 76], [49, 53, 59, 64, 67, 71, 76, 83], [54, 72], [54, 60, 72, 78], [54, 60, 72, 78], [54, 60, 72, 78], [55, 73], [55, 73, 79], [55, 73, 79], [55, 73, 79], [57, 65, 68], [57, 62, 65, 68], [57, 65, 68, 74], [57, 62, 65, 68, 74, 80], [57, 62, 65, 68, 74, 80], [57, 62, 68, 74, 80], [66, 69], [66, 69, 75], [66, 69, 75, 81], [66, 69, 75, 81], [69, 75, 81], [84], [84], [84], [77, 85], [77, 85], [77, 85], [77, 85], [], [], [86], [86], [86], [86], [], [], [87], [87], [87], [87], [], [87], [87], [87]]
private def c0List : List ℤ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, -1, -1, 1, -2, 1, -1, -3, -3, 1, -1, -3, -3, -12, -12, 1, 12, -3, -3, -13, 1, 28, -3, -4, 16, 57, -3, 11, 51, -3, -3, -12, -12, 47, 70, -3, 158, -13, -13, 45, 69, -3, -4, 178, 158, 532, -552]
private def c1List : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 6, 6, 0, -37, 2, 2, 6, 0, -43, 2, 2, -39, -53, 2, -37, -51, 2, 2, 6, 6, -49, -57, 2, -120, 6, 6, -49, -57, 2, 2, -126, -120, -296, 1068]
private def c2List : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 9, 0, 0, 9, 9, 0, 9, 9, 0, 0, 0, 0, 9, 9, 0, 18, 0, 0, 9, 9, 0, 0, 18, 18, 36, -295]
private def c3List : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24]
private def initStatesN : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 16, 23, 24, 25, 26, 27, 31, 36, 37, 40]
private def initSemListN : List ℕ := [0, 8126, 4382, 2912, 1937, 12257, 10787, 10913, 9812, 9938, 6537, 14663, 5562, 13688, 5944, 3062, 11188, 7444, 3974, 1999]
private def dpVal0 : List ℕ := [1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def dpVal1 : List ℕ := [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def dpVal2 : List ℕ := [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 3, 1, 0, 1, 1, 0, 2, 4, 4, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5, 1, 8, 1, 1, 2, 1, 7, 1, 1, 5, 2, 1, 6, 5, 1, 2, 0, 2, 5, 3, 1, 1, 0, 1, 4, 3, 1, 1, 0, 1, 0, 0]
private def dpVal3 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 1, 1, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 7, 7, 1, 5, 1, 7, 4, 4, 1, 7, 4, 5, 6, 9, 1, 25, 4, 4, 5, 1, 20, 4, 3, 23, 11, 4, 24, 14, 4, 5, 6, 9, 17, 10, 4, 14, 5, 7, 14, 9, 4, 3, 8, 14, 10, 10]
private def dpVal4 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 9, 9, 1, 8, 1, 9, 7, 6, 1, 9, 7, 6, 16, 17, 1, 58, 7, 6, 15, 1, 50, 7, 5, 53, 30, 6, 57, 34, 7, 6, 16, 17, 42, 28, 6, 47, 15, 16, 40, 27, 7, 5, 38, 47, 45, 64]
private def dpVal5 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 11, 11, 1, 10, 1, 11, 9, 9, 1, 11, 9, 9, 23, 23, 1, 116, 9, 9, 22, 1, 98, 9, 8, 109, 73, 9, 115, 79, 9, 9, 23, 23, 82, 63, 9, 104, 22, 22, 80, 62, 9, 8, 89, 104, 123, 235]
private def dpVal6 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 13, 13, 1, 12, 1, 13, 11, 11, 1, 13, 11, 11, 30, 30, 1, 194, 11, 11, 29, 1, 169, 11, 10, 184, 130, 11, 193, 138, 11, 11, 30, 30, 147, 116, 11, 212, 29, 29, 145, 115, 11, 10, 191, 212, 258, 621]
private def dpVal7 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 15, 15, 1, 14, 1, 15, 13, 13, 1, 15, 13, 13, 36, 36, 1, 292, 13, 13, 35, 1, 260, 13, 12, 280, 210, 13, 291, 220, 13, 13, 36, 36, 231, 191, 13, 353, 35, 35, 229, 190, 13, 12, 325, 353, 486, 1372]
private def dpVal8 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 17, 17, 1, 16, 1, 17, 15, 15, 1, 17, 15, 15, 42, 42, 1, 408, 15, 15, 41, 1, 370, 15, 14, 394, 309, 15, 407, 321, 15, 15, 42, 42, 335, 286, 15, 537, 41, 41, 333, 285, 15, 14, 503, 537, 788, 2655]
private def dpVal9 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 19, 19, 1, 18, 1, 19, 17, 17, 1, 19, 17, 17, 48, 48, 1, 542, 17, 17, 47, 1, 498, 17, 16, 526, 427, 17, 541, 441, 17, 17, 48, 48, 457, 400, 17, 758, 47, 47, 455, 399, 17, 16, 718, 758, 1173, 4627]
private def dpVal10 : List ℕ := [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 21, 21, 1, 20, 1, 21, 19, 19, 1, 21, 19, 19, 54, 54, 1, 694, 19, 19, 53, 1, 644, 19, 18, 676, 563, 19, 693, 579, 19, 19, 54, 54, 597, 532, 19, 1016, 53, 53, 595, 531, 19, 18, 970, 1016, 1632, 7445]

private def stateCodeN (i : ℕ) : ℕ := stateList.getD i 0
private def stateRowN (i : ℕ) : ℕ := (stateCodeN i / 125) % 16
private def predsN (j : ℕ) : List ℕ := predsList.getD j []

private def isSortedStrict : List ℕ → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (x < y) && isSortedStrict (y :: rest)

private def isNodupB : List ℕ → Bool
  | [] => true
  | x :: xs => !xs.contains x && isNodupB xs

private def dpStepL (v : List ℕ) : List ℕ :=
  predsList.map fun ps => ps.foldl (fun acc i => acc + v.getD i 0) 0

private def sumIntL (L : List ℤ) : ℤ :=
  L.foldl (fun acc x => acc + x) 0

private def sumNatL (L : List ℕ) : ℕ :=
  L.foldl (fun acc x => acc + x) 0

private lemma chk_len_state : stateList.length = 88 := rfl
private lemma chk_len_init : initList.length = 88 := rfl
private lemma chk_len_preds : predsList.length = 88 := rfl
private lemma chk_len_succs : succsList.length = 88 := rfl
private lemma chk_len_c0 : c0List.length = 88 := rfl
private lemma chk_len_c1 : c1List.length = 88 := rfl
private lemma chk_len_c2 : c2List.length = 88 := rfl
private lemma chk_len_c3 : c3List.length = 88 := rfl

private lemma chk_sorted : isSortedStrict stateList = true := rfl
private lemma chk_preds_nodup : predsList.all isNodupB = true := rfl
private lemma chk_preds_bounds : predsList.all (fun L => L.all (fun i => i < 88)) = true := rfl
private lemma chk_initStates_bounds : initStatesN.all (fun j => j < 88) = true := rfl
private lemma chk_succs_bounds : succsList.all (fun L => L.all (fun j => j < 88)) = true := rfl

private lemma chk_init_list :
    ((List.range 16).flatMap fun r0 => (List.range 16).filterMap fun r1 => semInitN r0 r1) =
      initSemListN := rfl

private lemma chk_init_closed :
    initSemListN.all (fun c => initStatesN.any (fun j => stateCodeN j == c)) = true := rfl

private lemma chk_init_count :
    (stateList.map fun c => initSemListN.count c) = initList := rfl

private lemma chk_step_sound :
    (List.zipWith (fun code ps =>
      let r := (code / 125) % 16
      ps.all (fun i => semStepN (stateCodeN i) r == some code)) stateList predsList).all id = true := rfl

private lemma chk_step_complete :
    (List.zipWith (fun i code =>
      (List.range 16).all fun r =>
        match semStepN code r with
        | none => true
        | some c => (succsList.getD i []).any (fun j =>
            stateCodeN j == c && (predsN j).contains i && r == stateRowN j))
      (List.range 88) stateList).all id = true := rfl

private lemma chk_dp0 : initList = dpVal0 := rfl
private lemma chk_dp1 : dpStepL dpVal0 = dpVal1 := rfl
private lemma chk_dp2 : dpStepL dpVal1 = dpVal2 := rfl
private lemma chk_dp3 : dpStepL dpVal2 = dpVal3 := rfl
private lemma chk_dp4 : dpStepL dpVal3 = dpVal4 := rfl
private lemma chk_dp5 : dpStepL dpVal4 = dpVal5 := rfl
private lemma chk_dp6 : dpStepL dpVal5 = dpVal6 := rfl
private lemma chk_dp7 : dpStepL dpVal6 = dpVal7 := rfl
private lemma chk_dp8 : dpStepL dpVal7 = dpVal8 := rfl
private lemma chk_dp9 : dpStepL dpVal8 = dpVal9 := rfl
private lemma chk_dp10 : dpStepL dpVal9 = dpVal10 := rfl

private lemma chk_poly_base :
    (List.range 88).all (fun j =>
      (dpVal10.getD j 0 : ℤ) ==
        c0List.getD j 0 + c1List.getD j 0 * 11 + c2List.getD j 0 * 121 + c3List.getD j 0 * 1331) = true := rfl

private lemma chk_poly_step :
    (List.range 88).all (fun j =>
      let c0 := c0List.getD j 0; let c1 := c1List.getD j 0
      let c2 := c2List.getD j 0; let c3 := c3List.getD j 0
      let ps := predsN j
      (c0 + c1 + c2 + c3 == ps.foldl (fun a i => a + c0List.getD i 0) 0) &&
      (c1 + 2 * c2 + 3 * c3 == ps.foldl (fun a i => a + c1List.getD i 0) 0) &&
      (c2 + 3 * c3 == ps.foldl (fun a i => a + c2List.getD i 0) 0) &&
      (c3 == ps.foldl (fun a i => a + c3List.getD i 0) 0)) = true := rfl

set_option maxRecDepth 2000 in
private lemma chk_poly_sums :
    (sumIntL c0List == 757) && (sumIntL c1List == 14) &&
    (sumIntL c2List == -115) && (sumIntL c3List == 24) = true := rfl

set_option maxRecDepth 2000 in
private lemma chk_small_sums :
    (sumNatL dpVal0 == 20) && (sumNatL dpVal1 == 36) &&
    (sumNatL dpVal2 == 130) && (sumNatL dpVal3 == 382) &&
    (sumNatL dpVal4 == 924) && (sumNatL dpVal5 == 1884) &&
    (sumNatL dpVal6 == 3463) && (sumNatL dpVal7 == 5800) &&
    (sumNatL dpVal8 == 9065) && (sumNatL dpVal9 == 13397) = true := rfl

/-! ### Part 7: Generic list helpers and structural properties from the `rfl` checks -/

private lemma list_getD_eq_getElem {α : Type*} (L : List α) (i : ℕ) (d : α) (h : i < L.length) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

private lemma isSortedStrict_lt : ∀ (L : List ℕ), isSortedStrict L = true →
    ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j → L[i] < L[j]
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | [_], _, i, j, hi, hj, hij => by simp at hi hj; omega
  | x :: y :: rest, h, i, j, hi, hj, hij => by
    simp only [isSortedStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        cases j' with
        | zero => exact h.1
        | succ j'' =>
          have h1 := isSortedStrict_lt (y :: rest) h.2 0 (j'' + 1) (by simp) (by simp at hj ⊢; omega) (by omega)
          exact Nat.lt_trans h.1 h1
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        exact isSortedStrict_lt (y :: rest) h.2 i' j' (by simp at hi ⊢; omega) (by simp at hj ⊢; omega) (by omega)

private lemma stateCodeN_injective : Function.Injective (fun i : Fin 88 => stateCodeN i.val) := by
  intro i j hij
  have hi : i.val < stateList.length := by rw [chk_len_state]; exact i.isLt
  have hj : j.val < stateList.length := by rw [chk_len_state]; exact j.isLt
  have h1 : stateCodeN i.val = stateList[i.val]'hi :=
    list_getD_eq_getElem stateList i.val 0 hi
  have h2 : stateCodeN j.val = stateList[j.val]'hj :=
    list_getD_eq_getElem stateList j.val 0 hj
  dsimp only at hij
  rw [h1, h2] at hij
  by_contra hne
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact ne_of_lt (isSortedStrict_lt stateList chk_sorted i.val j.val hi hj hlt) hij
  · exact ne_of_gt (isSortedStrict_lt stateList chk_sorted j.val i.val hj hi hgt) hij

private lemma nodup_of_isNodupB : ∀ (L : List ℕ), isNodupB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [isNodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hx : x ∉ xs := by
      intro hmem
      have h1 : xs.contains x = true := List.contains_iff_mem.mpr hmem
      rw [h1] at h
      exact Bool.false_ne_true h.1.symm
    exact List.nodup_cons.mpr ⟨hx, nodup_of_isNodupB xs h.2⟩

private lemma predsN_nodup (j : Fin 88) : (predsN j.val).Nodup := by
  have hlen : j.val < predsList.length := by rw [chk_len_preds]; exact j.isLt
  have hmem : predsN j.val ∈ predsList := by
    unfold predsN
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    exact List.getElem_mem hlen
  exact nodup_of_isNodupB _ (List.all_eq_true.mp chk_preds_nodup _ hmem)

private lemma predsN_lt (j : Fin 88) (i : ℕ) (hi : i ∈ predsN j.val) : i < 88 := by
  have hlen : j.val < predsList.length := by rw [chk_len_preds]; exact j.isLt
  have hmem : predsN j.val ∈ predsList := by
    unfold predsN
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    exact List.getElem_mem hlen
  have hall := List.all_eq_true.mp chk_preds_bounds _ hmem
  exact of_decide_eq_true (List.all_eq_true.mp hall i hi)

private lemma foldl_add_nat {α : Type*} (L : List α) (f : α → ℕ) (init : ℕ) :
    L.foldl (fun a x => a + f x) init = init + (L.map f).sum := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, Nat.add_assoc]

private lemma foldl_add_int {α : Type*} (L : List α) (f : α → ℤ) (init : ℤ) :
    L.foldl (fun a x => a + f x) init = init + (L.map f).sum := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, add_assoc]

private lemma sumNatL_eq (L : List ℕ) : sumNatL L = L.sum := by
  unfold sumNatL
  simpa using foldl_add_nat L id 0

private lemma sumIntL_eq (L : List ℤ) : sumIntL L = L.sum := by
  unfold sumIntL
  simpa using foldl_add_int L id 0

private lemma list_sum_natCast (L : List ℕ) :
    (L.sum : ℤ) = (L.map (fun x : ℕ => (x : ℤ))).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma sum_toFinset_of_nodup {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup)
    (f : α → ℕ) : (∑ x ∈ L.toFinset, f x) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hL
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using hL.1), ih hL.2]
    simp

private lemma semInitN_closed (r0 r1 : Fin 16) (st : ℕ) (h : semInitN r0.val r1.val = some st) :
    ∃ j : Fin 88, stateCodeN j.val = st := by
  have hmem : st ∈ initSemListN := by
    rw [← chk_init_list, List.mem_flatMap]
    refine ⟨r0.val, List.mem_range.mpr r0.isLt, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨r1.val, List.mem_range.mpr r1.isLt, h⟩
  have hchk := List.all_eq_true.mp chk_init_closed st hmem
  rw [List.any_eq_true] at hchk
  rcases hchk with ⟨j, hjmem, hjeq⟩
  have hjlt : j < 88 := of_decide_eq_true (List.all_eq_true.mp chk_initStates_bounds j hjmem)
  exact ⟨⟨j, hjlt⟩, beq_iff_eq.mp hjeq⟩

private lemma initCount_eq_count (j : Fin 88) :
    initList.getD j.val 0 = initSemListN.count (stateCodeN j.val) := by
  have hlen : j.val < stateList.length := by rw [chk_len_state]; exact j.isLt
  have h := congrArg (fun L => L.getD j.val 0) chk_init_count
  simpa [stateCodeN, List.getD_eq_getElem?_getD, hlen] using h.symm

private lemma count_initSemListN (st : ℕ) :
    initSemListN.count st =
      ((Finset.univ : Finset (Fin 16 × Fin 16)).filter
        (fun p => semInitN p.1.val p.2.val = some st)).card := by
  rw [← chk_init_list]
  have hprod : (Finset.univ : Finset (Fin 16 × Fin 16)) = Finset.univ ×ˢ Finset.univ := rfl
  rw [hprod, Finset.card_filter, Finset.sum_product]
  rw [List.count_flatMap]
  have hrange : ∀ (n : ℕ) (f : ℕ → ℕ),
      ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
    intro n f
    rw [Fin.sum_univ_def]
    congr 1
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2; simp
  rw [hrange 16]
  refine Finset.sum_congr rfl fun r0 _ => ?_
  have hfm : ∀ L : List ℕ,
      (L.filterMap (semInitN r0.val)).count st =
        (L.map fun r1 => if semInitN r0.val r1 = some st then 1 else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons x xs ih =>
      cases hx : semInitN r0.val x with
      | none => simp [hx, ih]
      | some y =>
        by_cases hy : y = st
        · subst hy; simp [hx, ih, Nat.add_comm]
        · have hy' : (y == st) = false := beq_false_of_ne hy
          simp [hx, hy, hy', ih]
  dsimp only [Function.comp_apply]
  rw [hfm (List.range 16), hrange 16]

private lemma semStepN_sound (j : Fin 88) (i : ℕ) (hi : i ∈ predsN j.val) :
    semStepN (stateCodeN i) (stateRowN j.val) = some (stateCodeN j.val) := by
  have hlen1 : j.val < stateList.length := by rw [chk_len_state]; exact j.isLt
  have hlen2 : j.val < predsList.length := by rw [chk_len_preds]; exact j.isLt
  have hzlen : j.val < (List.zipWith (fun code ps =>
      let r := (code / 125) % 16
      ps.all (fun i => semStepN (stateCodeN i) r == some code)) stateList predsList).length := by
    simp [hlen1, hlen2]
  have hmem := List.getElem_mem hzlen
  have hall := List.all_eq_true.mp chk_step_sound _ hmem
  simp only [id_eq, List.getElem_zipWith] at hall
  have hcode : ∀ h : j.val < stateList.length, stateList[j.val]'h = stateCodeN j.val :=
    fun h => (list_getD_eq_getElem stateList j.val 0 h).symm
  have hps : ∀ h : j.val < predsList.length, predsList[j.val]'h = predsN j.val :=
    fun h => (list_getD_eq_getElem predsList j.val [] h).symm
  simp only [hcode, hps] at hall
  exact beq_iff_eq.mp (List.all_eq_true.mp hall i hi)

private lemma semStepN_closed (i : Fin 88) (r : Fin 16) (st : ℕ)
    (h : semStepN (stateCodeN i.val) r.val = some st) :
    ∃ j : Fin 88, stateCodeN j.val = st ∧ i.val ∈ predsN j.val ∧ r.val = stateRowN j.val := by
  have hlen : i.val < stateList.length := by rw [chk_len_state]; exact i.isLt
  have hzlen : i.val < (List.zipWith (fun i code =>
      (List.range 16).all fun r =>
        match semStepN code r with
        | none => true
        | some c => (succsList.getD i []).any (fun j =>
            stateCodeN j == c && (predsN j).contains i && r == stateRowN j))
      (List.range 88) stateList).length := by
    simp [hlen, i.isLt]
  have hmem := List.getElem_mem hzlen
  have hall := List.all_eq_true.mp chk_step_complete _ hmem
  simp only [id_eq, List.getElem_zipWith, List.getElem_range] at hall
  have hcode : ∀ h : i.val < stateList.length, stateList[i.val]'h = stateCodeN i.val :=
    fun h => (list_getD_eq_getElem stateList i.val 0 h).symm
  simp only [hcode] at hall
  have hr := List.all_eq_true.mp hall r.val (List.mem_range.mpr r.isLt)
  rw [h, List.any_eq_true] at hr
  rcases hr with ⟨j, hjmem, hjcond⟩
  have hsuclen : i.val < succsList.length := by rw [chk_len_succs]; exact i.isLt
  have hsucmem : succsList.getD i.val [] ∈ succsList := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsuclen]
    exact List.getElem_mem hsuclen
  have hjlt : j < 88 :=
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp chk_succs_bounds _ hsucmem) j hjmem)
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hjcond
  exact ⟨⟨j, hjlt⟩, hjcond.1.1, hjcond.1.2, hjcond.2⟩

private lemma semStepN_iff_preds (i j : Fin 88) (r : Fin 16) :
    semStepN (stateCodeN i.val) r.val = some (stateCodeN j.val) ↔
      i.val ∈ predsN j.val ∧ r.val = stateRowN j.val := by
  constructor
  · intro h
    obtain ⟨j', hj', hmem, hr⟩ := semStepN_closed i r (stateCodeN j.val) h
    have hjj : j' = j := stateCodeN_injective hj'
    subst hjj
    exact ⟨hmem, hr⟩
  · rintro ⟨hmem, hr⟩
    rw [hr]
    exact semStepN_sound j i.val hmem

private lemma stateRowN_lt (j : Fin 88) : stateRowN j.val < 16 := by
  unfold stateRowN
  exact Nat.mod_lt _ (by decide)

/-! ### Part 8: Bijection between valid arrays and the 88-state DP -/

private abbrev ValidAt (n : ℕ) (j : Fin 88) : Type :=
  { M : Fin (n + 2) → Fin 4 → Fin 2 // IsValidArray (n + 1) M ∧ arrayState M = stateCodeN j.val }

private lemma validArray_in_states :
    ∀ (n : ℕ) (M : Fin (n + 2) → Fin 4 → Fin 2),
      IsValidArray (n + 1) M → ∃ j : Fin 88, arrayState M = stateCodeN j.val
  | 0, M, hM => by
    have hinit := (isValidArray_one_semInit M (arrayState M)).mp ⟨hM, rfl⟩
    obtain ⟨j, hj⟩ := semInitN_closed (encodeRow (M 0)) (encodeRow (M 1)) (arrayState M) hinit
    exact ⟨j, hj.symm⟩
  | n + 1, M, hM => by
    have hM_snoc : M = snocRow (Fin.init M) (M (Fin.last (n + 2))) := (snocRow_init_self M).symm
    rw [hM_snoc] at hM ⊢
    have ⟨hinit, hstep⟩ :=
      (isValidArray_snoc_semStep (Fin.init M) (M (Fin.last (n + 2))) _).mp ⟨hM, rfl⟩
    obtain ⟨i, hi⟩ := validArray_in_states n (Fin.init M) hinit
    rw [hi] at hstep
    obtain ⟨j, hj, _, _⟩ :=
      semStepN_closed i (encodeRow (M (Fin.last (n + 2)))) _ hstep
    exact ⟨j, hj.symm⟩

private def dpVec : ℕ → List ℕ
  | 0 => initList
  | n + 1 => dpStepL (dpVec n)

private lemma dpVec_length : ∀ n : ℕ, (dpVec n).length = 88
  | 0 => chk_len_init
  | n + 1 => by simp [dpVec, dpStepL, chk_len_preds]

private def dp (n : ℕ) (j : Fin 88) : ℕ :=
  (dpVec n).getD j.val 0

private lemma dp_zero (j : Fin 88) : dp 0 j = initList.getD j.val 0 := rfl

private lemma dp_succ (n : ℕ) (j : Fin 88) :
    dp (n + 1) j = ((predsN j.val).map fun i => (dpVec n).getD i 0).sum := by
  have hlen : j.val < predsList.length := by rw [chk_len_preds]; exact j.isLt
  change (dpStepL (dpVec n)).getD j.val 0 = _
  unfold dpStepL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen]
  simp only [Option.map_some, Option.getD_some]
  have hps : predsList[j.val]'hlen = predsN j.val :=
    (list_getD_eq_getElem predsList j.val [] hlen).symm
  rw [hps, foldl_add_nat, zero_add]

private def predsFin (j : Fin 88) : List (Fin 88) :=
  (predsN j.val).attach.map fun ⟨i, hi⟩ => ⟨i, predsN_lt j i hi⟩

private lemma predsFin_nodup (j : Fin 88) : (predsFin j).Nodup := by
  unfold predsFin
  apply List.Nodup.map
  · intro ⟨a, _⟩ ⟨b, _⟩ hab
    apply Subtype.ext
    exact congrArg Fin.val hab
  · exact List.nodup_attach.mpr (predsN_nodup j)

private lemma mem_predsFin_iff (j i : Fin 88) : i ∈ predsFin j ↔ i.val ∈ predsN j.val := by
  unfold predsFin
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨a, ha, h⟩
    have : a = i.val := congrArg Fin.val h
    rwa [← this]
  · intro hi
    exact ⟨i.val, hi, Fin.ext rfl⟩

private lemma sum_predsFin (n : ℕ) (j : Fin 88) :
    (∑ i ∈ (predsFin j).toFinset, dp n i) = dp (n + 1) j := by
  rw [sum_toFinset_of_nodup _ (predsFin_nodup j), dp_succ]
  unfold predsFin
  rw [List.map_map]
  have hcomp : (dp n ∘ fun x : { x // x ∈ predsN j.val } => (⟨x.1, predsN_lt j x.1 x.2⟩ : Fin 88)) =
      fun x => (dpVec n).getD x.1 0 := rfl
  rw [hcomp]
  have hattach : ∀ (L : List ℕ) (f : ℕ → ℕ), (L.attach.map fun x => f x.1) = L.map f := by
    intro L f; simp
  rw [hattach (predsN j.val) (fun i => (dpVec n).getD i 0)]

private lemma nat_card_sigma_fin {ι : Type*} [Fintype ι] (β : ι → Type*) [∀ i, Finite (β i)] :
    Nat.card (Σ i, β i) = ∑ i, Nat.card (β i) := by
  classical
  haveI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite (β i)
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma]

private lemma card_validAt_zero (j : Fin 88) : Nat.card (ValidAt 0 j) = initList.getD j.val 0 := by
  let e1 : ValidAt 0 j ≃
      { p : Fin 16 × Fin 16 // semInitN p.1.val p.2.val = some (stateCodeN j.val) } :=
    { toFun := fun x =>
        ⟨(encodeRow (x.1 0), encodeRow (x.1 1)),
          (isValidArray_one_semInit x.1 (stateCodeN j.val)).mp x.2⟩
      invFun := fun ⟨⟨r0, r1⟩, h⟩ =>
        ⟨![bit4 r0, bit4 r1], by
          have h' : semInitN (encodeRow (![bit4 r0, bit4 r1] 0)).val
              (encodeRow (![bit4 r0, bit4 r1] 1)).val = some (stateCodeN j.val) := by
            simpa [encodeRow_bit4] using h
          exact (isValidArray_one_semInit ![bit4 r0, bit4 r1] (stateCodeN j.val)).mpr h'⟩
      left_inv := fun ⟨M, _, _⟩ => by
        apply Subtype.ext
        funext i
        fin_cases i <;> funext c <;> simp [bit4_encodeRow]
      right_inv := fun ⟨⟨r0, r1⟩, _⟩ => by
        apply Subtype.ext
        dsimp only
        simp [encodeRow_bit4] }
  rw [Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_subtype,
      ← count_initSemListN, ← initCount_eq_count]

private lemma card_validAt_succ (n : ℕ) (j : Fin 88)
    (ih : ∀ i : Fin 88, Nat.card (ValidAt n i) = dp n i) :
    Nat.card (ValidAt (n + 1) j) = dp (n + 1) j := by
  let rj : Fin 16 := ⟨stateRowN j.val, stateRowN_lt j⟩
  let e : ValidAt (n + 1) j ≃ Σ i : (predsFin j).toFinset, ValidAt n i.1 :=
    { toFun := fun x =>
        let hpair : IsValidArray (n + 1) (Fin.init x.1) ∧
            semStepN (arrayState (Fin.init x.1)) (encodeRow (x.1 (Fin.last (n + 2)))).val =
              some (stateCodeN j.val) := by
          have hsnoc : x.1 = snocRow (Fin.init x.1) (x.1 (Fin.last (n + 2))) := (snocRow_init_self x.1).symm
          have hx := x.2
          rw [hsnoc] at hx
          exact (isValidArray_snoc_semStep (Fin.init x.1) (x.1 (Fin.last (n + 2))) (stateCodeN j.val)).mp hx
        let i := Classical.choose (validArray_in_states n (Fin.init x.1) hpair.1)
        have hi : arrayState (Fin.init x.1) = stateCodeN i.val :=
          Classical.choose_spec (validArray_in_states n (Fin.init x.1) hpair.1)
        have hmem : i ∈ (predsFin j).toFinset := by
          rw [List.mem_toFinset, mem_predsFin_iff]
          have hstep := hpair.2
          rw [hi] at hstep
          exact ((semStepN_iff_preds i j _).mp hstep).1
        ⟨⟨i, hmem⟩, ⟨Fin.init x.1, hpair.1, hi⟩⟩
      invFun := fun ⟨⟨i, hmem⟩, ⟨M0, hM0, hi⟩⟩ =>
        ⟨snocRow M0 (bit4 rj), by
          rw [isValidArray_snoc_semStep, hi, encodeRow_bit4]
          have hmem' : i.val ∈ predsN j.val := (mem_predsFin_iff j i).mp (List.mem_toFinset.mp hmem)
          exact ⟨hM0, (semStepN_iff_preds i j rj).mpr ⟨hmem', rfl⟩⟩⟩
      left_inv := fun ⟨M, hM, hst⟩ => by
        apply Subtype.ext
        have hsnoc : M = snocRow (Fin.init M) (M (Fin.last (n + 2))) := (snocRow_init_self M).symm
        have hpair : IsValidArray (n + 1) (Fin.init M) ∧
            semStepN (arrayState (Fin.init M)) (encodeRow (M (Fin.last (n + 2)))).val =
              some (stateCodeN j.val) := by
          rw [hsnoc] at hM hst
          exact (isValidArray_snoc_semStep (Fin.init M) (M (Fin.last (n + 2))) (stateCodeN j.val)).mp
            ⟨hM, hst⟩
        let i := Classical.choose (validArray_in_states n (Fin.init M) hpair.1)
        have hi : arrayState (Fin.init M) = stateCodeN i.val :=
          Classical.choose_spec (validArray_in_states n (Fin.init M) hpair.1)
        have hrow : encodeRow (M (Fin.last (n + 2))) = rj := by
          apply Fin.ext
          have hstep := hpair.2
          rw [hi] at hstep
          exact ((semStepN_iff_preds i j _).mp hstep).2
        dsimp only
        rw [← hrow]
        have hbit : bit4 (encodeRow (M (Fin.last (n + 2)))) = M (Fin.last (n + 2)) :=
          funext (bit4_encodeRow _)
        rw [hbit]
        exact snocRow_init_self M
      right_inv := fun ⟨⟨i, hmem⟩, ⟨M0, hM0, hi⟩⟩ => by
        dsimp only
        have hinit_eq : Fin.init (snocRow M0 (bit4 rj)) = M0 := init_snocRow _ _
        have hi_eq :
            Classical.choose (validArray_in_states n (Fin.init (snocRow M0 (bit4 rj)))
              (by simpa [hinit_eq] using hM0)) = i := by
          apply stateCodeN_injective
          dsimp only
          have hspec := Classical.choose_spec (validArray_in_states n
            (Fin.init (snocRow M0 (bit4 rj))) (by simpa [hinit_eq] using hM0))
          rw [← hspec, hinit_eq, hi]
        have hpair_eq : ∀ (a b : (predsFin j).toFinset) (x : ValidAt n a.1) (y : ValidAt n b.1),
            a = b → x.1 = y.1 →
            (⟨a, x⟩ : Σ k : (predsFin j).toFinset, ValidAt n k.1) = ⟨b, y⟩ := by
          rintro a _ ⟨x, hx⟩ ⟨y, hy⟩ rfl hxy; cases hxy; rfl
        exact hpair_eq _ _ _ _ (Subtype.ext hi_eq) hinit_eq }
  rw [Nat.card_congr e, nat_card_sigma_fin]
  have hsum : (∑ i : (predsFin j).toFinset, Nat.card (ValidAt n i.1)) =
      ∑ i : (predsFin j).toFinset, dp n i.1 :=
    Finset.sum_congr rfl fun i _ => ih i.1
  rw [hsum, Finset.sum_coe_sort (predsFin j).toFinset (dp n), sum_predsFin]

private lemma card_validAt (n : ℕ) (j : Fin 88) : Nat.card (ValidAt n j) = dp n j := by
  induction n generalizing j with
  | zero => rw [dp_zero]; exact card_validAt_zero j
  | succ n ih => exact card_validAt_succ n j ih

private lemma a_succ_eq_sum_dp (n : ℕ) : a (n + 1) = ∑ j : Fin 88, dp n j := by
  classical
  unfold a
  rw [← Nat.card_eq_fintype_card]
  let e : { M : Fin (n + 2) → Fin 4 → Fin 2 // IsValidArray (n + 1) M } ≃
      Σ j : Fin 88, ValidAt n j :=
    { toFun := fun ⟨M, hM⟩ =>
        let j := Classical.choose (validArray_in_states n M hM)
        ⟨j, ⟨M, hM, Classical.choose_spec (validArray_in_states n M hM)⟩⟩
      invFun := fun ⟨_, ⟨M, hM, _⟩⟩ => ⟨M, hM⟩
      left_inv := fun ⟨M, _⟩ => rfl
      right_inv := fun ⟨j, ⟨M, hM, hj⟩⟩ => by
        dsimp only
        have hjeq : Classical.choose (validArray_in_states n M hM) = j := by
          apply stateCodeN_injective
          dsimp only
          rw [← Classical.choose_spec (validArray_in_states n M hM), hj]
        have hpair_eq : ∀ (a b : Fin 88) (x : ValidAt n a) (y : ValidAt n b),
            a = b → x.1 = y.1 → (⟨a, x⟩ : Σ k : Fin 88, ValidAt n k) = ⟨b, y⟩ := by
          rintro a _ ⟨x, hx⟩ ⟨y, hy⟩ rfl hxy; cases hxy; rfl
        exact hpair_eq _ _ _ _ hjeq rfl }
  rw [Nat.card_congr e, nat_card_sigma_fin]
  exact Finset.sum_congr rfl fun j _ => card_validAt n j

private lemma sum_fin_getD_nat (L : List ℕ) (hL : L.length = 88) :
    (∑ j : Fin 88, L.getD j.val 0) = L.sum := by
  rw [Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem
  · simp [hL]
  · intro i hi1 hi2
    simp [list_getD_eq_getElem, hi2]

private lemma sum_fin_getD_int (L : List ℤ) (hL : L.length = 88) :
    (∑ j : Fin 88, L.getD j.val 0) = L.sum := by
  rw [Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem
  · simp [hL]
  · intro i hi1 hi2
    simp [list_getD_eq_getElem, hi2]

private lemma a_succ_eq_dpVec_sum (n : ℕ) : a (n + 1) = (dpVec n).sum := by
  rw [a_succ_eq_sum_dp]
  exact sum_fin_getD_nat (dpVec n) (dpVec_length n)

/-! ### Part 9: Step-by-step DP evaluation & exact cubic polynomial per state for `n ≥ 11` -/

private lemma dpVec_0 : dpVec 0 = dpVal0 := chk_dp0
private lemma dpVec_1 : dpVec 1 = dpVal1 := by rw [dpVec, dpVec_0, chk_dp1]
private lemma dpVec_2 : dpVec 2 = dpVal2 := by rw [dpVec, dpVec_1, chk_dp2]
private lemma dpVec_3 : dpVec 3 = dpVal3 := by rw [dpVec, dpVec_2, chk_dp3]
private lemma dpVec_4 : dpVec 4 = dpVal4 := by rw [dpVec, dpVec_3, chk_dp4]
private lemma dpVec_5 : dpVec 5 = dpVal5 := by rw [dpVec, dpVec_4, chk_dp5]
private lemma dpVec_6 : dpVec 6 = dpVal6 := by rw [dpVec, dpVec_5, chk_dp6]
private lemma dpVec_7 : dpVec 7 = dpVal7 := by rw [dpVec, dpVec_6, chk_dp7]
private lemma dpVec_8 : dpVec 8 = dpVal8 := by rw [dpVec, dpVec_7, chk_dp8]
private lemma dpVec_9 : dpVec 9 = dpVal9 := by rw [dpVec, dpVec_8, chk_dp9]
private lemma dpVec_10 : dpVec 10 = dpVal10 := by rw [dpVec, dpVec_9, chk_dp10]

private def evalPolyN (j : ℕ) (m : ℤ) : ℤ :=
  c0List.getD j 0 + c1List.getD j 0 * m + c2List.getD j 0 * m ^ 2 + c3List.getD j 0 * m ^ 3

private lemma dp_ten_eq_poly (j : Fin 88) : (dp 10 j : ℤ) = evalPolyN j.val 11 := by
  unfold dp evalPolyN
  rw [dpVec_10]
  have h := List.all_eq_true.mp chk_poly_base j.val (List.mem_range.mpr j.isLt)
  have heq := beq_iff_eq.mp h
  rw [heq]; ring

private lemma evalPolyN_succ (j : Fin 88) (m : ℤ) :
    evalPolyN j.val (m + 1) = ((predsN j.val).map fun i => evalPolyN i m).sum := by
  have h := List.all_eq_true.mp chk_poly_step j.val (List.mem_range.mpr j.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq, foldl_add_int, zero_add] at h
  rcases h with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  have hsum : ∀ L : List ℕ,
      (L.map fun i => evalPolyN i m).sum =
        (L.map fun i => c0List.getD i 0).sum +
        (L.map fun i => c1List.getD i 0).sum * m +
        (L.map fun i => c2List.getD i 0).sum * m ^ 2 +
        (L.map fun i => c3List.getD i 0).sum * m ^ 3 := by
    intro L
    induction L with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold evalPolyN
      ring
  rw [hsum (predsN j.val), ← h0, ← h1, ← h2, ← h3]
  unfold evalPolyN
  ring

private lemma dp_ge_ten_eq_poly (k : ℕ) (j : Fin 88) :
    (dp (10 + k) j : ℤ) = evalPolyN j.val (11 + (k : ℤ)) := by
  induction k generalizing j with
  | zero => simpa using dp_ten_eq_poly j
  | succ k ih =>
    rw [show 10 + (k + 1) = (10 + k) + 1 by omega, dp_succ]
    rw [show 11 + ((k + 1 : ℕ) : ℤ) = (11 + (k : ℤ)) + 1 by push_cast; ring]
    rw [evalPolyN_succ, list_sum_natCast, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hilt := predsN_lt j i hi
    exact ih ⟨i, hilt⟩

private lemma sum_evalPolyN (m : ℤ) :
    (∑ j : Fin 88, evalPolyN j.val m) = 757 + 14 * m - 115 * m ^ 2 + 24 * m ^ 3 := by
  have hchk := chk_poly_sums
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, sumIntL_eq] at hchk
  rcases hchk with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  have hsplit : (∑ j : Fin 88, evalPolyN j.val m) =
      (∑ j : Fin 88, c0List.getD j.val 0) +
      (∑ j : Fin 88, c1List.getD j.val 0) * m +
      (∑ j : Fin 88, c2List.getD j.val 0) * m ^ 2 +
      (∑ j : Fin 88, c3List.getD j.val 0) * m ^ 3 := by
    simp only [evalPolyN, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsplit,
    sum_fin_getD_int c0List chk_len_c0,
    sum_fin_getD_int c1List chk_len_c1,
    sum_fin_getD_int c2List chk_len_c2,
    sum_fin_getD_int c3List chk_len_c3,
    h0, h1, h2, h3]
  ring

/-! ### Part 10: Small values, closed form, recurrence, and generating function -/

private lemma small_dpVal_sums :
    dpVal0.sum = 20 ∧ dpVal1.sum = 36 ∧ dpVal2.sum = 130 ∧
    dpVal3.sum = 382 ∧ dpVal4.sum = 924 ∧ dpVal5.sum = 1884 ∧
    dpVal6.sum = 3463 ∧ dpVal7.sum = 5800 ∧ dpVal8.sum = 9065 ∧
    dpVal9.sum = 13397 := by
  have h := chk_small_sums
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, sumNatL_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private lemma a_closed_form (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 757 + 14 * (n : ℤ) - 115 * (n : ℤ) ^ 2 + 24 * (n : ℤ) ^ 3 := by
  by_cases h10 : n = 10
  · subst h10
    have h := a_succ_eq_dpVec_sum 9
    rw [dpVec_9, small_dpVal_sums.2.2.2.2.2.2.2.2.2] at h
    rw [h]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 11 + k := ⟨n - 11, by omega⟩
    have h := a_succ_eq_sum_dp (10 + k)
    have hcast : (a (11 + k) : ℤ) = ∑ j : Fin 88, (dp (10 + k) j : ℤ) := by
      rw [show 11 + k = (10 + k) + 1 by omega, h]
      push_cast; rfl
    rw [hcast]
    have hpt : (∑ j : Fin 88, (dp (10 + k) j : ℤ)) = ∑ j : Fin 88, evalPolyN j.val (11 + (k : ℤ)) :=
      Finset.sum_congr rfl fun j _ => dp_ge_ten_eq_poly k j
    rw [hpt, sum_evalPolyN]
    push_cast; ring

private lemma a_recurrence (n : ℕ) (hn : 13 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h0 := a_closed_form n (by omega)
  have h1 := a_closed_form (n - 1) (by omega)
  have h2 := a_closed_form (n - 2) (by omega)
  have h3 := a_closed_form (n - 3) (by omega)
  have h4 := a_closed_form (n - 4) (by omega)
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  rw [h0, h1, h2, h3, h4, c1, c2, c3, c4]
  ring

private lemma a_small_vals :
    a 1 = 20 ∧ a 2 = 36 ∧ a 3 = 130 ∧ a 4 = 382 ∧ a 5 = 924 ∧
    a 6 = 1884 ∧ a 7 = 3463 ∧ a 8 = 5800 ∧ a 9 = 9065 ∧ a 10 = 13397 ∧
    a 11 = 18940 ∧ a 12 = 25837 ∧ a 13 = 34232 := by
  have hs := small_dpVal_sums
  have h11 : (a 11 : ℤ) = 18940 := by rw [a_closed_form 11 (by omega)]; norm_num
  have h12 : (a 12 : ℤ) = 25837 := by rw [a_closed_form 12 (by omega)]; norm_num
  have h13 : (a 13 : ℤ) = 34232 := by rw [a_closed_form 13 (by omega)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · rw [a_succ_eq_dpVec_sum 0, dpVec_0, hs.1]
  · rw [a_succ_eq_dpVec_sum 1, dpVec_1, hs.2.1]
  · rw [a_succ_eq_dpVec_sum 2, dpVec_2, hs.2.2.1]
  · rw [a_succ_eq_dpVec_sum 3, dpVec_3, hs.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 4, dpVec_4, hs.2.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 5, dpVec_5, hs.2.2.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 6, dpVec_6, hs.2.2.2.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 7, dpVec_7, hs.2.2.2.2.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 8, dpVec_8, hs.2.2.2.2.2.2.2.2.1]
  · rw [a_succ_eq_dpVec_sum 9, dpVec_9, hs.2.2.2.2.2.2.2.2.2]

private lemma series_eq :
    (1 - X) ^ 4 * series =
      X * (20 - 44 * X + 106 * X ^ 2 - 2 * X ^ 3 + 52 * X ^ 4 - 4 * X ^ 5 +
           73 * X ^ 6 - 62 * X ^ 7 + 31 * X ^ 8 - 31 * X ^ 9 + 5 * X ^ 10 -
           X ^ 11 + X ^ 12) := by
  have hlhs : (1 - X) ^ 4 * series =
      series - C 4 * (X ^ 1 * series) + C 6 * (X ^ 2 * series) -
        C 4 * (X ^ 3 * series) + X ^ 4 * series := by
    simp only [map_ofNat]
    ring
  have hrhs :
      (X : PowerSeries ℚ) * (20 - 44 * X + 106 * X ^ 2 - 2 * X ^ 3 + 52 * X ^ 4 - 4 * X ^ 5 +
           73 * X ^ 6 - 62 * X ^ 7 + 31 * X ^ 8 - 31 * X ^ 9 + 5 * X ^ 10 -
           X ^ 11 + X ^ 12) =
      C 20 * X ^ 1 - C 44 * X ^ 2 + C 106 * X ^ 3 - C 2 * X ^ 4 + C 52 * X ^ 5 -
        C 4 * X ^ 6 + C 73 * X ^ 7 - C 62 * X ^ 8 + C 31 * X ^ 9 - C 31 * X ^ 10 +
        C 5 * X ^ 11 - C 1 * X ^ 12 + C 1 * X ^ 13 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_C_mul_X_pow, coeff_X_pow, series, coeff_mk]
  have hv := a_small_vals
  rcases hv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  by_cases hk : 13 < k
  · have hrec : (a k : ℚ) =
        4 * (a (k - 1) : ℚ) - 6 * (a (k - 2) : ℚ) + 4 * (a (k - 3) : ℚ) - (a (k - 4) : ℚ) := by
      exact_mod_cast a_recurrence k hk
    have hk0 : k ≠ 0 := by omega
    have hk1 : k - 1 ≠ 0 := by omega
    have hk2 : k - 2 ≠ 0 := by omega
    have hk3 : k - 3 ≠ 0 := by omega
    have hk4 : k - 4 ≠ 0 := by omega
    have hge1 : 1 ≤ k := by omega
    have hge2 : 2 ≤ k := by omega
    have hge3 : 3 ≤ k := by omega
    have hge4 : 4 ≤ k := by omega
    have hne : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 4 ∧ k ≠ 5 ∧ k ≠ 6 ∧ k ≠ 7 ∧ k ≠ 8 ∧
        k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by omega
    simp only [hk0, hk1, hk2, hk3, hk4, hge1, hge2, hge3, hge4,
      hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.2.2.2.2, ↓reduceIte]
    linarith
  · have hk' : k ≤ 13 := by omega
    interval_cases k <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] <;> norm_num

end OMA.S_oeis_a184065_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a184065.main :=
  ⟨OMA.S_oeis_a184065_Proof.series_eq,
   OMA.S_oeis_a184065_Proof.a_closed_form,
   OMA.S_oeis_a184065_Proof.a_recurrence⟩
