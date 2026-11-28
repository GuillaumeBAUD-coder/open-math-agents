import OMAStatements.S_oeis_a159227

-- Credit: @Dariusthedoggie
-- Proof: 2x2 subsquares summing to 27 force all entries to be 2-period-coupled in {1,4,9,16} or {4,4,9,10}; alternating column-pair parity yields an order-5 linear recurrence and g.f.

namespace OMA.P159227

open PowerSeries OMA.S_oeis_a159227

/-! ### Part 1: Allowed squares in a 2 X 2 sum to 27 -/

def sq5 : Fin 5 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 16
  | ⟨4, _⟩ => 25

lemma isSquare_le27 {v : ℕ} (hv : isSquare v) (hle : v ≤ 27) :
    v = 0 ∨ v = 1 ∨ v = 4 ∨ v = 9 ∨ v = 16 ∨ v = 25 := by
  obtain ⟨k, _, rfl⟩ := hv
  have hk : k ≤ 5 := by nlinarith
  interval_cases k <;> omega

lemma not_four_of_sum27 {a b c d : ℕ}
    (ha : isSquare a) (hb : isSquare b) (hc : isSquare c) (hd : isSquare d)
    (hsum : a + b + c + d = 27) :
    ∃ k : Fin 5, a = sq5 k := by
  have ha' := isSquare_le27 ha (by omega)
  have hb' := isSquare_le27 hb (by omega)
  have hc' := isSquare_le27 hc (by omega)
  have hd' := isSquare_le27 hd (by omega)
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exfalso
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

lemma entry_in_sq5 {n : ℕ} (hn : 2 ≤ n) (x : Fin n → Fin n → Fin 28) (hx : isValid x)
    (i j : Fin n) : ∃ k : Fin 5, (x i j : ℕ) = sq5 k := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · exact not_four_of_sum27 (hx.1 i j) (hx.1 i ⟨j.1 + 1, hj⟩)
        (hx.1 ⟨i.1 + 1, hi⟩ j) (hx.1 ⟨i.1 + 1, hi⟩ ⟨j.1 + 1, hj⟩)
        (hx.2 i.1 j.1 hi hj)
    · have hj' : (j : ℕ) - 1 + 1 < n := by omega
      have hsum := hx.2 i.1 (j.1 - 1) hi hj'
      have hjEq : (⟨(j : ℕ) - 1 + 1, hj'⟩ : Fin n) = j := by ext; dsimp; omega
      have hiEta : (⟨i.1, by omega⟩ : Fin n) = i := rfl
      rw [hjEq, hiEta] at hsum
      exact not_four_of_sum27 (hx.1 i j) (hx.1 i ⟨j.1 - 1, by omega⟩)
        (hx.1 ⟨i.1 + 1, hi⟩ ⟨j.1 - 1, by omega⟩) (hx.1 ⟨i.1 + 1, hi⟩ j) (by omega)
  · have hi' : (i : ℕ) - 1 + 1 < n := by omega
    have hiEq : (⟨(i : ℕ) - 1 + 1, hi'⟩ : Fin n) = i := by ext; dsimp; omega
    by_cases hj : (j : ℕ) + 1 < n
    · have hsum := hx.2 (i.1 - 1) j.1 hi' hj
      have hjEta : (⟨j.1, by omega⟩ : Fin n) = j := rfl
      rw [hiEq, hjEta] at hsum
      exact not_four_of_sum27 (hx.1 i j) (hx.1 ⟨i.1 - 1, by omega⟩ j)
        (hx.1 ⟨i.1 - 1, by omega⟩ ⟨j.1 + 1, hj⟩) (hx.1 i ⟨j.1 + 1, hj⟩) (by omega)
    · have hj' : (j : ℕ) - 1 + 1 < n := by omega
      have hjEq : (⟨(j : ℕ) - 1 + 1, hj'⟩ : Fin n) = j := by ext; dsimp; omega
      have hsum := hx.2 (i.1 - 1) (j.1 - 1) hi' hj'
      rw [hiEq, hjEq] at hsum
      exact not_four_of_sum27 (hx.1 i j) (hx.1 ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩)
        (hx.1 ⟨i.1 - 1, by omega⟩ j) (hx.1 i ⟨j.1 - 1, by omega⟩) (by omega)

/-! ### Part 2: Local 3 X 3 rigidity and global dichotomy -/

def isSq5Bool (v : ℕ) : Bool :=
  v == 0 || v == 1 || v == 9 || v == 16 || v == 25

def ok3x3 (a00 a01 a02 a10 a20 : Fin 5) : Bool :=
  let s00 := sq5 a00; let s01 := sq5 a01; let s02 := sq5 a02
  let s10 := sq5 a10; let s20 := sq5 a20
  if s00 + s01 + s10 ≤ 27 then
    let s11 := 27 - s00 - s01 - s10
    if isSq5Bool s11 && s01 + s02 + s11 ≤ 27 && s10 + s11 + s20 ≤ 27 then
      let s12 := 27 - s01 - s02 - s11
      let s21 := 27 - s10 - s11 - s20
      if isSq5Bool s12 && isSq5Bool s21 && s11 + s12 + s21 ≤ 27 then
        let s22 := 27 - s11 - s12 - s21
        if isSq5Bool s22 then
          (a00 == a02) || (a00 == a20)
        else true
      else true
    else true
  else true

lemma ok3x3_all : ∀ a00 a01 a02 a10 a20 : Fin 5, ok3x3 a00 a01 a02 a10 a20 = true := by
  decide +kernel

lemma isSq5Bool_sq5 (k : Fin 5) : isSq5Bool (sq5 k) = true := by
  fin_cases k <;> rfl

lemma local_3x3_per2 {n : ℕ} (x : Fin n → Fin n → Fin 28) (hx : isValid x)
    (i j : ℕ) (hi : i + 2 < n) (hj : j + 2 < n) :
    x ⟨i, by omega⟩ ⟨j, by omega⟩ = x ⟨i, by omega⟩ ⟨j + 2, hj⟩ ∨
    x ⟨i, by omega⟩ ⟨j, by omega⟩ = x ⟨i + 2, hi⟩ ⟨j, by omega⟩ := by
  have hn : 2 ≤ n := by omega
  obtain ⟨a00, h00⟩ := entry_in_sq5 hn x hx ⟨i, by omega⟩ ⟨j, by omega⟩
  obtain ⟨a01, h01⟩ := entry_in_sq5 hn x hx ⟨i, by omega⟩ ⟨j + 1, by omega⟩
  obtain ⟨a02, h02⟩ := entry_in_sq5 hn x hx ⟨i, by omega⟩ ⟨j + 2, hj⟩
  obtain ⟨a10, h10⟩ := entry_in_sq5 hn x hx ⟨i + 1, by omega⟩ ⟨j, by omega⟩
  obtain ⟨a11, h11⟩ := entry_in_sq5 hn x hx ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩
  obtain ⟨a12, h12⟩ := entry_in_sq5 hn x hx ⟨i + 1, by omega⟩ ⟨j + 2, hj⟩
  obtain ⟨a20, h20⟩ := entry_in_sq5 hn x hx ⟨i + 2, hi⟩ ⟨j, by omega⟩
  obtain ⟨a21, h21⟩ := entry_in_sq5 hn x hx ⟨i + 2, hi⟩ ⟨j + 1, by omega⟩
  obtain ⟨a22, h22⟩ := entry_in_sq5 hn x hx ⟨i + 2, hi⟩ ⟨j + 2, hj⟩
  have hb00 := hx.2 i j (by omega) (by omega)
  have hb01 := hx.2 i (j + 1) (by omega) hj
  have hb10 := hx.2 (i + 1) j hi (by omega)
  have hb11 := hx.2 (i + 1) (j + 1) hi hj
  rw [h00, h01, h10, h11] at hb00
  rw [h01, h02, h11, h12] at hb01
  rw [h10, h11, h20, h21] at hb10
  rw [h11, h12, h21, h22] at hb11
  have hok := ok3x3_all a00 a01 a02 a10 a20
  unfold ok3x3 at hok
  have hc1 : sq5 a00 + sq5 a01 + sq5 a10 ≤ 27 := by omega
  have hs11 : 27 - sq5 a00 - sq5 a01 - sq5 a10 = sq5 a11 := by omega
  have hc2 : sq5 a01 + sq5 a02 + sq5 a11 ≤ 27 := by omega
  have hc3 : sq5 a10 + sq5 a11 + sq5 a20 ≤ 27 := by omega
  have hs12 : 27 - sq5 a01 - sq5 a02 - sq5 a11 = sq5 a12 := by omega
  have hs21 : 27 - sq5 a10 - sq5 a11 - sq5 a20 = sq5 a21 := by omega
  have hc4 : sq5 a11 + sq5 a12 + sq5 a21 ≤ 27 := by omega
  have hs22 : 27 - sq5 a11 - sq5 a12 - sq5 a21 = sq5 a22 := by omega
  simp only [hc1, ↓reduceIte, hs11, isSq5Bool_sq5, hc2, hc3, hs12, hs21, hc4, hs22,
    Bool.and_self, Bool.true_and, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  rcases hok with rfl | rfl
  · left; exact Fin.ext (h00.trans h02.symm)
  · right; exact Fin.ext (h00.trans h20.symm)

def isRowPer2 {n : ℕ} (x : Fin n → Fin n → Fin 28) : Prop :=
  ∀ (i j : ℕ) (hi : i < n) (hj : j + 2 < n),
    x ⟨i, hi⟩ ⟨j, by omega⟩ = x ⟨i, hi⟩ ⟨j + 2, hj⟩

def isColPer2 {n : ℕ} (x : Fin n → Fin n → Fin 28) : Prop :=
  ∀ (i j : ℕ) (hi : i + 2 < n) (hj : j < n),
    x ⟨i, by omega⟩ ⟨j, hj⟩ = x ⟨i + 2, hi⟩ ⟨j, hj⟩

instance {n : ℕ} (x : Fin n → Fin n → Fin 28) : Decidable (isRowPer2 x) := by
  unfold isRowPer2
  exact decidable_of_iff
    (∀ i j : Fin n, ∀ hj : (j : ℕ) + 2 < n, x i j = x i ⟨(j : ℕ) + 2, hj⟩)
    ⟨fun h i j hi hj => h ⟨i, hi⟩ ⟨j, by omega⟩ hj,
     fun h i j hj => h i.1 j.1 i.isLt hj⟩

instance {n : ℕ} (x : Fin n → Fin n → Fin 28) : Decidable (isColPer2 x) := by
  unfold isColPer2
  exact decidable_of_iff
    (∀ i j : Fin n, ∀ hi : (i : ℕ) + 2 < n, x i j = x ⟨(i : ℕ) + 2, hi⟩ j)
    ⟨fun h i j hi hj => h ⟨i, by omega⟩ ⟨j, hj⟩ hi,
     fun h i j hi => h i.1 j.1 hi j.isLt⟩

lemma row_per2_propagate {n : ℕ} (x : Fin n → Fin n → Fin 28) (hx : isValid x)
    (j : ℕ) (hj : j + 2 < n) (i1 i2 : ℕ) (hi1 : i1 < n) (hi2 : i2 < n) :
    x ⟨i1, hi1⟩ ⟨j, by omega⟩ = x ⟨i1, hi1⟩ ⟨j + 2, hj⟩ ↔
    x ⟨i2, hi2⟩ ⟨j, by omega⟩ = x ⟨i2, hi2⟩ ⟨j + 2, hj⟩ := by
  have hstep : ∀ i : ℕ, ∀ hi : i + 1 < n,
      (x ⟨i, by omega⟩ ⟨j, by omega⟩ = x ⟨i, by omega⟩ ⟨j + 2, hj⟩ ↔
       x ⟨i + 1, hi⟩ ⟨j, by omega⟩ = x ⟨i + 1, hi⟩ ⟨j + 2, hj⟩) := by
    intro i hi
    have h1 := hx.2 i j hi (by omega)
    have h2 := hx.2 i (j + 1) hi hj
    have he : (⟨j + 1 + 1, hj⟩ : Fin n) = ⟨j + 2, hj⟩ := rfl
    rw [he] at h2
    constructor <;> intro h
    · exact Fin.ext (by have hv := congrArg Fin.val h; omega)
    · exact Fin.ext (by have hv := congrArg Fin.val h; omega)
  have hzero : ∀ i : ℕ, ∀ hi : i < n,
      (x ⟨0, by omega⟩ ⟨j, by omega⟩ = x ⟨0, by omega⟩ ⟨j + 2, hj⟩ ↔
       x ⟨i, hi⟩ ⟨j, by omega⟩ = x ⟨i, hi⟩ ⟨j + 2, hj⟩) := by
    intro i
    induction i with
    | zero => intro _; exact Iff.rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (hstep i hi)
  exact (hzero i1 hi1).symm.trans (hzero i2 hi2)

lemma col_per2_propagate {n : ℕ} (x : Fin n → Fin n → Fin 28) (hx : isValid x)
    (i : ℕ) (hi : i + 2 < n) (j1 j2 : ℕ) (hj1 : j1 < n) (hj2 : j2 < n) :
    x ⟨i, by omega⟩ ⟨j1, hj1⟩ = x ⟨i + 2, hi⟩ ⟨j1, hj1⟩ ↔
    x ⟨i, by omega⟩ ⟨j2, hj2⟩ = x ⟨i + 2, hi⟩ ⟨j2, hj2⟩ := by
  have hstep : ∀ j : ℕ, ∀ hj : j + 1 < n,
      (x ⟨i, by omega⟩ ⟨j, by omega⟩ = x ⟨i + 2, hi⟩ ⟨j, by omega⟩ ↔
       x ⟨i, by omega⟩ ⟨j + 1, hj⟩ = x ⟨i + 2, hi⟩ ⟨j + 1, hj⟩) := by
    intro j hj
    have h1 := hx.2 i j (by omega) hj
    have h2 := hx.2 (i + 1) j hi hj
    have he : (⟨i + 1 + 1, hi⟩ : Fin n) = ⟨i + 2, hi⟩ := rfl
    rw [he] at h2
    constructor <;> intro h
    · exact Fin.ext (by have hv := congrArg Fin.val h; omega)
    · exact Fin.ext (by have hv := congrArg Fin.val h; omega)
  have hzero : ∀ j : ℕ, ∀ hj : j < n,
      (x ⟨i, by omega⟩ ⟨0, by omega⟩ = x ⟨i + 2, hi⟩ ⟨0, by omega⟩ ↔
       x ⟨i, by omega⟩ ⟨j, hj⟩ = x ⟨i + 2, hi⟩ ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero => intro _; exact Iff.rfl
    | succ j ih => intro hj; exact (ih (by omega)).trans (hstep j hj)
  exact (hzero j1 hj1).symm.trans (hzero j2 hj2)

lemma valid_rowPer2_or_colPer2 {n : ℕ} (x : Fin n → Fin n → Fin 28) (hx : isValid x) :
    isRowPer2 x ∨ isColPer2 x := by
  by_contra h
  push Not at h
  obtain ⟨hr, hc⟩ := h
  unfold isRowPer2 at hr
  unfold isColPer2 at hc
  push Not at hr hc
  obtain ⟨i0, j0, hi0, hj0, hne_r⟩ := hr
  obtain ⟨i1, j1, hi1, hj1, hne_c⟩ := hc
  have hne1 : x ⟨i1, by omega⟩ ⟨j0, by omega⟩ ≠ x ⟨i1, by omega⟩ ⟨j0 + 2, hj0⟩ := by
    intro heq
    exact hne_r ((row_per2_propagate x hx j0 hj0 i0 i1 hi0 (by omega)).mpr heq)
  have hne2 : x ⟨i1, by omega⟩ ⟨j0, by omega⟩ ≠ x ⟨i1 + 2, hi1⟩ ⟨j0, by omega⟩ := by
    intro heq
    exact hne_c ((col_per2_propagate x hx i1 hi1 j1 j0 hj1 (by omega)).mpr heq)
  rcases local_3x3_per2 x hx i1 j0 hi1 hj0 with h1 | h2
  · exact hne1 h1
  · exact hne2 h2

/-! ### Part 3: Inclusion-Exclusion and exact count of `RowPer2` -/

lemma isValid_transpose {n : ℕ} (x : Fin n → Fin n → Fin 28) :
    isValid (fun i j => x j i) ↔ isValid x := by
  unfold isValid
  constructor <;> rintro ⟨h1, h2⟩
  · refine ⟨fun i j => h1 j i, fun i j hi hj => ?_⟩
    have h := h2 j i hj hi; dsimp only at h ⊢; omega
  · refine ⟨fun i j => h1 j i, fun i j hi hj => ?_⟩
    have h := h2 j i hj hi; dsimp only at h ⊢; omega

def rowPer2Card (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 => isValid x ∧ isRowPer2 x)).card

def bothPer2Card (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 =>
    isValid x ∧ isRowPer2 x ∧ isColPer2 x)).card

lemma total_eq_ie (n : ℕ) :
    total n + bothPer2Card n = 2 * rowPer2Card n := by
  let S := Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 => isValid x ∧ isRowPer2 x)
  let T := Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 => isValid x ∧ isColPer2 x)
  have hunion : S ∪ T = Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 => isValid x) := by
    ext x
    simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases valid_rowPer2_or_colPer2 x hx with hr | hc
      · exact Or.inl ⟨hx, hr⟩
      · exact Or.inr ⟨hx, hc⟩
  have hinter : S ∩ T = Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 =>
      isValid x ∧ isRowPer2 x ∧ isColPer2 x) := by
    ext x
    simp only [S, T, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hTcard : T.card = S.card := by
    let e : (Fin n → Fin n → Fin 28) ≃ (Fin n → Fin n → Fin 28) :=
      { toFun := fun x i j => x j i
        invFun := fun x i j => x j i
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨(isValid_transpose x).mpr hx.1, fun i j hi hj => hx.2 j i hj hi⟩
    · intro x1 _ x2 _ h; exact e.injective h
    · intro y hy
      refine ⟨e y, ?_, rfl⟩
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨(isValid_transpose y).mpr hy.1, fun i j hi hj => hy.2 j i hj hi⟩
  have hie := Finset.card_union_add_card_inter S T
  rw [hunion, hinter, hTcard] at hie
  dsimp only [S] at hie
  unfold total rowPer2Card bothPer2Card
  omega

lemma per2_mod2 {n : ℕ} (f : Fin n → Fin 28) (hn : 2 ≤ n)
    (hp : ∀ (k : ℕ) (hk : k + 2 < n), f ⟨k, by omega⟩ = f ⟨k + 2, hk⟩) :
    ∀ k : Fin n, f k = f ⟨(k : ℕ) % 2, by omega⟩ := by
  intro ⟨k, hk⟩
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h2 : k < 2
    · have hmod : k % 2 = k := Nat.mod_eq_of_lt h2
      congr 1; ext; exact hmod.symm
    · have hlt : k - 2 < k := by omega
      have hstep := hp (k - 2) (by omega)
      have h1 : (⟨k - 2 + 2, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
      rw [h1] at hstep
      rw [← hstep, ih (k - 2) hlt (by omega)]
      congr 1; ext; simp; omega

lemma bothPer2Card_eq (n : ℕ) (hn : 2 ≤ n) : bothPer2Card n = 28 := by
  -- Bijection with valid 2 X 2 blocks over Fin 5
  let B := {b : Fin 5 × Fin 5 × Fin 5 × Fin 5 //
    sq5 b.1 + sq5 b.2.1 + sq5 b.2.2.1 + sq5 b.2.2.2 = 27}
  have hB : Fintype.card B = 28 := by
    let sum5 (f : Fin 5 → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3 + f 4
    have hsum5 : ∀ f : Fin 5 → ℕ, ∑ x : Fin 5, f x = sum5 f := fun f => by
      simp [Fin.sum_univ_five, sum5]
    rw [Fintype.card_subtype, Finset.card_filter]
    simp_rw [Fintype.sum_prod_type, hsum5]
    decide +kernel
  rw [← hB]
  unfold bothPer2Card
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  have hsq5_lt : ∀ k : Fin 5, sq5 k < 28 := by intro k; fin_cases k <;> decide
  have hsq5_sq : ∀ k : Fin 5, isSquare (sq5 k) := by
    intro k; fin_cases k
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨5, by decide⟩
  have hsq5_inj : Function.Injective sq5 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [sq5]
  have choose_eq : ∀ {y : ℕ} (h : ∃ k : Fin 5, y = sq5 k) (k : Fin 5),
      y = sq5 k → Classical.choose h = k := by
    intro y h k hy
    exact hsq5_inj ((Classical.choose_spec h).symm.trans hy)
  refine Equiv.symm
    { toFun := fun ⟨⟨a, b, c, d⟩, hsum⟩ =>
        ⟨fun i j =>
          if (i : ℕ) % 2 = 0 then
            if (j : ℕ) % 2 = 0 then ⟨sq5 a, hsq5_lt a⟩ else ⟨sq5 b, hsq5_lt b⟩
          else
            if (j : ℕ) % 2 = 0 then ⟨sq5 c, hsq5_lt c⟩ else ⟨sq5 d, hsq5_lt d⟩,
         by
          dsimp only at hsum
          refine ⟨⟨fun i j => ?_, fun i j hi hj => ?_⟩,
            fun i j hi hj => ?_, fun i j hi hj => ?_⟩
          · dsimp only; split_ifs <;> exact hsq5_sq _
          · by_cases hi2 : i % 2 = 0 <;> by_cases hj2 : j % 2 = 0
            · have hi2' : (i + 1) % 2 ≠ 0 := by omega
              have hj2' : (j + 1) % 2 ≠ 0 := by omega
              dsimp only; simp only [hi2, hj2, hi2', hj2', ↓reduceIte, Fin.val_mk]; omega
            · have hi2' : (i + 1) % 2 ≠ 0 := by omega
              have hj2' : (j + 1) % 2 = 0 := by omega
              dsimp only; simp only [hi2, hj2, hi2', hj2', ↓reduceIte, Fin.val_mk]; omega
            · have hi2' : (i + 1) % 2 = 0 := by omega
              have hj2' : (j + 1) % 2 ≠ 0 := by omega
              dsimp only; simp only [hi2, hj2, hi2', hj2', ↓reduceIte, Fin.val_mk]; omega
            · have hi2' : (i + 1) % 2 = 0 := by omega
              have hj2' : (j + 1) % 2 = 0 := by omega
              dsimp only; simp only [hi2, hj2, hi2', hj2', ↓reduceIte, Fin.val_mk]; omega
          · simp [show (j + 2) % 2 = j % 2 by omega]
          · simp [show (i + 2) % 2 = i % 2 by omega]⟩
      invFun := fun ⟨x, hx, _, _⟩ =>
        let a := Classical.choose (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨0, by omega⟩)
        let b := Classical.choose (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨1, by omega⟩)
        let c := Classical.choose (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨0, by omega⟩)
        let d := Classical.choose (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨1, by omega⟩)
        ⟨(a, b, c, d), by
          have ha := Classical.choose_spec (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨0, by omega⟩)
          have hb := Classical.choose_spec (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨1, by omega⟩)
          have hc := Classical.choose_spec (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨0, by omega⟩)
          have hd := Classical.choose_spec (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨1, by omega⟩)
          have h00 := hx.2 0 0 (by omega) (by omega)
          simp only [Nat.zero_add] at h00
          dsimp only [a, b, c, d]
          rw [← ha, ← hb, ← hc, ← hd]
          exact h00⟩
      left_inv := by
        rintro ⟨⟨a, b, c, d⟩, hsum⟩
        apply Subtype.ext
        apply Prod.ext
        · dsimp only; apply choose_eq; rfl
        · apply Prod.ext
          · dsimp only; apply choose_eq; rfl
          · apply Prod.ext
            · dsimp only; apply choose_eq; rfl
            · dsimp only; apply choose_eq; rfl
      right_inv := by
        rintro ⟨x, hx, hr, hc⟩
        apply Subtype.ext
        funext i j
        dsimp only
        have ha := Classical.choose_spec (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨0, by omega⟩)
        have hb := Classical.choose_spec (entry_in_sq5 hn x hx ⟨0, by omega⟩ ⟨1, by omega⟩)
        have hc' := Classical.choose_spec (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨0, by omega⟩)
        have hd := Classical.choose_spec (entry_in_sq5 hn x hx ⟨1, by omega⟩ ⟨1, by omega⟩)
        have hrow := per2_mod2 (fun k => x i k) hn (fun k hk => hr i.1 k i.isLt hk) j
        have hcol := per2_mod2 (fun k => x k ⟨(j : ℕ) % 2, by omega⟩) hn
          (fun k hk => hc k ((j : ℕ) % 2) hk (by omega)) i
        have hmod : x i j = x ⟨(i : ℕ) % 2, by omega⟩ ⟨(j : ℕ) % 2, by omega⟩ :=
          hrow.trans hcol
        rw [hmod]
        by_cases hi2 : (i : ℕ) % 2 = 0 <;> by_cases hj2 : (j : ℕ) % 2 = 0
        · simp only [hi2, hj2, ↓reduceIte]; exact Fin.ext ha.symm
        · have hj1 : (j : ℕ) % 2 = 1 := by omega
          simp only [hi2, hj2, hj1, ↓reduceIte]; exact Fin.ext hb.symm
        · have hi1 : (i : ℕ) % 2 = 1 := by omega
          simp only [hi2, hi1, hj2, ↓reduceIte]; exact Fin.ext hc'.symm
        · have hi1 : (i : ℕ) % 2 = 1 := by omega
          have hj1 : (j : ℕ) % 2 = 1 := by omega
          simp only [hi2, hi1, hj2, hj1, ↓reduceIte]; exact Fin.ext hd.symm }

/-! ### Part 4: Exact count of `RowPer2` via row-pair sum fibers -/

def pairsWithSum (s : ℕ) : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun p : Fin 5 × Fin 5 => sq5 p.1 + sq5 p.2 = s)

def validSums : Finset ℕ := {1, 2, 9, 10, 17, 18, 25, 26}

def isValidSumBool (s : ℕ) : Bool :=
  s == 1 || s == 2 || s == 9 || s == 10 || s == 17 || s == 18 || s == 25 || s == 26

lemma isValidSumBool_ok :
    ∀ a b c d : Fin 5, sq5 a + sq5 b + sq5 c + sq5 d = 27 → isValidSumBool (sq5 a + sq5 b) = true := by
  decide +kernel

lemma sum_mem_validSums (a b c d : Fin 5) (h : sq5 a + sq5 b + sq5 c + sq5 d = 27) :
    sq5 a + sq5 b ∈ validSums := by
  have hb := isValidSumBool_ok a b c d h
  simp only [isValidSumBool, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with ((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1 <;> simp [validSums, h1]

lemma pairsWithSum_card_eq (s : ℕ) :
    (pairsWithSum s).card =
      let sum5 (f : Fin 5 → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3 + f 4
      sum5 fun a => sum5 fun b => if sq5 a + sq5 b = s then 1 else 0 := by
  unfold pairsWithSum
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_five]

lemma pairsWithSum_cards :
    (pairsWithSum 1).card = 2 ∧ (pairsWithSum 26).card = 2 ∧
    (pairsWithSum 2).card = 1 ∧ (pairsWithSum 25).card = 4 ∧
    (pairsWithSum 9).card = 2 ∧ (pairsWithSum 18).card = 1 ∧
    (pairsWithSum 10).card = 2 ∧ (pairsWithSum 17).card = 2 := by
  simp only [pairsWithSum_card_eq]
  decide +kernel

lemma card_even_odd (n : ℕ) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0)).card = (n + 1) / 2 ∧
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 ≠ 0)).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) % 2 = 0)).card =
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0)).card +
        (if n % 2 = 0 then 1 else 0) := by
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
      simp
    have h2 : (Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) % 2 ≠ 0)).card =
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 ≠ 0)).card +
        (if n % 2 ≠ 0 then 1 else 0) := by
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
      simp
    exact ⟨by have := ih.1; split_ifs at h1 <;> omega, by have := ih.2; split_ifs at h2 <;> omega⟩

lemma rowPer2Card_eq (n : ℕ) (hn : 2 ≤ n) :
    rowPer2Card n =
      4 * 2 ^ n + 4 ^ (n / 2) + 4 ^ ((n + 1) / 2) + 2 ^ (n / 2) + 2 ^ ((n + 1) / 2) := by
  -- Bijection with sequences `f : Fin n → Fin 5 × Fin 5` with adjacent pair sums = 27
  let P := Finset.univ.filter (fun f : Fin n → Fin 5 × Fin 5 =>
    ∀ i : Fin (n - 1),
      sq5 (f ⟨i.1, by omega⟩).1 + sq5 (f ⟨i.1, by omega⟩).2 +
      sq5 (f ⟨i.1 + 1, by omega⟩).1 + sq5 (f ⟨i.1 + 1, by omega⟩).2 = 27)
  have hsq5_lt : ∀ k : Fin 5, sq5 k < 28 := by intro k; fin_cases k <;> decide
  have hsq5_sq : ∀ k : Fin 5, isSquare (sq5 k) := by
    intro k; fin_cases k
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨5, by decide⟩
  have hsq5_inj : Function.Injective sq5 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [sq5]
  have choose_eq : ∀ {y : ℕ} (h : ∃ k : Fin 5, y = sq5 k) (k : Fin 5),
      y = sq5 k → Classical.choose h = k := by
    intro y h k hy
    exact hsq5_inj ((Classical.choose_spec h).symm.trans hy)
  have hbij : rowPer2Card n = P.card := by
    unfold rowPer2Card
    dsimp only [P]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    apply Fintype.card_congr
    refine Equiv.symm
      { toFun := fun ⟨f, hf⟩ =>
          ⟨fun i j =>
            if (j : ℕ) % 2 = 0 then ⟨sq5 (f i).1, hsq5_lt _⟩ else ⟨sq5 (f i).2, hsq5_lt _⟩,
           by
            refine ⟨⟨fun i j => ?_, fun i j hi hj => ?_⟩, fun i j hi hj => ?_⟩
            · dsimp only; split_ifs <;> exact hsq5_sq _
            · have hrow := hf ⟨i, by omega⟩
              dsimp only at hrow ⊢
              by_cases hj2 : j % 2 = 0
              · have hj2' : (j + 1) % 2 ≠ 0 := by omega
                simp only [hj2, hj2', ↓reduceIte, Fin.val_mk]; omega
              · have hj2' : (j + 1) % 2 = 0 := by omega
                simp only [hj2, hj2', ↓reduceIte, Fin.val_mk]; omega
            · simp [show (j + 2) % 2 = j % 2 by omega]⟩
        invFun := fun ⟨x, hx, hr⟩ =>
          ⟨fun i =>
            (Classical.choose (entry_in_sq5 hn x hx i ⟨0, by omega⟩),
             Classical.choose (entry_in_sq5 hn x hx i ⟨1, by omega⟩)),
           by
            intro i
            have hi : i.1 + 1 < n := by omega
            have h0 := Classical.choose_spec (entry_in_sq5 hn x hx ⟨i.1, by omega⟩ ⟨0, by omega⟩)
            have h1 := Classical.choose_spec (entry_in_sq5 hn x hx ⟨i.1, by omega⟩ ⟨1, by omega⟩)
            have h2 := Classical.choose_spec (entry_in_sq5 hn x hx ⟨i.1 + 1, hi⟩ ⟨0, by omega⟩)
            have h3 := Classical.choose_spec (entry_in_sq5 hn x hx ⟨i.1 + 1, hi⟩ ⟨1, by omega⟩)
            have hb := hx.2 i.1 0 hi (by omega)
            simp only [Nat.zero_add] at hb
            dsimp only
            rw [← h0, ← h1, ← h2, ← h3]
            exact hb⟩
        left_inv := by
          rintro ⟨f, hf⟩
          apply Subtype.ext
          funext i
          apply Prod.ext
          · dsimp only; apply choose_eq; rfl
          · dsimp only; apply choose_eq; rfl
        right_inv := by
          rintro ⟨x, hx, hr⟩
          apply Subtype.ext
          funext i j
          dsimp only
          have h0 := Classical.choose_spec (entry_in_sq5 hn x hx i ⟨0, by omega⟩)
          have h1 := Classical.choose_spec (entry_in_sq5 hn x hx i ⟨1, by omega⟩)
          have hrow := per2_mod2 (fun k => x i k) hn (fun k hk => hr i.1 k i.isLt hk) j
          rw [hrow]
          by_cases hj2 : (j : ℕ) % 2 = 0
          · simp only [hj2, ↓reduceIte]; exact Fin.ext h0.symm
          · have hj1 : (j : ℕ) % 2 = 1 := by omega
            simp only [hj2, hj1, ↓reduceIte]; exact Fin.ext h1.symm }
  rw [hbij]
  -- Partition P by s = sq5 (f 0).1 + sq5 (f 0).2 ∈ validSums
  have hpart : P.card =
      ∑ s ∈ validSums, (P.filter (fun f => sq5 (f ⟨0, by omega⟩).1 + sq5 (f ⟨0, by omega⟩).2 = s)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext f
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hf
        refine ⟨sq5 (f ⟨0, by omega⟩).1 + sq5 (f ⟨0, by omega⟩).2, ?_, hf, rfl⟩
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact sum_mem_validSums _ _ _ _ (hf ⟨0, by omega⟩)
      · rintro ⟨_, _, hf, _⟩; exact hf
    · intro s1 _ s2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro f hf1 hf2
      simp only [Finset.mem_filter] at hf1 hf2
      exact hne (hf1.2.symm.trans hf2.2)
  rw [hpart]
  -- Each fiber over s has cardinality (pairsWithSum s).card ^ ((n + 1) / 2) * (pairsWithSum (27 - s)).card ^ (n / 2)
  have hfiber : ∀ s ∈ validSums,
      (P.filter (fun f => sq5 (f ⟨0, by omega⟩).1 + sq5 (f ⟨0, by omega⟩).2 = s)).card =
        (pairsWithSum s).card ^ ((n + 1) / 2) * (pairsWithSum (27 - s)).card ^ (n / 2) := by
    intro s hs
    have hs_le : s ≤ 27 := by
      simp only [validSums, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hset : P.filter (fun f => sq5 (f ⟨0, by omega⟩).1 + sq5 (f ⟨0, by omega⟩).2 = s) =
        Finset.univ.filter (fun f : Fin n → Fin 5 × Fin 5 =>
          ∀ i : Fin n, f i ∈ (if (i : ℕ) % 2 = 0 then pairsWithSum s else pairsWithSum (27 - s))) := by
      ext f
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hadj, h0⟩ ⟨i, hi⟩
        induction i with
        | zero => simpa [pairsWithSum] using h0
        | succ i ih =>
          have hprev := ih (by omega)
          have hstep := hadj ⟨i, by omega⟩
          dsimp only at hstep
          by_cases hi2 : i % 2 = 0
          · have hi2' : (i + 1) % 2 ≠ 0 := by omega
            simp only [hi2, hi2', ↓reduceIte, pairsWithSum, Finset.mem_filter, Finset.mem_univ, true_and] at hprev ⊢
            omega
          · have hi2' : (i + 1) % 2 = 0 := by omega
            simp only [hi2, hi2', ↓reduceIte, pairsWithSum, Finset.mem_filter, Finset.mem_univ, true_and] at hprev ⊢
            omega
      · intro hall
        refine ⟨fun i => ?_, ?_⟩
        · have h1 := hall ⟨i.1, by omega⟩
          have h2 := hall ⟨i.1 + 1, by omega⟩
          by_cases hi2 : i.1 % 2 = 0
          · have hi2' : (i.1 + 1) % 2 ≠ 0 := by omega
            simp only [hi2, hi2', ↓reduceIte, pairsWithSum, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            omega
          · have hi2' : (i.1 + 1) % 2 = 0 := by omega
            simp only [hi2, hi2', ↓reduceIte, pairsWithSum, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            omega
        · have h0 := hall ⟨0, by omega⟩
          simpa [pairsWithSum] using h0
    rw [hset]
    -- Rewrite filter of `∀ i, f i ∈ S i` as `Fintype.piFinset`
    have hpi : (Finset.univ.filter (fun f : Fin n → Fin 5 × Fin 5 =>
          ∀ i : Fin n, f i ∈ (if (i : ℕ) % 2 = 0 then pairsWithSum s else pairsWithSum (27 - s)))) =
        Fintype.piFinset (fun i : Fin n =>
          if (i : ℕ) % 2 = 0 then pairsWithSum s else pairsWithSum (27 - s)) := by
      ext f; simp
    rw [hpi, Fintype.card_piFinset]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => (i : ℕ) % 2 = 0)]
    have hp1 : ∏ x ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0),
        (if (x : ℕ) % 2 = 0 then pairsWithSum s else pairsWithSum (27 - s)).card =
        (pairsWithSum s).card ^ ((n + 1) / 2) := by
      rw [Finset.prod_congr rfl (g := fun _ => (pairsWithSum s).card) (fun x hx => by simp [(Finset.mem_filter.mp hx).2])]
      rw [Finset.prod_const, (card_even_odd n).1]
    have hp2 : ∏ x ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) % 2 = 0),
        (if (x : ℕ) % 2 = 0 then pairsWithSum s else pairsWithSum (27 - s)).card =
        (pairsWithSum (27 - s)).card ^ (n / 2) := by
      rw [Finset.prod_congr rfl (g := fun _ => (pairsWithSum (27 - s)).card) (fun x hx => by simp [(Finset.mem_filter.mp hx).2])]
      rw [Finset.prod_const, (card_even_odd n).2]
    rw [hp1, hp2]
  rw [Finset.sum_congr rfl hfiber]
  obtain ⟨c1, c26, c2, c25, c9, c18, c10, c17⟩ := pairsWithSum_cards
  have hpow2 : 2 ^ ((n + 1) / 2) * 2 ^ (n / 2) = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  simp only [validSums]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [c1, c26, c2, c25, c9, c18, c10, c17, one_pow, one_mul, mul_one, hpow2]
  ring

/-! ### Part 5: Closed form, recurrence, and generating function -/

lemma a_closed_even (q : ℕ) (hq : 1 ≤ q) :
    a (2 * q) = 3 * 4 ^ q + 2 ^ q - 7 := by
  have hn : 2 ≤ 2 * q := by omega
  have ha : a (2 * q) = total (2 * q) / 4 := by
    cases h2q : 2 * q with
    | zero => omega
    | succ k => cases k with | zero => omega | succ m => rfl
  have hie := total_eq_ie (2 * q)
  rw [bothPer2Card_eq (2 * q) hn, rowPer2Card_eq (2 * q) hn] at hie
  have h1 : 2 * q / 2 = q := by omega
  have h2 : (2 * q + 1) / 2 = q := by omega
  have h4 : 2 ^ (2 * q) = 4 ^ q := by rw [pow_mul]; norm_num
  rw [h1, h2, h4] at hie
  have htot : total (2 * q) = 4 * (3 * 4 ^ q + 2 ^ q - 7) := by
    have hge : 7 ≤ 3 * 4 ^ q + 2 ^ q := by
      have : 4 ≤ 4 ^ q := by
        calc 4 = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) hq
      omega
    omega
  rw [ha, htot, Nat.mul_div_right _ (by omega)]

lemma a_closed_odd (q : ℕ) (hq : 1 ≤ q) :
    a (2 * q + 1) = 13 * 2 ^ (2 * q - 1) + 3 * 2 ^ (q - 1) - 7 := by
  have hn : 2 ≤ 2 * q + 1 := by omega
  have ha : a (2 * q + 1) = total (2 * q + 1) / 4 := by
    cases h2q : 2 * q + 1 with
    | zero => omega
    | succ k => cases k with | zero => omega | succ m => rfl
  have hie := total_eq_ie (2 * q + 1)
  rw [bothPer2Card_eq (2 * q + 1) hn, rowPer2Card_eq (2 * q + 1) hn] at hie
  have h1 : (2 * q + 1) / 2 = q := by omega
  have h2 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
  rw [h1, h2] at hie
  have hp1 : 2 ^ (2 * q + 1) = 4 * 2 ^ (2 * q - 1) := by
    have : 2 * q + 1 = (2 * q - 1) + 2 := by omega
    rw [this, pow_add]; ring
  have hp2 : 4 ^ q = 2 * 2 ^ (2 * q - 1) := by
    have h4 : 4 ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
    have : 2 * q = (2 * q - 1) + 1 := by omega
    conv_lhs => rw [h4, this, pow_succ]
    ring
  have hp3 : 4 ^ (q + 1) = 8 * 2 ^ (2 * q - 1) := by rw [pow_succ, hp2]; ring
  have hp4 : 2 ^ q = 2 * 2 ^ (q - 1) := by
    have : q = (q - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ]; ring
  have hp5 : 2 ^ (q + 1) = 4 * 2 ^ (q - 1) := by rw [pow_succ, hp4]; ring
  rw [hp1, hp2, hp3, hp4, hp5] at hie
  have htot : total (2 * q + 1) = 4 * (13 * 2 ^ (2 * q - 1) + 3 * 2 ^ (q - 1) - 7) := by
    have hge : 7 ≤ 13 * 2 ^ (2 * q - 1) + 3 * 2 ^ (q - 1) := by
      have : 1 ≤ 2 ^ (2 * q - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega
  rw [ha, htot, Nat.mul_div_right _ (by omega)]

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 0 := rfl
lemma a_2 : a 2 = 7 := by simpa using a_closed_even 1 (by omega)
lemma a_3 : a 3 = 22 := by simpa using a_closed_odd 1 (by omega)
lemma a_4 : a 4 = 45 := by simpa using a_closed_even 2 (by omega)
lemma a_5 : a 5 = 103 := by simpa using a_closed_odd 2 (by omega)
lemma a_6 : a 6 = 193 := by simpa using a_closed_even 3 (by omega)

lemma a_closed_even_int (q : ℕ) (hq : 1 ≤ q) :
    (a (2 * q) : ℤ) = 3 * (4 : ℤ) ^ q + (2 : ℤ) ^ q - 7 := by
  rw [a_closed_even q hq]
  have hge : 7 ≤ 3 * 4 ^ q + 2 ^ q := by
    have : 4 ≤ 4 ^ q := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    have : 1 ≤ 2 ^ q := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [Nat.cast_sub hge]
  push_cast
  ring

lemma a_closed_odd_int (q : ℕ) (hq : 1 ≤ q) :
    (a (2 * q + 1) : ℤ) = 13 * (2 : ℤ) ^ (2 * q - 1) + 3 * (2 : ℤ) ^ (q - 1) - 7 := by
  rw [a_closed_odd q hq]
  have hge : 7 ≤ 13 * 2 ^ (2 * q - 1) + 3 * 2 ^ (q - 1) := by
    have : 1 ≤ 2 ^ (2 * q - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [Nat.cast_sub hge]
  push_cast
  ring

lemma a_rec (n : ℕ) (hn : 7 ≤ n) :
    -(a n : ℤ) + a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) -
      8 * a (n - 4) + 8 * a (n - 5) = 0 := by
  rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hq4 : 4 ≤ q := by omega
    have h0 : n = 2 * q := by omega
    have h1 : n - 1 = 2 * (q - 1) + 1 := by omega
    have h2 : n - 2 = 2 * (q - 1) := by omega
    have h3 : n - 3 = 2 * (q - 2) + 1 := by omega
    have h4 : n - 4 = 2 * (q - 2) := by omega
    have h5 : n - 5 = 2 * (q - 3) + 1 := by omega
    rw [h1, h2, h3, h4, h5, h0]
    rw [a_closed_even_int q (by omega), a_closed_odd_int (q - 1) (by omega),
      a_closed_even_int (q - 1) (by omega), a_closed_odd_int (q - 2) (by omega),
      a_closed_even_int (q - 2) (by omega), a_closed_odd_int (q - 3) (by omega)]
    set k := q - 3
    have hqk : q = k + 3 := by omega
    have hq1 : q - 1 = k + 2 := by omega
    have hq2 : q - 2 = k + 1 := by omega
    rw [hq1, hq2, hqk]
    have e1 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
    have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e3 : 2 * k - 1 + 1 = 2 * k := by omega
    have e4 : k + 2 - 1 = k + 1 := by omega
    have e5 : k + 1 - 1 = k := by omega
    rw [e1, e2, e4, e5]
    have p1 : (4 : ℤ) ^ (k + 3) = 64 * (4 : ℤ) ^ k := by ring
    have p2 : (4 : ℤ) ^ (k + 2) = 16 * (4 : ℤ) ^ k := by ring
    have p3 : (4 : ℤ) ^ (k + 1) = 4 * (4 : ℤ) ^ k := by ring
    have p4 : (2 : ℤ) ^ (2 * k + 3) = 8 * (4 : ℤ) ^ k := by
      rw [pow_add, pow_mul]; norm_num; ring
    have p5 : (2 : ℤ) ^ (2 * k + 1) = 2 * (4 : ℤ) ^ k := by
      rw [pow_add, pow_mul]; norm_num; ring
    have p6 : 2 * (2 : ℤ) ^ (2 * k - 1) = (4 : ℤ) ^ k := by
      have hk1 : 1 ≤ k := by omega
      have : (2 : ℤ) ^ (2 * k) = 2 * (2 : ℤ) ^ (2 * k - 1) := by
        conv_lhs => rw [← e3, pow_succ']
      rw [← this, pow_mul]; norm_num
    have p7 : 2 * (2 : ℤ) ^ (k - 1) = (2 : ℤ) ^ k := by
      have hk1 : 1 ≤ k := by omega
      have : k - 1 + 1 = k := by omega
      conv_rhs => rw [← this, pow_succ']
    have p8 : (2 : ℤ) ^ (k + 3) = 8 * (2 : ℤ) ^ k := by ring
    have p9 : (2 : ℤ) ^ (k + 2) = 4 * (2 : ℤ) ^ k := by ring
    have p10 : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by ring
    linear_combination -3 * p1 - p8 + 13 * p4 + 3 * p10 + 18 * p2 + 6 * p9 -
      78 * p5 - 24 * p3 - 8 * p10 + 52 * p6 + 12 * p7
  · have hq3 : 3 ≤ q := by omega
    have h0 : n = 2 * q + 1 := by omega
    have h1 : n - 1 = 2 * q := by omega
    have h2 : n - 2 = 2 * (q - 1) + 1 := by omega
    have h3 : n - 3 = 2 * (q - 1) := by omega
    have h4 : n - 4 = 2 * (q - 2) + 1 := by omega
    have h5 : n - 5 = 2 * (q - 2) := by omega
    rw [h1, h2, h3, h4, h5, h0]
    rw [a_closed_odd_int q (by omega), a_closed_even_int q (by omega),
      a_closed_odd_int (q - 1) (by omega), a_closed_even_int (q - 1) (by omega),
      a_closed_odd_int (q - 2) (by omega), a_closed_even_int (q - 2) (by omega)]
    set k := q - 2
    have hqk : q = k + 2 := by omega
    have hq1 : q - 1 = k + 1 := by omega
    rw [hq1, hqk]
    have e1 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
    have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e3 : 2 * k - 1 + 1 = 2 * k := by omega
    have e5 : k + 1 - 1 = k := by omega
    rw [e1, e2, e5]
    have p1 : (4 : ℤ) ^ (k + 2) = 16 * (4 : ℤ) ^ k := by ring
    have p2 : (4 : ℤ) ^ (k + 1) = 4 * (4 : ℤ) ^ k := by ring
    have p3 : (2 : ℤ) ^ (2 * k + 3) = 8 * (4 : ℤ) ^ k := by
      rw [pow_add, pow_mul]; norm_num; ring
    have p4 : (2 : ℤ) ^ (2 * k + 1) = 2 * (4 : ℤ) ^ k := by
      rw [pow_add, pow_mul]; norm_num; ring
    have p5 : 2 * (2 : ℤ) ^ (2 * k - 1) = (4 : ℤ) ^ k := by
      have hk1 : 1 ≤ k := by omega
      have : (2 : ℤ) ^ (2 * k) = 2 * (2 : ℤ) ^ (2 * k - 1) := by
        conv_lhs => rw [← e3, pow_succ']
      rw [← this, pow_mul]; norm_num
    have p6 : 2 * (2 : ℤ) ^ (k - 1) = (2 : ℤ) ^ k := by
      have hk1 : 1 ≤ k := by omega
      have : k - 1 + 1 = k := by omega
      conv_rhs => rw [← this, pow_succ']
    have p7 : (2 : ℤ) ^ (k + 2) = 4 * (2 : ℤ) ^ k := by ring
    have p8 : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by ring
    linear_combination -13 * p3 - 3 * p8 + 3 * p1 + p7 + 78 * p4 -
      18 * p2 - 6 * p8 - 52 * p5 - 12 * p6

theorem main_proof :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((X - 1) * (2 * X + 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
    X ^ 2 * (-7 - 8 * X ^ 4 + 32 * X ^ 3 + 19 * X ^ 2 - 15 * X) := by
  set S := PowerSeries.mk (fun n => (a n : ℚ)) with hS
  have hl : S * ((X - 1) * (2 * X + 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
      C (-1 : ℚ) * S + C (1 : ℚ) * (S * X ^ 1) + C (6 : ℚ) * (S * X ^ 2) +
      C (-6 : ℚ) * (S * X ^ 3) + C (-8 : ℚ) * (S * X ^ 4) + C (8 : ℚ) * (S * X ^ 5) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (X ^ 2 * (-7 - 8 * X ^ 4 + 32 * X ^ 3 + 19 * X ^ 2 - 15 * X) : PowerSeries ℚ) =
      C (-7 : ℚ) * X ^ 2 + C (-15 : ℚ) * X ^ 3 + C (19 : ℚ) * X ^ 4 +
      C (32 : ℚ) * X ^ 5 + C (-8 : ℚ) * X ^ 6 := by
    simp only [map_neg, map_ofNat]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
  · have hq : -(a n : ℚ) + a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) -
        8 * a (n - 4) + 8 * a (n - 5) = 0 := by
      exact_mod_cast a_rec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have c6 : 6 ≤ n := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    have e6 : n - 6 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, c6, e2, e3, e4, e5, e6, if_true, if_false]
    linear_combination hq

end OMA.P159227

theorem OMA.solution : type_of% @OMA.S_oeis_a159227.main := OMA.P159227.main_proof
