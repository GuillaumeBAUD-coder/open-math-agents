import OMAStatements.S_mse_1911440

/-!
# Proof of `mse-1911440`: a strictly increasing function `ℚ → ℚ` with derivative `0` everywhere

We enumerate `ℚ` via `enumQ : ℕ ≃ ℚ` (`q n = enumQ n`) and recursively maintain, at stage `n`,
a partition of `ℚ` into `n + 1` open cells `(lo_i, hi_i)` (with irrational finite endpoints)
paired with rational codomain intervals `(ylo_i, yhi_i)` and pinned rational values
`val_i ∈ (ylo_i, yhi_i)` for `q 0, …, q n`.

At stage `n → n + 1`, the new rational `q (n + 1)` lies in a unique existing cell `k`.
We split cell `k` at an irrational midpoint `γ` between `q k` and `q (n + 1)`, shrinking
the codomain around `val_k` by `η ≤ |q (n + 1) - q k| / (4 * 2^(n + 1))` so that every point `x`
separated from `q k` at stage `n + 1` has `|x - q k| > |q (n + 1) - q k| / 4` and
`|f x - f (q k)| ≤ η ≤ 2^(-(n + 1)) * |x - q k|`.
Pinned values never change, order of cells gives `StrictMono f`, and nesting of codomains gives
`HasDerivAt f 0 q` for every `q : ℚ`.
-/

namespace OMA.P1911440

open Topology

private noncomputable def enumQ : ℕ ≃ ℚ :=
  (Denumerable.eqv ℚ).symm

private noncomputable def q (n : ℕ) : ℚ :=
  enumQ n

private lemma q_injective : Function.Injective q :=
  enumQ.injective

private lemma q_surjective : Function.Surjective q :=
  enumQ.surjective

private noncomputable def irrMid (u v : ℚ) : ℝ :=
  (u : ℝ) + ((v : ℝ) - (u : ℝ)) * (Real.sqrt 2 / 2)

private lemma one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa using h

private lemma sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have h : Real.sqrt 2 < Real.sqrt ((3 / 2 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h

private lemma irrMid_gt_add_quarter {u v : ℚ} (huv : u < v) :
    (u : ℝ) + ((v : ℝ) - (u : ℝ)) / 4 < irrMid u v := by
  unfold irrMid
  have hpos : (0 : ℝ) < (v : ℝ) - (u : ℝ) := by
    have : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  have h1 : (1 / 4 : ℝ) < Real.sqrt 2 / 2 := by linarith [one_lt_sqrt_two]
  nlinarith

private lemma irrMid_add_quarter_lt {u v : ℚ} (huv : u < v) :
    irrMid u v + ((v : ℝ) - (u : ℝ)) / 4 < (v : ℝ) := by
  unfold irrMid
  have hpos : (0 : ℝ) < (v : ℝ) - (u : ℝ) := by
    have : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  have h2 : Real.sqrt 2 / 2 < 3 / 4 := by linarith [sqrt_two_lt_three_halves]
  nlinarith

private lemma lt_irrMid {u v : ℚ} (huv : u < v) : (u : ℝ) < irrMid u v := by
  have hpos : (0 : ℝ) < (v : ℝ) - (u : ℝ) := by
    have : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  linarith [irrMid_gt_add_quarter huv]

private lemma irrMid_lt {u v : ℚ} (huv : u < v) : irrMid u v < (v : ℝ) := by
  have hpos : (0 : ℝ) < (v : ℝ) - (u : ℝ) := by
    have : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  linarith [irrMid_add_quarter_lt huv]

private lemma rat_ne_irrMid {u v : ℚ} (huv : u < v) (x : ℚ) :
    (x : ℝ) ≠ irrMid u v := by
  intro hx
  unfold irrMid at hx
  have hvu : ((v : ℝ) - (u : ℝ)) ≠ 0 := by
    have : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  have hsq : Real.sqrt 2 = ((2 * (x - u) / (v - u) : ℚ) : ℝ) := by
    push_cast
    field_simp [hvu]
    linarith
  exact irrational_sqrt_two.ne_rat (2 * (x - u) / (v - u)) hsq

private structure Cell where
  lo : Option ℝ
  hi : Option ℝ
  ylo : ℚ
  yhi : ℚ
  val : ℚ

private def ltLeft (a : Option ℝ) (x : ℝ) : Prop :=
  match a with
  | none => True
  | some r => r < x

private def ltRight (x : ℝ) (b : Option ℝ) : Prop :=
  match b with
  | none => True
  | some r => x < r

private def leBound (b a : Option ℝ) : Prop :=
  match b, a with
  | some r, some s => r ≤ s
  | _, _ => False

private def inDom (c : Cell) (x : ℝ) : Prop :=
  ltLeft c.lo x ∧ ltRight x c.hi

private def subCod (c₁ c₂ : Cell) : Prop :=
  c₂.ylo ≤ c₁.ylo ∧ c₁.yhi ≤ c₂.yhi

private lemma subCod_refl (c : Cell) : subCod c c :=
  ⟨le_rfl, le_rfl⟩

private lemma subCod_trans {c₁ c₂ c₃ : Cell} (h₁ : subCod c₁ c₂) (h₂ : subCod c₂ c₃) :
    subCod c₁ c₃ :=
  ⟨le_trans h₂.1 h₁.1, le_trans h₁.2 h₂.2⟩

private lemma ltLeft_of_lt {a : Option ℝ} {x y : ℝ} (h : ltLeft a x) (hxy : x < y) :
    ltLeft a y := by
  cases a with
  | none => trivial
  | some r => exact lt_trans h hxy

private lemma ltRight_of_lt {b : Option ℝ} {x y : ℝ} (h : ltRight y b) (hxy : x < y) :
    ltRight x b := by
  cases b with
  | none => trivial
  | some r => exact lt_trans hxy h

private lemma not_inDom_of_leBound {b a : Option ℝ} {x : ℝ}
    (hba : leBound b a) (hx1 : ltRight x b) (hx2 : ltLeft a x) : False := by
  cases b with
  | none => exact hba
  | some r =>
    cases a with
    | none => exact hba
    | some s => exact lt_irrefl x (lt_of_lt_of_le hx1 (le_trans hba (le_of_lt hx2)))

private lemma lt_of_leBound {b a : Option ℝ} {x y : ℝ}
    (hba : leBound b a) (hx : ltRight x b) (hy : ltLeft a y) : x < y := by
  cases b with
  | none => exact False.elim hba
  | some r =>
    cases a with
    | none => exact False.elim hba
    | some s => exact lt_of_lt_of_le hx (le_trans hba (le_of_lt hy))

private lemma leBound_of_ltLeft {b a : Option ℝ} {γ : ℝ}
    (hba : leBound b a) (hγ : ltLeft a γ) : leBound b (some γ) := by
  cases b with
  | none => exact False.elim hba
  | some r =>
    cases a with
    | none => exact False.elim hba
    | some s => exact le_trans hba (le_of_lt hγ)

private lemma leBound_of_ltRight {b a : Option ℝ} {γ : ℝ}
    (hba : leBound b a) (hγ : ltRight γ b) : leBound (some γ) a := by
  cases b with
  | none => exact False.elim hba
  | some r =>
    cases a with
    | none => exact False.elim hba
    | some s => exact le_trans (le_of_lt hγ) hba

private lemma exists_ball_inDom {c : Cell} {x : ℝ} (hx : inDom c x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → inDom c y := by
  rcases hx with ⟨hlo, hhi⟩
  cases h1 : c.lo with
  | none =>
    cases h2 : c.hi with
    | none =>
      refine ⟨1, by norm_num, fun y _ => ?_⟩
      simp [inDom, ltLeft, ltRight, h1, h2]
    | some s =>
      rw [h2] at hhi
      refine ⟨s - x, sub_pos.mpr hhi, fun y hy => ?_⟩
      have hlt := (abs_lt.mp hy).2
      simp [inDom, ltLeft, ltRight, h1, h2]
      linarith
  | some r =>
    rw [h1] at hlo
    cases h2 : c.hi with
    | none =>
      refine ⟨x - r, sub_pos.mpr hlo, fun y hy => ?_⟩
      have hgt := (abs_lt.mp hy).1
      simp [inDom, ltLeft, ltRight, h1, h2]
      linarith
    | some s =>
      rw [h2] at hhi
      refine ⟨min (x - r) (s - x), lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi), fun y hy => ?_⟩
      have h1' : -(x - r) < y - x := by
        have := (abs_lt.mp hy).1
        linarith [min_le_left (x - r) (s - x)]
      have h2' : y - x < s - x := by
        have := (abs_lt.mp hy).2
        linarith [min_le_right (x - r) (s - x)]
      simp [inDom, ltLeft, ltRight, h1, h2]
      constructor <;> linarith

private structure State (n : ℕ) where
  cell : Fin (n + 1) → Cell
  mem_dom : ∀ i : Fin (n + 1), inDom (cell i) (q i.1 : ℝ)
  mem_val : ∀ i : Fin (n + 1), (cell i).ylo < (cell i).val ∧ (cell i).val < (cell i).yhi
  cover : ∀ x : ℚ, ∃ i : Fin (n + 1), inDom (cell i) (x : ℝ)
  ord : ∀ i j : Fin (n + 1), q i.1 < q j.1 →
    leBound (cell i).hi (cell j).lo ∧ (cell i).yhi ≤ (cell j).ylo

private lemma State.unique {n : ℕ} (s : State n) {x : ℝ} {i j : Fin (n + 1)}
    (hi : inDom (s.cell i) x) (hj : inDom (s.cell j) x) : i = j := by
  by_contra hij
  have hne : q i.1 ≠ q j.1 := fun h => hij (Fin.ext (q_injective h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_inDom_of_leBound (s.ord i j hlt).1 hi.2 hj.1
  · exact not_inDom_of_leBound (s.ord j i hgt).1 hj.2 hi.1

private def state0 : State 0 where
  cell _ := ⟨none, none, -1, 1, 0⟩
  mem_dom _ := ⟨trivial, trivial⟩
  mem_val _ := by norm_num
  cover _ := ⟨0, trivial, trivial⟩
  ord i j h := by
    have : i = j := Fin.ext (by omega)
    subst this
    exact False.elim (lt_irrefl _ h)

private noncomputable def stepIdx {n : ℕ} (s : State n) : Fin (n + 1) :=
  Classical.choose (s.cover (q (n + 1)))

private lemma stepIdx_mem {n : ℕ} (s : State n) :
    inDom (s.cell (stepIdx s)) (q (n + 1) : ℝ) :=
  Classical.choose_spec (s.cover (q (n + 1)))

private lemma stepIdx_ne {n : ℕ} (s : State n) :
    q (stepIdx s).1 ≠ q (n + 1) := by
  intro h
  have := q_injective h
  omega

private noncomputable def stepGamma {n : ℕ} (s : State n) : ℝ :=
  if q (stepIdx s).1 < q (n + 1) then
    irrMid (q (stepIdx s).1) (q (n + 1))
  else
    irrMid (q (n + 1)) (q (stepIdx s).1)

private noncomputable def stepEta {n : ℕ} (s : State n) : ℚ :=
  let c := s.cell (stepIdx s)
  min (min ((c.val - c.ylo) / 2) ((c.yhi - c.val) / 2))
      (|q (n + 1) - q (stepIdx s).1| / (4 * (2 : ℚ) ^ (n + 1)))

private lemma stepEta_pos {n : ℕ} (s : State n) : 0 < stepEta s := by
  unfold stepEta
  have hv := s.mem_val (stepIdx s)
  have hne : q (n + 1) - q (stepIdx s).1 ≠ 0 := sub_ne_zero.mpr (stepIdx_ne s).symm
  have habs : (0 : ℚ) < |q (n + 1) - q (stepIdx s).1| := abs_pos.mpr hne
  have hden : (0 : ℚ) < 4 * (2 : ℚ) ^ (n + 1) := by positivity
  refine lt_min (lt_min ?_ ?_) (div_pos habs hden) <;> linarith

private lemma stepEta_le_left {n : ℕ} (s : State n) :
    stepEta s ≤ ((s.cell (stepIdx s)).val - (s.cell (stepIdx s)).ylo) / 2 :=
  le_trans (min_le_left _ _) (min_le_left _ _)

private lemma stepEta_le_right {n : ℕ} (s : State n) :
    stepEta s ≤ ((s.cell (stepIdx s)).yhi - (s.cell (stepIdx s)).val) / 2 :=
  le_trans (min_le_left _ _) (min_le_right _ _)

private lemma stepEta_le_slope {n : ℕ} (s : State n) :
    stepEta s ≤ |q (n + 1) - q (stepIdx s).1| / (4 * (2 : ℚ) ^ (n + 1)) :=
  min_le_right _ _

private lemma stepGamma_inDom {n : ℕ} (s : State n) :
    inDom (s.cell (stepIdx s)) (stepGamma s) := by
  unfold stepGamma
  have h1 := s.mem_dom (stepIdx s)
  have h2 := stepIdx_mem s
  split_ifs with hlt
  · exact ⟨ltLeft_of_lt h1.1 (lt_irrMid hlt), ltRight_of_lt h2.2 (irrMid_lt hlt)⟩
  · have hgt : q (n + 1) < q (stepIdx s).1 := lt_of_le_of_ne (not_lt.mp hlt) (stepIdx_ne s).symm
    exact ⟨ltLeft_of_lt h2.1 (lt_irrMid hgt), ltRight_of_lt h1.2 (irrMid_lt hgt)⟩

private lemma rat_ne_stepGamma {n : ℕ} (s : State n) (x : ℚ) :
    (x : ℝ) ≠ stepGamma s := by
  unfold stepGamma
  split_ifs with hlt
  · exact rat_ne_irrMid hlt x
  · have hgt : q (n + 1) < q (stepIdx s).1 := lt_of_le_of_ne (not_lt.mp hlt) (stepIdx_ne s).symm
    exact rat_ne_irrMid hgt x

private noncomputable def stepCell {n : ℕ} (s : State n) (i : Fin (n + 2)) : Cell :=
  if hi : i.1 < n + 1 then
    if ⟨i.1, hi⟩ = stepIdx s then
      let c := s.cell (stepIdx s)
      let γ := stepGamma s
      let η := stepEta s
      if q (stepIdx s).1 < q (n + 1) then
        ⟨c.lo, some γ, c.val - η / 2, c.val + η / 2, c.val⟩
      else
        ⟨some γ, c.hi, c.val - η / 2, c.val + η / 2, c.val⟩
    else
      s.cell ⟨i.1, hi⟩
  else
    let c := s.cell (stepIdx s)
    let γ := stepGamma s
    let η := stepEta s
    if q (stepIdx s).1 < q (n + 1) then
      ⟨some γ, c.hi, c.val + η / 2, c.val + η, c.val + 3 * η / 4⟩
    else
      ⟨c.lo, some γ, c.val - η, c.val - η / 2, c.val - 3 * η / 4⟩

private lemma stepCell_castSucc_ne {n : ℕ} (s : State n) {i : Fin (n + 1)} (hi : i ≠ stepIdx s) :
    stepCell s i.castSucc = s.cell i := by
  simp [stepCell, i.2, hi]

private lemma stepCell_k_of_lt {n : ℕ} (s : State n) (h : q (stepIdx s).1 < q (n + 1)) :
    stepCell s (stepIdx s).castSucc =
      ⟨(s.cell (stepIdx s)).lo, some (stepGamma s),
        (s.cell (stepIdx s)).val - stepEta s / 2,
        (s.cell (stepIdx s)).val + stepEta s / 2,
        (s.cell (stepIdx s)).val⟩ := by
  simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte, h]

private lemma stepCell_k_of_not_lt {n : ℕ} (s : State n) (h : ¬ q (stepIdx s).1 < q (n + 1)) :
    stepCell s (stepIdx s).castSucc =
      ⟨some (stepGamma s), (s.cell (stepIdx s)).hi,
        (s.cell (stepIdx s)).val - stepEta s / 2,
        (s.cell (stepIdx s)).val + stepEta s / 2,
        (s.cell (stepIdx s)).val⟩ := by
  simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte, h]

private lemma stepCell_last_of_lt {n : ℕ} (s : State n) (h : q (stepIdx s).1 < q (n + 1)) :
    stepCell s (Fin.last (n + 1)) =
      ⟨some (stepGamma s), (s.cell (stepIdx s)).hi,
        (s.cell (stepIdx s)).val + stepEta s / 2,
        (s.cell (stepIdx s)).val + stepEta s,
        (s.cell (stepIdx s)).val + 3 * stepEta s / 4⟩ := by
  simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte, h, ↓reduceIte]

private lemma stepCell_last_of_not_lt {n : ℕ} (s : State n) (h : ¬ q (stepIdx s).1 < q (n + 1)) :
    stepCell s (Fin.last (n + 1)) =
      ⟨(s.cell (stepIdx s)).lo, some (stepGamma s),
        (s.cell (stepIdx s)).val - stepEta s,
        (s.cell (stepIdx s)).val - stepEta s / 2,
        (s.cell (stepIdx s)).val - 3 * stepEta s / 4⟩ := by
  simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte, h, ↓reduceIte]

private lemma stepCell_castSucc_val {n : ℕ} (s : State n) (i : Fin (n + 1)) :
    (stepCell s i.castSucc).val = (s.cell i).val := by
  by_cases hi : i = stepIdx s
  · subst hi
    simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte]
    split_ifs <;> rfl
  · rw [stepCell_castSucc_ne s hi]

private lemma stepCell_subCod_k {n : ℕ} (s : State n) (i : Fin (n + 2))
    (hi : i = (stepIdx s).castSucc ∨ i = Fin.last (n + 1)) :
    subCod (stepCell s i) (s.cell (stepIdx s)) := by
  have hη : 0 < stepEta s := stepEta_pos s
  have hL := stepEta_le_left s
  have hR := stepEta_le_right s
  have hv := s.mem_val (stepIdx s)
  rcases hi with rfl | rfl
  · simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte]
    split_ifs <;> exact ⟨by linarith, by linarith⟩
  · simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    split_ifs <;> exact ⟨by linarith, by linarith⟩

private lemma step_lt_iff {n : ℕ} (s : State n) {i : Fin (n + 1)} (hi : i ≠ stepIdx s) :
    q i.1 < q (n + 1) ↔ q i.1 < q (stepIdx s).1 := by
  have hne : q i.1 ≠ q (stepIdx s).1 := fun h => hi (Fin.ext (q_injective h))
  constructor
  · intro hlt
    rcases lt_or_gt_of_ne hne with h1 | h2
    · exact h1
    · have hdom := lt_of_leBound (s.ord (stepIdx s) i h2).1 (stepIdx_mem s).2 (s.mem_dom i).1
      have hq : q (n + 1) < q i.1 := by exact_mod_cast hdom
      exact False.elim (lt_asymm hlt hq)
  · intro hlt
    have hdom := lt_of_leBound (s.ord i (stepIdx s) hlt).1 (s.mem_dom i).2 (stepIdx_mem s).1
    exact_mod_cast hdom

private lemma step_gt_iff {n : ℕ} (s : State n) {i : Fin (n + 1)} (hi : i ≠ stepIdx s) :
    q (n + 1) < q i.1 ↔ q (stepIdx s).1 < q i.1 := by
  have hne1 : q i.1 ≠ q (n + 1) := by
    intro h
    have := q_injective h
    omega
  have hne2 : q i.1 ≠ q (stepIdx s).1 := fun h => hi (Fin.ext (q_injective h))
  constructor
  · intro h
    rcases lt_or_gt_of_ne hne2 with h1 | h2
    · exact False.elim (lt_asymm h ((step_lt_iff s hi).mpr h1))
    · exact h2
  · intro h
    rcases lt_or_gt_of_ne hne1 with h1 | h2
    · exact False.elim (lt_asymm h ((step_lt_iff s hi).mp h1))
    · exact h2

private lemma stepCell_leBound_left {n : ℕ} (s : State n) {i : Fin (n + 1)}
    (hlt : q i.1 < q (stepIdx s).1) {j : Fin (n + 2)}
    (hj : j = (stepIdx s).castSucc ∨ j = Fin.last (n + 1)) :
    leBound (s.cell i).hi (stepCell s j).lo := by
  have hba := (s.ord i (stepIdx s) hlt).1
  have hγ := (stepGamma_inDom s).1
  rcases hj with rfl | rfl
  · simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte]
    split_ifs
    · exact hba
    · exact leBound_of_ltLeft hba hγ
  · simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    split_ifs
    · exact leBound_of_ltLeft hba hγ
    · exact hba

private lemma stepCell_leBound_right {n : ℕ} (s : State n) {i : Fin (n + 1)}
    (hlt : q (stepIdx s).1 < q i.1) {j : Fin (n + 2)}
    (hj : j = (stepIdx s).castSucc ∨ j = Fin.last (n + 1)) :
    leBound (stepCell s j).hi (s.cell i).lo := by
  have hba := (s.ord (stepIdx s) i hlt).1
  have hγ := (stepGamma_inDom s).2
  rcases hj with rfl | rfl
  · simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte]
    split_ifs
    · exact leBound_of_ltRight hba hγ
    · exact hba
  · simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    split_ifs
    · exact hba
    · exact leBound_of_ltRight hba hγ

private noncomputable def step {n : ℕ} (s : State n) : State (n + 1) where
  cell := stepCell s
  mem_dom i := by
    by_cases hi : i.1 < n + 1
    · let i' : Fin (n + 1) := ⟨i.1, hi⟩
      by_cases hik : i' = stepIdx s
      · have hdom := s.mem_dom (stepIdx s)
        have h1 : i = (stepIdx s).castSucc := Fin.ext (by simpa [i'] using congrArg Fin.val hik)
        subst h1
        simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte,
          inDom, stepGamma]
        split_ifs with hlt
        · exact ⟨hdom.1, lt_irrMid hlt⟩
        · have hgt : q (n + 1) < q (stepIdx s).1 :=
            lt_of_le_of_ne (not_lt.mp hlt) (stepIdx_ne s).symm
          exact ⟨irrMid_lt hgt, hdom.2⟩
      · have h1 : i = i'.castSucc := Fin.ext rfl
        rw [h1, stepCell_castSucc_ne s hik]
        exact s.mem_dom i'
    · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hlast
      have hdom := stepIdx_mem s
      simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte, inDom, stepGamma]
      split_ifs with hlt
      · exact ⟨irrMid_lt hlt, hdom.2⟩
      · have hgt : q (n + 1) < q (stepIdx s).1 :=
          lt_of_le_of_ne (not_lt.mp hlt) (stepIdx_ne s).symm
        exact ⟨hdom.1, lt_irrMid hgt⟩
  mem_val i := by
    have hη : 0 < stepEta s := stepEta_pos s
    by_cases hi : i.1 < n + 1
    · let i' : Fin (n + 1) := ⟨i.1, hi⟩
      by_cases hik : i' = stepIdx s
      · have h1 : i = (stepIdx s).castSucc := Fin.ext (by simpa [i'] using congrArg Fin.val hik)
        subst h1
        simp only [stepCell, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, ↓reduceIte]
        split_ifs <;> exact ⟨by linarith, by linarith⟩
      · have h1 : i = i'.castSucc := Fin.ext rfl
        rw [h1, stepCell_castSucc_ne s hik]
        exact s.mem_val i'
    · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hlast
      simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
      split_ifs <;> exact ⟨by linarith, by linarith⟩
  cover x := by
    rcases s.cover x with ⟨i, hi⟩
    by_cases hik : i = stepIdx s
    · subst hik
      have hne := rat_ne_stepGamma s x
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · by_cases hkn : q (stepIdx s).1 < q (n + 1)
        · refine ⟨(stepIdx s).castSucc, ?_⟩
          rw [stepCell_k_of_lt s hkn]
          exact ⟨hi.1, hlt⟩
        · refine ⟨Fin.last (n + 1), ?_⟩
          rw [stepCell_last_of_not_lt s hkn]
          exact ⟨hi.1, hlt⟩
      · by_cases hkn : q (stepIdx s).1 < q (n + 1)
        · refine ⟨Fin.last (n + 1), ?_⟩
          rw [stepCell_last_of_lt s hkn]
          exact ⟨hgt, hi.2⟩
        · refine ⟨(stepIdx s).castSucc, ?_⟩
          rw [stepCell_k_of_not_lt s hkn]
          exact ⟨hgt, hi.2⟩
    · refine ⟨i.castSucc, ?_⟩
      rw [stepCell_castSucc_ne s hik]
      exact hi
  ord i j hij := by
    by_cases hi : i = (stepIdx s).castSucc ∨ i = Fin.last (n + 1)
    · by_cases hj : j = (stepIdx s).castSucc ∨ j = Fin.last (n + 1)
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact False.elim (lt_irrefl _ hij)
        · simp only [Fin.val_castSucc, Fin.val_last] at hij
          rw [stepCell_k_of_lt s hij, stepCell_last_of_lt s hij]
          exact ⟨le_rfl, le_rfl⟩
        · simp only [Fin.val_castSucc, Fin.val_last] at hij
          have hnot : ¬ q (stepIdx s).1 < q (n + 1) := not_lt.mpr (le_of_lt hij)
          rw [stepCell_last_of_not_lt s hnot, stepCell_k_of_not_lt s hnot]
          exact ⟨le_rfl, le_rfl⟩
        · exact False.elim (lt_irrefl _ hij)
      · have hjlt : j.1 < n + 1 := by
          have : j ≠ Fin.last (n + 1) := fun h => hj (Or.inr h)
          have hne : j.1 ≠ n + 1 := fun h => this (Fin.ext h)
          omega
        let j' : Fin (n + 1) := ⟨j.1, hjlt⟩
        have hjk : j' ≠ stepIdx s := fun h => hj (Or.inl (Fin.ext (by simpa [j'] using congrArg Fin.val h)))
        have hj_eq : j = j'.castSucc := Fin.ext rfl
        have hkj : q (stepIdx s).1 < q j'.1 := by
          rcases hi with rfl | rfl
          · exact hij
          · exact (step_gt_iff s hjk).mp hij
        rw [hj_eq, stepCell_castSucc_ne s hjk]
        exact ⟨stepCell_leBound_right s hkj hi,
          le_trans (stepCell_subCod_k s i hi).2 (s.ord (stepIdx s) j' hkj).2⟩
    · have hilt : i.1 < n + 1 := by
        have : i ≠ Fin.last (n + 1) := fun h => hi (Or.inr h)
        have hne : i.1 ≠ n + 1 := fun h => this (Fin.ext h)
        omega
      let i' : Fin (n + 1) := ⟨i.1, hilt⟩
      have hik : i' ≠ stepIdx s := fun h => hi (Or.inl (Fin.ext (by simpa [i'] using congrArg Fin.val h)))
      have hi_eq : i = i'.castSucc := Fin.ext rfl
      by_cases hj : j = (stepIdx s).castSucc ∨ j = Fin.last (n + 1)
      · have hiklt : q i'.1 < q (stepIdx s).1 := by
          rcases hj with rfl | rfl
          · exact hij
          · exact (step_lt_iff s hik).mp hij
        rw [hi_eq, stepCell_castSucc_ne s hik]
        exact ⟨stepCell_leBound_left s hiklt hj,
          le_trans (s.ord i' (stepIdx s) hiklt).2 (stepCell_subCod_k s j hj).1⟩
      · have hjlt : j.1 < n + 1 := by
          have : j ≠ Fin.last (n + 1) := fun h => hj (Or.inr h)
          have hne : j.1 ≠ n + 1 := fun h => this (Fin.ext h)
          omega
        let j' : Fin (n + 1) := ⟨j.1, hjlt⟩
        have hjk : j' ≠ stepIdx s := fun h => hj (Or.inl (Fin.ext (by simpa [j'] using congrArg Fin.val h)))
        have hj_eq : j = j'.castSucc := Fin.ext rfl
        rw [hi_eq, hj_eq, stepCell_castSucc_ne s hik, stepCell_castSucc_ne s hjk]
        exact s.ord i' j' hij

private lemma step_subCod {n : ℕ} (s : State n) {x : ℚ} {i : Fin (n + 1)} {j : Fin (n + 2)}
    (hi : inDom (s.cell i) (x : ℝ)) (hj : inDom ((step s).cell j) (x : ℝ)) :
    subCod ((step s).cell j) (s.cell i) := by
  by_cases hik : i = stepIdx s
  · subst hik
    have hj' : j = (stepIdx s).castSucc ∨ j = Fin.last (n + 1) := by
      by_contra hnot
      push Not at hnot
      have hjlt : j.1 < n + 1 := by
        have hne : j.1 ≠ n + 1 := fun h => hnot.2 (Fin.ext h)
        omega
      let j' : Fin (n + 1) := ⟨j.1, hjlt⟩
      have hjk : j' ≠ stepIdx s := fun h =>
        hnot.1 (Fin.ext (by simpa [j'] using congrArg Fin.val h))
      have hjeq : j = j'.castSucc := Fin.ext rfl
      rw [hjeq] at hj
      change inDom (stepCell s j'.castSucc) (x : ℝ) at hj
      rw [stepCell_castSucc_ne s hjk] at hj
      exact hjk (s.unique hj hi)
    exact stepCell_subCod_k s j hj'
  · have hmem : inDom ((step s).cell i.castSucc) (x : ℝ) := by
      change inDom (stepCell s i.castSucc) (x : ℝ)
      rw [stepCell_castSucc_ne s hik]
      exact hi
    have hjeq : j = i.castSucc := (step s).unique hj hmem
    subst hjeq
    change subCod (stepCell s i.castSucc) (s.cell i)
    rw [stepCell_castSucc_ne s hik]
    exact subCod_refl _

private noncomputable def st : (n : ℕ) → State n
  | 0 => state0
  | n + 1 => step (st n)

private lemma st_val_eq {k n : ℕ} (hkn : k ≤ n) :
    ((st n).cell ⟨k, by omega⟩).val = ((st k).cell ⟨k, Nat.lt_succ_self k⟩).val := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    rfl
  | succ m ih =>
    rcases eq_or_lt_of_le hkn with rfl | hlt
    · rfl
    · have hkm : k ≤ m := by omega
      have h1 : (⟨k, by omega⟩ : Fin (m + 2)) = (⟨k, by omega⟩ : Fin (m + 1)).castSucc := rfl
      rw [h1]
      change (stepCell (st m) (⟨k, by omega⟩ : Fin (m + 1)).castSucc).val = _
      rw [stepCell_castSucc_val, ih hkm]

private lemma st_subCod {n m : ℕ} (hnm : n ≤ m) {x : ℚ} {i : Fin (n + 1)} {j : Fin (m + 1)}
    (hi : inDom ((st n).cell i) (x : ℝ)) (hj : inDom ((st m).cell j) (x : ℝ)) :
    subCod ((st m).cell j) ((st n).cell i) := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this
    have hij : i = j := (st 0).unique hi hj
    subst hij
    exact subCod_refl _
  | succ m ih =>
    rcases eq_or_lt_of_le hnm with rfl | hlt
    · have hij : i = j := (st (m + 1)).unique hi hj
      subst hij
      exact subCod_refl _
    · have hnm' : n ≤ m := by omega
      rcases (st m).cover x with ⟨l, hl⟩
      exact subCod_trans (step_subCod (st m) hl hj) (ih hnm' hl)

private noncomputable def f (x : ℚ) : ℚ :=
  ((st (enumQ.symm x)).cell ⟨enumQ.symm x, Nat.lt_succ_self _⟩).val

private lemma f_q (k : ℕ) :
    f (q k) = ((st k).cell ⟨k, Nat.lt_succ_self k⟩).val := by
  change ((st (enumQ.symm (enumQ k))).cell ⟨enumQ.symm (enumQ k), Nat.lt_succ_self _⟩).val = _
  generalize h : enumQ.symm (enumQ k) = m
  rw [enumQ.symm_apply_apply] at h
  subst h
  rfl

private lemma f_eq_cell_val {k n : ℕ} (hkn : k ≤ n) :
    ((st n).cell ⟨k, by omega⟩).val = f (q k) := by
  rw [st_val_eq hkn, f_q]

private lemma f_mem_cod {n : ℕ} {x : ℚ} {i : Fin (n + 1)}
    (hi : inDom ((st n).cell i) (x : ℝ)) :
    ((st n).cell i).ylo < f x ∧ f x < ((st n).cell i).yhi := by
  set r := enumQ.symm x
  have hqr : q r = x := enumQ.apply_symm_apply x
  set m := max n r
  have hnm : n ≤ m := le_max_left n r
  have hrm : r ≤ m := le_max_right n r
  let j : Fin (m + 1) := ⟨r, by omega⟩
  have hj : inDom ((st m).cell j) (x : ℝ) := by
    have := (st m).mem_dom j
    simpa [j, hqr] using this
  have hsub := st_subCod hnm hi hj
  have hval := (st m).mem_val j
  have hfeq : ((st m).cell j).val = f x := by
    have := f_eq_cell_val hrm
    simpa [j, hqr] using this
  rw [hfeq] at hval
  exact ⟨lt_of_le_of_lt hsub.1 hval.1, lt_of_lt_of_le hval.2 hsub.2⟩

private lemma f_strictMono : StrictMono f := by
  intro x y hxy
  set i := enumQ.symm x
  set j := enumQ.symm y
  have hqi : q i = x := enumQ.apply_symm_apply x
  have hqj : q j = y := enumQ.apply_symm_apply y
  set m := max i j
  have him : i ≤ m := le_max_left i j
  have hjm : j ≤ m := le_max_right i j
  let i' : Fin (m + 1) := ⟨i, by omega⟩
  let j' : Fin (m + 1) := ⟨j, by omega⟩
  have hord := ((st m).ord i' j' (by simpa [i', j', hqi, hqj] using hxy)).2
  have hvi := (st m).mem_val i'
  have hvj := (st m).mem_val j'
  have hfi : ((st m).cell i').val = f x := by
    have := f_eq_cell_val him
    simpa [i', hqi] using this
  have hfj : ((st m).cell j').val = f y := by
    have := f_eq_cell_val hjm
    simpa [j', hqj] using this
  linarith

private lemma step_leave_bound {m k : ℕ} (hkm : k ≤ m) {x : ℚ}
    (hin : inDom ((st m).cell ⟨k, by omega⟩) (x : ℝ))
    (hout : ¬ inDom ((st (m + 1)).cell ⟨k, by omega⟩) (x : ℝ)) :
    |(f x : ℝ) - (f (q k) : ℝ)| ≤ (1 / 2 : ℝ) ^ (m + 1) * |(x : ℝ) - (q k : ℝ)| := by
  let kf : Fin (m + 1) := ⟨k, by omega⟩
  have hks : kf = stepIdx (st m) := by
    by_contra hne
    apply hout
    have h1 : (⟨k, by omega⟩ : Fin (m + 2)) = kf.castSucc := rfl
    rw [h1]
    change inDom (stepCell (st m) kf.castSucc) (x : ℝ)
    rw [stepCell_castSucc_ne (st m) hne]
    exact hin
  have hlast_in : inDom ((st (m + 1)).cell (Fin.last (m + 1))) (x : ℝ) := by
    rcases (st (m + 1)).cover x with ⟨j, hj⟩
    by_cases hjl : j = Fin.last (m + 1)
    · rwa [← hjl]
    · by_cases hjk : j = kf.castSucc
      · exact False.elim (hout (by simpa [kf, hjk] using hj))
      · have hjlt : j.1 < m + 1 := by
          have hne : j.1 ≠ m + 1 := fun h => hjl (Fin.ext h)
          omega
        let j' : Fin (m + 1) := ⟨j.1, hjlt⟩
        have hj'ne : j' ≠ stepIdx (st m) := by
          intro h
          apply hjk
          rw [hks, ← h]
          rfl
        have hjeq : j = j'.castSucc := Fin.ext rfl
        rw [hjeq] at hj
        change inDom (stepCell (st m) j'.castSucc) (x : ℝ) at hj
        rw [stepCell_castSucc_ne (st m) hj'ne] at hj
        have hsame := (st m).unique hj hin
        exact False.elim (hj'ne (hsame.trans hks))
  have hfcod := f_mem_cod hlast_in
  have hvalk : ((st m).cell (stepIdx (st m))).val = f (q k) := by
    rw [← hks]
    exact f_eq_cell_val hkm
  set η := stepEta (st m)
  have hηslope : η ≤ |q (m + 1) - q (stepIdx (st m)).1| / (4 * (2 : ℚ) ^ (m + 1)) :=
    stepEta_le_slope (st m)
  have hkval : (stepIdx (st m)).1 = k := by
    simpa [kf] using (congrArg Fin.val hks).symm
  have hfy_diff : |(f x : ℝ) - (f (q k) : ℝ)| ≤ (η : ℝ) := by
    have hq_diff : |f x - f (q k)| ≤ η := by
      rw [abs_le]
      change ((stepCell (st m) (Fin.last (m + 1))).ylo < f x ∧
        f x < (stepCell (st m) (Fin.last (m + 1))).yhi) at hfcod
      simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte] at hfcod
      rw [hvalk] at hfcod
      split_ifs at hfcod <;> constructor <;> linarith
    exact_mod_cast hq_diff
  have hx_dist : |(q (m + 1) : ℝ) - (q k : ℝ)| / 4 ≤ |(x : ℝ) - (q k : ℝ)| := by
    change inDom (stepCell (st m) (Fin.last (m + 1))) (x : ℝ) at hlast_in
    simp only [stepCell, Fin.val_last, lt_self_iff_false, ↓reduceDIte, inDom, stepGamma] at hlast_in
    by_cases hlt : q (stepIdx (st m)).1 < q (m + 1)
    · rw [if_pos hlt] at hlast_in
      have hlt' : q k < q (m + 1) := by rwa [hkval] at hlt
      have hγ : (q k : ℝ) + ((q (m + 1) : ℝ) - (q k : ℝ)) / 4 < irrMid (q k) (q (m + 1)) :=
        irrMid_gt_add_quarter hlt'
      have hxγ : irrMid (q k) (q (m + 1)) < (x : ℝ) := by
        simpa [ltLeft, hkval, hlt'] using hlast_in.1
      have hpos : (0 : ℝ) < (q (m + 1) : ℝ) - (q k : ℝ) := by
        have : (q k : ℝ) < (q (m + 1) : ℝ) := by exact_mod_cast hlt'
        linarith
      have habs1 : |(q (m + 1) : ℝ) - (q k : ℝ)| = (q (m + 1) : ℝ) - (q k : ℝ) :=
        abs_of_nonneg (by linarith)
      have habs2 : |(x : ℝ) - (q k : ℝ)| = (x : ℝ) - (q k : ℝ) :=
        abs_of_nonneg (by linarith)
      rw [habs1, habs2]
      linarith
    · rw [if_neg hlt] at hlast_in
      have hgt : q (m + 1) < q (stepIdx (st m)).1 :=
        lt_of_le_of_ne (not_lt.mp hlt) (stepIdx_ne (st m)).symm
      have hgt' : q (m + 1) < q k := by rwa [hkval] at hgt
      have hγ : irrMid (q (m + 1)) (q k) + ((q k : ℝ) - (q (m + 1) : ℝ)) / 4 < (q k : ℝ) :=
        irrMid_add_quarter_lt hgt'
      have hxγ : (x : ℝ) < irrMid (q (m + 1)) (q k) := by
        simpa [ltRight, hkval, not_lt.mpr (le_of_lt hgt')] using hlast_in.2
      have hpos : (0 : ℝ) < (q k : ℝ) - (q (m + 1) : ℝ) := by
        have : (q (m + 1) : ℝ) < (q k : ℝ) := by exact_mod_cast hgt'
        linarith
      have habs1 : |(q (m + 1) : ℝ) - (q k : ℝ)| = (q k : ℝ) - (q (m + 1) : ℝ) := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have habs2 : |(x : ℝ) - (q k : ℝ)| = (q k : ℝ) - (x : ℝ) := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs1, habs2]
      linarith
  have hη_real : (η : ℝ) ≤ (|(q (m + 1) : ℝ) - (q k : ℝ)| / 4) * (1 / 2 : ℝ) ^ (m + 1) := by
    have h1 : (η : ℝ) ≤ |(q (m + 1) : ℝ) - (q k : ℝ)| / (4 * (2 : ℝ) ^ (m + 1)) := by
      rw [hkval] at hηslope
      have hcast : (η : ℝ) ≤ ((|q (m + 1) - q k| / (4 * (2 : ℚ) ^ (m + 1)) : ℚ) : ℝ) := by
        exact_mod_cast hηslope
      simpa only [Rat.cast_div, Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_pow] using hcast
    calc (η : ℝ)
        ≤ |(q (m + 1) : ℝ) - (q k : ℝ)| / (4 * (2 : ℝ) ^ (m + 1)) := h1
      _ = (|(q (m + 1) : ℝ) - (q k : ℝ)| / 4) * (1 / 2 : ℝ) ^ (m + 1) := by
          rw [one_div, inv_pow]; ring
  have hpow_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
  calc |(f x : ℝ) - (f (q k) : ℝ)|
      ≤ (η : ℝ) := hfy_diff
    _ ≤ (|(q (m + 1) : ℝ) - (q k : ℝ)| / 4) * (1 / 2 : ℝ) ^ (m + 1) := hη_real
    _ = (1 / 2 : ℝ) ^ (m + 1) * (|(q (m + 1) : ℝ) - (q k : ℝ)| / 4) := by ring
    _ ≤ (1 / 2 : ℝ) ^ (m + 1) * |(x : ℝ) - (q k : ℝ)| :=
        mul_le_mul_of_nonneg_left hx_dist hpow_nonneg

private lemma exists_leave_stage {k N r : ℕ} (hkN : k ≤ N) (hNr : N ≤ r) {x : ℚ}
    (hin : inDom ((st N).cell ⟨k, by omega⟩) (x : ℝ))
    (hout : ¬ inDom ((st r).cell ⟨k, by omega⟩) (x : ℝ)) :
    ∃ m : ℕ, ∃ hm : N ≤ m, m < r ∧
      inDom ((st m).cell ⟨k, by omega⟩) (x : ℝ) ∧
      ¬ inDom ((st (m + 1)).cell ⟨k, by omega⟩) (x : ℝ) := by
  induction r with
  | zero =>
    have : N = 0 := by omega
    subst this
    exact False.elim (hout hin)
  | succ r' ih =>
    rcases eq_or_lt_of_le hNr with rfl | hlt
    · exact False.elim (hout hin)
    · have hNr' : N ≤ r' := by omega
      by_cases hr' : inDom ((st r').cell ⟨k, by omega⟩) (x : ℝ)
      · exact ⟨r', hNr', Nat.lt_succ_self r', hr', hout⟩
      · rcases ih hNr' hin hr' with ⟨m, hm1, hm2, hm3, hm4⟩
        exact ⟨m, hm1, lt_trans hm2 (Nat.lt_succ_self r'), hm3, hm4⟩

private lemma f_hasDerivAt_zero (a : ℚ) : HasDerivAt f 0 a := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set k := enumQ.symm a
  have hqk : q k = a := enumQ.apply_symm_apply a
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set N := max k N0
  have hkN : k ≤ N := le_max_left k N0
  have hN0N : N0 ≤ N := le_max_right k N0
  have hdomk : inDom ((st N).cell ⟨k, by omega⟩) (a : ℝ) := by
    have := (st N).mem_dom ⟨k, by omega⟩
    simpa [hqk] using this
  obtain ⟨δ, hδpos, hδ⟩ := exists_ball_inDom hdomk
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hdist : |(x : ℝ) - (a : ℝ)| < δ := by
    simpa [Rat.dist_eq] using hx
  have hnorm_lhs : ‖f x - f a - (x - a) • (0 : ℚ)‖ = |(f x : ℝ) - (f a : ℝ)| := by
    simp only [smul_zero, sub_zero, ← dist_eq_norm, Rat.dist_eq]
  have hnorm_rhs : ‖x - a‖ = |(x : ℝ) - (a : ℝ)| := by
    rw [← dist_eq_norm, Rat.dist_eq]
  rw [hnorm_lhs, hnorm_rhs]
  by_cases hxa : x = a
  · subst hxa
    simp
  · have hxin : inDom ((st N).cell ⟨k, by omega⟩) (x : ℝ) := hδ (x : ℝ) hdist
    set r := enumQ.symm x
    have hqr : q r = x := enumQ.apply_symm_apply x
    have hrk : r ≠ k := fun h => hxa (by rw [← hqr, h, hqk])
    have hNr : N ≤ r := by
      by_contra hlt
      push Not at hlt
      have hx_in_r : inDom ((st N).cell ⟨r, by omega⟩) (x : ℝ) := by
        have := (st N).mem_dom ⟨r, by omega⟩
        simpa [hqr] using this
      have hsame := (st N).unique hx_in_r hxin
      exact hrk (congrArg Fin.val hsame)
    have hout : ¬ inDom ((st r).cell ⟨k, by omega⟩) (x : ℝ) := by
      intro hmem
      have hx_in_r : inDom ((st r).cell ⟨r, Nat.lt_succ_self r⟩) (x : ℝ) := by
        have := (st r).mem_dom ⟨r, Nat.lt_succ_self r⟩
        simpa [hqr] using this
      have hsame := (st r).unique hx_in_r hmem
      exact hrk (congrArg Fin.val hsame)
    obtain ⟨m, hmN, _, hmin, hmout⟩ := exists_leave_stage hkN hNr hxin hout
    have hbound := step_leave_bound (le_trans hkN hmN) hmin hmout
    rw [hqk] at hbound
    have hpow_le : (1 / 2 : ℝ) ^ (m + 1) ≤ ε := by
      have h2 : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ N0 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      exact le_trans h2 (le_of_lt hN0)
    exact le_trans hbound (mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _))

end OMA.P1911440

theorem OMA.solution : type_of% @OMA.S_mse_1911440.main :=
  ⟨OMA.P1911440.f, OMA.P1911440.f_strictMono, OMA.P1911440.f_hasDerivAt_zero⟩
