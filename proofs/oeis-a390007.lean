import OMAStatements.S_oeis_a390007
import Mathlib.Tactic.Linarith

-- Problem: A390007 (Rodrigo): for every integer n ≥ 3, the square of side n has a unique minimum-defect
--   set of three distinct rectangular tiles, except n = 4.
-- Credit: @alan-phobos-claude
-- Proof: the optimum is always the tee with a = ⌊(n+1)/3⌋ and b = ⌊(n−1)/2⌋. Its defect D is 8q, 5q+1,
--   8q+2, 4q+2, 8q+6 or 5q+4 for n = 6q + r, r = 0, …, 5. A tee (a, b) with defect at most D has
--   (n−2b)(n−a) ≤ D, n·a − b(n−a) ≤ D and (n−b)(n−a) − n·a ≤ D. If n − 2b is larger than at the
--   optimum (so ≥ 3, or ≥ 4 for even n), the first two force 2n² − nD − 2D ≤ 0 (resp. 8n² − 3nD − 8D ≤ 0),
--   which is false. Otherwise b is the optimal one, and the last two pin a down. Strips cost
--   n(z − x) ≥ 2n > D. At n = 4 the tees (1, 1) and (2, 1) tie with defect 6.

open OMA.S_oeis_a390007

namespace A390007

lemma spread_le {x l h D : ℤ} (hs : spread x l h ≤ D) : h - l ≤ D ∧ x - l ≤ D ∧ h - x ≤ D := by
  unfold spread at hs
  exact ⟨le_trans (le_max_left _ _) hs, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs⟩

/-- `n = 6q+0`: the only tee with defect at most `8*q` is `(2*q, 3*q-1)`. -/
lemma case0 (q a b : ℤ) (hq : 1 ≤ q) (ha : 0 < a) (ha' : a < (6*q)) (hb : 0 < b) (hb' : 2*b < (6*q))
    (hd : spread ((6*q)*a) (b*((6*q)-a)) (((6*q)-b)*((6*q)-a)) ≤ 8*q) : a = 2*q ∧ b = 3*q-1 := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q-1 := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q)-2*b) - 4 := by omega
    have hm : (0:ℤ) ≤ (6*q)-a := by omega
    have h3m : 4*((6*q)-a) ≤ 8*q := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q) by omega) (show (0:ℤ) ≤ 8*q - 4*((6*q)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- `n = 6q+1`: the only tee with defect at most `5*q+1` is `(2*q, 3*q)`. -/
lemma case1 (q a b : ℤ) (hq : 1 ≤ q) (ha : 0 < a) (ha' : a < (6*q+1)) (hb : 0 < b) (hb' : 2*b < (6*q+1))
    (hd : spread ((6*q+1)*a) (b*((6*q+1)-a)) (((6*q+1)-b)*((6*q+1)-a)) ≤ 5*q+1) : a = 2*q ∧ b = 3*q := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q+1)-2*b) - 3 := by omega
    have hm : (0:ℤ) ≤ (6*q+1)-a := by omega
    have h3m : 3*((6*q+1)-a) ≤ 5*q+1 := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q+1) by omega) (show (0:ℤ) ≤ 5*q+1 - 3*((6*q+1)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- `n = 6q+2`: the only tee with defect at most `8*q+2` is `(2*q+1, 3*q)`. -/
lemma case2 (q a b : ℤ) (hq : 1 ≤ q) (ha : 0 < a) (ha' : a < (6*q+2)) (hb : 0 < b) (hb' : 2*b < (6*q+2))
    (hd : spread ((6*q+2)*a) (b*((6*q+2)-a)) (((6*q+2)-b)*((6*q+2)-a)) ≤ 8*q+2) : a = 2*q+1 ∧ b = 3*q := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q+2)-2*b) - 4 := by omega
    have hm : (0:ℤ) ≤ (6*q+2)-a := by omega
    have h3m : 4*((6*q+2)-a) ≤ 8*q+2 := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q+2) by omega) (show (0:ℤ) ≤ 8*q+2 - 4*((6*q+2)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+1+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q+1-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- `n = 6q+3`: the only tee with defect at most `4*q+2` is `(2*q+1, 3*q+1)`. -/
lemma case3 (q a b : ℤ) (hq : 0 ≤ q) (ha : 0 < a) (ha' : a < (6*q+3)) (hb : 0 < b) (hb' : 2*b < (6*q+3))
    (hd : spread ((6*q+3)*a) (b*((6*q+3)-a)) (((6*q+3)-b)*((6*q+3)-a)) ≤ 4*q+2) : a = 2*q+1 ∧ b = 3*q+1 := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q+1 := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q+3)-2*b) - 3 := by omega
    have hm : (0:ℤ) ≤ (6*q+3)-a := by omega
    have h3m : 3*((6*q+3)-a) ≤ 4*q+2 := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q+3) by omega) (show (0:ℤ) ≤ 4*q+2 - 3*((6*q+3)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+1+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q+1-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- `n = 6q+4`: the only tee with defect at most `8*q+6` is `(2*q+1, 3*q+1)`. -/
lemma case4 (q a b : ℤ) (hq : 1 ≤ q) (ha : 0 < a) (ha' : a < (6*q+4)) (hb : 0 < b) (hb' : 2*b < (6*q+4))
    (hd : spread ((6*q+4)*a) (b*((6*q+4)-a)) (((6*q+4)-b)*((6*q+4)-a)) ≤ 8*q+6) : a = 2*q+1 ∧ b = 3*q+1 := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q+1 := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q+4)-2*b) - 4 := by omega
    have hm : (0:ℤ) ≤ (6*q+4)-a := by omega
    have h3m : 4*((6*q+4)-a) ≤ 8*q+6 := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q+4) by omega) (show (0:ℤ) ≤ 8*q+6 - 4*((6*q+4)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+1+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q+1-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- `n = 6q+5`: the only tee with defect at most `5*q+4` is `(2*q+2, 3*q+2)`. -/
lemma case5 (q a b : ℤ) (hq : 0 ≤ q) (ha : 0 < a) (ha' : a < (6*q+5)) (hb : 0 < b) (hb' : 2*b < (6*q+5))
    (hd : spread ((6*q+5)*a) (b*((6*q+5)-a)) (((6*q+5)-b)*((6*q+5)-a)) ≤ 5*q+4) : a = 2*q+2 ∧ b = 3*q+2 := by
  obtain ⟨e1, e2, e3⟩ := spread_le hd
  have hbB : b = 3*q+2 := by
    by_contra hne
    have hg : (0:ℤ) ≤ ((6*q+5)-2*b) - 3 := by omega
    have hm : (0:ℤ) ≤ (6*q+5)-a := by omega
    have h3m : 3*((6*q+5)-a) ≤ 5*q+4 := by nlinarith [mul_nonneg hg hm]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (6*q+5) by omega) (show (0:ℤ) ≤ 5*q+4 - 3*((6*q+5)-a) by omega),
      mul_nonneg hg hm, mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q by omega)]
  subst hbB
  refine ⟨le_antisymm ?_ ?_, rfl⟩
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ a - (2*q+2+1) by omega) (show (0:ℤ) ≤ q by omega)]
  · by_contra h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (2*q+2-1) - a by omega) (show (0:ℤ) ≤ q by omega)]

/-- The optimal set: the tee with `a = ⌊(n+1)/3⌋` and `b = ⌊(n-1)/2⌋`. -/
def starTile (n : ℤ) : TileSet := .tee ((n + 1) / 3) ((n - 1) / 2)

lemma key (n : ℤ) (hn : 3 ≤ n) : defect n (starTile n) < 2 * n ∧
    ∀ a b, valid n (.tee a b) → n ≠ 4 → defect n (.tee a b) ≤ defect n (starTile n) →
      a = (n + 1) / 3 ∧ b = (n - 1) / 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = n / 6 := ⟨_, rfl⟩
  rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5) with
    hr | hr | hr | hr | hr | hr
  · have hn' : n = 6*q := by omega
    have hA : (n + 1) / 3 = 2*q := by omega
    have hB : (n - 1) / 2 = 3*q-1 := by omega
    have hD : defect n (starTile n) ≤ 8*q := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case0 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'
  · have hn' : n = 6*q+1 := by omega
    have hA : (n + 1) / 3 = 2*q := by omega
    have hB : (n - 1) / 2 = 3*q := by omega
    have hD : defect n (starTile n) ≤ 5*q+1 := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case1 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'
  · have hn' : n = 6*q+2 := by omega
    have hA : (n + 1) / 3 = 2*q+1 := by omega
    have hB : (n - 1) / 2 = 3*q := by omega
    have hD : defect n (starTile n) ≤ 8*q+2 := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case2 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'
  · have hn' : n = 6*q+3 := by omega
    have hA : (n + 1) / 3 = 2*q+1 := by omega
    have hB : (n - 1) / 2 = 3*q+1 := by omega
    have hD : defect n (starTile n) ≤ 4*q+2 := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case3 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'
  · have hn' : n = 6*q+4 := by omega
    have hA : (n + 1) / 3 = 2*q+1 := by omega
    have hB : (n - 1) / 2 = 3*q+1 := by omega
    have hD : defect n (starTile n) ≤ 8*q+6 := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case4 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'
  · have hn' : n = 6*q+5 := by omega
    have hA : (n + 1) / 3 = 2*q+2 := by omega
    have hB : (n - 1) / 2 = 3*q+2 := by omega
    have hD : defect n (starTile n) ≤ 5*q+4 := by
      simp only [defect, starTile, spread, hA, hB]; subst hn'
      refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
    refine ⟨by omega, fun a b hv h4 hd => ?_⟩
    simp only [valid] at hv
    have hd' := le_trans hd hD
    rw [hA, hB]; subst hn'; simp only [defect] at hd'
    exact case5 q a b (by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hd'

/-- At `n = 4` the tees `(1, 1)` and `(2, 1)` are both optimal (defect 6). -/
lemma four_optimal (a : ℤ) (ha : a = 1 ∨ a = 2) : optimal 4 (.tee a 1) := by
  refine ⟨by simp only [valid]; omega, fun t ht => ?_⟩
  cases t with
  | strips x y z => simp only [valid] at ht; omega
  | tee c d =>
    simp only [valid] at ht
    obtain rfl : d = 1 := by omega
    rcases ha with rfl | rfl <;> rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> decide

end A390007

open A390007 in
theorem OMA.solution : type_of% @OMA.S_oeis_a390007.main := by
  intro n hn
  obtain ⟨hlt, huniq⟩ := key n hn
  have hsv : valid n (starTile n) := by simp only [starTile, valid]; omega
  have hbest : n ≠ 4 → ∀ t, valid n t → t ≠ starTile n → defect n (starTile n) < defect n t := by
    intro h4 t ht hne
    cases t with
    | strips x y z =>
      simp only [valid] at ht
      rw [show defect n (.strips x y z) = n * (z - x) from rfl]
      nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ z - x by omega) (show (0:ℤ) ≤ n by omega)]
    | tee a b =>
      by_contra hle
      obtain ⟨rfl, rfl⟩ := huniq a b ht h4 (not_lt.1 hle)
      exact hne rfl
  constructor
  · rintro ⟨s, -, hu⟩ rfl
    have h1 := hu _ (four_optimal 1 (Or.inl rfl))
    have h2 := hu _ (four_optimal 2 (Or.inr rfl))
    rw [← h2] at h1
    cases h1
  · intro h4
    refine ⟨starTile n, ⟨hsv, fun t ht => ?_⟩, fun s hs => ?_⟩
    · by_cases he : t = starTile n
      · rw [he]
      · exact (hbest h4 t ht he).le
    · by_contra hne
      exact absurd (hs.2 _ hsv) (not_le.2 (hbest h4 s hs.1 hne))
