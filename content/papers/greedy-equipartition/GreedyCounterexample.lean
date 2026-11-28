import Mathlib

/-! A coordinate certificate for the greedy equipartition counterexample.
A chord is specified by two boundary edges and two independent real parameters.
The signed shoelace sum measures twice the area swept along the counterclockwise
boundary from the first endpoint to the second. Reversing sides complements
this area. Both orientations are included below. -/

namespace GreedyEquipartition

abbrev Point := ℝ × ℝ

def sidePoint (p q : Point) (t : ℝ) : Point :=
  (p.1 + (q.1 - p.1)*t, p.2 + (q.2 - p.2)*t)

def cross (p q : Point) : ℝ := p.1*q.2 - p.2*q.1

def lengthSq (p q : Point) : ℝ := (p.1-q.1)^2 + (p.2-q.2)^2

def shoelace (p : Point) : List Point → Point → ℝ
  | [], last => cross p last
  | q :: qs, last => cross p q + shoelace q qs last

def pointOn (v : Fin 4 → Point) (i : Fin 4) := sidePoint (v i) (v (i+1))

def cutArea2 (v : Fin 4 → Point) (i j : Fin 4) (s t : ℝ) : ℝ :=
  let p := pointOn v i s
  let q := pointOn v j t
  let middle := ((List.finRange 4).filter (fun k => i < k ∧ k ≤ j)).map v
  shoelace p middle q + cross q p

def quad : Fin 4 → Point := ![(0,0), (8,0), (8,4), (2,6)]
def rest : Fin 4 → Point := ![(0,0), (8,3), (8,4), (2,6)]

def firstSeam (p q : Point) : Prop :=
  (p = (0,0) ∧ q = (8,3)) ∨ (q = (0,0) ∧ p = (8,3))

-- Each row bounds one pair of edges for a specified area. After the area
-- equation eliminates t, the slack is a polynomial in s. Its expansion
-- in nonnegative powers of (s-lo) and (hi-s) certifies the strict interior
-- bound. The endpoint calculations also identify every tie.

private theorem a01 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -32 * s * t + 32 * t = 24) :
    64 * s^2 - 128 * s + 16 * t^2 + 64 < 73 ∨ firstSeam (8 * s, 0) (8, 4 * t) := by
  have hb : 0 ≤ 32 - 32 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 1/4 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 3/4 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1/4
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1/4) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (7208960) * (s - (0))^1 * ((1/4) - s)^3 + (16531456) * (s - (0))^2 * ((1/4) - s)^2 + (12484608) * (s - (0))^3 * ((1/4) - s)^1 + (3096576) * (s - (0))^4 * ((1/4) - s)^0 := by positivity
  have hid : ((73) - (64 * s^2 - 128 * s + 16 * t^2 + 64)) * (32 - 32 * s)^2 = (7208960) * (s - (0))^1 * ((1/4) - s)^3 + (16531456) * (s - (0))^2 * ((1/4) - s)^2 + (12484608) * (s - (0))^3 * ((1/4) - s)^1 + (3096576) * (s - (0))^4 * ((1/4) - s)^0 := by
    linear_combination (512 * s * t - 512 * t - 384) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (32 - 32 * s))
  linarith only [hid, hpos, hn]

private theorem a02 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -16 * s * t - 32 * s + 40 * t + 32 = 24) :
    64 * s^2 + 96 * s * t - 128 * s + 40 * t^2 - 80 * t + 80 < 73 ∨ firstSeam (8 * s, 0) (8 - 6 * t, 2 * t + 4) := by
  have hb : 0 ≤ 40 - 16 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 1/4 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 1/4
  · subst s
    have hT : t = 0 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (1/4) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (86016) * (s - (1/4))^0 * ((1) - s)^4 + (2203648/3) * (s - (1/4))^1 * ((1) - s)^3 + (9293824/9) * (s - (1/4))^2 * ((1) - s)^2 + (3620864/9) * (s - (1/4))^3 * ((1) - s)^1 + (16384/9) * (s - (1/4))^4 * ((1) - s)^0 := by positivity
  have hid : ((73) - (64 * s^2 + 96 * s * t - 128 * s + 40 * t^2 - 80 * t + 80)) * (40 - 16 * s)^2 = (86016) * (s - (1/4))^0 * ((1) - s)^4 + (2203648/3) * (s - (1/4))^1 * ((1) - s)^3 + (9293824/9) * (s - (1/4))^2 * ((1) - s)^2 + (3620864/9) * (s - (1/4))^3 * ((1) - s)^1 + (16384/9) * (s - (1/4))^4 * ((1) - s)^0 := by
    linear_combination (1536 * s^2 + 640 * s * t - 6400 * s - 1600 * t + 3520) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (40 - 16 * s))
  linarith only [hid, hpos, hn]

private theorem a03 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : 48 * s * t - 48 * s + 72 = 24) :
    64 * s^2 + 32 * s * t - 32 * s + 40 * t^2 - 80 * t + 40 < 73 ∨ firstSeam (8 * s, 0) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 48 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 1 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 1
  · subst s
    have hT : t = 0 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  exact (hEnd0 (le_antisymm hhi hlo)).elim
private theorem a12 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -24 * s * t + 24 * t = 24) :
    16 * s^2 - 16 * s * t - 32 * s + 40 * t^2 + 16 * t + 16 < 73 ∨ firstSeam (8, 4 * s) (8 - 6 * t, 2 * t + 4) := by
  have hb : 0 ≤ 24 - 24 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 0 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  exact (hEnd0 (le_antisymm hhi hlo)).elim
private theorem a13 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -8 * s * t - 24 * s + 48 * t + 24 = 24) :
    16 * s^2 + 48 * s * t - 48 * s + 40 * t^2 - 48 * t + 72 < 73 ∨ firstSeam (8, 4 * s) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 48 - 8 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 0 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1
  · subst s
    have hT : t = 3/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (2304) * (s - (0))^0 * ((1) - s)^4 + (174336) * (s - (0))^1 * ((1) - s)^3 + (347968) * (s - (0))^2 * ((1) - s)^2 + (206720) * (s - (0))^3 * ((1) - s)^1 + (29760) * (s - (0))^4 * ((1) - s)^0 := by positivity
  have hid : ((73) - (16 * s^2 + 48 * s * t - 48 * s + 40 * t^2 - 48 * t + 72)) * (48 - 8 * s)^2 = (2304) * (s - (0))^0 * ((1) - s)^4 + (174336) * (s - (0))^1 * ((1) - s)^3 + (347968) * (s - (0))^2 * ((1) - s)^2 + (206720) * (s - (0))^3 * ((1) - s)^1 + (29760) * (s - (0))^4 * ((1) - s)^0 := by
    linear_combination (384 * s^2 + 320 * s * t - 3648 * s - 1920 * t + 2304) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (48 - 8 * s))
  linarith only [hid, hpos, hn]

private theorem a23 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -40 * s * t + 40 * t = 24) :
    40 * s^2 - 80 * s + 40 * t^2 + 40 < 73 ∨ firstSeam (8 - 6 * s, 2 * s + 4) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 40 - 40 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 2/5 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 3/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 2/5
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (2/5) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (1162500) * (s - (0))^0 * ((2/5) - s)^4 + (5000000) * (s - (0))^1 * ((2/5) - s)^3 + (6355000) * (s - (0))^2 * ((2/5) - s)^2 + (3000000) * (s - (0))^3 * ((2/5) - s)^1 + (418500) * (s - (0))^4 * ((2/5) - s)^0 := by positivity
  have hid : ((73) - (40 * s^2 - 80 * s + 40 * t^2 + 40)) * (40 - 40 * s)^2 = (1162500) * (s - (0))^0 * ((2/5) - s)^4 + (5000000) * (s - (0))^1 * ((2/5) - s)^3 + (6355000) * (s - (0))^2 * ((2/5) - s)^2 + (3000000) * (s - (0))^3 * ((2/5) - s)^1 + (418500) * (s - (0))^4 * ((2/5) - s)^0 := by
    linear_combination (1600 * s * t - 1600 * t - 960) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (40 - 40 * s))
  linarith only [hid, hpos, hn]

private theorem b01 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -32 * s * t + 32 * t = 48) :
    64 * s^2 - 128 * s + 16 * t^2 + 64 < 73 ∨ firstSeam (8 * s, 0) (8, 4 * t) := by
  have hb : 0 ≤ 32 - 32 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  nlinarith
private theorem b02 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -16 * s * t - 32 * s + 40 * t + 32 = 48) :
    64 * s^2 + 96 * s * t - 128 * s + 40 * t^2 - 80 * t + 80 < 73 ∨ firstSeam (8 * s, 0) (8 - 6 * t, 2 * t + 4) := by
  have hb : 0 ≤ 40 - 16 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 1/2 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 2/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1/2
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1/2) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (476160) * (s - (0))^0 * ((1/2) - s)^4 + (3450880) * (s - (0))^1 * ((1/2) - s)^3 + (5702656) * (s - (0))^2 * ((1/2) - s)^2 + (3284992) * (s - (0))^3 * ((1/2) - s)^1 + (540672) * (s - (0))^4 * ((1/2) - s)^0 := by positivity
  have hid : ((73) - (64 * s^2 + 96 * s * t - 128 * s + 40 * t^2 - 80 * t + 80)) * (40 - 16 * s)^2 = (476160) * (s - (0))^0 * ((1/2) - s)^4 + (3450880) * (s - (0))^1 * ((1/2) - s)^3 + (5702656) * (s - (0))^2 * ((1/2) - s)^2 + (3284992) * (s - (0))^3 * ((1/2) - s)^1 + (540672) * (s - (0))^4 * ((1/2) - s)^0 := by
    linear_combination (1536 * s^2 + 640 * s * t - 6400 * s - 1600 * t + 2560) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (40 - 16 * s))
  linarith only [hid, hpos, hn]

private theorem b03 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : 48 * s * t - 48 * s + 72 = 48) :
    64 * s^2 + 32 * s * t - 32 * s + 40 * t^2 - 80 * t + 40 < 73 ∨ firstSeam (8 * s, 0) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 48 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 1/2 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 1/2
  · subst s
    have hT : t = 0 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1
  · subst s
    have hT : t = 1/2 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (1/2) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (304128) * (s - (1/2))^0 * ((1) - s)^4 + (2267136) * (s - (1/2))^1 * ((1) - s)^3 + (4912128) * (s - (1/2))^2 * ((1) - s)^2 + (3649536) * (s - (1/2))^3 * ((1) - s)^1 + (552960) * (s - (1/2))^4 * ((1) - s)^0 := by positivity
  have hid : ((73) - (64 * s^2 + 32 * s * t - 32 * s + 40 * t^2 - 80 * t + 40)) * (48 * s)^2 = (304128) * (s - (1/2))^0 * ((1) - s)^4 + (2267136) * (s - (1/2))^1 * ((1) - s)^3 + (4912128) * (s - (1/2))^2 * ((1) - s)^2 + (3649536) * (s - (1/2))^3 * ((1) - s)^1 + (552960) * (s - (1/2))^4 * ((1) - s)^0 := by
    linear_combination (-1536 * s^2 - 1920 * s * t + 1920 * s + 960) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (48 * s))
  linarith only [hid, hpos, hn]

private theorem b12 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -24 * s * t + 24 * t = 48) :
    16 * s^2 - 16 * s * t - 32 * s + 40 * t^2 + 16 * t + 16 < 73 ∨ firstSeam (8, 4 * s) (8 - 6 * t, 2 * t + 4) := by
  have hb : 0 ≤ 24 - 24 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  nlinarith
private theorem b13 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -8 * s * t - 24 * s + 48 * t + 24 = 48) :
    16 * s^2 + 48 * s * t - 48 * s + 40 * t^2 - 48 * t + 72 < 73 ∨ firstSeam (8, 4 * s) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 48 - 8 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 3/4 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 1/2 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 3/4
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (3/4) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (327680/3) * (s - (0))^0 * ((3/4) - s)^4 + (5095424/9) * (s - (0))^1 * ((3/4) - s)^3 + (6956032/9) * (s - (0))^2 * ((3/4) - s)^2 + (2852864/9) * (s - (0))^3 * ((3/4) - s)^1 := by positivity
  have hid : ((73) - (16 * s^2 + 48 * s * t - 48 * s + 40 * t^2 - 48 * t + 72)) * (48 - 8 * s)^2 = (327680/3) * (s - (0))^0 * ((3/4) - s)^4 + (5095424/9) * (s - (0))^1 * ((3/4) - s)^3 + (6956032/9) * (s - (0))^2 * ((3/4) - s)^2 + (2852864/9) * (s - (0))^3 * ((3/4) - s)^1 := by
    linear_combination (384 * s^2 + 320 * s * t - 3648 * s - 1920 * t + 1344) * h
  left
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (48 - 8 * s))
  linarith only [hid, hpos, hn]

private theorem b23 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -40 * s * t + 40 * t = 48) :
    40 * s^2 - 80 * s + 40 * t^2 + 40 < 73 ∨ firstSeam (8 - 6 * s, 2 * s + 4) (2 - 2 * t, 6 - 6 * t) := by
  have hb : 0 ≤ 40 - 40 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  nlinarith
private theorem c01 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -8 * s * t + 8 * t = 24) :
    73 * s^2 - 6 * s * t - 146 * s + t^2 + 6 * t + 73 ≤ 272/5 := by
  have hb : 0 ≤ 8 - 8 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  nlinarith
private theorem c02 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -34 * s * t - 8 * s + 40 * t + 8 = 24) :
    73 * s^2 + 84 * s * t - 152 * s + 40 * t^2 - 80 * t + 80 ≤ 272/5 := by
  have hb : 0 ≤ 40 - 34 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 4/7 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 2/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 4/7
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (4/7) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (1237544) * (s - (0))^1 * ((4/7) - s)^3 + (9906428/5) * (s - (0))^2 * ((4/7) - s)^2 + (4724496/5) * (s - (0))^3 * ((4/7) - s)^1 + (583848/5) * (s - (0))^4 * ((4/7) - s)^0 := by positivity
  have hid : ((272/5) - (73 * s^2 + 84 * s * t - 152 * s + 40 * t^2 - 80 * t + 80)) * (40 - 34 * s)^2 = (1237544) * (s - (0))^1 * ((4/7) - s)^3 + (9906428/5) * (s - (0))^2 * ((4/7) - s)^2 + (4724496/5) * (s - (0))^3 * ((4/7) - s)^1 + (583848/5) * (s - (0))^4 * ((4/7) - s)^0 := by
    linear_combination (2856 * s^2 + 1360 * s * t - 6400 * s - 1600 * t + 2560) * h
  apply le_of_lt
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (40 - 34 * s))
  linarith only [hid, hpos, hn]

private theorem c03 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : 42 * s * t - 42 * s + 48 = 24) :
    73 * s^2 + 68 * s * t - 68 * s + 40 * t^2 - 80 * t + 40 ≤ 272/5 := by
  have hb : 0 ≤ 42 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 4/7 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 4/7
  · subst s
    have hT : t = 0 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1
  · subst s
    have hT : t = 3/7 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (4/7) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (22604288/45) * (s - (4/7))^0 * ((1) - s)^4 + (142951424/45) * (s - (4/7))^1 * ((1) - s)^3 + (90573952/15) * (s - (4/7))^2 * ((1) - s)^2 + (174101312/45) * (s - (4/7))^3 * ((1) - s)^1 + (16931852/45) * (s - (4/7))^4 * ((1) - s)^0 := by positivity
  have hid : ((272/5) - (73 * s^2 + 68 * s * t - 68 * s + 40 * t^2 - 80 * t + 40)) * (42 * s)^2 = (22604288/45) * (s - (4/7))^0 * ((1) - s)^4 + (142951424/45) * (s - (4/7))^1 * ((1) - s)^3 + (90573952/15) * (s - (4/7))^2 * ((1) - s)^2 + (174101312/45) * (s - (4/7))^3 * ((1) - s)^1 + (16931852/45) * (s - (4/7))^4 * ((1) - s)^0 := by
    linear_combination (-2856 * s^2 - 1680 * s * t + 1680 * s + 960) * h
  apply le_of_lt
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (42 * s))
  linarith only [hid, hpos, hn]

private theorem c12 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -6 * s * t + 6 * t = 24) :
    s^2 - 4 * s * t - 2 * s + 40 * t^2 + 4 * t + 1 ≤ 272/5 := by
  have hb : 0 ≤ 6 - 6 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  nlinarith
private theorem c13 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -2 * s * t - 6 * s + 42 * t + 6 = 24) :
    s^2 + 12 * s * t - 6 * s + 40 * t^2 - 12 * t + 45 ≤ 272/5 := by
  have hb : 0 ≤ 42 - 2 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 1 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 3/7 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 1
  · subst s
    have hT : t = 3/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (1) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (63468/5) * (s - (0))^0 * ((1) - s)^4 + (223296/5) * (s - (0))^1 * ((1) - s)^3 + (254528/5) * (s - (0))^2 * ((1) - s)^2 + (18944) * (s - (0))^3 * ((1) - s)^1 := by positivity
  have hid : ((272/5) - (s^2 + 12 * s * t - 6 * s + 40 * t^2 - 12 * t + 45)) * (42 - 2 * s)^2 = (63468/5) * (s - (0))^0 * ((1) - s)^4 + (223296/5) * (s - (0))^1 * ((1) - s)^3 + (254528/5) * (s - (0))^2 * ((1) - s)^2 + (18944) * (s - (0))^3 * ((1) - s)^1 := by
    linear_combination (24 * s^2 + 80 * s * t - 768 * s - 1680 * t - 216) * h
  apply le_of_lt
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (42 - 2 * s))
  linarith only [hid, hpos, hn]

private theorem c23 (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -40 * s * t + 40 * t = 24) :
    40 * s^2 - 80 * s + 40 * t^2 + 40 ≤ 272/5 := by
  have hb : 0 ≤ 40 - 40 * s := by linarith
  have hl := mul_nonneg ht hb
  have hu := mul_nonneg (sub_nonneg.mpr ht') hb
  have hlo : 0 ≤ s := by nlinarith
  have hhi : s ≤ 2/5 := by nlinarith
  by_cases hEnd0 : s = 0
  · subst s
    have hT : t = 3/5 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  by_cases hEnd1 : s = 2/5
  · subst s
    have hT : t = 1 := by linarith only [h]
    subst t
    norm_num [firstSeam]
  have hL : 0 < s - (0) := sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hEnd0))
  have hR : 0 < (2/5) - s := sub_pos.mpr (lt_of_le_of_ne hhi hEnd1)
  have hpos : 0 < (1280000) * (s - (0))^1 * ((2/5) - s)^3 + (1984000) * (s - (0))^2 * ((2/5) - s)^2 + (768000) * (s - (0))^3 * ((2/5) - s)^1 := by positivity
  have hid : ((272/5) - (40 * s^2 - 80 * s + 40 * t^2 + 40)) * (40 - 40 * s)^2 = (1280000) * (s - (0))^1 * ((2/5) - s)^3 + (1984000) * (s - (0))^2 * ((2/5) - s)^2 + (768000) * (s - (0))^3 * ((2/5) - s)^1 := by
    linear_combination (1600 * s * t - 1600 * t - 960) * h
  apply le_of_lt
  by_contra! hbad
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbad) (sq_nonneg (40 - 40 * s))
  linarith only [hid, hpos, hn]

theorem first_cut (i j : Fin 4) (s t : ℝ)
    (hij : i < j) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (ha : cutArea2 quad i j s t = 24 ∨ cutArea2 quad i j s t = 48) :
    lengthSq (pointOn quad i s) (pointOn quad j t) < 73 ∨ firstSeam (pointOn quad i s) (pointOn quad j t) := by
  fin_cases i <;> fin_cases j <;> first | (exfalso; exact (of_decide_eq_false rfl) hij) | skip
  · rcases ha with ha | ha
    · have h0 : -32 * s * t + 32 * t = 24 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0)] (sidePoint (8,0) (8,4) t) + cross (sidePoint (8,0) (8,4) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a01 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (8,0) (8,4) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (8,0) (8,4) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : -32 * s * t + 32 * t = 48 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0)] (sidePoint (8,0) (8,4) t) + cross (sidePoint (8,0) (8,4) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b01 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (8,0) (8,4) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (8,0) (8,4) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
  · rcases ha with ha | ha
    · have h0 : -16 * s * t - 32 * s + 40 * t + 32 = 24 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0), (8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a02 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (8,4) (2,6) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (8,4) (2,6) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : -16 * s * t - 32 * s + 40 * t + 32 = 48 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0), (8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b02 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (8,4) (2,6) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (8,4) (2,6) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
  · rcases ha with ha | ha
    · have h0 : 48 * s * t - 48 * s + 72 = 24 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0), (8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a03 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : 48 * s * t - 48 * s + 72 = 48 := by
        change shoelace (sidePoint (0,0) (8,0) s) [(8,0), (8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (0,0) (8,0) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b03 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (0,0) (8,0) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (0,0) (8,0) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
  · rcases ha with ha | ha
    · have h0 : -24 * s * t + 24 * t = 24 := by
        change shoelace (sidePoint (8,0) (8,4) s) [(8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (8,0) (8,4) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a12 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,0) (8,4) s) (sidePoint (8,4) (2,6) t) < 73 ∨ firstSeam (sidePoint (8,0) (8,4) s) (sidePoint (8,4) (2,6) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : -24 * s * t + 24 * t = 48 := by
        change shoelace (sidePoint (8,0) (8,4) s) [(8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (8,0) (8,4) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b12 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,0) (8,4) s) (sidePoint (8,4) (2,6) t) < 73 ∨ firstSeam (sidePoint (8,0) (8,4) s) (sidePoint (8,4) (2,6) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
  · rcases ha with ha | ha
    · have h0 : -8 * s * t - 24 * s + 48 * t + 24 = 24 := by
        change shoelace (sidePoint (8,0) (8,4) s) [(8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,0) (8,4) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a13 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,0) (8,4) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (8,0) (8,4) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : -8 * s * t - 24 * s + 48 * t + 24 = 48 := by
        change shoelace (sidePoint (8,0) (8,4) s) [(8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,0) (8,4) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b13 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,0) (8,4) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (8,0) (8,4) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
  · rcases ha with ha | ha
    · have h0 : -40 * s * t + 40 * t = 24 := by
        change shoelace (sidePoint (8,4) (2,6) s) [(2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,4) (2,6) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := a23 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,4) (2,6) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (8,4) (2,6) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
    · have h0 : -40 * s * t + 40 * t = 48 := by
        change shoelace (sidePoint (8,4) (2,6) s) [(2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,4) (2,6) s) = _ at ha
        dsimp [shoelace, sidePoint, cross] at ha
        linarith only [ha]
      have hh := b23 s t hs hs' ht ht' h0
      change lengthSq (sidePoint (8,4) (2,6) s) (sidePoint (2,6) (0,0) t) < 73 ∨ firstSeam (sidePoint (8,4) (2,6) s) (sidePoint (2,6) (0,0) t)
      dsimp [lengthSq, sidePoint]
      ring_nf at hh ⊢
      exact hh
theorem second_cut (i j : Fin 4) (s t : ℝ)
    (hij : i < j) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (ha : cutArea2 rest i j s t = 24) :
    lengthSq (pointOn rest i s) (pointOn rest j t) ≤ 272/5 := by
  fin_cases i <;> fin_cases j <;> first | (exfalso; exact (of_decide_eq_false rfl) hij) | skip
  ·
    have h0 : -8 * s * t + 8 * t = 24 := by
      change shoelace (sidePoint (0,0) (8,3) s) [(8,3)] (sidePoint (8,3) (8,4) t) + cross (sidePoint (8,3) (8,4) t) (sidePoint (0,0) (8,3) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c01 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (0,0) (8,3) s) (sidePoint (8,3) (8,4) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
  ·
    have h0 : -34 * s * t - 8 * s + 40 * t + 8 = 24 := by
      change shoelace (sidePoint (0,0) (8,3) s) [(8,3), (8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (0,0) (8,3) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c02 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (0,0) (8,3) s) (sidePoint (8,4) (2,6) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
  ·
    have h0 : 42 * s * t - 42 * s + 48 = 24 := by
      change shoelace (sidePoint (0,0) (8,3) s) [(8,3), (8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (0,0) (8,3) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c03 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (0,0) (8,3) s) (sidePoint (2,6) (0,0) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
  ·
    have h0 : -6 * s * t + 6 * t = 24 := by
      change shoelace (sidePoint (8,3) (8,4) s) [(8,4)] (sidePoint (8,4) (2,6) t) + cross (sidePoint (8,4) (2,6) t) (sidePoint (8,3) (8,4) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c12 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (8,3) (8,4) s) (sidePoint (8,4) (2,6) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
  ·
    have h0 : -2 * s * t - 6 * s + 42 * t + 6 = 24 := by
      change shoelace (sidePoint (8,3) (8,4) s) [(8,4), (2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,3) (8,4) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c13 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (8,3) (8,4) s) (sidePoint (2,6) (0,0) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
  ·
    have h0 : -40 * s * t + 40 * t = 24 := by
      change shoelace (sidePoint (8,4) (2,6) s) [(2,6)] (sidePoint (2,6) (0,0) t) + cross (sidePoint (2,6) (0,0) t) (sidePoint (8,4) (2,6) s) = _ at ha
      dsimp [shoelace, sidePoint, cross] at ha
      linarith only [ha]
    have hh := c23 s t hs hs' ht ht' h0
    change lengthSq (sidePoint (8,4) (2,6) s) (sidePoint (2,6) (0,0) t) ≤ 272/5
    dsimp [lengthSq, sidePoint]
    ring_nf at hh ⊢
    exact hh
/-- All legal one-third cuts. The chord's endpoints can be put in increasing
edge order, and either complementary region may be the piece of area 12. -/
def FirstCut (i j : Fin 4) (s t : ℝ) : Prop :=
  i < j ∧ s ∈ Set.Icc 0 1 ∧ t ∈ Set.Icc 0 1 ∧
    (cutArea2 quad i j s t = 24 ∨ cutArea2 quad i j s t = 48)

def FirstCutIsLongest (i j : Fin 4) (s t : ℝ) : Prop :=
  FirstCut i j s t ∧ ∀ (k l : Fin 4) (u v : ℝ), FirstCut k l u v →
    lengthSq (pointOn quad k u) (pointOn quad l v) ≤
      lengthSq (pointOn quad i s) (pointOn quad j t)

private theorem witnessArea : cutArea2 quad 0 1 0 (3/4) = 24 := by
  change shoelace (sidePoint (0,0) (8,0) 0) [(8,0)] (sidePoint (8,0) (8,4) (3/4)) +
    cross (sidePoint (8,0) (8,4) (3/4)) (sidePoint (0,0) (8,0) 0) = 24
  norm_num [shoelace, sidePoint, cross]
private theorem witnessLength :
    lengthSq (pointOn quad 0 0) (pointOn quad 1 (3/4)) = 73 := by
  change lengthSq (sidePoint (0,0) (8,0) 0) (sidePoint (8,0) (8,4) (3/4)) = 73
  norm_num [sidePoint,lengthSq]

private theorem witnessLegal : FirstCut 0 1 0 (3/4) :=
  ⟨by decide, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, Or.inl witnessArea⟩

private theorem seamLength {p q : Point} (h : firstSeam p q) : lengthSq p q = 73 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num [lengthSq]

theorem witnessIsLongest : FirstCutIsLongest 0 1 0 (3/4) := by
  refine ⟨witnessLegal, ?_⟩
  intro i j s t ⟨hij, hs, ht, ha⟩
  rw [witnessLength]
  rcases first_cut i j s t hij hs.1 hs.2 ht.1 ht.2 ha with h | h
  · exact h.le
  · exact (seamLength h).le

/-- The greedy remainder has a legal bisector attaining the second-cut bound. -/
theorem secondWitness :
    cutArea2 rest 0 2 0 (2/5) = 24 ∧
      lengthSq (pointOn rest 0 0) (pointOn rest 2 (2/5)) = 272/5 := by
  change shoelace (sidePoint (0,0) (8,3) 0) [(8,3),(8,4)] (sidePoint (8,4) (2,6) (2/5)) +
      cross (sidePoint (8,4) (2,6) (2/5)) (sidePoint (0,0) (8,3) 0) = 24 ∧
    lengthSq (sidePoint (0,0) (8,3) 0) (sidePoint (8,4) (2,6) (2/5)) = 272/5
  norm_num [shoelace, sidePoint, cross, lengthSq]

/-- The three triangles of the competing partition have area 12 each.
Their shared cuts are BD and BM, with M the midpoint of AD. -/
def triArea2 (p q r : Point) : ℝ := cross p q + cross q r + cross r p

theorem competingTriangles :
    triArea2 (8,0) (8,4) (2,6) = 24 ∧
    triArea2 (8,0) (2,6) (1,3) = 24 ∧ triArea2 (8,0) (1,3) (0,0) = 24 ∧
    lengthSq (8,0) (2,6) = 72 ∧ lengthSq (8,0) (1,3) = 58 := by
  norm_num [triArea2, cross, lengthSq]

/-- Every maximizing first cut gives exactly AE (in either order). Every
area bisector of the resulting quadrilateral AECD then gives a shorter
combined cut than BD and BM. -/
theorem greedy_fails {i j k l : Fin 4} {s t u v : ℝ}
    (hfirst : FirstCutIsLongest i j s t)
    (hkl : k < l) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (harea : cutArea2 rest k l u v = 24) :
    firstSeam (pointOn quad i s) (pointOn quad j t) ∧
      Real.sqrt (lengthSq (pointOn quad i s) (pointOn quad j t)) +
        Real.sqrt (lengthSq (pointOn rest k u) (pointOn rest l v)) <
      Real.sqrt (lengthSq (8,0) (2,6)) + Real.sqrt (lengthSq (8,0) (1,3)) := by
  obtain ⟨⟨hij, hs, ht, ha⟩, hmax⟩ := hfirst
  have hmin := hmax 0 1 0 (3/4) witnessLegal
  rw [witnessLength] at hmin
  have seam := (first_cut i j s t hij hs.1 hs.2 ht.1 ht.2 ha).resolve_left (not_lt.mpr hmin)
  refine ⟨seam, ?_⟩
  rw [seamLength seam, competingTriangles.2.2.2.1, competingTriangles.2.2.2.2]
  have h2 := second_cut k l u v hkl hu.1 hu.2 hv.1 hv.2 harea
  have hA : Real.sqrt 73 < 86/10 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hB : Real.sqrt (lengthSq (pointOn rest k u) (pointOn rest l v)) < 74/10 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  have hC : 84/10 < Real.sqrt 72 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hD : 76/10 < Real.sqrt 58 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

#print axioms GreedyEquipartition.witnessIsLongest
#print axioms GreedyEquipartition.secondWitness
#print axioms GreedyEquipartition.greedy_fails

end GreedyEquipartition
