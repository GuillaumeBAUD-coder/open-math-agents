import FormalConjectures.ErdosProblems.«214»

/-!
Csizmadia and Tóth, Note on a Ramsey-type problem in geometry (1994), use a regular
heptagon and its center. Here the seven outer points have dyadic coordinates.
The blue set consists of open disks of radius one half around a lattice. Separation
of the centers rules out a blue unit pair. An interval certificate shows that every
congruent copy of the eight points meets a blue disk.

The eight-point certificate and its congruence argument are from PanPapag's
bounds proof in PR 1792. The lattice estimates and common-sign lemma are from
mucoucah's twelve-point proof in PR 1053.
-/

open scoped EuclideanGeometry Congruent

namespace OMA214

lemma sign_lemma {ι : Type*} (C C' : ι → ℝ) (hC : ∀ i j, C i * C j = C' i * C' j) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ i, C i = σ * C' i := by
  by_cases h : ∀ i, C' i = 0
  · refine ⟨1, by norm_num, fun i => ?_⟩
    have := hC i i
    rw [h i] at this ⊢
    have h2 : C i ^ 2 = 0 := by nlinarith
    simpa using h2
  · simp only [not_forall] at h
    obtain ⟨r, hr⟩ := h
    have hrr := hC r r
    refine ⟨C r / C' r, ?_, fun i => ?_⟩
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hr)]
      linear_combination hrr
    · have hir := hC i r
      have hz : C' r * (C i * C' r - C r * C' i) = 0 := by
        linear_combination (-C i) * hrr + C r * hir
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact absurd h0 hr
      · rw [div_mul_eq_mul_div, eq_div_iff hr]
        linear_combination h0

lemma core (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (_hv1 : v ≤ 1)
    (h : 2 * u + 49 / 8 * v ≤ 65 / 16) : u ^ 2 + 49 / 16 * v ^ 2 ≤ 27 / 20 := by
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1), mul_nonneg hv0 (sub_nonneg.2 h),
    mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h), mul_nonneg hu0 hv0,
    mul_nonneg (sub_nonneg.2 hu1) hv0]

lemma core2 (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    u ^ 2 + 49 / 16 * v ^ 2 ≤ 27 / 20 ∨ (1 - u) ^ 2 + 49 / 16 * (1 - v) ^ 2 ≤ 27 / 20 := by
  rcases le_total (2 * u + 49 / 8 * v) (65 / 16) with h | h
  · exact Or.inl (core u v hu0 hu1 hv0 hv1 h)
  · right
    exact core (1 - u) (1 - v) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

lemma lattice_cover (qx qy : ℝ) :
    ∃ a b : ℤ, (qx - (2 * (a : ℝ) + b)) ^ 2 + (qy - 7 / 4 * (b : ℝ)) ^ 2 ≤ 27 / 20 := by
  set b0 : ℤ := ⌊4 * qy / 7⌋ with hb0
  have hv0 : (b0 : ℝ) ≤ 4 * qy / 7 := Int.floor_le _
  have hv1 : 4 * qy / 7 < b0 + 1 := Int.lt_floor_add_one _
  set a0 : ℤ := ⌊(qx - b0) / 2⌋ with ha0
  have hh0 : (a0 : ℝ) ≤ (qx - b0) / 2 := Int.floor_le _
  have hh1 : (qx - b0) / 2 < a0 + 1 := Int.lt_floor_add_one _
  set v : ℝ := 4 * qy / 7 - b0 with hv
  set h : ℝ := qx - b0 - 2 * a0 with hh
  have ey0 : qy - 7 / 4 * (b0 : ℝ) = 7 / 4 * v := by rw [hv]; ring
  have ey1 : qy - 7 / 4 * ((b0 + 1 : ℤ) : ℝ) = -(7 / 4 * (1 - v)) := by rw [hv]; push_cast; ring
  rcases le_total h 1 with hle | hle
  · rcases core2 h v (by linarith) hle (by linarith) (by linarith) with hc | hc
    · refine ⟨a0, b0, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + b0) = h := by rw [hh]; ring
      rw [ex, ey0]
      nlinarith [hc]
    · refine ⟨a0, b0 + 1, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + ((b0 + 1 : ℤ) : ℝ)) = -(1 - h) := by rw [hh]; push_cast; ring
      rw [ex, ey1]
      nlinarith [hc]
  · rcases core2 (2 - h) v (by linarith) (by linarith) (by linarith) (by linarith) with hc | hc
    · refine ⟨a0 + 1, b0, ?_⟩
      have ex : qx - (2 * ((a0 + 1 : ℤ) : ℝ) + b0) = -(2 - h) := by rw [hh]; push_cast; ring
      rw [ex, ey0]
      nlinarith [hc]
    · refine ⟨a0, b0 + 1, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + ((b0 + 1 : ℤ) : ℝ)) = (1 - (2 - h)) := by
        rw [hh]; push_cast; ring
      rw [ex, ey1]
      nlinarith [hc]

lemma lattice_sep_int (da db : ℤ) (h : da ≠ 0 ∨ db ≠ 0) :
    64 ≤ 16 * (2 * da + db) ^ 2 + 49 * db ^ 2 := by
  have hc : db = 0 ∨ db = 1 ∨ db = -1 ∨ 2 ≤ db ∨ db ≤ -2 := by omega
  rcases hc with hc | hc | hc | hc | hc
  · subst hc
    have : da ≤ -1 ∨ 1 ≤ da := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + 1 ≤ -1 ∨ 1 ≤ 2 * da + 1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + -1 ≤ -1 ∨ 1 ≤ 2 * da + -1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · nlinarith [sq_nonneg (2 * da + db)]
  · nlinarith [sq_nonneg (2 * da + db)]

noncomputable def L (a b : ℤ) : ℝ² := !₂[2 * (a : ℝ) + b, 7 / 4 * (b : ℝ)]

def S : Set ℝ² := {x | ∃ a b : ℤ, dist x (L a b) < 1 / 2}

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

lemma L_sep (a b a' b' : ℤ) (h : (a, b) ≠ (a', b')) : 2 ≤ dist (L a b) (L a' b') := by
  have h1 : a - a' ≠ 0 ∨ b - b' ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    apply h
    have e1 : a = a' := by omega
    have e2 : b = b' := by omega
    rw [e1, e2]
  have h2 := lattice_sep_int (a - a') (b - b') h1
  have h2' : (64 : ℝ) ≤ 16 * (2 * ((a : ℝ) - a') + ((b : ℝ) - b')) ^ 2 + 49 * ((b : ℝ) - b') ^ 2 := by
    exact_mod_cast h2
  have h3 : dist (L a b) (L a' b') ^ 2
      = (2 * (a : ℝ) + b - (2 * a' + b')) ^ 2 + (7 / 4 * (b : ℝ) - 7 / 4 * b') ^ 2 := by
    rw [dist_sq]
    simp [L]
  have h4 : (4 : ℝ) ≤ dist (L a b) (L a' b') ^ 2 := by
    rw [h3]
    nlinarith
  nlinarith [dist_nonneg (x := L a b) (y := L a' b')]

lemma S_avoid : Erdos214.UnitDistanceAvoiding S := by
  intro x hx y hy hxy
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨a', b', hab'⟩ := hy
  by_cases he : (a, b) = (a', b')
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := dist_triangle_right x y (L a b)
    linarith
  · have h2 := L_sep a b a' b' he
    have t1 := dist_triangle (L a b) x (L a' b')
    have t2 := dist_triangle x y (L a' b')
    rw [dist_comm] at hab
    linarith


end OMA214
namespace Eight
def X : Fin 8 → ℤ := ![0,840,524,-187,-757,-757,-187,524]
def Y : Fin 8 → ℤ := ![0,0,656,819,364,-364,-819,-656]
def U : Fin 7 → ℤ := ![0,8,-8,4,-4,4,-4]
def V : Fin 7 → ℤ := ![0,0,0,7,7,-7,-7]

-- All coordinates and both components of the unit direction are scaled by 1024.
def Covered (x y c s : ℝ) : Prop :=
  ∃ (i : Fin 8) (j : Fin 7),
    (4*x + U j*c - V j*s - 4*X i)^2 + (4*y + V j*c + U j*s - 4*Y i)^2 < 2048^2

structure Seg where
  lo : ℤ
  hi : ℤ

def Seg.Has (a : Seg) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ a.hi
def Seg.plus (a b : Seg) : Seg := ⟨a.lo+b.lo,a.hi+b.hi⟩
def Seg.scale (a : Seg) (k : ℤ) : Seg :=
  if 0 ≤ k then ⟨k*a.lo,k*a.hi⟩ else ⟨k*a.hi,k*a.lo⟩
def Seg.low (a : Seg) : ℤ := (max 0 (max a.lo (-a.hi)))^2
def Seg.high (a : Seg) : ℤ := (max (-a.lo) a.hi)^2

lemma Seg.add_mem {a b : Seg} {x y : ℝ} (hx : a.Has x) (hy : b.Has y) :
    (a.plus b).Has (x+y) := by
  obtain ⟨hl,hr⟩ := hx
  obtain ⟨hl',hr'⟩ := hy
  simpa [Has,plus] using And.intro (add_le_add hl hl') (add_le_add hr hr')

lemma Seg.scale_mem {a : Seg} {x : ℝ} (hx : a.Has x) (k : ℤ) :
    (a.scale k).Has (k*x) := by
  obtain ⟨hl,hr⟩ := hx
  by_cases h : 0 ≤ k
  · have hk : (0:ℝ) ≤ k := by exact_mod_cast h
    simpa [Has,scale,h] using And.intro (mul_le_mul_of_nonneg_left hl hk)
      (mul_le_mul_of_nonneg_left hr hk)
  · have hk : (k:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    simpa [Has,scale,h] using And.intro (mul_le_mul_of_nonpos_left hr hk)
      (mul_le_mul_of_nonpos_left hl hk)

lemma Seg.low_le {a : Seg} {x : ℝ} (hx : a.Has x) : (a.low : ℝ) ≤ x^2 := by
  obtain ⟨hl,hr⟩ := hx
  have h : max 0 (max (a.lo:ℝ) (-a.hi)) ≤ |x| :=
    max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _))
      ((neg_le_neg hr).trans (neg_le_abs _)))
  simpa [low, sq_abs] using sq_le_sq' ((neg_nonpos.mpr (abs_nonneg x)).trans (le_max_left ..)) h

lemma Seg.le_high {a : Seg} {x : ℝ} (hx : a.Has x) : x^2 ≤ (a.high : ℝ) := by
  obtain ⟨hl,hr⟩ := hx
  have hr' : x ≤ max (-(a.lo:ℝ)) a.hi := hr.trans (le_max_right ..)
  have hl' : -x ≤ max (-(a.lo:ℝ)) a.hi := (neg_le_neg hl).trans (le_max_left ..)
  simpa [high] using sq_le_sq' (by linarith : -max (-(a.lo:ℝ)) a.hi ≤ x) hr'

def displacement (a c s : Seg) (u v k : ℤ) : Seg :=
  (((a.scale 4).plus (c.scale u)).plus (s.scale v)).plus ⟨-4*k,-4*k⟩

lemma disp_mem {a c s : Seg} {x f g : ℝ} (hx : a.Has x) (hf : c.Has f) (hg : s.Has g)
    (u v k : ℤ) : (displacement a c s u v k).Has (4*x + u*f + v*g - 4*k) := by
  have hk : (Seg.mk (-4*k) (-4*k)).Has (-4*(k:ℝ)) := by simp [Seg.Has]
  have h := Seg.add_mem (Seg.add_mem (Seg.add_mem (Seg.scale_mem hx 4) (Seg.scale_mem hf u)) (Seg.scale_mem hg v)) hk
  simpa [displacement, sub_eq_add_neg] using h

structure Box where
  x : Seg
  y : Seg
  c : Seg
  s : Seg

def Box.Closed (b : Box) : Prop :=
  ∀ x y c s : ℝ, b.x.Has x → b.y.Has y → b.c.Has c → b.s.Has s →
    20*(x^2+y^2) ≤ 27*1024^2 → c^2+s^2 = 1024^2 → Covered x y c s

def outside (b : Box) : Bool := decide
  (27*1024^2 < 20*(b.x.low+b.y.low) ∨ 1024^2 < b.c.low+b.s.low ∨ b.c.high+b.s.high < 1024^2)

lemma outside_sound {b : Box} (h : outside b = true) : b.Closed := by
  intro x y c s hx hy hc hs hz hu
  unfold outside at h
  rcases of_decide_eq_true h with h|h|h
  · have h' : (27:ℝ)*1024^2 < 20*((b.x.low:ℝ)+b.y.low) := by exact_mod_cast h
    linarith [Seg.low_le hx,Seg.low_le hy]
  · have h' : (1024:ℝ)^2 < (b.c.low:ℝ)+b.s.low := by exact_mod_cast h
    linarith [Seg.low_le hc,Seg.low_le hs]
  · have h' : (b.c.high:ℝ)+b.s.high < 1024^2 := by exact_mod_cast h
    linarith [Seg.le_high hc,Seg.le_high hs]

def hit (b : Box) (i : Fin 8) (j : Fin 7) : Bool := decide
  ((displacement b.x b.c b.s (U j) (-V j) (X i)).high +
   (displacement b.y b.c b.s (V j) (U j) (Y i)).high < 2048^2)

lemma hit_sound {b : Box} {i : Fin 8} {j : Fin 7} (h : hit b i j = true) : b.Closed := by
  intro x y c s hx hy hc hs _ _
  refine ⟨i,j,?_⟩
  have ex := Seg.le_high (disp_mem hx hc hs (U j) (-V j) (X i))
  have ey := Seg.le_high (disp_mem hy hc hs (V j) (U j) (Y i))
  unfold hit at h
  have hz : ((displacement b.x b.c b.s (U j) (-V j) (X i)).high:ℝ) +
      (displacement b.y b.c b.s (V j) (U j) (Y i)).high < 2048^2 := by
    exact_mod_cast of_decide_eq_true h
  push_cast at ex
  calc
    _ = (4*x+(U j:ℝ)*c+ -(V j:ℝ)*s-4*(X i:ℝ))^2 +
        (4*y+(V j:ℝ)*c+(U j:ℝ)*s-4*(Y i:ℝ))^2 := by ring
    _ < _ := (add_le_add ex ey).trans_lt hz

def half (a : Seg) (right : Bool) : Seg :=
  let m := (a.lo+a.hi)/2
  if right then ⟨m,a.hi⟩ else ⟨a.lo,m⟩

lemma half_cases {a : Seg} {x : ℝ} (hx : a.Has x) : (half a false).Has x ∨ (half a true).Has x := by
  rcases le_total x (((a.lo+a.hi)/2 : ℤ):ℝ) with h|h
  · exact Or.inl ⟨hx.1,h⟩
  · exact Or.inr ⟨h,hx.2⟩

inductive Coord | x | y | c | s
def cut (b : Box) (d : Coord) (right : Bool) : Box := match d with
  | .x => {b with x := half b.x right}
  | .y => {b with y := half b.y right}
  | .c => {b with c := half b.c right}
  | .s => {b with s := half b.s right}

lemma cut_sound (b : Box) (d : Coord) (hl : (cut b d false).Closed)
    (hr : (cut b d true).Closed) : b.Closed := by
  intro x y c s hx hy hc hs hz hu
  cases d
  · rcases half_cases hx with h|h
    · exact hl _ _ _ _ h hy hc hs hz hu
    · exact hr _ _ _ _ h hy hc hs hz hu
  · rcases half_cases hy with h|h
    · exact hl _ _ _ _ hx h hc hs hz hu
    · exact hr _ _ _ _ hx h hc hs hz hu
  · rcases half_cases hc with h|h
    · exact hl _ _ _ _ hx hy h hs hz hu
    · exact hr _ _ _ _ hx hy h hs hz hu
  · rcases half_cases hs with h|h
    · exact hl _ _ _ _ hx hy hc h hz hu
    · exact hr _ _ _ _ hx hy hc h hz hu

-- A base-64 preorder traversal. Zero discards an impossible box; tags 1 to 56
-- give a point and lattice neighbour; the remaining tags bisect a coordinate.
def axis (tag : ℕ) : Coord :=
  if tag = 57 then .x else if tag = 58 then .y else if tag = 59 then .c else .s

def verify : ℕ → Box → ℕ → Option ℕ
  | 0, _, _ => none
  | n+1, b, code =>
    let tag := code % 64
    let tail := code / 64
    if tag = 0 then if outside b then some tail else none
    else if tag ≤ 56 then
      if hit b (Fin.ofNat 8 (tag-1)) (Fin.ofNat 7 ((tag-1)/8)) then some tail else none
    else do
      let rest ← verify n (cut b (axis tag) false) tail
      verify n (cut b (axis tag) true) rest

lemma verify_sound {n code rest : ℕ} {b : Box} (h : verify n b code = some rest) : b.Closed := by
  induction n generalizing b code rest with
  | zero => simp [verify] at h
  | succ n ih =>
    simp only [verify] at h
    split at h
    · split at h
      · exact outside_sound (by assumption)
      · contradiction
    · split at h
      · split at h
        · exact hit_sound (by assumption)
        · contradiction
      · cases he : verify n (cut b (axis (code%64)) false) (code/64) with
        | none => simp [he] at h
        | some q =>
          apply cut_sound b (axis (code%64)) (ih he)
          exact ih (by simpa [he] using h)

private theorem cell1 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell2 : Box.Closed ⟨⟨(-2048),(-1536)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell3 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x603a03903a039) (rest:=0) (by decide +kernel)

private theorem cell4 : Box.Closed ⟨⟨(-1536),(-1280)⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell5 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6180e40eb9) (rest:=0) (by decide +kernel)

private theorem cell6 : Box.Closed ⟨⟨(-1280),(-1216)⟩,⟨(-256),(-128)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell7 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-256),(-192)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell8 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-192),(-128)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2be3b03ce3b03ce38038f3be3cec0f00cbc032f3b032efcec0f3b03c032f00c80efcec0c80f32033f3bcfcec0f3bf00033f00ef3f00efcec0cc0f3363c03b63cec06004bbf3bf3bf3b0008c08c08fcefcefc0008bc8bbf3bf00012ed3f3b000a3cee28a8180e7cee203bf3b03ca2803cec0f00ec0f3bf00a3c4fba00ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell9 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-192),(-128)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xc3bf3b2f003cefcefc000000c3cc3bf3bf0002aec6039c3cabbf2aefcef003c03bf3b2ca03bf00efcaaa03cec0f2b03cafb03cafb03cec0f3b280ed0f00ed00106fcefc01bf3bf00ec06c06c0f3bf3b03c01b6c0f1aefc01af3bf00ec06bb03c680f3bf3bf0001a03b680f1a03cefc020800f20efc83bf3bf00800823efcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell10 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-192),(-128)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell8 cell9

private theorem cell11 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-256),(-128)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell7 cell10

private theorem cell12 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨(-256),(-128)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell6 cell11

private theorem cell13 : Box.Closed ⟨⟨(-1280),(-1216)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell14 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-128),(-64)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2be3b03ce3b03ce00e3c0321bacb8eb9f3b032efcec0f00cbccbbcbcec0f3b03c032f00c80efcec0c80f32cfccfbcfcec0f3bf00033f00ef3f00efcec0018ec0f3303b63c03b63cec0612f3bf3bf3b0008c08fcefc00002203c8bbf22efc8bbf3bf00012012efced3f3b000a3cee28a2f3b03ca00f2803cec0f00ec0f3bf284e803bf3ba00f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell15 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-128),(-64)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3b030ecbf30efcefc000000c3c030f3bf3bf00aaaf2aefcef003c03bf3b2ca03b2bc03bf00efcaaaa80abcec0f3b03cec0f2b03cafb03cec0f3b290f00ed001001befcefc01003bf3bf00ec06c06c0f3bf3b03c01b6db6bcefc01af3bf00ec06bb03c680f3bf3bf0001a69a03cefc01a03b686e9a83ae40f2003cefc83bf3bf00800823efcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell16 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-128),(-64)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell14 cell15

private theorem cell17 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-64),0⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3803ce3b03ce00f00cbccbbcbcec0f32cbbcbcec0f3b03c032f00032f00efcec0033ec0f33ec0f3bf00033f00ef3cf3f3bf00efcec061803b63cec00184bced2f3bf3bf3b000023f008fcefc000023880f3bf22efc8bbf3bf000120124fcefced34d303bf3bf3b000a28efcee203c8a803cec0f00ec0f3bf284e803bf3ba00f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell18 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-64),0⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3b030ecbf30efcefc000000c3cabbf3bf00abcef0c3b03c03bf3b00becbf0becb2bc03b2bc03bf00efcaaa02af2bec0f3b03cec0f2b03cac0f3b03cec0f3b28a43c03bf00ed0010efc43bf00ec06dbf1bec06c0f3bf3b03c01b01b03bf3bf00ec0680f3b03c680f3bf3bf0001a69aefc01a69a03cefc020f3bf3bf0080083cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell19 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-64),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell17 cell18

private theorem cell20 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell16 cell19

private theorem cell21 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell13 cell20

private theorem cell22 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨(-256),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell12 cell21

private theorem cell23 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨(-256),(-128)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell24 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-128),(-64)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell25 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x23023023f3bf3bf000008c0f2203cefc8a28bbf3bf228a2efcefcefc0004804934931ba4f9f3bf3bf3b4d34c0efcefcec0000028efca28a00f3bf3bf3b880f2203c880ec6ea203ba00efae40f3b03c03b03cefca134e81baa39f3ba00efcee803c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell26 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38e3b03ce00f3b03ce00e32ec6eb8e7cec0f00c86eb2cb2efae7c032f3bcbcec0f00cbccbbcbcec0f3b03c032f00032032f3bf00efcec003203cec0f3303b1bacf9cfc033f3bcfcec0f3bf00033f00ef3cc0ef3f3bf00efcec061803b63c03b63cec00186121ba639f3b4bced2f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell27 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell25 cell26

private theorem cell28 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xa28a1ba43943c43bf00efc03b40040043bf3bf10efc03b01b01befc6fb01b03cefcec0f006db03c6c06fb1ba6f9f3bf0001af00efcefc03b01a03c6bb03cec0f1a03cefcefc00069a680f3bf0069a03c686e9a69aefae40f3bf006a0ec6ea0e40f20efcefcefc00083c02083bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell29 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3b030ef01bac392fc2fbf30efcefc00000002aec6e80abb030efae7c02af3bf3bf00abcec0c3cc3bc3cc00ec0f3b03c03bf3b00becbf0becb1ba2f92bc2fb2bc03b2bc03bf00efcaaaeeaf2aabbabc02af00afcec0f3b03cec0f2b03cafb03cafb03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell30 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell28 cell29

private theorem cell31 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-64),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell27 cell30

private theorem cell32 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell24 cell31

private theorem cell33 : Box.Closed ⟨⟨(-1088),(-1024)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell34 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨(-128),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell32 cell33

private theorem cell35 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨(-256),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell23 cell34

private theorem cell36 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨(-256),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell22 cell35

private theorem cell37 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell5 cell36

private theorem cell38 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell4 cell37

private theorem cell39 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell3 cell38

private theorem cell40 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell2 cell39

private theorem cell41 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell1 cell40

private theorem cell42 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-2048),(-1536)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell43 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell44 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-1536),(-1280)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell45 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell46 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell47 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨(-1152),(-1088)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell48 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨(-1088),(-1024)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2aaaaec0f3b03c02af2bec0f2bec0f2bec0f3b03c02baecf3bf0002cf00efcec0b3bf00b00eecb2ccbbf3bf00efcec0cb2cbc03bcb203bc80efcefcec0033ef3f3bf3bf3b000014f14efc00053c4d303c4fbf3bf3bf00000cfbd3cec04bcd34480efc03bf3bf3b000013f124d203cefcefced34c0f3bf12480f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell49 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨(-1088),(-1024)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xaf3b2bcefc00bf0bec02bc2fb2bc2c0f3b03c03bf3b0002bb73cedcf0a03cedc6c0efc03bf00efc2c02fcecbf0c03cec0f0c300f3b03cec0f3b6db03bf00ec06bb01aefc6bb01a6bcefc6bbf00ec069aee4f24ec093bf3b03c900ec0900f3b03c923f23ec0f3bf3bf00023023023880f3bf3bf3bf000228bbf22efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell50 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨(-1088),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell48 cell49

private theorem cell51 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell47 cell50

private theorem cell52 : Box.Closed ⟨⟨(-576),(-512)⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x703a) (rest:=0) (by decide +kernel)

private theorem cell53 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell51 cell52

private theorem cell54 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell46 cell53

private theorem cell55 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell45 cell54

private theorem cell56 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell44 cell55

private theorem cell57 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell43 cell56

private theorem cell58 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell42 cell57

private theorem cell59 : Box.Closed ⟨⟨(-512),0⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x703a1c703ae40eb903a) (rest:=0) (by decide +kernel)

private theorem cell60 : Box.Closed ⟨⟨(-1024),0⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell58 cell59

private theorem cell61 : Box.Closed ⟨⟨(-1024),(-896)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x603a03903a) (rest:=0) (by decide +kernel)

private theorem cell62 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell63 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-1024),(-960)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell64 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-960),(-896)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2a03ca80f2bec0f3b03cac0f2b02b03cefcec0f3b03c02cb3bf0002cf00efcec0b00f3bf0002c03bf00ef2f00efcec0c80f3203bc80f3303bcfcefcec0cc0cfbf3bf3bf3b000022f00022f14efcefc014514500f3bf3bf3bf00034d3ced2012f34480efced2f3bf3b0004fced303c4c0f3bf124c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell65 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-960),(-896)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2fb2bcefc00bf002fcecb03c03bf3b2802bb73c280f3bf0aedc73c03bf00efc00cf0ceccf0cec0f0ca80f3b03ca80f3b03cec0f3b6c0edbf00edb01befc01af3b01aefc01af3bf00ec0680024ec0f3bf3b03c024f00ec0900f3b03c924ec0f3bf3bf000008fc03b8fc023f3bf00023022f3bf008bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell66 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-960),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell64 cell65

private theorem cell67 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell63 cell66

private theorem cell68 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell62 cell67

private theorem cell69 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2a03cac0f2bec0f3b03cac0f2b02b02bf3bf3b02cefcec0f3b03c02cb3bf0002cf00efcec0b2c02cf3bcbcec0f3bf00032f00ef2f00efcec0c80f3203bcfcec0cc0cf4f3bf3bf3bf3b000022f00880894efcefcefc014514500f3bf3bf3bf00034d3ced249203b4bced2f3bf3b0004fced303c4c0f3bf124c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell70 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2fb2bcefc00bf002fcecb03c03bf3b28a00aefc2bbf0aedc73c03bf00efc00cf0ceccf0cec0f0cabb03cabb03ca80f3b03cec0f3b71bf00edbf00edb01aefc01af3bf00ec0680680f3bf3b03c01a900f24efc93bf00ec0900f3b03c924ec0f3bf3bf0002403b8c0f23ec0f23efc023f3bf00023023f3bf008bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell71 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-896),(-832)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell69 cell70

private theorem cell72 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-832),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell73 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell71 cell72

private theorem cell74 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2a03caabec0f2bec0f3b03cac0f2b02bf3b000ac0f3b03cefcec0f3b03c02bb3903cb3b03c02cf00eecf3bf0002cf00efcec0b2cb3cec0f3bf0003203bf00ef2f00efcec0c80f32cbc03bcf3efcec0cc0cfbf3bf3bf3b000880894efcefc01451451403cec0f3bf3bf3bf00000d34f3bd3ced24b403b4bced2f3bf3b0004fced303c4c0f3bf124c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell75 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2fb2bcefc00bf002fcecb03c03bf3b28a01cefc2bbf0aedc71cf00efc03bf00efc00033c33bf0ceccf0cec0f0cabb03cabb03cec0f3b6c0edbf00edb6fb01a6bcefc01af3bf00ec068001aec0f3bf3b03c02493c93bf00ec0900f3b03c900900f3bf009008e4e7cefcec0f3bf3bf00000023f00efc03b8c0f23efc023f3bf000230238bbf3bf008bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell76 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-896),(-832)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell74 cell75

private theorem cell77 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-832),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell78 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell76 cell77

private theorem cell79 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell73 cell78

private theorem cell80 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell68 cell79

private theorem cell81 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell61 cell80

private theorem cell82 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell83 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell81 cell82

private theorem cell84 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-1024),(-960)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell85 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-960),(-896)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2a03ca80f2b03cec0f3b03cac0f2b02b03cefcec0f3b03c02baecf3b03c02cf00eecf3bf0002cf00efcec0b00f3bf0002c03bf00ef2cbbf00efcec0c80f3203bc80f32cfc03bcfcefcec0cfbf3bf3b000022f14efc014013ed4513ec0f3bf3bf3bf00000033d3cef4f3bd3cec04bcd34d00efced203bf3bf3b0004fced303c4c0f3bf124c0ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell86 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-960),(-896)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2fbf3b2bcefc00bf002fcecb03c03bf3b00aec073b73c73bf0a03cedc71c6fc03bf00efc03bf00efc00b33bf0cecb03bf0cec0f0ca80f3b03cec0f3b6c0edb01b6bcefc01af3b01aefc01af3bf00ec069aec0024ec0f3bf3b03c024f00ec0900f3b03c900900f3bf00923f23efcec0f3bf3bf000008fc03b8fc023f3bf000008fc022f3bf008bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell87 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-960),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell85 cell86

private theorem cell88 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell84 cell87

private theorem cell89 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-1024),(-960)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2aaaaaeaf3b03cec0f3b03cac0f2bec0f3b03c02b03c02bf00eecf3bf0002cf00efcec0b00f3bf00b00eec03c02cf00ef2f3bf00efcec0cb203bcb203bcc0efcefcec0cfbf3bf3b00002253bf14efc0144d403c4c0f3bf3bf3bf00000cf4f3bd3cec04bcd1203bf3bf3b0004d24fcefced34c0f3bf12480f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell90 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-1024),(-960)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xaf3b2bcefc00bf0becb2bc2fb03c03bf3b00aedcf0a03cedc71bf00efc03bf00efc00bf0033cecbf0cec0f0c32aec0f3b03cec0f3b6c0ec06fb01aefc6bb01aefc6bbf00ec0680680f3bf0093cec093bf3b03c024f00ec0900f3b03c9008c0f3bf008fcec0f3bf3bf00023023f3bf000008a3f22efc8bbf22efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell91 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-1024),(-960)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell89 cell90

private theorem cell92 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-960),(-896)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2aa87af903cafb03cec0f3b03cac0f2bafcec0f3b03c02b03c007b39f00eecf3bf0002cf00efcec0b00f3bf0002cf00eec03c032f00ef2f3bf00efcec0c80f32cbc03bc80f07cb91f3e7c03bcfcefcec0cfbf3bf3b000022022f3bf14efc014013ed403c4c0f3bf3bf3bf00000cf4f3bd3cec04bcd34d00efced203bf3bf3b0004fced303c4c0f3bf124874f9f00ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell93 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-960),(-896)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1cbe4af3bf3b2bcefc00bf002fcecb03c03bf3b00aec073b73c73bf0a03cedc71bf00efc03bf00efc00bf0033cecb03bf0cec0f0ca80f2aec0f3b03cec0f3b6c0edb0076f91dae7cefc01af3b01a6bcefc01af3bf00ec0680680f3bf0093cec0900f3bf3b03c024f00ec0900f3b03c9001e4e40f3bf008fcec0f3bf3bf000238fc023f3bf000008c01e3e7cefc8bbf22efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell94 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-960),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell92 cell93

private theorem cell95 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell91 cell94

private theorem cell96 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨(-1024),(-896)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell88 cell95

private theorem cell97 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x8bc000894efc53bf3bf005004fb500f1403c4c0f3b03cefcefcefc000000cf4f3bd3cef4f3b4804bcd1203bf3b480efcefcec0013f3b4c0f1303cefc492480efced303b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell98 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2a03caabec0f2bec0f3b03caeb02b03cefcec0f3b03c02b03c1abe86ac0efae6cf3b03c02cf00eecf3bf0002cf00efcec0b2cb3cec0f3bf0002cb3c03bf00ef2cb2f3bf00efcec0c80f32cbc03b033ec0f3303bcfcefcec0cfbf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell99 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell97 cell98

private theorem cell100 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x1b03b6c06fbf006c0efcec069af3bf006bcefc03b01a6bc6bb0006a4f3b03cefcec0f00924f24efc03b02403cec0f2402403cefc0241a3e86023efae7c023f3bf3b03cefcefc000023f00ee3f23efc0008c08e2efcefc022f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell101 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2fbf3b00aecaf0aefcefc00bf002fcecb03c03bf3b00aec02bb73c280f3bf0aedc71c6fc03bf00efc03bf00efc0002fc00cf3bf0033cecb03bf0cec0f0c32aec0f3b03ca80f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell102 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell100 cell101

private theorem cell103 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-832)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell99 cell102

private theorem cell104 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-832),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell105 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell103 cell104

private theorem cell106 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x8bc53bf005004fb5141d4e7cec0f1303c4fb03cefcefcefc000000cfb007d39d3cefcec0d34f3bf3b4b4d341d2e7c03bf3b480efcefcec0013f3b4c0f1303cefc492480f00efcec74f94fc03b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell107 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2aabb03ca871aaeb903cec0f2b03cec0f3b03caebafcec0f3b03c02bac71abeb9f3b03c0071acb3beb9f00eecb3bf3bf0002c02cf3bf00efcec0b2cec0f3bf0002c03bf00ef2032f00ef2f3bf00efcec0c80f3203bcb2cbcefc03b007cb903cec0f071b203beb9cfc03bcfcefcec0cfbf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell108 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell106 cell107

private theorem cell109 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x1b03b6c06c71806bbeb9f3bf000076b9f00efcec069af1aec06bbf3bf006bcefc03b01a01a03cefc6bb00093b03cefcec0f00924efc03b02403c93b03cec0f2493b0071a493beb903cefc0071a3eb98fc8fbf3b03cefcefc0008e3f23efc000023f000071a2eb9f22efcefc0228bbf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell110 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2c72f9f3bf3b0002bcecaf0aefcefc00bf002fcecb03c03bf3b00aec01cae5cf3b73c73bf0aedc73c03b707739f00edb03bf00efc03bf00efc00b00bf3bf001cce4cf0cefcecb03bf0cec0f0ca80f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell111 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell109 cell110

private theorem cell112 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-832)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell108 cell111

private theorem cell113 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-832),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell114 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell112 cell113

private theorem cell115 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨(-896),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell105 cell114

private theorem cell116 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell96 cell115

private theorem cell117 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x7) (rest:=0) (by decide +kernel)

private theorem cell118 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell116 cell117

private theorem cell119 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell120 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell118 cell119

private theorem cell121 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell83 cell120

private theorem cell122 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x6) (rest:=0) (by decide +kernel)

private theorem cell123 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell121 cell122

private theorem cell124 : Box.Closed ⟨⟨(-512),0⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1047e811fae7a0411b91bae411b91fa1b9eb91fa) (rest:=0) (by decide +kernel)

private theorem cell125 : Box.Closed ⟨⟨(-1024),0⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell123 cell124

private theorem cell126 : Box.Closed ⟨⟨(-1024),0⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell60 cell125

private theorem cell127 : Box.Closed ⟨⟨(-2048),0⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell41 cell126

private theorem cell128 : Box.Closed ⟨⟨(-2048),(-1536)⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell129 : Box.Closed ⟨⟨(-1536),(-1280)⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell130 : Box.Closed ⟨⟨(-1280),(-1216)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell131 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨0,64⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3803ce00f3b03ce00cbcec0f32ec0f32ec0f3b03c032f00032033f3bf00efcec0cf3ec0f3bf00033f00ef3cc0ed8f3bf00efcec061803b63cec00184bced2f3bf3bf3b000023f23efc000023f22880f22efcefc8a28bbf3bf3bf000120124fcefced34d303bf3bf3b000000a3bf28efcee203c880f00ec0f3bf28a28f3ba00f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell132 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨0,64⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3bc30f30efcefc00002af3bf00abcef0c00ec0f3b03c03bf3b00becbf0becb2bc03b2bc03bf00efcaaaeeaf2a02af3babcac0f3b03cec0f2bac0f3b03cec0f3b28a43c03bf00ed0010efc43bf00ec04006fbf1bec06c0f3bf3b03c01b6fbf00ec06c0f1aec0f3b03c680f3bf3bf0001a01a01a03c83bf3bf3bf00020f0083cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell133 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨0,64⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell131 cell132

private theorem cell134 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨64,128⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38e00f3b03c032f32ec0f32ec0f32ec0f3b03c032cb2f3bf00000cfc033f3bf00efcec0cc0f3bf00033f00ef3cc0ed8f3bf00efcec0600012ed2f3bf3bf3b0000208fbf23efc0008c08bb8c0f058ba8e2eb903cefcefc8a203c8bbf3bf3bf000124fcec0013efc4d3a00efc03bf3bf3b000022f28a22f28efcefcee203c880ec0f3bf28a00f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell135 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨64,128⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3bc3cefc000abbf00abcef0ab0f3bc3ca80f3b03c03bf3b000c3b2fcecbf0b03b03cecb2bc03bf00efca80abceeaf0016aeababae7c02bf3ba80efcafb03cec0f2baf8ec0f3b03cec0f3b28a03bf00ed0f00ec04006fbf1bec06c0f3bf3b03c01bf00ec06c0f1b03cec0f3b03c69af1aec0f3bf3bf0001a01a01a680f3bf3bf3bf00020f20efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell136 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨64,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell134 cell135

private theorem cell137 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell133 cell136

private theorem cell138 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell130 cell137

private theorem cell139 : Box.Closed ⟨⟨(-1280),(-1216)⟩,⟨128,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell140 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨128,192⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38e3803cec0f3b03cc80f32ec0f3b03c032c80ef2140e73f3bf3bf00033033f3bf00efcec0cc0f3bf0003303bf00ef303c63bf00efcec06004bbf3bf3b0000208fbf23efc0008e38e303cefcefc022ee203c880f3bf3bf3bf000004bb4fcec0a3c4d3a3c03bf3bf3b000022f288a803cefcefcee203c880ec0f3bf28a00f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell141 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨128,192⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3bc3cefc000abbf00abcec0c3cabbc3ca80f3b03c03bf3b0302fcecbf3003cecb280efc03bf00efc02af00abceea03bf00afcafbafcafb03cec0f2baf8ec0f3b03cec0f3b280ed0f00ec04006fcec001bec0f3bf3b03c01bf00ec06c0f1bec0f3b03c6c5039f1aec06bbf1aec0f3bf3bf0001a01af3bf0000083c83bf20efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell142 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨128,192⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell140 cell141

private theorem cell143 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨192,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell144 : Box.Closed ⟨⟨(-1216),(-1152)⟩,⟨128,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell142 cell143

private theorem cell145 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨128,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell139 cell144

private theorem cell146 : Box.Closed ⟨⟨(-1280),(-1152)⟩,⟨0,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell138 cell145

private theorem cell147 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x8e3efc023f3bf000008c58e2efa8f903cefc8858ba8a2ee2eb903c880f3bf3bf22880f22efcefcefc000480493152e93e53f3bf3bf3b4d34d303bf00efcefcec00000008bcefca2816803bea8e7ca00f3bf3bf3b880f22880f3b03c03b03cefca28a00efcee803c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell148 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38e3803cec0f3b03c038f00cbcec0f32cbbcbcec0f32cbbcbcec0f3b03c032f00000cbc005c80efacc0ef203beb9f3bf00efcec0033ec0f33033f3bcfcec0f3bf00033f00ef3cc0ed8173eb3e58f3bf3bf00efcec061803b63cec0018158e98e52f3b4bced2f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell149 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell147 cell148

private theorem cell150 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xa28a150e90e7c43bf00efc03b40043bf10efc03b01015be9be7c43b01befc6fb01b03cefcec0f006db03c6fbf006c0efcefc03b00501aefa01bec06bbeb903c680f3b03cec0f1a03cefcefc00069a6bbf0069a6bbf00680f2003cefcefcefc000020f20efc83bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell151 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30f3b030ef0f30efcefc000000abcabbf3bf00abcec0c3c140c3beb0e70f3bc3ca80f00ec0f3b03c03bf3b0002fb2fcecbf0becb14ae8be7c2fb2bc03b2bc03bf00efca80abceeaf00abc005abaaaaeeaeb9f3babc005aabefaaf9f2bec0f3b03cec0f2b03caebec0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell152 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell150 cell151

private theorem cell153 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,64⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell149 cell152

private theorem cell154 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨64,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell155 : Box.Closed ⟨⟨(-1152),(-1088)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell153 cell154

private theorem cell156 : Box.Closed ⟨⟨(-1088),(-1024)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell157 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨0,128⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell155 cell156

private theorem cell158 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨128,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell159 : Box.Closed ⟨⟨(-1152),(-1024)⟩,⟨0,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell157 cell158

private theorem cell160 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨0,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell146 cell159

private theorem cell161 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5005039eb9) (rest:=0) (by decide +kernel)

private theorem cell162 : Box.Closed ⟨⟨(-1280),(-1024)⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell160 cell161

private theorem cell163 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell129 cell162

private theorem cell164 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5e80e7a039) (rest:=0) (by decide +kernel)

private theorem cell165 : Box.Closed ⟨⟨(-1536),(-1024)⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell163 cell164

private theorem cell166 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell128 cell165

private theorem cell167 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell168 : Box.Closed ⟨⟨(-2048),(-1024)⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell166 cell167

private theorem cell169 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell170 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell171 : Box.Closed ⟨⟨(-1024),(-896)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5e80e7a) (rest:=0) (by decide +kernel)

private theorem cell172 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨768,832⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell173 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3203ccb25fb03cec0f3b03c5d7017f3b5fcec0f3b03c018f0063cec0600f3bf00600ed2f00efcec0492492480efcefcec09e7f3bf3bf3b00001af00020f20efcefc00083c01fee082003cec0f3bf3bf3bf000009e8f3ba3cec08bca2203bf3bf3b0007e27df03cefcefcedf7fb03c7c0f00ec0f3bf22880f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell174 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2af3babcefc000037f3bf00df7efcec0dfcdfbabcdfb03c03bf3b02aef0f2a03cef0c2ff00efc03bf00efc000e3ce3bf38ef703bf3803cec0f38e00f3b03cc80f3b03cec0f3bbeff00ec02bb2bc2bb2bc2bbf00ec028043bf3b03c010f00ed003c400f3bf3bf0000f3c0f0fefc3fbf000003daefc6bbf006bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell175 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨832,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell173 cell174

private theorem cell176 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell172 cell175

private theorem cell177 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨768,832⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell178 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x32c97ec0f3b03c5d7017017f3bf3b5fcec0f3b03c018f0063cec0600f3bf00600ed2f00efcec04924929c0efcefcec09c09e7f3bf3bf3bf3b00001af0001a83bf20efcefc00083c00000083cefcee0800f3bf3bf3bf00000a3ba3cec08bca28ee28bc03bf3bf3b0007df7fcefcec00207f9f1fefc7df03c03bf3b03c7c0f00ec0f3bf22880ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell179 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xabbf3babcefc000037f3bf00000dfcef7f37e37e40f3b03cefcef7dfcdfb03c03bf3b02aabcef0c3bf2a03cef0c00efc03bf00efc038f38ef803c03b03c03bf3803cec0f38e32ec0f3b03cc80f3b03cec0f3bbeff00eeff00ec0bfb2bc2bb2bc2bbf00ec028043bf3b03c010f00ed003c400f3bf3bf0000f3c0f0fec0f0fefc3fbf0000f6bbf1aefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell180 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨832,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell178 cell179

private theorem cell181 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell177 cell180

private theorem cell182 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell176 cell181

private theorem cell183 : Box.Closed ⟨⟨(-896),(-832)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell184 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨896,960⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3203cc80f17ec0f3b03c5d7017f3b5fcec0f3b03c018f0063cec0600f3bf00600ed2f00efcec0492480f1203b9fcefcec09e7f3bf3bf3b00001af0001af20efcefc00083c00083cee0f3bf3bf00000a3ba3cec08bc022f28a00efcee203bf3bf3b0007fcedf7fb03c7c0f00ec0f3bf227c0ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell185 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨896,960⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdfbf3babcefc000037f3bf00df7efcef703c03bf3b02aec0c3bc3ca80f3bf2a03cef0c00efc03bf00efce3803c03bf3803cec0f38c80f3b03cc80f3b03cec0f3bbeff00eef00aefc00af3b2bc2bbf00ec028043bf3b03c010f00ed003c400f3bf3bf0000f3c0f0fefc3fbf0000f01af3bf006bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell186 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨896,960⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell184 cell185

private theorem cell187 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨960,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell188 : Box.Closed ⟨⟨(-832),(-768)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell186 cell187

private theorem cell189 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell183 cell188

private theorem cell190 : Box.Closed ⟨⟨(-896),(-768)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell182 cell189

private theorem cell191 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell171 cell190

private theorem cell192 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell170 cell191

private theorem cell193 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell194 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨768,832⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell195 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x6bc0006a0efc83bf3bf00800020f3b83cefcefc000a3b022f00028efca2803bf3b8a2f00efcefcec001f7dff3bf3b00083c7e017a800ec5eb9f3bf1f7c0f00efcec0f1f03c03b03cefc8a28bcedf7fc03b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell196 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3203cc97ec0f17ec0f3b03c5c05fc0005fc018f3bf3b018efcec0f3b03c018f0063cec0600f3bf0001803bf00ed2480ed2f3bf00efcec049203b480f1203b9fcefcec09c09c09e8f3bf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell197 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell195 cell196

private theorem cell198 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x30bfc03bbfc03bbfc03bbc02bbf002bcec02bbf0aefc03b00a00aefc2bb00043b03cefcec0f0043c03b400f1003cefcefc000400ed003c3c0f3b03c3c0f3bf0fefc0003c03daefcefc01af3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell199 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdeaf3bf3baaaf2aefcefc000037f3bf00000dfcef7f3817a038ec5eb9dfce00f3b03cefcef7dfcdfb03c03bf3b02aabcec0c3bc3cc00ec0f3bf2a03cef003bf00efce3803c03bf38ec0f38e32ec0f3b03cc80f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell200 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell198 cell199

private theorem cell201 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨832,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell197 cell200

private theorem cell202 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell194 cell201

private theorem cell203 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨768,832⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5) (rest:=0) (by decide +kernel)

private theorem cell204 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x69aefc00068011a17ae7cefc020f3bf3bf0082083cefcefc000a3b022f00000122e7cefca2812203b17ae7c03bf3b8a28bcee203bf00efcefcec001f7fbf3b02012017ae60f3bf1f7fb11f7fb17ae40f00efcec0f1f7c0f3b03c03b03cefc8a2880f00efcedf03b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell205 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3203c5fb03c5c05c45f95fcefc00063c63bf3b018efcec0f3b03c018f0063cec0600f3bf00018118e7c03bf00ed2012f00ed2f3bf00efcec049203b9c44b99fc03b9fcefcec00279fcec0027127e7cec0a3bf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell206 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell204 cell205

private theorem cell207 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x3003b12fe6ff00efc03bbeff00efc03bbc0bc42b9f3bf2fec02bbf0aefc03b00a00a03cefc2bb000110e50f3b03cefcec0f0043c03b400f1003cefcefc000400ed0400f3b03c3c43f9f0fec0f3bf0fefc00f01af3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell208 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdfbf3b000abceeaf2aefcefc000000dfcdfbf3bf00000137dfb17ae7cef7dfbf3813817ae7ce3b03cefcef7dfb03c03bf3b000abbaaaf2aefcec0100abb17ae70f3bc3c12ae40f00ec0f3bf2a03cef003bf00efce38f38ec0f3803c13217ae40f32ec0f3b03ccb2ec0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell209 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell207 cell208

private theorem cell210 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨832,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell206 cell209

private theorem cell211 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell203 cell210

private theorem cell212 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨768,896⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell202 cell211

private theorem cell213 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨896,960⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3203c5fb03c5d701763bf3b018efcec0f3b03c018f0063cec0600f3bf0001803bf00ed2f00efcec0480f1203b9e703b9fcefcec09c09c09e8f3bf3bf3bf3bf3b00001af0001af0083cefcefc00083c00083cee0f3bf3bf00028ec08bc022f28a22f00efcee203bf3bf3b0007fcec081f83cefc7df03c03bf3b03c7c0f00ec0f3bf228bb7c0ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell214 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨896,960⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdfbf3baaaefcefc000037f3bf00000dfcef7f38dfce3b03cefcef703c03bf3b02aec0ab0f3bc3ca80f3bf2a03cef003bf00efce3803c03bf3803cec0f3803cc80f3b03cc80f3b03cec0f3bc2ff00eeff00eeff00eef02fefcbfb00aefc00af3bf00ec0280010ec0f3bf3b03c010f00ed003c400f3bf3bf0001003b40fec0f0fefc3fbf003c06bcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell215 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨896,960⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell213 cell214

private theorem cell216 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨960,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell217 : Box.Closed ⟨⟨(-768),(-704)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell215 cell216

private theorem cell218 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨896,960⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x32c80f3b03c5fb03c5c05fc018f3b018efcec0f3b03c018f0063cec0600f3bf000046394bc03bf00ed2f00efcec0480f1203b9e703b9fcefcec09c09e8f3bf3bf3bf3b000680680004839f20efcefcefc00083c820f3bf3bf00028ec08bc022f28128e448b9f00efcee28bc03bf3bf3b0007fcec083c7c47f903c03bf3b03c7c0f00ec0f3bf007fc8a203c03bf3b7c0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell219 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨896,960⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x37f3b000abceeaf3703cefcefc000037f3bf00000137e7cef7f3803cefcef703c03bf3b02aabcec012ae44c39f3bc3ca80f3bf2a03cef003bf00efce38f3803cec0f38138e40f3b03ccbb03ccbb03cec0f3bc2ff00eeff00eef02fefcbfb00aefc00af3bf00ec028000a110e7cec0f3bf3b03c010f00ed003c400f3bf3bf0001003b400f0f03cefc3fbf003c001af1aefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell220 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨896,960⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell218 cell219

private theorem cell221 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨960,1024⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x325fb03c5fb03c5c05fc018f3b63cec0f3b03c60063cec06184bcec0f3bf00012f00ed2f00efcec0480f1203b9fcec09c09e8f3bf3bf3bf3b00068068069a83cefcefcefc00083c83bf3bf00028ee28a803b880efcee203bf3bf3b0007fcec083c7df03c03bf3b03c7c0f00ec0f3bf007fc89f03c03bf3b7c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell222 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨960,1024⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdfb000abceeaf3703cefcefc000037f3bf00000dfcef7f3803cefcef703c03bf3b02aec0abb030efcabbf2aef003bf00efce3803cec0f38cbccbb03ccbb03ccbb03cec0f3bc2ff00eeff00eef00aefc00af3bf00ec0280280f3bf3b03c00a43c43bf00ed003c43bf3bf00010400f0f03cefc3fbf003c03daefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell223 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨960,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell221 cell222

private theorem cell224 : Box.Closed ⟨⟨(-704),(-640)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell220 cell223

private theorem cell225 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨896,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell217 cell224

private theorem cell226 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell212 cell225

private theorem cell227 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x4) (rest:=0) (by decide +kernel)

private theorem cell228 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell226 cell227

private theorem cell229 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell193 cell228

private theorem cell230 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell192 cell229

private theorem cell231 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell169 cell230

private theorem cell232 : Box.Closed ⟨⟨(-512),0⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x4101e8407ae41e84045e7a179045045e7ae7ae7a) (rest:=0) (by decide +kernel)

private theorem cell233 : Box.Closed ⟨⟨(-1024),0⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell231 cell232

private theorem cell234 : Box.Closed ⟨⟨(-1024),(-768)⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell235 : Box.Closed ⟨⟨(-768),(-640)⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell236 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨1024,1088⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1703c5fb03c5c0f0063c63b63cec0f3b03c60063cec0600f18012f3b4bcec0f3bf00012f00ed2f00efcec0480f1203b9fc03b9fcec09c0a3bf3bf3bf3b00068069aefcefc00001a03c83bf20efc83bf3bf00028028efcee28a203b880efcee28bc03bf3bf3b01fee07e0f3b03c7c0f00ec0f3bf1f7e2edff3b7c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell237 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨1024,1088⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xdfbdeaabbf37efcefc000037f3bf00e37f38efcef703bf3b02aabcec0abb02aefcabbf2aef003bc3c03bf00efce38e00cbcec0f3b03cec0f32cbb03ccbb03cec0f3bc00eeff00eef02f00aefcefc00af3bf00ec0280280f3bf3b03c00a280f10efc010f3bf00ed003c43bf3bf0001041003cefc00ff3bf003c03fcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell238 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨1024,1088⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell236 cell237

private theorem cell239 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨1088,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell240 : Box.Closed ⟨⟨(-640),(-576)⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell238 cell239

private theorem cell241 : Box.Closed ⟨⟨(-576),(-512)⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x13a) (rest:=0) (by decide +kernel)

private theorem cell242 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell240 cell241

private theorem cell243 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell244 : Box.Closed ⟨⟨(-640),(-512)⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell242 cell243

private theorem cell245 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell235 cell244

private theorem cell246 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨1280,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell247 : Box.Closed ⟨⟨(-768),(-512)⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell245 cell246

private theorem cell248 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell234 cell247

private theorem cell249 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨1536,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell250 : Box.Closed ⟨⟨(-1024),(-512)⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell248 cell249

private theorem cell251 : Box.Closed ⟨⟨(-512),0⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x4e8010013ae7ae7a) (rest:=0) (by decide +kernel)

private theorem cell252 : Box.Closed ⟨⟨(-1024),0⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell250 cell251

private theorem cell253 : Box.Closed ⟨⟨(-1024),0⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell233 cell252

private theorem cell254 : Box.Closed ⟨⟨(-2048),0⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell168 cell253

private theorem cell255 : Box.Closed ⟨⟨(-2048),0⟩,⟨(-2048),2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell127 cell254

private theorem cell256 : Box.Closed ⟨⟨0,512⟩,⟨(-2048),(-1536)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell257 : Box.Closed ⟨⟨0,256⟩,⟨(-1536),(-1280)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell258 : Box.Closed ⟨⟨0,128⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x71c0e8703ae7a) (rest:=0) (by decide +kernel)

private theorem cell259 : Box.Closed ⟨⟨128,192⟩,⟨(-1280),(-1216)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell260 : Box.Closed ⟨⟨128,192⟩,⟨(-1216),(-1152)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xc03c300f3b03c30c37cec0f0037c00df3b37cec0f3b03c00df0000d02bf3bf00efcec0afbf00ac0eebaebaebf3bf3bf00efcec002cec0f2cec002c02cb7cefceedf3bf3bf3b000013f13efc0004fcd7503cd40f3bf3bf3bf0002d02dcfcefcec0000d3cefccf3cf4f00efc03bf3bf3b000d3cef5d7503bf3b03cd00f34ec0f00ec0f3bf34d3c03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell261 : Box.Closed ⟨⟨128,192⟩,⟨(-1216),(-1152)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1c73cefc00001c01cf3bf3bf0001deddf1defcedc03c03bf3b00071bf3b6fcedbf1c03c03b03cedb6fc03b97c03bf00efc01df0077ceddf0b03cec0f0b2c0f3b03cec0f3b96593c03b93c03bf00ee402403bf3bf00ec08e3f23ee3f23ec08fbf3b03c8c0ec08c0f15ec0f3b03c540f3bf3bf00015540f1503cefc01553c53bf3bf00014f0053cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell262 : Box.Closed ⟨⟨128,192⟩,⟨(-1216),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell260 cell261

private theorem cell263 : Box.Closed ⟨⟨128,192⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell259 cell262

private theorem cell264 : Box.Closed ⟨⟨192,256⟩,⟨(-1280),(-1216)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell265 : Box.Closed ⟨⟨192,256⟩,⟨(-1216),(-1152)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xc03c300f3b03c300f0037c00df3b37cec0f3b03c00df0000df00efcec0aebec0f3bf0002bf00eebaebf3bf00efcec0000b3b03cec0f2c03bb3cec002cec0b7bf3bf3bf3b0004fc0004f54f503cefcefcd7503cd40f3bf3bf3bf0002d02dcfcefcec0033efccf303bf3bf3b000d3cef5d74ef503bf3b03cd00f00ec0f3bf34d3c03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell266 : Box.Closed ⟨⟨192,256⟩,⟨(-1216),(-1152)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1c73cefc00001cf3bf0001dedc77bf1defcedc03c03bf3b01bedbf1b03b03cedb97c03b97c03bf00efc01df0077ceddf0077c2fb77c2fb03cec0f0b03cec0f3b940ee403bf00ee4024efc000900efc03bf3bf00ec08e3f23ec08c0f3bf3b03c0238fbf00ec0540f3b03c540f3bf3bf00015540f1503cefc014f3bf00014f0053cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell267 : Box.Closed ⟨⟨192,256⟩,⟨(-1216),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell265 cell266

private theorem cell268 : Box.Closed ⟨⟨192,256⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell264 cell267

private theorem cell269 : Box.Closed ⟨⟨128,256⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell263 cell268

private theorem cell270 : Box.Closed ⟨⟨128,192⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x7) (rest:=0) (by decide +kernel)

private theorem cell271 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x13f00013d5303cd40f3bf3bf35d40f3503cefcefcefc000b40b6db73f3bf3bf3b000000cfbf3bf33cf3f3bcf3cc7cfae7c03bf00efcefcec0d3b035f00d7cd3bd40f00efcec0f3403c03b03cefcd34d3cef4f00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell272 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xc03c33b03c300f0030defc00df3b37cec0f3b03c00df0000df00efcec0aebafbafcec0f3bf0002bf00eebac0eebaebf3bf3bf00efcec0000b3b03cec0f2c03bb3c03bb3cec0b0002cb7ceedf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell273 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell271 cell272

private theorem cell274 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x25964f00efc03b93c03b90090093bf3bf0002403bf00efcefc03b0238fc8fb023efc8fb02303cefcec0f008e38fbf23efc03b01503cec0f1503cefcefc00055503c554ec0f3bf0053cefc014014f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell275 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1c71cf1cefcefc00001cf3bf0000077cedc740f3bf1d03cefcedc03bf3b0006c76fae5bf3b6fcedb6fc6fbf1b03b03c03b03cedb6fc6fb97c03b97c03bf00efc01df0077ceddf0077c00bf3b77c2fb03cec0f0b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell276 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell274 cell275

private theorem cell277 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1088)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell273 cell276

private theorem cell278 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x13f000004d303cefcd751f903cd47e40f3bf3bf35d40f35d40f3b03cefcefcefc000b40b73b47e47cfa1f9f3bf3bf3b000000007cfa1f9f3bf3bf33cc0ef303bf3bcf31f303be87e7c03bf00efcefcec0d3b035d47d7a1f9f3bf00d3cd3b1f5d3be87e40f00efcec0f3403c03b03cefcd341f4e87e74f3bd3cef403bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell279 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xc03c33b03c300f0030c1f937cefc00037c00df3bf3b37cec0f3b03c00d340ecdf3bf0000d00df3bf00efcec034737a1f9afc02bf3bafcec0f3bf0002b03bf00eebac0eeb1ebe87e47afa1f9f3bf3bf00efcec00001c0b3be87e40f3b03cec0f07b00efa1f9b3c03bb3c03bb3cec0b0002c1ede87e7ceedf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell280 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell278 cell279

private theorem cell281 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x251e5e87e64f00efc03b93c03b900900907024efa1f9f3bf3bf000001e403be87e7c03bf00efcefc03b0078fa1f91e3e87e7c8fb023efc8fb0008fb03cefcec0f008e303c8c757a1f9f3bf15efc03b01503c57b03cec0f15015efc57b03cefcefc00055503c540f3b03c5541f9f14ec0f3bf0053cefc014014f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell282 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x73b71c1dce87e7c73bf1cefcefc00001cf3bf000001dc77be87e7cedc700f3bf0777a1f977c77b03cefcedc03bf3b0001c06fbe87e5bf3b6fcec06fb01befc6fbf076fa1f903c03b03c03b03cec76fa1f9947e7c6fb97c03b97c03bf00efc00077c77bf0077ceddf00747e7c01d1f9f3b77c00bf0bec0f3b03cec0f0b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell283 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell281 cell282

private theorem cell284 : Box.Closed ⟨⟨192,256⟩,⟨(-1088),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell280 cell283

private theorem cell285 : Box.Closed ⟨⟨192,256⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell277 cell284

private theorem cell286 : Box.Closed ⟨⟨128,256⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell270 cell285

private theorem cell287 : Box.Closed ⟨⟨128,256⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell269 cell286

private theorem cell288 : Box.Closed ⟨⟨0,256⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell258 cell287

private theorem cell289 : Box.Closed ⟨⟨0,256⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell257 cell288

private theorem cell290 : Box.Closed ⟨⟨256,512⟩,⟨(-1536),(-1280)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell291 : Box.Closed ⟨⟨256,320⟩,⟨(-1280),(-1216)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell292 : Box.Closed ⟨⟨256,320⟩,⟨(-1216),(-1152)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xb33b03c300f3b03c300f0037c00df3b37cec0f3b03c00df00340efcec034dafbafcec0f3bf0002bf00eebf00efcec002b03cec0f2bafc03bb3c03bb3cec0b0002deedf3bf3bf3bf3b0004fc0004f5efcd75d40f3bf3bf3bf0002d02defcef3cf3cfcef303bf3bf3b000d3cef5d3503bf3b03cd00ec0f3bf34d33d3cef4f3bd3c03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell293 : Box.Closed ⟨⟨256,320⟩,⟨(-1216),(-1152)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1c71c6fc73bf1cefcefc00073bf0001dedcf1defcedc03c03bf3b01bedb6fc6fbf1bee503b97c03bf00efc01df1deddf1d2fb03cec0f0b03cec0f3b96503bf00ee4f00ee40240238fcefcefc0008fc03bf3bf00ec08c08c0f3bf3b03c0238d5efc57bf00ec057b03c540f3bf3bf00015540f1503cefc014f3bf00014f00513efcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell294 : Box.Closed ⟨⟨256,320⟩,⟨(-1216),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell292 cell293

private theorem cell295 : Box.Closed ⟨⟨256,320⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell291 cell294

private theorem cell296 : Box.Closed ⟨⟨320,384⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell297 : Box.Closed ⟨⟨256,384⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell295 cell296

private theorem cell298 : Box.Closed ⟨⟨256,320⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xb33b03c33b03c300f0c00df3b37cec0f3b03c00df0000df00efcec034d02bf3bafcec0f3bf0002bf00eebaebf3bf00efcec002b03cec0f2bac0eebeb9b3c03bb3c03bb3cec0b0002ceedf3bf3bf3bf3b0004fc000013d7bf35d75efcefcd7503cd40f3bf3bf3bf0002db7cec0033efccf303bcfcef3cc0efc03bf3bf3b034ec0d7cd3403c03bf3b03cd00f00ec0f3bf34d33cf3ef3eb9d3cef4f3bd00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell299 : Box.Closed ⟨⟨256,320⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x73b71c6db6fb6fae7c73bf1cefcefc00001cf3bf0000073cedcf1d03cefcedc03bf3b0006fb6fcedb01befc6fbf1b03b03cee597c03bf00efc01df0077ceddf1d77b77c74bec0f3b03cec0f0b03cec0f3b96403bf00ee4f00ee40240248c08fb8fae7cefcefc0008fc03bf3bf00ec08e3f23ec08c0f3bf3b03c0238c0f15efc57bf00ec0540f3b03c540f3bf3bf00015540f14efc014f3bf00500513efcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell300 : Box.Closed ⟨⟨256,320⟩,⟨(-1152),(-1088)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell298 cell299

private theorem cell301 : Box.Closed ⟨⟨256,320⟩,⟨(-1088),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell302 : Box.Closed ⟨⟨256,320⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell300 cell301

private theorem cell303 : Box.Closed ⟨⟨320,384⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xb33b03c300f3b03c30c00c37bf3b37cec0f3b03c00df00340efcec034dafcec0f3bf0002b03bf00eebf00efcec002b03cec0f2bafc03bb3c03bb3cec0b00b2df3bf3bf3bf3b0004fc000d75efcd75d40f3bf3bf3bf0002db7cef3ced03bcc0efcef303bf3bf3b000d3cec0d74d7cefcd34f3b03cd00ec0f3bf00d3c033d39f33cc8cfae7cef403bf3bd00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell304 : Box.Closed ⟨⟨320,384⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x73b01cedb21beb96fc6dce40f3bf1c03cefcefc00073bf0071cf1d73c77b03cefcedc03c03bf3b01bec06fb01befc6fbf1bee597c03bf00efc01df1deddf1d77b03cec0f0b03cec0f3b964f00ee4f00ee40240238fcefcefc0008fc03bf3bf00ec08c0023ec0f3bf3b03c02357c57bf00ec057b03c540f3bf3bf00015554ec0f14efc53bf00014f00513efcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell305 : Box.Closed ⟨⟨320,384⟩,⟨(-1152),(-1088)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell303 cell304

private theorem cell306 : Box.Closed ⟨⟨320,384⟩,⟨(-1088),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell307 : Box.Closed ⟨⟨320,384⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell305 cell306

private theorem cell308 : Box.Closed ⟨⟨256,384⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell302 cell307

private theorem cell309 : Box.Closed ⟨⟨256,384⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell297 cell308

private theorem cell310 : Box.Closed ⟨⟨384,512⟩,⟨(-1280),(-1152)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell311 : Box.Closed ⟨⟨384,448⟩,⟨(-1152),(-1088)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xb300f3b03c30c00defcec0f3b03c00df00340efcec0340f3bf0000dafc03bf00eebafbf00efcec0ac0f2b03bac0f08b39b3cefc03bb3cec0b00b00b3bf3bf3bf3bf3b0004c04c0d7cefcefc035d75d7bf3bf3bf0002def3033f2db73f00efcef303bf3bf3b000d3cec0d74efcd3b03cd00f3bf00d3ccc8d3903c03bf3bd00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell312 : Box.Closed ⟨⟨384,448⟩,⟨(-1152),(-1088)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x73b00021ce7cedbf1c03cefcefc01cf0071c77b03cefcedc03c03bf3b01bec06dbf3b97c6c0f3bf1bee503bf00efc75deddf1dec0f1d03c2fb03c2fb03cec0f3b900ee4f00ee4f00ee4024224e7c023f3b023efcefc023f3bf00ec08e3ec002357cec0f3bf3b03c015f00ec057b03c540f3bf3bf0001503b53c53bf00014f13efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell313 : Box.Closed ⟨⟨384,448⟩,⟨(-1152),(-1088)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell311 cell312

private theorem cell314 : Box.Closed ⟨⟨384,448⟩,⟨(-1088),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell315 : Box.Closed ⟨⟨384,448⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell313 cell314

private theorem cell316 : Box.Closed ⟨⟨448,512⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell317 : Box.Closed ⟨⟨384,512⟩,⟨(-1152),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell315 cell316

private theorem cell318 : Box.Closed ⟨⟨384,512⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell310 cell317

private theorem cell319 : Box.Closed ⟨⟨256,512⟩,⟨(-1280),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell309 cell318

private theorem cell320 : Box.Closed ⟨⟨256,512⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell290 cell319

private theorem cell321 : Box.Closed ⟨⟨0,512⟩,⟨(-1536),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell289 cell320

private theorem cell322 : Box.Closed ⟨⟨0,512⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell256 cell321

private theorem cell323 : Box.Closed ⟨⟨512,1024⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x803ae40eb903a) (rest:=0) (by decide +kernel)

private theorem cell324 : Box.Closed ⟨⟨0,1024⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell322 cell323

private theorem cell325 : Box.Closed ⟨⟨0,512⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x208123ae7a07923a04123a0411fa1f9eb9eb92081f91fae7a) (rest:=0) (by decide +kernel)

private theorem cell326 : Box.Closed ⟨⟨512,768⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell327 : Box.Closed ⟨⟨768,1024⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x23903a200239eb9) (rest:=0) (by decide +kernel)

private theorem cell328 : Box.Closed ⟨⟨768,896⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell329 : Box.Closed ⟨⟨896,1024⟩,⟨(-768),(-640)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x803a239) (rest:=0) (by decide +kernel)

private theorem cell330 : Box.Closed ⟨⟨896,960⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell331 : Box.Closed ⟨⟨960,1024⟩,⟨(-640),(-576)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x8) (rest:=0) (by decide +kernel)

private theorem cell332 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xd7c000d74efcd3bf3bf00034d3bf00bbbd00f34b88e40f3b03cefcefcefc00000eb3ceecf3b02df0002cefcb2cb08e7c03bf3bb40efcefcec0000bbcb6dbba239b80eeee88e7cb48e40f3bf3bf3bbaebbcec0f2eb80f3b03c03b03cefcb6d03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell333 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c75d748e5df3b03cec0f3b03c01ef007bcec0f007bc01ef3b7bcec0f007bc01e01ef3bf3b7bcec0f3b03c00cf0000cf00efcec0300f3bf0000c03bf00ecdf00efcec034d34d340efcefcecef3bf3b) (rest:=0) (by decide +kernel)

private theorem cell334 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell332 cell333

private theorem cell335 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x16015ed5f15ed5f15efc03b01500053b03cefcec0f0053c03b01403cec0f1403cefcefc000db603cdbb03cd80f3bf00db603cd80f3bf00d80f3603cefcefcefc000035d48e7cd7bf35efc035f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell336 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25f3b97cefc0000009bc9bbf3bf009a6f26efcec0948e7c026ee6e88e659ba239f3b97c980f3b03c03bf3b025ec0908e64f3b93c900ec0f3bf2503cee4916f00efc03bf00efc000988e7c73bf0073cee603bf1c73b03cec0f1c71dec0f3b03c740f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell337 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell335 cell336

private theorem cell338 : Box.Closed ⟨⟨960,1024⟩,⟨(-576),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell334 cell337

private theorem cell339 : Box.Closed ⟨⟨960,1024⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell331 cell338

private theorem cell340 : Box.Closed ⟨⟨896,1024⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell330 cell339

private theorem cell341 : Box.Closed ⟨⟨896,1024⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell329 cell340

private theorem cell342 : Box.Closed ⟨⟨768,1024⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell328 cell341

private theorem cell343 : Box.Closed ⟨⟨768,1024⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell327 cell342

private theorem cell344 : Box.Closed ⟨⟨512,1024⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell326 cell343

private theorem cell345 : Box.Closed ⟨⟨512,768⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x223a) (rest:=0) (by decide +kernel)

private theorem cell346 : Box.Closed ⟨⟨768,896⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x223a) (rest:=0) (by decide +kernel)

private theorem cell347 : Box.Closed ⟨⟨896,960⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x223a) (rest:=0) (by decide +kernel)

private theorem cell348 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xd40d7cefc000034088eb9f34efcd3bf3bf00034d34d00f3bf3bf00bbbd00f2e03cb80f3b03cefcefcefc00000eb3cec0b2cf3bf3b02df2cb00eecb0223ae7c03bf3bb6cb7bb7ab79b7ceedf00efcefcec0000000b8223ae7cefcb6db6d03c03be8223ae7cb40f3bf3bf3bbaeb80efcec0f2e03cb80eeee8223ae40f3b03c03b03cefcb6d03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell349 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c75d03cec0f3b03c01d088eb9f0078223ae7cec0f007bc01ef3b7bcec0f007bc01ef3b7bcec0f3b03c01e78223ae4cf3b03c00cf00eccf3bf0000cf00efceccf0000c03bf00ecc37b03c37bf00efcec034000e34ee8223ae4ef3b3bcecef3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell350 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell348 cell349

private theorem cell351 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x16596556e8223ae7c5bbf00efc03b57c03b01501553bf3b00053b03cefcec0f1401403cec0f1401403cefc014d8223ae7cdbbf3b03cefcefc000db603cd80f3bf00db603cd80f3bf00d8223ae40f35088eb903cefcefcefc000035f35efc035f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell352 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25f3b97cefc000000026ee6e8223ae7c026f3bf3bf00026ee6f26efcec097c940025f3be8223ae65f3b97c98223ae40f00ec0f3b03c03bf3b02596593b97a979f25efcec090223ae64f3b024efc93bf2503cee493c03b916f00efc03bf00efc0009bc026f3bf0073cee603bf0073c73b73c73b03cec0f1c71c088eb903cec0f3b03c740f1dec0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell353 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell351 cell352

private theorem cell354 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-448)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell350 cell353

private theorem cell355 : Box.Closed ⟨⟨960,1024⟩,⟨(-448),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell356 : Box.Closed ⟨⟨960,1024⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell354 cell355

private theorem cell357 : Box.Closed ⟨⟨896,1024⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell347 cell356

private theorem cell358 : Box.Closed ⟨⟨896,1024⟩,⟨(-384),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell359 : Box.Closed ⟨⟨896,1024⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell357 cell358

private theorem cell360 : Box.Closed ⟨⟨768,1024⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell346 cell359

private theorem cell361 : Box.Closed ⟨⟨768,1024⟩,⟨(-256),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell362 : Box.Closed ⟨⟨768,1024⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell360 cell361

private theorem cell363 : Box.Closed ⟨⟨512,1024⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell345 cell362

private theorem cell364 : Box.Closed ⟨⟨512,1024⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell344 cell363

private theorem cell365 : Box.Closed ⟨⟨0,1024⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell325 cell364

private theorem cell366 : Box.Closed ⟨⟨0,1024⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell324 cell365

private theorem cell367 : Box.Closed ⟨⟨1024,2048⟩,⟨(-2048),(-1024)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell368 : Box.Closed ⟨⟨1024,1280⟩,⟨(-1024),(-768)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell369 : Box.Closed ⟨⟨1024,1152⟩,⟨(-768),(-640)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell370 : Box.Closed ⟨⟨1024,1088⟩,⟨(-640),(-576)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c75d7bb03cec0f3b03c79eec0f1e01ef3b7bcec0f3b03c00cf00300efcec0300f3bf00300ecdf00efcec0340f0d34d3bcefcecef3bf3b000035f00035d3bf34efcefc03402eef4d00f3bf3bf3bf00000b3bb3cec0b7cb2ceed03bf3bf3b000b80b7bbae03cefcefceee03cb80f00ec0f3bf2db40f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell371 : Box.Closed ⟨⟨1024,1088⟩,⟨(-640),(-576)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25f3b97cefc000026f3bf009bcec09bc9bb940efc9bb03c03bf3b025ee493bf2503cee4900efc03bf00efc01cf1cee603bf1cec0f1c71dec0f3b03c740f3b03cec0f3b59657c57b57c015f3bf00ec054053bf3b03c014f00ec053b03c500f3bf3bf00036d80f36efc036dbbf3bf00000db5efcd7bf00d7cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell372 : Box.Closed ⟨⟨1024,1088⟩,⟨(-640),(-576)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell370 cell371

private theorem cell373 : Box.Closed ⟨⟨1024,1088⟩,⟨(-576),(-512)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c75d03cec0f3b03c01ef1eec0f1eec0f1e01ef3b7bcec0f3b03c01e33b03c33bf00300efceccf00300ecdf00efcec0340f0decef3bf3b000035035f3bf00034f34efcefc03402eef403cd2e03cec0f3bf3bf3bf000003acf3bb3cec0b7cb2cb3ceed03bf3bf3b00002ef2db6ef2d03cefcefceee03cb80f00ec0f3bf2db40f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell374 : Box.Closed ⟨⟨1024,1088⟩,⟨(-576),(-512)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25f3b97cefc000026f3bf009bcec097c9a5f3b97c980f3b03c03bf3b025ee493c93bf2503cee4916f00efc03bf00efc0009bc73bf0073cee603bf1cec0f1c700f3b03c740f1dec0f3b03cec0f3b595015f3bf00ec054053bf3b03c50053b03c500536efcec0f3bf3bf00036d80f36efc036036d80f3bf3bf3bf00000d7cd7bf00d7cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell375 : Box.Closed ⟨⟨1024,1088⟩,⟨(-576),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell373 cell374

private theorem cell376 : Box.Closed ⟨⟨1024,1088⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell372 cell375

private theorem cell377 : Box.Closed ⟨⟨1088,1152⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell378 : Box.Closed ⟨⟨1024,1152⟩,⟨(-640),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell376 cell377

private theorem cell379 : Box.Closed ⟨⟨1024,1152⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell369 cell378

private theorem cell380 : Box.Closed ⟨⟨1152,1280⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell381 : Box.Closed ⟨⟨1024,1280⟩,⟨(-768),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell379 cell380

private theorem cell382 : Box.Closed ⟨⟨1024,1280⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell368 cell381

private theorem cell383 : Box.Closed ⟨⟨1280,1536⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell384 : Box.Closed ⟨⟨1024,1536⟩,⟨(-1024),(-512)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell382 cell383

private theorem cell385 : Box.Closed ⟨⟨1024,1088⟩,⟨(-512),(-448)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c740f3b03c01df007bcec0f007bc7bb7bcec0f007bc01ef3b7bcec0f3b03c01e03c00cf00eccf3bf0000cf00efceccf0000cf00ecc03c37bf00efcec03403bbf3bf3b000035035035f3bf3bf00d3cefc000d34efcbb403cbaeec0f3bf3bf3bf0000eb3cec002defcb2cb00efceedb2df3bb7c03bf3bf3b00000002ef3bf2db6defcefceee03cbae03cec0f00ec0f3bf2db40efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell386 : Box.Closed ⟨⟨1024,1088⟩,⟨(-512),(-448)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x97b97cefc0000009bc9bbf3bf009bcee597b97c980f00ec0f3b03c03bf3b025964f25efcec093b93c93bf2503b03cee45bc03bf00efc0269bbf0073cee6f1c73b03cec0f1c03c740f1dec0f1dec0f3b03cec0f3b580ed5f00ec054053cec0500f3bf3b03c500500f3b03c500500f3bf00dbcec0f3bf3bf00036d80f3603cefc036db603cefc03603cd40f3bf3bf3bf00035f00d7cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell387 : Box.Closed ⟨⟨1024,1088⟩,⟨(-512),(-448)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell385 cell386

private theorem cell388 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x35f00035f34efcefc034d3bf3bf00034d34d00f3bf3bf2eb80f2e03cefcefcefc000380b2cf3bf3b00002df3bf2cb2c03bf3b02df2cb02e7ceedf00efcefcec000002defcb7bf3bbaebbcec0f2e03c0aee82e40f3b03c03b03cefcb6d03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell389 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c740f3b03c74077cec0f00782e7c01ef3b7bcec0f007bc01ef3b7bcec0f3b03c01e780eccf3bf0000cf00efceccf0000cf00ecc03c00df00ecdf3bf00efcec034000d3bcecef3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell390 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell388 cell389

private theorem cell391 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x16595f00efc03b57c03b01501503cefc014f3b01403cefcec0f1401403cec0f14036efcdbb03cefcefc000db603cd80f3bf00db603cd82e40f3bf00d40f35efcefcefc000d7c035f3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell392 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x97b97cefc0000000a6e82e7c026f3bf3bf009a6f26efcee5940ec0f3b03c03bf3b025902e64f2503cefcec093b93c93bf2503c03b03cee493c03b5bc03bf00efc026f009bcee6f0073c73b73c73b03cec0f1c73b03c71d03cec0f1d03cec0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell393 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell391 cell392

private theorem cell394 : Box.Closed ⟨⟨1024,1088⟩,⟨(-448),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell390 cell393

private theorem cell395 : Box.Closed ⟨⟨1024,1088⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell387 cell394

private theorem cell396 : Box.Closed ⟨⟨1088,1152⟩,⟨(-512),(-448)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c740f3b03c75eec0f1eec0f1e7bb7bcec0f3b03c01e780eccf3bf0000cf00efceccf00300ecc300ecdf3bf00efcec0340f0dec03bbf3bf3b000000d7c035d3bf3bf00d3cefc000d3cbaebbb03cb80f3bf3bf3bf0000eb3cec0000b7cefcb2cb3bb7c03bf3bf3b00002ef2defceee03cb80f00ec0f3bf2d03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell397 : Box.Closed ⟨⟨1088,1152⟩,⟨(-512),(-448)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25efc000026f3bf009bcee5980f3b03c03bf3b025924efcee4f2503c03b03cee45bc03bf00efc026f0099cefcee6f1c03cec0f1c03c71dec0f1d03cec0f3b03cec0f3b580ed5015f3bf00ec054053bf14ec053bf3b03c500500f3b03c500dbbf36ec0f3bf3bf00036db6efc036036d7bf3bf3bf00035f00d7cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell398 : Box.Closed ⟨⟨1088,1152⟩,⟨(-512),(-448)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell396 cell397

private theorem cell399 : Box.Closed ⟨⟨1088,1152⟩,⟨(-448),(-384)⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1d03c740f3b03c740f007bc7bb7bcec0f007bc7bb7bcec0f3b03c01e780eccf3bf0000cf00efceccf0000cf00ecc300ecdf3bf00efcec034000d3bcecef3bf3bf3b000000d7c034f3bf34efc000d34d3403cefcefcbae03cb80f3bf3bf3bf0000eb3cec0000b7cefcb2cb3ceecb40efc03bf3bf3b000b6defceee03cbad03cec0f00ec0f3bf2d03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell400 : Box.Closed ⟨⟨1088,1152⟩,⟨(-448),(-384)⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x25efc00000097c9bbf3bf009bcee597b03c03bf3b00097b93cee493c93bf2503c03b03cee45bc03bf00efc026f009bcee6f0073c73b73c73b03cec0f1c700f1d03cec0f3b03cec0f3b59657c03bf00ed5f00ec054053bf14ec0500f3bf3b03c500500f3b03c500dbbf36ec0f3bf3bf00036db603cefc036db603cefc035f3bf3bf00035f00d7cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell401 : Box.Closed ⟨⟨1088,1152⟩,⟨(-448),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell399 cell400

private theorem cell402 : Box.Closed ⟨⟨1088,1152⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell398 cell401

private theorem cell403 : Box.Closed ⟨⟨1024,1152⟩,⟨(-512),(-384)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell395 cell402

private theorem cell404 : Box.Closed ⟨⟨1024,1152⟩,⟨(-384),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell405 : Box.Closed ⟨⟨1024,1152⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell403 cell404

private theorem cell406 : Box.Closed ⟨⟨1152,1280⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x80eb903a) (rest:=0) (by decide +kernel)

private theorem cell407 : Box.Closed ⟨⟨1024,1280⟩,⟨(-512),(-256)⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell405 cell406

private theorem cell408 : Box.Closed ⟨⟨1024,1280⟩,⟨(-256),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell409 : Box.Closed ⟨⟨1024,1280⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell407 cell408

private theorem cell410 : Box.Closed ⟨⟨1280,1536⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell411 : Box.Closed ⟨⟨1024,1536⟩,⟨(-512),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell409 cell410

private theorem cell412 : Box.Closed ⟨⟨1024,1536⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell384 cell411

private theorem cell413 : Box.Closed ⟨⟨1536,2048⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell414 : Box.Closed ⟨⟨1024,2048⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell412 cell413

private theorem cell415 : Box.Closed ⟨⟨1024,2048⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell367 cell414

private theorem cell416 : Box.Closed ⟨⟨0,2048⟩,⟨(-2048),0⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell366 cell415

private theorem cell417 : Box.Closed ⟨⟨0,512⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3103139eb90c20c1eb90ba079e8307a0c1e84e41eb907ae7a) (rest:=0) (by decide +kernel)

private theorem cell418 : Box.Closed ⟨⟨512,768⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30ba) (rest:=0) (by decide +kernel)

private theorem cell419 : Box.Closed ⟨⟨768,1024⟩,⟨0,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell420 : Box.Closed ⟨⟨768,896⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30ba) (rest:=0) (by decide +kernel)

private theorem cell421 : Box.Closed ⟨⟨896,1024⟩,⟨256,384⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell422 : Box.Closed ⟨⟨896,960⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x30ba) (rest:=0) (by decide +kernel)

private theorem cell423 : Box.Closed ⟨⟨960,1024⟩,⟨384,448⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell424 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xbbc02e02ef3bf3bf00000b830bae40f2d0c2eb903cefcb6d03cb40f3bf3bf2db40f2d03cefcefcefc00034034d34d3ba0c2eb9f3bf3bf3b3bcecf02d3ed0c2eb9f3bf0f3c0f00efcec0f0f03c03b03cefc00f3bbf0eecf03b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell425 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x26980f3b03c9c30bae40f27ec0f27ec0f3b03c9e7027f3b9fcec0f009fc00077c01df3bf3b01defcec0f3b03c01d740eddf3bf0000077c01d740efa0c2eb9f3bf00efcec001d0c2eb903cec0f0077c03b7ba0c2eb97bc01ef3b7bcec0f3bf0001ef00edef00efcec0780f1e79e79e7bbe9ee7cefc03b7df0c2eb97fc03b7c0efcefcec001f7fcec07cdf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell426 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell424 cell425

private theorem cell427 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x15dfc03bdf7f00efc03b037ec0df70c2eb9f3bf37ec0db6dbbeb6e76f36ef6f3bf00dbcefc03b03603603cefcec0f00db603cd80d40f3bdba0c2eb9f3bf000350c2eb9f00efcefc03b035035efa0c2eb903cd40f3b03cec0f35035efcd7b03cefcefc000d40ef503cd40f3b03cbc0f3bf00bef03cbfbf2fefcefc000bc0bc0bc30bae7cefcefc000bbcbbbf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell428 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5fbf3b5965fb03cefcefc000017f3bf000005fced7f250c2eb95fc97b03cefced7f3b5955ba0c2eb957c57b57c03b57c03bf00efc025f0097cee5f0097c025f3b97c0250c2eb9f009830bae7cec0f3b03cec0f2603c9bb03c980f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell429 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell427 cell428

private theorem cell430 : Box.Closed ⟨⟨960,1024⟩,⟨448,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell426 cell429

private theorem cell431 : Box.Closed ⟨⟨960,1024⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell423 cell430

private theorem cell432 : Box.Closed ⟨⟨896,1024⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell422 cell431

private theorem cell433 : Box.Closed ⟨⟨896,1024⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell421 cell432

private theorem cell434 : Box.Closed ⟨⟨768,1024⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell420 cell433

private theorem cell435 : Box.Closed ⟨⟨768,1024⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell419 cell434

private theorem cell436 : Box.Closed ⟨⟨512,1024⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell418 cell435

private theorem cell437 : Box.Closed ⟨⟨512,768⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell438 : Box.Closed ⟨⟨768,896⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell439 : Box.Closed ⟨⟨896,960⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell440 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xbbc02e02ebae0f9f3bf3bf3bf00000b40f2d03cefcb6d03cb40f3bf3bf2db40f2db40f3b03cefcefcefc00d38e380ecef3b3bcefcec000ff3b3c0f0f03c03b03cefc38f03b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell441 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2603c9a7ec0f27ec0f3b03c9e7ec0f009fc02701d0f9f3bf3b01defcec0f3b03c01d75df3bf0001d01df3bf00efcec0740f1d740efa0f975ee83e7c01e0f9f3b7bcec0f3bf0001ef00edef00efcec0780f1e03b01fec0f1f0f97fc03b7fcefcec07c07cdf3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell442 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell440 cell441

private theorem cell443 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x15dfc03bdfc03bdc0df70f9f3bf00dc0efcec0dbbf00dbcefc03b03603603cefcec0f00db60f903cd76e83e75035efa0f9f3bf00d7cefc03b03503cd7b03cec0f35d7cd7b03cefcefc000d40ef50f903cbfb03cbc0f3bf00befefcefc000bc0beeefcefc02ef3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell444 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5fbf3b5bcefc000017f3bf005fced703c03bf3b596016efc5bbf16ed5f00efc00097c97bf0097cee5f0097c025f3b97c025f0097cec0f3b03cec0f260f99bc9bb03c9bb03c980f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell445 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell443 cell444

private theorem cell446 : Box.Closed ⟨⟨960,1024⟩,⟨512,576⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell442 cell445

private theorem cell447 : Box.Closed ⟨⟨960,1024⟩,⟨576,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell448 : Box.Closed ⟨⟨960,1024⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell446 cell447

private theorem cell449 : Box.Closed ⟨⟨896,1024⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell439 cell448

private theorem cell450 : Box.Closed ⟨⟨896,1024⟩,⟨640,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xfa0f9) (rest:=0) (by decide +kernel)

private theorem cell451 : Box.Closed ⟨⟨896,1024⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell449 cell450

private theorem cell452 : Box.Closed ⟨⟨768,1024⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell438 cell451

private theorem cell453 : Box.Closed ⟨⟨768,1024⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3e7a003e43eb9) (rest:=0) (by decide +kernel)

private theorem cell454 : Box.Closed ⟨⟨768,1024⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell452 cell453

private theorem cell455 : Box.Closed ⟨⟨512,1024⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell437 cell454

private theorem cell456 : Box.Closed ⟨⟨512,1024⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell436 cell455

private theorem cell457 : Box.Closed ⟨⟨0,1024⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell417 cell456

private theorem cell458 : Box.Closed ⟨⟨0,128⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x13a004eb913a) (rest:=0) (by decide +kernel)

private theorem cell459 : Box.Closed ⟨⟨128,192⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x4) (rest:=0) (by decide +kernel)

private theorem cell460 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x3fc3fbf0000ff0e3ce3c4e7cec0f0e03c380f3b03cefcefcefc00001e01e0fa1397fcefcedff3b0000000007fb0fa139f3bf3bf1f7df7c0ec3e84e7c03bf00efcefcec000e820383e84e7c800f3bf3bf3b38e380efcec0f0e380f3b03c03b03cefc820803e84e600fa139f3b800efcee003b03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell461 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c60063cec0f00984e7c026139f3b9bcec0f009bc026026f3bf3b9bcec0f3b03c026983e84e66f3b03c0269fb0fa139f00ee703c9fbf3bf00027f00efcec09fbf009c0ee79e79e70fa139f3bf3bf00efcec0000a03e84e40f3b03cec0f2803b0fa139a3c03ba3c03ba2803ba00efcefcec0028a03e84e5e139f3b7bcedef3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell462 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell460 cell461

private theorem cell463 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x36db6139c03e84e7cc3bf00efc03b030ec0c3bf30ec0c00c00c3b0fa139f3bf3bf00000c03e84e7c03bf00efcefc03b02f0fa139bfcbfbbfcbfb02fefcec0f2f03b02f03cec0f2f02ff3b02fbbb0fa13903cefc02eb83e84e7cbbbf3b03cefcefc000bae03cbbb03cb80f3bf00bae13903cb84e40f3bf00400f10efcefcefc010f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell464 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xe3bf3b038ef80fa139e03e84e7ce3bf38efcefc0000005bc5bbf3bf00016ed6f16efcec0e3c583e84e78f3be3c5bb03c03bf3b000037ec3e84e77f3bdfcef7f3703b0fa13903c03b03c03b03cef7df60fa139f00ef6f00efc03bf00efc0005bc016f3bf005c4e56f17efced6f1703cec0f175c0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell465 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell463 cell464

private theorem cell466 : Box.Closed ⟨⟨192,256⟩,⟨1024,1088⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell462 cell465

private theorem cell467 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x3fc3fbf0000ff0e3ceec0f0e03cefcefcefc00001e01e7fcefcedff3b0000007fbf3bf1f7df03bf00efcefcec002082083bf3bf3b380f0e03c03b03cefc820820f3b800efcee003c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell468 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c60063c026f3b9bcec0f009bc026f3b9bcec0f3b03c02603c026f00ee603c9fbf3bf00027f00efcec09fbf009e79e7f3bf00efcec0000a3b03cec0f28a04eb9a3c03ba3c03ba28a3cefcec001ea1ef3b7bcedef3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell469 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell467 cell468

private theorem cell470 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x36db0c3cc3bf00efc03bc30f30ec0c00c30c04eb9f3bf3bf0003003bf00efcefc03b02fbfcbfbbfcec0f2f03b02f03cec0f2f02ef3b02e03cefc02ef3b03cefcefc000bae03cb80f3bf00bae03c400f3bf10efcefc010f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell471 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38f3b038ef8e3ce3bf38efcefc000016f3bf005bcef8e3be3ce3b03c03bf3b000dfbdfcef7f3703b03c03b03cef7df6f00ef6f00efc03bf00efc016f00597efced6f1703cec0f175c0f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell472 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell470 cell471

private theorem cell473 : Box.Closed ⟨⟨192,256⟩,⟨1088,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell469 cell472

private theorem cell474 : Box.Closed ⟨⟨192,256⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell466 cell473

private theorem cell475 : Box.Closed ⟨⟨128,256⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell459 cell474

private theorem cell476 : Box.Closed ⟨⟨128,192⟩,⟨1152,1216⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c63b03c600f009bc026f3b9bcec0f3b03c026980ee6f3bf000009fc9fbf00efcec09c0f3bf009e7f00efcec002703cec0f27a3c03ba3c03ba3cec00287bcedef3bf3bf3b00000ff003fcefc0003ce3fcefc38e03c380f3bf3bf3bf0001e00079ff3b7fcefcec001fefc7fbf3b020ece03c3a003cec0f00ec0f3bf2081f83cee0f3b800efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell477 : Box.Closed ⟨⟨128,192⟩,⟨1152,1216⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xe3be38dfce3bf38efcefc000000e3c5bbf3bf005bcef803bf3bdf703b03cef7df6f00efc03bdbc03bf00efc016f005bced6f175bc5fb03cec0f1703c5c0f3b03cec0f3bdb0c3c03bf00ef0030030bfcefcefc000bfc03bf3bf00ec0beff3b03c02ff00ec0bef03cec0f3b03cb80bbbf2eec0f3bf3bf0002eb80f2e03cefc010f3bf0040043cefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell478 : Box.Closed ⟨⟨128,192⟩,⟨1152,1216⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell476 cell477

private theorem cell479 : Box.Closed ⟨⟨128,192⟩,⟨1216,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell480 : Box.Closed ⟨⟨128,192⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell478 cell479

private theorem cell481 : Box.Closed ⟨⟨192,256⟩,⟨1152,1216⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c618026f3b9bcec0f009bc026f3b9bcec0f3b03c026980ee69fbf3bf00027f00efcec09c0f3bf009e7f00efcec0028ec0f2803ba3cec00287bcedef3bf3bf3b00000ff003fcefc0003fc38e03c380f3bf3bf3bf000007bb01fefcec000001fefcefc7df03bf3bf3b000820efcece03c380f00ec0f3bf20820f3b800f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell482 : Box.Closed ⟨⟨192,256⟩,⟨1152,1216⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38f3be38f38efcefc000016f3bf005bcef8e3b03c03bf3b037ef7f3703b03c03b03cef703bd80efc03bf00efc016f005bced6f1703cec0f1703c5c0f3b03cec0f3bdb6c3c03bf00ef0030efc03003bf3bf00ec0beff3b03c02ff00ec0bc0f3b03cbeeec0bbbf2eec0f3bf3bf0002eb80f2e03cefc02eb80f10efc43bf3bf0043cefcefc) (rest:=0) (by decide +kernel)

private theorem cell483 : Box.Closed ⟨⟨192,256⟩,⟨1152,1216⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell481 cell482

private theorem cell484 : Box.Closed ⟨⟨192,256⟩,⟨1216,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell485 : Box.Closed ⟨⟨192,256⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell483 cell484

private theorem cell486 : Box.Closed ⟨⟨128,256⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell480 cell485

private theorem cell487 : Box.Closed ⟨⟨128,256⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell475 cell486

private theorem cell488 : Box.Closed ⟨⟨0,256⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell458 cell487

private theorem cell489 : Box.Closed ⟨⟨0,256⟩,⟨1280,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell490 : Box.Closed ⟨⟨0,256⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell488 cell489

private theorem cell491 : Box.Closed ⟨⟨256,320⟩,⟨1024,1088⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell492 : Box.Closed ⟨⟨256,320⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c626ec0f269bb9bcec0f009bc026f3b9bcec0f3b03c02603c027f00ee7f3bf00027f00efcec09fbf009c0ee79e79e89e7a3beb9f3bf3bf00efcec0028ec0f2803ba3c03ba28a00efcefcec079ef3bf3bf3b0000103fbf0fefc0003fc38f380f3bf3bf3bf000007807fbf3b7fcec000083cefc7df7e082003beb9f00efc03bf3bf3b0003a03a003cefcefcece03c380f00ec0f3bf20820f3b800f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell493 : Box.Closed ⟨⟨256,320⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38f3be38f38efcefc000016f3bf005bcec0e3c5bbe3c5bb03c03bf3b000e38038efae77f3bdfcef7f3803c03b03cef7dc0ef6f00efc03bf00efc016f17ed6f1703cec0f175d8ec0f3b03cec0f3bdb6f00ec0c3bc3cc3b030030efcefc03003bf3bf00ec0c2fc2fefae6ff2feeff2fec0bfbf3b03cbc0ec0bc0f3b03cbc0bc0f3bf00bbcec0f3bf3bf0002eb80f2e03cefc02ebaeefc02e43bf3bf3bf0043cefcefc) (rest:=0) (by decide +kernel)

private theorem cell494 : Box.Closed ⟨⟨256,320⟩,⟨1088,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell492 cell493

private theorem cell495 : Box.Closed ⟨⟨256,320⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell491 cell494

private theorem cell496 : Box.Closed ⟨⟨320,384⟩,⟨1024,1088⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell497 : Box.Closed ⟨⟨320,384⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c9a6ec0f26026f3b9bcec0f3b03c0269a6f3b03c9e7f3bf009c0efcec09c0f3bf009c0ee703c9c0ee89f903ca280fae68f3bf3bf00efcec0a2803ba2803b780efcefcec079ef3bf3bf3b0000103fbf003fcefc00f38f3ceec0f3bf3bf3bf0000079ff3b7fcec000083cefc7df820f00efc03bf3bf3b0003a03bcefcece03c380ec0f3bf20800ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell498 : Box.Closed ⟨⟨320,384⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xe3bf3be3cefc0005bbf005bced6e3c5bb03c03bf3b000e38f3bdfcef7f3803c03b03cef7df6f00efc03bf00efc0165fbf17ed6f17ec0f1703c5d8ec0f3b03cec0f3bdb6f00ec0c3b030efcc3b030efcc3bf00ec0c30c03eb9f00c2fe7cec0bfbf00bfcec0bfbf3b03c02ff00ec0bfb03cbeff00baef2eefcec0f3bf3bf0002eb80f2eefc02ebbbf3bf0043cefcefc) (rest:=0) (by decide +kernel)

private theorem cell499 : Box.Closed ⟨⟨320,384⟩,⟨1088,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell497 cell498

private theorem cell500 : Box.Closed ⟨⟨320,384⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell496 cell499

private theorem cell501 : Box.Closed ⟨⟨256,384⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell495 cell500

private theorem cell502 : Box.Closed ⟨⟨256,320⟩,⟨1152,1216⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1803c626ec0f26026f3b9bcec0f3b03c026980ee7f3bf009c0efcec09c0f3bf009e79e79e8f3bf3bf00efcec0a2803ba28a3cefcec001eedef3bf3bf3b0000103fbf003fcefc0003fc38e03c380f3bf3bf3bf000007807bbf3b7fcec000083cefc7df7e0f00efc03bf3bf3b0003a03a0efcefcece03c380ec0f3bf20800f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell503 : Box.Closed ⟨⟨256,320⟩,⟨1152,1216⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x38f3be3cefc0005bbf005bcef85bbe3c5bb03c03bf3b000e37f3bdfcef7f3803c03b03cef7d80ef6f00efc03bf00efc016f005bced6f1703cec0f1703c5d8ec0f3b03cec0f3bdb603bf00ef0c3cc3b030efcc3bf00ec0c2ff2feeff2feeff3b03c02ff00ec0bfb03cbc0bbbf2eec0f3bf3bf0002eb80f2eefc02e43bf3bf0043cefcefc) (rest:=0) (by decide +kernel)

private theorem cell504 : Box.Closed ⟨⟨256,320⟩,⟨1152,1216⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell502 cell503

private theorem cell505 : Box.Closed ⟨⟨256,320⟩,⟨1216,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell506 : Box.Closed ⟨⟨256,320⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell504 cell505

private theorem cell507 : Box.Closed ⟨⟨320,384⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell508 : Box.Closed ⟨⟨256,384⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell506 cell507

private theorem cell509 : Box.Closed ⟨⟨256,384⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell501 cell508

private theorem cell510 : Box.Closed ⟨⟨384,448⟩,⟨1024,1088⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell511 : Box.Closed ⟨⟨384,448⟩,⟨1088,1152⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x1862603cec0f3b03c9a69bb9bcec0f3b03c0269fb03c9fbf009fcec09c0f3bf009c0ee703c0039f9f00ee8f3bf00efcec0a2803ba00f287bc03b7bcefcec07bbf3bf3b0004003fcefc00f00eecff3bf3bf0000001fedff3b7fcec083c7c083c7c37f9f3b800efc03bf3bf3b0003bcece03c380ec0f3bf2083b80ef00ec0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell512 : Box.Closed ⟨⟨384,448⟩,⟨1088,1152⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5b8f3bf3be38efcefc0005bbf005bced603c03bf3b000e3b0f7e77f3803cefcef7f3803cef7df703bf00efc03bf00efc5d603bf17ec0f1703c63b03cec0f3bd80ef6030c3cefc030f3b030efcc3bf00ec0c000efe40f3bf00bfcec0bfbf3b03c02ff00eef03cbc0beeefcec0f3bf3bf0002ebaeefcbbbf00000bbc43bf10efcefcefc) (rest:=0) (by decide +kernel)

private theorem cell513 : Box.Closed ⟨⟨384,448⟩,⟨1088,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell511 cell512

private theorem cell514 : Box.Closed ⟨⟨384,448⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell510 cell513

private theorem cell515 : Box.Closed ⟨⟨448,512⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x3) (rest:=0) (by decide +kernel)

private theorem cell516 : Box.Closed ⟨⟨384,512⟩,⟨1024,1152⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell514 cell515

private theorem cell517 : Box.Closed ⟨⟨384,512⟩,⟨1152,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell518 : Box.Closed ⟨⟨384,512⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell516 cell517

private theorem cell519 : Box.Closed ⟨⟨256,512⟩,⟨1024,1280⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell509 cell518

private theorem cell520 : Box.Closed ⟨⟨256,512⟩,⟨1280,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell521 : Box.Closed ⟨⟨256,512⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell519 cell520

private theorem cell522 : Box.Closed ⟨⟨0,512⟩,⟨1024,1536⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell490 cell521

private theorem cell523 : Box.Closed ⟨⟨0,512⟩,⟨1536,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell524 : Box.Closed ⟨⟨0,512⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell522 cell523

private theorem cell525 : Box.Closed ⟨⟨512,1024⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xfae7ae7a) (rest:=0) (by decide +kernel)

private theorem cell526 : Box.Closed ⟨⟨0,1024⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell524 cell525

private theorem cell527 : Box.Closed ⟨⟨0,1024⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell457 cell526

private theorem cell528 : Box.Closed ⟨⟨1024,1280⟩,⟨0,256⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell529 : Box.Closed ⟨⟨1024,1152⟩,⟨256,384⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2) (rest:=0) (by decide +kernel)

private theorem cell530 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨(-1024),0⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0xbbc02ef3bf00000bae03cefcb6d0b903cb40f3bf3bf2db40f2d03cefcefcefc00034034ef3bf3b3bcecfb4fb40efcec0f0f03c03b03cefc00ff0e380f00efcecf03c03bf00ec0f3bf3b) (rest:=0) (by decide +kernel)

private theorem cell531 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨(-1024),0⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2603c980f27ec0f3b03c9e7ec0f3b03c9e7027f3b9fcec0f0077c01df3b77cec0f3b03c01d75df3bf0000077c01d0ba0b9f3bf00efcec001eec0f1eec0f3bf00780edef00efcec001e03cec0f1e780f1f0b97fcefc03b7df03b7fcefcec001f7fcecdf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell532 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell530 cell531

private theorem cell533 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨0,1024⟩,⟨(-1024),0⟩⟩ :=
  verify_sound (n:=32) (code:=0x15df7f00efc03bdc0dfbf37ec0df70b9f00dbcef6f3bf00036f00efcefc03b036036efcec0f00d80d80efcefc03b0350ba0b903cd40f3b03cec0f35d7cd7b03cefcefc000d7503cd40f3bf00bef03cbfbf2fefcefc000befefc000bc0bbcefc02ef3bf3bf3bf3b) (rest:=0) (by decide +kernel)

private theorem cell534 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨0,1024⟩,⟨0,1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x17f3b0005bced6f1703cefcefc000017f3bf00025ed7f25efced7f3b59657c03b57c03bf00efc025f0097cee5f0097c0250b9f3b97c026f26ec0f3b03cec0f2603c980f3b03cec0f3b) (rest:=0) (by decide +kernel)

private theorem cell535 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .s cell533 cell534

private theorem cell536 : Box.Closed ⟨⟨1024,1088⟩,⟨384,448⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell532 cell535

private theorem cell537 : Box.Closed ⟨⟨1024,1088⟩,⟨448,512⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x269a603cec0f3b03c9c0f3b03c9e7ec0f009fc01d77bf3b77cec0f3b03c01df0001d01df3bf00efcec001d03cec0f1e7bb7bcec0f3bf00780edef00efcec001eec0f1e79e7fcefc03b7df03b7fcefcec07cdf3bf3bf3b00002ef00bbcefc00002e03cb40f3bf2db40f2defcefcb6d03cb40f3bf3bf3bf0000decef3b3c0b7c3cf03c03bf3b03c3c0f00ec0f3bf003fc3bb3c0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell538 : Box.Closed ⟨⟨1024,1088⟩,⟨448,512⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x17f3b59703cefcefc000017f3bf000005fced7f2503cefced7f3b59503bf00efc025f0097cee5f25025f3b97c025f009bcec0f3b03cec0f2603c980f3b03cec0f3b577f00ef7037efcdfb037dbcdbbdbcefc03603bf3bf00ec0d80dbbf3b03c036db6efc000d7c03bf3bf00ec0d40f35ec0f3b03cd40f3bf3bf00035d75ec0f2f03cefc02fbfbf3bf0002ff00000bbcbbbf2eefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell539 : Box.Closed ⟨⟨1024,1088⟩,⟨448,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell537 cell538

private theorem cell540 : Box.Closed ⟨⟨1024,1088⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell536 cell539

private theorem cell541 : Box.Closed ⟨⟨1088,1152⟩,⟨384,448⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2603c9c0f3b03c9fb03c9e7027f3b9fcec0f0077c01df3b77cec0f3b03c01df0001d01ef3bf00efcec079eec0f3bf00780efcec001e03cec0f1e03b7fc03b7df7fcefcec07cdf3bf3bf3b00002ef00bbcefc00002ef2db40f2defcefcb6d03cb7bf3bf3bf0000d00d3bcefcecef3b3ed3ed03bf3b03c3c0f00ec0f3bf0f38f03bf3b3c0f00efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell542 : Box.Closed ⟨⟨1088,1152⟩,⟨384,448⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x17f3b017ed6f17efcefc000017f3bf00025ed7f25efced7f3b59657c03b57c03bf00efc94097cee5f25025f3b97c980f3b03cec0f2603c980f3b03cec0f3b577f00ef7dfcdfb037036efcefc000dbc03bf3bf00ec0dbb03c036dbbf00ec0d80f35ec0f3b03cd40f3bf3bf00035d40f3503cefc02fbc0f2fefcbfbf3bf00bc002ff00bbcefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell543 : Box.Closed ⟨⟨1088,1152⟩,⟨384,448⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell541 cell542

private theorem cell544 : Box.Closed ⟨⟨1088,1152⟩,⟨448,512⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2603c9a7ec0f3b03c9c0f3b03c9c0f0075defc01df3b77cec0f3b03c01df0001df00efcec0740f1eec0f3bf00780efcec001e03cec0f1e7dfefc03b7fcec07cdf3bf3bf3b00002ef00bbcefc00002eb7bf2defcb6db7bf3bf3bf0000dec03bc3bbf3b3ed3ed03bf3b03c3c0f00ec0f3bf0f38f03bf3b3c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell545 : Box.Closed ⟨⟨1088,1152⟩,⟨448,512⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5fb017ed6f17efcefc000017f3bf00025ed7f25efced7f3b59603ced503bf00efc965ee5f25966ec0f3b03cec0f2603c980f3b03cec0f3b577f00ef7037dfbdbcefc000dbc03bf3bf00ec0dbb03c036035f3bf00ec0d40f3b03cd40f3bf3bf00035d40f35bfb03cefc02ff3bf0002ff0002fbbbf00bbcefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell546 : Box.Closed ⟨⟨1088,1152⟩,⟨448,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell544 cell545

private theorem cell547 : Box.Closed ⟨⟨1088,1152⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell543 cell546

private theorem cell548 : Box.Closed ⟨⟨1024,1152⟩,⟨384,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell540 cell547

private theorem cell549 : Box.Closed ⟨⟨1024,1152⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell529 cell548

private theorem cell550 : Box.Closed ⟨⟨1152,1280⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0xbae7a) (rest:=0) (by decide +kernel)

private theorem cell551 : Box.Closed ⟨⟨1024,1280⟩,⟨256,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell549 cell550

private theorem cell552 : Box.Closed ⟨⟨1024,1280⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell528 cell551

private theorem cell553 : Box.Closed ⟨⟨1280,1536⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell554 : Box.Closed ⟨⟨1024,1536⟩,⟨0,512⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell552 cell553

private theorem cell555 : Box.Closed ⟨⟨1024,1088⟩,⟨512,576⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x26980f3b03c9c0f27ec0f3b03c9c09fc02701df3bf3b01defcec0f3b03c01df0001df00efcec0740f1d77c01ef3b7bcec0f3bf0001ef00edef00efcec0780f1e03b7df7fcefcec07c07cdf3bf3bf3bf3b00002ef00b80bbcefcefc00002d03cb7bf2defcb6db40f3bf3bf3bf003403bc3bbf3b3c0b4fefc3fb03c3c0ec0f3bf0e3c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell556 : Box.Closed ⟨⟨1024,1088⟩,⟨512,576⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5fb5bcefc0005fbf005d797b03cefced7f3b59603ced5f00efc025f25ee5f2594097cec0f3b03cec0f2603c9bb03c980f3b03cec0f3b577f00ef7f00ef7dfcdfb036efc036f3bf00ec0d80d80f3bf3b03c036d80f35d7cefc035f3bf00ec0d40f3b03cd40f3bf3bf0003503bd40f2fec0f2f03cefcbfbf0002f02ff3bf0002ef2eefcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell557 : Box.Closed ⟨⟨1024,1088⟩,⟨512,576⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell555 cell556

private theorem cell558 : Box.Closed ⟨⟨1024,1088⟩,⟨576,640⟩,⟨(-1024),0⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x2603c9a7ec0f27ec0f3b03c9e7027f3b01defcec0f3b03c01df0001df00efcec075d01df3b01eefcec0f3bf0001ef00edef00efcec0780f1e03b7dfefcec07c07fbf3bf3bf3b00002ef00b80badefcefcefc000b6defcb6db40f3bf3bf3bf003403bc38d3bcecef3bf3b0003fcecf03c3c0ec0f3bf0e3c0efc03b03cefcefc) (rest:=0) (by decide +kernel)

private theorem cell559 : Box.Closed ⟨⟨1024,1088⟩,⟨576,640⟩,⟨0,1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x5fb5bcefc0005fbf005fced703c03bf3b59657c5bbf1603ced5f00efc025f25ee5f2597b03cec0f259bb03c9bb03c980f3b03cec0f3bdc0ef7f00ef7dfb036efc036f3bf00ec0d80d80f3bf3b03c03603bd40f35efcd7bf00ec0d40f3b03cd40f3bf3bf0003503bbc0f2fefcbfbf0002f02fbbbf3bf00bbcefcefcefc) (rest:=0) (by decide +kernel)

private theorem cell560 : Box.Closed ⟨⟨1024,1088⟩,⟨576,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .c cell558 cell559

private theorem cell561 : Box.Closed ⟨⟨1024,1088⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell557 cell560

private theorem cell562 : Box.Closed ⟨⟨1088,1152⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell563 : Box.Closed ⟨⟨1024,1152⟩,⟨512,640⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell561 cell562

private theorem cell564 : Box.Closed ⟨⟨1024,1152⟩,⟨640,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell565 : Box.Closed ⟨⟨1024,1152⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell563 cell564

private theorem cell566 : Box.Closed ⟨⟨1152,1280⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell567 : Box.Closed ⟨⟨1024,1280⟩,⟨512,768⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell565 cell566

private theorem cell568 : Box.Closed ⟨⟨1024,1280⟩,⟨768,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell569 : Box.Closed ⟨⟨1024,1280⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell567 cell568

private theorem cell570 : Box.Closed ⟨⟨1280,1536⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell571 : Box.Closed ⟨⟨1024,1536⟩,⟨512,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell569 cell570

private theorem cell572 : Box.Closed ⟨⟨1024,1536⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell554 cell571

private theorem cell573 : Box.Closed ⟨⟨1536,2048⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell574 : Box.Closed ⟨⟨1024,2048⟩,⟨0,1024⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell572 cell573

private theorem cell575 : Box.Closed ⟨⟨1024,2048⟩,⟨1024,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  verify_sound (n:=32) (code:=0x0) (rest:=0) (by decide +kernel)

private theorem cell576 : Box.Closed ⟨⟨1024,2048⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell574 cell575

private theorem cell577 : Box.Closed ⟨⟨0,2048⟩,⟨0,2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell527 cell576

private theorem cell578 : Box.Closed ⟨⟨0,2048⟩,⟨(-2048),2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .y cell416 cell577

private theorem cell579 : Box.Closed ⟨⟨(-2048),2048⟩,⟨(-2048),2048⟩,⟨(-1024),1024⟩,⟨(-1024),1024⟩⟩ :=
  cut_sound _ .x cell255 cell578

theorem coverage (x y c s : ℝ) (hz : 20*(x^2+y^2) ≤ 27*1024^2)
    (hu : c^2+s^2=1024^2) : Covered x y c s := by
  apply cell579 x y c s <;> first | assumption | (constructor <;> norm_num <;> nlinarith [sq_nonneg x,sq_nonneg y,sq_nonneg c,sq_nonneg s])

open scoped EuclideanGeometry Congruent

noncomputable def K (i : Fin 8) : ℝ² := !₂[(X i : ℝ)/1024, (Y i : ℝ)/1024]

lemma K_inj : Function.Injective K := by
  have hinj : ∀ i j : Fin 8, X i = X j → Y i = Y j → i = j := by decide
  intro i j h
  apply hinj
  · have h0 := congrArg (fun v : ℝ² => v 0) h
    simpa [K] using h0
  · have h1 := congrArg (fun v : ℝ² => v 1) h
    simpa [K] using h1

lemma frame (px py : Fin 8 → ℝ) (hx0 : px 0 = 0) (hy0 : py 0 = 0)
    (hd : ∀ i j, (px i-px j)^2+(py i-py j)^2 =
      ((X i:ℝ)-X j)^2+((Y i:ℝ)-Y j)^2) :
    ∃ c s e : ℝ, c^2+s^2=1 ∧ e^2=1 ∧
      ∀ i, c*px i+s*py i = X i ∧ e*(-s*px i+c*py i) = Y i := by
  have hn (i : Fin 8) : (px i)^2+(py i)^2 = (X i:ℝ)^2+(Y i:ℝ)^2 := by
    simpa [hx0,hy0,show X 0 = 0 by rfl,show Y 0 = 0 by rfl] using hd i 0
  have hg (i j : Fin 8) : px i*px j+py i*py j = (X i:ℝ)*X j+(Y i:ℝ)*Y j := by
    linear_combination (hn i + hn j - hd i j)/2
  let c := px 1 / 840
  let s := py 1 / 840
  have hu : c^2+s^2=1 := by
    have h := hn 1
    norm_num [X,Y] at h
    dsimp [c,s]
    linarith
  have ha (i : Fin 8) : c*px i+s*py i = X i := by
    have h := hg i 1
    rw [show X 1 = 840 by rfl,show Y 1 = 0 by rfl] at h
    norm_num at h
    dsimp [c,s]
    linear_combination h/840
  have hm (i j : Fin 8) :
      (-s*px i+c*py i)*(-s*px j+c*py j) = (Y i:ℝ)*Y j := by
    calc
      _ = (c^2+s^2)*(px i*px j+py i*py j) -
          (c*px i+s*py i)*(c*px j+s*py j) := by ring
      _ = _ := by rw [hu,hg,ha,ha]; ring
  obtain ⟨e,he,hs⟩ := OMA214.sign_lemma _ _ hm
  refine ⟨c,s,e,hu,he,fun i => ⟨ha i,?_⟩⟩
  rw [hs]
  linear_combination (Y i:ℝ)*he

lemma iso_norm {c s e : ℝ} (hu : c^2+s^2=1) (he : e^2=1) (a b : ℝ) :
    (c*a+s*b)^2+(e*(-s*a+c*b))^2 = a^2+b^2 := by
  rw [mul_pow,he,one_mul]
  linear_combination (a^2+b^2)*hu

lemma offsets (j : Fin 7) {e : ℝ} (he : e^2=1) :
    ∃ m n : ℤ, 4*(2*(m:ℝ)+n) = U j ∧ 7*(n:ℝ) = e*V j := by
  have h : ∀ t : Fin 7, ∃ m n : ℤ, 4*(2*m+n) = U t ∧ 7*n = V t := by
    intro t
    fin_cases t
    · exact ⟨0,0,by decide⟩
    · exact ⟨1,0,by decide⟩
    · exact ⟨-1,0,by decide⟩
    · exact ⟨0,1,by decide⟩
    · exact ⟨-1,1,by decide⟩
    · exact ⟨1,-1,by decide⟩
    · exact ⟨0,-1,by decide⟩
  obtain ⟨m,n,hm,hn⟩ := h j
  have hm' : 4*(2*(m:ℝ)+n) = U j := by exact_mod_cast hm
  have hn' : 7*(n:ℝ) = V j := by exact_mod_cast hn
  rcases (sq_eq_one_iff.mp he) with rfl|rfl
  · exact ⟨m,n,hm',by simpa using hn'⟩
  · refine ⟨m+n,-n,?_,?_⟩ <;> push_cast <;> linarith

set_option maxHeartbeats 1600000 in
lemma configuration_hits
    (certificate : ∀ x y c s : ℝ, 20*(x^2+y^2) ≤ 27*1024^2 →
      c^2+s^2=1024^2 → Covered x y c s)
    (p : Fin 8 → ℝ²) (hc : p ≅ K) : ∃ i, p i ∈ OMA214.S := by
  let px (i : Fin 8) : ℝ := 1024*(p i 0-p 0 0)
  let py (i : Fin 8) : ℝ := 1024*(p i 1-p 0 1)
  have hd (i j : Fin 8) :
      (px i-px j)^2+(py i-py j)^2 = ((X i:ℝ)-X j)^2+((Y i:ℝ)-Y j)^2 := by
    have h := congrArg (fun t : ℝ => t^2) ((congruent_iff_dist_eq.mp hc) i j)
    change dist (p i) (p j)^2 = dist (K i) (K j)^2 at h
    rw [OMA214.dist_sq,OMA214.dist_sq] at h
    simp [K] at h
    dsimp [px,py]
    linear_combination 1024^2*h
  obtain ⟨c,s,e,hu,he,ha⟩ := frame px py (by simp [px]) (by simp [py]) hd
  obtain ⟨a,b,hnear⟩ := OMA214.lattice_cover (p 0 0) (p 0 1)
  let dx := 1024*(2*(a:ℝ)+b-p 0 0)
  let dy := 1024*(7/4*(b:ℝ)-p 0 1)
  let x := c*dx+s*dy
  let y := e*(-s*dx+c*dy)
  have hz : 20*(x^2+y^2) ≤ 27*1024^2 := by
    dsimp only [x,y]
    rw [iso_norm hu he]
    dsimp [dx,dy]
    linarith
  have hcs : (1024*c)^2+(1024*(-e*s))^2=1024^2 := by
    simp only [mul_pow,neg_pow_two,he,one_mul]
    linarith
  obtain ⟨i,j,hij⟩ := certificate x y (1024*c) (1024*(-e*s)) hz hcs
  obtain ⟨m,n,hm,hn⟩ := offsets j he
  refine ⟨i,a+m,b+n,?_⟩
  let u := (U j:ℝ)
  let v := (V j:ℝ)
  let A := dx + 256*u - px i
  let B := dy + 256*e*v - py i
  have hx : 4*x+(U j:ℝ)*(1024*c)-(V j:ℝ)*(1024*(-e*s))-4*(X i:ℝ) = 4*(c*A+s*B) := by
    dsimp [x,A,B,u,v]
    linear_combination 4*(ha i).1
  have hy : 4*y+(V j:ℝ)*(1024*c)+(U j:ℝ)*(1024*(-e*s))-4*(Y i:ℝ) = 4*(e*(-s*A+c*B)) := by
    dsimp [y,A,B,u,v]
    linear_combination 4*(ha i).2 - 1024*c*(V j:ℝ)*he
  rw [hx,hy] at hij
  have hAB : A^2+B^2 < 512^2 := by
    have hi := iso_norm hu he A B
    linarith
  have hLx : A = 1024*((OMA214.L (a+m) (b+n)) 0-p i 0) := by
    simp [A,u,dx,px,OMA214.L]
    linarith
  have hLy : B = 1024*((OMA214.L (a+m) (b+n)) 1-p i 1) := by
    simp [B,v,dy,py,OMA214.L]
    linarith
  have hdist : dist (p i) (OMA214.L (a+m) (b+n))^2 < 1/4 := by
    rw [OMA214.dist_sq]
    rw [hLx,hLy] at hAB
    linarith
  nlinarith [dist_nonneg (x:=p i) (y:=OMA214.L (a+m) (b+n))]

end Eight

theorem OMA.solution : type_of% @Erdos214.erdos_214.variants.csizmadia_toth := by
  intro h
  obtain ⟨p, hred, hcongr⟩ := h OMA214.S OMA214.S_avoid Eight.K Eight.K_inj
  obtain ⟨i, hi⟩ := Eight.configuration_hits Eight.coverage p hcongr
  exact hred i hi
