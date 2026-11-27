import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Proof of H2 for OEIS A105751

Proves that `OeisA105751.a n ≠ 0` for all `n ≥ 4` via 2-adic valuation of 4- and 8-factor
Gaussian blocks.
-/

namespace H2Proof

/-- Lightweight Gaussian integers to avoid complex arithmetic. -/
structure GInt where
  re : ℤ
  im : ℤ

def GInt.one : GInt := ⟨1, 0⟩

def GInt.mul (z w : GInt) : GInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def GInt.scale (c : ℤ) (z : GInt) : GInt :=
  ⟨c * z.re, c * z.im⟩

def GInt.toComplex (z : GInt) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.I

lemma GInt.ext {z w : GInt} (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z
  cases w
  simp_all

lemma GInt.mul_assoc (x y z : GInt) : (x.mul y).mul z = x.mul (y.mul z) := by
  apply GInt.ext <;> simp [GInt.mul] <;> ring

lemma GInt.one_mul (z : GInt) : GInt.one.mul z = z := by
  apply GInt.ext <;> simp [GInt.one, GInt.mul]

lemma GInt.mul_one (z : GInt) : z.mul GInt.one = z := by
  apply GInt.ext <;> simp [GInt.one, GInt.mul]

lemma GInt.scale_mul_left (c : ℤ) (z w : GInt) : (z.scale c).mul w = (z.mul w).scale c := by
  apply GInt.ext <;> simp [GInt.scale, GInt.mul] <;> ring

lemma GInt.scale_mul_right (c : ℤ) (z w : GInt) : z.mul (w.scale c) = (z.mul w).scale c := by
  apply GInt.ext <;> simp [GInt.scale, GInt.mul] <;> ring

lemma GInt.scale_scale (c d : ℤ) (z : GInt) : (z.scale d).scale c = z.scale (c * d) := by
  apply GInt.ext <;> simp [GInt.scale] <;> ring

lemma GInt.toComplex_one : GInt.one.toComplex = 1 := by
  simp [GInt.one, GInt.toComplex]

lemma GInt.toComplex_mul (z w : GInt) : (z.mul w).toComplex = z.toComplex * w.toComplex := by
  simp only [GInt.mul, GInt.toComplex]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination -(z.im : ℂ) * (w.im : ℂ) * hI

lemma GInt.toComplex_im (z : GInt) : z.toComplex.im = (z.im : ℝ) := by
  simp [GInt.toComplex]

/-- Partial products `∏_{k < n} (1 + k * i)` as `GInt`. -/
def Zg : ℕ → GInt
  | 0 => GInt.one
  | n + 1 => (Zg n).mul ⟨1, (n : ℤ)⟩

lemma Zg_toComplex (n : ℕ) :
    (Zg n).toComplex = (Finset.range n).prod (fun k : ℕ => (1 : ℂ) + (k : ℂ) * Complex.I) := by
  induction n with
  | zero =>
    simp [Zg, GInt.toComplex_one]
  | succ n ih =>
    rw [Zg, GInt.toComplex_mul, ih, Finset.prod_range_succ]
    simp [GInt.toComplex]

lemma a_eq_Zg_im (n : ℕ) : OeisA105751.a n = (Zg (n + 1)).im := by
  unfold OeisA105751.a
  dsimp only
  rw [← Zg_toComplex (n + 1), GInt.toComplex_im]
  exact Int.floor_intCast _

/-- Gaussian integers of the form `re + 4 * im * i`. -/
structure Quad4 where
  re : ℤ
  im : ℤ

def Quad4.one : Quad4 := ⟨1, 0⟩

def Quad4.mul (z w : Quad4) : Quad4 :=
  ⟨z.re * w.re - 16 * z.im * w.im, z.re * w.im + z.im * w.re⟩

def Quad4.toGInt (z : Quad4) : GInt := ⟨z.re, 4 * z.im⟩

lemma Quad4.ext {z w : Quad4} (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z
  cases w
  simp_all

lemma Quad4.mul_assoc (x y z : Quad4) : (x.mul y).mul z = x.mul (y.mul z) := by
  apply Quad4.ext <;> simp [Quad4.mul] <;> ring

lemma Quad4.one_mul (z : Quad4) : Quad4.one.mul z = z := by
  apply Quad4.ext <;> simp [Quad4.one, Quad4.mul]

lemma Quad4.mul_one (z : Quad4) : z.mul Quad4.one = z := by
  apply Quad4.ext <;> simp [Quad4.one, Quad4.mul]

lemma Quad4.toGInt_one : Quad4.one.toGInt = GInt.one := by
  apply GInt.ext <;> simp [Quad4.one, Quad4.toGInt, GInt.one]

lemma Quad4.toGInt_mul (z w : Quad4) : (z.mul w).toGInt = z.toGInt.mul w.toGInt := by
  apply GInt.ext <;> simp [Quad4.mul, Quad4.toGInt, GInt.mul] <;> ring

/-- Contiguous product of `L` terms of a `Quad4` sequence starting at `s`. -/
def prodFrom (f : ℕ → Quad4) (s : ℕ) : ℕ → Quad4
  | 0 => Quad4.one
  | L + 1 => (prodFrom f s L).mul (f (s + L))

lemma prodFrom_one (f : ℕ → Quad4) (s : ℕ) : prodFrom f s 1 = f s := by
  simp [prodFrom, Quad4.one_mul]

lemma prodFrom_pair (f : ℕ → Quad4) (s m : ℕ) :
    prodFrom f s (2 * m) = prodFrom (fun u => (f (s + 2 * u)).mul (f (s + 2 * u + 1))) 0 m := by
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h1, prodFrom, prodFrom, ih, prodFrom]
    simp only [Nat.zero_add]
    rw [Quad4.mul_assoc]
    have h2 : s + (2 * m + 1) = s + 2 * m + 1 := by omega
    rw [h2]

/-- `ExactTwo e z` means `2 ^ e` is the exact power of `2` dividing `z`. -/
def ExactTwo (e : ℕ) (z : ℤ) : Prop :=
  ∃ u : ℤ, Odd u ∧ z = (2 : ℤ) ^ e * u

lemma exactTwo_ne_zero {e : ℕ} {z : ℤ} (h : ExactTwo e z) : z ≠ 0 := by
  rcases h with ⟨u, ⟨k, rfl⟩, rfl⟩
  have hp : (2 : ℤ) ^ e ≠ 0 := by positivity
  intro hz
  have hu : 2 * k + 1 = 0 := (mul_eq_zero.mp hz).resolve_left hp
  omega

lemma exactTwo_dvd {e : ℕ} {z : ℤ} (h : ExactTwo e z) : (2 : ℤ) ^ e ∣ z := by
  rcases h with ⟨u, _, rfl⟩
  exact dvd_mul_right _ _

lemma exactTwo_not_dvd_succ {e : ℕ} {z : ℤ} (h : ExactTwo e z) : ¬ ((2 : ℤ) ^ (e + 1) ∣ z) := by
  rcases h with ⟨u, ⟨k, rfl⟩, rfl⟩
  rintro ⟨c, hc⟩
  have hp : (2 : ℤ) ^ e ≠ 0 := by positivity
  have h1 : (2 : ℤ) ^ e * (2 * k + 1) = (2 : ℤ) ^ e * (2 * c) := by
    rw [hc, pow_succ]
    ring
  have h2 : 2 * k + 1 = 2 * c := mul_left_cancel₀ hp h1
  omega

lemma exactTwo_mul_odd {e : ℕ} {z w : ℤ} (hz : ExactTwo e z) (hw : Odd w) :
    ExactTwo e (z * w) := by
  rcases hz with ⟨u, hu, rfl⟩
  exact ⟨u * w, hu.mul hw, by ring⟩

lemma exactTwo_add_dvd_succ {e : ℕ} {x y : ℤ} (hx : ExactTwo e x) (hy : (2 : ℤ) ^ (e + 1) ∣ y) :
    ExactTwo e (x + y) := by
  rcases hx with ⟨u, ⟨k, rfl⟩, rfl⟩
  rcases hy with ⟨c, rfl⟩
  refine ⟨2 * (k + c) + 1, ⟨k + c, rfl⟩, ?_⟩
  rw [pow_succ]
  ring

lemma exactTwo_of_odd {e : ℕ} {z : ℤ} (h : ExactTwo e z) (ho : Odd z) : e = 0 := by
  rcases h with ⟨u, _, rfl⟩
  rcases ho with ⟨k, hk⟩
  cases e with
  | zero => rfl
  | succ e' =>
    have : (2 : ℤ) ^ (e' + 1) * u = 2 * ((2 : ℤ) ^ e' * u) := by rw [pow_succ]; ring
    omega

lemma exactTwo_two_mul {e : ℕ} {m : ℤ} (h : ExactTwo e (2 * m)) :
    ∃ e' : ℕ, e = e' + 1 ∧ ExactTwo e' m := by
  rcases h with ⟨u, hu, hm⟩
  cases e with
  | zero =>
    rcases hu with ⟨k, rfl⟩
    simp at hm
    omega
  | succ e' =>
    refine ⟨e', rfl, u, hu, ?_⟩
    have h1 : 2 * m = 2 * ((2 : ℤ) ^ e' * u) := by
      rw [hm, pow_succ]
      ring
    omega

lemma exists_exactTwo_nat (L : ℕ) (hL : 1 ≤ L) : ∃ e : ℕ, ExactTwo e (L : ℤ) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    by_cases hpar : L % 2 = 0
    · set m := L / 2
      have hm1 : 1 ≤ m := by omega
      have hmlt : m < L := by omega
      rcases ih m hmlt hm1 with ⟨e, u, hu, hm⟩
      refine ⟨e + 1, u, hu, ?_⟩
      have hLm : (L : ℤ) = 2 * (m : ℤ) := by omega
      rw [hLm, hm, pow_succ]
      ring
    · refine ⟨0, (L : ℤ), ⟨(L / 2 : ℕ), by omega⟩, by simp⟩

/-- Dyadic regularity invariant at level `k` for a `Quad4` sequence. -/
structure Good (k : ℕ) (f : ℕ → Quad4) : Prop where
  re_odd : ∀ u : ℕ, Odd (f u).re
  im_exact : ∀ u : ℕ, ExactTwo k (f u).im
  lip_re : ∀ u v : ℕ, (2 : ℤ) ^ (k + 2) * ((u : ℤ) - v) ∣ (f u).re - (f v).re
  lip_im : ∀ u v : ℕ, (2 : ℤ) ^ (k + 2) * ((u : ℤ) - v) ∣ (f u).im - (f v).im

lemma good_shift {k : ℕ} {f : ℕ → Quad4} (hf : Good k f) (s : ℕ) :
    Good k (fun u => f (s + u)) where
  re_odd u := hf.re_odd (s + u)
  im_exact u := hf.im_exact (s + u)
  lip_re u v := by
    have h := hf.lip_re (s + u) (s + v)
    have heq : ((s + u : ℕ) : ℤ) - ((s + v : ℕ) : ℤ) = (u : ℤ) - (v : ℤ) := by push_cast; ring
    rwa [heq] at h
  lip_im u v := by
    have h := hf.lip_im (s + u) (s + v)
    have heq : ((s + u : ℕ) : ℤ) - ((s + v : ℕ) : ℤ) = (u : ℤ) - (v : ℤ) := by push_cast; ring
    rwa [heq] at h

lemma good_pair {k : ℕ} {f : ℕ → Quad4} (hf : Good k f) :
    Good (k + 1) (fun u => (f (2 * u)).mul (f (2 * u + 1))) where
  re_odd u := by
    rcases hf.re_odd (2 * u) with ⟨a, ha⟩
    rcases hf.re_odd (2 * u + 1) with ⟨b, hb⟩
    refine ⟨2 * a * b + a + b - 8 * (f (2 * u)).im * (f (2 * u + 1)).im, ?_⟩
    simp only [Quad4.mul, ha, hb]
    ring
  im_exact u := by
    set x := f (2 * u)
    set y := f (2 * u + 1)
    have hdiff : ((2 * u + 1 : ℕ) : ℤ) - ((2 * u : ℕ) : ℤ) = 1 := by push_cast; ring
    have hre : (2 : ℤ) ^ (k + 2) ∣ y.re - x.re := by
      have h := hf.lip_re (2 * u + 1) (2 * u)
      rwa [hdiff, mul_one] at h
    have him : (2 : ℤ) ^ (k + 2) ∣ y.im - x.im := by
      have h := hf.lip_im (2 * u + 1) (2 * u)
      rwa [hdiff, mul_one] at h
    rcases hre with ⟨c1, hc1⟩
    rcases him with ⟨c2, hc2⟩
    have hsplit : (x.mul y).im = 2 * x.im * y.re + (x.re * (y.im - x.im) - x.im * (y.re - x.re)) := by
      simp [Quad4.mul]
      ring
    rw [hsplit]
    have hmain : ExactTwo (k + 1) (2 * x.im * y.re) := by
      rcases hf.im_exact (2 * u) with ⟨u0, hu0, hx0⟩
      refine ⟨u0 * y.re, hu0.mul (hf.re_odd (2 * u + 1)), ?_⟩
      rw [hx0, pow_succ]
      ring
    have herr : (2 : ℤ) ^ (k + 2) ∣ x.re * (y.im - x.im) - x.im * (y.re - x.re) := by
      refine ⟨x.re * c2 - x.im * c1, ?_⟩
      rw [hc1, hc2]
      ring
    exact exactTwo_add_dvd_succ hmain herr
  lip_re u v := by
    set M := (2 : ℤ) ^ (k + 3) * ((u : ℤ) - v)
    have h0 : (2 : ℤ) ^ (k + 2) * (((2 * u : ℕ) : ℤ) - ((2 * v : ℕ) : ℤ)) = M := by
      push_cast; rw [pow_succ]; ring
    have h1 : (2 : ℤ) ^ (k + 2) * (((2 * u + 1 : ℕ) : ℤ) - ((2 * v + 1 : ℕ) : ℤ)) = M := by
      push_cast; rw [pow_succ]; ring
    have hre0 := hf.lip_re (2 * u) (2 * v)
    have him0 := hf.lip_im (2 * u) (2 * v)
    have hre1 := hf.lip_re (2 * u + 1) (2 * v + 1)
    have him1 := hf.lip_im (2 * u + 1) (2 * v + 1)
    rw [h0] at hre0 him0
    rw [h1] at hre1 him1
    rcases hre0 with ⟨d1, hd1⟩
    rcases him0 with ⟨d2, hd2⟩
    rcases hre1 with ⟨d3, hd3⟩
    rcases him1 with ⟨d4, hd4⟩
    have e1 : (f (2 * u)).re = (f (2 * v)).re + M * d1 := by linarith
    have e2 : (f (2 * u)).im = (f (2 * v)).im + M * d2 := by linarith
    have e3 : (f (2 * u + 1)).re = (f (2 * v + 1)).re + M * d3 := by linarith
    have e4 : (f (2 * u + 1)).im = (f (2 * v + 1)).im + M * d4 := by linarith
    refine ⟨d1 * (f (2 * v + 1)).re + (f (2 * v)).re * d3 + M * d1 * d3 -
      16 * (d2 * (f (2 * v + 1)).im + (f (2 * v)).im * d4 + M * d2 * d4), ?_⟩
    simp only [Quad4.mul, e1, e2, e3, e4]
    ring
  lip_im u v := by
    set M := (2 : ℤ) ^ (k + 3) * ((u : ℤ) - v)
    have h0 : (2 : ℤ) ^ (k + 2) * (((2 * u : ℕ) : ℤ) - ((2 * v : ℕ) : ℤ)) = M := by
      push_cast; rw [pow_succ]; ring
    have h1 : (2 : ℤ) ^ (k + 2) * (((2 * u + 1 : ℕ) : ℤ) - ((2 * v + 1 : ℕ) : ℤ)) = M := by
      push_cast; rw [pow_succ]; ring
    have hre0 := hf.lip_re (2 * u) (2 * v)
    have him0 := hf.lip_im (2 * u) (2 * v)
    have hre1 := hf.lip_re (2 * u + 1) (2 * v + 1)
    have him1 := hf.lip_im (2 * u + 1) (2 * v + 1)
    rw [h0] at hre0 him0
    rw [h1] at hre1 him1
    rcases hre0 with ⟨d1, hd1⟩
    rcases him0 with ⟨d2, hd2⟩
    rcases hre1 with ⟨d3, hd3⟩
    rcases him1 with ⟨d4, hd4⟩
    have e1 : (f (2 * u)).re = (f (2 * v)).re + M * d1 := by linarith
    have e2 : (f (2 * u)).im = (f (2 * v)).im + M * d2 := by linarith
    have e3 : (f (2 * u + 1)).re = (f (2 * v + 1)).re + M * d3 := by linarith
    have e4 : (f (2 * u + 1)).im = (f (2 * v + 1)).im + M * d4 := by linarith
    refine ⟨d1 * (f (2 * v + 1)).im + (f (2 * v)).re * d4 + M * d1 * d4 +
      d2 * (f (2 * v + 1)).re + (f (2 * v)).im * d3 + M * d2 * d3, ?_⟩
    simp only [Quad4.mul, e1, e2, e3, e4]
    ring

/-- Dyadic valuation theorem for contiguous products of any `Good` sequence. -/
theorem prodFrom_good (L : ℕ) (hL : 1 ≤ L) :
    ∀ (k : ℕ) (f : ℕ → Quad4) (s : ℕ), Good k f →
      Odd (prodFrom f s L).re ∧
      (∀ e : ℕ, ExactTwo e (L : ℤ) → ExactTwo (k + e) (prodFrom f s L).im) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro k f s hf
    by_cases hL1 : L = 1
    · subst hL1
      rw [prodFrom_one]
      refine ⟨hf.re_odd s, ?_⟩
      intro e he
      have he0 : e = 0 := exactTwo_of_odd he ⟨0, by norm_num⟩
      subst he0
      simpa using hf.im_exact s
    · by_cases hpar : L % 2 = 0
      · set m := L / 2
        have hLm : L = 2 * m := by omega
        have hm1 : 1 ≤ m := by omega
        have hmlt : m < L := by omega
        rw [hLm, prodFrom_pair]
        have hf' : Good (k + 1) (fun u => (f (s + 2 * u)).mul (f (s + 2 * u + 1))) := by
          have hsh := good_pair (good_shift hf s)
          convert hsh using 1
          ext u
          have : s + (2 * u + 1) = s + 2 * u + 1 := by omega
          simp [this]
        rcases ih m hmlt hm1 (k + 1) _ 0 hf' with ⟨hre, him⟩
        refine ⟨hre, ?_⟩
        intro e he
        have he2 : ExactTwo e (2 * (m : ℤ)) := by
          have : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; ring
          rwa [← this]
        rcases exactTwo_two_mul he2 with ⟨e', rfl, hm_ex⟩
        have hres := him e' hm_ex
        have hke : k + 1 + e' = k + (e' + 1) := by omega
        rwa [hke] at hres
      · set m := L / 2
        have hLm : L = 2 * m + 1 := by omega
        have hm1 : 1 ≤ m := by omega
        have h2m1 : 1 ≤ 2 * m := by omega
        have h2mlt : 2 * m < L := by omega
        rw [hLm, prodFrom]
        rcases ih (2 * m) h2mlt h2m1 k f s hf with ⟨hPre, hPim⟩
        set P := prodFrom f s (2 * m)
        set Q := f (s + 2 * m)
        have hQre : Odd Q.re := hf.re_odd (s + 2 * m)
        have hQim : ExactTwo k Q.im := hf.im_exact (s + 2 * m)
        refine ⟨?_, ?_⟩
        · rcases hPre with ⟨a, ha⟩
          rcases hQre with ⟨b, hb⟩
          refine ⟨2 * a * b + a + b - 8 * P.im * Q.im, ?_⟩
          simp only [Quad4.mul, ha, hb]
          ring
        · intro e he
          have hoddL : Odd ((2 * m + 1 : ℕ) : ℤ) := ⟨(m : ℤ), by push_cast; ring⟩
          have he0 : e = 0 := exactTwo_of_odd he hoddL
          subst he0
          rw [Nat.add_zero]
          rcases exists_exactTwo_nat (2 * m) h2m1 with ⟨e2, he2⟩
          have he2' : ExactTwo e2 (2 * (m : ℤ)) := by
            have : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; ring
            rwa [← this]
          rcases exactTwo_two_mul he2' with ⟨e', rfl, _⟩
          have hP_ex : ExactTwo (k + (e' + 1)) P.im := hPim (e' + 1) he2
          have hP_dvd : (2 : ℤ) ^ (k + 1) ∣ P.im := by
            have hd1 : (2 : ℤ) ^ (k + (e' + 1)) ∣ P.im := exactTwo_dvd hP_ex
            have hd2 : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ (k + (e' + 1)) := by
              refine ⟨(2 : ℤ) ^ e', ?_⟩
              rw [← pow_add]
              congr 1
              omega
            exact dvd_trans hd2 hd1
          have hmain : ExactTwo k (P.re * Q.im) := by
            rw [mul_comm]
            exact exactTwo_mul_odd hQim hPre
          have herr : (2 : ℤ) ^ (k + 1) ∣ P.im * Q.re := dvd_mul_of_dvd_left hP_dvd Q.re
          simpa [Quad4.mul] using exactTwo_add_dvd_succ hmain herr

/-- General constructor proving `Good 0` for paired 4-factor `Quad4` blocks. -/
lemma good_zero_of_qblock (q : ℤ → Quad4) (c : ℤ)
    (hre_odd : ∀ t : ℤ, Odd (q t).re)
    (hre_lip : ∀ t s : ℤ, 8 * (t - s) ∣ (q t).re - (q s).re)
    (him_lip : ∀ t s : ℤ, ∃ w : ℤ, Odd w ∧ (q t).im - (q s).im = (t - s) * w)
    (him_odd : ∀ u : ℕ, Odd ((q (2 * (u : ℤ) + c)).mul (q (2 * (u : ℤ) + c + 1))).im) :
    Good 0 (fun u => (q (2 * (u : ℤ) + c)).mul (q (2 * (u : ℤ) + c + 1))) where
  re_odd u := by
    rcases hre_odd (2 * (u : ℤ) + c) with ⟨a, ha⟩
    rcases hre_odd (2 * (u : ℤ) + c + 1) with ⟨b, hb⟩
    refine ⟨2 * a * b + a + b - 8 * (q (2 * (u : ℤ) + c)).im * (q (2 * (u : ℤ) + c + 1)).im, ?_⟩
    simp only [Quad4.mul, ha, hb]
    ring
  im_exact u := by
    exact ⟨_, him_odd u, by simp⟩
  lip_re u v := by
    set d : ℤ := (u : ℤ) - v
    set t0 : ℤ := 2 * (u : ℤ) + c
    set s0 : ℤ := 2 * (v : ℤ) + c
    set t1 : ℤ := 2 * (u : ℤ) + c + 1
    set s1 : ℤ := 2 * (v : ℤ) + c + 1
    have hts0 : t0 - s0 = 2 * d := by dsimp [d, t0, s0]; ring
    have hts1 : t1 - s1 = 2 * d := by dsimp [d, t1, s1]; ring
    have hre0 := hre_lip t0 s0
    have hre1 := hre_lip t1 s1
    rw [hts0] at hre0
    rw [hts1] at hre1
    rcases hre0 with ⟨a0, ha0⟩
    rcases hre1 with ⟨a1, ha1⟩
    rcases him_lip t0 s0 with ⟨w0, _, hw0⟩
    rcases him_lip t1 s1 with ⟨w1, _, hw1⟩
    rw [hts0] at hw0
    rw [hts1] at hw1
    have e1 : (q t0).re = (q s0).re + 16 * d * a0 := by linarith
    have e2 : (q t0).im = (q s0).im + 2 * d * w0 := by linarith
    have e3 : (q t1).re = (q s1).re + 16 * d * a1 := by linarith
    have e4 : (q t1).im = (q s1).im + 2 * d * w1 := by linarith
    change (2 : ℤ) ^ (0 + 2) * d ∣ ((q t0).mul (q t1)).re - ((q s0).mul (q s1)).re
    refine ⟨4 * a0 * (q s1).re + 4 * (q s0).re * a1 + 64 * d * a0 * a1 -
      8 * w0 * (q s1).im - 8 * (q s0).im * w1 - 16 * d * w0 * w1, ?_⟩
    simp only [Quad4.mul, e1, e2, e3, e4]
    ring
  lip_im u v := by
    set d : ℤ := (u : ℤ) - v
    set t0 : ℤ := 2 * (u : ℤ) + c
    set s0 : ℤ := 2 * (v : ℤ) + c
    set t1 : ℤ := 2 * (u : ℤ) + c + 1
    set s1 : ℤ := 2 * (v : ℤ) + c + 1
    have hts0 : t0 - s0 = 2 * d := by dsimp [d, t0, s0]; ring
    have hts1 : t1 - s1 = 2 * d := by dsimp [d, t1, s1]; ring
    have hre0 := hre_lip t0 s0
    have hre1 := hre_lip t1 s1
    rw [hts0] at hre0
    rw [hts1] at hre1
    rcases hre0 with ⟨a0, ha0⟩
    rcases hre1 with ⟨a1, ha1⟩
    rcases him_lip t0 s0 with ⟨w0, hw0_odd, hw0⟩
    rcases him_lip t1 s1 with ⟨w1, hw1_odd, hw1⟩
    rw [hts0] at hw0
    rw [hts1] at hw1
    have e1 : (q t0).re = (q s0).re + 16 * d * a0 := by linarith
    have e2 : (q t0).im = (q s0).im + 2 * d * w0 := by linarith
    have e3 : (q t1).re = (q s1).re + 16 * d * a1 := by linarith
    have e4 : (q t1).im = (q s1).im + 2 * d * w1 := by linarith
    have hs0_odd := hre_odd s0
    have hs1_odd := hre_odd s1
    have hsum_even : Even ((q s0).re * w1 + w0 * (q s1).re) := by
      rcases hs0_odd.mul hw1_odd with ⟨p1, hp1⟩
      rcases hw0_odd.mul hs1_odd with ⟨p2, hp2⟩
      exact ⟨p1 + p2 + 1, by linarith⟩
    rcases hsum_even with ⟨r, hr⟩
    change (2 : ℤ) ^ (0 + 2) * d ∣ ((q t0).mul (q t1)).im - ((q s0).mul (q s1)).im
    refine ⟨4 * a0 * (q s1).im + 8 * d * a0 * w1 + 4 * (q s0).im * a1 + 8 * d * w0 * a1 + r, ?_⟩
    simp only [Quad4.mul, e1, e2, e3, e4]
    linear_combination 2 * d * hr

/-- 4-factor block starting at `4*t + 1`: `∏_{j=0}^3 (1 + (4t + 1 + j) i) = 2 * toGInt (qBlock1 t)`. -/
def qBlock1 (t : ℤ) : Quad4 :=
  ⟨128 * t ^ 4 + 320 * t ^ 3 + 232 * t ^ 2 + 40 * t - 5,
   -(t + 1) * (4 * t + 1) * (8 * t + 5)⟩

/-- 4-factor block starting at `4*t`: `∏_{j=0}^3 (1 + (4t + j) i) = 2 * toGInt (qBlock0 t)`. -/
def qBlock0 (t : ℤ) : Quad4 :=
  ⟨128 * t ^ 4 + 192 * t ^ 3 + 40 * t ^ 2 - 24 * t - 5,
   -t * (4 * t + 3) * (8 * t + 3)⟩

lemma qBlock1_step (z : GInt) (t : ℤ) :
    ((((z.mul ⟨1, 4 * t + 1⟩).mul ⟨1, 4 * t + 2⟩).mul ⟨1, 4 * t + 3⟩).mul ⟨1, 4 * t + 4⟩) =
      z.mul ((qBlock1 t).toGInt.scale 2) := by
  apply GInt.ext <;> simp [GInt.mul, GInt.scale, Quad4.toGInt, qBlock1] <;> ring

lemma qBlock0_step (z : GInt) (t : ℤ) :
    ((((z.mul ⟨1, 4 * t⟩).mul ⟨1, 4 * t + 1⟩).mul ⟨1, 4 * t + 2⟩).mul ⟨1, 4 * t + 3⟩) =
      z.mul ((qBlock0 t).toGInt.scale 2) := by
  apply GInt.ext <;> simp [GInt.mul, GInt.scale, Quad4.toGInt, qBlock0] <;> ring

lemma qBlock1_re_odd (t : ℤ) : Odd (qBlock1 t).re := by
  refine ⟨64 * t ^ 4 + 160 * t ^ 3 + 116 * t ^ 2 + 20 * t - 3, ?_⟩
  simp [qBlock1]
  ring

lemma qBlock1_re_lip (t s : ℤ) : 8 * (t - s) ∣ (qBlock1 t).re - (qBlock1 s).re := by
  refine ⟨16 * (t ^ 3 + t ^ 2 * s + t * s ^ 2 + s ^ 3) + 40 * (t ^ 2 + t * s + s ^ 2) +
    29 * (t + s) + 5, ?_⟩
  simp [qBlock1]
  ring

lemma qBlock1_im_lip (t s : ℤ) : ∃ w : ℤ, Odd w ∧ (qBlock1 t).im - (qBlock1 s).im = (t - s) * w := by
  refine ⟨-(32 * (t ^ 2 + t * s + s ^ 2) + 60 * (t + s) + 33), ?_, ?_⟩
  · refine ⟨-(16 * (t ^ 2 + t * s + s ^ 2) + 30 * (t + s) + 17), ?_⟩
    ring
  · simp [qBlock1]
    ring

lemma qBlock0_re_odd (t : ℤ) : Odd (qBlock0 t).re := by
  refine ⟨64 * t ^ 4 + 96 * t ^ 3 + 20 * t ^ 2 - 12 * t - 3, ?_⟩
  simp [qBlock0]
  ring

lemma qBlock0_re_lip (t s : ℤ) : 8 * (t - s) ∣ (qBlock0 t).re - (qBlock0 s).re := by
  refine ⟨16 * (t ^ 3 + t ^ 2 * s + t * s ^ 2 + s ^ 3) + 24 * (t ^ 2 + t * s + s ^ 2) +
    5 * (t + s) - 3, ?_⟩
  simp [qBlock0]
  ring

lemma qBlock0_im_lip (t s : ℤ) : ∃ w : ℤ, Odd w ∧ (qBlock0 t).im - (qBlock0 s).im = (t - s) * w := by
  refine ⟨-(32 * (t ^ 2 + t * s + s ^ 2) + 36 * (t + s) + 9), ?_, ?_⟩
  · refine ⟨-(16 * (t ^ 2 + t * s + s ^ 2) + 18 * (t + s) + 5), ?_⟩
    ring
  · simp [qBlock0]
    ring

/-- 8-factor block starting at `8*u + 1`. -/
def b8_1 (u : ℕ) : Quad4 :=
  (qBlock1 (2 * (u : ℤ))).mul (qBlock1 (2 * (u : ℤ) + 1))

/-- 8-factor block starting at `8*u + 4`. -/
def b8_4 (u : ℕ) : Quad4 :=
  (qBlock0 (2 * (u : ℤ) + 1)).mul (qBlock0 (2 * (u : ℤ) + 2))

lemma good_b8_1 : Good 0 b8_1 := by
  have h := good_zero_of_qblock qBlock1 0 qBlock1_re_odd qBlock1_re_lip qBlock1_im_lip (by
    intro u
    set x := qBlock1 (2 * (u : ℤ) + 0)
    set y := qBlock1 (2 * (u : ℤ) + 0 + 1)
    have hx_im : Odd x.im := by
      have h1 : Odd (-(2 * (u : ℤ) + 1)) := ⟨-(u : ℤ) - 1, by ring⟩
      have h2 : Odd (4 * (2 * (u : ℤ) + 0) + 1) := ⟨4 * (u : ℤ), by ring⟩
      have h3 : Odd (8 * (2 * (u : ℤ) + 0) + 5) := ⟨8 * (u : ℤ) + 2, by ring⟩
      have hm := (h1.mul h2).mul h3
      convert hm using 1
      simp [x, qBlock1]
    have hy_im : Even y.im := by
      refine ⟨-((u : ℤ) + 1) * (4 * (2 * (u : ℤ) + 1) + 1) * (8 * (2 * (u : ℤ) + 1) + 5), ?_⟩
      simp [y, qBlock1]
      ring
    have hy_re : Odd y.re := qBlock1_re_odd _
    rcases hx_im.mul hy_re with ⟨a, ha⟩
    rcases hy_im with ⟨b, hb⟩
    refine ⟨x.re * b + a, ?_⟩
    simp only [Quad4.mul, ha, hb]
    ring)
  convert h using 1
  ext u
  simp [b8_1]

lemma good_b8_4 : Good 0 b8_4 := by
  have h := good_zero_of_qblock qBlock0 1 qBlock0_re_odd qBlock0_re_lip qBlock0_im_lip (by
    intro u
    set x := qBlock0 (2 * (u : ℤ) + 1)
    set y := qBlock0 (2 * (u : ℤ) + 1 + 1)
    have hx_im : Odd x.im := by
      have h1 : Odd (-(2 * (u : ℤ) + 1)) := ⟨-(u : ℤ) - 1, by ring⟩
      have h2 : Odd (4 * (2 * (u : ℤ) + 1) + 3) := ⟨4 * (u : ℤ) + 3, by ring⟩
      have h3 : Odd (8 * (2 * (u : ℤ) + 1) + 3) := ⟨8 * (u : ℤ) + 5, by ring⟩
      have hm := (h1.mul h2).mul h3
      convert hm using 1
      simp [x, qBlock0]
    have hy_im : Even y.im := by
      refine ⟨-((u : ℤ) + 1) * (4 * (2 * (u : ℤ) + 2) + 3) * (8 * (2 * (u : ℤ) + 2) + 3), ?_⟩
      simp [y, qBlock0]
      ring
    have hy_re : Odd y.re := qBlock0_re_odd _
    rcases hx_im.mul hy_re with ⟨a, ha⟩
    rcases hy_im with ⟨b, hb⟩
    refine ⟨x.re * b + a, ?_⟩
    simp only [Quad4.mul, ha, hb]
    ring)
  convert h using 1
  ext u
  have h2 : 2 * (u : ℤ) + 1 + 1 = 2 * (u : ℤ) + 2 := by ring
  simp [b8_4, h2]

lemma Zg_4_mul_add_1 (t : ℕ) :
    Zg (4 * t + 1) = (prodFrom (fun j => qBlock1 (j : ℤ)) 0 t).toGInt.scale ((2 : ℤ) ^ t) := by
  induction t with
  | zero =>
    apply GInt.ext <;> simp [Zg, prodFrom, Quad4.one, Quad4.toGInt, GInt.one, GInt.mul, GInt.scale]
  | succ t ih =>
    have hidx : 4 * (t + 1) + 1 = (((4 * t + 1) + 1) + 1) + 1 + 1 := by omega
    rw [hidx, Zg, Zg, Zg, Zg]
    have hs := qBlock1_step (Zg (4 * t + 1)) (t : ℤ)
    have he1 : ((4 * t + 1 : ℕ) : ℤ) = 4 * (t : ℤ) + 1 := by push_cast; ring
    have he2 : ((4 * t + 1 + 1 : ℕ) : ℤ) = 4 * (t : ℤ) + 2 := by push_cast; ring
    have he3 : ((4 * t + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (t : ℤ) + 3 := by push_cast; ring
    have he4 : ((4 * t + 1 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (t : ℤ) + 4 := by push_cast; ring
    rw [he1, he2, he3, he4, hs, ih, GInt.scale_mul_left, GInt.scale_mul_right, GInt.scale_scale,
      ← Quad4.toGInt_mul]
    rw [prodFrom, Nat.zero_add, pow_succ]

lemma prodFrom_qBlock1_re_odd (t : ℕ) :
    Odd (prodFrom (fun j => qBlock1 (j : ℤ)) 0 t).re := by
  induction t with
  | zero =>
    exact ⟨0, by simp [prodFrom, Quad4.one]⟩
  | succ t ih =>
    rw [prodFrom, Nat.zero_add]
    rcases ih with ⟨a, ha⟩
    rcases qBlock1_re_odd (t : ℤ) with ⟨b, hb⟩
    refine ⟨2 * a * b + a + b - 8 * (prodFrom (fun j => qBlock1 (j : ℤ)) 0 t).im * (qBlock1 (t : ℤ)).im, ?_⟩
    simp only [Quad4.mul, ha, hb]
    ring

lemma Zg_8_mul_add_1 (k : ℕ) :
    Zg (8 * k + 1) = (prodFrom b8_1 0 k).toGInt.scale ((4 : ℤ) ^ k) := by
  induction k with
  | zero =>
    apply GInt.ext <;> simp [Zg, prodFrom, Quad4.one, Quad4.toGInt, GInt.one, GInt.mul, GInt.scale]
  | succ k ih =>
    have h1 : 8 * (k + 1) + 1 = (((8 * k + 5) + 1) + 1) + 1 + 1 := by omega
    have h2 : 8 * k + 5 = (((8 * k + 1) + 1) + 1) + 1 + 1 := by omega
    rw [h1, Zg, Zg, Zg, Zg]
    have hs2 := qBlock1_step (Zg (8 * k + 5)) (2 * (k : ℤ) + 1)
    have ha1 : ((8 * k + 5 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 1 := by push_cast; ring
    have ha2 : ((8 * k + 5 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 2 := by push_cast; ring
    have ha3 : ((8 * k + 5 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 3 := by push_cast; ring
    have ha4 : ((8 * k + 5 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 4 := by push_cast; ring
    rw [ha1, ha2, ha3, ha4, hs2]
    rw [h2, Zg, Zg, Zg, Zg]
    have hs1 := qBlock1_step (Zg (8 * k + 1)) (2 * (k : ℤ))
    have hb1 : ((8 * k + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ)) + 1 := by push_cast; ring
    have hb2 : ((8 * k + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ)) + 2 := by push_cast; ring
    have hb3 : ((8 * k + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ)) + 3 := by push_cast; ring
    have hb4 : ((8 * k + 1 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ)) + 4 := by push_cast; ring
    rw [hb1, hb2, hb3, hb4, hs1, ih]
    simp only [GInt.scale_mul_left, GInt.scale_mul_right, GInt.scale_scale,
      ← Quad4.toGInt_mul, Quad4.mul_assoc, prodFrom, Nat.zero_add, b8_1]
    congr 1
    ring

lemma Zg_8_mul_add_4 (k : ℕ) :
    Zg (8 * k + 4) = (prodFrom b8_4 0 k).toGInt.scale ((-10) * (4 : ℤ) ^ k) := by
  induction k with
  | zero =>
    apply GInt.ext <;> simp [Zg, prodFrom, Quad4.one, Quad4.toGInt, GInt.one, GInt.mul, GInt.scale]
  | succ k ih =>
    have h1 : 8 * (k + 1) + 4 = (((8 * k + 8) + 1) + 1) + 1 + 1 := by omega
    have h2 : 8 * k + 8 = (((8 * k + 4) + 1) + 1) + 1 + 1 := by omega
    rw [h1, Zg, Zg, Zg, Zg]
    have hs2 := qBlock0_step (Zg (8 * k + 8)) (2 * (k : ℤ) + 2)
    have ha1 : ((8 * k + 8 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 2) := by push_cast; ring
    have ha2 : ((8 * k + 8 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 2) + 1 := by push_cast; ring
    have ha3 : ((8 * k + 8 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 2) + 2 := by push_cast; ring
    have ha4 : ((8 * k + 8 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 2) + 3 := by push_cast; ring
    rw [ha1, ha2, ha3, ha4, hs2]
    rw [h2, Zg, Zg, Zg, Zg]
    have hs1 := qBlock0_step (Zg (8 * k + 4)) (2 * (k : ℤ) + 1)
    have hb1 : ((8 * k + 4 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) := by push_cast; ring
    have hb2 : ((8 * k + 4 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 1 := by push_cast; ring
    have hb3 : ((8 * k + 4 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 2 := by push_cast; ring
    have hb4 : ((8 * k + 4 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (k : ℤ) + 1) + 3 := by push_cast; ring
    rw [hb1, hb2, hb3, hb4, hs1, ih]
    simp only [GInt.scale_mul_left, GInt.scale_mul_right, GInt.scale_scale,
      ← Quad4.toGInt_mul, Quad4.mul_assoc, prodFrom, Nat.zero_add, b8_4]
    congr 1
    ring

lemma Zg_im_ne_zero_4_add_1 (t : ℕ) : (Zg (4 * t + 2)).im ≠ 0 := by
  have hstep : Zg (4 * t + 2) = (Zg (4 * t + 1)).mul ⟨1, ((4 * t + 1 : ℕ) : ℤ)⟩ := rfl
  rw [hstep, Zg_4_mul_add_1 t, GInt.scale_mul_left]
  set P := prodFrom (fun j => qBlock1 (j : ℤ)) 0 t
  have hPre : Odd P.re := prodFrom_qBlock1_re_odd t
  have hodd : Odd (P.re * ((4 * t + 1 : ℕ) : ℤ) + 4 * P.im * 1) := by
    rcases hPre with ⟨a, ha⟩
    refine ⟨4 * a * (t : ℤ) + a + 2 * (t : ℤ) + 2 * P.im, ?_⟩
    rw [ha]
    push_cast
    ring
  simp only [GInt.scale, GInt.mul, Quad4.toGInt]
  have hp : (2 : ℤ) ^ t ≠ 0 := by positivity
  have ho : P.re * ((4 * t + 1 : ℕ) : ℤ) + 4 * P.im * 1 ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact mul_ne_zero hp ho

lemma Zg_im_ne_zero_4_add_2 (t : ℕ) : (Zg (4 * t + 3)).im ≠ 0 := by
  have hstep : Zg (4 * t + 3) =
      ((Zg (4 * t + 1)).mul ⟨1, ((4 * t + 1 : ℕ) : ℤ)⟩).mul ⟨1, ((4 * t + 2 : ℕ) : ℤ)⟩ := rfl
  rw [hstep, GInt.mul_assoc, Zg_4_mul_add_1 t, GInt.scale_mul_left]
  set P := prodFrom (fun j => qBlock1 (j : ℤ)) 0 t
  have hPre : Odd P.re := prodFrom_qBlock1_re_odd t
  set u : ℤ := 1 * 1 - ((4 * t + 1 : ℕ) : ℤ) * ((4 * t + 2 : ℕ) : ℤ)
  set v : ℤ := 1 * ((4 * t + 2 : ℕ) : ℤ) + ((4 * t + 1 : ℕ) : ℤ) * 1
  have hv_odd : Odd v := ⟨4 * (t : ℤ) + 1, by dsimp [v]; ring⟩
  have hodd : Odd (P.re * v + 4 * P.im * u) := by
    rcases hPre.mul hv_odd with ⟨a, ha⟩
    refine ⟨a + 2 * P.im * u, ?_⟩
    linarith
  simp only [GInt.scale, GInt.mul, Quad4.toGInt]
  have hp : (2 : ℤ) ^ t ≠ 0 := by positivity
  have ho : P.re * v + 4 * P.im * u ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact mul_ne_zero hp ho

lemma Zg_im_ne_zero_8_add_8 (m : ℕ) : (Zg (8 * m + 9)).im ≠ 0 := by
  have hidx : 8 * m + 9 = 8 * (m + 1) + 1 := by omega
  rw [hidx, Zg_8_mul_add_1 (m + 1)]
  rcases exists_exactTwo_nat (m + 1) (by omega) with ⟨e, he⟩
  have hP := (prodFrom_good (m + 1) (by omega) 0 b8_1 0 good_b8_1).2 e he
  have hPne : (prodFrom b8_1 0 (m + 1)).im ≠ 0 := exactTwo_ne_zero hP
  simp only [GInt.scale, Quad4.toGInt]
  have hp : (4 : ℤ) ^ (m + 1) ≠ 0 := by positivity
  exact mul_ne_zero hp (mul_ne_zero (by norm_num) hPne)

lemma Zg_im_ne_zero_8_add_11 (m : ℕ) : (Zg (8 * m + 12)).im ≠ 0 := by
  have hidx : 8 * m + 12 = 8 * (m + 1) + 4 := by omega
  rw [hidx, Zg_8_mul_add_4 (m + 1)]
  rcases exists_exactTwo_nat (m + 1) (by omega) with ⟨e, he⟩
  have hP := (prodFrom_good (m + 1) (by omega) 0 b8_4 0 good_b8_4).2 e he
  have hPne : (prodFrom b8_4 0 (m + 1)).im ≠ 0 := exactTwo_ne_zero hP
  simp only [GInt.scale, Quad4.toGInt]
  have hp : (-10 : ℤ) * (4 : ℤ) ^ (m + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (by positivity)
  exact mul_ne_zero hp (mul_ne_zero (by norm_num) hPne)

lemma Zg_im_ne_zero_8_add_7 (m : ℕ) : (Zg (8 * m + 8)).im ≠ 0 := by
  intro him0
  have hrel : Zg (8 * m + 9) = (Zg (8 * m + 8)).mul ⟨1, ((8 * m + 8 : ℕ) : ℤ)⟩ := rfl
  have hidx : 8 * m + 9 = 8 * (m + 1) + 1 := by omega
  have h9 := Zg_8_mul_add_1 (m + 1)
  rw [← hidx] at h9
  set P := prodFrom b8_1 0 (m + 1)
  have hre9 : (Zg (8 * m + 9)).re = (Zg (8 * m + 8)).re := by
    rw [hrel]; simp [GInt.mul, him0]
  have him9 : (Zg (8 * m + 9)).im = (Zg (8 * m + 8)).re * ((8 * m + 8 : ℕ) : ℤ) := by
    rw [hrel]; simp [GInt.mul, him0]
  have hreP : (Zg (8 * m + 9)).re = (4 : ℤ) ^ (m + 1) * P.re := by
    rw [h9]; simp [GInt.scale, Quad4.toGInt]
  have himP : (Zg (8 * m + 9)).im = (4 : ℤ) ^ (m + 1) * (4 * P.im) := by
    rw [h9]; simp [GInt.scale, Quad4.toGInt]
  have heq : (4 : ℤ) ^ (m + 1) * 4 * P.im = (4 : ℤ) ^ (m + 1) * 4 * (2 * ((m + 1 : ℕ) : ℤ) * P.re) := by
    have h8 : ((8 * m + 8 : ℕ) : ℤ) = 8 * ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hre9] at hreP
    calc
      (4 : ℤ) ^ (m + 1) * 4 * P.im = (Zg (8 * m + 9)).im := by rw [himP]; ring
      _ = (Zg (8 * m + 8)).re * ((8 * m + 8 : ℕ) : ℤ) := him9
      _ = (4 : ℤ) ^ (m + 1) * P.re * (8 * ((m + 1 : ℕ) : ℤ)) := by rw [hreP, h8]
      _ = (4 : ℤ) ^ (m + 1) * 4 * (2 * ((m + 1 : ℕ) : ℤ) * P.re) := by ring
  have hc : (4 : ℤ) ^ (m + 1) * 4 ≠ 0 := by positivity
  have hPeq : P.im = 2 * ((m + 1 : ℕ) : ℤ) * P.re := mul_left_cancel₀ hc heq
  rcases exists_exactTwo_nat (m + 1) (by omega) with ⟨e, he⟩
  have hPex : ExactTwo e P.im := by
    simpa using (prodFrom_good (m + 1) (by omega) 0 b8_1 0 good_b8_1).2 e he
  have hdvd : (2 : ℤ) ^ (e + 1) ∣ P.im := by
    rcases exactTwo_dvd he with ⟨c, hc'⟩
    refine ⟨c * P.re, ?_⟩
    rw [hPeq, hc', pow_succ]
    ring
  exact exactTwo_not_dvd_succ hPex hdvd

lemma Zg_im_ne_zero_8_add_4 (m : ℕ) : (Zg (8 * m + 5)).im ≠ 0 := by
  intro him0
  have hstep : Zg (8 * m + 9) = (Zg (8 * m + 5)).mul ((qBlock1 (2 * (m : ℤ) + 1)).toGInt.scale 2) := by
    have h1 : 8 * m + 9 = (((8 * m + 5) + 1) + 1) + 1 + 1 := by omega
    rw [h1, Zg, Zg, Zg, Zg]
    have ha1 : ((8 * m + 5 : ℕ) : ℤ) = 4 * (2 * (m : ℤ) + 1) + 1 := by push_cast; ring
    have ha2 : ((8 * m + 5 + 1 : ℕ) : ℤ) = 4 * (2 * (m : ℤ) + 1) + 2 := by push_cast; ring
    have ha3 : ((8 * m + 5 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (m : ℤ) + 1) + 3 := by push_cast; ring
    have ha4 : ((8 * m + 5 + 1 + 1 + 1 : ℕ) : ℤ) = 4 * (2 * (m : ℤ) + 1) + 4 := by push_cast; ring
    rw [ha1, ha2, ha3, ha4]
    exact qBlock1_step (Zg (8 * m + 5)) (2 * (m : ℤ) + 1)
  have hidx : 8 * m + 9 = 8 * (m + 1) + 1 := by omega
  have h9 := Zg_8_mul_add_1 (m + 1)
  rw [← hidx] at h9
  set P := prodFrom b8_1 0 (m + 1)
  set Q := qBlock1 (2 * (m : ℤ) + 1)
  have hre9 : (Zg (8 * m + 9)).re = (Zg (8 * m + 5)).re * (2 * Q.re) := by
    rw [hstep]; simp [GInt.mul, GInt.scale, Quad4.toGInt, him0]
  have him9 : (Zg (8 * m + 9)).im = (Zg (8 * m + 5)).re * (2 * (4 * Q.im)) := by
    rw [hstep]; simp [GInt.mul, GInt.scale, Quad4.toGInt, him0]
  have hcross : (Zg (8 * m + 9)).im * Q.re = 4 * (Zg (8 * m + 9)).re * Q.im := by
    rw [hre9, him9]; ring
  have hreP : (Zg (8 * m + 9)).re = (4 : ℤ) ^ (m + 1) * P.re := by
    rw [h9]; simp [GInt.scale, Quad4.toGInt]
  have himP : (Zg (8 * m + 9)).im = (4 : ℤ) ^ (m + 1) * (4 * P.im) := by
    rw [h9]; simp [GInt.scale, Quad4.toGInt]
  have heq : (4 : ℤ) ^ (m + 1) * 4 * (P.im * Q.re) = (4 : ℤ) ^ (m + 1) * 4 * (P.re * Q.im) := by
    rw [hreP, himP] at hcross
    linarith
  have hc : (4 : ℤ) ^ (m + 1) * 4 ≠ 0 := by positivity
  have hPeq : P.im * Q.re = P.re * Q.im := mul_left_cancel₀ hc heq
  rcases exists_exactTwo_nat (m + 1) (by omega) with ⟨e, he⟩
  have hPex : ExactTwo e P.im := by
    simpa using (prodFrom_good (m + 1) (by omega) 0 b8_1 0 good_b8_1).2 e he
  have hPQex : ExactTwo e (P.im * Q.re) := exactTwo_mul_odd hPex (qBlock1_re_odd _)
  have hQim : Q.im = -2 * ((m + 1 : ℕ) : ℤ) * (8 * (m : ℤ) + 5) * (16 * (m : ℤ) + 13) := by
    dsimp [Q, qBlock1]
    ring
  have hdvd : (2 : ℤ) ^ (e + 1) ∣ P.im * Q.re := by
    rcases exactTwo_dvd he with ⟨c, hc'⟩
    refine ⟨-P.re * c * (8 * (m : ℤ) + 5) * (16 * (m : ℤ) + 13), ?_⟩
    rw [hPeq, hQim, hc', pow_succ]
    ring
  exact exactTwo_not_dvd_succ hPQex hdvd

theorem main_H2 (n : ℕ) (hn : 4 ≤ n) : OeisA105751.a n ≠ 0 := by
  rw [a_eq_Zg_im]
  set q := n / 8
  set r := n % 8
  have hnr : n = 8 * q + r := by omega
  have hr : r < 8 := Nat.mod_lt n (by omega)
  interval_cases r
  · have hq : 1 ≤ q := by omega
    have h : n + 1 = 8 * (q - 1) + 9 := by omega
    rw [h]
    exact Zg_im_ne_zero_8_add_8 (q - 1)
  · have h : n + 1 = 4 * (2 * q) + 2 := by omega
    rw [h]
    exact Zg_im_ne_zero_4_add_1 (2 * q)
  · have h : n + 1 = 4 * (2 * q) + 3 := by omega
    rw [h]
    exact Zg_im_ne_zero_4_add_2 (2 * q)
  · have hq : 1 ≤ q := by omega
    have h : n + 1 = 8 * (q - 1) + 12 := by omega
    rw [h]
    exact Zg_im_ne_zero_8_add_11 (q - 1)
  · have h : n + 1 = 8 * q + 5 := by omega
    rw [h]
    exact Zg_im_ne_zero_8_add_4 q
  · have h : n + 1 = 4 * (2 * q + 1) + 2 := by omega
    rw [h]
    exact Zg_im_ne_zero_4_add_1 (2 * q + 1)
  · have h : n + 1 = 4 * (2 * q + 1) + 3 := by omega
    rw [h]
    exact Zg_im_ne_zero_4_add_2 (2 * q + 1)
  · have h : n + 1 = 8 * q + 8 := by omega
    rw [h]
    exact Zg_im_ne_zero_8_add_7 q

end H2Proof

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H2 :=
  H2Proof.main_H2
