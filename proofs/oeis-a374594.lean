import OMAStatements.S_oeis_a374594

namespace OMA.S_oeis_a374594



lemma mirror {a c h x y b d : ℤ} (hs : IsSol a c h x y b d) : IsSol a c h y x d b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  exact ⟨h1, h2, h3, h5, h4, by linarith, h8, h7, by linarith⟩

lemma sols_mirror : ∀ t ∈ sols,
    (t.1, t.2.1, t.2.2.1, t.2.2.2.2.1, t.2.2.2.1, t.2.2.2.2.2.2, t.2.2.2.2.2.1) ∈ sols := by
  decide +kernel

lemma sols_sound : ∀ t ∈ sols, IsSol t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
    t.2.2.2.2.2.2 := by
  intro t ht
  simp only [sols, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## Basic consequences -/

lemma lt_of_sq {p q : ℤ} (hq : 0 ≤ q) (h : p ^ 2 < q ^ 2) : p < q :=
  lt_of_pow_lt_pow_left₀ 2 hq h

lemma le_of_sq {p q : ℤ} (hq : 0 ≤ q) (h : p ^ 2 ≤ q ^ 2) : p ≤ q :=
  le_of_pow_le_pow_left₀ two_ne_zero hq h

/-! ## Case A: both offsets nonnegative -/

/-- Pythagorean pairs (h, x, d) with d^2 = h^2 + x^2, 3 ≤ h ≤ 12, 0 ≤ x ≤ 28, d ≥ 0. -/
def pyth3 : List (ℤ × ℤ × ℤ) :=
  [(3, 0, 3), (4, 0, 4), (5, 0, 5), (6, 0, 6), (7, 0, 7), (8, 0, 8), (9, 0, 9), (10, 0, 10),
    (11, 0, 11), (12, 0, 12),
    (3, 4, 5), (4, 3, 5), (5, 12, 13), (6, 8, 10), (7, 24, 25), (8, 6, 10), (8, 15, 17),
    (9, 12, 15), (10, 24, 26), (12, 5, 13), (12, 9, 15), (12, 16, 20)]

lemma pyth_small : ∀ h ∈ Finset.Icc (3 : ℤ) 12, ∀ x ∈ Finset.Icc (0 : ℤ) 28,
    ∀ d ∈ Finset.Icc (0 : ℤ) 41, d ^ 2 = h ^ 2 + x ^ 2 → (h, x, d) ∈ pyth3 := by
  decide +kernel

/-- The value of `c` forced by `(2c + x + y)(h - 2) = 2(b + d)`. -/
def cOf (p q : ℤ × ℤ × ℤ) : ℤ :=
  (2 * (q.2.2 + p.2.2) - (p.2.1 + q.2.1) * (p.1 - 2)) / (2 * (p.1 - 2))

lemma caseA_finite : ∀ p ∈ pyth3, ∀ q ∈ pyth3,
    p.1 = q.1 → 1 ≤ p.2.1 → 0 ≤ q.2.1 → q.2.1 ≤ p.2.1 → 1 ≤ cOf p q →
    (2 * cOf p q + p.2.1 + q.2.1) * (p.1 - 2) = 2 * (q.2.2 + p.2.2) →
    (cOf p q + p.2.1 + q.2.1, cOf p q, p.1, p.2.1, q.2.1, q.2.2, p.2.2) ∈ sols := by
  decide +kernel

lemma caseA {a c h x y b d : ℤ} (hs : IsSol a c h x y b d) (hy : 0 ≤ y) (hxy : y ≤ x) :
    (a, c, h, x, y, b, d) ∈ sols := by
  obtain ⟨hc, hca, hh, hb, hd, hsum, hD, hB, hE⟩ := hs
  have hx1 : 1 ≤ x := by omega
  have ha : a = c + x + y := by linarith
  have hE' : (2 * c + x + y) * (h - 2) = 2 * (b + d) := by subst ha; linarith
  have hdh : h < d := lt_of_sq hd (by rw [hD]; nlinarith)
  have hbh : h ≤ b := le_of_sq hb (by rw [hB]; nlinarith)
  have hdx : x < d := lt_of_sq hd (by rw [hD]; nlinarith)
  have hdle : d ≤ h + x := le_of_sq (by omega) (by rw [hD]; nlinarith)
  have hble : b ≤ h + y := le_of_sq (by omega) (by rw [hB]; nlinarith)
  have h3 : 3 ≤ h := by
    have hp : 0 < (2 * c + x + y) * (h - 2) := by rw [hE']; omega
    have := (pos_iff_pos_of_mul_pos hp).mp (by omega)
    omega
  have hc2 : 2 * (h - 2) ≤ 2 * c * (h - 2) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hexp : (2 * c + x + y) * (h - 2) = 2 * c * (h - 2) + (x + y) * (h - 2) := by ring
  have hkey : (x + y) * (h - 4) ≤ 2 * h + 4 := by
    have : (x + y) * (h - 4) = (x + y) * (h - 2) - 2 * (x + y) := by ring
    linarith
  have h12 : h ≤ 12 := by
    by_contra hgt
    push_neg at hgt
    have hxy3 : x + y ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      have := mul_le_mul_of_nonneg_right (show (4 : ℤ) ≤ x + y by omega) (show (0 : ℤ) ≤ h - 4 by omega)
      linarith
    have hd1 : h + 1 ≤ d := by omega
    have hsq1 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ h + 1) hd1
    have hsq2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ x) (show x ≤ 3 by omega)
    nlinarith
  have hx28 : x ≤ 28 := by
    rcases lt_or_ge h 5 with h5 | h5
    · have hxd : x + 1 ≤ d := by omega
      have hsq1 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ x + 1) hxd
      have hsq2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ h) (show h ≤ 4 by omega)
      nlinarith
    · have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ h - 4 by omega) (show (0 : ℤ) ≤ x + y by omega)
      linarith
  have p1 := pyth_small h (by simp; omega) x (by simp; omega) d (by simp; omega) hD
  have p2 := pyth_small h (by simp; omega) y (by simp; omega) b (by simp; omega) hB
  have hcOf : cOf (h, x, d) (h, y, b) = c := by
    unfold cOf
    simp only
    have hpos : (0 : ℤ) < 2 * (h - 2) := by omega
    rw [show 2 * (b + d) - (x + y) * (h - 2) = c * (2 * (h - 2)) by linarith]
    exact Int.mul_ediv_cancel _ (ne_of_gt hpos)
  have := caseA_finite (h, x, d) p1 (h, y, b) p2 rfl hx1 hy hxy (by rw [hcOf]; exact hc)
    (by rw [hcOf]; exact hE')
  rw [hcOf] at this
  rw [ha]
  exact this

/-! ## Case B: offsets of opposite signs -/

lemma caseB_finite : ∀ h ∈ Finset.Icc (3 : ℤ) 36, ∀ e ∈ Finset.Icc (3 : ℤ) 36, e < h → h < 2 * e →
    e - 2 ∣ h ^ 2 → e ∣ h ^ 2 → (e - 2) * e ∣ 2 * h ^ 2 →
    4 * (h - 2) ∣ (2 * h ^ 2 / ((e - 2) * e) + 2) * (2 * e - h) →
    (2 * h ^ 2 / ((e - 2) * e) + 2) * (2 * e - h) < 4 * (h - 2) := by
  decide +kernel

/-- Large heights are impossible in case B. -/
lemma bigh (w e h : ℤ) (hgt : 37 ≤ h) (he3 : 3 ≤ e) (heh : e < h) (h2e : h < 2 * e)
    (hw : w * ((e - 2) * e) = 2 * h ^ 2) (hc1 : 4 * (h - 2) ≤ (w + 2) * (2 * e - h)) : False := by
  have hP : 0 < (e - 2) * e := mul_pos (by omega) (by omega)
  have h37 : 37 * h ≤ h * h := mul_le_mul_of_nonneg_right hgt (by omega)
  have hP2 : (e - 2) * e < h ^ 2 := by
    have h1 : (e - 2) * e < e * e := mul_lt_mul_of_pos_right (by omega) (by omega)
    have h2 : e * e < h * h := mul_self_lt_mul_self (by omega) heh
    nlinarith
  have hw3 : 3 ≤ w := by
    by_contra hlt
    push_neg at hlt
    have := mul_le_mul_of_nonneg_right (show w ≤ 2 by omega) hP.le
    linarith
  have h4 : (h - 3) * (h + 1) ≤ 4 * ((e - 2) * e) := by
    have := mul_le_mul (show h - 3 ≤ 2 * e - 4 by omega) (show h + 1 ≤ 2 * e by omega)
      (by omega) (by omega)
    linarith
  have hw8 : w ≤ 8 := by
    by_contra hlt
    push_neg at hlt
    have := mul_le_mul_of_nonneg_right (show (9 : ℤ) ≤ w by omega) hP.le
    nlinarith
  have hsq : w * (e - 1) ^ 2 = 2 * h ^ 2 + w := by linear_combination hw
  have hA : (w + 6) * (h - 2) ≤ 2 * (w + 2) * (e - 1) := by
    have : (w + 2) * (2 * e - h) = 2 * (w + 2) * (e - 1) - (w + 2) * (h - 2) := by ring
    linarith
  have hB0 : 0 ≤ (w + 6) * (h - 2) := mul_nonneg (by omega) (by omega)
  have hsq2 := mul_self_le_mul_self hB0 hA
  clear hc1 h4 hP2 hP hA hB0 hw
  interval_cases w <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma caseB {a c h x y b d : ℤ} (hs : IsSol a c h x y b d) (hy : y < 0) : False := by
  obtain ⟨hc, hca, hh, hb, hd, hsum, hD, hB, hE⟩ := hs
  have hx : 1 ≤ x := by omega
  have ha : a = c + x + y := by linarith
  have hE' : (2 * c + x + y) * (h - 2) = 2 * (b + d) := by subst ha; linarith
  have hdx : x < d := lt_of_sq hd (by rw [hD]; nlinarith)
  have hby : -y < b := lt_of_sq hb (by rw [hB]; nlinarith)
  have hbh : h < b := lt_of_sq hb (by rw [hB]; nlinarith)
  have h3 : 3 ≤ h := by
    have hp : 0 < (2 * c + x + y) * (h - 2) := by rw [hE']; omega
    have := (pos_iff_pos_of_mul_pos hp).mp (by omega)
    omega
  have hU : (d + x) * (d - x) = h ^ 2 := by linear_combination hD
  have hV : (b - y) * (b + y) = h ^ 2 := by linear_combination hB
  have hd1p : 0 < d - x := by omega
  have hd2p : 0 < b + y := by omega
  have hd2h : b + y < h := by
    by_contra hge
    push_neg at hge
    have h1 : (b - y) * h ≤ (b - y) * (b + y) := mul_le_mul_of_nonneg_left hge (by omega)
    have h2 : h * h < (b - y) * h := mul_lt_mul_of_pos_right (by omega) (by omega)
    nlinarith
  have hd12 : d - x < b + y := by
    by_contra hge
    push_neg at hge
    have : d + x ≤ b - y := by
      by_contra hlt
      push_neg at hlt
      have : (b - y) * (b + y) < (d + x) * (d - x) := mul_lt_mul hlt hge (by omega) (by omega)
      nlinarith
    omega
  have hid : 4 * c * (h - 2) * ((d - x) * (b + y)) =
      (h ^ 2 + (d - x) * (b + y)) * (h * (d - x) - (h - 4) * (b + y)) := by
    linear_combination (2 * (d - x) * (b + y)) * hE' - ((h - 4) * (b + y)) * hD + (h * (d - x)) * hB
  have hpp : 0 < (d - x) * (b + y) := mul_pos hd1p hd2p
  have hpos : 0 < h * (d - x) - (h - 4) * (b + y) := by
    have h1 : 0 < 4 * c * (h - 2) * ((d - x) * (b + y)) := by
      have : 0 < 4 * c * (h - 2) := mul_pos (mul_pos (by norm_num) (by omega)) (by omega)
      positivity
    have h2 : 0 < h ^ 2 + (d - x) * (b + y) := by positivity
    rw [hid] at h1
    exact (pos_iff_pos_of_mul_pos h1).mp h2
  have hlt4 : h * ((b + y) - (d - x)) < 4 * (b + y) := by linarith
  have hdiff4 : (b + y) - (d - x) < 4 := by
    by_contra hge
    push_neg at hge
    have := mul_le_mul_of_nonneg_left hge (show (0 : ℤ) ≤ h by omega)
    linarith
  -- parity: d - x and b + y both have the parity of h
  have par1 : 2 ∣ h - (d - x) := by
    obtain ⟨k1, hk1⟩ := (Int.even_mul_pred_self h).two_dvd
    obtain ⟨k2, hk2⟩ := (Int.even_mul_pred_self (d - x)).two_dvd
    exact ⟨k2 - k1 + x * (d - x), by linear_combination hk1 * (-1) + hk2 - hU⟩
  have par2 : 2 ∣ h - (b + y) := by
    obtain ⟨k1, hk1⟩ := (Int.even_mul_pred_self h).two_dvd
    obtain ⟨k2, hk2⟩ := (Int.even_mul_pred_self (b + y)).two_dvd
    exact ⟨k2 - k1 - y * (b + y), by linear_combination hk1 * (-1) + hk2 - hV⟩
  have hdiff : (b + y) - (d - x) = 2 := by omega
  have h2e : h < 2 * (b + y) := by rw [hdiff] at hlt4; linarith
  -- w = (d + x) - (b - y)
  have hw : ((d + x) - (b - y)) * ((d - x) * (b + y)) = 2 * h ^ 2 := by
    linear_combination (b + y) * hU - (d - x) * hV + h ^ 2 * hdiff
  have hcw : 4 * c * (h - 2) = ((d + x) - (b - y) + 2) * (2 * (b + y) - h) := by
    have key : 4 * c * (h - 2) * ((d - x) * (b + y)) =
        ((d + x) - (b - y) + 2) * (2 * (b + y) - h) * ((d - x) * (b + y)) := by
      rw [hid]
      have hd1 : d - x = (b + y) - 2 := by linarith
      rw [hd1] at hw ⊢
      linear_combination (h - 2 * (b + y)) * hw
    exact mul_right_cancel₀ (ne_of_gt hpp) key
  obtain ⟨w, hwdef⟩ : ∃ w, w = (d + x) - (b - y) := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e, e = b + y := ⟨_, rfl⟩
  rw [← hwdef, ← hedef] at hcw
  have hd1e : d - x = e - 2 := by omega
  rw [← hwdef, hd1e, ← hedef] at hw
  rw [hd1e] at hU
  rw [← hedef] at hV hd2h h2e
  have he3 : 3 ≤ e := by omega
  have hc1 : 4 * (h - 2) ≤ (w + 2) * (2 * e - h) := by
    have := mul_le_mul_of_nonneg_right (show (4 : ℤ) * 1 ≤ 4 * c by omega)
      (show (0 : ℤ) ≤ h - 2 by omega)
    linarith
  have hh36 : h ≤ 36 := by
    by_contra hgt
    push_neg at hgt
    exact bigh w e h hgt he3 hd2h h2e hw hc1
  have hwdiv : 2 * h ^ 2 / ((e - 2) * e) = w := by
    rw [← hw]
    exact Int.mul_ediv_cancel _ (ne_of_gt (mul_pos (by omega) (by omega)))
  have hfin := caseB_finite h (by simp; omega) e (by simp; omega) hd2h h2e
    ⟨d + x, by linear_combination -hU⟩ ⟨b - y, by linear_combination -hV⟩
    ⟨w, by linear_combination -hw⟩ ⟨c, by rw [hwdiv]; linear_combination -hcw⟩
  rw [hwdiv] at hfin
  linarith

/-! ## The theorem -/

theorem conjecture :
    ∀ a c h x y b d : ℤ, IsSol a c h x y b d ↔ (a, c, h, x, y, b, d) ∈ sols := by
  intro a c h x y b d
  constructor
  · intro hs
    rcases le_total y x with hxy | hxy
    · rcases lt_or_ge y 0 with hy | hy
      · exact (caseB hs hy).elim
      · exact caseA hs hy hxy
    · have hm := mirror hs
      rcases lt_or_ge x 0 with hx | hx
      · exact (caseB hm hx).elim
      · exact sols_mirror _ (caseA hm hx hxy)
  · intro hm
    exact sols_sound _ hm

end OMA.S_oeis_a374594

theorem OMA.solution : type_of% @OMA.S_oeis_a374594.main :=
  OMA.S_oeis_a374594.conjecture
