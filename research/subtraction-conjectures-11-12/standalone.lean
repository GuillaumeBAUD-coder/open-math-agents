import Mathlib



/-!
Proposed formal proof; registry registration pending. Definition 2 (two-action specialisation) of Bhagat, Kulkarni,
Larsson and Murali, arXiv:2510.24280v2, pp.4--5. The mover maximises their own
cumulation, then maximises (friendly=true) or minimises (friendly=false) the
other player's cumulation among tied moves. The conventions swap in the
recursive call. For positive a<b this is precisely the paper's outcome for
S={a,b}. A zero action is guarded only to make the total definition well founded;
it is excluded from every mathematical theorem below.
-/
namespace Conj11

def move (s : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (s + v.2, v.1)

def choose (friendly : Bool) (u v : ℕ × ℕ) : ℕ × ℕ :=
  if u.1 < v.1 then v else if v.1 < u.1 then u
  else if friendly then (u.1, max u.2 v.2) else (u.1, min u.2 v.2)

def outcome (a b : ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  if h < a then (0, 0) else
    let u := move a (if h - a < h then outcome a b c₂ c₁ (h-a) else (0, 0))
    if h < b then u else
      choose c₁ u (move b (if h - b < h then outcome a b c₂ c₁ (h-b) else (0, 0)))
termination_by h

theorem outcome_of_lt (a b h : ℕ) (c₁ c₂ : Bool) (hh : h < a) :
    outcome a b c₁ c₂ h = (0, 0) := by
  rw [outcome]
  simp only [hh, ↓reduceIte]

theorem outcome_of_one (a b h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hah : a ≤ h) (hhb : h < b) :
    outcome a b c₁ c₂ h = move a (outcome a b c₂ c₁ (h-a)) := by
  rw [outcome]
  have hs : h - a < h := by omega
  simp only [Nat.not_lt.mpr hah, hhb, hs, ↓reduceIte]

theorem outcome_of_two (a b h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hb : 0 < b) (hah : a ≤ h) (hbh : b ≤ h) :
    outcome a b c₁ c₂ h =
      choose c₁ (move a (outcome a b c₂ c₁ (h-a)))
        (move b (outcome a b c₂ c₁ (h-b))) := by
  rw [outcome]
  have hsa : h - a < h := by omega
  have hsb : h - b < h := by omega
  simp only [Nat.not_lt.mpr hah, Nat.not_lt.mpr hbh, hsa, hsb, ↓reduceIte]

end Conj11


namespace Conj12Early
open Conj11

/-- Convention-independent early outcomes before the first discrepancy. -/
def early (a d t r : ℕ) : ℕ × ℕ :=
  if r < a then (t*(a+d), t*a+d*min t (r/d))
  else ((t+1)*a+d*min (t+1) ((r-a)/d), t*(a+d))

lemma mul_predecessor_add (t x : ℕ) (ht : 0 < t) :
    (t-1)*x+x=t*x := by
  have ht1 : t-1+1=t := by omega
  calc
    _ = (t-1+1)*x := by ring
    _ = _ := by rw [ht1]

lemma early_low_step (a d t r : ℕ) (c : Bool)
    (hd : 0 < d) (ht : 0 < t) (hr : r < a) :
    choose c (move a (early a d (t-1) (r+(a+d))))
      (move (a+d) (early a d (t-1) (r+a))) = early a d t r := by
  have h1 : ¬ r+(a+d) < a := by omega
  have h2 : ¬ r+a < a := by omega
  have hwin : (move a (early a d (t-1) (r+(a+d)))).1 <
      (move (a+d) (early a d (t-1) (r+a))).1 := by
    simp only [move, early, h1, h2, ↓reduceIte]
    omega
  rw [choose, if_pos hwin]
  have hts : t-1+1=t := by omega
  have hs := mul_predecessor_add t (a+d) ht
  have hrsub : r+a-a=r := by omega
  simp only [move, early, h2, hr, ↓reduceIte, hts, hrsub]
  apply Prod.ext
  · dsimp
    omega
  · rfl


lemma choose_same_second (c : Bool) (x y z : ℕ) :
    choose c (x,z) (y,z) = (max x y,z) := by
  cases c <;> simp only [choose, max_def, min_self, ↓reduceIte] <;>
    split_ifs <;> simp_all <;> omega

lemma early_cut_step (a d t r : ℕ) (c : Bool)
    (hd : 0 < d) (hda : d < a) (ht : 0 < t)
    (har : a ≤ r) (hrb : r < a+d) (hta : t*d < a) :
    choose c (move a (early a d t (r-a)))
      (move (a+d) (early a d (t-1) (r+a))) = early a d t r := by
  have h1 : r-a < a := by omega
  have h2 : ¬ r+a < a := by omega
  have h3 : ¬ r < a := by omega
  have hzero : (r-a)/d=0 := Nat.div_eq_of_lt (by omega)
  have hqr : t ≤ r/d := (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hts : t-1+1=t := by omega
  have hs := mul_predecessor_add t (a+d) ht
  have hsum : t*a+d*t=t*(a+d) := by ring
  have hwin : (move (a+d) (early a d (t-1) (r+a))).1 <
      (move a (early a d t (r-a))).1 := by
    simp only [move, early, h1, h2, ↓reduceIte, hts, hzero, Nat.min_zero,
      Nat.mul_zero, Nat.add_zero]
    nlinarith
  rw [choose, if_neg (by omega), if_pos hwin]
  simp only [move, early, h1, h3, ↓reduceIte, hzero, Nat.min_zero,
    Nat.mul_zero, Nat.add_zero]
  apply Prod.ext
  · dsimp
    ring
  · rfl

lemma early_middle_step (a d t r : ℕ) (c : Bool)
    (hd : 0 < d) (hbr : a+d ≤ r) (hr2 : r < 2*a) :
    choose c (move a (early a d t (r-a)))
      (move (a+d) (early a d t (r-(a+d)))) = early a d t r := by
  have h1 : r-a < a := by omega
  have h2 : r-(a+d) < a := by omega
  have h3 : ¬ r < a := by omega
  let q := (r-a)/d
  have hq : 0 < q := by
    have hx : 1 ≤ (r-a)/d := (Nat.le_div_iff_mul_le hd).2 (by omega)
    dsimp [q]
    omega
  have hs : (r-(a+d))/d=q-1 := by
    have he : r-(a+d)=(r-a)-d := by omega
    rw [he]
    simpa only [Nat.mul_one] using Nat.sub_mul_div (r-a) d 1
  simp only [move, early, h1, h2, h3, ↓reduceIte, hs]
  rw [choose_same_second]
  apply Prod.ext
  · change max (a+(t*a+d*min t q)) ((a+d)+(t*a+d*min t (q-1))) =
      (t+1)*a+d*min (t+1) q
    by_cases hqt : q ≤ t
    · rw [min_eq_right hqt, min_eq_right (by omega : q-1 ≤ t),
        min_eq_right (by omega : q ≤ t+1)]
      have hqd := mul_predecessor_add q d hq
      have he₁ : a+(t*a+d*q)=(t+1)*a+d*q := by ring
      have he₂ : (a+d)+(t*a+d*(q-1))=(t+1)*a+d*q := by nlinarith
      rw [he₁,he₂,max_self]
    · rw [min_eq_left (by omega : t ≤ q), min_eq_left (by omega : t ≤ q-1),
        min_eq_left (by omega : t+1 ≤ q)]
      rw [max_eq_right (by omega : a+(t*a+d*t) ≤ (a+d)+(t*a+d*t))]
      ring
  · rfl

lemma early_last_step (a d t r : ℕ) (c : Bool)
    (hd : 0 < d) (h2r : 2*a ≤ r) (hrL : r < 2*a+d)
    (ht : (t+1)*d ≤ a) :
    choose c (move a (early a d t (r-a)))
      (move (a+d) (early a d t (r-(a+d)))) = early a d t r := by
  have htlin : t*d+d ≤ a := by nlinarith
  have h1 : ¬ r-a < a := by omega
  have h2 : r-(a+d) < a := by omega
  have h3 : ¬ r < a := by omega
  have hzero : (r-a-a)/d=0 := Nat.div_eq_of_lt (by omega)
  have hqb : t ≤ (r-(a+d))/d := (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hqr : t+1 ≤ (r-a)/d := (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hsum : t*a+d*t=t*(a+d) := by ring
  have hwin : (move a (early a d t (r-a))).1 <
      (move (a+d) (early a d t (r-(a+d)))).1 := by
    simp only [move, early, h1, h2, ↓reduceIte, hzero, Nat.min_zero,
      Nat.mul_zero, Nat.add_zero, min_eq_left hqb]
    nlinarith
  rw [choose, if_pos hwin]
  simp only [move, early, h2, h3, ↓reduceIte, min_eq_left hqb, min_eq_left hqr]
  apply Prod.ext
  · dsimp
    ring
  · rfl



lemma outcome_eq_early_aux (a d h : ℕ) (hd : 0 < d) (hda : d < a) :
    ∀ t r : ℕ, h=t*(2*a+d)+r → r < 2*a+d → t*d < a →
      (2*a ≤ r → (t+1)*d ≤ a) →
      ∀ c₁ c₂ : Bool, outcome a (a+d) c₁ c₂ h = early a d t r := by
  have ha : 0 < a := by omega
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro t r he hr ht hlast c₁ c₂
    by_cases hlow : r < a
    · by_cases ht0 : t=0
      · subst t
        rw [outcome_of_lt a (a+d) h c₁ c₂ (by omega)]
        simp [early,hlow]
      · have htp : 0 < t := by omega
        have hts : t-1+1=t := by omega
        have hm := mul_predecessor_add t (2*a+d) htp
        have hmd := mul_predecessor_add t d htp
        have hah : a ≤ h := by omega
        have hbh : a+d ≤ h := by omega
        have hea : h-a=(t-1)*(2*a+d)+(r+(a+d)) := by omega
        have heb : h-(a+d)=(t-1)*(2*a+d)+(r+a) := by omega
        have hca := ih (h-a) (by omega) (t-1) (r+(a+d)) hea
          (by omega) (by omega) (by intro _;rw [hts];omega) c₂ c₁
        have hcb := ih (h-(a+d)) (by omega) (t-1) (r+a) heb
          (by omega) (by omega) (by intro _;rw [hts];omega) c₂ c₁
        rw [outcome_of_two a (a+d) h c₁ c₂ ha (by omega) hah hbh,hca,hcb]
        exact early_low_step a d t r c₁ hd htp hlow
    · by_cases hcut : r < a+d
      · by_cases ht0 : t=0
        · subst t
          have hah : a ≤ h := by omega
          have hhb : h < a+d := by omega
          have hchild : h-a < a := by omega
          have hzero : (r-a)/d=0 := Nat.div_eq_of_lt (by omega)
          rw [outcome_of_one a (a+d) h c₁ c₂ ha hah hhb,
            outcome_of_lt a (a+d) (h-a) c₂ c₁ hchild]
          simp [move,early,hlow,hzero]
        · have htp : 0 < t := by omega
          have hts : t-1+1=t := by omega
          have hm := mul_predecessor_add t (2*a+d) htp
          have hmd := mul_predecessor_add t d htp
          have hah : a ≤ h := by omega
          have hbh : a+d ≤ h := by omega
          have hea : h-a=t*(2*a+d)+(r-a) := by omega
          have heb : h-(a+d)=(t-1)*(2*a+d)+(r+a) := by omega
          have hca := ih (h-a) (by omega) t (r-a) hea
            (by omega) ht (by intro hc;omega) c₂ c₁
          have hcb := ih (h-(a+d)) (by omega) (t-1) (r+a) heb
            (by omega) (by omega) (by intro _;rw [hts];omega) c₂ c₁
          rw [outcome_of_two a (a+d) h c₁ c₂ ha (by omega) hah hbh,hca,hcb]
          exact early_cut_step a d t r c₁ hd hda htp (by omega) hcut ht
      · by_cases hmid : r < 2*a
        · have hah : a ≤ h := by omega
          have hbh : a+d ≤ h := by omega
          have hea : h-a=t*(2*a+d)+(r-a) := by omega
          have heb : h-(a+d)=t*(2*a+d)+(r-(a+d)) := by omega
          have hca := ih (h-a) (by omega) t (r-a) hea
            (by omega) ht (by intro hc;omega) c₂ c₁
          have hcb := ih (h-(a+d)) (by omega) t (r-(a+d)) heb
            (by omega) ht (by intro hc;omega) c₂ c₁
          rw [outcome_of_two a (a+d) h c₁ c₂ ha (by omega) hah hbh,hca,hcb]
          exact early_middle_step a d t r c₁ hd (by omega) hmid
        · have hah : a ≤ h := by omega
          have hbh : a+d ≤ h := by omega
          have hea : h-a=t*(2*a+d)+(r-a) := by omega
          have heb : h-(a+d)=t*(2*a+d)+(r-(a+d)) := by omega
          have hca := ih (h-a) (by omega) t (r-a) hea
            (by omega) ht (by intro hc;omega) c₂ c₁
          have hcb := ih (h-(a+d)) (by omega) t (r-(a+d)) heb
            (by omega) ht (by intro hc;omega) c₂ c₁
          rw [outcome_of_two a (a+d) h c₁ c₂ ha (by omega) hah hbh,hca,hcb]
          exact early_last_step a d t r c₁ hd (by omega) hr (hlast (by omega))

theorem outcome_eq_early (a d t r : ℕ) (c₁ c₂ : Bool)
    (hd : 0 < d) (hda : d < a) (hr : r < 2*a+d) (ht : t*d < a)
    (hlast : 2*a ≤ r → (t+1)*d ≤ a) :
    outcome a (a+d) c₁ c₂ (t*(2*a+d)+r) = early a d t r :=
  outcome_eq_early_aux a d _ hd hda t r rfl hr ht hlast c₁ c₂

end Conj12Early


/-!
Proposed formal proof; registry registration pending. Definition 2 (two-action specialisation) of Bhagat, Kulkarni,
Larsson and Murali, arXiv:2510.24280v2, pp.4--5. The mover maximises their own
cumulation, then maximises (friendly=true) or minimises (friendly=false) the
other player's cumulation among tied moves. The conventions swap in the
recursive call. For positive a<b this is precisely the paper's outcome for
S={a,b}. A zero action is guarded only to make the total definition well founded;
it is excluded from every mathematical theorem below.
-/


open Conj11

namespace Conj12Assembly

def Core (a d : ℕ) : Prop :=
  ∀ (t r : ℕ) (c₁ c₂ : Bool), 0 < d → d < a → r < 2 * a + d → t * d < a →
    (2 * a ≤ r → (t + 1) * d ≤ a) →
    outcome a (a + d) c₁ c₂ (t * (2 * a + d) + r) = Conj12Early.early a d t r

theorem all_conventions_before (a d n h : ℕ) (hd : 0 < d) (hda : d < a)
    (hnd : n * d < a) (hcore : Core a d)
    (hh : h < n * (2 * a + d) + 2 * a) (c₁ c₂ : Bool) :
    outcome a (a + d) c₁ c₂ h = outcome a (a + d) true true h := by
  let L := 2 * a + d
  let t := h / L
  let r := h % L
  have hL : 0 < L := by dsimp [L]; omega
  have hr : r < L := Nat.mod_lt _ hL
  have hrep : h = t * L + r := by
    dsimp [t, r]
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div h L).symm
  have hbig : h < (n + 1) * L := by
    change h < n * L + 2 * a at hh
    calc
      h < n * L + 2 * a := hh
      _ < n * L + L := by dsimp [L]; omega
      _ = (n + 1) * L := by ring
  have htn : t ≤ n := by
    have hx := (Nat.div_lt_iff_lt_mul hL).2 hbig
    dsimp [t]
    omega
  have ht : t * d < a := (Nat.mul_le_mul_right d htn).trans_lt hnd
  have hlast : 2 * a ≤ r → (t + 1) * d ≤ a := by
    intro hlarge
    have htn' : t < n := by
      by_contra hnot
      have hteq : t = n := by omega
      rw [hteq] at hrep
      change h < n * L + 2 * a at hh
      omega
    exact (Nat.mul_le_mul_right d (show t + 1 ≤ n by omega)).trans hnd.le
  rw [hrep, hcore t r c₁ c₂ hd hda hr ht hlast,
    hcore t r true true hd hda hr ht hlast]

theorem endpoint_outcomes (a d n : ℕ) (hd : 0 < d) (hda : d < a) (hn : 0 < n)
    (hnd : n * d < a) (hupper : a < (n + 1) * d) (hcore : Core a d) :
    let H := n * (2 * a + d) + 2 * a
    outcome a (a + d) true true H = (a + n * (a + d), (n + 1) * a) ∧
      outcome a (a + d) false false H = (a + n * (a + d), n * (a + d)) := by
  dsimp only
  let H := n * (2 * a + d) + 2 * a
  have ha : 0 < a := by omega
  have hdiv : a / d = n := by
    have hlo := (Nat.le_div_iff_mul_le hd).2 hnd.le
    have hhi := (Nat.div_lt_iff_lt_mul hd).2 hupper
    omega
  have hsubdiv : (a - d) / d = n - 1 := by
    simpa only [Nat.mul_one, hdiv] using (Nat.sub_mul_div a d 1)
  have hcalc : n * a + d * (n - 1) = n * (a + d) - d := by
    have hn1 : n - 1 + 1 = n := by omega
    have hx : d * (n - 1) + d = n * d := by
      calc
        _ = d * (n - 1 + 1) := by ring
        _ = _ := by rw [hn1]; ring
    have hy : n * (a + d) = n * a + n * d := by ring
    omega
  have hchilda (c₁ c₂ : Bool) :
      outcome a (a + d) c₁ c₂ (H - a) = ((n + 1) * a, n * (a + d)) := by
    have he : H - a = n * (2 * a + d) + a := by dsimp [H]; omega
    rw [he, hcore n a c₁ c₂ hd hda (by omega) hnd (by omega)]
    simp [Conj12Early.early]
  have hchildb (c₁ c₂ : Bool) :
      outcome a (a + d) c₁ c₂ (H - (a + d)) =
        (n * (a + d), n * (a + d) - d) := by
    have he : H - (a + d) = n * (2 * a + d) + (a - d) := by dsimp [H]; omega
    have hr : a - d < a := by omega
    rw [he, hcore n (a - d) c₁ c₂ hd hda (by omega) hnd (by omega)]
    simp only [Conj12Early.early, if_pos hr, hsubdiv,
      Nat.min_eq_right (Nat.sub_le n 1), hcalc]
  have hlegal : a + d ≤ H := by dsimp [H]; omega
  have hown : (a + d) + (n * (a + d) - d) = a + n * (a + d) := by
    have hx := Nat.mul_le_mul_right (a + d) (show 1 ≤ n by omega)
    simp only [one_mul] at hx
    omega
  have hopp : n * (a + d) < (n + 1) * a := by nlinarith
  constructor
  · rw [outcome_of_two a (a + d) H true true ha (by omega) (by omega) hlegal,
      hchilda, hchildb]
    simp [move, choose, hown, Nat.max_eq_left hopp.le]
  · rw [outcome_of_two a (a + d) H false false ha (by omega) (by omega) hlegal,
      hchilda, hchildb]
    simp [move, choose, hown, Nat.min_eq_right hopp.le]

theorem first_discrepancy (a d n : ℕ) (hd : 0 < d) (hda : d < a) (hn : 0 < n)
    (hnd : n * d < a) (hupper : a < (n + 1) * d) (hcore : Core a d) :
    IsLeast {h : ℕ | outcome a (a + d) true true h ≠
        outcome a (a + d) false false h} (n * (2 * a + d) + 2 * a) := by
  have he := endpoint_outcomes a d n hd hda hn hnd hupper hcore
  dsimp only at he
  constructor
  · intro hsame
    rw [he.1, he.2] at hsame
    have hs := congrArg Prod.snd hsame
    simp only at hs
    nlinarith
  · intro h hdis
    by_contra hnot
    have hh : h < n * (2 * a + d) + 2 * a := by omega
    exact hdis (all_conventions_before a d n h hd hda hnd hcore hh false false).symm

end Conj12Assembly

open Conj11

namespace Conj12Complete

theorem core_proved (a d : ℕ) : Conj12Assembly.Core a d := by
  intro t r c₁ c₂ hd hda hr ht hlast
  exact Conj12Early.outcome_eq_early a d t r c₁ c₂ hd hda hr ht hlast

theorem conjecture_12 (a d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (hnd : n * d < a) (hupper : a < (n + 1) * d) :
    IsLeast {h : ℕ | outcome a (a + d) true true h ≠
        outcome a (a + d) false false h} ((n + 2) * a + n * (a + d)) := by
  have hda : d < a := by
    have hx := Nat.mul_le_mul_right d (show 1 ≤ n by omega)
    simp only [one_mul] at hx
    omega
  have hformula : n * (2 * a + d) + 2 * a = (n + 2) * a + n * (a + d) := by ring
  simpa only [hformula] using
    Conj12Assembly.first_discrepancy a d n hd hda hn hnd hupper (core_proved a d)

/-- Original source parameters, with the two strict ratio inequalities
expressed by positive-denominator integer cross multiplication. -/
theorem original_ratio_first_discrepancy (a b n : ℕ) (_ha : 0 < a) (hn : 0 < n)
    (hsmall : n * b < (n + 1) * a) (hlarge : (n + 2) * a < (n + 1) * b) :
    IsLeast {h : ℕ | outcome a b true true h ≠ outcome a b false false h}
      ((n + 2) * a + n * b) := by
  have hab : a < b := by
    by_contra hx
    have hba : b ≤ a := by omega
    have hm := Nat.mul_le_mul_left (n + 1) hba
    nlinarith
  let d := b - a
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hbd : b = a + d := by dsimp [d]; omega
  have hnd : n * d < a := by rw [hbd] at hsmall; nlinarith
  have hupper : a < (n + 1) * d := by rw [hbd] at hlarge; nlinarith
  simpa only [← hbd] using conjecture_12 a d n hd hn hnd hupper

theorem nonresonant_parameters (a b : ℕ) (hab : a < b) (hdom : b < 2 * a)
    (hnon : ∀ k : ℕ, 0 < k → b * k ≠ a * (k + 1)) :
    ∃ n : ℕ, 0 < n ∧ n * b < (n + 1) * a ∧ (n + 2) * a < (n + 1) * b := by
  let d := b - a
  let n := a / d
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hbd : b = a + d := by dsimp [d]; omega
  have hda : d < a := by omega
  have hn : 0 < n := by
    have hx : 1 ≤ a / d := (Nat.le_div_iff_mul_le hd).2 (by simpa using hda.le)
    dsimp [n]
    omega
  have hndle : n * d ≤ a := Nat.div_mul_le_self a d
  have hnd : n * d < a := by
    by_contra hx
    have heq : n * d = a := by omega
    apply hnon n hn
    rw [hbd, ← heq]
    ring
  have hupper : a < (n + 1) * d := by
    apply (Nat.div_lt_iff_lt_mul hd).1
    change n < n + 1
    omega
  refine ⟨n, hn, ?_, ?_⟩ <;> rw [hbd] <;> nlinarith

/-- The complete original nonresonant source claim, including existence
of the positive interval index and the least distinguishing heap. -/
theorem original_conjecture_12 (a b : ℕ) (ha : 0 < a) (hab : a < b) (hdom : b < 2 * a)
    (hnon : ∀ k : ℕ, 0 < k → b * k ≠ a * (k + 1)) :
    ∃ n : ℕ, 0 < n ∧ n * b < (n + 1) * a ∧ (n + 2) * a < (n + 1) * b ∧
      IsLeast {h : ℕ | outcome a b true true h ≠ outcome a b false false h}
        ((n + 2) * a + n * b) := by
  obtain ⟨n, hn, hs, hl⟩ := nonresonant_parameters a b hab hdom hnon
  exact ⟨n, hn, hs, hl, original_ratio_first_discrepancy a b n ha hn hs hl⟩

end Conj12Complete


/-!
Proposed formal proof; registry registration pending. Definition 2 (two-action specialisation) of Bhagat, Kulkarni,
Larsson and Murali, arXiv:2510.24280v2, pp.4--5. The mover maximises their own
cumulation, then maximises (friendly=true) or minimises (friendly=false) the
other player's cumulation among tied moves. The conventions swap in the
recursive call. For positive a<b this is precisely the paper's outcome for
S={a,b}. A zero action is guarded only to make the total definition well founded;
it is excluded from every mathematical theorem below.
-/


namespace Conj11Early

open Conj11

/-- The early closed form, used only with t≤k and r<2k+1. -/
def early (k t r : ℕ) : ℕ × ℕ :=
  let A := t * (k+1)
  if r < k then (A, A - (t-r)) else (A + min (k+1) (r-t), A)

lemma base_shift (k t : ℕ) (ht : 0 < t) :
    (t-1)*(k+1)+(k+1)=t*(k+1) := by
  have ht1 : t-1+1=t := by omega
  calc
    _ = (t-1+1)*(k+1) := by ring
    _ = _ := by rw [ht1]

lemma early_low_step (k t r : ℕ) (c : Bool)
    (hk : 0 < k) (ht : 0 < t) (htk : t ≤ k) (hr : r < k) :
    choose c
      (move k (early k (t-1) (r+k+1)))
      (move (k+1) (early k (t-1) (r+k))) = early k t r := by
  have hs := base_shift k t ht
  have h1 : ¬ r+k+1 < k := by omega
  have h2 : ¬ r+k < k := by omega
  cases c <;>
    simp only [early, move, h1, h2, hr, ↓reduceIte, choose, min_def, max_def] <;>
    split_ifs <;> simp_all <;> omega

lemma early_middle_step (k t r : ℕ) (c : Bool)
    (_hk : 0 < k) (htk : t ≤ k) (hr : k < r) (hr2 : r < 2*k) :
    choose c
      (move k (early k t (r-k)))
      (move (k+1) (early k t (r-(k+1)))) = early k t r := by
  have hA : t ≤ t*(k+1) := by nlinarith
  have h1 : r-k < k := by omega
  have h2 : r-(k+1) < k := by omega
  have h3 : ¬ r < k := by omega
  cases c <;>
    simp only [early, move, h1, h2, h3, ↓reduceIte, choose, min_def, max_def] <;>
    split_ifs <;> simp_all <;> omega

lemma early_cut_step (k t : ℕ) (c : Bool)
    (hk : 0 < k) (ht : 0 < t) (htk : t ≤ k) :
    choose c
      (move k (early k t 0))
      (move (k+1) (early k (t-1) (2*k))) = early k t k := by
  have hs := base_shift k t ht
  have h1 : ¬ 2*k < k := by omega
  have h2 : ¬ k < k := by omega
  cases c <;>
    simp only [early, move, hk, h1, h2, ↓reduceIte, choose, min_def, max_def] <;>
    split_ifs <;> simp_all <;> omega

lemma early_last_step (k t : ℕ) (c : Bool)
    (hk : 0 < k) (htk : t ≤ k) :
    choose c
      (move k (early k t k))
      (move (k+1) (early k t (k-1))) = early k t (2*k) := by
  have hA : t ≤ t*(k+1) := by nlinarith
  have h1 : ¬ 2*k < k := by omega
  have h2 : ¬ k < k := by omega
  have h3 : k-1 < k := by omega
  cases c <;>
    simp only [early, move, h1, h2, h3, ↓reduceIte, choose, min_def, max_def] <;>
    split_ifs <;> simp_all <;> omega



lemma outcome_eq_early_aux (k h : ℕ) (hk : 0 < k) :
    ∀ t r : ℕ, h = t*(2*k+1)+r → t ≤ k → r < 2*k+1 →
      ∀ c₁ c₂ : Bool, outcome k (k+1) c₁ c₂ h = early k t r := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro t r he ht hr c₁ c₂
    by_cases hlow : r < k
    · by_cases ht0 : t = 0
      · subst t
        have hh : h < k := by omega
        rw [outcome_of_lt k (k+1) h c₁ c₂ hh]
        simp [early, hlow]
      · have htp : 0 < t := by omega
        have hm : (t-1)*(2*k+1)+(2*k+1)=t*(2*k+1) := by
          have htx : t-1+1=t := by omega
          calc
            _ = (t-1+1)*(2*k+1) := by ring
            _ = _ := by rw [htx]
        have ha : k ≤ h := by omega
        have hb : k+1 ≤ h := by omega
        have hea : h-k = (t-1)*(2*k+1)+(r+k+1) := by omega
        have heb : h-(k+1) = (t-1)*(2*k+1)+(r+k) := by omega
        have hca := ih (h-k) (by omega) (t-1) (r+k+1) hea
          (by omega) (by omega) c₂ c₁
        have hcb := ih (h-(k+1)) (by omega) (t-1) (r+k) heb
          (by omega) (by omega) c₂ c₁
        rw [outcome_of_two k (k+1) h c₁ c₂ hk (by omega) ha hb, hca, hcb]
        exact early_low_step k t r c₁ hk htp ht hlow
    · by_cases hcut : r = k
      · subst r
        by_cases ht0 : t = 0
        · subst t
          have hh : h = k := by omega
          rw [hh]
          rw [outcome_of_one k (k+1) k c₁ c₂ hk (by omega) (by omega)]
          rw [Nat.sub_self, outcome_of_lt k (k+1) 0 c₂ c₁ hk]
          simp [move, early]
        · have htp : 0 < t := by omega
          have hm : (t-1)*(2*k+1)+(2*k+1)=t*(2*k+1) := by
            have htx : t-1+1=t := by omega
            calc
              _ = (t-1+1)*(2*k+1) := by ring
              _ = _ := by rw [htx]
          have ha : k ≤ h := by omega
          have hb : k+1 ≤ h := by omega
          have hea : h-k = t*(2*k+1)+0 := by omega
          have heb : h-(k+1) = (t-1)*(2*k+1)+(2*k) := by omega
          have hca := ih (h-k) (by omega) t 0 hea ht (by omega) c₂ c₁
          have hcb := ih (h-(k+1)) (by omega) (t-1) (2*k) heb
            (by omega) (by omega) c₂ c₁
          rw [outcome_of_two k (k+1) h c₁ c₂ hk (by omega) ha hb, hca, hcb]
          exact early_cut_step k t c₁ hk htp ht
      · by_cases hlast : r = 2*k
        · subst r
          have ha : k ≤ h := by omega
          have hb : k+1 ≤ h := by omega
          have hea : h-k = t*(2*k+1)+k := by omega
          have heb : h-(k+1) = t*(2*k+1)+(k-1) := by omega
          have hca := ih (h-k) (by omega) t k hea ht (by omega) c₂ c₁
          have hcb := ih (h-(k+1)) (by omega) t (k-1) heb ht (by omega) c₂ c₁
          rw [outcome_of_two k (k+1) h c₁ c₂ hk (by omega) ha hb, hca, hcb]
          exact early_last_step k t c₁ hk ht
        · have hmid : k < r := by omega
          have hmid2 : r < 2*k := by omega
          have ha : k ≤ h := by omega
          have hb : k+1 ≤ h := by omega
          have hea : h-k = t*(2*k+1)+(r-k) := by omega
          have heb : h-(k+1) = t*(2*k+1)+(r-(k+1)) := by omega
          have hca := ih (h-k) (by omega) t (r-k) hea ht (by omega) c₂ c₁
          have hcb := ih (h-(k+1)) (by omega) t (r-(k+1)) heb ht (by omega) c₂ c₁
          rw [outcome_of_two k (k+1) h c₁ c₂ hk (by omega) ha hb, hca, hcb]
          exact early_middle_step k t r c₁ hk ht hmid hmid2

theorem outcome_eq_early (k t r : ℕ) (c₁ c₂ : Bool)
    (hk : 0 < k) (ht : t ≤ k) (hr : r < 2*k+1) :
    outcome k (k+1) c₁ c₂ (t*(2*k+1)+r) = early k t r :=
  outcome_eq_early_aux k _ hk t r rfl ht hr c₁ c₂

lemma early_base_total (k r : ℕ) (hk : 0 < k) (hr : r ≤ k) :
    (early k (k-1) r).1 + (early k (k-1) r).2 = (k-1)*(2*k+1)+r := by
  have hbase : (k-1)*(2*k+1)+(k-1)=2*((k-1)*(k+1)) := by ring
  have hA : k-1 ≤ (k-1)*(k+1) := by nlinarith
  simp only [early, min_def]
  split_ifs <;> simp_all <;> omega

theorem base_block_all_conventions (k h : ℕ) (hk : 0 < k)
    (hlo : (k-1)*(2*k+1) ≤ h) (hhi : h ≤ (k-1)*(2*k+1)+k) :
    ∃ v : ℕ × ℕ, (∀ c₁ c₂ : Bool, outcome k (k+1) c₁ c₂ h = v) ∧
      v.1 + v.2 = h := by
  let r := h-(k-1)*(2*k+1)
  have hr : r ≤ k := by dsimp [r]; omega
  have he : h = (k-1)*(2*k+1)+r := by dsimp [r]; omega
  refine ⟨early k (k-1) r, ?_, ?_⟩
  · intro c₁ c₂
    rw [he]
    exact outcome_eq_early k (k-1) r c₁ c₂ hk (by omega) (by omega)
  · rw [early_base_total k r hk hr, ← he]

end Conj11Early


/-!
Proposed formal proof; registry registration pending. Definition 2 (two-action specialisation) of Bhagat, Kulkarni,
Larsson and Murali, arXiv:2510.24280v2, pp.4--5. The mover maximises their own
cumulation, then maximises (friendly=true) or minimises (friendly=false) the
other player's cumulation among tied moves. The conventions swap in the
recursive call. For positive a<b this is precisely the paper's outcome for
S={a,b}. A zero action is guarded only to make the total definition well founded;
it is excluded from every mathematical theorem below.
-/

open Conj11

namespace Conj11Extension

theorem choose_independent_of_convention (u v : ℕ × ℕ) (c : Bool)
    (htotal : u.1 + u.2 = v.1 + v.2) :
    choose c u v = choose true u v := by
  by_cases huv : u.1 < v.1
  · simp [choose, huv]
  by_cases hvu : v.1 < u.1
  · simp [choose, huv, hvu]
  have heq : u = v := by
    apply Prod.ext <;> omega
  subst v
  cases c <;> simp [choose]

theorem choose_preserves_total (u v : ℕ × ℕ) (c : Bool) (h : ℕ)
    (hu : u.1 + u.2 = h) (hv : v.1 + v.2 = h) :
    (choose c u v).1 + (choose c u v).2 = h := by
  by_cases huv : u.1 < v.1
  · simpa [choose, huv] using hv
  by_cases hvu : v.1 < u.1
  · simpa [choose, huv, hvu] using hu
  have heq : u = v := by
    apply Prod.ext <;> omega
  subst v
  cases c <;> simpa [choose] using hu

/-- Once all profiles coincide and exhaust the heap on one full move-length
block, equality and exhaustion persist forever. No explicit eventual formula
is assumed or needed. -/
theorem eventual_convention_independence (k T : ℕ) (hk : 0 < k)
    (hbase : ∀ h : ℕ, T ≤ h → h ≤ T + k →
      (∀ c₁ c₂ : Bool,
        outcome k (k + 1) c₁ c₂ h = outcome k (k + 1) true true h) ∧
      (outcome k (k + 1) true true h).1 +
        (outcome k (k + 1) true true h).2 = h) :
    ∀ h : ℕ, T ≤ h →
      (∀ c₁ c₂ : Bool,
        outcome k (k + 1) c₁ c₂ h = outcome k (k + 1) true true h) ∧
      (outcome k (k + 1) true true h).1 +
        (outcome k (k + 1) true true h).2 = h := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hT
    by_cases hsmall : h ≤ T + k
    · exact hbase h hT hsmall
    have hb : k + 1 ≤ h := by omega
    have hak : h - k < h := by omega
    have hab : h - (k + 1) < h := by omega
    have hTk : T ≤ h - k := by omega
    have hTb : T ≤ h - (k + 1) := by omega
    obtain ⟨heqk, hsumk⟩ := ih (h - k) hak hTk
    obtain ⟨heqb, hsumb⟩ := ih (h - (k + 1)) hab hTb
    let u := move k (outcome k (k + 1) true true (h - k))
    let v := move (k + 1) (outcome k (k + 1) true true (h - (k + 1)))
    have hu : u.1 + u.2 = h := by
      dsimp [u, move]
      omega
    have hv : v.1 + v.2 = h := by
      dsimp [v, move]
      omega
    have hstep (c₁ c₂ : Bool) : outcome k (k + 1) c₁ c₂ h = choose c₁ u v := by
      rw [outcome_of_two k (k + 1) h c₁ c₂ hk (by omega) (by omega) hb]
      rw [heqk c₂ c₁, heqb c₂ c₁]
    refine ⟨?_, ?_⟩
    · intro c₁ c₂
      rw [hstep c₁ c₂, hstep true true]
      exact choose_independent_of_convention u v c₁ (hu.trans hv.symm)
    · rw [hstep true true]
      exact choose_preserves_total u v true h hu hv

end Conj11Extension

open Conj11

namespace Conj11Result

theorem normalized_all_conventions (k h : ℕ) (hk : 0 < k) (c₁ c₂ : Bool) :
    outcome k (k + 1) c₁ c₂ h = outcome k (k + 1) true true h := by
  let T := (k - 1) * (2 * k + 1)
  by_cases hearly : h < T
  · let t := h / (2 * k + 1)
    let r := h % (2 * k + 1)
    have hL : 0 < 2 * k + 1 := by omega
    have ht : t ≤ k := by
      have hx : h / (2 * k + 1) < k - 1 :=
        (Nat.div_lt_iff_lt_mul hL).2 hearly
      dsimp [t]
      omega
    have hr : r < 2 * k + 1 := Nat.mod_lt _ hL
    have heq : h = t * (2 * k + 1) + r := by
      dsimp [t, r]
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div h (2 * k + 1)).symm
    rw [heq, Conj11Early.outcome_eq_early k t r c₁ c₂ hk ht hr,
      Conj11Early.outcome_eq_early k t r true true hk ht hr]
  · have hbase : ∀ j : ℕ, T ≤ j → j ≤ T + k →
        (∀ d₁ d₂ : Bool,
          outcome k (k + 1) d₁ d₂ j = outcome k (k + 1) true true j) ∧
        (outcome k (k + 1) true true j).1 +
          (outcome k (k + 1) true true j).2 = j := by
      intro j hlo hhi
      obtain ⟨v, hv, hsum⟩ := Conj11Early.base_block_all_conventions k j hk hlo hhi
      constructor
      · intro d₁ d₂
        rw [hv d₁ d₂, hv true true]
      · rw [hv true true]
        exact hsum
    exact (Conj11Extension.eventual_convention_independence k T hk hbase h
      (by omega)).1 c₁ c₂

end Conj11Result


namespace Conj11Scaling
open Conj11

def scale (d : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (d*v.1,d*v.2)

lemma move_scale (d s : ℕ) (v : ℕ × ℕ) :
    move (d*s) (scale d v) = scale d (move s v) := by
  ext <;> simp [move, scale, Nat.mul_add]

lemma choose_scale (d : ℕ) (hd : 0 < d) (c : Bool) (u v : ℕ × ℕ) :
    choose c (scale d u) (scale d v) = scale d (choose c u v) := by
  by_cases huv : u.1 < v.1
  · have huv' : (scale d u).1 < (scale d v).1 := (Nat.mul_lt_mul_left hd).2 huv
    rw [choose, if_pos huv', choose, if_pos huv]
  · have huv' : ¬ (scale d u).1 < (scale d v).1 := by
      simpa only [scale, Nat.mul_lt_mul_left hd] using huv
    by_cases hvu : v.1 < u.1
    · have hvu' : (scale d v).1 < (scale d u).1 := (Nat.mul_lt_mul_left hd).2 hvu
      rw [choose, if_neg huv', if_pos hvu', choose, if_neg huv, if_pos hvu]
    · have hvu' : ¬ (scale d v).1 < (scale d u).1 := by
        simpa only [scale, Nat.mul_lt_mul_left hd] using hvu
      rw [choose, if_neg huv', if_neg hvu', choose, if_neg huv, if_neg hvu]
      cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, scale, mul_min, mul_max]

theorem outcome_scale (a b d h : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∀ c₁ c₂ : Bool, outcome (d*a) (d*b) c₁ c₂ h =
      scale d (outcome a b c₁ c₂ (h/d)) := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro c₁ c₂
    have hdapos : 0 < d*a := Nat.mul_pos hd ha
    have hdbpos : 0 < d*b := Nat.mul_pos hd hb
    by_cases hlt : h < d*a
    · have hqa : h/d < a := (Nat.div_lt_iff_lt_mul hd).2 (by simpa [Nat.mul_comm] using hlt)
      rw [outcome_of_lt (d*a) (d*b) h c₁ c₂ hlt,
        outcome_of_lt a b (h/d) c₁ c₂ hqa]
      simp [scale]
    · have hda : d*a ≤ h := by omega
      have hqa : a ≤ h/d := (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hda)
      have hca := ih (h-d*a) (by omega) c₂ c₁
      rw [Nat.sub_mul_div] at hca
      by_cases hltb : h < d*b
      · have hqb : h/d < b := (Nat.div_lt_iff_lt_mul hd).2 (by simpa [Nat.mul_comm] using hltb)
        rw [outcome_of_one (d*a) (d*b) h c₁ c₂ hdapos hda hltb,
          outcome_of_one a b (h/d) c₁ c₂ ha hqa hqb, hca, move_scale]
      · have hdb : d*b ≤ h := by omega
        have hqb : b ≤ h/d := (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hdb)
        have hcb := ih (h-d*b) (by omega) c₂ c₁
        rw [Nat.sub_mul_div] at hcb
        rw [outcome_of_two (d*a) (d*b) h c₁ c₂ hdapos hdbpos hda hdb,
          outcome_of_two a b (h/d) c₁ c₂ ha hb hqa hqb,
          hca, hcb, move_scale, move_scale, choose_scale d hd]

/-- The integer cross-multiplication form of the source ratio condition
forces consecutive positive integer multiples. -/
theorem ratio_eq_consecutive_multiples (a b k : ℕ) (ha : 0 < a) (_hk : 0 < k)
    (hratio : b*k=a*(k+1)) :
    ∃ d : ℕ, 0 < d ∧ a = k*d ∧ b = (k+1)*d := by
  have hab : a < b := by nlinarith
  have hsmall : a=k*(b-a) := by
    rw [Nat.mul_sub_left_distrib]
    have hx : k*b=k*a+a := by nlinarith
    omega
  refine ⟨b-a, by omega, hsmall, ?_⟩
  have hba : b-a+a=b := by omega
  nlinarith

end Conj11Scaling

namespace Conj11Complete
open Conj11

theorem consecutive_multiple_convention_independence (k d h : ℕ)
    (c₁ c₂ : Bool) (hk : 0 < k) (hd : 0 < d) :
    outcome (k*d) ((k+1)*d) c₁ c₂ h = outcome (k*d) ((k+1)*d) true true h := by
  have e₁ := Conj11Scaling.outcome_scale k (k+1) d h hk (by omega) hd c₁ c₂
  have e₂ := Conj11Scaling.outcome_scale k (k+1) d h hk (by omega) hd true true
  calc
    _ = Conj11Scaling.scale d (outcome k (k+1) c₁ c₂ (h/d)) := by
      simpa only [Nat.mul_comm] using e₁
    _ = Conj11Scaling.scale d (outcome k (k+1) true true (h/d)) :=
      congrArg (Conj11Scaling.scale d) (Conj11Result.normalized_all_conventions k (h/d) hk c₁ c₂)
    _ = _ := by simpa only [Nat.mul_comm] using e₂.symm

theorem ratio_convention_independence (a b k h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hk : 0 < k) (hratio : b*k=a*(k+1)) :
    outcome a b c₁ c₂ h = outcome a b true true h := by
  obtain ⟨d,hd,had,hbd⟩ := Conj11Scaling.ratio_eq_consecutive_multiples a b k ha hk hratio
  rw [had,hbd]
  exact consecutive_multiple_convention_independence k d h c₁ c₂ hk hd

/-- Conjecture 11 of arXiv:2510.24280v2, with the positive-denominator
ratio b/a=(k+1)/k expressed by exact integer cross multiplication. -/
theorem conjecture_11 (a b k h : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hratio : b*k=a*(k+1)) :
    outcome a b true true h = outcome a b false false h :=
  (ratio_convention_independence a b k h false false ha hk hratio).symm


end Conj11Complete
