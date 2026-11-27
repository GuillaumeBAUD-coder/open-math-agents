import OMAStatements.S_oeis_a260911
import Mathlib

namespace OMA.A260911

abbrev Goal (p : ℕ) := ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < p ∧
    a^2 + b^2 = c^2 ∧ IsSquare (a : ZMod p) ∧ IsSquare (b : ZMod p) ∧ IsSquare (c : ZMod p)

-- An entry records a Pythagorean triple and a square root for each side.
structure Certificate where
  a : ℕ
  b : ℕ
  c : ℕ
  x : ℕ
  y : ℕ
  z : ℕ

def Certificate.valid (w : Certificate) (p : ℕ) : Bool := decide
  (0 < w.a ∧ w.a < w.b ∧ w.b < w.c ∧ w.c < p ∧ w.a^2 + w.b^2 = w.c^2 ∧
    w.a ≡ w.x*w.x [MOD p] ∧ w.b ≡ w.y*w.y [MOD p] ∧ w.c ≡ w.z*w.z [MOD p])

def smallTable : List (ℕ × Certificate) := [
  (101, ⟨33, 56, 65, 29, 37, 41⟩),
  (103, ⟨8, 15, 17, 27, 18, 29⟩),
  (107, ⟨16, 30, 34, 4, 43, 26⟩),
  (109, ⟨3, 4, 5, 49, 2, 21⟩),
  (113, ⟨11, 60, 61, 24, 25, 20⟩),
  (127, ⟨8, 15, 17, 32, 53, 12⟩),
  (131, ⟨3, 4, 5, 38, 2, 23⟩),
  (137, ⟨8, 15, 17, 62, 17, 47⟩),
  (139, ⟨7, 24, 25, 29, 21, 5⟩),
  (149, ⟨7, 24, 25, 56, 60, 5⟩),
  (151, ⟨20, 21, 29, 41, 25, 28⟩),
  (157, ⟨12, 35, 37, 13, 52, 42⟩),
  (163, ⟨10, 24, 26, 70, 26, 29⟩),
  (167, ⟨7, 24, 25, 72, 58, 5⟩),
  (173, ⟨9, 40, 41, 3, 46, 53⟩),
  (179, ⟨3, 4, 5, 19, 2, 30⟩),
  (181, ⟨3, 4, 5, 33, 2, 27⟩),
  (191, ⟨3, 4, 5, 24, 2, 14⟩),
  (193, ⟨7, 24, 25, 59, 88, 5⟩),
  (197, ⟨7, 24, 25, 91, 40, 5⟩),
  (199, ⟨28, 45, 53, 25, 29, 75⟩),
  (211, ⟨16, 30, 34, 4, 36, 33⟩),
  (223, ⟨8, 15, 17, 30, 98, 54⟩),
  (227, ⟨16, 30, 34, 4, 22, 48⟩),
  (229, ⟨3, 4, 5, 71, 2, 66⟩),
  (233, ⟨60, 91, 109, 35, 18, 80⟩),
  (239, ⟨3, 4, 5, 106, 2, 31⟩),
  (241, ⟨3, 4, 5, 56, 2, 103⟩),
  (251, ⟨3, 4, 5, 76, 2, 16⟩),
  (257, ⟨8, 15, 17, 120, 23, 70⟩),
  (263, ⟨12, 35, 37, 46, 78, 33⟩),
  (269, ⟨16, 30, 34, 4, 90, 29⟩),
  (271, ⟨9, 40, 41, 3, 103, 47⟩),
  (277, ⟨16, 30, 34, 4, 108, 119⟩),
  (281, ⟨28, 45, 53, 77, 56, 89⟩),
  (283, ⟨7, 24, 25, 63, 34, 5⟩),
  (293, ⟨10, 24, 26, 89, 84, 57⟩),
  (307, ⟨7, 24, 25, 43, 115, 5⟩),
  (311, ⟨3, 4, 5, 25, 2, 117⟩),
  (313, ⟨88, 105, 137, 62, 123, 78⟩),
  (317, ⟨7, 24, 25, 18, 138, 5⟩),
  (331, ⟨24, 70, 74, 149, 100, 111⟩),
  (337, ⟨7, 24, 25, 119, 19, 5⟩),
  (347, ⟨16, 30, 34, 4, 77, 46⟩),
  (349, ⟨3, 4, 5, 165, 2, 62⟩),
  (353, ⟨8, 15, 17, 19, 108, 82⟩),
  (359, ⟨3, 4, 5, 163, 2, 148⟩),
  (367, ⟨60, 63, 87, 157, 141, 120⟩),
  (373, ⟨9, 40, 41, 3, 164, 55⟩),
  (379, ⟨16, 30, 34, 4, 48, 105⟩),
  (383, ⟨7, 24, 25, 34, 96, 5⟩),
  (389, ⟨7, 24, 25, 120, 56, 5⟩),
  (397, ⟨16, 30, 34, 4, 53, 35⟩),
  (401, ⟨9, 40, 41, 3, 21, 57⟩),
  (409, ⟨3, 4, 5, 168, 2, 150⟩),
  (419, ⟨3, 4, 5, 29, 2, 41⟩),
  (421, ⟨3, 4, 5, 74, 2, 200⟩),
  (431, ⟨3, 4, 5, 36, 2, 181⟩),
  (433, ⟨12, 35, 37, 102, 86, 125⟩),
  (439, ⟨28, 45, 53, 109, 22, 184⟩),
  (443, ⟨12, 35, 37, 101, 56, 193⟩),
  (449, ⟨9, 40, 41, 3, 104, 85⟩),
  (457, ⟨7, 24, 25, 98, 107, 5⟩),
  (461, ⟨24, 70, 74, 206, 158, 205⟩),
  (463, ⟨8, 15, 17, 57, 101, 61⟩),
  (467, ⟨9, 40, 41, 3, 177, 173⟩),
  (479, ⟨3, 4, 5, 31, 2, 22⟩),
  (487, ⟨15, 36, 39, 224, 6, 195⟩),
  (491, ⟨3, 4, 5, 113, 2, 147⟩),
  (499, ⟨20, 21, 29, 100, 206, 45⟩),
  (503, ⟨7, 24, 25, 55, 87, 5⟩),
  (509, ⟨20, 21, 29, 23, 101, 242⟩),
  (521, ⟨20, 21, 29, 123, 208, 219⟩),
  (523, ⟨7, 24, 25, 141, 46, 5⟩),
  (541, ⟨3, 4, 5, 57, 2, 196⟩),
  (547, ⟨13, 84, 85, 126, 94, 105⟩),
  (557, ⟨7, 24, 25, 243, 53, 5⟩),
  (563, ⟨17, 144, 145, 95, 12, 234⟩),
  (569, ⟨9, 40, 41, 3, 271, 151⟩),
  (571, ⟨20, 21, 29, 48, 239, 107⟩),
  (577, ⟨17, 144, 145, 245, 12, 69⟩),
  (587, ⟨16, 63, 65, 4, 91, 69⟩),
  (593, ⟨8, 15, 17, 284, 269, 69⟩),
  (599, ⟨3, 4, 5, 188, 2, 49⟩),
  (601, ⟨3, 4, 5, 115, 2, 273⟩),
  (607, ⟨11, 60, 61, 35, 270, 191⟩),
  (613, ⟨9, 40, 41, 3, 86, 138⟩),
  (617, ⟨15, 36, 39, 218, 6, 114⟩),
  (619, ⟨7, 24, 25, 61, 50, 5⟩)]

lemma small_verified : ∀ w ∈ smallTable, w.2.valid w.1 = true := by decide +kernel

set_option maxRecDepth 8000 in
lemma small_complete : ∀ p : Fin 630, 100 < p.val → p.val.Prime →
    p.val ∈ smallTable.map Prod.fst := by decide +kernel

lemma square_of_modEq {p a x : ℕ} (h : a ≡ x*x [MOD p]) : IsSquare (a : ZMod p) := by
  exact ⟨(x : ZMod p), by simpa using (ZMod.natCast_eq_natCast_iff a (x*x) p).2 h⟩

lemma small {p : ℕ} (hp : p.Prime) (hlo : 100 < p) (hhi : p < 630) : Goal p := by
  obtain ⟨⟨q,w⟩,hmem,heq⟩ := List.mem_map.mp (small_complete ⟨p,hhi⟩ hlo hp)
  change q = p at heq
  subst q
  have hw := small_verified (p,w) hmem
  change w.valid p = true at hw
  unfold Certificate.valid at hw
  obtain ⟨ha,hb,hc,hd,he,hx,hy,hz⟩ := of_decide_eq_true hw
  exact ⟨w.a,w.b,w.c,ha,hb,hc,hd,he,square_of_modEq hx,square_of_modEq hy,square_of_modEq hz⟩

abbrev Atom := Fin 15

def atom : Atom → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 97, 113]

def val (l : List Atom) : ℕ := (l.map atom).prod

def parity (color : Atom → Bool) : List Atom → Bool
  | [] => false
  | i :: l => xor (color i) (parity color l)

abbrev Triple := List Atom × List Atom × List Atom

-- Each side is stored as its list of prime factors, indexed by atom.
def triples : List Triple := [
  ([0, 0, 2, 2], [1, 1, 1, 8], [6, 11]),
  ([0, 0, 0, 0, 1, 3], [6, 10], [2, 2, 2, 2]),
  ([0, 0, 1, 1, 3], [1, 4, 6], [1, 2, 12]),
  ([0, 0, 1, 8], [6, 9], [2, 14]),
  ([0, 0, 8], [1, 2, 2, 3], [5, 12]),
  ([2, 10], [0, 0, 1, 1, 5], [6, 9]),
  ([0, 0, 4], [1, 3, 8], [2, 13]),
  ([0, 0, 0, 1, 1], [1, 4, 5], [1, 2, 9]),
  ([2, 5], [0, 0, 1, 2, 3], [2, 2, 6]),
  ([0, 0, 0, 1, 2], [0, 2, 2, 3], [0, 2, 11]),
  ([1, 1, 2], [0, 0, 0, 0, 1, 3], [1, 14]),
  ([0, 0, 1, 6], [4, 8], [2, 2, 5]),
  ([0, 0, 1, 1], [6, 7], [2, 2, 5]),
  ([3, 8], [0, 0, 0, 0, 1, 2], [6, 6]),
  ([1, 5], [0, 0, 1, 1, 3], [1, 2, 6]),
  ([3, 7], [0, 0, 1, 5], [2, 12]),
  ([0, 0, 0, 5], [1, 1, 6], [2, 11]),
  ([1, 7], [0, 0, 0, 0, 4], [2, 11]),
  ([6], [0, 0, 0, 0, 1, 1], [2, 9]),
  ([2, 5], [0, 0, 0, 1, 1], [13]),
  ([0, 0, 1, 1], [3, 4], [2, 6]),
  ([0, 0, 0, 0], [1, 1, 3], [2, 5]),
  ([1, 1], [0, 0, 0, 2], [12]),
  ([0, 0, 1], [2, 3], [11]),
  ([0, 0, 0, 0], [0, 1, 2], [0, 6]),
  ([0, 0, 2], [1, 3], [9]),
  ([3], [0, 0, 0, 1], [2, 2]),
  ([1, 1], [0, 0, 1], [1, 2])]

def valid (t : Triple) : Bool := decide
  (0 < val t.1 ∧ val t.1 < val t.2.1 ∧ val t.2.1 < val t.2.2 ∧ val t.2.2 ≤ 629 ∧
    (val t.1)^2 + (val t.2.1)^2 = (val t.2.2)^2)

lemma shape : ∀ t ∈ triples, valid t = true := by decide +kernel

def positive (color : Atom → Bool) (t : Triple) :=
  !(parity color t.1 || parity color t.2.1 || parity color t.2.2)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
lemma covered (color : Atom → Bool) : triples.any (positive color) = true := by
  simp only [triples, List.any_cons, List.any_nil, positive, parity,
    Bool.xor_false, Bool.or_false, Bool.false_or, Bool.xor_self]
  generalize color 0 = b0
  generalize color 1 = b1
  generalize color 2 = b2
  generalize color 3 = b3
  generalize color 4 = b4
  generalize color 5 = b5
  generalize color 6 = b6
  generalize color 7 = b7
  generalize color 8 = b8
  generalize color 9 = b9
  generalize color 10 = b10
  generalize color 11 = b11
  generalize color 12 = b12
  generalize color 13 = b13
  generalize color 14 = b14
  clear color
  -- Splitting four bits keeps each of the remaining truth tables short.
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide +revert +kernel

lemma atom_bounds : ∀ i, 0 < atom i ∧ atom i ≤ 113 := by decide +kernel

lemma nz {n p : ℕ} (hn : 0 < n) (hp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => (Nat.le_of_dvd hn h).not_gt hp

def color (p : ℕ) [Fact p.Prime] (i : Atom) : Bool :=
  decide (legendreSym p (atom i) = -1)

def signValue (b : Bool) : ℤ := if b then -1 else 1

lemma sign_xor (a b : Bool) : signValue (xor a b) = signValue a * signValue b := by
  cases a <;> cases b <;> decide

lemma sign (p : ℕ) [Fact p.Prime] (hp : 629 < p) (l : List Atom) :
    legendreSym p (val l) = signValue (parity (color p) l) := by
  induction l with
  | nil => simp [val, parity, legendreSym, signValue]
  | cons i l ih =>
    have hr := atom_bounds i
    have hn := nz hr.1 (show atom i < p by omega)
    have ha : (((atom i : ℕ) : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hn
    have hh : legendreSym p (atom i) = signValue (color p i) := by
      rcases legendreSym.eq_one_or_neg_one p ha with h | h <;> simp [signValue, color, h]
    change legendreSym p ((atom i * val l : ℕ) : ℤ) = signValue (xor (color p i) (parity (color p) l))
    rw [Nat.cast_mul, legendreSym.mul, sign_xor, hh, ih]

lemma square_val (p : ℕ) [Fact p.Prime] (hp : 629 < p) (l : List Atom)
    (hlo : 0 < val l) (hhi : val l < p) (h : parity (color p) l = false) :
    IsSquare (val l : ZMod p) := by
  apply (legendreSym.eq_one_iff' p (nz hlo hhi)).mp
  simp [sign p hp l,h,signValue]

lemma large (p : ℕ) [Fact p.Prime] (hp : 629 < p) : Goal p := by
  obtain ⟨t,ht,hgood⟩ := List.any_eq_true.mp (covered (color p))
  have hvalid := shape t ht
  unfold valid at hvalid
  obtain ⟨ha,hb,hc,hd,he⟩ := of_decide_eq_true hvalid
  simp [positive] at hgood
  obtain ⟨⟨h1,h2⟩,h3⟩ := hgood
  exact ⟨_,_,_,ha,hb,hc,by omega,he,
    square_val p hp _ ha (by omega) h1,
    square_val p hp _ (by omega) (by omega) h2,
    square_val p hp _ (by omega) (by omega) h3⟩

end OMA.A260911

theorem OMA.solution : type_of% @OMA.S_oeis_a260911.main := by
  intro p hp hlo
  by_cases h : p < 630
  · exact OMA.A260911.small hp hlo h
  · let _ : Fact p.Prime := ⟨hp⟩
    exact OMA.A260911.large p (by omega)
