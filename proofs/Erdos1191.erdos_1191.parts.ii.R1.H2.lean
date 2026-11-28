import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R1
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

/-!
# An integer encoding for dyadic difference packings

The tag for block index j encodes j and its square in separate bit positions.
The two moments recover an unordered pair of indices from the sum of two tags.
The outer encoding splits each input into chunks of widths 1, 2, 4, and so
on. Each chunk gets 12 tag bits and each field gets a carry bit, so the
original sum and the tag sum can be recovered from the encoded sum.

The cutoff estimate proves H2 with exponent 30. The final equivalence
identifies H1 as the remaining search for finite packings at every horizon.
-/

-- Credit: @NicholasWierenga

namespace Erdos1191Codec

structure Slot where
  isTag : Bool
  width : Nat

def capacity : List Slot → Bool → Nat
  | [], _ => 1
  | slot :: slots, isTag =>
      if slot.isTag = isTag then 2 ^ slot.width * capacity slots isTag
      else capacity slots isTag

def encode : List Slot → Nat → Nat → Nat
  | [], _, _ => 0
  | ⟨false, width⟩ :: slots, n, k =>
      n % (2 ^ width) + (2 * 2 ^ width) * encode slots (n / (2 ^ width)) k
  | ⟨true, width⟩ :: slots, n, k =>
      k % (2 ^ width) + (2 * 2 ^ width) * encode slots n (k / (2 ^ width))

lemma peel {m u v u' v' x y x' y' : Nat} (hm : 0 < m)
    (hu : u < m) (hv : v < m) (hu' : u' < m) (hv' : v' < m)
    (h : (u + (2 * m) * x) + (v + (2 * m) * y) =
      (u' + (2 * m) * x') + (v' + (2 * m) * y')) :
    u + v = u' + v' ∧ x + y = x' + y' := by
  have hl : u + v < 2 * m := by omega
  have hr : u' + v' < 2 * m := by omega
  have hp : 0 < 2 * m := by omega
  have h' : (u + v) + (2 * m) * (x + y) =
      (u' + v') + (2 * m) * (x' + y') := by
    simp only [Nat.mul_add]
    omega
  constructor
  · have hmod := congrArg (fun n : Nat => n % (2 * m)) h'
    simpa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hmod
  · have hdiv := congrArg (fun n : Nat => n / (2 * m)) h'
    simpa [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl,
      Nat.div_eq_of_lt hr] using hdiv

lemma assemble {m a b c d : Nat}
    (hdigit : a % m + b % m = c % m + d % m)
    (htail : a / m + b / m = c / m + d / m) : a + b = c + d := by
  have hs (r s : Nat) : r + s = (r % m + s % m) + m * (r / m + s / m) := by
    rw [Nat.mul_add]
    have hr := Nat.mod_add_div r m
    have hs := Nat.mod_add_div s m
    omega
  rw [hs a b, hs c d, hdigit, htail]

theorem encode_reflect (slots : List Slot) {a b c d w x y z : Nat}
    (ha : a < capacity slots false) (hb : b < capacity slots false)
    (hc : c < capacity slots false) (hd : d < capacity slots false)
    (hw : w < capacity slots true) (hx : x < capacity slots true)
    (hy : y < capacity slots true) (hz : z < capacity slots true)
    (h : encode slots a w + encode slots b x = encode slots c y + encode slots d z) :
    a + b = c + d ∧ w + x = y + z := by
  induction slots generalizing a b c d w x y z with
  | nil =>
      simp [capacity] at ha hb hc hd hw hx hy hz
      simp [ha, hb, hc, hd, hw, hx, hy, hz]
  | cons slot slots ih =>
      obtain ⟨isTag, width⟩ := slot
      have hpos : 0 < (2 : Nat) ^ width := Nat.pow_pos (by decide)
      cases isTag
      · simp [capacity] at ha hb hc hd hw hx hy hz
        simp only [encode] at h
        obtain ⟨hdigit, hrest⟩ := peel hpos
          (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h
        have ⟨hn, hk⟩ := ih (Nat.div_lt_of_lt_mul ha) (Nat.div_lt_of_lt_mul hb)
          (Nat.div_lt_of_lt_mul hc) (Nat.div_lt_of_lt_mul hd) hw hx hy hz hrest
        exact ⟨assemble hdigit hn, hk⟩
      · simp [capacity] at ha hb hc hd hw hx hy hz
        simp only [encode] at h
        obtain ⟨hdigit, hrest⟩ := peel hpos
          (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h
        have ⟨hn, hk⟩ := ih ha hb hc hd (Nat.div_lt_of_lt_mul hw) (Nat.div_lt_of_lt_mul hx)
          (Nat.div_lt_of_lt_mul hy) (Nat.div_lt_of_lt_mul hz) hrest
        exact ⟨hn, assemble hdigit hk⟩

theorem encode_zero (slots : List Slot) : encode slots 0 0 = 0 := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      obtain ⟨isTag, width⟩ := slot
      cases isTag <;> simp [encode, ih]

theorem encode_append (slots suffix : List Slot) {n k : Nat}
    (hn : n < capacity slots false) (hk : k < capacity slots true) :
    encode (slots ++ suffix) n k = encode slots n k := by
  induction slots generalizing n k with
  | nil =>
      simp [capacity] at hn hk
      simp [hn, hk, encode, encode_zero]
  | cons slot slots ih =>
      obtain ⟨isTag, width⟩ := slot
      cases isTag
      · simp [capacity] at hn hk
        simp only [List.cons_append, encode]
        rw [ih (Nat.div_lt_of_lt_mul hn) hk]
      · simp [capacity] at hn hk
        simp only [List.cons_append, encode]
        rw [ih hn (Nat.div_lt_of_lt_mul hk)]

end Erdos1191Codec

namespace Erdos1191Codec

/-- Each stage stores a fixed-width label chunk and a doubling-width input chunk. -/
def stages (labelWidth inputWidth : Nat) : Nat → List Slot
  | 0 => []
  | count + 1 =>
      ⟨true, labelWidth⟩ :: ⟨false, inputWidth⟩ ::
        stages labelWidth (2 * inputWidth) count

lemma stages_add (L w j s : Nat) :
    stages L w (j + s) = stages L w j ++ stages L (2 ^ j * w) s := by
  induction j generalizing w with
  | zero => simp [stages]
  | succ j ih =>
      rw [Nat.succ_add]
      simp only [stages, List.cons_append, List.cons.injEq, true_and]
      rw [ih, Nat.pow_succ, Nat.mul_assoc]

lemma span_succ (w j : Nat) :
    w * (2 ^ (j + 1) - 1) = w + (2 * w) * (2 ^ j - 1) := by
  have hpos : 0 < (2 : Nat) ^ j := Nat.pow_pos (by decide)
  have h : 2 ^ (j + 1) - 1 = 1 + 2 * (2 ^ j - 1) := by
    rw [Nat.pow_succ]
    omega
  rw [h, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm w 2]

theorem capacity_stages_input (L w j : Nat) :
    capacity (stages L w j) false = 2 ^ (w * (2 ^ j - 1)) := by
  induction j generalizing w with
  | zero => simp [stages, capacity]
  | succ j ih =>
      change 2 ^ w * capacity (stages L (2 * w) j) false = 2 ^ (w * (2 ^ (j + 1) - 1))
      rw [ih, span_succ, Nat.pow_add]

theorem capacity_stages_label (L w j : Nat) :
    capacity (stages L w j) true = 2 ^ (L * j) := by
  induction j generalizing w with
  | zero => simp [stages, capacity]
  | succ j ih => simp [stages, capacity, ih, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

lemma pack_lt {u m tail cap : Nat} (hu : u < m) (ht : tail < cap) :
    u + (2 * m) * tail < (2 * m) * cap := by
  calc
    u + (2 * m) * tail < (2 * m) * (tail + 1) := by
      rw [Nat.mul_succ]
      omega
    _ ≤ (2 * m) * cap := Nat.mul_le_mul_left _ (by omega)

/-- The width of a partially occupied final input chunk controls the result. -/
theorem encode_stages_lt (L w j r n k : Nat)
    (hn : n < 2 ^ (w * (2 ^ j - 1) + r))
    (hk : k < 2 ^ (L * (j + 1))) :
    encode (stages L w (j + 1)) n k <
      2 ^ (w * (2 ^ j - 1) + r + (L + 2) * (j + 1)) := by
  have he (a : Nat) : 2 * 2 ^ a = 2 ^ (a + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  induction j generalizing w n k with
  | zero =>
      simp only [Nat.pow_zero, Nat.sub_self, Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hn hk ⊢
      have hp : 0 < (2 : Nat) ^ L := Nat.pow_pos (by decide)
      simp only [stages, encode, Nat.mul_zero, Nat.add_zero]
      have hm := Nat.lt_of_le_of_lt (Nat.mod_le n (2 ^ w)) hn
      have h := pack_lt (Nat.mod_lt k hp) hm
      have h' : k % 2 ^ L + 2 * 2 ^ L * (n % 2 ^ w) < 2 ^ (L + 1 + r) := by
        simpa only [he, ← Nat.pow_add] using h
      exact Nat.lt_of_lt_of_le h' (Nat.pow_le_pow_right (by decide) (by omega))
  | succ j ih =>
      have hp : 0 < (2 : Nat) ^ L := Nat.pow_pos (by decide)
      have hq : 0 < (2 : Nat) ^ w := Nat.pow_pos (by decide)
      have hnd : n / 2 ^ w < 2 ^ ((2 * w) * (2 ^ j - 1) + r) := by
        rw [span_succ, Nat.add_assoc, Nat.pow_add] at hn
        exact Nat.div_lt_of_lt_mul hn
      have hkd : k / 2 ^ L < 2 ^ (L * (j + 1)) := by
        apply Nat.div_lt_of_lt_mul
        simpa [Nat.mul_succ, Nat.pow_add, Nat.mul_comm] using hk
      have ht := ih (2 * w) _ _ hnd hkd
      change k % 2 ^ L + (2 * 2 ^ L) * (n % 2 ^ w + (2 * 2 ^ w) *
        encode (stages L (2 * w) (j + 1)) (n / 2 ^ w) (k / 2 ^ L)) < _
      have h := pack_lt (Nat.mod_lt k hp) (pack_lt (Nat.mod_lt n hq) ht)
      have hexp :
          L + 1 + (w + 1 + ((2 * w) * (2 ^ j - 1) + r + (L + 2) * (j + 1))) =
            w * (2 ^ (j + 1) - 1) + r + (L + 2) * (j + 1 + 1) := by
        rw [span_succ, Nat.mul_succ (L + 2) (j + 1)]
        omega
      simpa only [he, ← Nat.pow_add, hexp] using h

/-- A common stage count can be used after both integers fit their slots. -/
theorem encode_stages_stable (L j s : Nat) {n k : Nat}
    (hn : n < 2 ^ (2 ^ j - 1)) (hk : k < 2 ^ (L * j)) :
    encode (stages L 1 (j + s)) n k = encode (stages L 1 j) n k := by
  rw [stages_add]
  apply encode_append
  · simpa [capacity_stages_input] using hn
  · simpa [capacity_stages_label] using hk

end Erdos1191Codec

namespace Erdos1191Codec

/-- Choose at least one stage, enough to store both inputs. -/
def requiredStages (L n k : Nat) : Nat :=
  max ((n.log2 + 1).log2 + 1) (k.log2 / L + 1)

def encodePair (L n k : Nat) : Nat :=
  encode (stages L 1 (requiredStages L n k)) n k

lemma size_first (n : Nat) : n < 2 ^ (2 ^ ((n.log2 + 1).log2 + 1) - 1) := by
  have hbits := Nat.lt_log2_self (n := n.log2 + 1)
  have hwidth : n.log2 + 1 ≤ 2 ^ ((n.log2 + 1).log2 + 1) - 1 := by omega
  exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hwidth)

lemma fits_mono (L j j' : Nat) {n k : Nat} (hle : j ≤ j')
    (hn : n < 2 ^ (2 ^ j - 1)) (hk : k < 2 ^ (L * j)) :
    n < 2 ^ (2 ^ j' - 1) ∧ k < 2 ^ (L * j') := by
  have hp : 2 ^ j ≤ (2 : Nat) ^ j' := Nat.pow_le_pow_right (by decide) hle
  exact ⟨Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)),
    Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hle))⟩

lemma requiredStages_fits (L n k : Nat) (hL : 0 < L) :
    n < 2 ^ (2 ^ (requiredStages L n k) - 1) ∧
      k < 2 ^ (L * requiredStages L n k) := by
  have hn : (n.log2 + 1).log2 + 1 ≤ requiredStages L n k := Nat.le_max_left ..
  have hk : k.log2 / L + 1 ≤ requiredStages L n k := Nat.le_max_right ..
  have hp : 2 ^ ((n.log2 + 1).log2 + 1) ≤ (2 : Nat) ^ (requiredStages L n k) :=
    Nat.pow_le_pow_right (by decide) hn
  have hd : k.log2 / L < requiredStages L n k := by omega
  have hlabel : k.log2 < L * requiredStages L n k := by
    simpa [Nat.mul_comm] using Nat.lt_mul_of_div_lt hd hL
  have hwidth : k.log2 + 1 ≤ L * requiredStages L n k := by omega
  exact ⟨Nat.lt_of_lt_of_le (size_first n) (Nat.pow_le_pow_right (by decide) (by omega)),
    Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hwidth)⟩

lemma encode_stages_of_le {L j j' n k : Nat} (hle : j ≤ j')
    (hn : n < 2 ^ (2 ^ j - 1)) (hk : k < 2 ^ (L * j)) :
    encode (stages L 1 j') n k = encode (stages L 1 j) n k := by
  rw [← Nat.add_sub_of_le hle]
  exact encode_stages_stable L j (j' - j) hn hk

theorem encodePair_eq_of_fits {L j n k : Nat} (hL : 0 < L)
    (hn : n < 2 ^ (2 ^ j - 1)) (hk : k < 2 ^ (L * j)) :
    encodePair L n k = encode (stages L 1 j) n k := by
  unfold encodePair
  rcases Nat.le_total (requiredStages L n k) j with h | h
  · obtain ⟨hn', hk'⟩ := requiredStages_fits L n k hL
    exact (encode_stages_of_le h hn' hk').symm
  · exact encode_stages_of_le h hn hk

theorem encodePair_reflect {L a b c d w x y z : Nat} (hL : 0 < L)
    (h : encodePair L a w + encodePair L b x = encodePair L c y + encodePair L d z) :
    a + b = c + d ∧ w + x = y + z := by
  let j := requiredStages L a w + requiredStages L b x +
    requiredStages L c y + requiredStages L d z
  have fits (n k : Nat) (hle : requiredStages L n k ≤ j) :
      n < 2 ^ (2 ^ j - 1) ∧ k < 2 ^ (L * j) :=
    fits_mono L _ j hle (requiredStages_fits L n k hL).1 (requiredStages_fits L n k hL).2
  obtain ⟨ha, hw⟩ := fits a w (by dsimp [j]; omega)
  obtain ⟨hb, hx⟩ := fits b x (by dsimp [j]; omega)
  obtain ⟨hc, hy⟩ := fits c y (by dsimp [j]; omega)
  obtain ⟨hd, hz⟩ := fits d z (by dsimp [j]; omega)
  rw [encodePair_eq_of_fits hL ha hw, encodePair_eq_of_fits hL hb hx,
    encodePair_eq_of_fits hL hc hy, encodePair_eq_of_fits hL hd hz] at h
  have app := @encode_reflect (stages L 1 j) a b c d w x y z
  rw [capacity_stages_input, capacity_stages_label, Nat.one_mul] at app
  exact app ha hb hc hd hw hx hy hz h

theorem encodePair_injective {L : Nat} (hL : 0 < L) {a b w x : Nat}
    (h : encodePair L a w = encodePair L b x) : a = b ∧ w = x := by
  have hs : encodePair L a w + encodePair L a w =
      encodePair L b x + encodePair L b x := by rw [h]
  obtain ⟨hn, hk⟩ := encodePair_reflect hL hs
  exact ⟨by omega, by omega⟩

/-- Quantitative growth, with the final data chunk counted by its occupied bits. -/
theorem encodePair_lt_bits {L n k : Nat} (hL : 0 < L)
    (hk : k < 2 ^ (L * ((n.log2 + 1).log2 + 1))) :
    encodePair L n k < 2 ^ (n.log2 + 1 + (L + 2) * ((n.log2 + 1).log2 + 1)) := by
  let b := n.log2 + 1
  let j := b.log2
  rw [encodePair_eq_of_fits hL (size_first n) hk]
  have hp : 2 ^ j ≤ b := Nat.log2_self_le (by dsimp [b]; omega)
  let r := b - (2 ^ j - 1)
  have hwidth : 1 * (2 ^ j - 1) + r = b := by dsimp [r]; omega
  have hn : n < 2 ^ (1 * (2 ^ j - 1) + r) := by
    rw [hwidth]
    exact Nat.lt_log2_self
  have h := encode_stages_lt L 1 j r n k hn hk
  rwa [hwidth] at h

theorem encodePair_le_log {L n k : Nat} (hL : 0 < L)
    (hk : k < 2 ^ (L * ((n.log2 + 1).log2 + 1))) :
    encodePair L n k + 1 ≤ 2 ^ (L + 3) * (n + 1) * (n.log2 + 1) ^ (L + 2) := by
  let b := n.log2 + 1
  let j := b.log2
  have hp : 2 ^ j ≤ b := Nat.log2_self_le (by dsimp [b]; omega)
  have hq : 2 ^ b ≤ 2 * (n + 1) := by
    cases n with
    | zero => decide
    | succ n =>
        have hn : 2 ^ (n + 1).log2 ≤ n + 1 := Nat.log2_self_le (Nat.succ_ne_zero n)
        dsimp [b]
        rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
  calc
    encodePair L n k + 1 ≤ 2 ^ (b + (L + 2) * (j + 1)) := encodePair_lt_bits hL hk
    _ = 2 ^ (L + 2) * 2 ^ b * (2 ^ j) ^ (L + 2) := by
      rw [Nat.pow_add 2 b ((L + 2) * (j + 1)), Nat.mul_succ (L + 2) j,
        Nat.pow_add 2 ((L + 2) * j) (L + 2), Nat.mul_comm (L + 2) j, Nat.pow_mul]
      simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 2 ^ (L + 2) * (2 * (n + 1)) * b ^ (L + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) (Nat.pow_le_pow_left hp _)
    _ = 2 ^ (L + 3) * (n + 1) * b ^ (L + 2) := by
      rw [show 2 ^ (L + 3) = 2 ^ (L + 2) * 2 from Nat.pow_succ 2 (L + 2)]
      simp only [Nat.mul_assoc]

end Erdos1191Codec

namespace Erdos1191Codec

/-- An explicit output cutoff for the 12-bit label codec. -/
theorem encodePair_cutoff {x a k : Nat} (hx : 2 ≤ x) (ha : 1 ≤ a)
    (hax : a ≤ x / (1 + x.log2) ^ 30)
    (hk : k < 2 ^ (12 * ((a.log2 + 1).log2 + 1))) :
    encodePair 12 a k + 1 ≤ x := by
  let t := 1 + x.log2
  have hpos : 0 < t := by dsimp [t]; omega
  have ha_le_x : a ≤ x := Nat.le_trans hax (Nat.div_le_self _ _)
  have hlog : a.log2 ≤ x.log2 :=
    (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (by omega)) ha_le_x)
  have hwidth : a.log2 + 1 ≤ t := by dsimp [t]; omega
  have htwo : 2 ≤ t := by
    have hlogx : 1 ≤ x.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hx)
    dsimp [t]
    omega
  have ha_mul : a * t ^ 30 ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hpos)).1 hax
  calc
    encodePair 12 a k + 1 ≤ 2 ^ 15 * (a + 1) * (a.log2 + 1) ^ 14 :=
      encodePair_le_log (by decide) hk
    _ ≤ 2 ^ 15 * (2 * a) * t ^ 14 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hwidth _)
    _ = a * (2 ^ 16 * t ^ 14) := by
      rw [← Nat.mul_assoc (2 ^ 15) 2 a, show (2 : Nat) ^ 15 * 2 = 2 ^ 16 by decide]
      rw [Nat.mul_comm ((2 : Nat) ^ 16) a, Nat.mul_assoc]
    _ ≤ a * (t ^ 16 * t ^ 14) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left htwo _))
    _ = a * t ^ 30 := by rw [← Nat.pow_add]
    _ ≤ x := ha_mul

end Erdos1191Codec

namespace Erdos1191Tags

def digit (a b : ℕ) : ℕ := a % 2 + 4 * (b % 2)

/-- Alternate the bits of two numbers, leaving one guard bit after each. -/
def tagBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | width + 1, a, b => digit a b + 16 * tagBits width (a / 2) (b / 2)

lemma digit_lt (a b : ℕ) : digit a b < 6 := by
  unfold digit
  omega

lemma digit_reflect {a b c d p q r s : ℕ}
    (h : digit a p + digit b q = digit c r + digit d s) :
    a % 2 + b % 2 = c % 2 + d % 2 ∧ p % 2 + q % 2 = r % 2 + s % 2 := by
  unfold digit at h
  omega

lemma peel {a b c d p q r s : ℕ}
    (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (h : (a + 16 * p) + (b + 16 * q) = (c + 16 * r) + (d + 16 * s)) :
    a + b = c + d ∧ p + q = r + s := by
  omega

lemma assemble {a b c d : ℕ}
    (hlo : a % 2 + b % 2 = c % 2 + d % 2)
    (hhi : a / 2 + b / 2 = c / 2 + d / 2) : a + b = c + d := by
  omega

lemma tagBits_zero (width : ℕ) : tagBits width 0 0 = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [tagBits, digit, ih]

lemma tagBits_lt (width a b : ℕ) : tagBits width a b < 16 ^ width := by
  induction width generalizing a b with
  | zero => simp [tagBits]
  | succ width ih =>
      simp only [tagBits, Nat.pow_succ]
      have hd := digit_lt a b
      have ht := ih (a / 2) (b / 2)
      omega

lemma div_two_lt {n width : ℕ} (h : n < 2 ^ (width + 1)) :
    n / 2 < 2 ^ width :=
  Nat.div_lt_of_lt_mul (by simpa only [Nat.pow_succ, Nat.mul_comm] using h)

lemma tagBits_stable (width extra : ℕ) {a b : ℕ}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) :
    tagBits (width + extra) a b = tagBits width a b := by
  induction width generalizing a b with
  | zero =>
      have ha' : a = 0 := by simpa using ha
      have hb' : b = 0 := by simpa using hb
      simp [ha', hb', tagBits_zero]
  | succ width ih =>
      rw [Nat.succ_add]
      simp only [tagBits]
      rw [ih (div_two_lt ha) (div_two_lt hb)]

lemma tagBits_reflect (width : ℕ) {a b c d p q r s : ℕ}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hc : c < 2 ^ width)
    (hd : d < 2 ^ width) (hp : p < 2 ^ width) (hq : q < 2 ^ width)
    (hr : r < 2 ^ width) (hs : s < 2 ^ width)
    (h : tagBits width a p + tagBits width b q = tagBits width c r + tagBits width d s) :
    a + b = c + d ∧ p + q = r + s := by
  induction width generalizing a b c d p q r s with
  | zero =>
      simp at ha hb hc hd hp hq hr hs
      simp [ha, hb, hc, hd, hp, hq, hr, hs]
  | succ width ih =>
      simp only [tagBits] at h
      obtain ⟨hlo, hhi⟩ :=
        peel (digit_lt a p) (digit_lt b q) (digit_lt c r) (digit_lt d s) h
      obtain ⟨hfirst, hsecond⟩ := digit_reflect hlo
      obtain ⟨hfirst', hsecond'⟩ :=
        ih (div_two_lt ha) (div_two_lt hb) (div_two_lt hc) (div_two_lt hd)
          (div_two_lt hp) (div_two_lt hq) (div_two_lt hr) (div_two_lt hs) hhi
      exact ⟨assemble hfirst hfirst', assemble hsecond hsecond'⟩

def bitWidth (j : ℕ) : ℕ := (j * j).log2 + 1

/-- A polynomially bounded tag storing the first and second powers of its label. -/
def tag (j : ℕ) : ℕ := tagBits (bitWidth j) j (j * j)

lemma first_fits (j : ℕ) : j < 2 ^ bitWidth j := by
  exact lt_of_le_of_lt (Nat.le_mul_self j) Nat.lt_log2_self

lemma second_fits (j : ℕ) : j * j < 2 ^ bitWidth j :=
  Nat.lt_log2_self

lemma tag_extend {j width : ℕ} (h : bitWidth j ≤ width) :
    tagBits width j (j * j) = tag j := by
  rw [← Nat.add_sub_of_le h]
  exact tagBits_stable (bitWidth j) _ (first_fits j) (second_fits j)

lemma recover_moments {a b c d : ℕ}
    (h : tag a + tag b = tag c + tag d) :
    a + b = c + d ∧ a * a + b * b = c * c + d * d := by
  let width := bitWidth a + bitWidth b + bitWidth c + bitWidth d
  have hwidtha : bitWidth a ≤ width := by dsimp [width]; omega
  have hwidthb : bitWidth b ≤ width := by dsimp [width]; omega
  have hwidthc : bitWidth c ≤ width := by dsimp [width]; omega
  have hwidthd : bitWidth d ≤ width := by dsimp [width]; omega
  rw [← tag_extend hwidtha, ← tag_extend hwidthb, ← tag_extend hwidthc,
    ← tag_extend hwidthd] at h
  have lift (j : ℕ) (hj : bitWidth j ≤ width) :
      j < 2 ^ width ∧ j * j < 2 ^ width := by
    have hmono := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    exact ⟨lt_of_lt_of_le (first_fits j) hmono, lt_of_lt_of_le (second_fits j) hmono⟩
  exact tagBits_reflect width (lift a hwidtha).1 (lift b hwidthb).1
    (lift c hwidthc).1 (lift d hwidthd).1 (lift a hwidtha).2
    (lift b hwidthb).2 (lift c hwidthc).2 (lift d hwidthd).2 h

theorem unordered_of_moments {a b c d : ℕ} (hs : a + b = c + d)
    (hq : a * a + b * b = c * c + d * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs' : (a : ℤ) + b = c + d := by exact_mod_cast hs
  have hq' : (a : ℤ) * a + b * b = c * c + d * d := by exact_mod_cast hq
  have hs2 := congrArg (fun n : ℤ => n ^ 2) hs'
  have hp : (a : ℤ) * b = c * d := by nlinarith
  have hlin := congrArg (fun n : ℤ => (a : ℤ) * n) hs'
  have hzero : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by nlinarith
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

theorem tag_reflect {a b c d : ℕ} (h : tag a + tag b = tag c + tag d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  unordered_of_moments (recover_moments h).1 (recover_moments h).2

theorem tag_injective : Function.Injective tag := by
  intro a b h
  have hsum : tag a + tag a = tag b + tag b := by rw [h]
  rcases tag_reflect hsum with ⟨hab, _⟩ | ⟨hab, _⟩ <;> exact hab

theorem tag_le (j : ℕ) : tag j + 1 ≤ 16 * (j + 1) ^ 8 := by
  have hbits : 2 ^ bitWidth j ≤ 2 * (j + 1) ^ 2 := by
    by_cases hj : j = 0
    · subst j
      decide
    · have hpow : 2 ^ (j * j).log2 ≤ j * j :=
        Nat.log2_self_le (Nat.mul_ne_zero hj hj)
      unfold bitWidth
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul_left 2 (by nlinarith)
  calc
    tag j + 1 ≤ 16 ^ bitWidth j := tagBits_lt (bitWidth j) j (j * j)
    _ = (2 ^ bitWidth j) ^ 4 := by
      rw [show (16 : ℕ) = 2 ^ 4 by decide, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
    _ ≤ (2 * (j + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left hbits _
    _ = 16 * (j + 1) ^ 8 := by rw [Nat.mul_pow, ← Nat.pow_mul]

theorem tag_fits {j n : ℕ} (hj : j ≤ n.log2 + 1) :
    tag j < 2 ^ (12 * ((n.log2 + 1).log2 + 1)) := by
  let w := (n.log2 + 1).log2 + 1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hsize : j + 1 ≤ 2 ^ w :=
    Nat.succ_le_of_lt (lt_of_le_of_lt hj Nat.lt_log2_self)
  calc
    tag j + 1 ≤ 16 * (j + 1) ^ 8 := tag_le j
    _ ≤ 16 * (2 ^ w) ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
    _ = 2 ^ (4 + w * 8) := by rw [Nat.pow_add (2 : ℕ) 4 (w * 8), Nat.pow_mul (2 : ℕ) w 8]
    _ ≤ 2 ^ (12 * w) := Nat.pow_le_pow_right (by decide) (by omega)

end Erdos1191Tags

namespace Erdos1191Codec

open Filter Set

/-- An explicit encoder recovers sums and dyadic block labels and has a logarithmic cutoff. -/
theorem blockEncoder :
    ∃ (E : ℕ → ℕ) (d : ℕ),
      (∀ a b u v, E a + E b = E u + E v →
        a + b = u + v ∧
          ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
           (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
      ∀ᶠ x : ℕ in atTop, ∀ a ∈ Icc 1 (x / (1 + Nat.log 2 x) ^ d), E a ∈ Icc 1 x := by
  let E (a : ℕ) := encodePair 12 a (Erdos1191Tags.tag a.log2) + 1
  refine ⟨E, 30, ?_, ?_⟩
  · intro a b u v h
    have heq : encodePair 12 a (Erdos1191Tags.tag a.log2) +
        encodePair 12 b (Erdos1191Tags.tag b.log2) =
        encodePair 12 u (Erdos1191Tags.tag u.log2) +
        encodePair 12 v (Erdos1191Tags.tag v.log2) := by
      dsimp [E] at h
      omega
    obtain ⟨hadd, htags⟩ := encodePair_reflect (by decide) heq
    exact ⟨hadd, by simpa only [Nat.log2_eq_log_two] using Erdos1191Tags.tag_reflect htags⟩
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    intro a ha
    change 1 ≤ a ∧ a ≤ x / (1 + Nat.log 2 x) ^ 30 at ha
    change 1 ≤ E a ∧ E a ≤ x
    refine ⟨by dsimp [E]; omega, ?_⟩
    have hcutoff : a ≤ x / (1 + x.log2) ^ 30 := by
      simpa only [Nat.log2_eq_log_two] using ha.2
    exact encodePair_cutoff hx ha.1 hcutoff (Erdos1191Tags.tag_fits (Nat.le_succ _))

end Erdos1191Codec

/-- The finite packing condition is equivalent to the original infinite Sidon problem. -/
theorem Erdos1191Codec.finitePacking_iff :
    OMA.R_Erdos1191_erdos_1191_parts_ii_R1.H1 ↔ type_of% @Erdos1191.erdos_1191.parts.ii :=
  ⟨fun h ↦ OMA.R_Erdos1191_erdos_1191_parts_ii_R1.main h Erdos1191Codec.blockEncoder,
   OMA.R_Erdos1191_erdos_1191_parts_ii_R1.H1_of_target⟩

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_ii_R1.H2 := by
  exact Erdos1191Codec.blockEncoder
