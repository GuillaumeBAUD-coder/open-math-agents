import OMAReductions.R_OeisA238568_conjecture_4_R1
import Mathlib

namespace OMA.PackedConvolution

open Finset

def pack (base count : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ range count, f i * base^i

theorem pack_succ (base count : ℕ) (f : ℕ → ℕ) :
    pack base (count+1) f = f 0 + base * pack base count (fun i => f (i+1)) := by
  unfold pack
  rw [sum_range_succ', add_comm, Finset.mul_sum]
  simp only [pow_zero, mul_one, add_right_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ']
  ring

theorem digit_pack {base count i : ℕ} (f : ℕ → ℕ) (positive : 0 < base)
    (bound : ∀ j < count, f j < base) (hi : i < count) :
    pack base count f / base^i % base = f i := by
  induction count generalizing f i with
  | zero => omega
  | succ count ih =>
    rw [pack_succ]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (bound 0 (by omega))
    | succ i =>
      have hzero : f 0 / base = 0 := Nat.div_eq_of_lt (bound 0 (by omega))
      rw [pow_succ' base i, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ positive,
        hzero, Nat.zero_add]
      exact ih (fun j => f (j+1)) (fun j hj => bound (j+1) (by omega)) (by omega)

def convolution (m n : ℕ) (f g : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ range m, ∑ j ∈ range n, if k = i+j then f i*g j else 0

theorem pack_mul (base m n : ℕ) (f g : ℕ → ℕ) :
    pack base m f * pack base n g = pack base (m+n) (convolution m n f g) := by
  unfold pack convolution
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    ∑ i ∈ range m, ∑ j ∈ range n, (f i*base^i)*(g j*base^j) =
        ∑ i ∈ range m, ∑ j ∈ range n, ∑ k ∈ range (m+n),
          (if k=i+j then f i*g j else 0)*base^k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have ht : i+j ∈ range (m+n) := by
        have := mem_range.mp hi
        have := mem_range.mp hj
        rw [mem_range]
        omega
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos ht, pow_add]
      ring
    _ = ∑ i ∈ range m, ∑ k ∈ range (m+n), ∑ j ∈ range n,
        (if k=i+j then f i*g j else 0)*base^k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k ∈ range (m+n), ∑ i ∈ range m, ∑ j ∈ range n,
        (if k=i+j then f i*g j else 0)*base^k := Finset.sum_comm
    _ = ∑ k ∈ range (m+n),
        (∑ i ∈ range m, ∑ j ∈ range n, if k=i+j then f i*g j else 0)*base^k := by
      simp_rw [Finset.sum_mul]

theorem digit_mul {base m n k : ℕ} (f g : ℕ → ℕ) (positive : 0 < base)
    (bound : ∀ j < m+n, convolution m n f g j < base) (hi : k < m+n) :
    pack base m f * pack base n g / base^k % base = convolution m n f g k := by
  rw [pack_mul]
  exact digit_pack _ positive bound hi


theorem pack_lt_pow {base count : ℕ} (f : ℕ → ℕ)
    (bound : ∀ i < count, f i < base) :
    pack base count f < base^count := by
  induction count generalizing f with
  | zero => simp [pack]
  | succ count ih =>
    rw [pack_succ]
    let rest := pack base count (fun i => f (i+1))
    have tail : rest < base^count := ih _ (fun i hi => bound _ (by omega))
    have head : f 0 < base := bound 0 (by omega)
    change f 0 + base * rest < base^(count+1)
    calc
      _ < base + base*rest := Nat.add_lt_add_right head _
      _ = base*(rest+1) := by ring
      _ ≤ base*base^count := Nat.mul_le_mul_left _ (by omega)
      _ = base^(count+1) := (pow_succ' base count).symm

theorem pack_bit_in_lane (width count : ℕ) (f : ℕ → ℕ)
    (bound : ∀ i < count, f i < 2^width) {i bit : ℕ} (hi : i < count) (hb : bit < width) :
    (pack (2^width) count f).testBit (width*i+bit) = (f i).testBit bit := by
  let word := pack (2^width) count f
  calc
    word.testBit (width*i+bit) = (word / 2^(width*i)).testBit bit := by
      simpa only [Nat.add_comm] using (Nat.testBit_div_two_pow (n := width*i) word bit).symm
    _ = ((word / (2^width)^i)%2^width).testBit bit := by
      rw [Nat.pow_mul, Nat.testBit_mod_two_pow]
      simp [hb]
    _ = (f i).testBit bit := by
      rw [show word / (2^width)^i % 2^width = f i from digit_pack f (by positivity) bound hi]

theorem pack_testBit (width count : ℕ) (f : ℕ → ℕ)
    (widthPos : 0 < width) (bound : ∀ i < count, f i < 2^width) (j : ℕ) :
    (pack (2^width) count f).testBit j =
      if j/width<count then (f (j/width)).testBit (j%width) else false := by
  have address : width*(j/width)+j%width = j := by
    simpa [Nat.add_comm] using Nat.mod_add_div j width
  by_cases inside : j/width < count
  · rw [if_pos inside]
    calc
      _ = (pack (2^width) count f).testBit (width*(j/width)+j%width) :=
        congrArg (fun b => (pack (2^width) count f).testBit b) address.symm
      _ = _ := pack_bit_in_lane width count f bound inside (Nat.mod_lt _ widthPos)
  · rw [if_neg inside]
    have pos : width*count ≤ j := (Nat.mul_le_mul_left width (Nat.le_of_not_gt inside)).trans
      (by omega)
    apply Nat.testBit_lt_two_pow
    calc
      pack (2^width) count f < (2^width)^count := pack_lt_pow _ bound
      _ = 2^(width*count) := Nat.pow_mul 2 width count |>.symm
      _ ≤ 2^j := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) pos

end OMA.PackedConvolution

namespace OMA.SquareCountPilot

def repeatedBits (stride count : ℕ) : ℕ :=
  match count with
  | 0 => 0
  | 1 => 1
  | 2 => 1 + (1 <<< stride)
  | 3 => 1 + (1 <<< stride) + (1 <<< (2 * stride))
  | m + 4 => ((1 <<< (stride * (m + 4))) - 1) / ((1 <<< stride) - 1)


open Finset

theorem repeatedBits_eq_sum {stride : ℕ} (positive : 0 < stride) (count : ℕ) :
    repeatedBits stride count = ∑ i ∈ range count, 2^(stride*i) := by
  match count with
  | 0 => simp [repeatedBits]
  | 1 => simp [repeatedBits]
  | 2 => simp [repeatedBits, sum_range_succ, Nat.shiftLeft_eq]
  | 3 => simp [repeatedBits, sum_range_succ, Nat.shiftLeft_eq, Nat.mul_comm stride 2]
  | n + 4 =>
    have hb : 2 ≤ 2 ^ stride := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
    simp only [repeatedBits, Nat.shiftLeft_eq, one_mul]
    rw [pow_mul, ← Nat.geomSum_eq hb]
    simp only [pow_mul]

private theorem geometric_lt {stride : ℕ} (positive : 0 < stride) (count : ℕ) :
    (∑ i ∈ range count, 2^(stride*i)) < 2^(stride*count) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [sum_range_succ, Nat.mul_succ, pow_add]
    calc
      (∑ i ∈ range count, 2^(stride*i)) + 2^(stride*count) < 2^(stride*count)*2 := by omega
      _ ≤ 2^(stride*count)*2^stride := Nat.mul_le_mul_left _ (Nat.one_lt_two_pow (Nat.ne_of_gt positive))

private theorem testBit_geometric {stride : ℕ} (positive : 0 < stride) (count index : ℕ) :
    (∑ i ∈ range count, 2^(stride*i)).testBit index = true ↔
      ∃ i < count, stride*i = index := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [sum_range_succ, Nat.add_comm]
    rw [← Nat.mul_one (2^(stride*count)),
      Nat.testBit_two_pow_mul_add 1 (geometric_lt positive count)]
    by_cases before : index < stride*count
    · rw [if_pos before, ih]
      constructor
      · rintro ⟨i, hi, eq⟩
        exact ⟨i, by omega, eq⟩
      · rintro ⟨i, hi, eq⟩
        refine ⟨i, ?_, eq⟩
        by_contra! ge
        exact (Nat.not_lt_of_ge (eq ▸ Nat.mul_le_mul_left stride ge)) before
    · rw [if_neg before, Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · intro diff
        exact ⟨count, Nat.lt_succ_self _, by omega⟩
      · rintro ⟨i, hi, eq⟩
        by_contra! diff
        have bound := Nat.mul_le_mul_left stride (show i ≤ count by omega)
        omega

theorem testBit_repeatedBits {stride : ℕ} (positive : 0 < stride) (count index : ℕ) :
    (repeatedBits stride count).testBit index = true ↔ ∃ i < count, stride*i = index := by
  rw [repeatedBits_eq_sum positive]
  exact testBit_geometric positive count index

end OMA.SquareCountPilot

namespace OMA.PrimeProgression

abbrev Bit (word i : ℕ) := word.testBit i = true

def repeatMarks (p _depth k : ℕ) : ℕ :=
  if p=0 then if k=0 then 0 else 1 else OMA.SquareCountPilot.repeatedBits p k

private theorem or_bit {a b i : ℕ} : Bit (a ||| b) i ↔ Bit a i ∨ Bit b i := by simp [Bit]

private theorem shift_bit {a s i : ℕ} : Bit (a <<< s) i ↔ s ≤ i ∧ Bit a (i-s) := by simp [Bit]

private theorem one_mark {s i : ℕ} : Bit (1 <<< s) i ↔ i = s := by
  rw [shift_bit]
  by_cases h : s ≤ i
  · simp only [h, true_and, Bit, Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  · simp [h]
    omega

theorem repeatMarks_bit (p d k i : ℕ) (_hk : k < 2^d) :
    Bit (repeatMarks p d k) i ↔ ∃ j < k, i = p*j := by
  by_cases hp : p=0
  · subst p
    by_cases hz : k=0
    · subst k
      simp [repeatMarks, Bit]
    · simp [repeatMarks, hz, Bit, Nat.testBit_one_eq_true_iff_self_eq_zero]
      intro hi
      exact ⟨0, by omega⟩
  · simpa only [repeatMarks, if_neg hp, Bit, eq_comm] using
      (OMA.SquareCountPilot.testBit_repeatedBits (by omega : 0<p) k i)

def firstOffset (p base : ℕ) : ℕ :=
  p*p/2 + p*((base-p*p/2 +(p-1))/p) - base

def primeMarks (p depth base width : ℕ) : ℕ :=
  let offset := firstOffset p base
  if offset < width then
    repeatMarks p depth (1+(width-1-offset)/p) <<< offset
  else 0

def composite (ps : List ℕ) (depth base width : ℕ) : ℕ :=
  ps.foldr (fun p mask => primeMarks p depth base width ||| mask)
    (if base=0 then 1 else 0)

private theorem mark_contains {p d base width i j : ℕ} (hp : 0 < p)
    (hw : width < 2^d) (hi : i < width)
    (hj : base+i = p*p/2 + p*j) : Bit (primeMarks p d base width) i := by
  let start := p*p/2
  let need := base-start
  let q := (need+(p-1))/p
  change base+i = start+p*j at hj
  have hbase : base ≤ start+p*q := by
    have hmod := Nat.mod_lt (need+(p-1)) hp
    have hdiv := Nat.div_add_mod (need+(p-1)) p
    change p*q+(need+(p-1))%p=need+(p-1) at hdiv
    dsimp [need] at hdiv hmod
    omega
  have hq : q ≤ j := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [Nat.succ_mul, Nat.mul_comm j p]
    dsimp [need]
    omega
  let t := j-q
  let offset := firstOffset p base
  have ht : p*t = p*j-p*q := Nat.mul_sub p j q
  have hoff : offset = start+p*q-base := rfl
  have he : i = offset+p*t := by
    rw [ht,hoff]
    have hmul := Nat.mul_le_mul_left p hq
    omega
  have hinside : offset < width := by omega
  have hcount : t < 1+(width-1-offset)/p := by
    have hm : p*t ≤ width-1-offset := by omega
    have hdiv := (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.mul_comm] using hm : t*p ≤ width-1-offset)
    omega
  have hdepth : 1+(width-1-offset)/p < 2^d := by
    have hd := Nat.div_le_self (width-1-offset) p
    omega
  unfold primeMarks
  rw [if_pos hinside, shift_bit]
  refine ⟨by omega, (repeatMarks_bit _ _ _ _ hdepth).mpr ⟨t,hcount,?_⟩⟩
  omega

private theorem marked_if_mem {ps : List ℕ} {p depth base width i : ℕ}
    (hp : p ∈ ps) (hm : Bit (primeMarks p depth base width) i) :
    Bit (composite ps depth base width) i := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    change Bit (primeMarks q depth base width ||| composite ps depth base width) i
    rw [or_bit]
    rcases List.mem_cons.mp hp with rfl|h
    · exact Or.inl hm
    · exact Or.inr (ih h)

private theorem unit_marked (ps : List ℕ) (depth width : ℕ) :
    Bit (composite ps depth 0 width) 0 := by
  induction ps with
  | nil => simp [composite, Bit]
  | cons p ps ih =>
    change Bit (primeMarks p depth 0 width ||| composite ps depth 0 width) 0
    exact or_bit.mpr (Or.inr ih)

private theorem odd_factor {p q x : ℕ} (he : x=p*q) (odd : x%2=1) :
    p%2=1 ∧ q%2=1 := by
  rw [he, Nat.mul_mod] at odd
  have hp := Nat.mod_lt p (by decide : 0<2)
  have hq := Nat.mod_lt q (by decide : 0<2)
  have notp : p%2≠0 := by intro h; simp [h] at odd
  have notq : q%2≠0 := by intro h; simp [h] at odd
  omega

theorem unmarked_prime {ps : List ℕ} {bound depth base width i : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hwidth : width < 2^depth) (hi : i<width)
    (hxbound : 2*(base+i)+1 < (bound+1)^2)
    (hx : (composite ps depth base width).testBit i = false) :
    (2*(base+i)+1).Prime := by
  let x := 2*(base+i)+1
  have hpos : 0<x := by dsimp [x]; omega
  have hn : x ≠ 1 := by
    intro eq
    have hb : base=0 := by dsimp [x] at eq; omega
    have hz : i=0 := by dsimp [x] at eq; omega
    rw [hb,hz] at hx
    have hu := unit_marked ps depth width
    change (composite ps depth 0 width).testBit 0 = true at hu
    rw [hx] at hu
    contradiction
  by_contra notPrime
  let p := x.minFac
  have prime : p.Prime := Nat.minFac_prime hn
  have sq : p^2 ≤ x := Nat.minFac_sq_le_self hpos notPrime
  have small : p ≤ bound := by
    by_contra! h
    have hs : (bound+1)^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
    change x < (bound+1)^2 at hxbound
    omega
  obtain ⟨q, eq⟩ := Nat.minFac_dvd x
  change x = p*q at eq
  have odd : x%2=1 := by dsimp [x]; omega
  obtain ⟨op, oq⟩ := odd_factor eq odd
  have hp := prime.pos
  have order : p ≤ q := by
    rw [eq, pow_two] at sq
    exact Nat.le_of_mul_le_mul_left sq hp
  let j := (q-p)/2
  have qp : q=p+2*j := by dsimp [j]; omega
  have mul : p*q = p*p + 2*(p*j) := by rw [qp]; ring
  have oddSquare : (p*p)%2=1 := by rw [Nat.mul_mod,op]
  have hline : base+i = p*p/2+p*j := by dsimp [x] at eq; omega
  have hh := marked_if_mem (complete p small prime op) (mark_contains hp hwidth hi hline)
  change (composite ps depth base width).testBit i = true at hh
  rw [hx] at hh
  contradiction

end OMA.PrimeProgression

namespace OMA.PrimePopulation

def population (width word : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (word.testBit i).toNat

private theorem divide (left right word : ℕ) :
    population (left+right) word = population left word + population right (word >>> left) := by
  unfold population
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_shiftRight]

private theorem crop (width word : ℕ) :
    population width (word % (1 <<< width)) = population width word := by
  unfold population
  apply Finset.sum_congr rfl
  intro i member
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_mod_two_pow]
  simp [Finset.mem_range.mp member]

private def octet (word : ℕ) : ℕ := (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4*(word%256)))%16

set_option maxRecDepth 30000 in
private theorem octet_table : ∀ i : Fin 256, octet i.val = population 8 i.val := by decide +kernel

private theorem octet_exact (word : ℕ) : octet word = population 8 word := by
  have exact_table := octet_table ⟨word%256, Nat.mod_lt _ (by decide)⟩
  have lookup : octet (word%256) = octet word := by simp [octet]
  rw [lookup] at exact_table
  exact exact_table.trans (crop 8 word)

private def pop32 (word : ℕ) : ℕ :=
  octet word + (octet (word >>> 8) + (octet (word >>> 16) + octet (word >>> 24)))

private theorem pop32_exact (word : ℕ) : pop32 word = population 32 word := by
  rw [show (32 : ℕ) = 8+(8+(8+8)) by decide, divide 8 24, divide 8 16, divide 8 8]
  simp only [pop32, octet_exact, ← Nat.shiftRight_add]

private def width (n : ℕ) : ℕ := 32*2^n

private theorem double_width (n : ℕ) : width (n+1) = width n + width n := by
  simp [width, Nat.pow_succ, Nat.mul_two, Nat.mul_add]

private theorem population_full (n : ℕ) : population n ((1 <<< n)-1) = n := by
  unfold population
  calc
    _ = ∑ _i ∈ Finset.range n, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simp [Finset.mem_range.mp hi]
    _ = _ := by simp

def countBlock : ℕ → ℕ → ℕ
  | 0, word => if word = 0 then 0 else
      if word = (1 <<< width 0)-1 then width 0 else pop32 word
  | step+1, word =>
    if word = 0 then 0 else if word = (1 <<< width (step+1))-1 then width (step+1) else
      let half := width step
      countBlock step (word % (1 <<< half)) + countBlock step (word >>> half)

theorem exactCount (depth word : ℕ) : countBlock depth word = population (width depth) word := by
  induction depth generalizing word with
  | zero =>
    by_cases empty : word = 0
    · subst word
      simp [countBlock, population]
    · by_cases full : word = (1 <<< width 0)-1
      · rw [countBlock, if_neg empty, if_pos full, full, population_full]
      · rw [countBlock, if_neg empty, if_neg full]
        exact pop32_exact word
  | succ depth ih =>
    by_cases empty : word = 0
    · subst word
      simp [countBlock, population]
    · by_cases full : word = (1 <<< width (depth+1))-1
      · rw [countBlock, if_neg empty, if_pos full, full, population_full]
      · rw [countBlock, if_neg empty, if_neg full]
        dsimp only
        rw [ih, ih, double_width, divide, crop]

theorem boundedCount (left right word : ℕ) (fit : word < 2^left) :
    population (left+right) word = population left word := by
  have zero : word >>> left = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt fit
  rw [divide, zero]
  simp [population]

theorem card_eq (width word : ℕ) :
    population width word = ((Finset.range width).filter (fun i => word.testBit i)).card := by
  classical
  calc
    population width word = ∑ i ∈ Finset.range width, (if word.testBit i then (1:ℕ) else 0) := by
      unfold population
      apply Finset.sum_congr rfl
      intro i _
      cases word.testBit i <;> decide
    _ = _ := by simp

def prefixPop (depth width word : ℕ) : ℕ :=
  countBlock depth (word % (1 <<< width))

theorem prefixPop_exact {depth width word : ℕ} (h : width ≤ 32*2^depth) :
    prefixPop depth width word = population width word := by
  unfold prefixPop
  rw [exactCount]
  have hw : PrimePopulation.width depth = width+(PrimePopulation.width depth-width) := by
    change width ≤ PrimePopulation.width depth at h
    omega
  conv_lhs => rw [hw,divide,crop]
  have hz : (word % (1 <<< width)) >>> width = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity))
  simp [hz,population]

def oddCount (width : ℕ) : ℕ :=
  Nat.count (fun i => (2*i+1).Prime) width

def checkedSegment (ps : List ℕ) (markDepth popDepth base width : ℕ) : ℕ :=
  width - prefixPop popDepth width (OMA.PrimeProgression.composite ps markDepth base width)

theorem checkedSegment_lower {ps : List ℕ} {bound markDepth popDepth base width : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width < 2^markDepth)
    (hpop : width ≤ 32*2^popDepth)
    (limit : 2*(base+width) ≤ (bound+1)^2) :
    checkedSegment ps markDepth popDepth base width ≤
      Nat.count (fun i => (2*(base+i)+1).Prime) width := by
  let word := OMA.PrimeProgression.composite ps markDepth base width
  unfold checkedSegment
  change width - prefixPop popDepth width word ≤ _
  rw [prefixPop_exact hpop,card_eq,Nat.count_eq_card_filter_range]
  have all := Finset.card_filter_add_card_filter_not (s:=Finset.range width) (fun i => word.testBit i = true)
  rw [Finset.card_range] at all
  have decomp : width-((Finset.range width).filter fun i => word.testBit i = true).card =
      ((Finset.range width).filter fun i => ¬word.testBit i = true).card := by omega
  rw [decomp]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hin,hzero⟩ := Finset.mem_filter.mp hi
  have hlt := Finset.mem_range.mp hin
  exact Finset.mem_filter.mpr ⟨hin,OMA.PrimeProgression.unmarked_prime complete hw hlt
    (by omega) (Bool.eq_false_iff.mpr hzero)⟩

theorem checkedSegment_add {ps : List ℕ} {bound markDepth popDepth base width current : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width<2^markDepth) (hpop : width≤32*2^popDepth)
    (limit : 2*(base+width)≤(bound+1)^2) (hc : current ≤ oddCount base) :
    current + checkedSegment ps markDepth popDepth base width ≤ oddCount (base+width) := by
  unfold oddCount at hc ⊢
  rw [Nat.count_add]
  exact Nat.add_le_add hc (checkedSegment_lower complete hw hpop limit)

theorem oddCount_le_primeCounting {n slots : ℕ} (lo : 2 ≤ n) (hi : slots ≤ (n+1)/2) :
    1+oddCount slots ≤ n.primeCounting := by
  let f : ℕ ↪ ℕ := ⟨fun i => 2*i+1, by intro i j eq; change 2*i+1 = 2*j+1 at eq; omega⟩
  let odd := ((Finset.range slots).filter (fun i => (2*i+1).Prime)).map f
  have two : 2 ∉ odd := by
    intro h
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp h
    change 2*i+1 = 2 at eq
    omega
  have incl : insert 2 odd ⊆ Nat.primesLE n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_primesLE.mpr ⟨lo,Nat.prime_two⟩
    · obtain ⟨i,hi',eq⟩ := Finset.mem_map.mp hx
      obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hi'
      have hlt := Finset.mem_range.mp hr
      change 2*i+1 = x at eq
      exact Nat.mem_primesLE.mpr ⟨by omega,eq ▸ hp⟩
  have h := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem two,Nat.primesLE_card_eq_primeCounting] at h
  have hc : odd.card = oddCount slots := by
    unfold odd oddCount
    rw [Finset.card_map,Nat.count_eq_card_filter_range]
  omega

end OMA.PrimePopulation

namespace OMA.PrimePopulation

theorem oddCount_eq_primeCounting {n : ℕ} (hn : 2≤n) :
    n.primeCounting = 1+oddCount ((n+1)/2) := by
  apply le_antisymm ?_ (oddCount_le_primeCounting hn (slots := (n+1)/2) (le_refl _))
  let f : ℕ ↪ ℕ := ⟨fun i => 2*i+1, by
    intro i j eq
    change 2*i+1=2*j+1 at eq
    omega⟩
  let odd := ((Finset.range ((n+1)/2)).filter (fun i => (2*i+1).Prime)).map f
  have two : 2 ∉ odd := by
    intro has
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp has
    change 2*i+1=2 at eq
    omega
  have covers : Nat.primesLE n ⊆ insert 2 odd := by
    intro p hp
    obtain ⟨hpn,prime⟩ := Nat.mem_primesLE.mp hp
    apply Finset.mem_insert.mpr
    rcases prime.eq_two_or_odd with e|r
    · exact Or.inl e
    · right
      have value : 2*(p/2)+1=p := by omega
      have hlt : p/2<(n+1)/2 := by omega
      exact Finset.mem_map.mpr ⟨p/2,Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hlt,value.symm ▸ prime⟩,value⟩
  have h := Finset.card_le_card covers
  rw [Finset.card_insert_of_notMem two,Nat.primesLE_card_eq_primeCounting] at h
  have eq : odd.card=oddCount ((n+1)/2) := by
    unfold odd oddCount
    rw [Finset.card_map,Nat.count_eq_card_filter_range]
  omega

end OMA.PrimePopulation

/- The test uses each odd trial divisor up through the relevant square root. -/
namespace OMA.PrimeSieveBase

private def checks (trial q : ℕ) : Bool :=
  decide (3≤q ∧ q%2=1) &&
  (List.range' 3 (trial-2)).all (fun k => decide (q≤k ∨ q%k≠0))

def smallPrimes (bound trial : ℕ) : List ℕ :=
  (List.range (bound+1)).filter (checks trial)

theorem mem_smallPrimes {q bound trial : ℕ} (hq : q≤bound) (prime : q.Prime) (odd : q%2=1) :
    q ∈ smallPrimes bound trial := by
  unfold smallPrimes checks
  simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨by omega,⟨by have := prime.two_le; omega,odd⟩,?_⟩
  intro k member
  have lower := (List.mem_range'_1.mp member).1
  by_cases order : q≤k
  · exact Or.inl order
  · right
    intro zero
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero zero) (by omega) (by omega) prime

theorem prime_of_mem_smallPrimes {q bound trial : ℕ} (stop : bound<(trial+1)^2)
    (member : q ∈ smallPrimes bound trial) : q.Prime := by
  unfold smallPrimes checks at member
  simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at member
  obtain ⟨within,⟨large,odd⟩,filter⟩ := member
  by_contra hn
  let p := q.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have dvd : p∣q := Nat.minFac_dvd q
  have podd : p%2=1 := hp.eq_two_or_odd.resolve_left (by
    intro h
    rw [h] at dvd
    have zero := Nat.mod_eq_zero_of_dvd dvd
    omega)
  have plarge : 3≤p := by have := hp.two_le; omega
  have psmall : p≤trial := by
    by_contra! ht
    have hpow : (trial+1)^2≤p^2 := Nat.pow_le_pow_left ht 2
    have hl := Nat.minFac_sq_le_self (by omega : 0<q) hn
    change p^2≤q at hl
    omega
  have lt : p<q := (Nat.not_prime_iff_minFac_lt (by omega : 2≤q)).mp hn
  have hb : p ∈ List.range' 3 (trial-2) := List.mem_range'_1.mpr ⟨plarge,by omega⟩
  exact (filter p hb).elim (fun h => (Nat.not_le_of_lt lt) h) (fun h => h (Nat.mod_eq_zero_of_dvd dvd))

end OMA.PrimeSieveBase

namespace OMA.PrimePopulation

abbrev Row := ℕ × ℕ × ℕ × ℕ

def popDepth (span : ℕ) : ℕ :=
  if span ≤ 32 then 0 else (span/32).log2+1

private theorem depth_bound (span : ℕ) : span ≤ 32*2^(popDepth span) := by
  unfold popDepth
  split
  · simpa
  · have h : span/32 < 2^((span/32).log2+1) := Nat.lt_log2_self
    omega

def sliceOdd (word left span : ℕ) : ℕ :=
  span - prefixPop (popDepth span) span (word >>> left)

end OMA.PrimePopulation

namespace OMA.PrimeProgression

private theorem prime_of_no_mark {ps : List ℕ} {depth base width i : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (hw : width<2^depth)
    (prime : (2*(base+i)+1).Prime) : (composite ps depth base width).testBit i = false := by
  induction ps with
  | nil =>
    by_cases hb : base=0
    · subst base
      have hi : i≠0 := by intro hz; subst i; exact Nat.not_prime_one prime
      change (1 : ℕ).testBit i = false
      exact Bool.eq_false_iff.mpr fun ht => hi (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht)
    · simp [composite, hb]
  | cons p ps ih =>
    obtain ⟨hp, odd⟩ := roster p (by simp)
    have tail : (composite ps depth base width).testBit i = false :=
      ih (fun q hq => roster q (List.mem_cons_of_mem _ hq))
    change (primeMarks p depth base width ||| composite ps depth base width).testBit i = false
    rw [Nat.testBit_or, tail, Bool.or_false]
    by_contra hm
    have flagged : Bit (primeMarks p depth base width) i := by
      cases h : (primeMarks p depth base width).testBit i <;> simp_all [Bit]
    let s := p*p/2
    let k := (base-s+(p-1))/p
    let offset := firstOffset p base
    have hoff : offset = s+p*k-base := rfl
    have hbase : base ≤ s+p*k := by
      have hmod := Nat.mod_lt (base-s+(p-1)) hp.pos
      have hdiv := Nat.div_add_mod (base-s+(p-1)) p
      change p*k+(base-s+(p-1))%p=base-s+(p-1) at hdiv
      omega
    change Bit (if offset < width then repeatMarks p depth (1+(width-1-offset)/p) <<< offset else 0) i at flagged
    split at flagged
    · rename_i hinside
      rw [shift_bit] at flagged
      have hdepth : 1+(width-1-offset)/p < 2^depth := by
        have hd := Nat.div_le_self (width-1-offset) p
        omega
      obtain ⟨j, _, hj⟩ := (repeatMarks_bit _ _ _ _ hdepth).mp flagged.2
      have hrow : base+i=s+p*(k+j) := by rw [Nat.mul_add]; omega
      have parity : (p*p)%2=1 := by rw [Nat.mul_mod, odd]
      have hs : 2*s+1=p*p := by dsimp [s]; omega
      have factor : 2*(base+i)+1=p*(p+2*(k+j)) := by
        rw [hrow]
        calc
          2 * (s + p * (k + j)) + 1 = (2*s+1)+2*(p*(k+j)) := by ring
          _ = _ := by rw [hs]; ring
      have lt : p < 2*(base+i)+1 := by
        rw [factor]
        calc
          p < p*2 := by have := hp.pos; omega
          _ ≤ p*(p+2*(k+j)) := Nat.mul_le_mul_left _ (by have := hp.two_le; omega)
      exact (Nat.not_prime_of_dvd_of_lt ⟨_, factor⟩ hp.two_le lt) prime
    · simp [Bit] at flagged

theorem unmarked_iff_prime {ps : List ℕ} {bound depth base width i : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width<2^depth) (hi : i<width) (cap : 2*(base+width)≤(bound+1)^2) :
    (composite ps depth base width).testBit i = false ↔ (2*(base+i)+1).Prime :=
  ⟨unmarked_prime complete hw hi (by omega), prime_of_no_mark roster hw⟩

end OMA.PrimeProgression

namespace OMA.PrimePopulation

theorem sliceOdd_exact {ps : List ℕ} {bound markDepth base width left span : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width<2^markDepth) (cap : 2*(base+width)≤(bound+1)^2)
    (inside : left+span ≤ width) :
    sliceOdd (OMA.PrimeProgression.composite ps markDepth base width) left span =
      Nat.count (fun i => (2*(base+left+i)+1).Prime) span := by
  let word := OMA.PrimeProgression.composite ps markDepth base width
  unfold sliceOdd
  change span-prefixPop (popDepth span) span (word >>> left) = _
  rw [prefixPop_exact (depth_bound span), card_eq, Nat.count_eq_card_filter_range]
  have all := Finset.card_filter_add_card_filter_not (s:=Finset.range span)
    (fun i => (word >>> left).testBit i = true)
  rw [Finset.card_range] at all
  have decomp : span-((Finset.range span).filter fun i => (word >>> left).testBit i = true).card =
      ((Finset.range span).filter fun i => ¬(word >>> left).testBit i = true).card := by omega
  rw [decomp]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Bool.not_eq_true, Nat.testBit_shiftRight]
  constructor
  · intro ⟨hi, hm⟩
    exact ⟨hi, by simpa only [Nat.add_assoc] using
      (OMA.PrimeProgression.unmarked_iff_prime roster complete hw (by omega) cap).mp hm⟩
  · intro ⟨hi, hp⟩
    exact ⟨hi, (OMA.PrimeProgression.unmarked_iff_prime roster complete hw (by omega) cap).mpr
      (by simpa only [Nat.add_assoc] using hp)⟩

theorem from_two_endpoints {a b : ℕ} (ha : 2≤a) (hab : a≤b) :
    b.primeCounting-a.primeCounting =
      Nat.count (fun i => (2*((a+1)/2+i)+1).Prime) ((b+1)/2-(a+1)/2) := by
  let x := (a+1)/2
  let y := (b+1)/2
  rw [oddCount_eq_primeCounting ha, oddCount_eq_primeCounting (ha.trans hab)]
  let f : ℕ → Prop := fun i => (2*i+1).Prime
  change 1+Nat.count f y-(1+Nat.count f x) = Nat.count (fun i => f (x+i)) (y-x)
  have hsplit : Nat.count f y = Nat.count f x+Nat.count (fun i => f (x+i)) (y-x) := by
    conv_lhs => rw [show y=x+(y-x) by dsimp [x,y]; omega]
    exact Nat.count_add f x (y-x)
  omega

theorem index_bound {n k : ℕ} (hn : 0<n) (h : k.primeCounting<n) : k<Nat.nth Nat.Prime (n-1) := by
  by_contra! hk
  have hp := Nat.prime_nth_prime (n-1)
  have count : (Nat.nth Nat.Prime (n-1)).primeCounting = n := by
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    unfold Nat.primeCounting'
    rw [Nat.count_succ]
    simp only [hp, if_true]
    rw [show Nat.count Nat.Prime (Nat.nth Nat.Prime (n-1)) = n-1 from Nat.primeCounting'_nth_eq _]
    omega
  have := Nat.monotone_primeCounting hk
  omega

end OMA.PrimePopulation

namespace OMA.PrimeProgression

def checkedComposite (ps : List ℕ) (depth base width : ℕ) : ℕ :=
  ps.foldl (fun mask p => mask ||| primeMarks p depth base width)
    (if base=0 then 1 else 0)

theorem checkedComposite_eq (ps : List ℕ) (depth base width : ℕ) :
    checkedComposite ps depth base width = composite ps depth base width := by
  unfold checkedComposite composite
  have pure := List.foldl_eq_foldr (f := (· ||| ·))
    (l := ps.map (fun p => primeMarks p depth base width))
    (a := if base=0 then 1 else 0)
  simpa only [List.foldl_map, List.foldr_map] using pure

end OMA.PrimeProgression

namespace OMA.PrimeProgression

def fastOffset (p base : ℕ) : ℕ :=
  let first := p*p/2
  let start := max base first
  (start-base)+(p-(start-first)%p)%p

private theorem ceil_mul (p x : ℕ) (hp : 0<p) :
    p*((x+(p-1))/p) = x+(p-x%p)%p := by
  let q := x/p
  let r := x%p
  have divided : r+p*q=x := Nat.mod_add_div x p
  have hr : r<p := Nat.mod_lt _ hp
  have shape : x+(p-1) = p*q+(r+(p-1)) := by omega
  rw [shape,Nat.mul_add_div hp]
  change p*(q+(r+(p-1))/p)=x+(p-r)%p
  by_cases hz : r=0
  · rw [hz, zero_add, Nat.div_eq_of_lt (by omega : p-1<p), add_zero,
      Nat.sub_zero, Nat.mod_self, add_zero]
    omega
  · have hlow : 1 ≤ (r+(p-1))/p :=
      (Nat.le_div_iff_mul_le hp).mpr (by omega)
    have hhigh : (r+(p-1))/p < 2 :=
      (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have he : (r+(p-1))/p = 1 := by omega
    rw [he, Nat.mul_succ, Nat.mod_eq_of_lt (by omega : p-r<p)]
    omega

private theorem fastOffset_eq {p : ℕ} (hp : 0<p) (base : ℕ) :
    fastOffset p base = firstOffset p base := by
  unfold fastOffset firstOffset
  rw [ceil_mul _ _ hp]
  let first := p*p/2
  change max base first-base+(p-(max base first-first)%p)%p =
    first+(base-first+(p-(base-first)%p)%p)-base
  by_cases h : base ≤ first
  · rw [max_eq_right h, Nat.sub_eq_zero_of_le h]
    simp
  · rw [max_eq_left (by omega : first ≤ base)]
    omega

def strike (base width acc p : ℕ) : ℕ :=
  let offset := fastOffset p base
  if offset < width then
    let marks := OMA.SquareCountPilot.repeatedBits p (1+(width-1-offset)/p) <<< offset
    acc ||| marks
  else acc

private theorem strike_eq {p : ℕ} (hp : 0 < p) (depth base width acc : ℕ) :
    strike base width acc p = acc ||| primeMarks p depth base width := by
  unfold strike primeMarks
  rw [fastOffset_eq hp]
  by_cases h : firstOffset p base < width
  · simp [h, repeatMarks, Nat.ne_of_gt hp]
  · simp [h]

def fastComposite (ps : List ℕ) (base width : ℕ) : ℕ :=
  ps.foldl (strike base width) (if base=0 then 1 else 0)

private theorem strike_fold_eq {ps : List ℕ} (positive : ∀ p ∈ ps, 0<p)
    (depth base width acc : ℕ) :
    ps.foldl (strike base width) acc =
      ps.foldl (fun word p => word ||| primeMarks p depth base width) acc := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p tail ih =>
    simp only [List.foldl_cons]
    rw [strike_eq (positive p (by simp)) depth]
    exact ih (fun q hq => positive q (List.mem_cons_of_mem _ hq)) _

theorem fastComposite_eq {ps : List ℕ} (positive : ∀ p ∈ ps, 0<p)
    (depth base width : ℕ) :
    fastComposite ps base width = composite ps depth base width := by
  unfold fastComposite
  rw [strike_fold_eq positive depth]
  exact checkedComposite_eq ps depth base width

end OMA.PrimeProgression

namespace OMA.PackedConvolution

open Finset

private theorem pack_bitwise (width count : ℕ) (op : Bool → Bool → Bool)
    (opZero : op false false = false) (f g : ℕ → ℕ) (positive : 0 < width)
    (hf : ∀ i < count, f i < 2^width) (hg : ∀ i < count, g i < 2^width) :
    Nat.bitwise op (pack (2^width) count f) (pack (2^width) count g) =
      pack (2^width) count (fun i => Nat.bitwise op (f i) (g i)) := by
  have hfg : ∀ i < count, Nat.bitwise op (f i) (g i) < 2^width :=
    fun i hi => Nat.bitwise_lt_two_pow (hf i hi) (hg i hi)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_bitwise opZero, pack_testBit _ _ _ positive hf,
    pack_testBit _ _ _ positive hg, pack_testBit _ _ _ positive hfg]
  by_cases h : j/width < count
  · simp [h,Nat.testBit_bitwise opZero]
  · simp [h,opZero]

private theorem pack_and (width count : ℕ) (f g : ℕ → ℕ) (positive : 0 < width)
    (hf : ∀ i < count, f i < 2^width) (hg : ∀ i < count, g i < 2^width) :
    (pack (2^width) count f) &&& (pack (2^width) count g) =
      pack (2^width) count (fun i => f i &&& g i) :=
  pack_bitwise width count Bool.and rfl f g positive hf hg

private theorem pack_or (width count : ℕ) (f g : ℕ → ℕ) (positive : 0 < width)
    (hf : ∀ i < count, f i < 2^width) (hg : ∀ i < count, g i < 2^width) :
    (pack (2^width) count f) ||| (pack (2^width) count g) =
      pack (2^width) count (fun i => f i ||| g i) :=
  pack_bitwise width count Bool.or rfl f g positive hf hg

theorem pack_shiftLeft (base count shift : ℕ) (f : ℕ → ℕ) :
    (pack base count f) <<< shift = pack base count (fun i => f i <<< shift) := by
  simp only [pack,Nat.shiftLeft_eq,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem shifted_lt {x old shift cap : ℕ} (hx : x < 2^old) (hcap : old+shift ≤ cap) :
    x <<< shift < 2^cap := by
  rw [Nat.shiftLeft_eq]
  calc
    _ < 2^old*2^shift := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2^(old+shift) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hcap

private theorem high_half {x block : ℕ} (bound : x < 2^(2*block)) :
    x &&& ((2^block-1) <<< block) = (x >>> block) <<< block := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one]
  by_cases hb : block ≤ j
  · simp only [hb,decide_true,Bool.true_and,show block+(j-block)=j by omega]
    by_cases hj : j-block < block
    · simp [hj]
    · have hx : x < 2^j := bound.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega))
      simp [Nat.testBit_lt_two_pow hx]
  · simp [hb]

/-- Regroup the low and high halves of each radix digit as consecutive digits. -/
theorem pack_pairs (base count : ℕ) (low high : ℕ → ℕ) :
    pack (base^2) count (fun i => low i + base*high i) =
      pack base (2*count) (fun i => if i%2=0 then low (i/2) else high (i/2)) := by
  induction count generalizing low high with
  | zero => simp [pack]
  | succ count ih =>
    let pair := fun i : ℕ => if i%2=0 then low (i/2) else high (i/2)
    have hzero : pair 0 = low 0 := by simp [pair]
    have hone : pair (0+1) = high 0 := by simp [pair]
    have shift : (fun i => pair (i+1+1)) =
        (fun i => if i%2=0 then low (i/2+1) else high (i/2+1)) := by
      funext i
      simp only [pair, show (i+1+1)%2=i%2 by omega, show (i+1+1)/2=i/2+1 by omega]
    change pack (base^2) (count+1) (fun i => low i + base*high i) = pack base (2*(count+1)) pair
    rw [show 2*(count+1)=(2*count+1)+1 by omega,
      pack_succ (base^2) count, pack_succ base (2*count+1), pack_succ base (2*count),
      hzero, hone, shift, ← ih (fun i => low (i+1)) (fun i => high (i+1))]
    ring

/-- Expand each pair of adjacent blocks to two separate radix positions. -/
theorem spreadStep_eq_of_mask {lane block groups guard : ℕ} (f : ℕ → ℕ)
    (hlane : 0<lane) (hblock : 0<block) (hf : ∀ i < groups, f i < 2^(2*block))
    (hguard : guard = pack (2^(lane*(2*block))) groups (fun _ => 2^block-1)) :
    let word := pack (2^(lane*(2*block))) groups f
    (word &&& guard) ||| ((word &&& (guard <<< block)) <<< ((lane-1)*block)) =
      pack (2^(lane*block)) (2*groups)
        (fun i => if i%2=0 then f (i/2)%2^block else f (i/2)/2^block) := by
  let w := lane*block
  let width := lane*(2*block)
  let base := (2 : ℕ)^width
  let half := (2 : ℕ)^block
  have hw : block ≤ w := by
    simpa only [one_mul] using Nat.mul_le_mul_right block (show 1 ≤ lane by omega)
  have hwidth : width = 2*w := by dsimp [width,w]; ring
  have len : 0 < width := by dsimp [width]; positivity
  have half_lt : half-1 < half := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have extend : 2*block ≤ width := by rw [hwidth]; omega
  have grow : block+(lane-1)*block=w := by
    dsimp [w]
    rw [Nat.sub_mul,one_mul]
    change block ≤ lane*block at hw
    omega
  have fits : ∀ i < groups, f i < 2^width :=
    fun i hi => (hf i hi).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) extend)
  have maskFits : ∀ _i : ℕ, _i < groups → half-1 < 2^width :=
    fun _ _ => half_lt.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega))
  have hiMaskFits : ∀ _i : ℕ, _i < groups → (half-1) <<< block < 2^width :=
    fun _ _ => shifted_lt half_lt (by omega)
  let lo := fun i => f i % half
  let hi := fun i => (f i / half) <<< w
  have hlo (i : ℕ) : lo i < 2^w :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hw)
  have hlo' (i : ℕ) (_ : i<groups) : lo i < 2^width :=
    (hlo i).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega))
  have hhi (i : ℕ) (hin : i<groups) : hi i < 2^width := by
    apply shifted_lt _ (by omega : block+w ≤ width)
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add]
    simpa only [two_mul] using hf i hin
  have lower : (pack base groups f) &&& guard = pack base groups lo := by
    rw [show guard = pack (2^width) groups (fun _ => half-1) from hguard]
    rw [pack_and width groups f (fun _ => half-1) len fits maskFits]
    simp only [lo,half,base,Nat.and_two_pow_sub_one_eq_mod]
  have upper : ((pack base groups f) &&& (guard <<< block)) <<< ((lane-1)*block) = pack base groups hi := by
    rw [show guard = pack (2^width) groups (fun _ => half-1) from hguard,pack_shiftLeft,
      pack_and width groups f (fun _ => (half-1) <<< block) len fits hiMaskFits,pack_shiftLeft]
    unfold pack
    apply Finset.sum_congr rfl
    intro i hmem
    change ((f i &&& ((half-1) <<< block)) <<< ((lane-1)*block))*base^i = hi i*base^i
    rw [show f i &&& ((half-1) <<< block) = (f i >>> block) <<< block from high_half (hf i (mem_range.mp hmem))]
    apply congrArg (fun value => value*base^i)
    simp only [hi,half,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,Nat.mul_assoc,← pow_add,grow]
  have both : (pack base groups lo) ||| (pack base groups hi) =
      pack base groups (fun i => lo i + 2^w*(f i / half)) := by
    rw [pack_or width groups lo hi len hlo' hhi]
    unfold pack
    apply Finset.sum_congr rfl
    intro i _
    change (lo i ||| ((f i / half) <<< w))*base^i = (lo i + 2^w*(f i / half))*base^i
    rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (hlo i),Nat.shiftLeft_eq]
    congr 1
    ring
  change ((pack base groups f) &&& guard) |||
      (((pack base groups f) &&& (guard <<< block)) <<< ((lane-1)*block)) = _
  rw [lower,upper,both,show base=(2^w)^2 by dsimp [base]; rw [hwidth,Nat.mul_comm 2 w,Nat.pow_mul]]
  exact pack_pairs (2^w) groups lo (fun i => f i / half)

end OMA.PackedConvolution

namespace OMA.SquareCountPilot

open Finset OMA.PackedConvolution

def spreadStep (lane bits scale word : ℕ) : ℕ :=
  let block := 1 <<< scale
  let groups := 1 <<< (bits - 1 - scale)
  let guard := ((1 <<< block) - 1) * repeatedBits (lane * (2 * block)) groups
  (word &&& guard) ||| ((word &&& (guard <<< block)) <<< ((lane-1)*block))

def spread (lane bits word : ℕ) : ℕ :=
  (List.range bits).reverse.foldl (spreadStep lane bits |> fun step n i => step i n) word

private def rawDigit (source block i : ℕ) : ℕ := source / 2^(block*i) % 2^block

private theorem split_rawDigit (source block i : ℕ) :
    (if i%2=0 then rawDigit source (2*block) (i/2) % 2^block
      else rawDigit source (2*block) (i/2) / 2^block) = rawDigit source block i := by
  have address : block*i = 2*block*(i/2) + block*(i%2) := by
    calc
      block*i = block*(2*(i/2)+i%2) := congrArg (fun n => block*n) (by omega)
      _ = _ := by ring
  have splitPower : (2:ℕ)^(2*block) = 2^block*2^block := by rw [two_mul,pow_add]
  by_cases even : i%2=0
  · rw [if_pos even]
    simp only [even,mul_zero,add_zero] at address
    unfold rawDigit
    rw [address,splitPower,Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)]
  · rw [if_neg even]
    have odd : i%2=1 := by omega
    simp only [odd,mul_one] at address
    unfold rawDigit
    rw [splitPower,Nat.mod_mul_right_div_self,Nat.div_div_eq_div_mul,← pow_add,address]

private theorem guard_pack (lane block groups : ℕ) (positive : 0 < lane*(2*block)) :
    (2^block-1) * repeatedBits (lane*(2*block)) groups =
      pack (2^(lane*(2*block))) groups (fun _ => 2^block-1) := by
  rw [repeatedBits_eq_sum positive,Finset.mul_sum]
  unfold pack
  simp only [pow_mul]

private theorem spreadStep_eq (lane bits scale source : ℕ) (hlane : 0<lane) :
    spreadStep lane bits scale
      (pack (2^(lane*(2*2^scale))) (2^(bits-1-scale)) (rawDigit source (2*2^scale))) =
      pack (2^(lane*2^scale)) (2*2^(bits-1-scale)) (rawDigit source (2^scale)) := by
  unfold spreadStep
  have powerShift (n : ℕ) : (1 : ℕ) <<< n = 2^n := by simp [Nat.shiftLeft_eq]
  simp only [powerShift]
  let block := (2:ℕ)^scale
  let groups := (2:ℕ)^(bits-1-scale)
  have hp : 0<block := Nat.two_pow_pos _
  have hg := guard_pack lane block groups (by positivity)
  have hf : ∀ i < groups, rawDigit source (2*block) i < 2^(2*block) :=
    fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _)
  change _ = pack (2^(lane*block)) (2*groups) (rawDigit source block)
  refine (spreadStep_eq_of_mask (rawDigit source (2*block)) hlane hp hf hg).trans ?_
  exact congrArg (pack (2^(lane*block)) (2*groups)) (funext (split_rawDigit source block))

private theorem spread_fold (lane bits stages source : ℕ) (hlane : 0<lane) (hstages : stages≤bits) :
    (List.range stages).reverse.foldl (fun word i => spreadStep lane bits i word)
      (pack (2^(lane*2^stages)) (2^(bits-stages)) (rawDigit source (2^stages))) =
      pack (2^lane) (2^bits) (rawDigit source 1) := by
  induction stages with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,List.foldl_cons]
    have step : spreadStep lane bits i
        (pack (2^(lane*2^(i+1))) (2^(bits-(i+1))) (rawDigit source (2^(i+1)))) =
        pack (2^(lane*2^i)) (2^(bits-i)) (rawDigit source (2^i)) := by
      rw [show (2:ℕ)^(i+1)=2*2^i by exact pow_succ' 2 i,
        show bits-(i+1)=bits-1-i by omega, spreadStep_eq _ _ _ _ hlane]
      rw [show bits-i=(bits-1-i)+1 by omega,pow_succ']
    rw [step]
    exact ih (by omega)

theorem spread_eq_pack (lane bits source : ℕ) (hlane : 0<lane) (hsize : source < 2^(2^bits)) :
    spread lane bits source = pack (2^lane) (2^bits) (fun i => source / 2^i % 2) := by
  have start : source = pack (2^(lane*2^bits)) (2^(bits-bits)) (rawDigit source (2^bits)) := by
    simp [pack,rawDigit,Nat.mod_eq_of_lt hsize]
  unfold spread
  calc
    _ = (List.range bits).reverse.foldl (fun word i => spreadStep lane bits i word)
        (pack (2^(lane*2^bits)) (2^(bits-bits)) (rawDigit source (2^bits))) :=
      congrArg ((List.range bits).reverse.foldl (fun word i => spreadStep lane bits i word)) start
    _ = pack (2^lane) (2^bits) (rawDigit source 1) := spread_fold lane bits bits source hlane le_rfl
    _ = pack (2^lane) (2^bits) (fun i => source / 2^i % 2) :=
      congrArg (pack (2^lane) (2^bits)) (funext (fun i => by simp [rawDigit]))

end OMA.SquareCountPilot

namespace OMA.PackedPrimeCensus

open Finset OMA.PackedConvolution

def bitValue (word i : ℕ) : ℕ := word / 2^i % 2

theorem bitValue_le (word i : ℕ) : bitValue word i ≤ 1 := by
  unfold bitValue
  have := Nat.mod_lt (word / 2^i) (by decide : 0 < 2)
  omega

theorem bitValue_eq (word i : ℕ) : bitValue word i = (word.testBit i).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := bitValue_le word i
  unfold bitValue at *
  rcases Nat.mod_two_eq_zero_or_one (word / 2^i) with h0 | h1
  · simp [h0]
  · simp [h1]

private theorem convolve_ones (f : ℕ → ℕ) (m n k : ℕ) :
    OMA.PackedConvolution.convolution m n f (fun _ => 1) k =
      ∑ i ∈ range m, if i ≤ k ∧ k - i < n then f i else 0 := by
  unfold OMA.PackedConvolution.convolution
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ k
  · have eq (j : ℕ) : k = i+j ↔ j = k-i := by omega
    simp_rw [eq, mul_one]
    simp [Finset.sum_ite_eq', Finset.mem_range, hi]
  · have neq (j : ℕ) : ¬ k = i+j := by omega
    simp [hi, neq]

private theorem convolve_ones_bound (word m n k : ℕ) :
    OMA.PackedConvolution.convolution m n (bitValue word) (fun _ => 1) k ≤ m := by
  rw [convolve_ones]
  calc
    _ ≤ ∑ i ∈ range m, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      split
      · exact bitValue_le word i
      · exact Nat.zero_le _
    _ = m := by simp

private theorem convolve_ones_prefix {word m n k : ℕ} (hm : k < m) (hn : k < n) :
    OMA.PackedConvolution.convolution m n (bitValue word) (fun _ => 1) k =
      ∑ i ∈ range (k+1), bitValue word i := by
  rw [convolve_ones]
  calc
    _ = ∑ i ∈ range (k+1), if i ≤ k ∧ k-i < n then bitValue word i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ hi
      rw [Finset.mem_range] at hi
      have hn' : ¬ i ≤ k := by omega
      simp [hn']
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ k := by simpa [Finset.mem_range] using hi
      have hb : k-i < n := (Nat.sub_le _ _).trans_lt hn
      simp [hi',hb]

def laneDigit (lane word k : ℕ) : ℕ := word / (2^lane)^k % 2^lane

private theorem laneDigit_zero (lane word : ℕ) :
    laneDigit lane (word <<< lane) 0 = 0 := by
  simp [laneDigit, Nat.shiftLeft_eq]

private theorem laneDigit_succ (lane word k : ℕ) :
    laneDigit lane (word <<< lane) (k+1) = laneDigit lane word k := by
  unfold laneDigit
  rw [Nat.shiftLeft_eq, pow_succ' (2^lane) k, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ (Nat.two_pow_pos lane)]

theorem cumulative_digit {lane size width word k : ℕ}
    (hbase : size < 2^lane) (hsize : width ≤ size) (hk : k ≤ width) :
    laneDigit lane
      ((pack (2^lane) size (bitValue word) * pack (2^lane) width (fun _ => 1)) <<< lane) k =
      ∑ j ∈ range k, bitValue word j := by
  cases k with
  | zero => simp [laneDigit_zero]
  | succ k =>
    rw [laneDigit_succ]
    unfold laneDigit
    rw [digit_mul _ _ (Nat.two_pow_pos lane)
      (fun j _ => (convolve_ones_bound word size width j).trans_lt hbase) (by omega)]
    exact convolve_ones_prefix (by omega) (by omega)

private theorem laneDigit_mask (lane word k : ℕ) :
    laneDigit lane word k = (word >>> (lane*k)) &&& ((1 <<< lane)-1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul]
  rfl

theorem laneDigit_and (lane a b k : ℕ) :
    laneDigit lane (a &&& b) k = laneDigit lane a k &&& laneDigit lane b k := by
  simp only [laneDigit_mask]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight]
  cases ha : a.testBit (lane*k+i) <;>
    cases hb : b.testBit (lane*k+i) <;>
    cases hc : (((1 : ℕ) <<< lane)-1).testBit i <;> simp

theorem laneDigit_or (lane a b k : ℕ) :
    laneDigit lane (a ||| b) k = laneDigit lane a k ||| laneDigit lane b k := by
  simp only [laneDigit_mask]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight]
  cases ha : a.testBit (lane*k+i) <;>
    cases hb : b.testBit (lane*k+i) <;>
    cases hc : (((1 : ℕ) <<< lane)-1).testBit i <;> simp

theorem laneDigit_shift {lane value src dst : ℕ} (hval : value < 2^lane) :
    laneDigit lane (value <<< (lane*src)) dst = if dst=src then value else 0 := by
  rw [laneDigit_mask]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < lane
  · by_cases h : dst = src
    · subst src
      simp [hi, show lane*dst ≤ lane*dst+i by omega, show lane*dst+i-lane*dst=i by omega]
    · rw [if_neg h]
      simp only [hi, decide_true, Bool.and_true, Nat.zero_testBit]
      rcases lt_or_gt_of_ne h with hlt|hgt
      · have hm := Nat.mul_le_mul_left lane (show dst+1 ≤ src by omega)
        rw [Nat.mul_succ] at hm
        simp [show ¬ lane*src ≤ lane*dst+i by omega]
      · have hm := Nat.mul_le_mul_left lane (show src+1 ≤ dst by omega)
        rw [Nat.mul_succ] at hm
        have hb : value < 2^(lane*dst+i-lane*src) :=
          hval.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
        simp [Nat.testBit_lt_two_pow hb]
  · have hv : value.testBit i = false := Nat.testBit_lt_two_pow
      (hval.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    by_cases h : dst = src <;> simp [hi,h,hv]

private theorem laneDigit_and_full (lane word k : ℕ) :
    laneDigit lane word k &&& (2^lane-1) = laneDigit lane word k := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos lane))

end OMA.PackedPrimeCensus

namespace OMA.PackedPrimeCensus

def selectLanes (lane : ℕ) (value : ℕ × ℕ → ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | row :: rest => (value row <<< (lane * row.1)) ||| selectLanes lane value rest

private theorem laneDigit_select_absent {lane index : ℕ} (value : ℕ × ℕ → ℕ)
    {rows : List (ℕ × ℕ)} (bounds : ∀ row ∈ rows, value row < 2^lane)
    (absent : index ∉ rows.map Prod.fst) :
    laneDigit lane (selectLanes lane value rows) index = 0 := by
  induction rows with
  | nil => simp [selectLanes, laneDigit]
  | cons head tail ih =>
    have hhead : index ≠ head.1 := fun h => absent (by simp [h])
    have htail : index ∉ tail.map Prod.fst := fun h => absent (by simp [h])
    rw [selectLanes, laneDigit_or, laneDigit_shift (bounds head (by simp)), if_neg hhead,
      ih (fun row hr => bounds row (List.mem_cons_of_mem _ hr)) htail]
    simp

private theorem laneDigit_select {lane : ℕ} (value : ℕ × ℕ → ℕ)
    {rows : List (ℕ × ℕ)} {row : ℕ × ℕ} (member : row ∈ rows)
    (unique : (rows.map Prod.fst).Nodup) (bounds : ∀ q ∈ rows, value q < 2^lane) :
    laneDigit lane (selectLanes lane value rows) row.1 = value row := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rw [selectLanes, laneDigit_or, laneDigit_shift (bounds head (by simp))]
    rcases List.mem_cons.mp member with he|ht
    · subst head
      rw [if_pos rfl, laneDigit_select_absent value
        (fun q hq => bounds q (List.mem_cons_of_mem _ hq)) unique.1]
      simp
    · have unequal : row.1 ≠ head.1 := fun ho =>
        unique.1 (ho ▸ List.mem_map.mpr ⟨row,ht,rfl⟩)
      rw [if_neg unequal, ih ht unique.2 (fun q hq => bounds q (List.mem_cons_of_mem _ hq))]
      simp

private def selectors (lane : ℕ) (rows : List (ℕ × ℕ)) : ℕ × ℕ :=
  rows.foldl (fun acc row =>
    let off := lane * row.1
    (acc.1 ||| (((1 <<< lane)-1) <<< off), acc.2 ||| (row.2 <<< off))) (0,0)

private theorem selectors_fold (lane : ℕ) (rows : List (ℕ × ℕ)) (a b : ℕ) :
    rows.foldl (fun acc row =>
      let off := lane * row.1
      (acc.1 ||| (((1 <<< lane)-1) <<< off), acc.2 ||| (row.2 <<< off))) (a,b) =
    (a ||| selectLanes lane (fun _ => (1 <<< lane)-1) rows,
     b ||| selectLanes lane Prod.snd rows) := by
  induction rows generalizing a b with
  | nil => simp [selectLanes]
  | cons row tail ih =>
    rw [List.foldl_cons, ih]
    simp [selectLanes, Nat.or_assoc]

private theorem selectors_spec (lane : ℕ) (rows : List (ℕ × ℕ)) :
    selectors lane rows =
      (selectLanes lane (fun _ => (1 <<< lane)-1) rows, selectLanes lane Prod.snd rows) := by
  unfold selectors
  rw [selectors_fold]
  simp

def matchLanes (lane word : ℕ) (rows : List (ℕ × ℕ)) : Prop :=
  let cuts := selectors lane rows
  (word &&& cuts.1) = cuts.2

instance (lane word : ℕ) (rows : List (ℕ × ℕ)) : Decidable (matchLanes lane word rows) := by
  unfold matchLanes
  infer_instance

theorem matchLanes_sound {lane word : ℕ} {rows : List (ℕ × ℕ)} {row : ℕ × ℕ}
    (member : row ∈ rows) (unique : (rows.map Prod.fst).Nodup)
    (bounds : ∀ q ∈ rows, q.2 < 2^lane) (checked : matchLanes lane word rows) :
    laneDigit lane word row.1 = row.2 := by
  unfold matchLanes at checked
  rw [selectors_spec] at checked
  have eq := congrArg (fun x => laneDigit lane x row.1) checked
  rw [laneDigit_and, laneDigit_select _ member unique (fun _ _ => by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    have := Nat.two_pow_pos lane
    omega), laneDigit_select _ member unique bounds, Nat.shiftLeft_eq, Nat.one_mul,
    laneDigit_and_full] at eq
  exact eq

end OMA.PackedPrimeCensus

namespace OMA.PrimeDifference

open OMA.PrimePopulation OMA.PrimeProgression

def oddSlot (x : ℕ) : ℕ := (x+1)/2

private theorem sieveDifference {ps : List ℕ} {bound depth base width a b : ℕ}
    (primes : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width < 2^depth) (cap : 2*(base+width) ≤ (bound+1)^2)
    (lo : 2 ≤ a) (ord : a ≤ b) (ha : base ≤ oddSlot a) (hb : oddSlot b ≤ base+width) :
    sliceOdd (composite ps depth base width) (oddSlot a-base) (oddSlot b-oddSlot a) =
      b.primeCounting-a.primeCounting := by
  have hslots : oddSlot a ≤ oddSlot b := by unfold oddSlot; omega
  have inside : oddSlot a-base+(oddSlot b-oddSlot a) ≤ width := by omega
  rw [sliceOdd_exact primes complete hw cap inside, from_two_endpoints lo ord]
  rw [show base+(oddSlot a-base)=oddSlot a by omega]
  rfl

private def primeGate (q : ℕ) : Bool :=
  if q ≤ 128 then decide q.Prime else decide (q ≤ 16384 ∧ q.Coprime (Nat.factorial 128))

private theorem primeGate_sound {q : ℕ} (h : primeGate q = true) : q.Prime := by
  unfold primeGate at h
  split at h
  · exact of_decide_eq_true h
  · rename_i hsmall
    obtain ⟨hu, hc⟩ := of_decide_eq_true h
    by_contra hprime
    let p := q.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hs : p^2 ≤ q := Nat.minFac_sq_le_self (by omega) hprime
    have hlim : p ≤ 128 := by
      by_contra! hgt
      have hn : (129 : ℕ)^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hcommon : p ∣ Nat.gcd q (Nat.factorial 128) :=
      Nat.dvd_gcd (Nat.minFac_dvd _) (Nat.dvd_factorial hp.pos hlim)
    have hg : Nat.gcd q (Nat.factorial 128) = 1 := hc
    rw [hg] at hcommon
    have := hp.two_le
    have := Nat.dvd_one.mp hcommon
    omega

structure Row where
  n : ℕ
  k : ℕ
  low : ℕ
  high : ℕ

private def startAt (row : Row) : ℕ := oddSlot (row.k*row.n)
private def stopAt (row : Row) : ℕ := oddSlot (row.n^2)
private def span (row : Row) : ℕ := stopAt row - startAt row

def statementsAt (base : ℕ) (rows : List Row) : List (ℕ × ℕ) :=
  (rows.flatMap fun r => [(startAt r-base,r.low),(stopAt r-base,r.high)]).eraseDups

private theorem left_mem {base : ℕ} {rows : List Row} {r : Row} (hr : r ∈ rows) :
    (startAt r-base,r.low) ∈ statementsAt base rows := by
  unfold statementsAt
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨r,hr,by simp⟩

private theorem right_mem {base : ℕ} {rows : List Row} {r : Row} (hr : r ∈ rows) :
    (stopAt r-base,r.high) ∈ statementsAt base rows := by
  unfold statementsAt
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨r,hr,by simp⟩

def rowGate (base width : ℕ) (r : Row) : Bool :=
  decide (2 < r.n ∧ 0 < r.k ∧ r.k < r.n ∧ base ≤ startAt r ∧ stopAt r ≤ base+width) &&
  primeGate (span r-(r.high-r.low))

def hasWitness (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < n ∧
    Nat.Prime (Nat.primeCounting (n^2)-Nat.primeCounting (k*n))

theorem rowGate_sound {ps : List ℕ} {bound depth base width : ℕ} {rows : List Row} {r : Row}
    (primes : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width < 2^depth) (cap : 2*(base+width) ≤ (bound+1)^2)
    (hcount : ∀ q ∈ statementsAt base rows,
      population q.1 (composite ps depth base width) = q.2)
    (hr : r ∈ rows) (h : rowGate base width r = true) : hasWitness r.n := by
  simp only [rowGate,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hn,hk,hkn,hlo,hhi⟩,hp⟩ := h
  have hleft := hcount _ (left_mem hr)
  have hright := hcount _ (right_mem hr)
  let word := composite ps depth base width
  change population (startAt r-base) word = r.low at hleft
  change population (stopAt r-base) word = r.high at hright
  have ha : 2 ≤ r.k*r.n := (by omega : 2 ≤ r.n).trans
    (by simpa using Nat.mul_le_mul_right r.n (show 1 ≤ r.k by omega))
  have hab : r.k*r.n ≤ r.n^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  have hs : startAt r ≤ stopAt r := by
    unfold startAt stopAt oddSlot
    omega
  have heq := sieveDifference primes complete hw cap ha hab hlo hhi
  have hsame :
      population (stopAt r-base) word =
        population (startAt r-base) word + population (span r) (word >>> (startAt r-base)) := by
    calc
      _ = population ((startAt r-base)+span r) word := by
        congr 1
        unfold span
        omega
      _ = _ := divide _ _ _
  have hpop : population (span r) (word >>> (startAt r-base)) = r.high-r.low := by
    omega
  have hslice : sliceOdd word (startAt r-base) (span r) = span r-(r.high-r.low) := by
    unfold sliceOdd
    rw [prefixPop_exact (depth_bound _), hpop]
  refine ⟨r.k,hk,hkn,?_⟩
  change sliceOdd word (startAt r-base) (span r) =
    (r.n^2).primeCounting-(r.k*r.n).primeCounting at heq
  rw [← heq, hslice]
  exact primeGate_sound hp

def covers (lower upper : ℕ) : Prop := ∀ n, lower ≤ n → n ≤ upper → hasWitness n

theorem covers_from_rows {lower upper : ℕ} {rows : List Row}
    (indices : rows.map Row.n = List.range' lower (upper+1-lower))
    (good : ∀ r ∈ rows, hasWitness r.n) : covers lower upper := by
  intro n hlo hhi
  have hmem : n ∈ List.range' lower (upper+1-lower) :=
    List.mem_range'.mpr ⟨n-lower, by omega, by omega⟩
  rw [← indices] at hmem
  obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hmem
  exact good row hrow

theorem covers_join {lower mid upper : ℕ}
    (left : covers lower mid) (right : covers (mid+1) upper) : covers lower upper := by
  intro n ha hb
  by_cases hm : n ≤ mid
  · exact left n ha hm
  · exact right n (by omega) hb

end OMA.PrimeDifference

namespace OMA.PackedPrimeCensus

open Finset
open OMA.PackedConvolution OMA.SquareCountPilot
open OMA.PrimePopulation OMA.PrimeProgression OMA.PrimeDifference

def laneCounts (lane depth width word : ℕ) : ℕ :=
  (spread lane depth (word &&& ((1 <<< width)-1)) * repeatedBits lane width) <<< lane

private theorem repeatedBits_pack {lane : ℕ} (positive : 0 < lane) (width : ℕ) :
    repeatedBits lane width = pack (2^lane) width (fun _ => 1) := by
  rw [repeatedBits_eq_sum positive]
  unfold pack
  simp [Nat.pow_mul]

theorem laneCounts_sound {lane depth width k : ℕ} (word : ℕ)
    (hpos : 0 < lane) (hwidth : width ≤ 2^depth) (hcap : 2^depth < 2^lane)
    (hk : k ≤ width) :
    laneDigit lane (laneCounts lane depth width word) k = population k word := by
  let cropped := word &&& ((1 <<< width)-1)
  have hl : cropped < 2^(2^depth) := by
    have hsmall : cropped < 2^width := by
      unfold cropped
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    exact hsmall.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hwidth)
  unfold laneCounts
  rw [spread_eq_pack lane depth cropped hpos hl, repeatedBits_pack hpos]
  change laneDigit lane
    ((pack (2^lane) (2^depth) (bitValue cropped) *
      pack (2^lane) width (fun _ => 1)) <<< lane) k = _
  rw [cumulative_digit (word := cropped) hcap hwidth hk]
  unfold population
  apply Finset.sum_congr rfl
  intro j hj
  have hinside : j < width := (Finset.mem_range.mp hj).trans_le hk
  rw [bitValue_eq]
  simp [cropped, Nat.shiftLeft_eq, hinside]

private def pointCover (base : ℕ) (points : List (ℕ × ℕ)) (r : OMA.PrimeDifference.Row) : Bool :=
  points.contains (startAt r-base,r.low) && points.contains (stopAt r-base,r.high)

private theorem pointCover_all {base : ℕ} {points : List (ℕ × ℕ)} {rows : List OMA.PrimeDifference.Row}
    (h : rows.all (pointCover base points) = true) :
    ∀ q ∈ statementsAt base rows, q ∈ points := by
  intro q hq
  unfold statementsAt at hq
  rw [List.mem_eraseDups, List.mem_flatMap] at hq
  obtain ⟨r, hr, hm⟩ := hq
  have hs := List.all_eq_true.mp h r hr
  simp only [pointCover, Bool.and_eq_true, List.contains_iff_mem] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl
  · exact hs.1
  · exact hs.2

private def groupData (base width first last : ℕ) (rows : List OMA.PrimeDifference.Row)
    (points : List (ℕ × ℕ)) : Prop :=
  rows.map OMA.PrimeDifference.Row.n = List.range' first (last+1-first) ∧
  rows.all (rowGate base width) = true ∧
  rows.all (pointCover base points) = true ∧
  (points.map Prod.fst).Nodup ∧
  points.all (fun pair => decide (pair.1 ≤ width ∧ pair.2 < 2^19)) = true

instance (base width first last : ℕ) (rows : List OMA.PrimeDifference.Row)
    (points : List (ℕ × ℕ)) : Decidable (groupData base width first last rows points) := by
  unfold groupData
  infer_instance

private def compareNamed (ps : List ℕ) (lane depth base width : ℕ)
    (points : List (ℕ × ℕ)) : Prop :=
  let cuts := selectors lane points
  (laneCounts lane depth width (fastComposite ps base width) &&& cuts.1) = cuts.2

instance (ps : List ℕ) (lane depth base width : ℕ) (points : List (ℕ × ℕ)) :
    Decidable (compareNamed ps lane depth base width points) := by
  unfold compareNamed
  infer_instance

theorem groupChecked {ps : List ℕ} {bound depth base width first last : ℕ}
    {rows : List OMA.PrimeDifference.Row} {points : List (ℕ × ℕ)}
    (primes : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width < 2^depth) (hdepth : 2^depth < 2^19) (hcap : 2*(base+width) ≤ (bound+1)^2)
    (data : groupData base width first last rows points)
    (counts : compareNamed ps 19 depth base width points) : covers first last := by
  obtain ⟨indices, rowsGood, included, unique, inRange⟩ := data
  let word := fastComposite ps base width
  have numbers : matchLanes 19 (laneCounts 19 depth width word) points := counts
  have exactCounts (q : ℕ × ℕ) (hq : q ∈ statementsAt base rows) :
      population q.1 (composite ps depth base width) = q.2 := by
    have hq' : q ∈ points := pointCover_all included q hq
    have inBounds (r : ℕ × ℕ) (hr : r ∈ points) : r.1 ≤ width ∧ r.2 < 2^19 :=
      of_decide_eq_true (List.all_eq_true.mp inRange r hr)
    have hdigit := matchLanes_sound hq' unique (fun r hr => (inBounds r hr).2) numbers
    have hrow := laneCounts_sound word (by decide : 0 < 19) hw.le hdepth (inBounds q hq').1
    calc
      population q.1 (composite ps depth base width) = population q.1 word := by
        simp only [word,fastComposite_eq (fun p hp => (primes p hp).1.pos) depth base width]
      _ = q.2 := hrow.symm.trans hdigit
  apply covers_from_rows indices
  intro r hr
  exact rowGate_sound primes complete hw hcap exactCounts hr (List.all_eq_true.mp rowsGood r hr)

end OMA.PackedPrimeCensus

namespace OMA.PackedPrimeCensus

open OMA.PrimeDifference

private def primeRoster : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem roster_eq : primeRoster = OMA.PrimeSieveBase.smallPrimes 5000 70 := by
  decide +kernel

private theorem roster_prime : ∀ p ∈ primeRoster, p.Prime ∧ p%2=1 := by
  intro p hm
  rw [roster_eq] at hm
  exact ⟨OMA.PrimeSieveBase.prime_of_mem_smallPrimes (by decide) hm,
    by unfold OMA.PrimeSieveBase.smallPrimes OMA.PrimeSieveBase.checks at hm
       simp only [List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at hm
       exact hm.2.1.2⟩

private theorem roster_complete : ∀ p ≤ 5000, p.Prime → p%2=1 → p ∈ primeRoster := by
  rw [roster_eq]
  intro p hp hprime hodd
  exact OMA.PrimeSieveBase.mem_smallPrimes hp hprime hodd

private def g000 : List Row :=
  [⟨3,1,0,1⟩,
  ⟨4,2,0,2⟩,
  ⟨5,3,2,4⟩,
  ⟨6,4,3,7⟩,
  ⟨7,6,8,10⟩,
  ⟨8,7,12,14⟩,
  ⟨9,8,16,19⟩,
  ⟨10,8,18,25⟩,
  ⟨11,9,25,31⟩,
  ⟨12,11,34,38⟩,
  ⟨13,12,42,46⟩,
  ⟨14,13,49,54⟩,
  ⟨15,14,59,65⟩,
  ⟨16,15,68,74⟩,
  ⟨17,16,78,84⟩,
  ⟨18,16,83,96⟩,
  ⟨19,15,82,109⟩,
  ⟨20,19,115,122⟩,
  ⟨21,19,122,136⟩,
  ⟨22,21,142,150⟩,
  ⟨23,22,157,166⟩,
  ⟨24,20,148,183⟩,
  ⟨25,24,191,199⟩,
  ⟨26,22,181,216⟩,
  ⟨27,26,225,236⟩,
  ⟨28,18,156,255⟩,
  ⟨29,28,265,275⟩,
  ⟨30,26,253,296⟩,
  ⟨31,27,274,319⟩,
  ⟨32,31,329,340⟩,
  ⟨33,29,317,364⟩,
  ⟨34,22,242,387⟩,
  ⟨35,34,400,413⟩,
  ⟨36,35,425,438⟩,
  ⟨37,36,449,466⟩,
  ⟨38,35,448,494⟩,
  ⟨39,32,421,521⟩,
  ⟨40,39,534,549⟩,
  ⟨41,37,519,578⟩,
  ⟨42,40,577,608⟩,
  ⟨43,25,358,642⟩,
  ⟨44,43,656,673⟩,
  ⟨45,44,691,707⟩,
  ⟨46,45,723,739⟩,
  ⟨47,46,755,776⟩,
  ⟨48,47,793,810⟩,
  ⟨49,45,775,844⟩,
  ⟨50,47,827,883⟩,
  ⟨51,50,902,923⟩,
  ⟨52,47,860,959⟩,
  ⟨53,52,976,996⟩,
  ⟨54,53,1015,1037⟩,
  ⟨55,53,1037,1079⟩,
  ⟨56,55,1100,1123⟩,
  ⟨57,56,1144,1168⟩,
  ⟨58,56,1167,1208⟩,
  ⟨59,58,1231,1254⟩,
  ⟨60,57,1230,1297⟩,
  ⟨61,55,1206,1342⟩,
  ⟨62,60,1341,1390⟩,
  ⟨63,61,1390,1436⟩,
  ⟨64,63,1459,1484⟩,
  ⟨65,64,1507,1535⟩,
  ⟨66,65,1556,1584⟩,
  ⟨67,63,1533,1636⟩,
  ⟨68,67,1661,1688⟩,
  ⟨69,68,1712,1740⟩,
  ⟨70,69,1766,1796⟩,
  ⟨71,59,1521,1846⟩,
  ⟨72,71,1873,1902⟩,
  ⟨73,69,1845,1960⟩,
  ⟨74,72,1959,2016⟩,
  ⟨75,74,2043,2074⟩,
  ⟨76,75,2100,2131⟩,
  ⟨77,74,2099,2186⟩,
  ⟨78,73,2097,2249⟩,
  ⟨79,71,2067,2310⟩,
  ⟨80,78,2309,2366⟩,
  ⟨81,80,2400,2434⟩,
  ⟨82,81,2465,2495⟩,
  ⟨83,81,2495,2559⟩,
  ⟨84,73,2267,2622⟩,
  ⟨85,83,2622,2690⟩,
  ⟨86,85,2723,2759⟩,
  ⟨87,86,2794,2825⟩,
  ⟨88,87,2857,2890⟩,
  ⟨89,86,2856,2961⟩,
  ⟨90,86,2889,3032⟩,
  ⟨91,90,3068,3103⟩,
  ⟨92,89,3067,3174⟩,
  ⟨93,92,3212,3248⟩,
  ⟨94,92,3247,3318⟩,
  ⟨95,94,3355,3392⟩,
  ⟨96,90,3245,3466⟩,
  ⟨97,96,3504,3542⟩,
  ⟨98,94,3464,3617⟩]

private def points000 : List (ℕ × ℕ) := [(0,0),(2,0),(3,1),(6,2),(10,3),(11,4),(16,7),(19,8),(23,10),(26,12),(30,14),(34,16),(38,18),(39,19),(48,25),(59,31),(64,34),(70,38),(76,42),(83,46),(89,49),(96,54),(103,59),(111,65),(118,68),(126,74),(134,78),(141,82),(142,83),(143,84),(160,96),(179,109),(188,115),(198,122),(219,136),(229,142),(238,148),(240,150),(250,156),(251,157),(263,166),(284,181),(286,183),(298,191),(311,199),(336,216),(349,225),(363,236),(372,242),(388,253),(390,255),(404,265),(417,274),(419,275),(448,296),(477,317),(479,319),(494,329),(510,340),(536,358),(543,364),(576,387),(593,400),(611,413),(622,421),(628,425),(646,438),(663,448),(664,449),(683,466),(720,494),(757,519),(759,521),(778,534),(798,549),(838,577),(839,578),(880,608),(923,642),(944,656),(966,673),(988,691),(1011,707),(1033,723),(1056,739),(1079,755),(1101,775),(1103,776),(1126,793),(1150,810),(1173,827),(1199,844),(1220,860),(1248,883),(1273,902),(1299,923),(1350,959),(1376,976),(1403,996),(1429,1015),(1456,1037),(1511,1079),(1538,1100),(1566,1123),(1594,1144),(1622,1167),(1623,1168),(1676,1206),(1680,1208),(1708,1230),(1709,1231),(1739,1254),(1798,1297),(1858,1341),(1859,1342),(1920,1390),(1983,1436),(2014,1459),(2046,1484),(2078,1507),(2093,1521),(2109,1533),(2111,1535),(2143,1556),(2176,1584),(2243,1636),(2276,1661),(2310,1688),(2344,1712),(2379,1740),(2413,1766),(2448,1796),(2517,1845),(2519,1846),(2554,1873),(2590,1902),(2662,1959),(2663,1960),(2736,2016),(2773,2043),(2803,2067),(2811,2074),(2845,2097),(2847,2099),(2848,2100),(2886,2131),(2963,2186),(3040,2249),(3064,2267),(3118,2309),(3119,2310),(3198,2366),(3238,2400),(3279,2434),(3319,2465),(3360,2495),(3443,2559),(3526,2622),(3611,2690),(3653,2723),(3696,2759),(3739,2794),(3783,2825),(3825,2856),(3826,2857),(3868,2889),(3870,2890),(3959,2961),(4048,3032),(4092,3067),(4093,3068),(4139,3103),(4230,3174),(4276,3212),(4318,3245),(4322,3247),(4323,3248),(4416,3318),(4463,3355),(4511,3392),(4604,3464),(4606,3466),(4654,3504),(4703,3542),(4800,3617)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check000 :
    PLift (groupData 2 4800 3 98 g000 points000) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts000 :
    compareNamed primeRoster 19 13 2 4800 points000 := by
  decide +kernel

private theorem cover000 : covers 3 98 :=
  @groupChecked primeRoster 5000 13 2 4800 3 98 g000 points000
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check000.down counts000

private def g001 : List Row :=
  [⟨99,98,286,325⟩,
  ⟨100,94,170,403⟩,
  ⟨101,99,403,481⟩,
  ⟨102,101,520,560⟩,
  ⟨103,87,0,643⟩,
  ⟨104,100,558,725⟩,
  ⟨105,102,682,809⟩,
  ⟨106,101,681,893⟩,
  ⟨107,106,933,976⟩,
  ⟨108,106,975,1064⟩,
  ⟨109,107,1064,1150⟩,
  ⟨110,106,1062,1235⟩,
  ⟨111,99,793,1322⟩,
  ⟨112,107,1187,1406⟩,
  ⟨113,112,1448,1494⟩,
  ⟨114,107,1273,1583⟩,
  ⟨115,110,1446,1673⟩,
  ⟨116,112,1581,1766⟩,
  ⟨117,115,1766,1860⟩,
  ⟨118,116,1859,1948⟩,
  ⟨119,118,1997,2046⟩,
  ⟨120,119,2097,2146⟩,
  ⟨121,119,2146,2238⟩,
  ⟨122,113,1895,2331⟩,
  ⟨123,121,2331,2431⟩,
  ⟨124,123,2479,2524⟩,
  ⟨125,124,2572,2624⟩,
  ⟨126,125,2670,2722⟩,
  ⟨127,125,2722,2820⟩,
  ⟨128,127,2871,2924⟩,
  ⟨129,122,2666,3029⟩,
  ⟨130,117,2462,3134⟩,
  ⟨131,124,2867,3237⟩,
  ⟨132,131,3291,3340⟩,
  ⟨133,120,2753,3445⟩,
  ⟨134,130,3338,3553⟩,
  ⟨135,133,3553,3657⟩,
  ⟨136,132,3551,3762⟩,
  ⟨137,135,3762,3876⟩,
  ⟨138,137,3935,3991⟩,
  ⟨139,134,3816,4103⟩,
  ⟨140,139,4156,4209⟩,
  ⟨141,137,4102,4325⟩,
  ⟨142,141,4379,4433⟩,
  ⟨143,142,4492,4547⟩,
  ⟨144,143,4607,4666⟩,
  ⟨145,140,4489,4779⟩,
  ⟨146,141,4604,4898⟩,
  ⟨147,144,4837,5011⟩,
  ⟨148,138,4537,5128⟩,
  ⟨149,144,4954,5244⟩,
  ⟨150,149,5305,5367⟩,
  ⟨151,150,5427,5486⟩,
  ⟨152,147,5303,5604⟩,
  ⟨153,150,5547,5730⟩,
  ⟨154,153,5793,5853⟩,
  ⟨155,152,5793,5973⟩,
  ⟨156,155,6031,6098⟩,
  ⟨157,148,5658,6228⟩,
  ⟨158,153,6029,6357⟩,
  ⟨159,157,6357,6485⟩,
  ⟨160,156,6355,6614⟩,
  ⟨161,154,6287,6742⟩,
  ⟨162,161,6807,6871⟩,
  ⟨163,157,6610,7002⟩,
  ⟨164,155,6540,7129⟩,
  ⟨165,163,7129,7265⟩,
  ⟨166,165,7334,7400⟩,
  ⟨167,154,6659,7534⟩,
  ⟨168,163,7331,7668⟩,
  ⟨169,168,7740,7806⟩,
  ⟨170,164,7530,7937⟩,
  ⟨171,170,8006,8075⟩,
  ⟨172,164,7662,8213⟩,
  ⟨173,166,7863,8356⟩,
  ⟨174,169,8140,8496⟩,
  ⟨175,159,7506,8643⟩,
  ⟨176,175,8713,8782⟩,
  ⟨177,169,8351,8920⟩,
  ⟨178,175,8853,9067⟩,
  ⟨179,178,9140,9217⟩,
  ⟨180,177,9139,9356⟩,
  ⟨181,169,8626,9501⟩,
  ⟨182,173,8987,9643⟩,
  ⟨183,179,9499,9792⟩,
  ⟨184,178,9496,9935⟩,
  ⟨185,183,9935,10089⟩,
  ⟨186,185,10161,10235⟩,
  ⟨187,181,9932,10386⟩,
  ⟨188,183,10158,10539⟩,
  ⟨189,176,9702,10698⟩,
  ⟨190,180,10079,10848⟩,
  ⟨191,187,10696,11005⟩,
  ⟨192,186,10693,11156⟩,
  ⟨193,191,11156,11312⟩,
  ⟨194,193,11390,11464⟩]

private def points001 : List (ℕ × ℕ) := [(0,0),(219,170),(370,286),(420,325),(519,403),(620,481),(670,520),(719,558),(721,560),(824,643),(872,681),(874,682),(927,725),(1014,793),(1032,809),(1137,893),(1190,933),(1243,975),(1244,976),(1349,1062),(1351,1064),(1460,1150),(1511,1187),(1569,1235),(1618,1273),(1680,1322),(1791,1406),(1844,1446),(1847,1448),(1904,1494),(2015,1581),(2017,1583),(2132,1673),(2247,1766),(2363,1859),(2364,1860),(2412,1895),(2481,1948),(2540,1997),(2600,2046),(2659,2097),(2719,2146),(2840,2238),(2961,2331),(3084,2431),(3124,2462),(3145,2479),(3207,2524),(3269,2572),(3332,2624),(3388,2666),(3394,2670),(3457,2722),(3499,2753),(3584,2820),(3641,2867),(3647,2871),(3711,2924),(3840,3029),(3969,3134),(4100,3237),(4165,3291),(4229,3338),(4231,3340),(4364,3445),(4495,3551),(4497,3553),(4632,3657),(4767,3762),(4832,3816),(4904,3876),(4972,3935),(5041,3991),(5178,4102),(5180,4103),(5249,4156),(5319,4209),(5460,4325),(5530,4379),(5601,4433),(5669,4489),(5672,4492),(5731,4537),(5744,4547),(5812,4604),(5815,4607),(5887,4666),(6032,4779),(6103,4837),(6177,4898),(6247,4954),(6324,5011),(6471,5128),(6620,5244),(6691,5303),(6694,5305),(6769,5367),(6844,5427),(6920,5486),(6994,5547),(7071,5604),(7137,5658),(7224,5730),(7299,5793),(7300,5793),(7377,5853),(7532,5973),(7606,6029),(7609,6031),(7687,6098),(7844,6228),(7916,6287),(7999,6355),(8001,6357),(8160,6485),(8229,6540),(8315,6610),(8319,6614),(8378,6659),(8480,6742),(8560,6807),(8641,6871),(8804,7002),(8967,7129),(9132,7265),(9211,7331),(9214,7334),(9297,7400),(9432,7506),(9459,7530),(9464,7534),(9623,7662),(9631,7668),(9715,7740),(9800,7806),(9878,7863),(9969,7937),(10054,8006),(10140,8075),(10222,8140),(10311,8213),(10476,8351),(10484,8356),(10657,8496),(10814,8626),(10832,8643),(10919,8713),(11007,8782),(11094,8853),(11184,8920),(11262,8987),(11361,9067),(11449,9139),(11450,9140),(11540,9217),(11719,9356),(11895,9496),(11898,9499),(11900,9501),(12081,9643),(12151,9702),(12264,9792),(12443,9932),(12447,9935),(12619,10079),(12632,10089),(12721,10158),(12724,10161),(12817,10235),(13004,10386),(13191,10539),(13375,10693),(13378,10696),(13380,10698),(13569,10848),(13760,11005),(13951,11156),(14144,11312),(14240,11390),(14337,11464)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check001 :
    PLift (groupData 4481 14337 99 194 g001 points001) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts001 :
    compareNamed primeRoster 19 14 4481 14337 points001 := by
  decide +kernel

private theorem cover001 : covers 99 194 :=
  @groupChecked primeRoster 5000 14 4481 14337 99 194 g001 points001
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check001.down counts001

private def g002 : List Row :=
  [⟨195,191,482,799⟩,
  ⟨196,192,635,960⟩,
  ⟨197,195,960,1120⟩,
  ⟨198,192,794,1279⟩,
  ⟨199,197,1279,1441⟩,
  ⟨200,192,952,1601⟩,
  ⟨201,200,1681,1769⟩,
  ⟨202,197,1519,1935⟩,
  ⟨203,195,1433,2096⟩,
  ⟨204,203,2177,2260⟩,
  ⟨205,201,2094,2421⟩,
  ⟨206,175,0,2586⟩,
  ⟨207,197,1925,2749⟩,
  ⟨208,195,1832,2921⟩,
  ⟨209,205,2747,3094⟩,
  ⟨210,200,2412,3265⟩,
  ⟨211,208,3182,3438⟩,
  ⟨212,207,3180,3607⟩,
  ⟨213,205,3087,3782⟩,
  ⟨214,213,3871,3959⟩,
  ⟨215,209,3604,4136⟩,
  ⟨216,215,4226,4311⟩,
  ⟨217,209,3775,4492⟩,
  ⟨218,208,3770,4667⟩,
  ⟨219,217,4667,4843⟩,
  ⟨220,215,4577,5026⟩,
  ⟨221,197,3038,5203⟩,
  ⟨222,220,5202,5381⟩,
  ⟨223,221,5381,5563⟩,
  ⟨224,223,5651,5740⟩,
  ⟨225,224,5832,5926⟩,
  ⟨226,209,4551,6113⟩,
  ⟨227,224,6021,6295⟩,
  ⟨228,227,6387,6478⟩,
  ⟨229,226,6386,6669⟩,
  ⟨230,228,6668,6857⟩,
  ⟨231,192,3367,7043⟩,
  ⟨232,230,7042,7233⟩,
  ⟨233,232,7327,7427⟩,
  ⟨234,218,6087,7612⟩,
  ⟨235,233,7612,7806⟩,
  ⟨236,234,7805,8000⟩,
  ⟨237,226,7128,8191⟩,
  ⟨238,226,7218,8383⟩,
  ⟨239,232,7899,8573⟩,
  ⟨240,239,8668,8769⟩,
  ⟨241,239,8769,8963⟩,
  ⟨242,239,8864,9160⟩,
  ⟨243,238,8862,9361⟩,
  ⟨244,243,9455,9554⟩,
  ⟨245,243,9554,9758⟩,
  ⟨246,245,9857,9961⟩,
  ⟨247,239,9353,10162⟩,
  ⟨248,239,9447,10370⟩,
  ⟨249,248,10467,10573⟩,
  ⟨250,249,10673,10779⟩,
  ⟨251,250,10882,10985⟩,
  ⟨252,247,10670,11191⟩,
  ⟨253,241,10146,11395⟩,
  ⟨254,251,11288,11608⟩,
  ⟨255,253,11608,11822⟩,
  ⟨256,254,11821,12030⟩,
  ⟨257,256,12128,12234⟩,
  ⟨258,257,12344,12450⟩,
  ⟨259,256,12343,12661⟩,
  ⟨260,249,11702,12869⟩,
  ⟨261,253,12229,13082⟩,
  ⟨262,261,13195,13303⟩,
  ⟨263,256,12762,13520⟩,
  ⟨264,262,13519,13742⟩,
  ⟨265,260,13407,13957⟩,
  ⟨266,264,13956,14175⟩,
  ⟨267,266,14281,14392⟩,
  ⟨268,262,13953,14608⟩,
  ⟨269,267,14608,14824⟩,
  ⟨270,263,14276,15048⟩,
  ⟨271,268,14937,15273⟩,
  ⟨272,261,14269,15496⟩,
  ⟨273,265,14817,15718⟩,
  ⟨274,273,15829,15943⟩,
  ⟨275,267,15266,16167⟩,
  ⟨276,267,15374,16393⟩,
  ⟨277,262,14914,16625⟩,
  ⟨278,260,14789,16852⟩,
  ⟨279,278,16964,17075⟩,
  ⟨280,277,16963,17310⟩,
  ⟨281,278,17193,17542⟩,
  ⟨282,281,17659,17777⟩,
  ⟨283,281,17777,18007⟩,
  ⟨284,277,17420,18241⟩,
  ⟨285,283,18241,18467⟩,
  ⟨286,280,18002,18703⟩,
  ⟨287,284,18588,18936⟩,
  ⟨288,287,19052,19173⟩,
  ⟨289,280,18345,19413⟩,
  ⟨290,289,19534,19656⟩]

private def points002 : List (ℕ × ℕ) := [(0,0),(598,482),(791,635),(983,794),(988,799),(1175,952),(1183,960),(1380,1120),(1577,1279),(1768,1433),(1776,1441),(1872,1519),(1975,1601),(2075,1681),(2176,1769),(2255,1832),(2365,1925),(2377,1935),(2578,2094),(2580,2096),(2681,2177),(2783,2260),(2975,2412),(2988,2421),(3193,2586),(3398,2747),(3400,2749),(3607,2921),(3744,3038),(3808,3087),(3816,3094),(3917,3180),(3919,3182),(4025,3265),(4151,3367),(4236,3438),(4443,3604),(4447,3607),(4647,3770),(4652,3775),(4660,3782),(4766,3871),(4873,3959),(5088,4136),(5195,4226),(5303,4311),(5520,4492),(5592,4551),(5625,4577),(5737,4667),(5956,4843),(6175,5026),(6395,5202),(6396,5203),(6617,5381),(6840,5563),(6951,5651),(7063,5740),(7175,5832),(7288,5926),(7399,6021),(7481,6087),(7513,6113),(7740,6295),(7852,6386),(7853,6387),(7967,6478),(8195,6668),(8196,6669),(8425,6857),(8655,7042),(8656,7043),(8756,7128),(8869,7218),(8887,7233),(9003,7327),(9120,7427),(9353,7612),(9587,7805),(9588,7806),(9699,7899),(9823,8000),(10060,8191),(10297,8383),(10536,8573),(10655,8668),(10775,8769),(10892,8862),(10894,8864),(11016,8963),(11257,9160),(11492,9353),(11500,9361),(11611,9447),(11621,9455),(11743,9554),(11988,9758),(12110,9857),(12233,9961),(12462,10146),(12480,10162),(12727,10370),(12851,10467),(12976,10573),(13097,10670),(13100,10673),(13225,10779),(13350,10882),(13476,10985),(13727,11191),(13852,11288),(13980,11395),(14233,11608),(14345,11702),(14487,11821),(14488,11822),(14743,12030),(14871,12128),(14992,12229),(15000,12234),(15127,12343),(15128,12344),(15257,12450),(15516,12661),(15639,12762),(15775,12869),(16036,13082),(16166,13195),(16297,13303),(16425,13407),(16559,13519),(16560,13520),(16823,13742),(17083,13953),(17087,13956),(17088,13957),(17353,14175),(17471,14269),(17480,14276),(17486,14281),(17620,14392),(17887,14608),(18115,14789),(18148,14817),(18156,14824),(18262,14914),(18289,14937),(18425,15048),(18688,15266),(18696,15273),(18821,15374),(18967,15496),(19240,15718),(19376,15829),(19513,15943),(19788,16167),(20063,16393),(20340,16625),(20617,16852),(20755,16963),(20756,16964),(20896,17075),(21034,17193),(21175,17310),(21309,17420),(21456,17542),(21596,17659),(21737,17777),(22015,18002),(22020,18007),(22303,18241),(22435,18345),(22588,18467),(22729,18588),(22873,18703),(23160,18936),(23303,19052),(23447,19173),(23736,19413),(23880,19534),(24025,19656)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check002 :
    PLift (groupData 18025 24025 195 290 g002 points002) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts002 :
    compareNamed primeRoster 19 15 18025 24025 points002 := by
  decide +kernel

private theorem cover002 : covers 195 290 :=
  @groupChecked primeRoster 5000 15 18025 24025 195 290 g002 points002
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check002.down counts002

private def g003 : List Row :=
  [⟨291,289,162,400⟩,
  ⟨292,291,522,639⟩,
  ⟨293,289,398,881⟩,
  ⟨294,293,1007,1123⟩,
  ⟨295,294,1246,1371⟩,
  ⟨296,292,1121,1612⟩,
  ⟨297,293,1369,1860⟩,
  ⟨298,297,1986,2112⟩,
  ⟨299,280,0,2354⟩,
  ⟨300,297,2230,2597⟩,
  ⟨301,297,2353,2842⟩,
  ⟨302,295,2225,3091⟩,
  ⟨303,297,2593,3345⟩,
  ⟨304,300,3089,3590⟩,
  ⟨305,300,3212,3838⟩,
  ⟨306,300,3342,4087⟩,
  ⟨307,297,3082,4346⟩,
  ⟨308,301,3708,4595⟩,
  ⟨309,296,3196,4846⟩,
  ⟨310,306,4593,5100⟩,
  ⟨311,304,4464,5362⟩,
  ⟨312,306,4842,5621⟩,
  ⟨313,309,5360,5879⟩,
  ⟨314,313,6014,6142⟩,
  ⟨315,313,6142,6398⟩,
  ⟨316,309,5743,6658⟩,
  ⟨317,313,6397,6924⟩,
  ⟨318,308,5868,7187⟩,
  ⟨319,318,7317,7446⟩,
  ⟨320,310,6386,7705⟩,
  ⟨321,318,7573,7976⟩,
  ⟨322,319,7835,8245⟩,
  ⟨323,319,7974,8511⟩,
  ⟨324,318,7971,8776⟩,
  ⟨325,322,8647,9046⟩,
  ⟨326,321,8645,9321⟩,
  ⟨327,319,8505,9584⟩,
  ⟨328,327,9719,9864⟩,
  ⟨329,328,9999,10133⟩,
  ⟨330,324,9580,10407⟩,
  ⟨331,330,10539,10676⟩,
  ⟨332,328,10405,10956⟩,
  ⟨333,332,11096,11232⟩,
  ⟨334,326,10401,11508⟩,
  ⟨335,333,11508,11784⟩,
  ⟨336,333,11643,12068⟩,
  ⟨337,321,10110,12339⟩,
  ⟨338,337,12483,12621⟩,
  ⟨339,330,11635,12904⟩,
  ⟨340,331,11916,13189⟩,
  ⟨341,333,12333,13464⟩,
  ⟨342,341,13609,13751⟩,
  ⟨343,318,10476,14037⟩,
  ⟨344,342,14036,14319⟩,
  ⟨345,331,12603,14609⟩,
  ⟨346,329,12452,14894⟩,
  ⟨347,346,15035,15180⟩,
  ⟨348,339,14166,15463⟩,
  ⟨349,347,15463,15751⟩,
  ⟨350,349,15894,16038⟩,
  ⟨351,346,15604,16333⟩,
  ⟨352,346,15746,16621⟩,
  ⟨353,348,16182,16914⟩,
  ⟨354,352,16913,17206⟩,
  ⟨355,353,17206,17500⟩,
  ⟨356,355,17647,17796⟩,
  ⟨357,356,17949,18099⟩,
  ⟨358,349,17052,18394⟩,
  ⟨359,358,18536,18687⟩,
  ⟨360,358,18686,18979⟩,
  ⟨361,348,17338,19284⟩,
  ⟨362,360,19283,19584⟩,
  ⟨363,361,19584,19888⟩,
  ⟨364,362,19887,20192⟩,
  ⟨365,364,20338,20490⟩,
  ⟨366,363,20338,20798⟩,
  ⟨367,364,20640,21102⟩,
  ⟨368,367,21256,21409⟩,
  ⟨369,357,19873,21714⟩,
  ⟨370,359,20327,22009⟩,
  ⟨371,366,21553,22318⟩,
  ⟨372,371,22474,22629⟩,
  ⟨373,371,22629,22941⟩,
  ⟨374,373,23093,23251⟩,
  ⟨375,367,22312,23561⟩,
  ⟨376,374,23560,23869⟩,
  ⟨377,375,23869,24179⟩,
  ⟨378,376,24178,24497⟩,
  ⟨379,377,24497,24817⟩,
  ⟨380,371,23705,25138⟩,
  ⟨381,380,25294,25456⟩,
  ⟨382,378,25136,25773⟩,
  ⟨383,381,25773,26089⟩,
  ⟨384,381,25928,26407⟩,
  ⟨385,383,26407,26731⟩,
  ⟨386,378,25765,27052⟩]

private def points003 : List (ℕ × ℕ) := [(0,0),(190,162),(479,398),(481,400),(626,522),(772,639),(1065,881),(1211,1007),(1356,1121),(1358,1123),(1505,1246),(1651,1369),(1653,1371),(1948,1612),(2245,1860),(2393,1986),(2542,2112),(2685,2225),(2690,2230),(2839,2353),(2841,2354),(3136,2593),(3140,2597),(3441,2842),(3730,3082),(3740,3089),(3742,3091),(3872,3196),(3890,3212),(4040,3342),(4045,3345),(4348,3590),(4494,3708),(4653,3838),(4958,4087),(5265,4346),(5412,4464),(5570,4593),(5572,4595),(5876,4842),(5881,4846),(6190,5100),(6499,5360),(6501,5362),(6812,5621),(6962,5743),(7112,5868),(7125,5879),(7281,6014),(7438,6142),(7740,6386),(7751,6397),(7753,6398),(8068,6658),(8385,6924),(8702,7187),(8861,7317),(9021,7446),(9179,7573),(9340,7705),(9499,7835),(9656,7971),(9659,7974),(9661,7976),(9982,8245),(10297,8505),(10305,8511),(10463,8645),(10465,8647),(10628,8776),(10953,9046),(11278,9321),(11600,9580),(11605,9584),(11768,9719),(11932,9864),(12096,9999),(12229,10110),(12261,10133),(12582,10401),(12588,10405),(12590,10407),(12677,10476),(12755,10539),(12921,10676),(13252,10956),(13418,11096),(13585,11232),(13918,11508),(14075,11635),(14084,11643),(14253,11784),(14410,11916),(14588,12068),(14917,12333),(14925,12339),(15057,12452),(15093,12483),(15238,12603),(15262,12621),(15601,12904),(15940,13189),(16281,13464),(16451,13609),(16622,13751),(16964,14036),(16965,14037),(17126,14166),(17308,14319),(17653,14609),(17998,14894),(18171,15035),(18345,15180),(18692,15463),(18863,15604),(19036,15746),(19041,15751),(19215,15894),(19390,16038),(19562,16182),(19741,16333),(20092,16621),(20444,16913),(20445,16914),(20611,17052),(20798,17206),(20954,17338),(21153,17500),(21330,17647),(21508,17796),(21686,17949),(21865,18099),(22222,18394),(22401,18536),(22580,18686),(22581,18687),(22940,18979),(23300,19283),(23301,19284),(23662,19584),(24007,19873),(24024,19887),(24025,19888),(24388,20192),(24555,20327),(24569,20338),(24570,20338),(24753,20490),(24934,20640),(25118,20798),(25485,21102),(25668,21256),(25852,21409),(26033,21553),(26221,21714),(26590,22009),(26953,22312),(26961,22318),(27146,22474),(27332,22629),(27705,22941),(27891,23093),(28078,23251),(28452,23560),(28453,23561),(28630,23705),(28828,23869),(29204,24178),(29205,24179),(29582,24497),(29961,24817),(30338,25136),(30340,25138),(30530,25294),(30721,25456),(31094,25765),(31102,25773),(31292,25928),(31485,26089),(31868,26407),(32253,26731),(32638,27052)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check003 :
    PLift (groupData 41860 32638 291 386 g003 points003) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts003 :
    compareNamed primeRoster 19 15 41860 32638 points003 := by
  decide +kernel

private theorem cover003 : covers 291 386 :=
  @groupChecked primeRoster 5000 15 41860 32638 291 386 g003 points003
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check003.down counts003

private def g004 : List Row :=
  [⟨387,385,3937,4251⟩,
  ⟨388,385,4091,4572⟩,
  ⟨389,384,4090,4896⟩,
  ⟨390,387,4733,5211⟩,
  ⟨391,384,4406,5536⟩,
  ⟨392,356,0,5863⟩,
  ⟨393,392,6032,6192⟩,
  ⟨394,389,5702,6520⟩,
  ⟨395,393,6520,6848⟩,
  ⟨396,392,6518,7183⟩,
  ⟨397,396,7348,7510⟩,
  ⟨398,392,6844,7845⟩,
  ⟨399,391,6842,8181⟩,
  ⟨400,396,7843,8512⟩,
  ⟨401,396,8008,8844⟩,
  ⟨402,390,7168,9179⟩,
  ⟨403,401,9179,9523⟩,
  ⟨404,399,9009,9852⟩,
  ⟨405,404,10024,10190⟩,
  ⟨406,405,10357,10529⟩,
  ⟨407,399,9515,10874⟩,
  ⟨408,407,11045,11218⟩,
  ⟨409,408,11385,11553⟩,
  ⟨410,407,11385,11899⟩,
  ⟨411,410,12075,12250⟩,
  ⟨412,410,12249,12594⟩,
  ⟨413,408,12072,12932⟩,
  ⟨414,413,13102,13280⟩,
  ⟨415,412,13101,13621⟩,
  ⟨416,414,13620,13965⟩,
  ⟨417,413,13620,14317⟩,
  ⟨418,416,14316,14663⟩,
  ⟨419,417,14663,15023⟩,
  ⟨420,419,15196,15365⟩,
  ⟨421,420,15532,15712⟩,
  ⟨422,420,15711,16072⟩,
  ⟨423,419,15711,16418⟩,
  ⟨424,423,16594,16765⟩,
  ⟨425,421,16416,17115⟩,
  ⟨426,425,17302,17484⟩,
  ⟨427,425,17484,17838⟩,
  ⟨428,421,16934,18193⟩,
  ⟨429,428,18365,18549⟩,
  ⟨430,418,16749,18910⟩,
  ⟨431,428,18729,19263⟩,
  ⟨432,431,19436,19621⟩,
  ⟨433,429,19261,19976⟩,
  ⟨434,433,20160,20346⟩,
  ⟨435,422,18350,20711⟩,
  ⟨436,433,20527,21068⟩,
  ⟨437,432,20525,21437⟩,
  ⟨438,435,21256,21800⟩,
  ⟨439,437,21800,22168⟩,
  ⟨440,430,20699,22532⟩,
  ⟨441,440,22713,22905⟩,
  ⟨442,437,22344,23270⟩,
  ⟨443,441,23270,23642⟩,
  ⟨444,440,23268,24017⟩,
  ⟨445,438,23084,24385⟩,
  ⟨446,442,24015,24756⟩,
  ⟨447,441,24013,25131⟩,
  ⟨448,440,24010,25509⟩,
  ⟨449,446,25317,25888⟩,
  ⟨450,447,25698,26260⟩,
  ⟨451,442,24938,26637⟩,
  ⟨452,448,26258,27023⟩,
  ⟨453,450,26830,27401⟩,
  ⟨454,433,23784,27778⟩,
  ⟨455,449,27021,28159⟩,
  ⟨456,450,27397,28536⟩,
  ⟨457,416,21075,28913⟩,
  ⟨458,457,29105,29293⟩,
  ⟨459,454,28721,29670⟩,
  ⟨460,455,29102,30053⟩,
  ⟨461,453,28907,30444⟩,
  ⟨462,452,28902,30833⟩,
  ⟨463,461,30833,31223⟩,
  ⟨464,463,31409,31612⟩,
  ⟨465,464,31808,32004⟩,
  ⟨466,457,30634,32400⟩,
  ⟨467,457,30821,32789⟩,
  ⟨468,466,32788,33177⟩,
  ⟨469,464,32588,33562⟩,
  ⟨470,452,30410,33957⟩,
  ⟨471,470,34156,34351⟩,
  ⟨472,470,34350,34751⟩,
  ⟨473,466,33755,35142⟩,
  ⟨474,471,34942,35540⟩,
  ⟨475,469,34748,35934⟩,
  ⟨476,475,36134,36335⟩,
  ⟨477,472,35736,36736⟩,
  ⟨478,477,36938,37136⟩,
  ⟨479,468,35329,37531⟩,
  ⟨480,471,36126,37919⟩,
  ⟨481,477,37529,38328⟩,
  ⟨482,480,38327,38736⟩]

private def points004 : List (ℕ × ℕ) := [(0,0),(4722,3937),(4912,4090),(4914,4091),(5109,4251),(5296,4406),(5496,4572),(5689,4733),(5885,4896),(6274,5211),(6665,5536),(6857,5702),(7056,5863),(7252,6032),(7449,6192),(7840,6518),(7842,6520),(8229,6842),(8232,6844),(8237,6848),(8614,7168),(8632,7183),(8830,7348),(9029,7510),(9424,7843),(9426,7845),(9622,8008),(9825,8181),(10224,8512),(10625,8844),(10822,9009),(11026,9179),(11421,9515),(11429,9523),(11832,9852),(12034,10024),(12237,10190),(12439,10357),(12642,10529),(13049,10874),(13252,11045),(13456,11218),(13659,11385),(13660,11385),(13865,11553),(14274,11899),(14476,12072),(14479,12075),(14684,12249),(14685,12250),(15096,12594),(15509,12932),(15714,13101),(15715,13102),(15922,13280),(16335,13620),(16336,13620),(16337,13621),(16752,13965),(17168,14316),(17169,14317),(17586,14663),(18005,15023),(18214,15196),(18424,15365),(18634,15532),(18843,15711),(18844,15711),(18845,15712),(19266,16072),(19687,16416),(19689,16418),(19900,16594),(20094,16749),(20112,16765),(20318,16934),(20537,17115),(20749,17302),(20962,17484),(21389,17838),(21816,18193),(22009,18350),(22030,18365),(22245,18549),(22458,18729),(22674,18910),(23103,19261),(23105,19263),(23320,19436),(23536,19621),(23969,19976),(24185,20160),(24402,20346),(24616,20525),(24618,20527),(24824,20699),(24837,20711),(25272,21068),(25280,21075),(25489,21256),(25709,21437),(26146,21800),(26585,22168),(26801,22344),(27024,22532),(27244,22713),(27465,22905),(27679,23084),(27904,23268),(27906,23270),(28349,23642),(28515,23784),(28784,24010),(28788,24013),(28790,24015),(28792,24017),(29237,24385),(29682,24756),(29895,24938),(30129,25131),(30351,25317),(30576,25509),(30799,25698),(31025,25888),(31472,26258),(31474,26260),(31925,26637),(32149,26830),(32372,27021),(32376,27023),(32824,27397),(32829,27401),(33282,27778),(33737,28159),(34192,28536),(34417,28721),(34636,28902),(34641,28907),(34649,28913),(34874,29102),(34877,29105),(35106,29293),(35565,29670),(36024,30053),(36444,30410),(36485,30444),(36705,30634),(36934,30821),(36946,30833),(37409,31223),(37640,31409),(37872,31612),(38104,31808),(38337,32004),(38802,32400),(39032,32588),(39268,32788),(39269,32789),(39736,33177),(40205,33562),(40433,33755),(40674,33957),(40909,34156),(41144,34350),(41145,34351),(41612,34748),(41616,34751),(41851,34942),(42089,35142),(42310,35329),(42562,35540),(42796,35736),(43037,35934),(43264,36126),(43274,36134),(43512,36335),(43989,36736),(44227,36938),(44466,37136),(44943,37529),(44945,37531),(45424,37919),(45904,38327),(45905,38328),(46386,38736)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check004 :
    PLift (groupData 69776 46386 387 482 g004 points004) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts004 :
    compareNamed primeRoster 19 16 69776 46386 points004 := by
  decide +kernel

private theorem cover004 : covers 387 482 :=
  @groupChecked primeRoster 5000 16 69776 46386 387 482 g004 points004
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check004.down counts004

private def g005 : List Row :=
  [⟨483,481,0,410⟩,
  ⟨484,483,614,819⟩,
  ⟨485,484,1021,1221⟩,
  ⟨486,482,817,1638⟩,
  ⟨487,481,815,2047⟩,
  ⟨488,487,2260,2463⟩,
  ⟨489,479,808,2870⟩,
  ⟨490,489,3074,3278⟩,
  ⟨491,489,3278,3690⟩,
  ⟨492,481,1833,4096⟩,
  ⟨493,487,3274,4514⟩,
  ⟨494,492,4513,4928⟩,
  ⟨495,494,5131,5338⟩,
  ⟨496,485,3474,5753⟩,
  ⟨497,496,5963,6165⟩,
  ⟨498,487,4289,6585⟩,
  ⟨499,493,5750,6996⟩,
  ⟨500,492,5746,7415⟩,
  ⟨501,499,7415,7845⟩,
  ⟨502,501,8047,8257⟩,
  ⟨503,499,7843,8682⟩,
  ⟨504,503,8899,9104⟩,
  ⟨505,494,7192,9531⟩,
  ⟨506,505,9738,9948⟩,
  ⟨507,504,9737,10385⟩,
  ⟨508,507,10595,10812⟩,
  ⟨509,508,11021,11235⟩,
  ⟨510,506,10811,11664⟩,
  ⟨511,510,11880,12095⟩,
  ⟨512,507,11448,12531⟩,
  ⟨513,512,12745,12965⟩,
  ⟨514,513,13175,13389⟩,
  ⟨515,513,13389,13825⟩,
  ⟨516,515,14040,14255⟩,
  ⟨517,515,14255,14689⟩,
  ⟨518,514,14253,15110⟩,
  ⟨519,517,15110,15546⟩,
  ⟨520,519,15766,15983⟩,
  ⟨521,520,16200,16420⟩,
  ⟨522,520,16419,16852⟩,
  ⟨523,522,17074,17299⟩,
  ⟨524,520,16850,17747⟩,
  ⟨525,521,17298,18181⟩,
  ⟨526,522,17745,18618⟩,
  ⟨527,525,18618,19066⟩,
  ⟨528,526,19065,19510⟩,
  ⟨529,528,19735,19959⟩,
  ⟨530,519,17950,20402⟩,
  ⟨531,507,15486,20839⟩,
  ⟨532,531,21062,21287⟩,
  ⟨533,532,21518,21744⟩,
  ⟨534,531,21517,22181⟩,
  ⟨535,531,21742,22639⟩,
  ⟨536,535,22862,23089⟩,
  ⟨537,535,23089,23555⟩,
  ⟨538,537,23783,23999⟩,
  ⟨539,528,21949,24453⟩,
  ⟨540,539,24676,24903⟩,
  ⟨541,540,25134,25362⟩,
  ⟨542,531,23311,25825⟩,
  ⟨543,542,26053,26282⟩,
  ⟨544,535,24668,26743⟩,
  ⟨545,541,26280,27197⟩,
  ⟨546,541,26508,27662⟩,
  ⟨547,538,26045,28128⟩,
  ⟨548,538,26270,28591⟩,
  ⟨549,548,28816,29048⟩,
  ⟨550,544,28123,29516⟩,
  ⟨551,550,29741,29970⟩,
  ⟨552,541,27882,30431⟩,
  ⟨553,552,30658,30888⟩,
  ⟨554,552,30887,31352⟩,
  ⟨555,554,31585,31826⟩,
  ⟨556,555,32058,32293⟩,
  ⟨557,552,31582,32764⟩,
  ⟨558,548,30876,33235⟩,
  ⟨559,551,31819,33708⟩,
  ⟨560,554,32760,34177⟩,
  ⟨561,558,33940,34643⟩,
  ⟨562,559,34408,35120⟩,
  ⟨563,551,32751,35588⟩,
  ⟨564,562,35587,36062⟩,
  ⟨565,552,33457,36529⟩,
  ⟨566,556,34633,36996⟩,
  ⟨567,566,37238,37475⟩,
  ⟨568,567,37714,37951⟩,
  ⟨569,567,37951,38437⟩,
  ⟨570,557,35807,38913⟩,
  ⟨571,570,39149,39388⟩,
  ⟨572,571,39630,39875⟩,
  ⟨573,568,39146,40350⟩,
  ⟨574,573,40592,40836⟩,
  ⟨575,548,34805,41319⟩,
  ⟨576,573,41074,41801⟩,
  ⟨577,570,40589,42292⟩,
  ⟨578,574,41799,42776⟩]

private def points005 : List (ℕ × ℕ) := [(0,0),(483,410),(724,614),(954,808),(962,815),(964,817),(966,819),(1208,1021),(1451,1221),(1936,1638),(2164,1833),(2423,2047),(2666,2260),(2910,2463),(3399,2870),(3643,3074),(3884,3274),(3888,3278),(4118,3474),(4379,3690),(4870,4096),(5101,4289),(5362,4513),(5363,4514),(5856,4928),(6103,5131),(6351,5338),(6838,5746),(6842,5750),(6846,5753),(7094,5963),(7343,6165),(7840,6585),(8339,6996),(8573,7192),(8838,7415),(9337,7843),(9339,7845),(9589,8047),(9840,8257),(10343,8682),(10594,8899),(10846,9104),(11351,9531),(11602,9737),(11603,9738),(11856,9948),(12363,10385),(12616,10595),(12868,10811),(12870,10812),(13124,11021),(13379,11235),(13630,11448),(13888,11664),(14143,11880),(14399,12095),(14910,12531),(15166,12745),(15423,12965),(15679,13175),(15936,13389),(16451,13825),(16708,14040),(16964,14253),(16966,14255),(17483,14689),(18000,15110),(18447,15486),(18519,15546),(18778,15766),(19038,15983),(19298,16200),(19558,16419),(19559,16420),(20078,16850),(20080,16852),(20341,17074),(20601,17298),(20603,17299),(21124,17745),(21126,17747),(21373,17950),(21651,18181),(22176,18618),(22702,19065),(22703,19066),(23230,19510),(23494,19735),(23759,19959),(24288,20402),(24819,20839),(25084,21062),(25350,21287),(25615,21517),(25616,21518),(25881,21742),(25883,21744),(26134,21949),(26416,22181),(26951,22639),(27218,22862),(27486,23089),(27739,23311),(28023,23555),(28291,23783),(28560,23999),(29099,24453),(29358,24668),(29368,24676),(29638,24903),(29908,25134),(30179,25362),(30720,25825),(30981,26045),(30991,26053),(31250,26270),(31261,26280),(31263,26282),(31531,26508),(31806,26743),(32351,27197),(32896,27662),(33154,27882),(33438,28123),(33443,28128),(33990,28591),(34264,28816),(34539,29048),(35088,29516),(35363,29741),(35639,29970),(36190,30431),(36466,30658),(36730,30876),(36742,30887),(36743,30888),(37296,31352),(37570,31582),(37573,31585),(37843,31819),(37851,31826),(38128,32058),(38406,32293),(38945,32751),(38958,32760),(38963,32764),(39520,33235),(39778,33457),(40079,33708),(40357,33940),(40638,34177),(40917,34408),(41186,34633),(41199,34643),(41388,34805),(41760,35120),(42322,35587),(42323,35588),(42583,35807),(42886,36062),(43451,36529),(44016,36996),(44299,37238),(44583,37475),(44866,37714),(45150,37951),(45719,38437),(46288,38913),(46570,39146),(46573,39149),(46859,39388),(47144,39630),(47430,39875),(48003,40350),(48283,40589),(48289,40592),(48576,40836),(48862,41074),(49151,41319),(49724,41799),(49726,41801),(50303,42292),(50880,42776)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check005 :
    PLift (groupData 116162 50880 483 578 g005 points005) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts005 :
    compareNamed primeRoster 19 16 116162 50880 points005 := by
  decide +kernel

private theorem cover005 : covers 483 578 :=
  @groupChecked primeRoster 5000 16 116162 50880 483 578 g005 points005
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check005.down counts005

private def g006 : List Row :=
  [⟨579,571,6629,8578⟩,
  ⟨580,579,8824,9071⟩,
  ⟨581,580,9311,9555⟩,
  ⟨582,581,9803,10041⟩,
  ⟨583,540,0,10542⟩,
  ⟨584,580,10039,11034⟩,
  ⟨585,576,9303,11527⟩,
  ⟨586,585,11773,12019⟩,
  ⟨587,584,11772,12516⟩,
  ⟨588,585,12266,13011⟩,
  ⟨589,586,12760,13505⟩,
  ⟨590,586,13009,13998⟩,
  ⟨591,590,14247,14502⟩,
  ⟨592,589,14246,14997⟩,
  ⟨593,590,14746,15497⟩,
  ⟨594,590,14995,15992⟩,
  ⟨595,591,15495,16494⟩,
  ⟨596,594,16493,16986⟩,
  ⟨597,583,13978,17498⟩,
  ⟨598,595,17239,18009⟩,
  ⟨599,593,16983,18509⟩,
  ⟨600,590,16485,19018⟩,
  ⟨601,600,19277,19541⟩,
  ⟨602,594,18002,20037⟩,
  ⟨603,602,20298,20547⟩,
  ⟨604,599,19786,21057⟩,
  ⟨605,604,21311,21567⟩,
  ⟨606,604,21566,22069⟩,
  ⟨607,597,20027,22583⟩,
  ⟨608,604,22067,23110⟩,
  ⟨609,597,20532,23629⟩,
  ⟨610,606,23109,24150⟩,
  ⟨611,606,23363,24662⟩,
  ⟨612,602,22572,25183⟩,
  ⟨613,612,25433,25687⟩,
  ⟨614,611,25432,26204⟩,
  ⟨615,614,26466,26731⟩,
  ⟨616,610,25683,27248⟩,
  ⟨617,613,26730,27771⟩,
  ⟨618,615,27507,28295⟩,
  ⟨619,605,25162,28818⟩,
  ⟨620,619,29081,29338⟩,
  ⟨621,620,29602,29860⟩,
  ⟨622,621,30123,30387⟩,
  ⟨623,611,27754,30923⟩,
  ⟨624,617,29597,31450⟩,
  ⟨625,609,27743,31970⟩,
  ⟨626,609,28003,32497⟩,
  ⟨627,626,32753,33014⟩,
  ⟨628,626,33013,33540⟩,
  ⟨629,625,33012,34071⟩,
  ⟨630,616,30903,34612⟩,
  ⟨631,621,32487,35143⟩,
  ⟨632,629,34877,35674⟩,
  ⟨633,631,35674,36210⟩,
  ⟨634,628,35138,36757⟩,
  ⟨635,629,35670,37294⟩,
  ⟨636,635,37565,37830⟩,
  ⟨637,626,35393,38374⟩,
  ⟨638,637,38646,38924⟩,
  ⟨639,638,39191,39458⟩,
  ⟨640,638,39457,39996⟩,
  ⟨641,633,38368,40535⟩,
  ⟨642,639,40265,41071⟩,
  ⟨643,641,41071,41625⟩,
  ⟨644,642,41624,42165⟩,
  ⟨645,642,41900,42705⟩,
  ⟨646,645,42979,43259⟩,
  ⟨647,642,42435,43802⟩,
  ⟨648,633,40241,44344⟩,
  ⟨649,644,43527,44893⟩,
  ⟨650,649,45169,45447⟩,
  ⟨651,643,43797,45992⟩,
  ⟨652,650,45991,46540⟩,
  ⟨653,622,38545,47100⟩,
  ⟨654,652,47099,47656⟩,
  ⟨655,637,43225,48213⟩,
  ⟨656,648,46533,48760⟩,
  ⟨657,652,47927,49313⟩,
  ⟨658,657,49583,49859⟩,
  ⟨659,648,47365,50413⟩,
  ⟨660,655,49581,50960⟩,
  ⟨661,657,50411,51522⟩,
  ⟨662,658,50958,52091⟩,
  ⟨663,661,52091,52657⟩,
  ⟨664,663,52933,53212⟩,
  ⟨665,664,53493,53773⟩,
  ⟨666,665,54052,54326⟩,
  ⟨667,660,52929,54881⟩,
  ⟨668,667,55170,55457⟩,
  ⟨669,664,54599,56031⟩,
  ⟨670,669,56314,56606⟩,
  ⟨671,669,56606,57168⟩,
  ⟨672,671,57441,57730⟩,
  ⟨673,672,58011,58307⟩,
  ⟨674,672,58306,58883⟩]

private def points006 : List (ℕ × ℕ) := [(0,0),(7895,6629),(10211,8578),(10500,8824),(10790,9071),(11070,9303),(11080,9311),(11371,9555),(11661,9803),(11950,10039),(11952,10041),(12535,10542),(13118,11034),(13703,11527),(13994,11772),(13995,11773),(14288,12019),(14580,12266),(14875,12516),(15167,12760),(15460,13009),(15462,13011),(16051,13505),(16616,13978),(16640,13998),(16934,14246),(16935,14247),(17231,14502),(17525,14746),(17820,14995),(17822,14997),(18413,15495),(18415,15497),(19008,15992),(19590,16485),(19602,16493),(19603,16494),(20194,16983),(20198,16986),(20495,17239),(20795,17498),(21384,18002),(21392,18009),(21991,18509),(22590,19018),(22890,19277),(23191,19541),(23488,19786),(23780,20027),(23792,20037),(24093,20298),(24377,20532),(24395,20547),(24998,21057),(25300,21311),(25602,21566),(25603,21567),(26206,22067),(26208,22069),(26802,22572),(26815,22583),(27420,23109),(27422,23110),(27723,23363),(28031,23629),(28640,24150),(29251,24662),(29838,25162),(29862,25183),(30167,25432),(30168,25433),(30470,25683),(30475,25687),(31088,26204),(31395,26466),(31701,26730),(31703,26731),(32318,27248),(32625,27507),(32903,27743),(32917,27754),(32935,27771),(33207,28003),(33552,28295),(34171,28818),(34480,29081),(34790,29338),(35094,29597),(35100,29602),(35411,29860),(35721,30123),(36032,30387),(36630,30903),(36655,30923),(37278,31450),(37903,31970),(38516,32487),(38528,32497),(38841,32753),(39153,33012),(39154,33013),(39155,33014),(39782,33540),(40411,34071),(41040,34612),(41354,34877),(41666,35138),(41671,35143),(41971,35393),(42298,35670),(42302,35674),(42935,36210),(43568,36757),(44203,37294),(44520,37565),(44838,37830),(45467,38368),(45475,38374),(45673,38545),(45793,38646),(46112,38924),(46431,39191),(46750,39457),(46751,39458),(47390,39996),(47682,40241),(47709,40265),(48031,40535),(48672,41071),(49314,41624),(49315,41625),(49635,41900),(49958,42165),(50277,42435),(50603,42705),(50925,42979),(51208,43225),(51248,43259),(51568,43527),(51887,43797),(51895,43802),(52542,44344),(53191,44893),(53515,45169),(53840,45447),(54490,45991),(54491,45992),(55134,46533),(55142,46540),(55794,47099),(55795,47100),(56106,47365),(56448,47656),(56772,47927),(57103,48213),(57758,48760),(58415,49313),(58740,49581),(58743,49583),(59072,49859),(59729,50411),(59731,50413),(60388,50958),(60390,50960),(61051,51522),(61712,52091),(62375,52657),(62700,52929),(62706,52933),(63038,53212),(63370,53493),(63703,53773),(64035,54052),(64368,54326),(64698,54599),(65035,54881),(65368,55170),(65702,55457),(66371,56031),(66705,56314),(67040,56606),(67711,57168),(68046,57441),(68382,57730),(68718,58011),(69054,58306),(69055,58307),(69728,58883)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check006 :
    PLift (groupData 157410 69728 579 674 g006 points006) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts006 :
    compareNamed primeRoster 19 17 157410 69728 points006 := by
  decide +kernel

private theorem cover006 : covers 579 674 :=
  @groupChecked primeRoster 5000 17 157410 69728 579 674 g006 points006
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check006.down counts006

private def g007 : List Row :=
  [⟨675,663,0,3437⟩,
  ⟨676,673,3155,4012⟩,
  ⟨677,675,4012,4588⟩,
  ⟨678,675,4294,5160⟩,
  ⟨679,678,5456,5743⟩,
  ⟨680,675,4870,6331⟩,
  ⟨681,680,6619,6907⟩,
  ⟨682,671,4281,7469⟩,
  ⟨683,681,7469,8055⟩,
  ⟨684,682,8054,8635⟩,
  ⟨685,680,7759,9209⟩,
  ⟨686,670,5134,9783⟩,
  ⟨687,683,9207,10358⟩,
  ⟨688,684,9782,10947⟩,
  ⟨689,681,9202,11525⟩,
  ⟨690,679,8907,12095⟩,
  ⟨691,690,12389,12692⟩,
  ⟨692,691,12984,13271⟩,
  ⟨693,687,12091,13859⟩,
  ⟨694,687,12384,14446⟩,
  ⟨695,694,14741,15030⟩,
  ⟨696,686,12681,15620⟩,
  ⟨697,696,15926,16232⟩,
  ⟨698,696,16231,16820⟩,
  ⟨699,693,15617,17407⟩,
  ⟨700,695,16525,17994⟩,
  ⟨701,694,16522,18587⟩,
  ⟨702,701,18880,19184⟩,
  ⟨703,702,19482,19781⟩,
  ⟨704,703,20073,20366⟩,
  ⟨705,702,20072,20967⟩,
  ⟨706,702,20365,21566⟩,
  ⟨707,702,20659,22158⟩,
  ⟨708,700,20360,22749⟩,
  ⟨709,708,23056,23364⟩,
  ⟨710,709,23668,23970⟩,
  ⟨711,706,23055,24564⟩,
  ⟨712,711,24870,25167⟩,
  ⟨713,710,24869,25776⟩,
  ⟨714,710,25166,26383⟩,
  ⟨715,710,25471,26988⟩,
  ⟨716,714,26987,27602⟩,
  ⟨717,716,27897,28203⟩,
  ⟨718,717,28505,28821⟩,
  ⟨719,701,23933,29421⟩,
  ⟨720,719,29715,30022⟩,
  ⟨721,718,29714,30633⟩,
  ⟨722,720,30632,31245⟩,
  ⟨723,720,30939,31851⟩,
  ⟨724,719,30937,32470⟩,
  ⟨725,723,32470,33082⟩,
  ⟨726,716,30621,33688⟩,
  ⟨727,724,33386,34310⟩,
  ⟨728,719,32156,34929⟩,
  ⟨729,721,33074,35547⟩,
  ⟨730,726,34928,36165⟩,
  ⟨731,730,36479,36786⟩,
  ⟨732,731,37103,37416⟩,
  ⟨733,715,32436,38024⟩,
  ⟨734,730,37414,38655⟩,
  ⟨735,732,38345,39285⟩,
  ⟨736,714,33030,39909⟩,
  ⟨737,731,38652,40532⟩,
  ⟨738,734,39908,41161⟩,
  ⟨739,737,41161,41791⟩,
  ⟨740,738,41790,42423⟩,
  ⟨741,726,38321,43050⟩,
  ⟨742,741,43360,43678⟩,
  ⟨743,730,40201,44304⟩,
  ⟨744,734,41782,44939⟩,
  ⟨745,742,44624,45569⟩,
  ⟨746,744,45568,46213⟩,
  ⟨747,744,45889,46843⟩,
  ⟨748,747,47162,47483⟩,
  ⟨749,733,43022,48103⟩,
  ⟨750,745,47159,48753⟩,
  ⟨751,750,49063,49392⟩,
  ⟨752,751,49708,50025⟩,
  ⟨753,752,50345,50669⟩,
  ⟨754,753,50994,51312⟩,
  ⟨755,717,39760,51952⟩,
  ⟨756,749,50339,52588⟩,
  ⟨757,750,50990,53221⟩,
  ⟨758,756,53220,53869⟩,
  ⟨759,752,52258,54514⟩,
  ⟨760,756,53867,55154⟩,
  ⟨761,760,55481,55801⟩,
  ⟨762,757,54827,56451⟩,
  ⟨763,762,56769,57092⟩,
  ⟨764,731,47046,57739⟩,
  ⟨765,763,57739,58391⟩,
  ⟨766,760,57089,59038⟩,
  ⟨767,766,59355,59672⟩,
  ⟨768,766,59671,60332⟩,
  ⟨769,764,59353,60995⟩,
  ⟨770,763,59351,61649⟩]

private def points007 : List (ℕ × ℕ) := [(0,0),(3711,3155),(4050,3437),(4725,4012),(5048,4281),(5062,4294),(5402,4588),(5737,4870),(6047,5134),(6079,5160),(6418,5456),(6758,5743),(7437,6331),(7777,6619),(8118,6907),(8799,7469),(9137,7759),(9481,8054),(9482,8055),(10165,8635),(10492,8907),(10842,9202),(10848,9207),(10850,9209),(11533,9782),(11535,9783),(12222,10358),(12909,10947),(13598,11525),(14283,12091),(14287,12095),(14626,12384),(14632,12389),(14965,12681),(14978,12692),(15323,12984),(15669,13271),(16362,13859),(17055,14446),(17402,14741),(17750,15030),(18441,15617),(18445,15620),(18793,15926),(19141,16231),(19142,16232),(19484,16522),(19487,16525),(19839,16820),(20538,17407),(21237,17994),(21938,18587),(22288,18880),(22639,19184),(22990,19482),(23342,19781),(23692,20072),(23693,20073),(24037,20360),(24043,20365),(24045,20366),(24394,20659),(24750,20967),(25455,21566),(26162,22158),(26869,22749),(27220,23055),(27223,23056),(27578,23364),(27932,23668),(28247,23933),(28287,23970),(28998,24564),(29352,24869),(29353,24870),(29707,25166),(29709,25167),(30062,25471),(30422,25776),(31135,26383),(31849,26987),(31850,26988),(32565,27602),(32923,27897),(33282,28203),(33640,28505),(33999,28821),(34718,29421),(35076,29714),(35077,29715),(35437,30022),(36145,30621),(36157,30632),(36158,30633),(36515,30937),(36517,30939),(36879,31245),(37602,31851),(37953,32156),(38285,32436),(38325,32470),(38989,33030),(39042,33074),(39050,33082),(39411,33386),(39775,33688),(40502,34310),(41227,34928),(41229,34929),(41958,35547),(42687,36165),(43052,36479),(43418,36786),(43783,37103),(44147,37414),(44149,37416),(44882,38024),(45220,38321),(45247,38345),(45611,38652),(45615,38655),(46350,39285),(46905,39760),(47083,39908),(47085,39909),(47432,40201),(47822,40532),(48559,41161),(49285,41782),(49297,41790),(49298,41791),(50037,42423),(50746,43022),(50778,43050),(51148,43360),(51519,43678),(52262,44304),(52632,44624),(53005,44939),(53749,45568),(53750,45569),(54121,45889),(54495,46213),(55242,46843),(55479,47046),(55612,47159),(55615,47162),(55989,47483),(56738,48103),(57487,48753),(57862,49063),(58238,49392),(58613,49708),(58989,50025),(59359,50339),(59365,50345),(59742,50669),(60112,50990),(60118,50994),(60495,51312),(61250,51952),(61621,52258),(62005,52588),(62761,53220),(62762,53221),(63517,53867),(63519,53869),(64278,54514),(64654,54827),(65037,55154),(65417,55481),(65798,55801),(66559,56451),(66940,56769),(67317,57089),(67322,57092),(68085,57739),(68850,58391),(69615,59038),(69992,59351),(69995,59353),(69998,59355),(70381,59671),(70382,59672),(71149,60332),(71918,60995),(72687,61649)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check007 :
    PLift (groupData 223763 72687 675 770 g007 points007) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts007 :
    compareNamed primeRoster 19 17 223763 72687 points007 := by
  decide +kernel

private theorem cover007 : covers 675 770 :=
  @groupChecked primeRoster 5000 17 223763 72687 675 770 g007 points007
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check007.down counts007

private def g008 : List Row :=
  [⟨771,741,0,9812⟩,
  ⟨772,769,9477,10462⟩,
  ⟨773,766,8833,11120⟩,
  ⟨774,753,4881,11779⟩,
  ⟨775,774,12110,12439⟩,
  ⟨776,755,6178,13097⟩,
  ⟨777,773,12438,13759⟩,
  ⟨778,774,13095,14412⟩,
  ⟨779,778,14742,15079⟩,
  ⟨780,779,15407,15738⟩,
  ⟨781,768,12091,16395⟩,
  ⟨782,775,14737,17065⟩,
  ⟨783,779,16393,17730⟩,
  ⟨784,774,15069,18396⟩,
  ⟨785,781,17728,19057⟩,
  ⟨786,785,19385,19711⟩,
  ⟨787,776,16720,20388⟩,
  ⟨788,784,19709,21058⟩,
  ⟨789,782,19380,21733⟩,
  ⟨790,784,20384,22405⟩,
  ⟨791,780,19373,23077⟩,
  ⟨792,780,19697,23758⟩,
  ⟨793,790,23423,24440⟩,
  ⟨794,791,24098,25122⟩,
  ⟨795,791,24438,25795⟩,
  ⟨796,786,23067,26470⟩,
  ⟨797,793,25793,27146⟩,
  ⟨798,791,25459,27819⟩,
  ⟨799,797,27819,28505⟩,
  ⟨800,798,28504,29197⟩,
  ⟨801,792,26798,29880⟩,
  ⟨802,798,29196,30567⟩,
  ⟨803,802,30914,31245⟩,
  ⟨804,803,31585,31926⟩,
  ⟨805,794,28841,32608⟩,
  ⟨806,801,31583,33291⟩,
  ⟨807,777,23665,33983⟩,
  ⟨808,799,31577,34666⟩,
  ⟨809,795,30546,35356⟩,
  ⟨810,802,33285,36046⟩,
  ⟨811,807,35354,36735⟩,
  ⟨812,811,37084,37429⟩,
  ⟨813,812,37771,38111⟩,
  ⟨814,805,35686,38808⟩,
  ⟨815,811,38109,39498⟩,
  ⟨816,814,39497,40186⟩,
  ⟨817,814,39842,40887⟩,
  ⟨818,806,37414,41589⟩,
  ⟨819,815,40886,42285⟩,
  ⟨820,815,41233,42976⟩,
  ⟨821,820,43328,43678⟩,
  ⟨822,821,44025,44375⟩,
  ⟨823,822,44725,45078⟩,
  ⟨824,823,45441,45780⟩,
  ⟨825,824,46130,46470⟩,
  ⟨826,823,46129,47175⟩,
  ⟨827,826,47533,47880⟩,
  ⟨828,820,45773,48586⟩,
  ⟨829,824,47530,49290⟩,
  ⟨830,829,49638,49992⟩,
  ⟨831,826,48936,50701⟩,
  ⟨832,825,48933,51414⟩,
  ⟨833,831,51414,52116⟩,
  ⟨834,833,52471,52827⟩,
  ⟨835,826,50339,53534⟩,
  ⟨836,833,53181,54254⟩,
  ⟨837,829,52110,54971⟩,
  ⟨838,835,54608,55686⟩,
  ⟨839,836,55328,56396⟩,
  ⟨840,831,53879,57102⟩,
  ⟨841,838,56746,57815⟩,
  ⟨842,839,57456,58528⟩,
  ⟨843,841,58528,59240⟩,
  ⟨844,840,58526,59957⟩,
  ⟨845,844,60317,60679⟩,
  ⟨846,837,58159,61403⟩,
  ⟨847,846,61763,62128⟩,
  ⟨848,847,62497,62860⟩,
  ⟨849,847,62860,63582⟩,
  ⟨850,846,62859,64296⟩,
  ⟨851,848,63933,65017⟩,
  ⟨852,851,65377,65744⟩,
  ⟨853,847,64292,66468⟩,
  ⟨854,849,65374,67196⟩,
  ⟨855,852,66836,67926⟩,
  ⟨856,848,65738,68653⟩,
  ⟨857,855,68653,69383⟩,
  ⟨858,855,69017,70105⟩,
  ⟨859,852,68282,70840⟩,
  ⟨860,859,71212,71569⟩,
  ⟨861,860,71940,72310⟩,
  ⟨862,857,71209,73047⟩,
  ⟨863,860,72678,73794⟩,
  ⟨864,858,72305,74538⟩,
  ⟨865,859,73043,75279⟩,
  ⟨866,864,75278,76013⟩]

private def points008 : List (ℕ × ℕ) := [(0,0),(5755,4881),(7284,6178),(10403,8833),(11178,9477),(11565,9812),(12336,10462),(13109,11120),(13882,11779),(14248,12091),(14269,12110),(14655,12438),(14657,12439),(15430,13095),(15432,13097),(16209,13759),(16986,14412),(17369,14737),(17375,14742),(17752,15069),(17765,15079),(18154,15407),(18544,15738),(19323,16393),(19325,16395),(19700,16720),(20106,17065),(20887,17728),(20889,17730),(21672,18396),(22457,19057),(22834,19373),(22843,19380),(22849,19385),(23224,19697),(23240,19709),(23242,19711),(24024,20384),(24029,20388),(24816,21058),(25605,21733),(26394,22405),(27172,23067),(27185,23077),(27579,23423),(27864,23665),(27976,23758),(28371,24098),(28767,24438),(28769,24440),(29562,25122),(29953,25459),(30355,25793),(30357,25795),(31152,26470),(31540,26798),(31949,27146),(32746,27819),(33544,28504),(33545,28505),(33929,28841),(34342,29196),(34344,29197),(35145,29880),(35922,30546),(35946,30567),(36347,30914),(36749,31245),(37140,31577),(37147,31583),(37150,31585),(37552,31926),(38357,32608),(39154,33285),(39162,33291),(39969,33983),(40776,34666),(41583,35354),(41585,35356),(41979,35686),(42394,36046),(43205,36735),(43610,37084),(43998,37414),(44016,37429),(44422,37771),(44827,38109),(44829,38111),(45642,38808),(46456,39497),(46457,39498),(46863,39842),(47272,40186),(48087,40886),(48089,40887),(48494,41233),(48906,41589),(49725,42285),(50544,42976),(50954,43328),(51365,43678),(51775,44025),(52186,44375),(52597,44725),(53009,45078),(53420,45441),(53824,45773),(53832,45780),(54243,46129),(54244,46130),(54657,46470),(55482,47175),(55892,47530),(55895,47533),(56309,47880),(57136,48586),(57544,48933),(57547,48936),(57965,49290),(58379,49638),(58794,49992),(59199,50339),(59625,50701),(60456,51414),(61281,52110),(61289,52116),(61705,52471),(62122,52827),(62538,53181),(62957,53534),(63364,53879),(63792,54254),(64209,54608),(64629,54971),(65046,55328),(65466,55686),(66305,56396),(66723,56746),(67144,57102),(67563,57456),(67985,57815),(68395,58159),(68824,58526),(68826,58528),(69669,59240),(70512,59957),(70934,60317),(71357,60679),(72202,61403),(72625,61763),(73049,62128),(73472,62497),(73894,62859),(73896,62860),(74745,63582),(75168,63933),(75590,64292),(75594,64296),(76445,65017),(76867,65374),(76870,65377),(77288,65738),(77296,65744),(78149,66468),(78574,66836),(79002,67196),(79857,67926),(80278,68282),(80712,68653),(81139,69017),(81569,69383),(82426,70105),(83285,70840),(83711,71209),(83714,71212),(84144,71569),(84574,71940),(85000,72305),(85005,72310),(85434,72678),(85862,73043),(85866,73047),(86729,73794),(87592,74538),(88456,75278),(88457,75279),(89322,76013)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check008 :
    PLift (groupData 285656 89322 771 866 g008 points008) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts008 :
    compareNamed primeRoster 19 17 285656 89322 points008 := by
  decide +kernel

private theorem cover008 : covers 771 866 :=
  @groupChecked primeRoster 5000 17 285656 89322 771 866 g008 points008
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check008.down counts008

private def g009 : List Row :=
  [⟨867,861,1874,4092⟩,
  ⟨868,855,0,4833⟩,
  ⟨869,867,4833,5563⟩,
  ⟨870,869,5936,6312⟩,
  ⟨871,865,4830,7060⟩,
  ⟨872,871,7430,7795⟩,
  ⟨873,871,7795,8531⟩,
  ⟨874,866,6305,9280⟩,
  ⟨875,874,9651,10016⟩,
  ⟨876,874,10015,10760⟩,
  ⟨877,876,11134,11506⟩,
  ⟨878,875,11133,12251⟩,
  ⟨879,878,12624,13003⟩,
  ⟨880,877,12623,13750⟩,
  ⟨881,866,8885,14510⟩,
  ⟨882,880,14509,15260⟩,
  ⟨883,881,15260,16012⟩,
  ⟨884,878,14506,16761⟩,
  ⟨885,883,16761,17519⟩,
  ⟨886,885,17895,18271⟩,
  ⟨887,886,18643,19028⟩,
  ⟨888,886,19027,19778⟩,
  ⟨889,879,16751,20543⟩,
  ⟨890,872,14475,21298⟩,
  ⟨891,888,20916,22054⟩,
  ⟨892,889,21670,22811⟩,
  ⟨893,876,17100,23568⟩,
  ⟨894,890,22810,24335⟩,
  ⟨895,886,21663,25084⟩,
  ⟨896,875,17848,25857⟩,
  ⟨897,896,26246,26628⟩,
  ⟨898,895,26245,27381⟩,
  ⟨899,891,25078,28165⟩,
  ⟨900,896,27379,28928⟩,
  ⟨901,899,28928,29692⟩,
  ⟨902,901,30073,30463⟩,
  ⟨903,901,30463,31239⟩,
  ⟨904,889,26221,32004⟩,
  ⟨905,890,26978,32789⟩,
  ⟨906,897,30066,33550⟩,
  ⟨907,905,33550,34320⟩,
  ⟨908,906,34319,35088⟩,
  ⟨909,900,32385,35857⟩,
  ⟨910,908,35856,36629⟩,
  ⟨911,901,33538,37416⟩,
  ⟨912,911,37804,38187⟩,
  ⟨913,903,35078,38960⟩,
  ⟨914,911,38572,39752⟩,
  ⟨915,912,39358,40532⟩,
  ⟨916,915,40928,41315⟩,
  ⟨917,910,39353,42106⟩,
  ⟨918,917,42497,42883⟩,
  ⟨919,912,40924,43662⟩,
  ⟨920,919,44057,44458⟩,
  ⟨921,897,35793,45244⟩,
  ⟨922,916,43658,46027⟩,
  ⟨923,917,44455,46815⟩,
  ⟨924,923,47210,47613⟩,
  ⟨925,921,46813,48406⟩,
  ⟨926,925,48794,49186⟩,
  ⟨927,925,49186,49982⟩,
  ⟨928,927,50382,50767⟩,
  ⟨929,924,49580,51554⟩,
  ⟨930,926,50765,52354⟩,
  ⟨931,924,50376,53144⟩,
  ⟨932,925,51161,53932⟩,
  ⟨933,930,53533,54722⟩,
  ⟨934,898,41180,55525⟩,
  ⟨935,928,53529,56335⟩,
  ⟨936,928,53925,57122⟩,
  ⟨937,928,54317,57927⟩,
  ⟨938,937,58322,58720⟩,
  ⟨939,938,59118,59515⟩,
  ⟨940,935,58319,60322⟩,
  ⟨941,936,59115,61131⟩,
  ⟨942,930,57107,61932⟩,
  ⟨943,942,62332,62733⟩,
  ⟨944,932,58705,63546⟩,
  ⟨945,924,55880,64350⟩,
  ⟨946,945,64754,65156⟩,
  ⟨947,945,65156,65964⟩,
  ⟨948,947,66366,66769⟩,
  ⟨949,944,65551,67593⟩,
  ⟨950,949,67993,68407⟩,
  ⟨951,945,66765,69229⟩,
  ⟨952,946,67589,70036⟩,
  ⟨953,948,68813,70837⟩,
  ⟨954,949,69622,71634⟩,
  ⟨955,952,71232,72454⟩,
  ⟨956,953,72051,73288⟩,
  ⟨957,947,70026,74110⟩,
  ⟨958,957,74519,74925⟩,
  ⟨959,955,74108,75743⟩,
  ⟨960,959,76154,76563⟩,
  ⟨961,949,72437,77380⟩,
  ⟨962,959,76967,78187⟩]

private def points009 : List (ℕ × ℕ) := [(0,0),(2174,1874),(4775,4092),(5638,4830),(5642,4833),(6511,5563),(6945,5936),(7372,6305),(7380,6312),(8251,7060),(8686,7430),(9122,7795),(9995,8531),(10403,8885),(10868,9280),(11305,9651),(11742,10015),(11743,10016),(12618,10760),(13055,11133),(13056,11134),(13495,11506),(14372,12251),(14810,12623),(14811,12624),(15251,13003),(16130,13750),(16970,14475),(17006,14506),(17010,14509),(17011,14510),(17892,15260),(18775,16012),(19646,16751),(19658,16761),(20064,17100),(20543,17519),(20930,17848),(20985,17895),(21428,18271),(21871,18643),(22314,19027),(22315,19028),(23202,19778),(24091,20543),(24534,20916),(24980,21298),(25415,21663),(25424,21670),(25871,22054),(26760,22810),(26762,22811),(27655,23568),(28548,24335),(29435,25078),(29443,25084),(30338,25857),(30758,26221),(30785,26245),(30786,26246),(31235,26628),(31655,26978),(32130,27379),(32132,27381),(33031,28165),(33930,28928),(34831,29692),(35271,30066),(35281,30073),(35732,30463),(36635,31239),(37538,32004),(37980,32385),(38443,32789),(39336,33538),(39348,33550),(40254,34319),(40255,34320),(41150,35078),(41162,35088),(41999,35793),(42070,35856),(42071,35857),(42980,36629),(43891,37416),(44346,37804),(44802,38187),(45257,38572),(45715,38960),(46165,39353),(46170,39358),(46628,39752),(47543,40532),(47994,40924),(48000,40928),(48296,41180),(48458,41315),(49375,42106),(49833,42497),(50292,42883),(51206,43658),(51211,43662),(51670,44057),(52126,44455),(52130,44458),(53051,45244),(53972,46027),(54893,46813),(54895,46815),(55356,47210),(55818,47613),(56743,48406),(57205,48794),(57668,49186),(58128,49580),(58595,49982),(59052,50376),(59058,50382),(59520,50765),(59522,50767),(59980,51161),(60451,51554),(61380,52354),(62311,53144),(62770,53529),(62775,53533),(63234,53925),(63242,53932),(63698,54317),(64175,54722),(65108,55525),(65520,55880),(66043,56335),(66960,57107),(66978,57122),(67915,57927),(68380,58319),(68383,58322),(68834,58705),(68852,58720),(69318,59115),(69321,59118),(69791,59515),(70730,60322),(71671,61131),(72612,61932),(73083,62332),(73555,62733),(74498,63546),(75443,64350),(75915,64754),(76388,65156),(76858,65551),(77335,65964),(77808,66366),(78278,66765),(78282,66769),(79226,67589),(79231,67593),(79705,67993),(80180,68407),(80652,68813),(81131,69229),(81603,69622),(82070,70026),(82082,70036),(83035,70837),(83510,71232),(83988,71634),(84464,72051),(84925,72437),(84943,72454),(85898,73288),(86853,74108),(86855,74110),(87333,74519),(87812,74925),(88771,75743),(89250,76154),(89730,76563),(90209,76967),(90691,77380),(91652,78187)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check009 :
    PLift (groupData 371070 91652 867 962 g009 points009) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts009 :
    compareNamed primeRoster 19 17 371070 91652 points009 := by
  decide +kernel

private theorem cover009 : covers 867 962 :=
  @groupChecked primeRoster 5000 17 371070 91652 867 962 g009 points009
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check009.down counts009

private def g010 : List Row :=
  [⟨963,962,11565,11980⟩,
  ⟨964,962,11979,12806⟩,
  ⟨965,963,12806,13634⟩,
  ⟨966,965,14049,14461⟩,
  ⟨967,930,0,15281⟩,
  ⟨968,967,15699,16112⟩,
  ⟨969,968,16528,16946⟩,
  ⟨970,969,17362,17776⟩,
  ⟨971,966,16526,18601⟩,
  ⟨972,971,19009,19424⟩,
  ⟨973,969,18599,20268⟩,
  ⟨974,973,20689,21105⟩,
  ⟨975,964,17349,21939⟩,
  ⟨976,975,22350,22771⟩,
  ⟨977,973,21937,23608⟩,
  ⟨978,970,21098,24447⟩,
  ⟨979,976,24022,25294⟩,
  ⟨980,969,21515,26132⟩,
  ⟨981,974,24018,26965⟩,
  ⟨982,972,23597,27798⟩,
  ⟨983,981,27798,28642⟩,
  ⟨984,979,27377,29484⟩,
  ⟨985,984,29906,30326⟩,
  ⟨986,968,23574,31157⟩,
  ⟨987,984,30738,32008⟩,
  ⟨988,987,32422,32845⟩,
  ⟨989,985,32007,33702⟩,
  ⟨990,989,34123,34557⟩,
  ⟨991,990,34981,35406⟩,
  ⟨992,991,35834,36257⟩,
  ⟨993,989,35404,37107⟩,
  ⟨994,990,36255,37960⟩,
  ⟨995,994,38387,38812⟩,
  ⟨996,995,39240,39659⟩,
  ⟨997,994,39239,40524⟩,
  ⟨998,993,39237,41373⟩,
  ⟨999,997,41373,42221⟩,
  ⟨1000,998,42220,43081⟩,
  ⟨1001,995,41370,43930⟩,
  ⟨1002,1001,44348,44778⟩,
  ⟨1003,997,43077,45643⟩,
  ⟨1004,1001,45215,46488⟩,
  ⟨1005,999,44774,47340⟩,
  ⟨1006,998,44770,48207⟩,
  ⟨1007,999,45637,49064⟩,
  ⟨1008,1006,49063,49922⟩,
  ⟨1009,999,46478,50790⟩,
  ⟨1010,1009,51222,51648⟩,
  ⟨1011,1010,52076,52509⟩,
  ⟨1012,1006,50785,53378⟩,
  ⟨1013,1003,49912,54238⟩,
  ⟨1014,1011,53806,55104⟩,
  ⟨1015,1014,55542,55971⟩,
  ⟨1016,1014,55970,56859⟩,
  ⟨1017,1007,53366,57718⟩,
  ⟨1018,1006,53360,58587⟩,
  ⟨1019,1010,55535,59462⟩,
  ⟨1020,1019,59903,60346⟩,
  ⟨1021,998,51167,61212⟩,
  ⟨1022,1020,61211,62084⟩,
  ⟨1023,1022,62519,62964⟩,
  ⟨1024,1016,60339,63842⟩,
  ⟨1025,1023,63842,64718⟩,
  ⟨1026,1012,59440,65603⟩,
  ⟨1027,1021,63840,66482⟩,
  ⟨1028,1014,61190,67365⟩,
  ⟨1029,1027,67365,68245⟩,
  ⟨1030,1029,68689,69133⟩,
  ⟨1031,1030,69573,70030⟩,
  ⟨1032,1020,65586,70901⟩,
  ⟨1033,1026,68683,71790⟩,
  ⟨1034,1032,71789,72674⟩,
  ⟨1035,1029,70899,73555⟩,
  ⟨1036,1035,73998,74445⟩,
  ⟨1037,1036,74892,75328⟩,
  ⟨1038,1037,75765,76217⟩,
  ⟨1039,1034,74890,77109⟩,
  ⟨1040,1039,77541,77988⟩,
  ⟨1041,1039,77988,78880⟩,
  ⟨1042,1037,77540,79778⟩,
  ⟨1043,1042,80220,80669⟩,
  ⟨1044,1043,81114,81575⟩,
  ⟨1045,1032,76645,82461⟩,
  ⟨1046,1038,79771,83342⟩,
  ⟨1047,1039,80663,84234⟩,
  ⟨1048,1047,84683,85134⟩,
  ⟨1049,1046,84682,86033⟩,
  ⟨1050,1045,84680,86932⟩,
  ⟨1051,1044,84677,87833⟩,
  ⟨1052,1048,86930,88723⟩,
  ⟨1053,1040,83766,89614⟩,
  ⟨1054,1049,88271,90523⟩,
  ⟨1055,1051,89612,91409⟩,
  ⟨1056,1047,88265,92316⟩,
  ⟨1057,1053,91407,93228⟩,
  ⟨1058,1053,91861,94133⟩]

private def points010 : List (ℕ × ℕ) := [(0,0),(13548,11565),(14029,11979),(14030,11980),(14993,12806),(15958,13634),(16440,14049),(16923,14461),(17890,15281),(18373,15699),(18857,16112),(19338,16526),(19341,16528),(19826,16946),(20295,17349),(20310,17362),(20795,17776),(21764,18599),(21766,18601),(22251,19009),(22737,19424),(23710,20268),(24196,20689),(24675,21098),(24683,21105),(25155,21515),(25656,21937),(25658,21939),(26145,22350),(26633,22771),(27569,23574),(27597,23597),(27610,23608),(28092,24018),(28097,24022),(28587,24447),(29566,25294),(30545,26132),(31526,26965),(32013,27377),(32507,27798),(33490,28642),(34473,29484),(34965,29906),(35458,30326),(35949,30738),(36443,31157),(37428,32007),(37430,32008),(37923,32422),(38417,32845),(39406,33702),(39900,34123),(40395,34557),(40890,34981),(41384,35404),(41386,35406),(41881,35834),(42375,36255),(42377,36257),(43370,37107),(44363,37960),(44860,38387),(45358,38812),(45852,39237),(45854,39239),(45855,39240),(46353,39659),(47350,40524),(48343,41370),(48347,41373),(49345,42220),(49346,42221),(50341,43077),(50345,43081),(51346,43930),(51846,44348),(52339,44770),(52343,44774),(52347,44778),(52847,45215),(53342,45637),(53350,45643),(54341,46478),(54353,46488),(55358,47340),(56363,48207),(57369,49063),(57370,49064),(58365,49912),(58377,49922),(59381,50785),(59386,50790),(59824,51167),(59890,51222),(60395,51648),(60900,52076),(61406,52509),(62399,53360),(62405,53366),(62417,53378),(62922,53806),(63430,54238),(64443,55104),(64940,55535),(64950,55542),(65457,55970),(65458,55971),(66473,56859),(67490,57718),(68507,58587),(69501,59440),(69526,59462),(70035,59903),(70537,60339),(70545,60346),(71541,61190),(71565,61211),(71566,61212),(72587,62084),(73098,62519),(73610,62964),(74629,63840),(74633,63842),(75658,64718),(76665,65586),(76683,65603),(77710,66482),(78737,67365),(79766,68245),(80274,68683),(80280,68689),(80795,69133),(81310,69573),(81826,70030),(82853,70899),(82857,70901),(83889,71789),(83890,71790),(84923,72674),(85958,73555),(86475,73998),(86993,74445),(87508,74890),(87511,74892),(88030,75328),(88548,75765),(89067,76217),(89565,76645),(90106,77109),(90622,77540),(90625,77541),(91145,77988),(92186,78880),(93219,79771),(93227,79778),(93748,80220),(94262,80663),(94270,80669),(94791,81114),(95313,81575),(96358,82461),(97403,83342),(97905,83766),(98450,84234),(98967,84677),(98970,84680),(98972,84682),(98973,84683),(99497,85134),(100546,86033),(101593,86930),(101595,86932),(102646,87833),(103161,88265),(103168,88271),(103697,88723),(104748,89612),(104750,89614),(105803,90523),(106856,91407),(106858,91409),(107382,91861),(107913,92316),(108970,93228),(110027,94133)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check010 :
    PLift (groupData 449655 110027 963 1058 g010 points010) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts010 :
    compareNamed primeRoster 19 17 449655 110027 points010 := by
  decide +kernel

private theorem cover010 : covers 963 1058 :=
  @groupChecked primeRoster 5000 17 449655 110027 963 1058 g010 points010
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check010.down counts010

private def g011 : List Row :=
  [⟨1059,1056,2724,4086⟩,
  ⟨1060,1049,5,5012⟩,
  ⟨1061,1048,0,5920⟩,
  ⟨1062,1061,6377,6829⟩,
  ⟨1063,1060,6377,7733⟩,
  ⟨1064,1063,8192,8641⟩,
  ⟨1065,1063,8641,9549⟩,
  ⟨1066,1062,8639,10460⟩,
  ⟨1067,1066,10919,11382⟩,
  ⟨1068,1062,9544,12299⟩,
  ⟨1069,1063,10456,13220⟩,
  ⟨1070,1068,13219,14138⟩,
  ⟨1071,1060,9989,15059⟩,
  ⟨1072,1067,13675,15982⟩,
  ⟨1073,1069,15058,16891⟩,
  ⟨1074,1068,15055,17810⟩,
  ⟨1075,1067,15052,18739⟩,
  ⟨1076,1075,19191,19646⟩,
  ⟨1077,1076,20103,20571⟩,
  ⟨1078,1075,20102,21486⟩,
  ⟨1079,1068,17339,22393⟩,
  ⟨1080,1079,22854,23323⟩,
  ⟨1081,1079,23323,24247⟩,
  ⟨1082,1064,16855,25170⟩,
  ⟨1083,1080,24708,26106⟩,
  ⟨1084,1076,23316,27035⟩,
  ⟨1085,1080,25638,27962⟩,
  ⟨1086,1067,20065,28883⟩,
  ⟨1087,1085,28883,29803⟩,
  ⟨1088,1085,29343,30736⟩,
  ⟨1089,1088,31198,31660⟩,
  ⟨1090,1088,31659,32592⟩,
  ⟨1091,1087,31658,33529⟩,
  ⟨1092,1083,30264,34459⟩,
  ⟨1093,1081,29788,35399⟩,
  ⟨1094,1093,35866,36342⟩,
  ⟨1095,1093,36342,37280⟩,
  ⟨1096,1095,37748,38217⟩,
  ⟨1097,1091,36338,39168⟩,
  ⟨1098,1092,37275,40120⟩,
  ⟨1099,1090,36801,41064⟩,
  ⟨1100,1095,39634,42017⟩,
  ⟨1101,1098,41542,42953⟩,
  ⟨1102,1101,43417,43889⟩,
  ⟨1103,1102,44355,44834⟩,
  ⟨1104,1090,39144,45775⟩,
  ⟨1105,1101,44832,46725⟩,
  ⟨1106,1105,47202,47676⟩,
  ⟨1107,1106,48149,48630⟩,
  ⟨1108,1106,48629,49580⟩,
  ⟨1109,1106,49099,50530⟩,
  ⟨1110,1105,49097,51475⟩,
  ⟨1111,1108,51010,52448⟩,
  ⟨1112,1111,52924,53413⟩,
  ⟨1113,1110,52924,54361⟩,
  ⟨1114,1112,54360,55317⟩,
  ⟨1115,1101,49560,56278⟩,
  ⟨1116,1103,50992,57233⟩,
  ⟨1117,1116,57701,58181⟩,
  ⟨1118,1117,58657,59127⟩,
  ⟨1119,1116,58656,60096⟩,
  ⟨1120,1119,60582,61063⟩,
  ⟨1121,1118,60582,62025⟩,
  ⟨1122,1112,58168,62969⟩,
  ⟨1123,1112,58644,63934⟩,
  ⟨1124,1111,58638,64895⟩,
  ⟨1125,1118,62490,65859⟩,
  ⟨1126,1125,66335,66819⟩,
  ⟨1127,1117,62959,67785⟩,
  ⟨1128,1116,62953,68738⟩,
  ⟨1129,1126,68259,69714⟩,
  ⟨1130,1129,70210,70692⟩,
  ⟨1131,1130,71181,71668⟩,
  ⟨1132,1129,71181,72640⟩,
  ⟨1133,1126,70204,73607⟩,
  ⟨1134,1131,73116,74576⟩,
  ⟨1135,1133,74576,75538⟩,
  ⟨1136,1135,76024,76513⟩,
  ⟨1137,1133,75536,77497⟩,
  ⟨1138,1136,77496,78483⟩,
  ⟨1139,1119,69672,79453⟩,
  ⟨1140,1127,74078,80439⟩,
  ⟨1141,1135,78479,81415⟩,
  ⟨1142,1136,79449,82388⟩,
  ⟨1143,1142,82885,83374⟩,
  ⟨1144,1143,83866,84359⟩,
  ⟨1145,1128,76973,85339⟩,
  ⟨1146,1133,79925,86325⟩,
  ⟨1147,1143,85337,87314⟩,
  ⟨1148,1138,83364,88295⟩,
  ⟨1149,1143,86322,89282⟩,
  ⟨1150,1149,89782,90260⟩,
  ⟨1151,1136,83841,91243⟩,
  ⟨1152,1151,91743,92230⟩,
  ⟨1153,1152,92735,93229⟩,
  ⟨1154,1148,91238,94221⟩]

private def points011 : List (ℕ × ℕ) := [(0,0),(6,5),(3188,2724),(4777,4086),(5836,5012),(6897,5920),(7426,6377),(7427,6377),(7958,6829),(9021,7733),(9552,8192),(10082,8639),(10084,8641),(11144,9544),(11149,9549),(11666,9989),(12210,10456),(12214,10460),(12747,10919),(13281,11382),(14348,12299),(15416,13219),(15417,13220),(15948,13675),(16486,14138),(17549,15052),(17552,15055),(17555,15058),(17557,15059),(18628,15982),(19660,16855),(19701,16891),(20222,17339),(20774,17810),(21849,18739),(22386,19191),(22924,19646),(23417,20065),(23461,20102),(23462,20103),(24001,20571),(25078,21486),(26157,22393),(26696,22854),(27228,23316),(27236,23323),(28317,24247),(28856,24708),(29398,25170),(29936,25638),(30481,26106),(31564,27035),(32649,27962),(33734,28883),(34276,29343),(34803,29788),(34821,29803),(35354,30264),(35908,30736),(36452,31198),(36995,31658),(36996,31659),(36997,31660),(38086,32592),(39177,33529),(40268,34459),(41361,35399),(41907,35866),(42450,36338),(42454,36342),(42991,36801),(43544,37275),(43549,37280),(44096,37748),(44644,38217),(45716,39144),(45741,39168),(46286,39634),(46838,40120),(47937,41064),(48485,41542),(49036,42017),(50137,42953),(50687,43417),(51238,43889),(51789,44355),(52339,44832),(52341,44834),(53444,45775),(54549,46725),(55101,47202),(55654,47676),(56207,48149),(56760,48629),(56761,48630),(57311,49097),(57313,49099),(57844,49560),(57868,49580),(58977,50530),(59510,50992),(59530,51010),(60086,51475),(61197,52448),(61751,52924),(61752,52924),(62308,53413),(63420,54360),(63421,54361),(64534,55317),(65649,56278),(66764,57233),(67322,57701),(67868,58168),(67881,58181),(68418,58638),(68424,58644),(68438,58656),(68439,58657),(68998,59127),(70117,60096),(70675,60582),(70676,60582),(71236,61063),(72357,62025),(72911,62490),(73460,62953),(73466,62959),(73478,62969),(74601,63934),(75724,64895),(76849,65859),(77411,66335),(77974,66819),(79101,67785),(79663,68259),(80228,68738),(81307,69672),(81357,69714),(81915,70204),(81921,70210),(82486,70692),(83050,71181),(83051,71181),(83617,71668),(84748,72640),(85313,73116),(85881,73607),(86426,74078),(87014,74576),(88147,75536),(88149,75538),(88716,76024),(89284,76513),(89816,76973),(90420,77496),(90421,77497),(91554,78479),(91558,78483),(92692,79449),(92697,79453),(93245,79925),(93836,80439),(94977,81415),(96118,82388),(96689,82885),(97248,83364),(97261,83374),(97804,83841),(97832,83866),(98404,84359),(99547,85337),(99549,85339),(100690,86322),(100694,86325),(101841,87314),(102988,88295),(104137,89282),(104711,89782),(105286,90260),(106432,91238),(106437,91243),(107012,91743),(107588,92230),(108164,92735),(108741,93229),(109894,94221)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check011 :
    PLift (groupData 555964 109894 1059 1154 g011 points011) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts011 :
    compareNamed primeRoster 19 17 555964 109894 points011 := by
  decide +kernel

private theorem cover011 : covers 1059 1154 :=
  @groupChecked primeRoster 5000 17 555964 109894 1059 1154 g011 points011
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check011.down counts011

private def g012 : List Row :=
  [⟨1155,1153,67,1059⟩,
  ⟨1156,1154,1058,2057⟩,
  ⟨1157,1152,558,3050⟩,
  ⟨1158,1157,3543,4033⟩,
  ⟨1159,1154,2549,5026⟩,
  ⟨1160,1154,3047,6024⟩,
  ⟨1161,1150,1552,7027⟩,
  ⟨1162,1149,1546,8038⟩,
  ⟨1163,1155,5018,9029⟩,
  ⟨1164,1159,7523,10032⟩,
  ⟨1165,1157,7020,11019⟩,
  ⟨1166,1142,10,12029⟩,
  ⟨1167,1141,0,13028⟩,
  ⟨1168,1167,13531,14026⟩,
  ⟨1169,1168,14525,15039⟩,
  ⟨1170,1160,11007,16036⟩,
  ⟨1171,1164,13526,17038⟩,
  ⟨1172,1166,15034,18051⟩,
  ⟨1173,1172,18555,19059⟩,
  ⟨1174,1173,19563,20053⟩,
  ⟨1175,1170,18552,21057⟩,
  ⟨1176,1175,21555,22072⟩,
  ⟨1177,1175,22072,23086⟩,
  ⟨1178,1177,23585,24095⟩,
  ⟨1179,1170,20547,25110⟩,
  ⟨1180,1173,22575,26128⟩,
  ⟨1181,1179,26128,27136⟩,
  ⟨1182,1180,27135,28136⟩,
  ⟨1183,1182,28636,29139⟩,
  ⟨1184,1174,25099,30156⟩,
  ⟨1185,1182,29644,31183⟩,
  ⟨1186,1184,31182,32211⟩,
  ⟨1187,1184,31689,33229⟩,
  ⟨1188,1187,33740,34245⟩,
  ⟨1189,1188,34751,35257⟩,
  ⟨1190,1180,31171,36300⟩,
  ⟨1191,1184,33734,37332⟩,
  ⟨1192,1187,35783,38362⟩,
  ⟨1193,1188,36819,39393⟩,
  ⟨1194,1193,39900,40408⟩,
  ⟨1195,1193,40408,41424⟩,
  ⟨1196,1191,39898,42457⟩,
  ⟨1197,1189,39387,43474⟩,
  ⟨1198,1191,40905,44491⟩,
  ⟨1199,1187,39378,45521⟩,
  ⟨1200,1192,42450,46549⟩,
  ⟨1201,1197,45519,47584⟩,
  ⟨1202,1200,47583,48622⟩,
  ⟨1203,1194,44996,49649⟩,
  ⟨1204,1203,50164,50683⟩,
  ⟨1205,1203,50683,51721⟩,
  ⟨1206,1193,46019,52755⟩,
  ⟨1207,1206,53259,53780⟩,
  ⟨1208,1206,53779,54824⟩,
  ⟨1209,1207,54824,55860⟩,
  ⟨1210,1208,55859,56896⟩,
  ⟨1211,1209,56896,57928⟩,
  ⟨1212,1207,56368,58979⟩,
  ⟨1213,1207,56892,60032⟩,
  ⟨1214,1212,60031,61066⟩,
  ⟨1215,1209,58976,62122⟩,
  ⟨1216,1206,57916,63157⟩,
  ⟨1217,1215,63157,64193⟩,
  ⟨1218,1213,62634,65236⟩,
  ⟨1219,1217,65236,66292⟩,
  ⟨1220,1205,59475,67342⟩,
  ⟨1221,1203,58947,68377⟩,
  ⟨1222,1219,67857,69427⟩,
  ⟨1223,1218,67855,70470⟩,
  ⟨1224,1220,69426,71525⟩,
  ⟨1225,1194,56269,72586⟩,
  ⟨1226,1214,67326,73633⟩,
  ⟨1227,1226,74159,74670⟩,
  ⟨1228,1226,74669,75730⟩,
  ⟨1229,1228,76248,76774⟩,
  ⟨1230,1229,77302,77834⟩,
  ⟨1231,1217,71505,78893⟩,
  ⟨1232,1231,79422,79949⟩,
  ⟨1233,1225,76768,81017⟩,
  ⟨1234,1233,81550,82084⟩,
  ⟨1235,1227,78887,83136⟩,
  ⟨1236,1223,77286,84211⟩,
  ⟨1237,1232,82610,85270⟩,
  ⟨1238,1226,79933,86352⟩,
  ⟨1239,1233,84208,87422⟩,
  ⟨1240,1238,87421,88482⟩,
  ⟨1241,1229,83121,89546⟩,
  ⟨1242,1238,88480,90611⟩,
  ⟨1243,1239,89545,91700⟩,
  ⟨1244,1241,91158,92761⟩,
  ⟨1245,1243,92761,93827⟩,
  ⟨1246,1242,92759,94902⟩,
  ⟨1247,1237,90600,95978⟩,
  ⟨1248,1245,95428,97031⟩,
  ⟨1249,1233,89519,98102⟩,
  ⟨1250,1248,98101,99188⟩]

private def points012 : List (ℕ × ℕ) := [(0,0),(12,10),(84,67),(658,558),(1238,1058),(1239,1059),(1795,1546),(1801,1552),(2394,2057),(2969,2549),(3546,3047),(3551,3050),(4129,3543),(4708,4033),(5859,5018),(5867,5026),(7026,6024),(8179,7020),(8187,7027),(8764,7523),(9348,8038),(10511,9029),(11674,10032),(12826,11007),(12839,11019),(14004,12029),(15171,13028),(15748,13526),(15754,13531),(16338,14026),(16922,14525),(17502,15034),(17507,15039),(18676,16036),(19847,17038),(21018,18051),(21601,18552),(21604,18555),(22191,19059),(22777,19563),(23364,20053),(23941,20547),(24539,21057),(25126,21555),(25714,22072),(26296,22575),(26891,23086),(27479,23585),(28068,24095),(29234,25099),(29247,25110),(30426,26128),(31606,27135),(31607,27136),(32788,28136),(33379,28636),(33971,29139),(34561,29644),(35154,30156),(36326,31171),(36338,31182),(36339,31183),(36930,31689),(37524,32211),(38711,33229),(39298,33734),(39304,33740),(39898,34245),(40492,34751),(41087,35257),(41678,35783),(42276,36300),(42868,36819),(43467,37332),(44658,38362),(45833,39378),(45843,39387),(45851,39393),(46444,39898),(46447,39900),(47044,40408),(47635,40905),(48239,41424),(49426,42450),(49434,42457),(50631,43474),(51828,44491),(52417,44996),(53025,45519),(53027,45521),(53605,46019),(54226,46549),(55426,47583),(55427,47584),(56628,48622),(57831,49649),(58432,50164),(59034,50683),(60239,51721),(61444,52755),(62047,53259),(62650,53779),(62651,53780),(63858,54824),(65066,55859),(65067,55860),(65551,56269),(65668,56368),(66272,56892),(66276,56896),(67474,57916),(67487,57928),(68658,58947),(68694,58976),(68698,58979),(69276,59475),(69910,60031),(69911,60032),(71124,61066),(72339,62122),(72943,62634),(73554,63157),(74771,64193),(75988,65236),(77207,66292),(78408,67326),(78426,67342),(79033,67855),(79035,67857),(79647,68377),(80866,69426),(80868,69427),(82091,70470),(83290,71505),(83314,71525),(84539,72586),(85764,73633),(86377,74159),(86990,74669),(86991,74670),(88218,75730),(88832,76248),(89439,76768),(89447,76774),(90040,77286),(90061,77302),(90676,77834),(91899,78887),(91907,78893),(92522,79422),(93120,79933),(93138,79949),(94371,81017),(94987,81550),(95604,82084),(96218,82610),(96821,83121),(96839,83136),(98070,84208),(98074,84211),(99311,85270),(100548,86352),(101786,87421),(101787,87422),(103024,88480),(103026,88482),(104235,89519),(104265,89545),(104267,89546),(105496,90600),(105508,90611),(106128,91158),(106751,91700),(107992,92759),(107994,92761),(109239,93827),(110484,94902),(111106,95428),(111731,95978),(112978,97031),(114226,98101),(114227,98102),(115476,99188)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check012 :
    PLift (groupData 665774 115476 1155 1250 g012 points012) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts012 :
    compareNamed primeRoster 19 17 665774 115476 points012 := by
  decide +kernel

private theorem cover012 : covers 1155 1250 :=
  @groupChecked primeRoster 5000 17 665774 115476 1155 1250 g012 points012
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check012.down counts012

private def g013 : List Row :=
  [⟨1251,1246,3780,6477⟩,
  ⟨1252,1248,5396,7541⟩,
  ⟨1253,1250,7005,8634⟩,
  ⟨1254,1236,0,9703⟩,
  ⟨1255,1253,9703,10785⟩,
  ⟨1256,1251,9165,11862⟩,
  ⟨1257,1253,10783,12950⟩,
  ⟨1258,1255,12413,14037⟩,
  ⟨1259,1257,14037,15117⟩,
  ⟨1260,1255,13486,16217⟩,
  ⟨1261,1259,16217,17287⟩,
  ⟨1262,1249,11307,18393⟩,
  ⟨1263,1248,11301,19473⟩,
  ⟨1264,1259,17835,20562⟩,
  ⟨1265,1264,21102,21656⟩,
  ⟨1266,1263,21101,22731⟩,
  ⟨1267,1263,21655,23806⟩,
  ⟨1268,1263,22194,24897⟩,
  ⟨1269,1260,21095,25997⟩,
  ⟨1270,1256,19449,27090⟩,
  ⟨1271,1267,25995,28190⟩,
  ⟨1272,1269,27647,29286⟩,
  ⟨1273,1272,29827,30375⟩,
  ⟨1274,1272,30374,31469⟩,
  ⟨1275,1272,30917,32573⟩,
  ⟨1276,1273,32019,33650⟩,
  ⟨1277,1276,34195,34751⟩,
  ⟨1278,1275,34195,35841⟩,
  ⟨1279,1274,34194,36935⟩,
  ⟨1280,1276,35839,38046⟩,
  ⟨1281,1273,34744,39159⟩,
  ⟨1282,1247,20971,40269⟩,
  ⟨1283,1277,38042,41368⟩,
  ⟨1284,1269,34172,42475⟩,
  ⟨1285,1281,41366,43577⟩,
  ⟨1286,1283,43026,44678⟩,
  ⟨1287,1283,43575,45776⟩,
  ⟨1288,1251,26390,46895⟩,
  ⟨1289,1272,38578,48012⟩,
  ⟨1290,1289,48560,49116⟩,
  ⟨1291,1284,46326,50232⟩,
  ⟨1292,1290,50231,51324⟩,
  ⟨1293,1290,50769,52440⟩,
  ⟨1294,1293,53002,53560⟩,
  ⟨1295,1293,53560,54664⟩,
  ⟨1296,1293,54106,55769⟩,
  ⟨1297,1295,55769,56887⟩,
  ⟨1298,1281,48530,58020⟩,
  ⟨1299,1278,47403,59130⟩,
  ⟨1300,1281,49642,60259⟩,
  ⟨1301,1288,54090,61376⟩,
  ⟨1302,1300,61375,62498⟩,
  ⟨1303,1294,58561,63614⟩,
  ⟨1304,1302,63613,64726⟩,
  ⟨1305,1304,65282,65838⟩,
  ⟨1306,1301,64167,66975⟩,
  ⟨1307,1302,65280,68099⟩,
  ⟨1308,1303,66410,69219⟩,
  ⟨1309,1270,48405,70360⟩,
  ⟨1310,1306,69217,71484⟩,
  ⟨1311,1303,68092,72609⟩,
  ⟨1312,1280,55656,73745⟩,
  ⟨1313,1309,72608,74887⟩,
  ⟨1314,1310,73743,76012⟩,
  ⟨1315,1310,74304,77143⟩,
  ⟨1316,1300,69191,78286⟩,
  ⟨1317,1314,77712,79417⟩,
  ⟨1318,1310,76005,80550⟩,
  ⟨1319,1318,81125,81684⟩,
  ⟨1320,1317,81124,82827⟩,
  ⟨1321,1318,82249,83968⟩,
  ⟨1322,1321,84533,85093⟩,
  ⟨1323,1305,75976,86220⟩,
  ⟨1324,1316,82821,87348⟩,
  ⟨1325,1324,87921,88495⟩,
  ⟨1326,1315,83380,89642⟩,
  ⟨1327,1323,88493,90800⟩,
  ⟨1328,1325,90217,91958⟩,
  ⟨1329,1324,90215,93099⟩,
  ⟨1330,1325,91381,94239⟩,
  ⟨1331,1328,93669,95385⟩,
  ⟨1332,1325,92516,96531⟩,
  ⟨1333,1310,84478,97679⟩,
  ⟨1334,1331,97105,98823⟩,
  ⟨1335,1334,99390,99969⟩,
  ⟨1336,1335,100538,101117⟩,
  ⟨1337,1334,100537,102266⟩,
  ⟨1338,1326,96515,103434⟩,
  ⟨1339,1329,98812,104578⟩,
  ⟨1340,1338,104577,105726⟩,
  ⟨1341,1338,105153,106884⟩,
  ⟨1342,1341,107450,108024⟩,
  ⟨1343,1333,103425,109187⟩,
  ⟨1344,1337,106302,110345⟩,
  ⟨1345,1328,101666,111502⟩,
  ⟨1346,1344,111501,112654⟩]

private def points013 : List (ℕ × ℕ) := [(0,0),(4401,3780),(6276,5396),(7529,6477),(8153,7005),(8780,7541),(10033,8634),(10656,9165),(11286,9703),(12539,10783),(12541,10785),(13140,11301),(13147,11307),(13796,11862),(14423,12413),(15053,12950),(15678,13486),(16310,14037),(17569,15117),(18828,16217),(20089,17287),(20716,17835),(21350,18393),(22588,19449),(22613,19473),(23876,20562),(24355,20971),(24498,21095),(24507,21101),(24508,21102),(25139,21655),(25141,21656),(25770,22194),(26406,22731),(27673,23806),(28940,24897),(30207,25995),(30209,25997),(30672,26390),(31478,27090),(32112,27647),(32749,28190),(34020,29286),(34656,29827),(35292,30374),(35293,30375),(35928,30917),(36566,31469),(37202,32019),(37841,32573),(39116,33650),(39726,34172),(39751,34194),(39753,34195),(39754,34195),(40385,34744),(40393,34751),(41668,35839),(41670,35841),(42949,36935),(44224,38042),(44228,38046),(44832,38578),(45509,39159),(46790,40269),(48071,41366),(48073,41368),(49356,42475),(49997,43026),(50639,43575),(50641,43577),(51926,44678),(53213,45776),(53850,46326),(54500,46895),(55089,47403),(55789,48012),(56243,48405),(56397,48530),(56433,48560),(57078,49116),(57678,49642),(58368,50231),(58369,50232),(59013,50769),(59660,51324),(60953,52440),(61599,53002),(62246,53560),(62872,54090),(62892,54106),(63541,54664),(64708,55656),(64836,55769),(66133,56887),(67430,58020),(68069,58561),(68729,59130),(70028,60259),(71328,61375),(71329,61376),(72630,62498),(73932,63613),(73933,63614),(74581,64167),(75236,64726),(75885,65280),(75888,65282),(76541,65838),(77190,66410),(77846,66975),(79145,68092),(79153,68099),(80428,69191),(80458,69217),(80460,69219),(81769,70360),(83078,71484),(84387,72608),(84389,72609),(85698,73743),(85700,73745),(86353,74304),(87013,74887),(88286,75976),(88318,76005),(88326,76012),(89641,77143),(90297,77712),(90956,78286),(92273,79417),(93590,80550),(94248,81124),(94249,81125),(94909,81684),(95567,82249),(96220,82821),(96228,82827),(96873,83380),(97549,83968),(98143,84478),(98209,84533),(98870,85093),(100193,86220),(101516,87348),(102178,87921),(102839,88493),(102841,88495),(104166,89642),(104826,90215),(104828,90217),(105493,90800),(106153,91381),(106820,91958),(107478,92516),(108149,93099),(108812,93669),(109478,94239),(110809,95385),(112122,96515),(112140,96531),(112805,97105),(113473,97679),(114794,98812),(114806,98823),(115473,99390),(116141,99969),(116807,100537),(116808,100538),(117476,101117),(118108,101666),(118813,102266),(120138,103425),(120150,103434),(121488,104577),(121489,104578),(122157,105153),(122828,105726),(123492,106302),(124169,106884),(124839,107450),(125510,108024),(126853,109187),(128196,110345),(129540,111501),(129541,111502),(130886,112654)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check013 :
    PLift (groupData 774972 130886 1251 1346 g013 points013) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts013 :
    compareNamed primeRoster 19 17 774972 130886 points013 := by
  decide +kernel

private theorem cover013 : covers 1251 1346 :=
  @groupChecked primeRoster 5000 17 774972 130886 1251 1346 g013 points013
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check013.down counts013

private def g014 : List Row :=
  [⟨1347,1328,0,11010⟩,
  ⟨1348,1343,9259,12168⟩,
  ⟨1349,1347,12168,13344⟩,
  ⟨1350,1345,11579,14505⟩,
  ⟨1351,1350,15078,15653⟩,
  ⟨1352,1350,15652,16811⟩,
  ⟨1353,1351,16811,17971⟩,
  ⟨1354,1337,9230,19138⟩,
  ⟨1355,1351,17969,20306⟩,
  ⟨1356,1349,17387,21492⟩,
  ⟨1357,1356,22075,22665⟩,
  ⟨1358,1357,23247,23825⟩,
  ⟨1359,1353,21488,24994⟩,
  ⟨1360,1359,25578,26161⟩,
  ⟨1361,1353,22659,27330⟩,
  ⟨1362,1356,24990,28499⟩,
  ⟨1363,1362,29076,29669⟩,
  ⟨1364,1342,17920,30843⟩,
  ⟨1365,1364,31429,32023⟩,
  ⟨1366,1362,30841,33184⟩,
  ⟨1367,1365,33184,34352⟩,
  ⟨1368,1331,13772,35541⟩,
  ⟨1369,1363,33180,36724⟩,
  ⟨1370,1362,33176,37899⟩,
  ⟨1371,1365,35538,39080⟩,
  ⟨1372,1370,39079,40254⟩,
  ⟨1373,1363,35531,41449⟩,
  ⟨1374,1373,42035,42625⟩,
  ⟨1375,1368,39662,43802⟩,
  ⟨1376,1374,43801,44984⟩,
  ⟨1377,1370,42029,46176⟩,
  ⟨1378,1373,44393,47359⟩,
  ⟨1379,1378,47962,48563⟩,
  ⟨1380,1379,49156,49757⟩,
  ⟨1381,1378,49155,50950⟩,
  ⟨1382,1381,51535,52129⟩,
  ⟨1383,1381,52129,53313⟩,
  ⟨1384,1377,50343,54504⟩,
  ⟨1385,1384,55094,55686⟩,
  ⟨1386,1381,53903,56889⟩,
  ⟨1387,1378,52707,58090⟩,
  ⟨1388,1386,58089,59278⟩,
  ⟨1389,1388,59867,60465⟩,
  ⟨1390,1387,59866,61658⟩,
  ⟨1391,1388,61058,62864⟩,
  ⟨1392,1389,62265,64070⟩,
  ⟨1393,1384,59857,65263⟩,
  ⟨1394,1389,63466,66464⟩,
  ⟨1395,1391,65262,67655⟩,
  ⟨1396,1394,67654,68851⟩,
  ⟨1397,1394,68253,70072⟩,
  ⟨1398,1395,69464,71268⟩,
  ⟨1399,1397,71268,72476⟩,
  ⟨1400,1394,70069,73692⟩,
  ⟨1401,1400,74297,74897⟩,
  ⟨1402,1366,54365,76110⟩,
  ⟨1403,1396,73087,77321⟩,
  ⟨1404,1398,74892,78547⟩,
  ⟨1405,1402,77937,79764⟩,
  ⟨1406,1395,74283,80985⟩,
  ⟨1407,1406,81591,82194⟩,
  ⟨1408,1403,80376,83405⟩,
  ⟨1409,1408,84006,84614⟩,
  ⟨1410,1408,84613,85832⟩,
  ⟨1411,1393,76075,87051⟩,
  ⟨1412,1404,83397,88258⟩,
  ⟨1413,1412,88871,89475⟩,
  ⟨1414,1408,87046,90681⟩,
  ⟨1415,1404,85214,91910⟩,
  ⟨1416,1403,85208,93123⟩,
  ⟨1417,1384,74177,94337⟩,
  ⟨1418,1412,91906,95553⟩,
  ⟨1419,1410,91283,96782⟩,
  ⟨1420,1419,97383,97992⟩,
  ⟨1421,1416,96169,99219⟩,
  ⟨1422,1409,92500,100440⟩,
  ⟨1423,1416,97378,101676⟩,
  ⟨1424,1413,96159,102904⟩,
  ⟨1425,1418,99831,104128⟩,
  ⟨1426,1415,98594,105346⟩,
  ⟨1427,1425,105346,106580⟩,
  ⟨1428,1391,85077,107818⟩,
  ⟨1429,1420,103505,109055⟩,
  ⟨1430,1423,105955,110283⟩,
  ⟨1431,1430,110901,111520⟩,
  ⟨1432,1430,111519,112760⟩,
  ⟨1433,1429,111518,114005⟩,
  ⟨1434,1428,111515,115246⟩,
  ⟨1435,1434,115855,116472⟩,
  ⟨1436,1431,114618,117709⟩,
  ⟨1437,1433,116471,118936⟩,
  ⟨1438,1437,119562,120184⟩,
  ⟨1439,1438,120802,121419⟩,
  ⟨1440,1438,121418,122665⟩,
  ⟨1441,1439,122665,123913⟩,
  ⟨1442,1438,122663,125158⟩]

private def points014 : List (ℕ × ℕ) := [(0,0),(10741,9230),(10774,9259),(12797,11010),(13467,11579),(14144,12168),(15493,13344),(15996,13772),(16842,14505),(17517,15078),(18192,15652),(18193,15653),(19544,16811),(20214,17387),(20836,17920),(20895,17969),(20897,17971),(22250,19138),(23605,20306),(24956,21488),(24960,21492),(25638,22075),(26309,22659),(26317,22665),(26995,23247),(27674,23825),(29028,24990),(29033,24994),(29712,25578),(30392,26161),(31753,27330),(33114,28499),(33795,29076),(34477,29669),(35838,30841),(35840,30843),(36522,31429),(37205,32023),(38562,33176),(38566,33180),(38570,33184),(39937,34352),(41292,35531),(41300,35538),(41304,35541),(42673,36724),(44042,37899),(45412,39079),(45413,39080),(46092,39662),(46784,40254),(48157,41449),(48837,42029),(48843,42035),(49530,42625),(50904,43801),(50905,43802),(51589,44393),(52280,44984),(53657,46176),(55034,47359),(55723,47962),(56413,48563),(57101,49155),(57102,49156),(57792,49757),(58476,50343),(59173,50950),(59863,51535),(60554,52129),(61235,52707),(61937,53313),(62625,53903),(63158,54365),(63320,54504),(64012,55094),(64705,55686),(66090,56889),(67476,58089),(67477,58090),(68864,59278),(69548,59857),(69557,59866),(69558,59867),(70253,60465),(70946,61058),(71642,61658),(72336,62265),(73033,62864),(73725,63466),(74424,64070),(75815,65262),(75817,65263),(77210,66464),(78604,67654),(78605,67655),(79301,68253),(80000,68851),(80697,69464),(81392,70069),(81397,70072),(82794,71268),(84193,72476),(84886,73087),(85592,73692),(86156,74177),(86277,74283),(86292,74297),(86988,74892),(86993,74897),(88354,76075),(88394,76110),(89797,77321),(90497,77937),(91200,78547),(92605,79764),(93304,80376),(94010,80985),(94713,81591),(95417,82194),(96816,83397),(96824,83405),(97528,84006),(98232,84613),(98233,84614),(98766,85077),(98916,85208),(98922,85214),(99642,85832),(101048,87046),(101053,87051),(102464,88258),(103170,88871),(103877,89475),(105290,90681),(105987,91283),(106700,91906),(106705,91910),(107391,92500),(108120,93123),(109537,94337),(110954,95553),(111648,96159),(111660,96169),(112373,96782),(113076,97378),(113082,97383),(113792,97992),(114487,98594),(115213,99219),(115917,99831),(116634,100440),(118057,101676),(119480,102904),(120182,103505),(120905,104128),(122330,105346),(123037,105955),(123757,106580),(125184,107818),(126613,109055),(128042,110283),(128757,110901),(129468,111515),(129471,111518),(129472,111519),(129473,111520),(130904,112760),(132337,114005),(133050,114618),(133770,115246),(134487,115855),(135203,116471),(135205,116472),(136640,117709),(138077,118936),(138795,119562),(139514,120184),(140233,120802),(140952,121418),(140953,121419),(142390,122663),(142392,122665),(143833,123913),(145274,125158)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check014 :
    PLift (groupData 894408 145274 1347 1442 g014 points014) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts014 :
    compareNamed primeRoster 19 18 894408 145274 points014 := by
  decide +kernel

private theorem cover014 : covers 1347 1442 :=
  @groupChecked primeRoster 5000 18 894408 145274 1347 1442 g014 points014
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check014.down counts014

private def g015 : List Row :=
  [⟨1443,1435,5594,10593⟩,
  ⟨1444,1425,0,11841⟩,
  ⟨1445,1426,1228,13079⟩,
  ⟨1446,1444,13078,14325⟩,
  ⟨1447,1446,14950,15571⟩,
  ⟨1448,1443,13694,16835⟩,
  ⟨1449,1444,14947,18083⟩,
  ⟨1450,1441,13688,19326⟩,
  ⟨1451,1438,12445,20576⟩,
  ⟨1452,1445,17452,21825⟩,
  ⟨1453,1452,22450,23076⟩,
  ⟨1454,1453,23711,24335⟩,
  ⟨1455,1446,19944,25581⟩,
  ⟨1456,1454,25580,26845⟩,
  ⟨1457,1455,26845,28103⟩,
  ⟨1458,1455,27472,29366⟩,
  ⟨1459,1442,19922,30615⟩,
  ⟨1460,1458,30614,31875⟩,
  ⟨1461,1459,31875,33139⟩,
  ⟨1462,1455,29985,34393⟩,
  ⟨1463,1461,34393,35659⟩,
  ⟨1464,1463,36290,36919⟩,
  ⟨1465,1462,36289,38174⟩,
  ⟨1466,1465,38808,39438⟩,
  ⟨1467,1464,38807,40715⟩,
  ⟨1468,1467,41342,41975⟩,
  ⟨1469,1466,41341,43228⟩,
  ⟨1470,1467,42604,44492⟩,
  ⟨1471,1470,45124,45757⟩,
  ⟨1472,1467,43850,47043⟩,
  ⟨1473,1469,45755,48312⟩,
  ⟨1474,1461,41324,49584⟩,
  ⟨1475,1464,43839,50861⟩,
  ⟨1476,1475,51486,52121⟩,
  ⟨1477,1472,50212,53402⟩,
  ⟨1478,1467,47672,54684⟩,
  ⟨1479,1473,52118,55962⟩,
  ⟨1480,1471,51478,57231⟩,
  ⟨1481,1478,56595,58510⟩,
  ⟨1482,1468,50840,59791⟩,
  ⟨1483,1481,59791,61083⟩,
  ⟨1484,1480,59789,62374⟩,
  ⟨1485,1484,63011,63647⟩,
  ⟨1486,1482,62373,64924⟩,
  ⟨1487,1477,59780,66194⟩,
  ⟨1488,1481,63005,67494⟩,
  ⟨1489,1485,66192,68781⟩,
  ⟨1490,1481,64282,70080⟩,
  ⟨1491,1475,61054,71373⟩,
  ⟨1492,1484,67487,72658⟩,
  ⟨1493,1452,47502,73932⟩,
  ⟨1494,1482,67477,75224⟩,
  ⟨1495,1485,70071,76513⟩,
  ⟨1496,1475,64247,77802⟩,
  ⟨1497,1496,78449,79097⟩,
  ⟨1498,1497,79748,80394⟩,
  ⟨1499,1489,75214,81688⟩,
  ⟨1500,1494,79092,82979⟩,
  ⟨1501,1488,75855,84293⟩,
  ⟨1502,1501,84935,85577⟩,
  ⟨1503,1501,85577,86857⟩,
  ⟨1504,1490,79074,88155⟩,
  ⟨1505,1504,88808,89448⟩,
  ⟨1506,1488,79060,90747⟩,
  ⟨1507,1494,83622,92037⟩,
  ⟨1508,1507,92674,93325⟩,
  ⟨1509,1505,92035,94632⟩,
  ⟨1510,1503,91386,95938⟩,
  ⟨1511,1492,84895,97257⟩,
  ⟨1512,1510,97256,98571⟩,
  ⟨1513,1510,97919,99876⟩,
  ⟨1514,1509,97917,101181⟩,
  ⟨1515,1489,85504,102492⟩,
  ⟨1516,1514,102491,103796⟩,
  ⟨1517,1480,80893,105095⟩,
  ⟨1518,1517,105751,106407⟩,
  ⟨1519,1517,106407,107735⟩,
  ⟨1520,1504,98542,109035⟩,
  ⟨1521,1515,106405,110355⟩,
  ⟨1522,1521,111015,111673⟩,
  ⟨1523,1520,111014,112992⟩,
  ⟨1524,1523,113657,114318⟩,
  ⟨1525,1501,99814,115647⟩,
  ⟨1526,1524,115646,116949⟩,
  ⟨1527,1521,114316,118284⟩,
  ⟨1528,1525,117613,119594⟩,
  ⟨1529,1524,117612,120914⟩,
  ⟨1530,1521,116289,122237⟩,
  ⟨1531,1522,117606,123559⟩,
  ⟨1532,1525,120247,124900⟩,
  ⟨1533,1528,122890,126224⟩,
  ⟨1534,1531,125555,127549⟩,
  ⟨1535,1523,120897,128878⟩,
  ⟨1536,1535,129539,130194⟩,
  ⟨1537,1519,119560,131522⟩,
  ⟨1538,1495,104255,132839⟩]

private def points015 : List (ℕ × ℕ) := [(0,0),(1435,1228),(6503,5594),(12275,10593),(13718,11841),(14419,12445),(15162,13078),(15163,13079),(15875,13688),(15882,13694),(16608,14325),(17328,14947),(17331,14950),(18055,15571),(19502,16835),(20220,17452),(20951,18083),(22400,19326),(23089,19922),(23115,19944),(23851,20576),(25302,21825),(26028,22450),(26755,23076),(27481,23711),(28208,24335),(29662,25580),(29663,25581),(31118,26845),(31845,27472),(32575,28103),(34032,29366),(34755,29985),(35490,30614),(35491,30615),(36950,31875),(38411,33139),(39872,34393),(41335,35659),(42065,36289),(42066,36290),(42798,36919),(44263,38174),(44994,38807),(44995,38808),(45728,39438),(47195,40715),(47907,41324),(47927,41341),(47928,41342),(48662,41975),(49395,42604),(50131,43228),(50850,43839),(50862,43850),(51600,44492),(52335,45124),(53069,45755),(53071,45757),(54542,47043),(55068,47502),(55263,47672),(56015,48312),(57488,49584),(58222,50212),(58938,50840),(58963,50861),(59690,51478),(59700,51486),(60434,52118),(60438,52121),(61915,53402),(63392,54684),(64871,55962),(65609,56595),(66350,57231),(67831,58510),(69300,59780),(69310,59789),(69312,59791),(70763,61054),(70795,61083),(72276,62373),(72278,62374),(73014,63005),(73020,63011),(73763,63647),(74450,64247),(74495,64282),(75248,64924),(76733,66192),(76735,66194),(78204,67477),(78214,67487),(78222,67494),(79711,68781),(81188,70071),(81200,70080),(82691,71373),(84182,72658),(85675,73932),(87156,75214),(87168,75224),(87894,75855),(88663,76513),(90158,77802),(90906,78449),(91614,79060),(91630,79074),(91650,79092),(91655,79097),(92403,79748),(93152,80394),(93730,80893),(94651,81688),(96150,82979),(96879,83622),(97651,84293),(98356,84895),(98401,84935),(99068,85504),(99152,85577),(100655,86857),(102158,88155),(102910,88808),(103663,89448),(105168,90747),(105915,91386),(106673,92035),(106675,92037),(107428,92674),(108182,93325),(109691,94632),(111200,95938),(112710,97256),(112711,97257),(113463,97917),(113465,97919),(114190,98542),(114222,98571),(115663,99814),(115735,99876),(117248,101181),(118762,102491),(118763,102492),(120278,103796),(120805,104255),(121795,105095),(122553,105751),(123308,106405),(123312,106407),(124831,107735),(126350,109035),(127871,110355),(128630,111014),(128631,111015),(129392,111673),(130915,112992),(131676,113657),(132434,114316),(132438,114318),(133962,115646),(133963,115647),(134715,116289),(135488,116949),(136241,117606),(136248,117612),(136250,117613),(137015,118284),(138502,119560),(138542,119594),(139300,120247),(140053,120897),(140071,120914),(141600,122237),(142362,122890),(143131,123559),(144662,124900),(145427,125555),(146195,126224),(147728,127549),(149263,128878),(150030,129539),(150798,130194),(152335,131522),(153872,132839)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check015 :
    PLift (groupData 1028850 153872 1443 1538 g015 points015) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts015 :
    compareNamed primeRoster 19 18 1028850 153872 points015 := by
  decide +kernel

private theorem cover015 : covers 1443 1538 :=
  @groupChecked primeRoster 5000 18 1028850 153872 1443 1538 g015 points015
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check015.down counts015

private def g016 : List Row :=
  [⟨1539,1533,8,3984⟩,
  ⟨1540,1538,3983,5326⟩,
  ⟨1541,1531,0,6654⟩,
  ⟨1542,1532,1329,7990⟩,
  ⟨1543,1540,7326,9324⟩,
  ⟨1544,1543,9983,10648⟩,
  ⟨1545,1538,7321,11986⟩,
  ⟨1546,1544,11985,13304⟩,
  ⟨1547,1546,13974,14647⟩,
  ⟨1548,1546,14646,16001⟩,
  ⟨1549,1541,11980,17319⟩,
  ⟨1550,1547,16660,18668⟩,
  ⟨1551,1547,17318,20001⟩,
  ⟨1552,1546,17315,21354⟩,
  ⟨1553,1552,22032,22702⟩,
  ⟨1554,1535,11285,24037⟩,
  ⟨1555,1550,22029,25370⟩,
  ⟨1556,1555,26049,26718⟩,
  ⟨1557,1551,24034,28062⟩,
  ⟨1558,1550,24030,29409⟩,
  ⟨1559,1558,30081,30764⟩,
  ⟨1560,1559,31437,32116⟩,
  ⟨1561,1560,32786,33460⟩,
  ⟨1562,1560,33459,34828⟩,
  ⟨1563,1556,31431,36169⟩,
  ⟨1564,1563,36840,37509⟩,
  ⟨1565,1564,38192,38866⟩,
  ⟨1566,1560,36165,40216⟩,
  ⟨1567,1562,38189,41566⟩,
  ⟨1568,1567,42243,42918⟩,
  ⟨1569,1568,43591,44267⟩,
  ⟨1570,1565,42240,45618⟩,
  ⟨1571,1563,41560,46985⟩,
  ⟨1572,1565,43587,48346⟩,
  ⟨1573,1566,44946,49713⟩,
  ⟨1574,1550,34763,51072⟩,
  ⟨1575,1569,48343,52437⟩,
  ⟨1576,1573,51757,53804⟩,
  ⟨1577,1575,53804,55158⟩,
  ⟨1578,1577,55827,56519⟩,
  ⟨1579,1573,53800,57894⟩,
  ⟨1580,1579,58570,59257⟩,
  ⟨1581,1574,55821,60622⟩,
  ⟨1582,1580,60621,61980⟩,
  ⟨1583,1568,53094,63346⟩,
  ⟨1584,1578,60617,64722⟩,
  ⟨1585,1578,61300,66087⟩,
  ⟨1586,1585,66767,67451⟩,
  ⟨1587,1586,68147,68838⟩,
  ⟨1588,1586,68837,70214⟩,
  ⟨1589,1564,54416,71566⟩,
  ⟨1590,1589,72252,72944⟩,
  ⟨1591,1589,72944,74302⟩,
  ⟨1592,1588,72942,75687⟩,
  ⟨1593,1592,76378,77074⟩,
  ⟨1594,1588,74297,78448⟩,
  ⟨1595,1588,74987,79837⟩,
  ⟨1596,1589,76372,81215⟩,
  ⟨1597,1593,79835,82596⟩,
  ⟨1598,1581,72222,83974⟩,
  ⟨1599,1598,84659,85358⟩,
  ⟨1600,1589,79131,86744⟩,
  ⟨1601,1600,87432,88120⟩,
  ⟨1602,1598,86742,89513⟩,
  ⟨1603,1599,88119,90894⟩,
  ⟨1604,1602,90893,92270⟩,
  ⟨1605,1560,62449,93659⟩,
  ⟨1606,1603,92972,95034⟩,
  ⟨1607,1603,93657,96410⟩,
  ⟨1608,1593,87407,97800⟩,
  ⟨1609,1608,98493,99195⟩,
  ⟨1610,1609,99885,100589⟩,
  ⟨1611,1606,98491,101978⟩,
  ⟨1612,1611,102673,103372⟩,
  ⟨1613,1612,104068,104772⟩,
  ⟨1614,1613,105472,106172⟩,
  ⟨1615,1612,105471,107577⟩,
  ⟨1616,1606,101967,108978⟩,
  ⟨1617,1605,101963,110364⟩,
  ⟨1618,1610,106164,111753⟩,
  ⟨1619,1616,111055,113167⟩,
  ⟨1620,1615,111053,114562⟩,
  ⟨1621,1607,106150,115974⟩,
  ⟨1622,1618,114560,117371⟩,
  ⟨1623,1614,112451,118758⟩,
  ⟨1624,1622,118757,120170⟩,
  ⟨1625,1616,115258,121588⟩,
  ⟨1626,1625,122278,122982⟩,
  ⟨1627,1623,121586,124383⟩,
  ⟨1628,1621,120875,125786⟩,
  ⟨1629,1595,103244,127198⟩,
  ⟨1630,1628,127197,128594⟩,
  ⟨1631,1630,129294,129997⟩,
  ⟨1632,1629,129293,131424⟩,
  ⟨1633,1632,132112,132822⟩,
  ⟨1634,1633,133530,134246⟩]

private def points016 : List (ℕ × ℕ) := [(0,0),(8,8),(1536,1329),(4624,3983),(4625,3984),(6164,5326),(7705,6654),(8469,7321),(8474,7326),(9246,7990),(10789,9324),(11560,9983),(12332,10648),(13059,11285),(13869,11980),(13876,11985),(13877,11986),(15422,13304),(16195,13974),(16968,14646),(16969,14647),(18516,16001),(19289,16660),(20060,17315),(20063,17318),(20065,17319),(21614,18668),(23165,20001),(24716,21354),(25489,22029),(25492,22032),(26269,22702),(27814,24030),(27818,24034),(27822,24037),(29377,25370),(30154,26049),(30932,26718),(32489,28062),(34046,29409),(34825,30081),(35605,30764),(36378,31431),(36384,31437),(37164,32116),(37944,32786),(38724,33459),(38725,33460),(40214,34763),(40286,34828),(41844,36165),(41849,36169),(42630,36840),(43412,37509),(44191,38189),(44194,38192),(44977,38866),(46542,40216),(48101,41560),(48109,41566),(48889,42240),(48892,42243),(49676,42918),(50454,43587),(50460,43591),(51245,44267),(52023,44946),(52814,45618),(54385,46985),(55952,48343),(55956,48346),(57529,49713),(59102,51072),(59888,51757),(60677,52437),(61436,53094),(62248,53800),(62252,53804),(62962,54416),(63829,55158),(64611,55821),(64617,55827),(65406,56519),(66985,57894),(67774,58570),(68564,59257),(70140,60617),(70144,60621),(70145,60622),(70929,61300),(71726,61980),(72264,62449),(73309,63346),(74892,64722),(76477,66087),(77269,66767),(78062,67451),(78855,68147),(79648,68837),(79649,68838),(81236,70214),(82825,71566),(83583,72222),(83619,72252),(84412,72942),(84414,72944),(86000,74297),(86005,74302),(86794,74987),(87596,75687),(88386,76372),(88392,76378),(89189,77074),(90782,78448),(91564,79131),(92375,79835),(92377,79837),(93972,81215),(95569,82596),(97166,83974),(97965,84659),(98765,85358),(100362,86742),(100364,86744),(101136,87407),(101164,87432),(101963,88119),(101965,88120),(103566,89513),(105168,90893),(105169,90894),(106772,92270),(107573,92972),(108375,93657),(108377,93659),(109982,95034),(111589,96410),(113196,97800),(113997,98491),(114000,98493),(114805,99195),(115609,99885),(116414,100589),(118007,101963),(118012,101967),(118025,101978),(118830,102673),(119492,103244),(119636,103372),(120442,104068),(121249,104772),(122054,105471),(122055,105472),(122838,106150),(122854,106164),(122862,106172),(124477,107577),(126092,108978),(127709,110364),(128514,111053),(128516,111055),(129326,111753),(130125,112451),(130945,113167),(132562,114560),(132564,114562),(133364,115258),(134185,115974),(135806,117371),(137428,118757),(137429,118758),(139052,120170),(139858,120875),(140675,121586),(140677,121588),(141489,122278),(142302,122982),(143929,124383),(145556,125786),(147184,127197),(147185,127198),(148814,128594),(149628,129293),(149629,129294),(150445,129997),(152076,131424),(152892,132112),(153709,132822),(154525,133530),(155342,134246)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check016 :
    PLift (groupData 1179636 155342 1539 1634 g016 points016) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts016 :
    compareNamed primeRoster 19 18 1179636 155342 points016 := by
  decide +kernel

private theorem cover016 : covers 1539 1634 :=
  @groupChecked primeRoster 5000 18 1179636 155342 1539 1634 g016 points016
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check016.down counts016

private def g017 : List Row :=
  [⟨1635,1634,8514,9225⟩,
  ⟨1636,1634,9224,10627⟩,
  ⟨1637,1620,0,12044⟩,
  ⟨1638,1621,1412,13468⟩,
  ⟨1639,1637,13468,14878⟩,
  ⟨1640,1629,8504,16293⟩,
  ⟨1641,1638,15583,17708⟩,
  ⟨1642,1640,17707,19122⟩,
  ⟨1643,1642,19832,20541⟩,
  ⟨1644,1619,4185,21968⟩,
  ⟨1645,1643,21968,23384⟩,
  ⟨1646,1644,23383,24800⟩,
  ⟨1647,1644,24092,26226⟩,
  ⟨1648,1647,26938,27649⟩,
  ⟨1649,1648,28359,29057⟩,
  ⟨1650,1649,29778,30502⟩,
  ⟨1651,1637,21947,31937⟩,
  ⟨1652,1651,32650,33373⟩,
  ⟨1653,1651,33373,34799⟩,
  ⟨1654,1653,35519,36243⟩,
  ⟨1655,1652,35518,37688⟩,
  ⟨1656,1652,36242,39105⟩,
  ⟨1657,1651,36240,40538⟩,
  ⟨1658,1648,34787,41974⟩,
  ⟨1659,1657,41974,43410⟩,
  ⟨1660,1650,37677,44860⟩,
  ⟨1661,1657,43408,46297⟩,
  ⟨1662,1652,40527,47720⟩,
  ⟨1663,1660,47011,49159⟩,
  ⟨1664,1663,49875,50594⟩,
  ⟨1665,1656,45563,52035⟩,
  ⟨1666,1654,44843,53478⟩,
  ⟨1667,1650,42669,54926⟩,
  ⟨1668,1657,48422,56367⟩,
  ⟨1669,1659,50584,57812⟩,
  ⟨1670,1666,56365,59262⟩,
  ⟨1671,1657,50573,60711⟩,
  ⟨1672,1659,52739,62154⟩,
  ⟨1673,1660,54187,63611⟩,
  ⟨1674,1671,62892,65050⟩,
  ⟨1675,1673,65050,66486⟩,
  ⟨1676,1672,65048,67937⟩,
  ⟨1677,1671,65046,69368⟩,
  ⟨1678,1675,68651,70815⟩,
  ⟨1679,1677,70815,72265⟩,
  ⟨1680,1677,71541,73708⟩,
  ⟨1681,1678,72986,75161⟩,
  ⟨1682,1675,71536,76636⟩,
  ⟨1683,1674,71532,78085⟩,
  ⟨1684,1667,67179,79520⟩,
  ⟨1685,1680,77356,80970⟩,
  ⟨1686,1646,53305,82434⟩,
  ⟨1687,1680,78792,83900⟩,
  ⟨1688,1683,81702,85353⟩,
  ⟨1689,1687,85353,86819⟩,
  ⟨1690,1688,86818,88275⟩,
  ⟨1691,1681,82427,89753⟩,
  ⟨1692,1691,90486,91219⟩,
  ⟨1693,1690,90485,92676⟩,
  ⟨1694,1693,93404,94150⟩,
  ⟨1695,1690,91946,95621⟩,
  ⟨1696,1695,96351,97096⟩,
  ⟨1697,1693,95620,98571⟩,
  ⟨1698,1692,95617,100034⟩,
  ⟨1699,1683,89724,101505⟩,
  ⟨1700,1699,102239,102976⟩,
  ⟨1701,1700,103710,104452⟩,
  ⟨1702,1698,102974,105929⟩,
  ⟨1703,1702,106677,107402⟩,
  ⟨1704,1702,107401,108882⟩,
  ⟨1705,1704,109615,110355⟩,
  ⟨1706,1699,106673,111823⟩,
  ⟨1707,1692,102215,113309⟩,
  ⟨1708,1705,112567,114792⟩,
  ⟨1709,1702,111084,116257⟩,
  ⟨1710,1709,117001,117743⟩,
  ⟨1711,1707,116255,119228⟩,
  ⟨1712,1702,113296,120703⟩,
  ⟨1713,1712,121451,122201⟩,
  ⟨1714,1711,121450,123668⟩,
  ⟨1715,1712,122938,125158⟩,
  ⟨1716,1712,123667,126656⟩,
  ⟨1717,1716,127396,128152⟩,
  ⟨1718,1716,128151,129628⟩,
  ⟨1719,1717,129628,131120⟩,
  ⟨1720,1716,129626,132623⟩,
  ⟨1721,1709,125144,134109⟩,
  ⟨1722,1716,131115,135590⟩,
  ⟨1723,1718,133367,137076⟩,
  ⟨1724,1720,135588,138573⟩,
  ⟨1725,1722,137815,140066⟩,
  ⟨1726,1718,135582,141567⟩,
  ⟨1727,1725,141567,143053⟩,
  ⟨1728,1724,141566,144535⟩,
  ⟨1729,1728,145289,146041⟩,
  ⟨1730,1728,146040,147543⟩]

private def points017 : List (ℕ × ℕ) := [(0,0),(1629,1412),(4848,4185),(9810,8504),(9825,8514),(10642,9224),(10643,9225),(12278,10627),(13915,12044),(15552,13468),(17191,14878),(18009,15583),(18830,16293),(20470,17707),(20471,17708),(22112,19122),(22933,19832),(23755,20541),(25374,21947),(25398,21968),(27042,23383),(27043,23384),(27864,24092),(28688,24800),(30335,26226),(31158,26938),(31982,27649),(32806,28359),(33631,29057),(34455,29778),(35280,30502),(36931,31937),(37756,32650),(38582,33373),(40222,34787),(40235,34799),(41060,35518),(41061,35519),(41884,36240),(41886,36242),(41888,36243),(43530,37677),(43543,37688),(45198,39105),(46842,40527),(46855,40538),(48512,41974),(49305,42669),(50169,43408),(50171,43410),(51812,44843),(51830,44860),(52650,45563),(53491,46297),(54320,47011),(55152,47720),(55968,48422),(56815,49159),(57646,49875),(58454,50573),(58466,50584),(58478,50594),(60143,52035),(60954,52739),(61608,53305),(61808,53478),(62620,54187),(63475,54926),(65140,56365),(65142,56367),(66811,57812),(68480,59262),(70151,60711),(71822,62154),(72657,62892),(73495,63611),(75164,65046),(75166,65048),(75168,65050),(76843,66486),(77644,67179),(78518,67937),(79355,68651),(80195,69368),(81872,70815),(82701,71532),(82705,71536),(82710,71541),(83551,72265),(84389,72986),(85230,73708),(86911,75161),(88592,76636),(89430,77356),(90275,78085),(91110,78792),(91958,79520),(93643,80970),(94482,81702),(95316,82427),(95328,82434),(97015,83900),(98702,85353),(100390,86818),(100391,86819),(102080,88275),(103739,89724),(103771,89753),(104615,90485),(104616,90486),(105462,91219),(106305,91946),(107155,92676),(108001,93404),(108848,94150),(110538,95617),(110541,95620),(110543,95621),(111390,96351),(112238,97096),(113935,98571),(115632,100034),(117331,101505),(118152,102215),(118180,102239),(119028,102974),(119030,102976),(119880,103710),(120731,104452),(122432,105929),(123277,106673),(123283,106677),(124134,107401),(124135,107402),(125838,108882),(126690,109615),(127543,110355),(128389,111084),(129248,111823),(130100,112567),(130942,113296),(130955,113309),(132662,114792),(134369,116255),(134371,116257),(135225,117001),(136080,117743),(137791,119228),(139502,120703),(140357,121450),(140358,121451),(141215,122201),(142070,122938),(142926,123667),(142928,123668),(144625,125144),(144643,125158),(146358,126656),(147216,127396),(148074,128151),(148075,128152),(149790,129626),(149792,129628),(151506,131115),(151511,131120),(153230,132623),(154087,133367),(154951,134109),(156664,135582),(156670,135588),(156672,135590),(158395,137076),(159255,137815),(160118,138573),(161843,140066),(163566,141566),(163568,141567),(165295,143053),(167022,144535),(167886,145289),(168750,146040),(168751,146041),(170480,147543)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check017 :
    PLift (groupData 1325970 170480 1635 1730 g017 points017) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts017 :
    compareNamed primeRoster 19 18 1325970 170480 points017 := by
  decide +kernel

private theorem cover017 : covers 1635 1730 :=
  @groupChecked primeRoster 5000 18 1325970 170480 1635 1730 g017 points017
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check017.down counts017

private def g018 : List Row :=
  [⟨1731,1729,6820,8318⟩,
  ⟨1732,1727,6074,9811⟩,
  ⟨1733,1727,6816,11306⟩,
  ⟨1734,1733,12054,12812⟩,
  ⟨1735,1731,11304,14313⟩,
  ⟨1736,1733,13555,15806⟩,
  ⟨1737,1736,16562,17324⟩,
  ⟨1738,1735,16561,18831⟩,
  ⟨1739,1735,17323,20344⟩,
  ⟨1740,1711,0,21841⟩,
  ⟨1741,1734,18073,23356⟩,
  ⟨1742,1735,19575,24863⟩,
  ⟨1743,1725,12778,26382⟩,
  ⟨1744,1737,22592,27899⟩,
  ⟨1745,1737,23350,29401⟩,
  ⟨1746,1741,27142,30920⟩,
  ⟨1747,1746,31674,32441⟩,
  ⟨1748,1744,30918,33951⟩,
  ⟨1749,1745,32439,35470⟩,
  ⟨1750,1739,28633,36979⟩,
  ⟨1751,1742,31666,38515⟩,
  ⟨1752,1733,25591,40028⟩,
  ⟨1753,1746,36224,41537⟩,
  ⟨1754,1736,29363,43038⟩,
  ⟨1755,1753,43038,44560⟩,
  ⟨1756,1755,45309,46078⟩,
  ⟨1757,1753,44558,47605⟩,
  ⟨1758,1756,47604,49105⟩,
  ⟨1759,1756,48350,50622⟩,
  ⟨1760,1750,44548,52155⟩,
  ⟨1761,1753,47597,53712⟩,
  ⟨1762,1759,52925,55221⟩,
  ⟨1763,1761,55221,56745⟩,
  ⟨1764,1757,52920,58265⟩,
  ⟨1765,1762,57501,59802⟩,
  ⟨1766,1765,60560,61312⟩,
  ⟨1767,1752,51372,62848⟩,
  ⟨1768,1767,63609,64384⟩,
  ⟨1769,1765,62846,65917⟩,
  ⟨1770,1768,65916,67445⟩,
  ⟨1771,1764,63603,68979⟩,
  ⟨1772,1770,68978,70517⟩,
  ⟨1773,1770,69755,72062⟩,
  ⟨1774,1771,71291,73603⟩,
  ⟨1775,1768,69751,75135⟩,
  ⟨1776,1775,75898,76659⟩,
  ⟨1777,1776,77433,78191⟩,
  ⟨1778,1767,71277,79749⟩,
  ⟨1779,1777,79749,81295⟩,
  ⟨1780,1775,78972,82821⟩,
  ⟨1781,1770,75885,84362⟩,
  ⟨1782,1770,76644,85907⟩,
  ⟨1783,1773,79738,87452⟩,
  ⟨1784,1782,87451,89002⟩,
  ⟨1785,1781,87451,90542⟩,
  ⟨1786,1772,81275,92078⟩,
  ⟨1787,1785,92078,93626⟩,
  ⟨1788,1776,85890,95171⟩,
  ⟨1789,1775,85884,96708⟩,
  ⟨1790,1768,81244,98247⟩,
  ⟨1791,1786,95944,99803⟩,
  ⟨1792,1775,88203,101348⟩,
  ⟨1793,1791,101348,102902⟩,
  ⟨1794,1791,102122,104446⟩,
  ⟨1795,1790,102120,106007⟩,
  ⟨1796,1794,106006,107561⟩,
  ⟨1797,1785,99785,109114⟩,
  ⟨1798,1795,108343,110673⟩,
  ⟨1799,1798,111455,112224⟩,
  ⟨1800,1798,112223,113772⟩,
  ⟨1801,1799,113772,115350⟩,
  ⟨1802,1790,107543,116908⟩,
  ⟨1803,1801,116908,118470⟩,
  ⟨1804,1802,118469,120040⟩,
  ⟨1805,1800,117688,121608⟩,
  ⟨1806,1804,121607,123156⟩,
  ⟨1807,1805,123156,124730⟩,
  ⟨1808,1800,120032,126287⟩,
  ⟨1809,1804,123943,127865⟩,
  ⟨1810,1795,117664,129428⟩,
  ⟨1811,1791,115305,130992⟩,
  ⟨1812,1809,130203,132568⟩,
  ⟨1813,1811,132568,134140⟩,
  ⟨1814,1812,134139,135702⟩,
  ⟨1815,1803,127849,137286⟩,
  ⟨1816,1815,138074,138855⟩,
  ⟨1817,1816,139650,140452⟩,
  ⟨1818,1817,141245,142027⟩,
  ⟨1819,1816,141244,143600⟩,
  ⟨1820,1766,102593,145164⟩,
  ⟨1821,1818,144382,146747⟩,
  ⟨1822,1820,146746,148329⟩,
  ⟨1823,1822,149127,149908⟩,
  ⟨1824,1820,148327,151484⟩,
  ⟨1825,1823,151484,153068⟩,
  ⟨1826,1807,139609,154659⟩]

private def points018 : List (ℕ × ℕ) := [(0,0),(7012,6074),(7876,6816),(7880,6820),(9611,8318),(11342,9811),(13073,11304),(13075,11306),(13941,12054),(14768,12778),(14808,12812),(15674,13555),(16543,14313),(18278,15806),(19145,16561),(19146,16562),(20013,17323),(20015,17324),(20877,18073),(21752,18831),(22615,19575),(23491,20344),(25230,21841),(26094,22592),(26963,23350),(26971,23356),(28712,24863),(29538,25591),(30455,26382),(31323,27142),(32198,27899),(33055,28633),(33902,29363),(33943,29401),(35686,30918),(35688,30920),(36551,31666),(36561,31674),(37433,32439),(37435,32441),(39182,33951),(40931,35470),(41799,36224),(42680,36979),(44431,38515),(46182,40028),(47935,41537),(49688,43038),(51430,44548),(51441,44558),(51443,44560),(52320,45309),(53198,46078),(54947,47597),(54954,47604),(54955,47605),(55832,48350),(56712,49105),(58471,50622),(59322,51372),(60230,52155),(61104,52920),(61109,52925),(61991,53712),(63752,55221),(65515,56745),(66395,57501),(67278,58265),(69043,59802),(69925,60560),(70808,61312),(72573,62846),(72575,62848),(73452,63603),(73458,63609),(74342,64384),(76110,65916),(76111,65917),(77880,67445),(79650,68978),(79651,68979),(80530,69751),(80535,69755),(81422,70517),(82293,71277),(82307,71291),(83195,72062),(84968,73603),(86743,75135),(87615,75885),(87630,75898),(88500,76644),(88518,76659),(89406,77433),(90295,78191),(91180,78972),(92060,79738),(92072,79749),(93790,81244),(93826,81275),(93851,81295),(95630,82821),(97411,84362),(99168,85884),(99174,85890),(99192,85907),(100973,87451),(100974,87451),(100975,87452),(101830,88203),(102758,89002),(104543,90542),(106328,92078),(108115,93626),(109902,95171),(110793,95944),(111691,96708),(113480,98247),(115253,99785),(115271,99803),(117062,101348),(117955,102120),(117957,102122),(118490,102593),(118855,102902),(120648,104446),(122442,106006),(122443,106007),(124220,107543),(124238,107561),(125135,108343),(126035,109114),(127832,110673),(128731,111455),(129630,112223),(129631,112224),(131430,113772),(133181,115305),(133231,115350),(135032,116908),(135905,117664),(135930,117688),(136834,118469),(136835,118470),(138630,120032),(138638,120040),(140442,121607),(140443,121608),(142248,123156),(143148,123943),(144055,124730),(145862,126287),(147653,127849),(147671,127865),(149480,129428),(150384,130203),(151291,130992),(153102,132568),(154914,134139),(154915,134140),(156728,135702),(158543,137286),(159450,138074),(160358,138855),(161221,139609),(161266,139650),(162175,140452),(163082,141244),(163083,141245),(163992,142027),(165811,143600),(166719,144382),(167630,145164),(169450,146746),(169451,146747),(171270,148327),(171272,148329),(172183,149127),(173095,149908),(174918,151484),(176743,153068),(178568,154659)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check018 :
    PLift (groupData 1488570 178568 1731 1826 g018 points018) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts018 :
    compareNamed primeRoster 19 18 1488570 178568 points018 := by
  decide +kernel

private theorem cover018 : covers 1731 1826 :=
  @groupChecked primeRoster 5000 18 1488570 178568 1731 1826 g018 points018
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check018.down counts018

private def g019 : List Row :=
  [⟨1827,1786,0,32485⟩,
  ⟨1828,1826,32484,34055⟩,
  ⟨1829,1827,34055,35643⟩,
  ⟨1830,1824,32481,37232⟩,
  ⟨1831,1826,34841,38826⟩,
  ⟨1832,1819,30079,40420⟩,
  ⟨1833,1828,38020,42034⟩,
  ⟨1834,1833,42826,43636⟩,
  ⟨1835,1832,42825,45199⟩,
  ⟨1836,1826,38814,46781⟩,
  ⟨1837,1833,45197,48384⟩,
  ⟨1838,1828,42022,49963⟩,
  ⟨1839,1831,45193,51566⟩,
  ⟨1840,1832,46774,53157⟩,
  ⟨1841,1837,51565,54748⟩,
  ⟨1842,1841,55540,56352⟩,
  ⟨1843,1839,54747,57942⟩,
  ⟨1844,1837,53945,59540⟩,
  ⟨1845,1842,58732,61127⟩,
  ⟨1846,1843,60336,62732⟩,
  ⟨1847,1846,63527,64320⟩,
  ⟨1848,1844,62730,65917⟩,
  ⟨1849,1837,57925,67526⟩,
  ⟨1850,1843,63521,69133⟩,
  ⟨1851,1847,67525,70736⟩,
  ⟨1852,1847,68326,72337⟩,
  ⟨1853,1851,72337,73939⟩,
  ⟨1854,1853,74752,75540⟩,
  ⟨1855,1844,68315,77145⟩,
  ⟨1856,1854,77144,78743⟩,
  ⟨1857,1856,79548,80364⟩,
  ⟨1858,1854,78741,81966⟩,
  ⟨1859,1831,61047,83582⟩,
  ⟨1860,1858,83581,85202⟩,
  ⟨1861,1845,73912,86827⟩,
  ⟨1862,1860,86826,88447⟩,
  ⟨1863,1835,67444,90063⟩,
  ⟨1864,1863,90877,91678⟩,
  ⟨1865,1863,91678,93316⟩,
  ⟨1866,1861,90875,94939⟩,
  ⟨1867,1855,86812,96575⟩,
  ⟨1868,1866,96574,98203⟩,
  ⟨1869,1867,98203,99815⟩,
  ⟨1870,1864,96572,101439⟩,
  ⟨1871,1848,84332,103072⟩,
  ⟨1872,1871,103893,104690⟩,
  ⟨1873,1865,99808,106323⟩,
  ⟨1874,1868,103067,107946⟩,
  ⟨1875,1856,94089,109563⟩,
  ⟨1876,1871,107133,111206⟩,
  ⟨1877,1873,109562,112837⟩,
  ⟨1878,1873,110384,114486⟩,
  ⟨1879,1874,112010,116121⟩,
  ⟨1880,1867,107117,117740⟩,
  ⟨1881,1879,117740,119370⟩,
  ⟨1882,1878,117739,121016⟩,
  ⟨1883,1880,120198,122656⟩,
  ⟨1884,1880,121015,124284⟩,
  ⟨1885,1877,119364,125927⟩,
  ⟨1886,1885,126743,127555⟩,
  ⟨1887,1885,127555,129191⟩,
  ⟨1888,1881,125103,130834⟩,
  ⟨1889,1881,125921,132456⟩,
  ⟨1890,1885,130017,134095⟩,
  ⟨1891,1888,133274,135752⟩,
  ⟨1892,1879,126726,137397⟩,
  ⟨1893,1890,136571,139038⟩,
  ⟨1894,1893,139858,140674⟩,
  ⟨1895,1894,141494,142315⟩,
  ⟨1896,1889,138217,143972⟩,
  ⟨1897,1893,142314,145605⟩,
  ⟨1898,1895,144788,147246⟩,
  ⟨1899,1893,143968,148892⟩,
  ⟨1900,1895,146426,150517⟩,
  ⟨1901,1864,121691,152157⟩,
  ⟨1902,1859,118346,153802⟩,
  ⟨1903,1900,152984,155456⟩,
  ⟨1904,1900,153800,157087⟩,
  ⟨1905,1890,146408,158745⟩,
  ⟨1906,1903,157913,160389⟩,
  ⟨1907,1900,156263,162051⟩,
  ⟨1908,1892,150490,163715⟩,
  ⟨1909,1906,162881,165372⟩,
  ⟨1910,1905,162879,167037⟩,
  ⟨1911,1909,167037,168721⟩,
  ⟨1912,1902,162039,170382⟩,
  ⟨1913,1907,167033,172029⟩,
  ⟨1914,1901,162863,173695⟩,
  ⟨1915,1914,174524,175355⟩,
  ⟨1916,1911,172870,177017⟩,
  ⟨1917,1906,169540,178675⟩,
  ⟨1918,1915,177837,180317⟩,
  ⟨1919,1916,179497,181987⟩,
  ⟨1920,1916,180315,183656⟩,
  ⟨1921,1916,181139,185325⟩,
  ⟨1922,1916,181982,186991⟩]

private def points019 : List (ℕ × ℕ) := [(0,0),(34693,30079),(37449,32481),(37453,32484),(37454,32485),(39281,34055),(40192,34841),(41110,35643),(42939,37232),(43851,38020),(44757,38814),(44770,38826),(46601,40420),(48421,42022),(48434,42034),(49349,42825),(49350,42826),(50267,43636),(52094,45193),(52100,45197),(52102,45199),(53929,46774),(53937,46781),(55774,48384),(57611,49963),(59448,51565),(59450,51566),(61289,53157),(62203,53945),(63128,54747),(63130,54748),(64050,55540),(64971,56352),(66796,57925),(66814,57942),(67734,58732),(68657,59540),(69578,60336),(70404,61047),(70502,61127),(72345,62730),(72347,62732),(73264,63521),(73270,63527),(74194,64320),(76041,65917),(77792,67444),(77888,67525),(77890,67526),(78799,68315),(78811,68326),(79739,69133),(81590,70736),(83441,72337),(85262,73912),(85294,73939),(86220,74752),(87147,75540),(89001,77144),(89002,77145),(90855,78741),(90857,78743),(91785,79548),(92714,80364),(94571,81966),(96429,83581),(96430,83582),(97293,84332),(98289,85202),(100132,86812),(100149,86826),(100150,86827),(102011,88447),(103874,90063),(104802,90875),(104805,90877),(105737,91678),(107602,93316),(108489,94089),(109467,94939),(111329,96572),(111333,96574),(111334,96575),(113201,98203),(115062,99808),(115070,99815),(116939,101439),(118805,103067),(118810,103072),(119745,103893),(120681,104690),(122554,106323),(123469,107117),(123487,107133),(124427,107946),(126300,109562),(126302,109563),(127236,110384),(128177,111206),(129112,112010),(130054,112837),(131931,114486),(133810,116121),(135687,117739),(135689,117740),(136398,118346),(137562,119364),(137570,119370),(138509,120198),(139449,121015),(139451,121016),(140221,121691),(141334,122656),(143217,124284),(144153,125103),(145094,125921),(145102,125927),(146023,126726),(146044,126743),(146987,127555),(148874,129191),(149814,130017),(150761,130834),(152650,132456),(153593,133274),(154539,134095),(156430,135752),(157374,136571),(158321,137397),(159261,138217),(160214,139038),(161160,139858),(162107,140674),(163054,141494),(164000,142314),(164002,142315),(165893,143968),(165897,143972),(166844,144788),(167794,145605),(168714,146408),(168739,146426),(169691,147246),(171590,148892),(173457,150490),(173489,150517),(175390,152157),(176339,152984),(177289,153800),(177291,153802),(179194,155456),(180139,156263),(181097,157087),(182048,157913),(183002,158745),(184907,160389),(186801,162039),(186814,162051),(187746,162863),(187764,162879),(187766,162881),(188721,163715),(190630,165372),(192535,167033),(192539,167037),(194450,168721),(195390,169540),(196361,170382),(198274,172029),(199227,172870),(200187,173695),(201144,174524),(202102,175355),(204017,177017),(204974,177837),(205934,178675),(206891,179497),(207849,180315),(207851,180317),(208807,181139),(209765,181982),(209770,181987),(211689,183656),(213610,185325),(215531,186991)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check019 :
    PLift (groupData 1631511 215531 1827 1922 g019 points019) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts019 :
    compareNamed primeRoster 19 18 1631511 215531 points019 := by
  decide +kernel

private theorem cover019 : covers 1827 1922 :=
  @groupChecked primeRoster 5000 18 1631511 215531 1827 1922 g019 points019
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check019.down counts019

private def g020 : List Row :=
  [⟨1923,1913,0,8338⟩,
  ⟨1924,1923,9165,10000⟩,
  ⟨1925,1923,10000,11668⟩,
  ⟨1926,1920,8335,13344⟩,
  ⟨1927,1920,9161,15019⟩,
  ⟨1928,1926,15018,16695⟩,
  ⟨1929,1927,16695,18361⟩,
  ⟨1930,1928,18360,20033⟩,
  ⟨1931,1929,20033,21693⟩,
  ⟨1932,1930,21692,23353⟩,
  ⟨1933,1909,4956,25033⟩,
  ⟨1934,1931,24200,26718⟩,
  ⟨1935,1928,22516,28406⟩,
  ⟨1936,1923,19178,30099⟩,
  ⟨1937,1920,17496,31758⟩,
  ⟨1938,1936,31757,33438⟩,
  ⟨1939,1918,17480,35127⟩,
  ⟨1940,1937,34277,36838⟩,
  ⟨1941,1939,36838,38522⟩,
  ⟨1942,1938,36836,40211⟩,
  ⟨1943,1936,35980,41900⟩,
  ⟨1944,1928,30072,43585⟩,
  ⟨1945,1923,26666,45270⟩,
  ⟨1946,1939,41058,46950⟩,
  ⟨1947,1944,46112,48654⟩,
  ⟨1948,1933,37656,50359⟩,
  ⟨1949,1947,50359,52037⟩,
  ⟨1950,1945,49496,53730⟩,
  ⟨1951,1946,51198,55415⟩,
  ⟨1952,1942,48643,57114⟩,
  ⟨1953,1948,54571,58811⟩,
  ⟨1954,1943,51186,60482⟩,
  ⟨1955,1954,61333,62174⟩,
  ⟨1956,1955,63014,63861⟩,
  ⟨1957,1955,63861,65567⟩,
  ⟨1958,1946,57100,67269⟩,
  ⟨1959,1946,57939,68976⟩,
  ⟨1960,1954,65563,70670⟩,
  ⟨1961,1956,68123,72367⟩,
  ⟨1962,1961,73220,74064⟩,
  ⟨1963,1958,71516,75783⟩,
  ⟨1964,1961,74924,77487⟩,
  ⟨1965,1962,76633,79192⟩,
  ⟨1966,1963,78330,80896⟩,
  ⟨1967,1953,70650,82608⟩,
  ⟨1968,1962,79188,84331⟩,
  ⟨1969,1965,82606,86041⟩,
  ⟨1970,1966,84329,87748⟩,
  ⟨1971,1928,52680,89466⟩,
  ⟨1972,1967,86894,91171⟩,
  ⟨1973,1965,86035,92878⟩,
  ⟨1974,1973,93711,94571⟩,
  ⟨1975,1967,89460,96297⟩,
  ⟨1976,1973,95429,98026⟩,
  ⟨1977,1975,98026,99732⟩,
  ⟨1978,1970,94563,101444⟩,
  ⟨1979,1973,98022,103162⟩,
  ⟨1980,1969,95418,104881⟩,
  ⟨1981,1979,104881,106599⟩,
  ⟨1982,1981,107460,108314⟩,
  ⟨1983,1978,105745,110030⟩,
  ⟨1984,1978,106595,111760⟩,
  ⟨1985,1977,106592,113483⟩,
  ⟨1986,1984,113482,115197⟩,
  ⟨1987,1985,115197,116921⟩,
  ⟨1988,1981,112614,118635⟩,
  ⟨1989,1988,119513,120377⟩,
  ⟨1990,1986,118633,122110⟩,
  ⟨1991,1985,118631,123853⟩,
  ⟨1992,1975,110865,125590⟩,
  ⟨1993,1989,123851,127316⟩,
  ⟨1994,1988,123848,129043⟩,
  ⟨1995,1982,119495,130770⟩,
  ⟨1996,1978,116886,132511⟩,
  ⟨1997,1991,129040,134258⟩,
  ⟨1998,1996,134257,136004⟩,
  ⟨1999,1997,136004,137732⟩,
  ⟨2000,1983,124690,139483⟩,
  ⟨2001,1996,136857,141217⟩,
  ⟨2002,1995,136855,142951⟩,
  ⟨2003,2002,143826,144689⟩,
  ⟨2004,2003,145565,146428⟩,
  ⟨2005,2003,146428,148176⟩,
  ⟨2006,1986,132468,149907⟩,
  ⟨2007,1997,142942,151650⟩,
  ⟨2008,2003,149045,153392⟩,
  ⟨2009,2008,154260,155126⟩,
  ⟨2010,2001,149040,156862⟩,
  ⟨2011,2008,155992,158600⟩,
  ⟨2012,1996,146400,160335⟩,
  ⟨2013,2012,161207,162087⟩,
  ⟨2014,2011,161206,163844⟩,
  ⟨2015,2011,162085,165594⟩,
  ⟨2016,2013,164715,167342⟩,
  ⟨2017,2016,168225,169103⟩,
  ⟨2018,2013,166467,170859⟩]

private def points020 : List (ℕ × ℕ) := [(0,0),(5699,4956),(9610,8335),(9615,8338),(10570,9161),(10576,9165),(11538,10000),(13463,11668),(15388,13344),(17314,15018),(17315,15019),(19242,16695),(20151,17480),(20170,17496),(21170,18360),(21171,18361),(22114,19178),(23100,20033),(25030,21692),(25031,21693),(25990,22516),(26962,23353),(27927,24200),(28895,25033),(30768,26666),(30828,26718),(32763,28406),(34666,30072),(34698,30099),(36634,31757),(36635,31758),(38572,33438),(39540,34277),(40511,35127),(41474,35980),(42448,36836),(42450,36838),(43392,37656),(44391,38522),(46332,40211),(47297,41058),(48275,41900),(50218,43585),(52163,45270),(53134,46112),(54108,46950),(56042,48643),(56055,48654),(57025,49496),(58002,50359),(58961,51186),(58973,51198),(59951,52037),(60694,52680),(61900,53730),(62872,54571),(63851,55415),(65784,57100),(65802,57114),(66757,57939),(67755,58811),(69708,60482),(70685,61333),(71663,62174),(72640,63014),(73618,63861),(75570,65563),(75575,65567),(77532,67269),(78508,68123),(79491,68976),(81426,70650),(81450,70670),(82427,71516),(83411,72367),(84391,73220),(85372,74064),(86352,74924),(87335,75783),(88315,76633),(89298,77487),(90279,78330),(91258,79188),(91263,79192),(93228,80896),(95193,82606),(95195,82608),(97160,84329),(97162,84331),(99123,86035),(99131,86041),(100112,86894),(101100,87748),(103063,89460),(103071,89466),(105042,91171),(107015,92878),(108001,93711),(108980,94563),(108988,94571),(109960,95418),(109974,95429),(110963,96297),(112934,98022),(112938,98026),(114915,99732),(116892,101444),(118871,103162),(120850,104881),(121837,105745),(122823,106592),(122826,106595),(122831,106599),(123821,107460),(124812,108314),(126795,110030),(127750,110865),(128778,111760),(129764,112614),(130762,113482),(130763,113483),(132748,115197),(134694,116886),(134735,116921),(136718,118631),(136720,118633),(136722,118635),(137695,119495),(137716,119513),(138711,120377),(140700,122110),(142686,123848),(142689,123851),(142691,123853),(143650,124690),(144682,125590),(146675,127316),(148664,129040),(148668,129043),(150663,130770),(152608,132468),(152658,132511),(154654,134257),(154655,134258),(156652,136004),(157645,136855),(157648,136857),(158651,137732),(160650,139483),(162651,141217),(164640,142942),(164652,142951),(165653,143826),(166655,144689),(167656,145565),(168626,146400),(168658,146428),(170663,148176),(171655,149040),(171662,149045),(172668,149907),(174675,151650),(176682,153392),(177686,154260),(178691,155126),(179694,155992),(180700,156862),(182711,158600),(184722,160335),(185727,161206),(185728,161207),(186733,162085),(186735,162087),(188748,163844),(189754,164715),(190763,165594),(191767,166467),(192778,167342),(193786,168225),(194795,169103),(196812,170859)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check020 :
    PLift (groupData 1839350 196812 1923 2018 g020 points020) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts020 :
    compareNamed primeRoster 19 18 1839350 196812 points020 := by
  decide +kernel

private theorem cover020 : covers 1923 2018 :=
  @groupChecked primeRoster 5000 18 1839350 196812 1923 2018 g020 points020
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check020.down counts020

private def g021 : List Row :=
  [⟨2019,2017,0,1742⟩,
  ⟨2020,2019,2614,3485⟩,
  ⟨2021,2020,4371,5251⟩,
  ⟨2022,2019,4370,6994⟩,
  ⟨2023,2015,1735,8758⟩,
  ⟨2024,2022,8757,10510⟩,
  ⟨2025,2024,11385,12271⟩,
  ⟨2026,2023,11384,14040⟩,
  ⟨2027,2024,13160,15792⟩,
  ⟨2028,2023,13158,17545⟩,
  ⟨2029,2028,18438,19316⟩,
  ⟨2030,2016,8735,21098⟩,
  ⟨2031,2030,21986,22863⟩,
  ⟨2032,2018,12249,24626⟩,
  ⟨2033,2005,1657,26410⟩,
  ⟨2034,2031,25515,28187⟩,
  ⟨2035,2032,27298,29954⟩,
  ⟨2036,2035,30839,31718⟩,
  ⟨2037,2034,30838,33493⟩,
  ⟨2038,2033,30836,35258⟩,
  ⟨2039,2037,35258,37020⟩,
  ⟨2040,2038,37019,38788⟩,
  ⟨2041,2036,36138,40540⟩,
  ⟨2042,2032,33483,42320⟩,
  ⟨2043,2042,43214,44105⟩,
  ⟨2044,2041,43213,45890⟩,
  ⟨2045,2042,44993,47660⟩,
  ⟨2046,2040,44101,49418⟩,
  ⟨2047,2038,43207,51190⟩,
  ⟨2048,2037,43204,52975⟩,
  ⟨2049,2041,47654,54759⟩,
  ⟨2050,2048,54758,56531⟩,
  ⟨2051,2049,56531,58305⟩,
  ⟨2052,2046,54754,60089⟩,
  ⟨2053,2042,52067,61878⟩,
  ⟨2054,2045,55639,63665⟩,
  ⟨2055,2054,64557,65446⟩,
  ⟨2056,2050,61874,67233⟩,
  ⟨2057,2046,59188,69031⟩,
  ⟨2058,2056,69030,70817⟩,
  ⟨2059,2054,68125,72626⟩,
  ⟨2060,2057,71729,74400⟩,
  ⟨2061,2053,69024,76205⟩,
  ⟨2062,2058,74399,77982⟩,
  ⟨2063,2058,75295,79770⟩,
  ⟨2064,2060,77980,81567⟩,
  ⟨2065,2054,73499,83358⟩,
  ⟨2066,2056,76193,85162⟩,
  ⟨2067,2065,85162,86960⟩,
  ⟨2068,2062,83354,88761⟩,
  ⟨2069,2068,89662,90558⟩,
  ⟨2070,2068,90557,92370⟩,
  ⟨2071,2068,91455,94179⟩,
  ⟨2072,2063,87844,95975⟩,
  ⟨2073,2072,96883,97789⟩,
  ⟨2074,2072,97788,99581⟩,
  ⟨2075,2072,98690,101382⟩,
  ⟨2076,2068,95968,103185⟩,
  ⟨2077,2070,98687,104980⟩,
  ⟨2078,2076,104979,106794⟩,
  ⟨2079,2072,102275,108611⟩,
  ⟨2080,2079,109522,110425⟩,
  ⟨2081,2078,109521,112224⟩,
  ⟨2082,2073,105893,114039⟩,
  ⟨2083,2081,114039,115845⟩,
  ⟨2084,2083,116746,117657⟩,
  ⟨2085,2084,118565,119481⟩,
  ⟨2086,2066,103141,121294⟩,
  ⟨2087,2084,120379,123109⟩,
  ⟨2088,2086,123108,124933⟩,
  ⟨2089,2083,121290,126746⟩,
  ⟨2090,2078,117640,128573⟩,
  ⟨2091,2089,128573,130381⟩,
  ⟨2092,2086,126741,132190⟩,
  ⟨2093,2085,126738,134007⟩,
  ⟨2094,2086,128565,135824⟩,
  ⟨2095,2094,136735,137656⟩,
  ⟨2096,2086,130372,139471⟩,
  ⟨2097,2090,134908,141301⟩,
  ⟨2098,2097,142227,143137⟩,
  ⟨2099,2098,144041,144952⟩,
  ⟨2100,2098,144951,146794⟩,
  ⟨2101,2096,144039,148601⟩,
  ⟨2102,2097,145874,150428⟩,
  ⟨2103,2102,151342,152243⟩,
  ⟨2104,2103,153152,154067⟩,
  ⟨2105,2104,154967,155881⟩,
  ⟨2106,2105,156801,157723⟩,
  ⟨2107,2105,157723,159537⟩,
  ⟨2108,2104,157721,161350⟩,
  ⟨2109,2107,161350,163188⟩,
  ⟨2110,2109,164100,165018⟩,
  ⟨2111,2110,165932,166857⟩,
  ⟨2112,2108,165016,168683⟩,
  ⟨2113,2112,169599,170525⟩,
  ⟨2114,2099,158612,172354⟩]

private def points021 : List (ℕ × ℕ) := [(0,0),(1921,1657),(2011,1735),(2019,1742),(3028,2614),(4038,3485),(5047,4370),(5048,4371),(6059,5251),(8080,6994),(10078,8735),(10102,8757),(10103,8758),(12126,10510),(13137,11384),(13138,11385),(14126,12249),(14151,12271),(15160,13158),(15162,13160),(16176,14040),(18203,15792),(20230,17545),(21244,18438),(22259,19316),(24288,21098),(25303,21986),(26319,22863),(28350,24626),(29365,25515),(30383,26410),(31398,27298),(32416,28187),(34451,29954),(35465,30836),(35467,30838),(35468,30839),(36486,31718),(38510,33483),(38523,33493),(40560,35258),(41576,36138),(42598,37019),(42599,37020),(44638,38788),(46679,40540),(48720,42320),(49726,43204),(49731,43207),(49740,43213),(49741,43214),(50758,44101),(50763,44105),(51783,44993),(52806,45890),(54843,47654),(54851,47660),(56896,49418),(58943,51190),(59951,52067),(60990,52975),(63034,54754),(63038,54758),(63039,54759),(64053,55639),(65088,56531),(67139,58305),(68149,59188),(69190,60089),(71238,61874),(71243,61878),(73296,63665),(74323,64557),(75351,65446),(77406,67233),(78431,68125),(79455,69024),(79462,69030),(79463,69031),(81520,70817),(82548,71729),(83579,72626),(84593,73499),(85636,74399),(85638,74400),(86665,75295),(87686,76193),(87699,76205),(89758,77980),(89760,77982),(91823,79770),(93886,81567),(95946,83354),(95951,83358),(98016,85162),(100083,86960),(101106,87844),(102150,88761),(103184,89662),(104218,90557),(104219,90558),(105252,91455),(106288,92370),(108359,94179),(110422,95968),(110430,95975),(111466,96883),(112502,97788),(112503,97789),(113533,98687),(113538,98690),(114576,99581),(116651,101382),(117682,102275),(118676,103141),(118726,103185),(120802,104979),(120803,104980),(121831,105893),(122880,106794),(124959,108611),(125997,109521),(125998,109522),(127038,110425),(129119,112224),(131200,114039),(133283,115845),(134324,116746),(135348,117640),(135366,117657),(136408,118565),(137451,119481),(138492,120379),(139532,121290),(139536,121294),(141622,123108),(141623,123109),(143710,124933),(145791,126738),(145794,126741),(145799,126746),(147880,128565),(147888,128573),(149966,130372),(149979,130381),(152070,132190),(154163,134007),(155203,134908),(156256,135824),(157303,136735),(158351,137656),(160446,139471),(162543,141301),(163591,142227),(164640,143137),(165686,144039),(165689,144041),(166738,144951),(166739,144952),(167785,145874),(168838,146794),(170939,148601),(173040,150428),(174091,151342),(175143,152243),(176194,153152),(177246,154067),(178298,154967),(179351,155881),(180403,156801),(181454,157721),(181456,157723),(182481,158612),(183563,159537),(185670,161350),(187779,163188),(188833,164100),(189886,165016),(189888,165018),(190943,165932),(191999,166857),(194110,168683),(195166,169599),(196223,170525),(198336,172354)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check021 :
    PLift (groupData 2036162 198336 2019 2114 g021 points021) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts021 :
    compareNamed primeRoster 19 18 2036162 198336 points021 := by
  decide +kernel

private theorem cover021 : covers 2019 2114 :=
  @groupChecked primeRoster 5000 18 2036162 198336 2019 2114 g021 points021
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check021.down counts021

private def g022 : List Row :=
  [⟨2115,2096,979,18415⟩,
  ⟨2116,2114,18414,20247⟩,
  ⟨2117,2112,17484,22086⟩,
  ⟨2118,2113,19330,23916⟩,
  ⟨2119,2113,20244,25748⟩,
  ⟨2120,2090,0,27599⟩,
  ⟨2121,2112,21159,29445⟩,
  ⟨2122,2117,26670,31292⟩,
  ⟨2123,2122,32203,33126⟩,
  ⟨2124,2123,34058,34983⟩,
  ⟨2125,2123,34983,36845⟩,
  ⟨2126,2109,22981,38695⟩,
  ⟨2127,2125,38695,40551⟩,
  ⟨2128,2126,40550,42401⟩,
  ⟨2129,2127,42401,44259⟩,
  ⟨2130,2124,40546,46115⟩,
  ⟨2131,2125,42397,47967⟩,
  ⟨2132,2130,47966,49827⟩,
  ⟨2133,2131,49827,51689⟩,
  ⟨2134,2126,46108,53527⟩,
  ⟨2135,2133,53527,55385⟩,
  ⟨2136,2134,55384,57251⟩,
  ⟨2137,2133,55383,59094⟩,
  ⟨2138,2128,51678,60945⟩,
  ⟨2139,2137,60945,62815⟩,
  ⟨2140,2138,62814,64671⟩,
  ⟨2141,2139,64671,66529⟩,
  ⟨2142,2136,62810,68397⟩,
  ⟨2143,2136,63740,70258⟩,
  ⟨2144,2141,69332,72109⟩,
  ⟨2145,2142,71181,73990⟩,
  ⟨2146,2145,74923,75857⟩,
  ⟨2147,2141,72106,77708⟩,
  ⟨2148,2145,76790,79573⟩,
  ⟨2149,2138,71169,81458⟩,
  ⟨2150,2143,76785,83327⟩,
  ⟨2151,2145,79569,85183⟩,
  ⟨2152,2151,86133,87060⟩,
  ⟨2153,2133,70211,88938⟩,
  ⟨2154,2148,85179,90812⟩,
  ⟨2155,2151,88936,92689⟩,
  ⟨2156,2155,93631,94558⟩,
  ⟨2157,2154,93631,96448⟩,
  ⟨2158,2142,83300,98343⟩,
  ⟨2159,2156,97380,100218⟩,
  ⟨2160,2156,98341,102092⟩,
  ⟨2161,2158,101155,103964⟩,
  ⟨2162,2160,103963,105842⟩,
  ⟨2163,2161,105842,107724⟩,
  ⟨2164,2163,108657,109590⟩,
  ⟨2165,2159,105839,111453⟩,
  ⟨2166,2155,103022,113352⟩,
  ⟨2167,2165,113352,115236⟩,
  ⟨2168,2163,112395,117114⟩,
  ⟨2169,2166,116162,118995⟩,
  ⟨2170,2156,107704,120891⟩,
  ⟨2171,2164,116158,122786⟩,
  ⟨2172,2169,121841,124666⟩,
  ⟨2173,2162,116149,126552⟩,
  ⟨2174,2173,127509,128447⟩,
  ⟨2175,2174,129392,130349⟩,
  ⟨2176,2174,130348,132217⟩,
  ⟨2177,2173,130347,134108⟩,
  ⟨2178,2173,131276,136012⟩,
  ⟨2179,2172,131273,137909⟩,
  ⟨2180,2175,135065,139814⟩,
  ⟨2181,2174,135062,141719⟩,
  ⟨2182,2175,136956,143610⟩,
  ⟨2183,2176,138855,145513⟩,
  ⟨2184,2158,122711,147412⟩,
  ⟨2185,2178,142661,149332⟩,
  ⟨2186,2159,125533,151223⟩,
  ⟨2187,2180,146450,153122⟩,
  ⟨2188,2186,153121,155032⟩,
  ⟨2189,2185,153120,156951⟩,
  ⟨2190,2186,155030,158853⟩,
  ⟨2191,2184,154079,160757⟩,
  ⟨2192,2186,156946,162645⟩,
  ⟨2193,2185,156943,164562⟩,
  ⟨2194,2188,160752,166471⟩,
  ⟨2195,2191,164560,168381⟩,
  ⟨2196,2190,164557,170282⟩,
  ⟨2197,2195,170282,172216⟩,
  ⟨2198,2197,173171,174133⟩,
  ⟨2199,2196,173170,176036⟩,
  ⟨2200,2181,159767,177926⟩,
  ⟨2201,2195,174129,179855⟩,
  ⟨2202,2198,177925,181772⟩,
  ⟨2203,2196,176964,183678⟩,
  ⟨2204,2197,178885,185608⟩,
  ⟨2205,2196,178882,187522⟩,
  ⟨2206,2200,183674,189439⟩,
  ⟨2207,2206,190387,191352⟩,
  ⟨2208,2207,192304,193271⟩,
  ⟨2209,2204,190384,195206⟩,
  ⟨2210,2209,196153,197119⟩]

private def points022 : List (ℕ × ℕ) := [(0,0),(1120,979),(20152,17484),(21212,18414),(21213,18415),(22267,19330),(23324,20244),(23328,20247),(24376,21159),(25445,22086),(26467,22981),(27562,23916),(29681,25748),(30737,26670),(31800,27599),(33921,29445),(36042,31292),(37103,32203),(38165,33126),(39226,34058),(40288,34983),(42413,36845),(44538,38695),(46660,40546),(46664,40550),(46665,40551),(48788,42397),(48792,42401),(50921,44259),(53042,46108),(53050,46115),(55180,47966),(55181,47967),(57312,49827),(59432,51678),(59445,51689),(61578,53527),(63711,55383),(63712,55384),(63713,55385),(65848,57251),(67985,59094),(70122,60945),(72256,62810),(72260,62814),(72261,62815),(73324,63740),(74400,64671),(76541,66529),(78682,68397),(79752,69332),(80775,70211),(80825,70258),(81881,71169),(81895,71181),(82964,72106),(82968,72109),(85113,73990),(86185,74923),(87258,75857),(88325,76785),(88330,76790),(89405,77708),(91548,79569),(91552,79573),(93701,81458),(95818,83300),(95850,83327),(97996,85179),(98001,85183),(99076,86133),(100152,87060),(102303,88936),(102305,88938),(104458,90812),(106613,92689),(107689,93631),(107690,93631),(108768,94558),(110925,96448),(112002,97380),(113080,98341),(113082,98343),(115241,100218),(116319,101155),(117400,102092),(118465,103022),(119560,103963),(119561,103964),(121718,105839),(121722,105842),(123860,107704),(123885,107724),(124966,108657),(126048,109590),(128213,111453),(129292,112395),(130378,113352),(132545,115236),(133613,116149),(133622,116158),(133627,116162),(134712,117114),(136881,118995),(139050,120891),(140134,121841),(141136,122711),(141221,122786),(143392,124666),(144387,125533),(145565,126552),(146651,127509),(147738,128447),(148825,129392),(149911,130347),(149912,130348),(149913,130349),(150994,131273),(150997,131276),(152088,132217),(154265,134108),(155347,135062),(155350,135065),(156442,136012),(157525,136956),(158621,137909),(159704,138855),(160800,139814),(162981,141719),(164065,142661),(165162,143610),(167345,145513),(168430,146450),(169528,147412),(171713,149332),(173898,151223),(176083,153120),(176084,153121),(176085,153122),(177172,154079),(178270,155030),(178272,155032),(180453,156943),(180456,156946),(180461,156951),(182650,158853),(183700,159767),(184836,160752),(184841,160757),(187032,162645),(189220,164557),(189223,164560),(189225,164562),(191418,166471),(193613,168381),(195808,170282),(198005,172216),(199102,173170),(199103,173171),(200198,174129),(200202,174133),(202401,176036),(203494,176964),(204598,177925),(204600,177926),(205690,178882),(205694,178885),(206801,179855),(209002,181772),(211200,183674),(211205,183678),(213408,185608),(215613,187522),(217818,189439),(218918,190384),(218921,190387),(220025,191352),(221128,192304),(222232,193271),(224441,195206),(225545,196153),(226650,197119)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check022 :
    PLift (groupData 2215400 226650 2115 2210 g022 points022) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts022 :
    compareNamed primeRoster 19 18 2215400 226650 points022 := by
  decide +kernel

private theorem cover022 : covers 2115 2210 :=
  @groupChecked primeRoster 5000 18 2215400 226650 2115 2210 g022 points022
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check022.down counts022

private def g023 : List Row :=
  [⟨2211,2208,0,2884⟩,
  ⟨2212,2209,1920,4795⟩,
  ⟨2213,2210,3830,6707⟩,
  ⟨2214,2212,6706,8607⟩,
  ⟨2215,2210,5745,10556⟩,
  ⟨2216,2214,10555,12478⟩,
  ⟨2217,2214,11503,14410⟩,
  ⟨2218,2214,12476,16349⟩,
  ⟨2219,2216,15384,18270⟩,
  ⟨2220,2217,17306,20205⟩,
  ⟨2221,2219,20205,22133⟩,
  ⟨2222,2220,22132,24071⟩,
  ⟨2223,2219,22131,26006⟩,
  ⟨2224,2221,25035,27928⟩,
  ⟨2225,2203,8556,29868⟩,
  ⟨2226,2223,28904,31804⟩,
  ⟨2227,2218,25026,33747⟩,
  ⟨2228,2224,31802,35671⟩,
  ⟨2229,2225,33746,37597⟩,
  ⟨2230,2223,32760,39546⟩,
  ⟨2231,2225,35667,41483⟩,
  ⟨2232,2229,40521,43420⟩,
  ⟨2233,2230,42444,45355⟩,
  ⟨2234,2231,44392,47286⟩,
  ⟨2235,2230,44390,49239⟩,
  ⟨2236,2225,40511,51190⟩,
  ⟨2237,2235,51190,53134⟩,
  ⟨2238,2237,54123,55091⟩,
  ⟨2239,2237,55091,57047⟩,
  ⟨2240,2233,52156,58999⟩,
  ⟨2241,2240,59974,60944⟩,
  ⟨2242,2238,58997,62894⟩,
  ⟨2243,2241,62894,64844⟩,
  ⟨2244,2236,58992,66797⟩,
  ⟨2245,2238,61921,68760⟩,
  ⟨2246,2245,69739,70713⟩,
  ⟨2247,2243,68758,72681⟩,
  ⟨2248,2247,73664,74639⟩,
  ⟨2249,2246,73663,76580⟩,
  ⟨2250,2237,65807,78543⟩,
  ⟨2251,2244,73659,80507⟩,
  ⟨2252,2244,74633,82460⟩,
  ⟨2253,2252,83453,84429⟩,
  ⟨2254,2253,85412,86388⟩,
  ⟨2255,2251,84427,88344⟩,
  ⟨2256,2250,84424,90309⟩,
  ⟨2257,2247,82451,92265⟩,
  ⟨2258,2246,82446,94235⟩,
  ⟨2259,2257,94235,96213⟩,
  ⟨2260,2259,97193,98192⟩,
  ⟨2261,2255,94232,100152⟩,
  ⟨2262,2259,99168,102128⟩,
  ⟨2263,2230,71582,104105⟩,
  ⟨2264,2262,104104,106055⟩,
  ⟨2265,2259,102124,108036⟩,
  ⟨2266,2264,108035,109994⟩,
  ⟨2267,2264,109016,111974⟩,
  ⟨2268,2247,93213,113938⟩,
  ⟨2269,2268,114925,115921⟩,
  ⟨2270,2265,112946,117894⟩,
  ⟨2271,2264,112943,119883⟩,
  ⟨2272,2271,120867,121852⟩,
  ⟨2273,2248,99100,123836⟩,
  ⟨2274,2273,124831,125817⟩,
  ⟨2275,2272,124830,127794⟩,
  ⟨2276,2272,125815,129790⟩,
  ⟨2277,2274,128796,131779⟩,
  ⟨2278,2277,132762,133764⟩,
  ⟨2279,2278,134750,135751⟩,
  ⟨2280,2270,127781,137734⟩,
  ⟨2281,2277,135749,139710⟩,
  ⟨2282,2280,139709,141678⟩,
  ⟨2283,2278,138725,143682⟩,
  ⟨2284,2283,144667,145660⟩,
  ⟨2285,2282,144666,147645⟩,
  ⟨2286,2283,146654,149634⟩,
  ⟨2287,2272,136719,151629⟩,
  ⟨2288,2284,149632,153621⟩,
  ⟨2289,2279,145648,155610⟩,
  ⟨2290,2285,152626,157594⟩,
  ⟨2291,2276,144644,159584⟩,
  ⟨2292,2288,157592,161563⟩,
  ⟨2293,2291,161563,163579⟩,
  ⟨2294,2283,154616,165576⟩,
  ⟨2295,2285,157583,167571⟩,
  ⟨2296,2292,165574,169565⟩,
  ⟨2297,2287,161551,171565⟩,
  ⟨2298,2295,170558,173566⟩,
  ⟨2299,2297,173566,175588⟩,
  ⟨2300,2291,168565,177588⟩,
  ⟨2301,2298,176592,179577⟩,
  ⟨2302,2299,178580,181584⟩,
  ⟨2303,2293,173556,183584⟩,
  ⟨2304,2294,175577,185586⟩,
  ⟨2305,2298,180572,187609⟩,
  ⟨2306,2298,181577,189614⟩]

private def points023 : List (ℕ × ℕ) := [(0,0),(2210,1920),(3317,2884),(4421,3830),(5528,4795),(6631,5745),(7740,6706),(7741,6707),(9894,8556),(9954,8607),(12168,10555),(12169,10556),(13275,11503),(14382,12476),(14384,12478),(16601,14410),(17708,15384),(18818,16349),(19926,17306),(21037,18270),(23256,20205),(25475,22131),(25476,22132),(25477,22133),(27698,24071),(28799,25026),(28808,25035),(29921,26006),(32144,27928),(33255,28904),(34369,29868),(36592,31802),(36594,31804),(37701,32760),(38819,33746),(38821,33747),(41044,35667),(41048,35671),(43277,37597),(45506,39546),(46606,40511),(46620,40521),(47737,41483),(48851,42444),(49968,43420),(51081,44390),(51083,44392),(52201,45355),(54434,47286),(56669,49239),(58904,51190),(60016,52156),(61141,53134),(62259,54123),(63378,55091),(65617,57047),(67848,58992),(67854,58997),(67856,58999),(68976,59974),(70097,60944),(71211,61921),(72338,62894),(74581,64844),(75681,65807),(76824,66797),(79067,68758),(79069,68760),(80191,69739),(81314,70713),(82301,71582),(83561,72681),(84678,73659),(84683,73663),(84684,73664),(85800,74633),(85808,74639),(88057,76580),(90306,78543),(92557,80507),(94790,82446),(94796,82451),(94808,82460),(95934,83453),(97056,84424),(97059,84427),(97061,84429),(98187,85412),(99314,86388),(101569,88344),(103824,90309),(106081,92265),(107154,93213),(108334,94232),(108338,94235),(110597,96213),(111726,97193),(112856,98192),(113908,99100),(113985,99168),(115117,100152),(117374,102124),(117378,102128),(119640,104104),(119641,104105),(121904,106055),(124168,108035),(124169,108036),(125300,109016),(126434,109994),(128701,111974),(129828,112943),(129831,112946),(130968,113938),(132102,114925),(133237,115921),(135506,117894),(137777,119883),(138912,120867),(140048,121852),(142321,123836),(143456,124830),(143457,124831),(144592,125815),(144594,125817),(146856,127781),(146869,127794),(148005,128796),(149144,129790),(151421,131779),(152559,132762),(153698,133764),(154837,134750),(155975,135749),(155977,135751),(157088,136719),(158256,137734),(159393,138725),(160536,139709),(160537,139710),(162818,141678),(165101,143682),(166214,144644),(166241,144666),(166242,144667),(167372,145648),(167384,145660),(168525,146654),(169669,147645),(171952,149632),(171954,149634),(174241,151629),(175381,152626),(176528,153621),(177657,154616),(178817,155610),(181094,157583),(181104,157592),(181106,157594),(183397,159584),(185676,161551),(185688,161563),(187981,163579),(190272,165574),(190274,165576),(192569,167571),(193706,168565),(194864,169565),(196011,170558),(197161,171565),(199446,173556),(199458,173566),(201744,175577),(201757,175588),(202905,176592),(204056,177588),(205205,178580),(206357,179577),(207501,180572),(208650,181577),(208658,181584),(210961,183584),(213264,185586),(215569,187609),(217874,189614)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check023 :
    PLift (groupData 2440944 217874 2211 2306 g023 points023) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts023 :
    compareNamed primeRoster 19 18 2440944 217874 points023 := by
  decide +kernel

private theorem cover023 : covers 2211 2306 :=
  @groupChecked primeRoster 5000 18 2440944 217874 2211 2306 g023 points023
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check023.down counts023

private def g024 : List Row :=
  [⟨2307,2304,15132,18150⟩,
  ⟨2308,2307,19152,20155⟩,
  ⟨2309,2301,14119,22162⟩,
  ⟨2310,2306,20153,24166⟩,
  ⟨2311,2306,21158,26179⟩,
  ⟨2312,2284,0,28191⟩,
  ⟨2313,2309,26177,30210⟩,
  ⟨2314,2307,25168,32228⟩,
  ⟨2315,2284,3012,34244⟩,
  ⟨2316,2304,24148,36255⟩,
  ⟨2317,2303,24144,38274⟩,
  ⟨2318,2294,16066,40311⟩,
  ⟨2319,2316,39293,42309⟩,
  ⟨2320,2318,42308,44321⟩,
  ⟨2321,2314,39290,46345⟩,
  ⟨2322,2317,43317,48361⟩,
  ⟨2323,2317,44317,50399⟩,
  ⟨2324,2314,42297,52418⟩,
  ⟨2325,2322,51402,54457⟩,
  ⟨2326,2317,47340,56486⟩,
  ⟨2327,2320,51397,58503⟩,
  ⟨2328,2324,56484,60541⟩,
  ⟨2329,2320,53435,62555⟩,
  ⟨2330,2323,57485,64579⟩,
  ⟨2331,2311,46306,66615⟩,
  ⟨2332,2331,67637,68640⟩,
  ⟨2333,2332,69653,70681⟩,
  ⟨2334,2321,59496,72716⟩,
  ⟨2335,2334,73730,74731⟩,
  ⟨2336,2335,75754,76773⟩,
  ⟨2337,2330,71689,78800⟩,
  ⟨2338,2335,77784,80834⟩,
  ⟨2339,2329,72705,82889⟩,
  ⟨2340,2332,76765,84924⟩,
  ⟨2341,2313,58417,86974⟩,
  ⟨2342,2332,78788,89009⟩,
  ⟨2343,2342,90030,91053⟩,
  ⟨2344,2343,92078,93093⟩,
  ⟨2345,2338,87978,95135⟩,
  ⟨2346,2338,89003,97174⟩,
  ⟨2347,2343,95134,99211⟩,
  ⟨2348,2347,100241,101276⟩,
  ⟨2349,2342,96152,103313⟩,
  ⟨2350,2344,99207,105374⟩,
  ⟨2351,2339,95120,107437⟩,
  ⟨2352,2335,92049,109492⟩,
  ⟨2353,2338,96132,111513⟩,
  ⟨2354,2350,109490,113567⟩,
  ⟨2355,2343,103297,115638⟩,
  ⟨2356,2355,116671,117692⟩,
  ⟨2357,2356,118727,119757⟩,
  ⟨2358,2357,120785,121807⟩,
  ⟨2359,2358,122827,123868⟩,
  ⟨2360,2357,122826,125905⟩,
  ⟨2361,2359,125905,127955⟩,
  ⟨2362,2351,118714,130042⟩,
  ⟨2363,2362,131054,132087⟩,
  ⟨2364,2359,128987,134140⟩,
  ⟨2365,2349,119727,136210⟩,
  ⟨2366,2364,136209,138268⟩,
  ⟨2367,2365,138268,140328⟩,
  ⟨2368,2367,141370,142403⟩,
  ⟨2369,2363,138265,144453⟩,
  ⟨2370,2369,145492,146526⟩,
  ⟨2371,2367,144451,148600⟩,
  ⟨2372,2363,141363,150670⟩,
  ⟨2373,2371,150670,152730⟩,
  ⟨2374,2359,139265,154789⟩,
  ⟨2375,2374,155824,156873⟩,
  ⟨2376,2373,155823,158948⟩,
  ⟨2377,2376,159989,161029⟩,
  ⟨2378,2376,161028,163099⟩,
  ⟨2379,2376,162059,165179⟩,
  ⟨2380,2378,165178,167247⟩,
  ⟨2381,2377,165177,169338⟩,
  ⟨2382,2380,169337,171408⟩,
  ⟨2383,2382,172444,173487⟩,
  ⟨2384,2373,164129,175574⟩,
  ⟨2385,2384,176604,177648⟩,
  ⟨2386,2385,178687,179713⟩,
  ⟨2387,2380,174526,181784⟩,
  ⟨2388,2375,170358,183851⟩,
  ⟨2389,2355,150550,185936⟩,
  ⟨2390,2387,184888,188030⟩,
  ⟨2391,2386,184886,190095⟩,
  ⟨2392,2391,191124,192171⟩,
  ⟨2393,2389,190093,194262⟩,
  ⟨2394,2393,195301,196349⟩,
  ⟨2395,2384,186969,198443⟩,
  ⟨2396,2394,198442,200531⟩,
  ⟨2397,2381,185910,202619⟩,
  ⟨2398,2390,196341,204702⟩,
  ⟨2399,2398,205749,206786⟩,
  ⟨2400,2390,198433,208890⟩,
  ⟨2401,2384,193189,210989⟩,
  ⟨2402,2386,196319,213098⟩]

private def points024 : List (ℕ × ℕ) := [(0,0),(3426,3012),(16201,14119),(17360,15132),(18442,16066),(20821,18150),(21974,19152),(23126,20153),(23128,20155),(24279,21158),(25437,22162),(27722,24144),(27728,24148),(27746,24166),(28895,25168),(30055,26177),(30057,26179),(32368,28191),(34681,30210),(36994,32228),(39309,34244),(41624,36255),(43941,38274),(45093,39290),(45098,39293),(46258,40311),(48564,42297),(48576,42308),(48577,42309),(49733,43317),(50892,44317),(50896,44321),(53167,46306),(53217,46345),(54367,47340),(55538,48361),(57861,50399),(59016,51397),(59021,51402),(60184,52418),(61336,53435),(62509,54457),(64832,56484),(64834,56486),(65991,57485),(67063,58417),(67161,58503),(68303,59496),(69488,60541),(71817,62555),(74146,64579),(76477,66615),(77642,67637),(78808,68640),(79974,69653),(81141,70681),(82301,71689),(83462,72705),(83474,72716),(84641,73730),(85809,74731),(86976,75754),(88136,76765),(88144,76773),(89311,77784),(90468,78788),(90481,78800),(92818,80834),(95157,82889),(97496,84924),(99837,86974),(101001,87978),(102170,89003),(102178,89009),(103349,90030),(104521,91053),(105656,92049),(105692,92078),(106864,93093),(109191,95120),(109207,95134),(109209,95135),(110353,96132),(110375,96152),(111554,97174),(113896,99207),(113901,99211),(115074,100241),(116248,101276),(118579,103297),(118597,103313),(120946,105374),(123297,107437),(125646,109490),(125648,109492),(128001,111513),(130354,113567),(132709,115638),(133886,116671),(135064,117692),(136227,118714),(136242,118727),(137389,119727),(137421,119757),(138599,120785),(139778,121807),(140956,122826),(140957,122827),(142137,123868),(144496,125905),(146857,127955),(148034,128987),(149218,130042),(150399,131054),(151581,132087),(153944,134140),(156308,136209),(156309,136210),(158670,138265),(158674,138268),(159829,139265),(161041,140328),(162214,141363),(162224,141370),(163408,142403),(165775,144451),(165777,144453),(166961,145492),(168146,146526),(170517,148600),(172744,150550),(172888,150670),(175261,152730),(177634,154789),(178820,155823),(178821,155824),(180009,156873),(182384,158948),(183572,159989),(184760,161028),(184761,161029),(185948,162059),(187138,163099),(188312,164129),(189515,165177),(189516,165178),(189517,165179),(191896,167247),(194276,169337),(194277,169338),(195446,170358),(196658,171408),(197849,172444),(199041,173487),(200226,174526),(201424,175574),(202616,176604),(203809,177648),(205001,178687),(206194,179713),(208581,181784),(210968,183851),(212159,184886),(212161,184888),(213325,185910),(213357,185936),(214536,186969),(215746,188030),(218135,190093),(218137,190095),(219332,191124),(220528,192171),(221688,193189),(222921,194262),(224117,195301),(225282,196319),(225306,196341),(225314,196349),(227696,198433),(227708,198442),(227709,198443),(230104,200531),(232501,202619),(234898,204702),(236097,205749),(237297,206786),(239696,208890),(242097,210989),(244498,213098)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check024 :
    PLift (groupData 2640304 244498 2307 2402 g024 points024) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts024 :
    compareNamed primeRoster 19 18 2640304 244498 points024 := by
  decide +kernel

private theorem cover024 : covers 2307 2402 :=
  @groupChecked primeRoster 5000 18 2640304 244498 2307 2402 g024 points024
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check024.down counts024

private def g025 : List Row :=
  [⟨2403,2402,8485,9524⟩,
  ⟨2404,2401,8484,11633⟩,
  ⟨2405,2404,12684,13736⟩,
  ⟨2406,2402,11631,15836⟩,
  ⟨2407,2404,14784,17928⟩,
  ⟨2408,2406,17927,20028⟩,
  ⟨2409,2395,7420,22140⟩,
  ⟨2410,2403,16879,24221⟩,
  ⟨2411,2395,9495,26324⟩,
  ⟨2412,2401,16872,28429⟩,
  ⟨2413,2384,0,30532⟩,
  ⟨2414,2405,23169,32651⟩,
  ⟨2415,2397,15801,34747⟩,
  ⟨2416,2413,33704,36861⟩,
  ⟨2417,2415,36861,38971⟩,
  ⟨2418,2405,27352,41070⟩,
  ⟨2419,2412,35795,43169⟩,
  ⟨2420,2409,33690,45279⟩,
  ⟨2421,2418,44220,47395⟩,
  ⟨2422,2421,48467,49515⟩,
  ⟨2423,2421,49515,51631⟩,
  ⟨2424,2420,49513,53742⟩,
  ⟨2425,2417,47389,55858⟩,
  ⟨2426,2423,54792,57940⟩,
  ⟨2427,2423,55856,60057⟩,
  ⟨2428,2424,57938,62163⟩,
  ⟨2429,2423,57936,64286⟩,
  ⟨2430,2429,65339,66403⟩,
  ⟨2431,2429,66403,68517⟩,
  ⟨2432,2431,69565,70614⟩,
  ⟨2433,2427,66399,72731⟩,
  ⟨2434,2431,71669,74841⟩,
  ⟨2435,2434,75897,76966⟩,
  ⟨2436,2435,78030,79081⟩,
  ⟨2437,2436,80142,81204⟩,
  ⟨2438,2437,82262,83324⟩,
  ⟨2439,2426,71650,85451⟩,
  ⟨2440,2416,62104,87591⟩,
  ⟨2441,2426,73765,89722⟩,
  ⟨2442,2441,90785,91849⟩,
  ⟨2443,2442,92913,93978⟩,
  ⟨2444,2442,93977,96128⟩,
  ⟨2445,2441,93976,98259⟩,
  ⟨2446,2442,96127,100400⟩,
  ⟨2447,2445,100400,102510⟩,
  ⟨2448,2444,100398,104651⟩,
  ⟨2449,2448,105724,106810⟩,
  ⟨2450,2447,105724,108936⟩,
  ⟨2451,2450,109997,111066⟩,
  ⟨2452,2440,100384,113189⟩,
  ⟨2453,2398,56569,115328⟩,
  ⟨2454,2447,109992,117472⟩,
  ⟨2455,2448,112118,119588⟩,
  ⟨2456,2452,117470,121723⟩,
  ⟨2457,2436,101412,123912⟩,
  ⟨2458,2450,117464,126047⟩,
  ⟨2459,2435,102451,128198⟩,
  ⟨2460,2453,122815,130338⟩,
  ⟨2461,2460,131408,132476⟩,
  ⟨2462,2461,133546,134626⟩,
  ⟨2463,2459,132474,136787⟩,
  ⟨2464,2462,136786,138937⟩,
  ⟨2465,2451,126028,141076⟩,
  ⟨2466,2465,142146,143228⟩,
  ⟨2467,2460,137862,145406⟩,
  ⟨2468,2440,117382,147537⟩,
  ⟨2469,2467,147537,149695⟩,
  ⟨2470,2431,109834,151836⟩,
  ⟨2471,2452,133510,153984⟩,
  ⟨2472,2471,155070,156139⟩,
  ⟨2473,2472,157215,158295⟩,
  ⟨2474,2473,159369,160455⟩,
  ⟨2475,2472,159368,162620⟩,
  ⟨2476,2459,146434,164773⟩,
  ⟨2477,2472,161534,166940⟩,
  ⟨2478,2462,151811,169092⟩,
  ⟨2479,2477,169092,171264⟩,
  ⟨2480,2473,165851,173414⟩,
  ⟨2481,2477,171262,175577⟩,
  ⟨2482,2477,172349,177743⟩,
  ⟨2483,2475,171258,179907⟩,
  ⟨2484,2483,180983,182058⟩,
  ⟨2485,2483,182058,184232⟩,
  ⟨2486,2481,180980,186398⟩,
  ⟨2487,2483,184231,188588⟩,
  ⟨2488,2484,186397,190756⟩,
  ⟨2489,2487,190756,192934⟩,
  ⟨2490,2480,184223,195090⟩,
  ⟨2491,2490,196170,197259⟩,
  ⟨2492,2483,189663,199430⟩,
  ⟨2493,2472,178776,201622⟩,
  ⟨2494,2484,192925,203816⟩,
  ⟨2495,2493,203816,205980⟩,
  ⟨2496,2491,202712,208155⟩,
  ⟨2497,2493,205978,210331⟩,
  ⟨2498,2497,211418,212516⟩]

private def points025 : List (ℕ × ℕ) := [(0,0),(8482,7420),(9706,8484),(9707,8485),(10877,9495),(10909,9524),(13310,11631),(13312,11633),(14514,12684),(15717,13736),(16918,14784),(18082,15801),(18122,15836),(19310,16872),(19319,16879),(20528,17927),(20529,17928),(22936,20028),(25345,22140),(26539,23169),(27754,24221),(30165,26324),(31349,27352),(32576,28429),(34989,30532),(37402,32651),(38594,33690),(38608,33704),(39817,34747),(41018,35795),(42232,36861),(44649,38971),(47066,41070),(49485,43169),(50693,44220),(51904,45279),(54317,47389),(54325,47395),(55535,48467),(56744,49513),(56746,49515),(59169,51631),(61592,53742),(62803,54792),(64015,55856),(64017,55858),(64851,56569),(66438,57936),(66440,57938),(66442,57940),(68869,60057),(71224,62104),(71296,62163),(73725,64286),(74939,65339),(76150,66399),(76154,66403),(78585,68517),(79800,69565),(81016,70614),(82211,71650),(82231,71669),(83449,72731),(84637,73765),(85882,74841),(87099,75897),(88317,76966),(89534,78030),(90752,79081),(91970,80142),(93189,81204),(94407,82262),(95626,83324),(98065,85451),(100504,87591),(102945,89722),(104165,90785),(105386,91849),(106607,92913),(107827,93976),(107828,93977),(107829,93978),(110270,96127),(110272,96128),(112717,98259),(115144,100384),(115160,100398),(115162,100400),(116330,101412),(117537,102451),(117609,102510),(120056,104651),(121279,105724),(121280,105724),(122505,106810),(124954,108936),(125989,109834),(126173,109992),(126179,109997),(127405,111066),(128624,112118),(129856,113189),(132309,115328),(134664,117382),(134754,117464),(134760,117470),(134762,117472),(137217,119588),(139672,121723),(140894,122815),(142129,123912),(144562,126028),(144586,126047),(147045,128198),(149504,130338),(150734,131408),(151963,132474),(151965,132476),(153150,133510),(153195,133546),(154426,134626),(156888,136786),(156889,136787),(158114,137862),(159352,138937),(161817,141076),(163049,142146),(164282,143228),(166749,145406),(167946,146434),(169216,147537),(171685,149695),(174122,151811),(174154,151836),(176625,153984),(177860,155070),(179096,156139),(180332,157215),(181569,158295),(182804,159368),(182805,159369),(184042,160455),(185276,161534),(186517,162620),(188992,164773),(190224,165851),(191469,166940),(193946,169092),(196417,171258),(196423,171262),(196425,171264),(197661,172349),(198904,173414),(201385,175577),(203866,177743),(205052,178776),(206349,179907),(207587,180980),(207590,180983),(208832,182058),(211304,184223),(211315,184231),(211317,184232),(213800,186397),(213802,186398),(216289,188588),(217522,189663),(218776,190756),(221252,192925),(221265,192934),(223754,195090),(224999,196170),(226245,197259),(228736,199430),(231229,201622),(232472,202712),(233722,203816),(236215,205978),(236217,205980),(238712,208155),(241209,210331),(242457,211418),(243706,212516)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check025 :
    PLift (groupData 2876296 243706 2403 2498 g025 points025) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts025 :
    compareNamed primeRoster 19 18 2876296 243706 points025 := by
  decide +kernel

private theorem cover025 : covers 2403 2498 :=
  @groupChecked primeRoster 5000 18 2876296 243706 2403 2498 g025 points025
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check025.down counts025

private def g026 : List Row :=
  [⟨2499,2497,9862,12044⟩,
  ⟨2500,2499,13131,14224⟩,
  ⟨2501,2497,12042,16397⟩,
  ⟨2502,2501,17488,18576⟩,
  ⟨2503,2502,19667,20746⟩,
  ⟨2504,2491,8746,22933⟩,
  ⟨2505,2482,0,25117⟩,
  ⟨2506,2505,26209,27305⟩,
  ⟨2507,2492,13107,29469⟩,
  ⟨2508,2503,26206,31655⟩,
  ⟨2509,2505,29468,33843⟩,
  ⟨2510,2507,32748,36010⟩,
  ⟨2511,2506,32746,38185⟩,
  ⟨2512,2511,39279,40384⟩,
  ⟨2513,2509,38184,42593⟩,
  ⟨2514,2508,38181,44770⟩,
  ⟨2515,2511,42592,46961⟩,
  ⟨2516,2515,48053,49144⟩,
  ⟨2517,2516,50240,51350⟩,
  ⟨2518,2516,51349,53550⟩,
  ⟨2519,2518,54647,55744⟩,
  ⟨2520,2516,53548,57945⟩,
  ⟨2521,2519,57945,60153⟩,
  ⟨2522,2518,57943,62346⟩,
  ⟨2523,2506,45840,64555⟩,
  ⟨2524,2523,65652,66763⟩,
  ⟨2525,2524,67880,68980⟩,
  ⟨2526,2515,59041,71193⟩,
  ⟨2527,2518,63456,73405⟩,
  ⟨2528,2527,74523,75620⟩,
  ⟨2529,2523,71190,77824⟩,
  ⟨2530,2527,76727,80031⟩,
  ⟨2531,2530,81131,82230⟩,
  ⟨2532,2524,75612,84437⟩,
  ⟨2533,2531,84437,86663⟩,
  ⟨2534,2532,86662,88865⟩,
  ⟨2535,2521,75598,91074⟩,
  ⟨2536,2516,71152,93295⟩,
  ⟨2537,2536,94403,95515⟩,
  ⟨2538,2536,95514,97735⟩,
  ⟨2539,2536,96631,99949⟩,
  ⟨2540,2533,94398,102159⟩,
  ⟨2541,2534,96626,104367⟩,
  ⟨2542,2538,102157,106588⟩,
  ⟨2543,2511,73285,108802⟩,
  ⟨2544,2542,108801,111032⟩,
  ⟨2545,2537,104360,113257⟩,
  ⟨2546,2538,106583,115478⟩,
  ⟨2547,2543,113255,117702⟩,
  ⟨2548,2547,118816,119923⟩,
  ⟨2549,2526,96574,122149⟩,
  ⟨2550,2546,119921,124362⟩,
  ⟨2551,2550,125467,126592⟩,
  ⟨2552,2547,123257,128810⟩,
  ⟨2553,2550,127705,131036⟩,
  ⟨2554,2552,131035,133272⟩,
  ⟨2555,2550,129932,135511⟩,
  ⟨2556,2549,129929,137724⟩,
  ⟨2557,2530,109839,139962⟩,
  ⟨2558,2539,121001,142193⟩,
  ⟨2559,2554,138851,144420⟩,
  ⟨2560,2556,142191,146658⟩,
  ⟨2561,2552,138846,148900⟩,
  ⟨2562,2559,147777,151117⟩,
  ⟨2563,2558,147775,153356⟩,
  ⟨2564,2563,154473,155592⟩,
  ⟨2565,2555,146647,157835⟩,
  ⟨2566,2562,155591,160046⟩,
  ⟨2567,2545,137672,162286⟩,
  ⟨2568,2564,160045,164534⟩,
  ⟨2569,2552,147743,166777⟩,
  ⟨2570,2567,165661,169017⟩,
  ⟨2571,2565,164531,171261⟩,
  ⟨2572,2568,169015,173486⟩,
  ⟨2573,2563,164524,175726⟩,
  ⟨2574,2568,171256,177987⟩,
  ⟨2575,2574,179112,180233⟩,
  ⟨2576,2568,173480,182493⟩,
  ⟨2577,2567,173476,184740⟩,
  ⟨2578,2570,177979,186984⟩,
  ⟨2579,2577,186984,189250⟩,
  ⟨2580,2574,184736,191505⟩,
  ⟨2581,2580,192641,193765⟩,
  ⟨2582,2575,188103,196017⟩,
  ⟨2583,2579,193763,198270⟩,
  ⟨2584,2581,197138,200527⟩,
  ⟨2585,2583,200527,202781⟩,
  ⟨2586,2582,200525,205054⟩,
  ⟨2587,2586,206187,207302⟩,
  ⟨2588,2584,205052,209555⟩,
  ⟨2589,2587,209555,211813⟩,
  ⟨2590,2589,212949,214065⟩,
  ⟨2591,2576,199367,216323⟩,
  ⟨2592,2586,211809,218576⟩,
  ⟨2593,2589,216322,220831⟩,
  ⟨2594,2583,210676,223096⟩]

private def points026 : List (ℕ × ℕ) := [(0,0),(10027,8746),(11297,9862),(13794,12042),(13796,12044),(15017,13107),(15045,13131),(16295,14224),(18796,16397),(20046,17488),(21297,18576),(22548,19667),(23800,20746),(26303,22933),(28808,25117),(30057,26206),(30060,26209),(31313,27305),(33818,29468),(33820,29469),(36327,31655),(37578,32746),(37580,32748),(38836,33843),(41345,36010),(43851,38181),(43854,38184),(43856,38185),(45111,39279),(46367,40384),(48878,42592),(48880,42593),(51393,44770),(52614,45840),(53908,46961),(55165,48053),(56423,49144),(57681,50240),(58939,51349),(58940,51350),(61455,53548),(61457,53550),(62716,54647),(63976,55744),(66493,57943),(66495,57945),(67740,59041),(69016,60153),(71537,62346),(72788,63456),(74060,64555),(75321,65652),(76583,66763),(77845,67880),(79108,68980),(81583,71152),(81629,71190),(81633,71193),(84032,73285),(84160,73405),(85423,74523),(86663,75598),(86679,75612),(86687,75620),(87950,76727),(89216,77824),(91745,80031),(93010,81131),(94276,82230),(96807,84437),(99339,86662),(99340,86663),(101873,88865),(104408,91074),(106943,93295),(108205,94398),(108211,94403),(109479,95514),(109480,95515),(110682,96574),(110742,96626),(110747,96631),(112017,97735),(114556,99949),(117093,102157),(117095,102159),(119628,104360),(119636,104367),(122169,106583),(122177,106588),(124719,108801),(124720,108802),(125900,109839),(127263,111032),(129806,113255),(129808,113257),(132353,115478),(134900,117702),(136173,118816),(137445,119921),(137447,119923),(138676,121001),(139996,122149),(141267,123257),(142545,124362),(143820,125467),(145096,126592),(146370,127705),(147647,128810),(148917,129929),(148920,129932),(150199,131035),(150200,131036),(152753,133272),(155308,135511),(157803,137672),(157863,137724),(159131,138846),(159138,138851),(160420,139962),(162975,142191),(162977,142193),(165536,144420),(168083,146647),(168095,146658),(169339,147743),(169372,147775),(169374,147777),(170656,148900),(173217,151117),(175780,153356),(177061,154473),(178341,155591),(178343,155592),(180908,157835),(183471,160045),(183473,160046),(186040,162286),(188595,164524),(188603,164531),(188607,164534),(189890,165661),(191176,166777),(193743,169015),(193745,169017),(196311,171256),(196316,171261),(198875,173476),(198879,173480),(198887,173486),(201460,175726),(204025,177979),(204033,177987),(205320,179112),(206608,180233),(209183,182493),(211755,184736),(211760,184740),(214337,186984),(215620,188103),(216916,189250),(219495,191505),(220785,192641),(222074,193763),(222076,193765),(224657,196017),(225947,197138),(227240,198270),(228503,199367),(229821,200525),(229823,200527),(232408,202781),(234991,205052),(234993,205054),(236286,206187),(237580,207302),(240167,209555),(241446,210676),(242751,211809),(242756,211813),(244050,212949),(245345,214065),(247934,216322),(247936,216323),(250527,218576),(253120,220831),(255713,223096)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check026 :
    PLift (groupData 3108705 255713 2499 2594 g026 points026) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts026 :
    compareNamed primeRoster 19 18 3108705 255713 points026 := by
  decide +kernel

private theorem cover026 : covers 2499 2594 :=
  @groupChecked primeRoster 5000 18 3108705 255713 2499 2594 g026 points026
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check026.down counts026

private def g027 : List Row :=
  [⟨2595,2586,7932,18111⟩,
  ⟨2596,2587,10184,20379⟩,
  ⟨2597,2592,16979,22649⟩,
  ⟨2598,2576,0,24907⟩,
  ⟨2599,2577,2254,27172⟩,
  ⟨2600,2599,28303,29422⟩,
  ⟨2601,2597,27171,31700⟩,
  ⟨2602,2599,30563,33979⟩,
  ⟨2603,2597,29418,36256⟩,
  ⟨2604,2595,28294,38531⟩,
  ⟨2605,2600,35116,40808⟩,
  ⟨2606,2603,39669,43099⟩,
  ⟨2607,2606,44234,45387⟩,
  ⟨2608,2607,46511,47652⟩,
  ⟨2609,2600,39660,49918⟩,
  ⟨2610,2607,48781,52187⟩,
  ⟨2611,2610,53322,54471⟩,
  ⟨2612,2609,53321,56740⟩,
  ⟨2613,2602,46499,59024⟩,
  ⟨2614,2611,57891,61303⟩,
  ⟨2615,2614,62444,63585⟩,
  ⟨2616,2607,55594,65867⟩,
  ⟨2617,2616,67009,68155⟩,
  ⟨2618,2613,64733,70439⟩,
  ⟨2619,2613,65864,72712⟩,
  ⟨2620,2607,60148,74975⟩,
  ⟨2621,2619,74975,77259⟩,
  ⟨2622,2597,50995,79551⟩,
  ⟨2623,2622,80699,81844⟩,
  ⟨2624,2622,81843,84118⟩,
  ⟨2625,2614,73836,86413⟩,
  ⟨2626,2613,73830,88696⟩,
  ⟨2627,2612,73825,90997⟩,
  ⟨2628,2611,73818,93299⟩,
  ⟨2629,2628,94443,95591⟩,
  ⟨2630,2629,96740,97898⟩,
  ⟨2631,2630,99028,100181⟩,
  ⟨2632,2627,96737,102490⟩,
  ⟨2633,2614,82942,104793⟩,
  ⟨2634,2633,105924,107074⟩,
  ⟨2635,2633,107074,109372⟩,
  ⟨2636,2627,101325,111664⟩,
  ⟨2637,2631,107072,113944⟩,
  ⟨2638,2609,82893,116267⟩,
  ⟨2639,2624,101309,118563⟩,
  ⟨2640,2635,115096,120869⟩,
  ⟨2641,2635,116263,123167⟩,
  ⟨2642,2641,124319,125483⟩,
  ⟨2643,2639,123165,127798⟩,
  ⟨2644,2628,111638,130101⟩,
  ⟨2645,2644,131265,132409⟩,
  ⟨2646,2644,132408,134723⟩,
  ⟨2647,2643,132407,137040⟩,
  ⟨2648,2646,137039,139356⟩,
  ⟨2649,2643,134720,141670⟩,
  ⟨2650,2611,98868,143974⟩,
  ⟨2651,2650,145125,146288⟩,
  ⟨2652,2634,127765,148584⟩,
  ⟨2653,2651,148584,150888⟩,
  ⟨2654,2648,146283,153196⟩,
  ⟨2655,2653,153196,155504⟩,
  ⟨2656,2651,152038,157825⟩,
  ⟨2657,2644,145109,160141⟩,
  ⟨2658,2656,160140,162485⟩,
  ⟨2659,2656,161317,164819⟩,
  ⟨2660,2647,152021,167132⟩,
  ⟨2661,2653,160133,169450⟩,
  ⟨2662,2659,168283,171773⟩,
  ⟨2663,2656,165961,174081⟩,
  ⟨2664,2657,168278,176421⟩,
  ⟨2665,2664,177578,178732⟩,
  ⟨2666,2661,175247,181049⟩,
  ⟨2667,2664,179881,183383⟩,
  ⟨2668,2667,184539,185710⟩,
  ⟨2669,2648,163606,188050⟩,
  ⟨2670,2660,178721,190404⟩,
  ⟨2671,2659,178716,192745⟩,
  ⟨2672,2667,189219,195088⟩,
  ⟨2673,2650,170554,197413⟩,
  ⟨2674,2665,189212,199746⟩,
  ⟨2675,2659,183354,202083⟩,
  ⟨2676,2673,200906,204417⟩,
  ⟨2677,2672,200905,206759⟩,
  ⟨2678,2676,206758,209083⟩,
  ⟨2679,2660,189182,211452⟩,
  ⟨2680,2668,199730,213783⟩,
  ⟨2681,2680,214955,216133⟩,
  ⟨2682,2680,216132,218465⟩,
  ⟨2683,2682,219647,220816⟩,
  ⟨2684,2681,219646,223149⟩,
  ⟨2685,2684,224327,225503⟩,
  ⟨2686,2685,226667,227843⟩]

private def points027 : List (ℕ × ℕ) := [(0,0),(2588,2254),(9111,7932),(11702,10184),(19488,16979),(20789,18111),(23384,20379),(25981,22649),(28578,24907),(31175,27171),(31177,27172),(32466,28294),(32476,28303),(33772,29418),(33776,29422),(35075,30563),(36377,31700),(38978,33979),(40276,35116),(41581,36256),(44184,38531),(45476,39660),(45485,39669),(46789,40808),(49394,43099),(50697,44234),(52001,45387),(53289,46499),(53304,46511),(54608,47652),(55911,48781),(57217,49918),(58443,50995),(59826,52187),(61130,53321),(61131,53322),(62437,54471),(63732,55594),(65048,56740),(66353,57891),(67661,59024),(68946,60148),(70274,61303),(71581,62444),(72889,63585),(74193,64733),(75500,65864),(75504,65867),(76812,67009),(78121,68155),(80738,70439),(83357,72712),(84630,73818),(84638,73825),(84645,73830),(84651,73836),(85976,74975),(88597,77259),(91218,79551),(92529,80699),(93840,81843),(93841,81844),(95047,82893),(95107,82942),(96464,84118),(99089,86413),(101714,88696),(104341,90997),(106968,93299),(108282,94443),(109597,95591),(110908,96737),(110911,96740),(112226,97898),(113351,98868),(113541,99028),(114857,100181),(116144,101309),(116162,101325),(117488,102490),(120121,104793),(121437,105924),(122750,107072),(122754,107074),(125389,109372),(127992,111638),(128024,111664),(130661,113944),(131976,115096),(133294,116263),(133298,116267),(135937,118563),(138576,120869),(141215,123165),(141217,123167),(142537,124319),(143858,125483),(146460,127765),(146501,127798),(149144,130101),(150466,131265),(151787,132407),(151788,132408),(151789,132409),(154430,134720),(154434,134723),(157080,137039),(157081,137040),(159728,139356),(162377,141670),(165026,143974),(166330,145109),(166351,145125),(167672,146283),(167677,146288),(170328,148584),(172981,150888),(174286,152021),(174304,152038),(175634,153196),(178289,155504),(180944,157825),(183593,160133),(183600,160140),(183601,160141),(184928,161317),(186258,162485),(187532,163606),(188917,164819),(190240,165961),(191576,167132),(192900,168278),(192905,168283),(194237,169450),(195501,170554),(196898,171773),(199561,174081),(200889,175247),(202224,176421),(203556,177578),(204871,178716),(204876,178721),(204889,178732),(206220,179881),(207554,181049),(210189,183354),(210221,183383),(211554,184539),(212888,185710),(215557,188050),(216846,189182),(216881,189212),(216888,189219),(218226,190404),(220897,192745),(223568,195088),(226241,197413),(228896,199730),(228914,199746),(230248,200905),(230250,200906),(231589,202083),(234264,204417),(236940,206758),(236941,206759),(239618,209083),(242297,211452),(244976,213783),(246316,214955),(247656,216132),(247657,216133),(250338,218465),(251678,219646),(251679,219647),(253021,220816),(255704,223149),(257046,224327),(258389,225503),(259731,226667),(261074,227843)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check027 :
    PLift (groupData 3346224 261074 2595 2686 g027 points027) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts027 :
    compareNamed primeRoster 19 18 3346224 261074 points027 := by
  decide +kernel

private theorem cover027 : covers 2595 2686 :=
  @groupChecked primeRoster 5000 18 3346224 261074 2595 2686 g027 points027
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check027.down counts027

private def g028 : List Row :=
  [⟨2687,2676,3544,16450⟩,
  ⟨2688,2686,16449,18790⟩,
  ⟨2689,2671,0,21152⟩,
  ⟨2690,2678,9387,23500⟩,
  ⟨2691,2689,23500,25842⟩,
  ⟨2692,2691,27012,28191⟩,
  ⟨2693,2687,23496,30536⟩,
  ⟨2694,2691,29357,32895⟩,
  ⟨2695,2691,30534,35247⟩,
  ⟨2696,2691,31709,37592⟩,
  ⟨2697,2685,25828,39947⟩,
  ⟨2698,2693,36411,42299⟩,
  ⟨2699,2695,39945,44660⟩,
  ⟨2700,2698,44659,47010⟩,
  ⟨2701,2695,42296,49368⟩,
  ⟨2702,2700,49367,51732⟩,
  ⟨2703,2676,22246,54094⟩,
  ⟨2704,2698,49364,56463⟩,
  ⟨2705,2698,50535,58816⟩,
  ⟨2706,2705,60002,61182⟩,
  ⟨2707,2701,56459,63547⟩,
  ⟨2708,2703,59999,65916⟩,
  ⟨2709,2690,45805,68290⟩,
  ⟨2710,2706,65914,70673⟩,
  ⟨2711,2710,71859,73034⟩,
  ⟨2712,2710,73033,75398⟩,
  ⟨2713,2710,74222,77769⟩,
  ⟨2714,2704,68277,80138⟩,
  ⟨2715,2693,56407,82505⟩,
  ⟨2716,2710,77765,84862⟩,
  ⟨2717,2687,51628,87236⟩,
  ⟨2718,2717,88412,89620⟩,
  ⟨2719,2693,61105,92005⟩,
  ⟨2720,2717,90805,94382⟩,
  ⟨2721,2720,95570,96758⟩,
  ⟨2722,2718,94381,99152⟩,
  ⟨2723,2720,97959,101521⟩,
  ⟨2724,2723,102706,103895⟩,
  ⟨2725,2713,91990,106277⟩,
  ⟨2726,2724,106276,108655⟩,
  ⟨2727,2708,88373,111027⟩,
  ⟨2728,2721,105081,113416⟩,
  ⟨2729,2723,108651,115789⟩,
  ⟨2730,2721,107458,118164⟩,
  ⟨2731,2726,114596,120565⟩,
  ⟨2732,2726,115785,122962⟩,
  ⟨2733,2730,121754,125363⟩,
  ⟨2734,2730,122960,127755⟩,
  ⟨2735,2733,127755,130123⟩,
  ⟨2736,2735,131321,132516⟩,
  ⟨2737,2716,109790,134912⟩,
  ⟨2738,2735,133705,137325⟩,
  ⟨2739,2737,137325,139715⟩,
  ⟨2740,2734,134909,142110⟩,
  ⟨2741,2736,138504,144518⟩,
  ⟨2742,2740,144517,146892⟩,
  ⟨2743,2732,136098,149306⟩,
  ⟨2744,2743,150515,151720⟩,
  ⟨2745,2739,146888,154104⟩,
  ⟨2746,2727,133667,156503⟩,
  ⟨2747,2737,146880,158892⟩,
  ⟨2748,2747,160084,161279⟩,
  ⟨2749,2747,161279,163681⟩,
  ⟨2750,2718,127643,166080⟩,
  ⟨2751,2743,158885,168508⟩,
  ⟨2752,2742,158880,170907⟩,
  ⟨2753,2752,172118,173322⟩,
  ⟨2754,2748,168503,175734⟩,
  ⟨2755,2736,155261,178133⟩,
  ⟨2756,2737,157650,180531⟩,
  ⟨2757,2756,181734,182934⟩,
  ⟨2758,2754,180529,185326⟩,
  ⟨2759,2751,178127,187730⟩,
  ⟨2760,2747,174504,190151⟩,
  ⟨2761,2757,187729,192590⟩,
  ⟨2762,2761,193771,194961⟩,
  ⟨2763,2754,186515,197390⟩,
  ⟨2764,2757,191361,199812⟩,
  ⟨2765,2759,194957,202233⟩,
  ⟨2766,2765,203432,204636⟩,
  ⟨2767,2762,201018,207055⟩,
  ⟨2768,2762,202229,209470⟩,
  ⟨2769,2750,188901,211894⟩,
  ⟨2770,2749,188891,214305⟩,
  ⟨2771,2762,205835,216734⟩,
  ⟨2772,2771,217951,219158⟩,
  ⟨2773,2772,220367,221575⟩,
  ⟨2774,2760,207032,223991⟩,
  ⟨2775,2762,210667,226408⟩,
  ⟨2776,2768,219150,228845⟩]

private def points028 : List (ℕ × ℕ) := [(0,0),(4046,3544),(10750,9387),(18824,16449),(18825,16450),(21512,18790),(24201,21152),(25454,22246),(26886,23496),(26890,23500),(29563,25828),(29581,25842),(30926,27012),(32272,28191),(33617,29357),(34963,30534),(34965,30536),(36308,31709),(37658,32895),(40353,35247),(41697,36411),(43048,37592),(45743,39945),(45745,39947),(48438,42296),(48442,42299),(51140,44659),(51141,44660),(52445,45805),(53840,47010),(56536,49364),(56540,49367),(56541,49368),(57885,50535),(59130,51628),(59242,51732),(61945,54094),(64588,56407),(64644,56459),(64648,56463),(67353,58816),(68702,59999),(68705,60002),(69974,61105),(70058,61182),(72765,63547),(75470,65914),(75472,65916),(78168,68277),(78181,68290),(80890,70673),(82245,71859),(83600,73033),(83601,73034),(84955,74222),(86312,75398),(89020,77765),(89025,77769),(91738,80138),(94453,82505),(97168,84862),(99885,87236),(101198,88373),(101243,88412),(102602,89620),(103960,90805),(105303,91990),(105321,92005),(108038,94381),(108040,94382),(109400,95570),(110761,96758),(112120,97959),(113482,99152),(116205,101521),(117566,102706),(118928,103895),(120284,105081),(121652,106276),(121653,106277),(123005,107458),(124374,108651),(124378,108655),(125686,109790),(127105,111027),(129832,113416),(131193,114596),(132556,115785),(132561,115789),(135290,118164),(138021,120565),(139385,121754),(140750,122960),(140752,122962),(143485,125363),(146090,127643),(146218,127755),(148953,130123),(150320,131321),(151688,132516),(153011,133667),(153055,133705),(154420,134909),(154425,134912),(155778,136098),(157162,137325),(158528,138504),(159901,139715),(162640,142110),(165380,144517),(165381,144518),(168110,146880),(168118,146888),(168122,146892),(170865,149306),(172236,150515),(173608,151720),(176353,154104),(177680,155261),(179098,156503),(180426,157650),(181832,158880),(181837,158885),(181845,158892),(183218,160084),(184592,161279),(187341,163681),(190090,166080),(192836,168503),(192841,168508),(195592,170907),(196968,172118),(198345,173322),(199700,174504),(201098,175734),(203845,178127),(203853,178133),(206606,180529),(206608,180531),(207986,181734),(209365,182934),(212122,185326),(213491,186515),(214879,187729),(214881,187730),(216205,188891),(216215,188901),(217640,190151),(219014,191361),(220401,192590),(221781,193771),(223158,194957),(223162,194961),(225925,197390),(228688,199812),(230067,201018),(231448,202229),(231453,202233),(232835,203432),(234218,204636),(235591,205835),(236960,207032),(236985,207055),(239752,209470),(241115,210667),(242521,211894),(245290,214305),(248061,216734),(249446,217951),(250824,219150),(250832,219158),(252218,220367),(253605,221575),(256378,223991),(259153,226408),(261928,228845)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check028 :
    PLift (groupData 3591160 261928 2687 2776 g028 points028) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts028 :
    compareNamed primeRoster 19 18 3591160 261928 points028 := by
  decide +kernel

private theorem cover028 : covers 2687 2776 :=
  @groupChecked primeRoster 5000 18 3591160 261928 2687 2776 g028 points028
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check028.down counts028

private def g029 : List Row :=
  [⟨2777,2770,3,8500⟩,
  ⟨2778,2769,0,10922⟩,
  ⟨2779,2778,12131,13340⟩,
  ⟨2780,2777,12130,15777⟩,
  ⟨2781,2771,6062,18220⟩,
  ⟨2782,2781,19434,20658⟩,
  ⟨2783,2777,15774,23090⟩,
  ⟨2784,2783,24324,25537⟩,
  ⟨2785,2783,25537,27963⟩,
  ⟨2786,2779,21868,30402⟩,
  ⟨2787,2781,25533,32843⟩,
  ⟨2788,2786,32842,35281⟩,
  ⟨2789,2785,32841,37718⟩,
  ⟨2790,2787,36482,40146⟩,
  ⟨2791,2784,34067,42613⟩,
  ⟨2792,2790,42612,45055⟩,
  ⟨2793,2767,15706,47492⟩,
  ⟨2794,2793,48721,49921⟩,
  ⟨2795,2789,45052,52368⟩,
  ⟨2796,2786,42602,54795⟩,
  ⟨2797,2795,54795,57245⟩,
  ⟨2798,2797,58467,59703⟩,
  ⟨2799,2795,57243,62158⟩,
  ⟨2800,2799,63375,64584⟩,
  ⟨2801,2798,63375,67014⟩,
  ⟨2802,2795,60916,69464⟩,
  ⟨2803,2801,69464,71914⟩,
  ⟨2804,2803,73134,74357⟩,
  ⟨2805,2800,70683,76819⟩,
  ⟨2806,2802,74355,79258⟩,
  ⟨2807,2804,78038,81708⟩,
  ⟨2808,2802,76814,84151⟩,
  ⟨2809,2787,59649,86605⟩,
  ⟨2810,2806,84149,89060⟩,
  ⟨2811,2804,82920,91528⟩,
  ⟨2812,2811,92776,93991⟩,
  ⟨2813,2801,81693,96442⟩,
  ⟨2814,2809,92775,98903⟩,
  ⟨2815,2810,95203,101360⟩,
  ⟨2816,2809,95200,103825⟩,
  ⟨2817,2785,66906,106285⟩,
  ⟨2818,2813,102594,108752⟩,
  ⟨2819,2806,95186,111201⟩,
  ⟨2820,2818,111200,113673⟩,
  ⟨2821,2820,114914,116152⟩,
  ⟨2822,2821,117379,118611⟩,
  ⟨2823,2819,116151,121096⟩,
  ⟨2824,2820,118609,123556⟩,
  ⟨2825,2810,107491,126016⟩,
  ⟨2826,2821,122322,128476⟩,
  ⟨2827,2824,127257,130957⟩,
  ⟨2828,2822,126012,133427⟩,
  ⟨2829,2823,128473,135911⟩,
  ⟨2830,2826,133426,138377⟩,
  ⟨2831,2811,116112,140863⟩,
  ⟨2832,2825,134669,143352⟩,
  ⟨2833,2824,134665,145813⟩,
  ⟨2834,2829,142103,148307⟩,
  ⟨2835,2831,145811,150790⟩,
  ⟨2836,2824,138361,153264⟩,
  ⟨2837,2834,152037,155746⟩,
  ⟨2838,2833,152035,158223⟩,
  ⟨2839,2835,155745,160690⟩,
  ⟨2840,2825,144557,163164⟩,
  ⟨2841,2832,154487,165645⟩,
  ⟨2842,2838,163162,168145⟩,
  ⟨2843,2842,169388,170643⟩,
  ⟨2844,2837,164404,173129⟩,
  ⟨2845,2844,174374,175630⟩,
  ⟨2846,2844,175629,178126⟩,
  ⟨2847,2840,171880,180628⟩,
  ⟨2848,2844,178125,183112⟩,
  ⟨2849,2821,150706,185599⟩,
  ⟨2850,2849,186842,188088⟩,
  ⟨2851,2850,189311,190546⟩,
  ⟨2852,2850,190545,193060⟩,
  ⟨2853,2850,191809,195568⟩,
  ⟨2854,2846,188080,198067⟩,
  ⟨2855,2845,188076,200564⟩,
  ⟨2856,2851,196819,203048⟩,
  ⟨2857,2856,204296,205544⟩,
  ⟨2858,2855,204295,208035⟩,
  ⟨2859,2851,200557,210546⟩,
  ⟨2860,2859,211808,213047⟩,
  ⟨2861,2858,211807,215528⟩,
  ⟨2862,2861,216782,218034⟩,
  ⟨2863,2862,219291,220544⟩,
  ⟨2864,2845,199288,223047⟩,
  ⟨2865,2863,223047,225539⟩,
  ⟨2866,2861,221793,228039⟩]

private def points029 : List (ℕ × ℕ) := [(0,0),(4,3),(6935,6062),(9724,8500),(12501,10922),(13889,12130),(13890,12131),(15280,13340),(17975,15706),(18055,15774),(18059,15777),(20840,18220),(22230,19434),(23621,20658),(25006,21868),(26404,23090),(27795,24324),(29183,25533),(29187,25537),(31972,27963),(34757,30402),(37542,32841),(37543,32842),(37544,32843),(38931,34067),(40331,35281),(41724,36482),(43120,37718),(45909,40146),(48687,42602),(48699,42612),(48700,42613),(51487,45052),(51491,45055),(54284,47492),(55680,48721),(57077,49921),(59872,52368),(62667,54795),(65462,57243),(65464,57245),(66862,58467),(68201,59649),(68261,59703),(69654,60916),(71060,62158),(72458,63375),(72459,63375),(73859,64584),(76532,66906),(76660,67014),(79461,69464),(80859,70683),(82264,71914),(83665,73134),(85065,74355),(85067,74357),(87867,76814),(87872,76819),(89273,78038),(90677,79258),(93466,81693),(93484,81708),(94881,82920),(96289,84149),(96291,84151),(99100,86605),(101909,89060),(104720,91528),(106122,92775),(106125,92776),(107531,93991),(108916,95186),(108931,95200),(108934,95203),(110344,96442),(113157,98903),(115972,101360),(117376,102594),(118787,103825),(121604,106285),(122984,107491),(124421,108752),(127239,111200),(127240,111201),(130059,113673),(131469,114914),(132830,116112),(132878,116151),(132880,116152),(134290,117379),(135699,118609),(135701,118611),(138524,121096),(139932,122322),(141347,123556),(144167,126012),(144172,126016),(145583,127257),(146993,128473),(146997,128476),(149824,130957),(152649,133426),(152651,133427),(154055,134665),(154059,134669),(155480,135911),(158291,138361),(158309,138377),(161140,140863),(162552,142103),(163971,143352),(165359,144557),(166802,145811),(166804,145813),(169637,148307),(172374,150706),(172472,150790),(173886,152035),(173888,152037),(175307,153264),(176715,154487),(178142,155745),(178144,155746),(180981,158223),(183820,160690),(186657,163162),(186659,163164),(188073,164404),(189500,165645),(192341,168145),(193762,169388),(195184,170643),(196599,171880),(198027,173129),(199449,174374),(200871,175629),(200872,175630),(203715,178125),(203717,178126),(206564,180628),(209411,183112),(212260,185599),(213684,186842),(215097,188076),(215101,188080),(215109,188088),(216534,189311),(217959,190545),(217960,190546),(219384,191809),(220811,193060),(223664,195568),(225087,196819),(226517,198067),(227899,199288),(229364,200557),(229372,200564),(232227,203048),(233654,204295),(233655,204296),(235084,205544),(237941,208035),(240800,210546),(242228,211807),(242229,211808),(243659,213047),(246520,215528),(247950,216782),(249381,218034),(250812,219291),(252244,220544),(253672,221793),(255107,223047),(257972,225539),(260837,228039)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check029 :
    PLift (groupData 3846141 260837 2777 2866 g029 points029) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts029 :
    compareNamed primeRoster 19 18 3846141 260837 points029 := by
  decide +kernel

private theorem cover029 : covers 2777 2866 :=
  @groupChecked primeRoster 5000 18 3846141 260837 2777 2866 g029 points029
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check029.down counts029

private def g030 : List Row :=
  [⟨2867,2862,60354,66603⟩,
  ⟨2868,2865,65343,69122⟩,
  ⟨2869,2856,55326,71628⟩,
  ⟨2870,2861,62835,74123⟩,
  ⟨2871,2868,72865,76625⟩,
  ⟨2872,2870,76624,79137⟩,
  ⟨2873,2808,0,81656⟩,
  ⟨2874,2869,77870,84172⟩,
  ⟨2875,2865,74112,86704⟩,
  ⟨2876,2849,55266,89215⟩,
  ⟨2877,2876,90469,91727⟩,
  ⟨2878,2876,91726,94237⟩,
  ⟨2879,2868,82906,96748⟩,
  ⟨2880,2872,89208,99277⟩,
  ⟨2881,2880,100533,101801⟩,
  ⟨2882,2880,101800,104309⟩,
  ⟨2883,2877,99273,106831⟩,
  ⟨2884,2881,105574,109353⟩,
  ⟨2885,2883,109353,111871⟩,
  ⟨2886,2867,90427,114395⟩,
  ⟨2887,2885,114395,116933⟩,
  ⟨2888,2887,118194,119457⟩,
  ⟨2889,2850,72704,121971⟩,
  ⟨2890,2888,121970,124477⟩,
  ⟨2891,2889,124477,127015⟩,
  ⟨2892,2853,80226,129563⟩,
  ⟨2893,2888,125741,132087⟩,
  ⟨2894,2889,128281,134629⟩,
  ⟨2895,2890,130826,137153⟩,
  ⟨2896,2882,121948,139677⟩,
  ⟨2897,2893,137151,142212⟩,
  ⟨2898,2896,142211,144750⟩,
  ⟨2899,2898,146008,147291⟩,
  ⟨2900,2893,140942,149833⟩,
  ⟨2901,2899,149833,152351⟩,
  ⟨2902,2897,148565,154901⟩,
  ⟨2903,2886,135855,157448⟩,
  ⟨2904,2902,157447,159984⟩,
  ⟨2905,2898,153614,162533⟩,
  ⟨2906,2884,137097,165096⟩,
  ⟨2907,2902,161260,167645⟩,
  ⟨2908,2900,159977,170180⟩,
  ⟨2909,2907,170180,172716⟩,
  ⟨2910,2902,165089,175282⟩,
  ⟨2911,2904,168909,177819⟩,
  ⟨2912,2907,173993,180366⟩,
  ⟨2913,2897,162504,182891⟩,
  ⟨2914,2906,175274,185441⟩,
  ⟨2915,2909,180363,187985⟩,
  ⟨2916,2914,187984,190541⟩,
  ⟨2917,2910,184167,193088⟩,
  ⟨2918,2911,186706,195628⟩,
  ⟨2919,2898,171396,198183⟩,
  ⟨2920,2919,199456,200719⟩,
  ⟨2921,2912,191801,203283⟩,
  ⟨2922,2907,186685,205833⟩,
  ⟨2923,2916,199450,208378⟩,
  ⟨2924,2923,209658,210953⟩,
  ⟨2925,2924,212214,213486⟩,
  ⟨2926,2925,214771,216055⟩,
  ⟨2927,2919,208371,218632⟩,
  ⟨2928,2926,218631,221176⟩,
  ⟨2929,2928,222446,223712⟩,
  ⟨2930,2922,216048,226275⟩,
  ⟨2931,2925,221172,228842⟩]

private def points030 : List (ℕ × ℕ) := [(0,0),(63170,55266),(63240,55326),(68985,60354),(71843,62835),(74718,65343),(76153,66603),(79020,69122),(81889,71628),(83133,72704),(83322,72865),(84746,74112),(84758,74123),(87628,76624),(87629,76625),(89061,77870),(90500,79137),(91746,80226),(93373,81656),(94794,82906),(96246,84172),(99121,86704),(101988,89208),(101996,89215),(103389,90427),(103434,90469),(104872,91726),(104873,91727),(107750,94237),(110629,96748),(113504,99273),(113508,99277),(114948,100533),(116388,101800),(116389,101801),(119270,104309),(120710,105574),(122153,106831),(125036,109353),(127921,111871),(130806,114395),(133693,116933),(135136,118194),(136580,119457),(139444,121948),(139468,121970),(139469,121971),(142358,124477),(143800,125741),(145249,127015),(146691,128281),(148140,129563),(149583,130826),(151033,132087),(153926,134629),(155337,135855),(156760,137097),(156819,137151),(156821,137153),(159716,139677),(161158,140942),(162612,142211),(162613,142212),(165510,144750),(166959,146008),(168409,147291),(169855,148565),(171308,149833),(174209,152351),(175653,153614),(177110,154901),(180012,157447),(180013,157448),(182908,159977),(182916,159984),(184365,161260),(185789,162504),(185821,162533),(188718,165089),(188726,165096),(191633,167645),(193080,168909),(194540,170180),(195939,171396),(197449,172716),(198900,173993),(200350,175274),(200358,175282),(203269,177819),(206176,180363),(206180,180366),(209093,182891),(210543,184167),(212006,185441),(213435,186685),(213457,186706),(214920,187984),(214921,187985),(217836,190541),(219284,191801),(220753,193088),(223670,195628),(226589,198183),(228042,199450),(228048,199456),(229508,200719),(232429,203283),(235350,205833),(238265,208371),(238273,208378),(239734,209658),(241196,210953),(242658,212214),(244121,213486),(245583,214771),(247038,216048),(247046,216055),(249972,218631),(249973,218632),(252896,221172),(252900,221176),(254364,222446),(255829,223712),(258758,226275),(261689,228842)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check030 :
    PLift (groupData 4033692 261689 2867 2931 g030 points030) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts030 :
    compareNamed primeRoster 19 18 4033692 261689 points030 := by
  decide +kernel

private theorem cover030 : covers 2867 2931 :=
  @groupChecked primeRoster 5000 18 4033692 261689 2867 2931 g030 points030
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check030.down counts030

private def g031 : List Row :=
  [⟨2932,2921,0,14087⟩,
  ⟨2933,2929,11517,16650⟩,
  ⟨2934,2933,17931,19217⟩,
  ⟨2935,2933,19217,21769⟩,
  ⟨2936,2927,12795,24340⟩,
  ⟨2937,2936,25621,26911⟩,
  ⟨2938,2932,21764,29491⟩,
  ⟨2939,2933,24336,32050⟩,
  ⟨2940,2939,33334,34623⟩,
  ⟨2941,2940,35922,37212⟩,
  ⟨2942,2941,38484,39764⟩,
  ⟨2943,2942,41046,42325⟩,
  ⟨2944,2942,42324,44915⟩,
  ⟨2945,2938,38478,47479⟩,
  ⟨2946,2925,22998,50080⟩,
  ⟨2947,2946,51372,52655⟩,
  ⟨2948,2943,48786,55227⟩,
  ⟨2949,2942,48783,57804⟩,
  ⟨2950,2944,52650,60377⟩,
  ⟨2951,2948,59089,62959⟩,
  ⟨2952,2946,57799,65532⟩,
  ⟨2953,2952,66824,68110⟩,
  ⟨2954,2949,64256,70688⟩,
  ⟨2955,2951,68108,73267⟩,
  ⟨2956,2955,74563,75862⟩,
  ⟨2957,2955,75862,78446⟩,
  ⟨2958,2951,71979,81049⟩,
  ⟨2959,2953,75859,83645⟩,
  ⟨2960,2939,59042,86211⟩,
  ⟨2961,2960,87496,88798⟩,
  ⟨2962,2955,82331,91379⟩,
  ⟨2963,2950,77135,93984⟩,
  ⟨2964,2960,91377,96544⟩,
  ⟨2965,2964,97838,99154⟩,
  ⟨2966,2952,83622,101751⟩,
  ⟨2967,2966,103050,104355⟩,
  ⟨2968,2962,99150,106957⟩,
  ⟨2969,2963,101748,109546⟩,
  ⟨2970,2969,110848,112160⟩,
  ⟨2971,2957,96522,114740⟩,
  ⟨2972,2970,114739,117344⟩,
  ⟨2973,2971,117344,119964⟩,
  ⟨2974,2971,118659,122573⟩,
  ⟨2975,2973,122573,125165⟩,
  ⟨2976,2970,119960,127771⟩,
  ⟨2977,2974,126460,130385⟩,
  ⟨2978,2977,131692,133008⟩,
  ⟨2979,2975,130384,135599⟩,
  ⟨2980,2977,134309,138208⟩,
  ⟨2981,2954,105570,140827⟩,
  ⟨2982,2959,113402,143436⟩,
  ⟨2983,2974,134301,146032⟩,
  ⟨2984,2978,140822,148665⟩,
  ⟨2985,2971,132990,151268⟩,
  ⟨2986,2981,147344,153872⟩,
  ⟨2987,2982,149972,156487⟩,
  ⟨2988,2987,157777,159078⟩,
  ⟨2989,2988,160385,161699⟩,
  ⟨2990,2977,147328,164304⟩,
  ⟨2991,2985,159074,166930⟩,
  ⟨2992,2980,153858,169543⟩,
  ⟨2993,2991,169543,172169⟩,
  ⟨2994,2993,173487,174805⟩,
  ⟨2995,2989,169539,177431⟩,
  ⟨2996,2992,174803,180056⟩,
  ⟨2997,2996,181366,182674⟩,
  ⟨2998,2994,180054,185277⟩,
  ⟨2999,2998,186593,187896⟩,
  ⟨3000,2996,185275,190514⟩,
  ⟨3001,2996,186591,193175⟩,
  ⟨3002,2988,177409,195814⟩,
  ⟨3003,3002,197130,198451⟩,
  ⟨3004,3001,197129,201064⟩,
  ⟨3005,3002,199751,203712⟩,
  ⟨3006,2999,197125,206343⟩,
  ⟨3007,3004,205027,208975⟩,
  ⟨3008,3005,207662,211587⟩,
  ⟨3009,3007,211587,214249⟩,
  ⟨3010,3008,214248,216885⟩,
  ⟨3011,3005,211583,219525⟩,
  ⟨3012,3011,220833,222148⟩,
  ⟨3013,3010,220833,224790⟩,
  ⟨3014,3003,212910,227418⟩]

private def points031 : List (ℕ × ℕ) := [(0,0),(13193,11517),(14650,12795),(16126,14087),(19059,16650),(20525,17931),(21992,19217),(24922,21764),(24927,21769),(26339,22998),(27858,24336),(27862,24340),(29330,25621),(30799,26911),(33736,29491),(36675,32050),(38144,33334),(39614,34623),(41084,35922),(42555,37212),(44019,38478),(44025,38484),(45496,39764),(46967,41046),(48438,42324),(48439,42325),(51382,44915),(54327,47479),(55793,48783),(55796,48786),(57272,50080),(58745,51372),(60214,52650),(60219,52655),(63166,55227),(66110,57799),(66115,57804),(67534,59042),(67588,59089),(69064,60377),(72015,62959),(73487,64256),(74966,65532),(76442,66824),(77917,68108),(77919,68110),(80872,70688),(82343,71979),(83827,73267),(85304,74563),(86778,75859),(86782,75862),(88239,77135),(89739,78446),(92696,81049),(94169,82331),(95630,83622),(95655,83645),(98614,86211),(100094,87496),(101575,88798),(104534,91377),(104536,91379),(107499,93984),(110438,96522),(110462,96544),(111944,97838),(113422,99150),(113427,99154),(116388,101748),(116392,101751),(117875,103050),(119359,104355),(120751,105570),(122326,106957),(125295,109546),(126779,110848),(128264,112160),(129683,113402),(131234,114739),(131235,114740),(134206,117344),(135691,118659),(137174,119960),(137179,119964),(140152,122573),(143127,125165),(144613,126460),(146102,127771),(149077,130384),(149079,130385),(150567,131692),(152032,132990),(152056,133008),(153535,134301),(153544,134309),(155035,135599),(158014,138208),(160990,140822),(160995,140827),(163976,143436),(166959,146032),(168429,147328),(168447,147344),(169942,148665),(171431,149972),(172927,151268),(175894,153858),(175912,153872),(178899,156487),(180392,157777),(181882,159074),(181886,159078),(183380,160385),(184875,161699),(187864,164304),(190855,166930),(193842,169539),(193846,169543),(196839,172169),(198335,173487),(199830,174803),(199832,174805),(202802,177409),(202827,177431),(205820,180054),(205822,180056),(207320,181366),(208819,182674),(211814,185275),(211816,185277),(213312,186591),(213315,186593),(214815,187896),(217814,190514),(220815,193175),(223816,195814),(225311,197125),(225316,197129),(225317,197130),(226819,198451),(228319,199751),(229822,201064),(232827,203712),(234328,205027),(235832,206343),(237334,207662),(238839,208975),(241842,211583),(241846,211587),(243335,212910),(244854,214248),(244855,214249),(247864,216885),(250875,219525),(252379,220833),(252380,220833),(253886,222148),(256899,224790),(259912,227418)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check031 :
    PLift (groupData 4282186 259912 2932 3014 g031 points031) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts031 :
    compareNamed primeRoster 19 18 4282186 259912 points031 := by
  decide +kernel

private theorem cover031 : covers 2932 3014 :=
  @groupChecked primeRoster 5000 18 4282186 259912 2932 3014 g031 points031
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check031.down counts031

private def g032 : List Row :=
  [⟨3015,3011,4013,9270⟩,
  ⟨3016,3015,10597,11912⟩,
  ⟨3017,3015,11912,14550⟩,
  ⟨3018,3017,15863,17193⟩,
  ⟨3019,3016,15862,19850⟩,
  ⟨3020,3013,13243,22494⟩,
  ⟨3021,3020,23830,25150⟩,
  ⟨3022,3019,23829,27799⟩,
  ⟨3023,3000,0,30426⟩,
  ⟨3024,3023,31744,33057⟩,
  ⟨3025,3021,30425,35714⟩,
  ⟨3026,3021,31741,38369⟩,
  ⟨3027,3014,23811,41028⟩,
  ⟨3028,3024,38368,43673⟩,
  ⟨3029,3028,45005,46327⟩,
  ⟨3030,3021,37028,48966⟩,
  ⟨3031,3028,47646,51616⟩,
  ⟨3032,3030,51615,54264⟩,
  ⟨3033,3030,52934,56907⟩,
  ⟨3034,3025,47638,59582⟩,
  ⟨3035,3032,58241,62237⟩,
  ⟨3036,3025,50278,64887⟩,
  ⟨3037,3021,46300,67529⟩,
  ⟨3038,3015,39636,70176⟩,
  ⟨3039,3017,43622,72840⟩,
  ⟨3040,3037,71506,75495⟩,
  ⟨3041,3040,76821,78169⟩,
  ⟨3042,3038,75493,80808⟩,
  ⟨3043,3037,75491,83469⟩,
  ⟨3044,3037,76815,86150⟩,
  ⟨3045,3036,76811,88805⟩,
  ⟨3046,3036,78157,91480⟩,
  ⟨3047,3036,79471,94143⟩,
  ⟨3048,3035,79465,96818⟩,
  ⟨3049,3044,92800,99486⟩,
  ⟨3050,3048,99485,102134⟩,
  ⟨3051,3041,91468,104822⟩,
  ⟨3052,3051,106155,107484⟩,
  ⟨3053,3049,104820,110169⟩,
  ⟨3054,3053,111507,112841⟩,
  ⟨3055,3051,110168,115521⟩,
  ⟨3056,3049,108816,118185⟩,
  ⟨3057,3048,108813,120871⟩,
  ⟨3058,3046,107469,123524⟩,
  ⟨3059,3050,114173,126206⟩,
  ⟨3060,3056,123522,128873⟩,
  ⟨3061,3059,128873,131555⟩,
  ⟨3062,3059,130216,134238⟩,
  ⟨3063,3059,131553,136940⟩,
  ⟨3064,3062,136939,139614⟩,
  ⟨3065,3056,130209,142303⟩,
  ⟨3066,3062,139612,144983⟩,
  ⟨3067,3066,146332,147669⟩,
  ⟨3068,3051,127512,150361⟩,
  ⟨3069,3067,150361,153051⟩,
  ⟨3070,3055,135568,155736⟩,
  ⟨3071,3054,135562,158437⟩,
  ⟨3072,3071,159795,161134⟩,
  ⟨3073,3072,162479,163819⟩,
  ⟨3074,3069,159792,166506⟩,
  ⟨3075,3073,166506,169208⟩,
  ⟨3076,3075,170566,171911⟩,
  ⟨3077,3075,171911,174615⟩,
  ⟨3078,3075,173258,177288⟩,
  ⟨3079,3073,171908,179992⟩,
  ⟨3080,3065,162455,182694⟩,
  ⟨3081,3080,184039,185389⟩,
  ⟨3082,3081,186729,188089⟩,
  ⟨3083,3073,177277,190779⟩,
  ⟨3084,3078,185385,193466⟩,
  ⟨3085,3083,193466,196178⟩,
  ⟨3086,3072,179969,198878⟩,
  ⟨3087,3086,200236,201599⟩,
  ⟨3088,3035,132588,204281⟩,
  ⟨3089,3087,204281,206987⟩,
  ⟨3090,3089,208345,209691⟩,
  ⟨3091,3090,211055,212404⟩,
  ⟨3092,3090,212403,215098⟩,
  ⟨3093,3089,212402,217831⟩,
  ⟨3094,3079,200211,220529⟩,
  ⟨3095,3092,219177,223233⟩,
  ⟨3096,3077,200197,225912⟩,
  ⟨3097,3093,223231,228616⟩]

private def points032 : List (ℕ × ℕ) := [(0,0),(4583,4013),(10613,9270),(12120,10597),(13628,11912),(15130,13243),(16645,14550),(18152,15862),(18153,15863),(19662,17193),(22681,19850),(25700,22494),(27189,23811),(27209,23829),(27210,23830),(28721,25150),(31742,27799),(34763,30425),(34765,30426),(36273,31741),(36276,31744),(37788,33057),(40813,35714),(42315,37028),(43836,38368),(43838,38369),(45285,39636),(46865,41028),(49832,43622),(49892,43673),(51406,45005),(52889,46300),(52921,46327),(54425,47638),(54434,47646),(55950,48966),(57450,50278),(58980,51615),(58981,51616),(60495,52934),(62012,54264),(65045,56907),(66560,58241),(68078,59582),(71113,62237),(74148,64887),(77185,67529),(80222,70176),(81740,71506),(83261,72840),(86296,75491),(86298,75493),(86300,75495),(87810,76811),(87814,76815),(87820,76821),(89328,78157),(89341,78169),(90840,79465),(90846,79471),(92382,80808),(95425,83469),(98468,86150),(101513,88805),(104546,91468),(104558,91480),(106078,92800),(107605,94143),(110652,96818),(113700,99485),(113701,99486),(116750,102134),(119799,104820),(119801,104822),(121326,106155),(122834,107469),(122852,107484),(124368,108813),(124372,108816),(125903,110168),(125905,110169),(127431,111507),(128958,112841),(130475,114173),(132013,115521),(135068,118185),(138125,120871),(141180,123522),(141182,123524),(144241,126206),(145734,127512),(147300,128873),(148820,130209),(148829,130216),(150359,131553),(150361,131555),(151540,132588),(153422,134238),(154917,135562),(154925,135568),(156484,136939),(156485,136940),(159546,139612),(159548,139614),(162613,142303),(165678,144983),(167211,146332),(168745,147669),(171812,150361),(174881,153051),(177950,155736),(181021,158437),(182553,159792),(182556,159795),(184092,161134),(185600,162455),(185628,162479),(187165,163819),(190238,166506),(193313,169208),(194850,170566),(196384,171908),(196388,171911),(197925,173258),(199465,174615),(202530,177277),(202542,177288),(205596,179969),(205621,179992),(208700,182694),(210240,184039),(211776,185385),(211781,185389),(213321,186729),(214862,188089),(217945,190779),(221028,193466),(224113,196178),(227198,198878),(228696,200197),(228713,200211),(228741,200236),(230285,201599),(233372,204281),(236461,206987),(238005,208345),(239550,209691),(241095,211055),(242639,212402),(242640,212403),(242641,212404),(245732,215098),(248825,217831),(250370,219177),(251918,220529),(255011,223231),(255013,223233),(258108,225912),(261205,228616)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check032 :
    PLift (groupData 4534500 261205 3015 3097 g032 points032) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts032 :
    compareNamed primeRoster 19 18 4534500 261205 points032 := by
  decide +kernel

private theorem cover032 : covers 3015 3097 :=
  @groupChecked primeRoster 5000 18 4534500 261205 3015 3097 g032 points032
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check032.down counts032

private def g033 : List Row :=
  [⟨3098,3097,2747,4099⟩,
  ⟨3099,3096,2746,6826⟩,
  ⟨3100,3098,6825,9542⟩,
  ⟨3101,3097,6824,12257⟩,
  ⟨3102,3099,10916,14982⟩,
  ⟨3103,3101,14982,17688⟩,
  ⟨3104,3101,16327,20414⟩,
  ⟨3105,3088,0,23134⟩,
  ⟨3106,3104,23133,25838⟩,
  ⟨3107,3096,13606,28558⟩,
  ⟨3108,3107,29919,31282⟩,
  ⟨3109,3107,31282,34002⟩,
  ⟨3110,3107,32633,36711⟩,
  ⟨3111,3109,36711,39443⟩,
  ⟨3112,3109,38073,42164⟩,
  ⟨3113,3112,43527,44885⟩,
  ⟨3114,3112,44884,47619⟩,
  ⟨3115,3108,40788,50372⟩,
  ⟨3116,3111,46252,53089⟩,
  ⟨3117,3108,43519,55825⟩,
  ⟨3118,3115,54447,58561⟩,
  ⟨3119,3118,59927,61288⟩,
  ⟨3120,3106,44863,64004⟩,
  ⟨3121,3120,65363,66733⟩,
  ⟨3122,3121,68096,69458⟩,
  ⟨3123,3121,69458,72198⟩,
  ⟨3124,3123,73578,74941⟩,
  ⟨3125,3123,74941,77683⟩,
  ⟨3126,3122,74939,80430⟩,
  ⟨3127,3126,81798,83169⟩,
  ⟨3128,3125,81797,85918⟩,
  ⟨3129,3127,85918,88650⟩,
  ⟨3130,3120,77673,91392⟩,
  ⟨3131,3129,91392,94122⟩,
  ⟨3132,3109,65303,96858⟩,
  ⟨3133,3121,83154,99611⟩,
  ⟨3134,3112,72146,102331⟩,
  ⟨3135,3126,92741,105090⟩,
  ⟨3136,3133,103724,107835⟩,
  ⟨3137,3130,100965,110584⟩,
  ⟨3138,3129,100962,113350⟩,
  ⟨3139,3129,102320,116114⟩,
  ⟨3140,3127,100953,118860⟩,
  ⟨3141,3123,96824,121602⟩,
  ⟨3142,3135,114727,124363⟩,
  ⟨3143,3136,117480,127120⟩,
  ⟨3144,3140,124361,129876⟩,
  ⟨3145,3140,125737,132633⟩,
  ⟨3146,3140,127115,135372⟩,
  ⟨3147,3146,136765,138142⟩,
  ⟨3148,3143,134005,140904⟩,
  ⟨3149,3138,128485,143668⟩,
  ⟨3150,3145,139524,146432⟩,
  ⟨3151,3148,145045,149203⟩,
  ⟨3152,3147,145043,151940⟩,
  ⟨3153,3151,151940,154704⟩,
  ⟨3154,3146,146426,157475⟩,
  ⟨3155,3148,150572,160242⟩,
  ⟨3156,3155,161626,163011⟩,
  ⟨3157,3152,158854,165776⟩,
  ⟨3158,3154,163009,168556⟩,
  ⟨3159,3158,169932,171315⟩,
  ⟨3160,3146,154680,174093⟩,
  ⟨3161,3150,161613,176886⟩,
  ⟨3162,3153,167152,179648⟩,
  ⟨3163,3157,174089,182427⟩,
  ⟨3164,3149,164370,185197⟩,
  ⟨3165,3160,181041,187971⟩,
  ⟨3166,3164,187970,190727⟩,
  ⟨3167,3166,192111,193504⟩,
  ⟨3168,3166,193503,196274⟩,
  ⟨3169,3160,186573,199051⟩,
  ⟨3170,3160,187959,201812⟩,
  ⟨3171,3170,203191,204580⟩,
  ⟨3172,3171,205969,207358⟩,
  ⟨3173,3163,196262,210140⟩,
  ⟨3174,3172,210139,212930⟩,
  ⟨3175,3143,171201,215700⟩,
  ⟨3176,3175,217077,218474⟩,
  ⟨3177,3176,219871,221267⟩,
  ⟨3178,3173,217074,224048⟩,
  ⟨3179,3175,221265,226850⟩,
  ⟨3180,3179,228230,229621⟩]

private def points033 : List (ℕ × ℕ) := [(0,0),(3132,2746),(3133,2747),(4682,4099),(7779,6824),(7780,6825),(7781,6826),(10880,9542),(12429,10916),(13981,12257),(15516,13606),(17082,14982),(18632,16327),(20185,17688),(23288,20414),(26392,23133),(26393,23134),(29498,25838),(32605,28558),(34158,29919),(35712,31282),(37265,32633),(38821,34002),(41930,36711),(43484,38073),(45041,39443),(46590,40788),(48152,42164),(49698,43519),(49708,43527),(51240,44863),(51264,44884),(51265,44885),(52818,46252),(54378,47619),(57493,50372),(60608,53089),(62165,54447),(63725,55825),(66842,58561),(68401,59927),(69961,61288),(73080,64004),(74574,65303),(74640,65363),(76201,66733),(77761,68096),(79322,69458),(82384,72146),(82445,72198),(84006,73578),(85566,74939),(85568,74941),(88680,77673),(88693,77683),(91818,80430),(93380,81797),(93381,81798),(94927,83154),(94945,83169),(98072,85918),(101201,88650),(104330,91392),(105885,92741),(107461,94122),(110552,96824),(110592,96858),(113725,99611),(115270,100953),(115281,100962),(115285,100965),(116846,102320),(116858,102331),(118424,103724),(119993,105090),(123128,107835),(126265,110584),(129402,113350),(130965,114727),(132541,116114),(134104,117480),(135680,118860),(138821,121602),(141960,124361),(141962,124363),(143530,125737),(145100,127115),(145105,127120),(146661,128485),(148248,129876),(151393,132633),(152962,134005),(154538,135372),(156111,136765),(157685,138142),(159255,139524),(160832,140904),(163981,143668),(165552,145043),(165554,145045),(167122,146426),(167130,146432),(170281,149203),(171850,150572),(173432,151940),(176560,154680),(176585,154704),(179738,157475),(181312,158854),(182893,160242),(184455,161613),(184470,161626),(186046,163009),(186048,163011),(187598,164370),(189205,165776),(190773,167152),(192362,168556),(193941,169932),(195393,171201),(195521,171315),(198676,174089),(198680,174093),(201841,176886),(205002,179648),(206580,181041),(208165,182427),(211328,185197),(212900,186573),(214480,187959),(214492,187970),(214493,187971),(217658,190727),(219241,192111),(220824,193503),(220825,193504),(223980,196262),(223992,196274),(227161,199051),(230330,201812),(231915,203191),(233501,204580),(235086,205969),(236672,207358),(239844,210139),(239845,210140),(243018,212930),(246193,215700),(247777,217074),(247780,217077),(249368,218474),(250956,219871),(252543,221265),(252545,221267),(255722,224048),(258901,226850),(260490,228230),(262080,229621)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check033 :
    PLift (groupData 4794120 262080 3098 3180 g033 points033) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts033 :
    compareNamed primeRoster 19 18 4794120 262080 points033 := by
  decide +kernel

private theorem cover033 : covers 3098 3180 :=
  @groupChecked primeRoster 5000 18 4794120 262080 3098 3180 g033 points033
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check033.down counts033

private def g034 : List Row :=
  [⟨3181,3163,0,25082⟩,
  ⟨3182,3167,6970,27864⟩,
  ⟨3183,3177,22293,30655⟩,
  ⟨3184,3182,30654,33449⟩,
  ⟨3185,3173,19511,36210⟩,
  ⟨3186,3184,36209,39006⟩,
  ⟨3187,3186,40405,41808⟩,
  ⟨3188,3187,43205,44600⟩,
  ⟨3189,3184,40402,47404⟩,
  ⟨3190,3188,47403,50196⟩,
  ⟨3191,3188,48815,53001⟩,
  ⟨3192,3191,54398,55801⟩,
  ⟨3193,3186,48810,58625⟩,
  ⟨3194,3193,60017,61421⟩,
  ⟨3195,3188,54392,64214⟩,
  ⟨3196,3188,55794,67025⟩,
  ⟨3197,3196,68438,69844⟩,
  ⟨3198,3191,62804,72624⟩,
  ⟨3199,3195,69843,75418⟩,
  ⟨3200,3192,67019,78218⟩,
  ⟨3201,3198,76812,81037⟩,
  ⟨3202,3200,81036,83841⟩,
  ⟨3203,3201,83841,86643⟩,
  ⟨3204,3200,83839,89438⟩,
  ⟨3205,3204,90822,92234⟩,
  ⟨3206,3190,72593,95032⟩,
  ⟨3207,3190,73982,97853⟩,
  ⟨3208,3200,89431,100662⟩,
  ⟨3209,3208,102070,103478⟩,
  ⟨3210,3208,103477,106308⟩,
  ⟨3211,3208,104896,109114⟩,
  ⟨3212,3184,72534,111945⟩,
  ⟨3213,3210,110543,114750⟩,
  ⟨3214,3211,113338,117558⟩,
  ⟨3215,3214,118956,120373⟩,
  ⟨3216,3210,114745,123170⟩,
  ⟨3217,3208,113329,126017⟩,
  ⟨3218,3209,116147,128839⟩,
  ⟨3219,3198,102023,131646⟩,
  ⟨3220,3210,120362,134475⟩,
  ⟨3221,3218,133058,137289⟩,
  ⟨3222,3201,110494,140124⟩,
  ⟨3223,3189,94904,142934⟩,
  ⟨3224,3219,138706,145757⟩,
  ⟨3225,3213,131631,148570⟩,
  ⟨3226,3224,148569,151398⟩,
  ⟨3227,3219,142928,154223⟩,
  ⟨3228,3227,155623,157040⟩,
  ⟨3229,3228,158455,159877⟩,
  ⟨3230,3201,121680,162694⟩,
  ⟨3231,3228,161284,165532⟩,
  ⟨3232,3231,166950,168355⟩,
  ⟨3233,3227,162690,171202⟩,
  ⟨3234,3216,148532,174021⟩,
  ⟨3235,3234,175439,176860⟩,
  ⟨3236,3233,175438,179679⟩,
  ⟨3237,3224,164093,182513⟩,
  ⟨3238,3222,162668,185355⟩,
  ⟨3239,3211,148483,188176⟩,
  ⟨3240,3230,176848,191019⟩,
  ⟨3241,3231,179668,193856⟩,
  ⟨3242,3231,181083,196693⟩,
  ⟨3243,3239,193854,199531⟩,
  ⟨3244,3234,188165,202386⟩,
  ⟨3245,3244,203804,205246⟩,
  ⟨3246,3239,198106,208086⟩,
  ⟨3247,3246,209508,210933⟩,
  ⟨3248,3247,212356,213757⟩,
  ⟨3249,3247,213757,216605⟩,
  ⟨3250,3249,218026,219452⟩,
  ⟨3251,3237,202367,222287⟩,
  ⟨3252,3244,213753,225154⟩,
  ⟨3253,3235,202353,228007⟩]

private def points034 : List (ℕ × ℕ) := [(0,0),(7945,6970),(22251,19511),(25444,22293),(28629,25082),(31810,27864),(34992,30654),(34993,30655),(38176,33449),(41360,36209),(41361,36210),(44546,39006),(46136,40402),(46139,40405),(47733,41808),(49326,43205),(50920,44600),(54108,47403),(54109,47404),(55697,48810),(55702,48815),(57298,50196),(60489,53001),(62078,54392),(62084,54398),(63672,55794),(63680,55801),(66873,58625),(68469,60017),(70066,61421),(71657,62804),(73261,64214),(76448,67019),(76456,67025),(78054,68438),(79651,69843),(79653,69844),(82752,72534),(82818,72593),(82850,72624),(84413,73982),(86049,75418),(87647,76812),(89248,78218),(92448,81036),(92449,81037),(95648,83839),(95650,83841),(98853,86643),(102048,89431),(102056,89438),(103658,90822),(105261,92234),(108322,94904),(108466,95032),(111673,97853),(114880,100662),(116429,102023),(116484,102070),(118088,103477),(118089,103478),(119692,104896),(121298,106308),(124509,109114),(126059,110494),(126113,110543),(127720,111945),(129316,113329),(129325,113338),(130928,114745),(130933,114750),(132529,116147),(134146,117558),(135753,118956),(137348,120362),(137361,120373),(138863,121680),(140576,123170),(143793,126017),(147010,128839),(150211,131631),(150229,131646),(151837,133058),(153448,134475),(156669,137289),(158276,138706),(159890,140124),(163105,142928),(163113,142934),(166336,145757),(169463,148483),(169520,148532),(169560,148569),(169561,148570),(172786,151398),(176013,154223),(177626,155623),(179240,157040),(180854,158455),(182469,159877),(184082,161284),(185666,162668),(185694,162690),(185698,162694),(187292,164093),(188929,165532),(190544,166950),(192160,168355),(195393,171202),(198626,174021),(200242,175438),(200243,175439),(201848,176848),(201861,176860),(205084,179668),(205096,179679),(206699,181083),(208333,182513),(211570,185355),(214796,188165),(214809,188176),(218048,191019),(221287,193854),(221289,193856),(224530,196693),(226145,198106),(227773,199531),(230976,202353),(230992,202367),(231016,202386),(232638,203804),(234261,205246),(237506,208086),(239129,209508),(240753,210933),(242376,212356),(243992,213753),(244000,213757),(247249,216605),(248873,218026),(250498,219452),(253749,222287),(257000,225154),(260253,228007)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check034 :
    PLift (groupData 5030752 260253 3181 3253 g034 points034) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts034 :
    compareNamed primeRoster 19 18 5030752 260253 points034 := by
  decide +kernel

private theorem cover034 : covers 3181 3253 :=
  @groupChecked primeRoster 5000 18 5030752 260253 3181 3253 g034 points034
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check034.down counts034

private def g035 : List Row :=
  [⟨3254,3248,15658,24233⟩,
  ⟨3255,3236,0,27076⟩,
  ⟨3256,3240,7109,29940⟩,
  ⟨3257,3249,21374,32801⟩,
  ⟨3258,3256,32800,35657⟩,
  ⟨3259,3258,37086,38519⟩,
  ⟨3260,3246,21357,41358⟩,
  ⟨3261,3260,42787,44221⟩,
  ⟨3262,3259,42786,47080⟩,
  ⟨3263,3254,37077,49930⟩,
  ⟨3264,3259,45654,52793⟩,
  ⟨3265,3251,35635,55653⟩,
  ⟨3266,3265,57078,58518⟩,
  ⟨3267,3266,59945,61356⟩,
  ⟨3268,3243,28447,64210⟩,
  ⟨3269,3263,58514,67072⟩,
  ⟨3270,3261,57069,69937⟩,
  ⟨3271,3268,68489,72803⟩,
  ⟨3272,3261,59932,75659⟩,
  ⟨3273,3271,75659,78523⟩,
  ⟨3274,3236,26923,81372⟩,
  ⟨3275,3269,75655,84257⟩,
  ⟨3276,3270,78518,87129⟩,
  ⟨3277,3269,78515,90010⟩,
  ⟨3278,3270,81365,92880⟩,
  ⟨3279,3277,92880,95750⟩,
  ⟨3280,3279,97191,98634⟩,
  ⟨3281,3279,98634,101518⟩,
  ⟨3282,3272,89999,104412⟩,
  ⟨3283,3278,100076,107287⟩,
  ⟨3284,3274,95737,110164⟩,
  ⟨3285,3275,98623,113061⟩,
  ⟨3286,3283,111612,115942⟩,
  ⟨3287,3279,107282,118811⟩,
  ⟨3288,3284,115940,121695⟩,
  ⟨3289,3279,110154,124570⟩,
  ⟨3290,3289,126024,127470⟩,
  ⟨3291,3289,127470,130364⟩,
  ⟨3292,3290,130363,133234⟩,
  ⟨3293,3287,127467,136097⟩,
  ⟨3294,3289,131793,138979⟩,
  ⟨3295,3291,136095,141876⟩,
  ⟨3296,3294,141875,144762⟩,
  ⟨3297,3293,141874,147641⟩,
  ⟨3298,3293,143319,150543⟩,
  ⟨3299,3292,143317,153455⟩,
  ⟨3300,3296,150541,156344⟩,
  ⟨3301,3297,153454,159245⟩,
  ⟨3302,3300,159244,162115⟩,
  ⟨3303,3258,99854,165015⟩,
  ⟨3304,3303,166469,167924⟩,
  ⟨3305,3300,163551,170805⟩,
  ⟨3306,3304,170804,173691⟩,
  ⟨3307,3298,163545,176604⟩,
  ⟨3308,3307,178039,179496⟩,
  ⟨3309,3297,164998,182375⟩,
  ⟨3310,3306,179494,185285⟩,
  ⟨3311,3306,180922,188179⟩,
  ⟨3312,3303,178034,191077⟩,
  ⟨3313,3310,189632,194003⟩,
  ⟨3314,3313,195454,196900⟩,
  ⟨3315,3304,183820,199816⟩,
  ⟨3316,3298,176568,202715⟩,
  ⟨3317,3303,185264,205622⟩,
  ⟨3318,3316,205621,208542⟩,
  ⟨3319,3317,208542,211464⟩,
  ⟨3320,3319,212927,214376⟩,
  ⟨3321,3308,198324,217294⟩,
  ⟨3322,3321,218744,220206⟩,
  ⟨3323,3313,208530,223118⟩,
  ⟨3324,3322,223117,226020⟩,
  ⟨3325,3305,199771,228928⟩]

private def points035 : List (ℕ × ℕ) := [(0,0),(8130,7109),(17906,15658),(24390,21357),(24407,21374),(27668,24233),(30742,26923),(30923,27076),(32472,28447),(34178,29940),(37434,32800),(37435,32801),(40668,35635),(40692,35657),(42311,37077),(42321,37086),(43951,38519),(47210,41358),(48839,42786),(48840,42787),(50471,44221),(52098,45654),(53732,47080),(56995,49930),(60258,52793),(63523,55653),(65145,57069),(65155,57078),(66784,58514),(66788,58518),(68406,59932),(68421,59945),(70055,61356),(73322,64210),(76591,67072),(78224,68489),(79860,69937),(83131,72803),(86398,75655),(86402,75659),(89667,78515),(89670,78518),(89675,78523),(92940,81365),(92948,81372),(96223,84257),(99498,87129),(102762,89999),(102775,90010),(106052,92880),(109318,95737),(109331,95750),(110970,97191),(112598,98623),(112610,98634),(113997,99854),(114247,100076),(115891,101518),(119172,104412),(122447,107282),(122455,107287),(125726,110154),(125738,110164),(127379,111612),(129023,113061),(132306,115940),(132308,115942),(135595,118811),(138882,121695),(142171,124570),(143815,126024),(145456,127467),(145460,127470),(148750,130363),(148751,130364),(150393,131793),(152042,133234),(155333,136095),(155335,136097),(158628,138979),(161921,141874),(161922,141875),(161923,141876),(163564,143317),(163567,143319),(165218,144762),(168515,147641),(171810,150541),(171812,150543),(175109,153454),(175111,153455),(178410,156344),(181710,159244),(181711,159245),(185012,162115),(186653,163545),(186660,163551),(188297,164998),(188315,165015),(189966,166469),(191618,167924),(194922,170804),(194923,170805),(198228,173691),(201494,176568),(201535,176604),(203178,178034),(203188,178039),(204840,179494),(204842,179496),(206493,180922),(208151,182375),(209790,183820),(211436,185264),(211460,185285),(214771,188179),(216425,189632),(218082,191077),(221395,194003),(223051,195454),(224708,196900),(226344,198324),(227973,199771),(228023,199816),(231338,202715),(234654,205621),(234655,205622),(237960,208530),(237972,208542),(241291,211464),(242950,212927),(244610,214376),(247931,217294),(249591,218744),(251252,220206),(254574,223117),(254575,223118),(257898,226020),(261223,228928)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check035 :
    PLift (groupData 5266590 261223 3254 3325 g035 points035) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts035 :
    compareNamed primeRoster 19 18 5266590 261223 points035 := by
  decide +kernel

private theorem cover035 : covers 3254 3325 :=
  @groupChecked primeRoster 5000 18 5266590 261223 3254 3325 g035 points035
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check035.down counts035

private def g036 : List Row :=
  [⟨3326,3306,0,29161⟩,
  ⟨3327,3325,29161,32079⟩,
  ⟨3328,3319,21886,34991⟩,
  ⟨3329,3327,34991,37899⟩,
  ⟨3330,3327,36440,40834⟩,
  ⟨3331,3320,27692,43740⟩,
  ⟨3332,3329,42280,46647⟩,
  ⟨3333,3329,43739,49576⟩,
  ⟨3334,3325,39356,52482⟩,
  ⟨3335,3331,49574,55421⟩,
  ⟨3336,3324,40817,58374⟩,
  ⟨3337,3313,26196,61309⟩,
  ⟨3338,3325,45176,64240⟩,
  ⟨3339,3315,32020,67145⟩,
  ⟨3340,3338,67144,70075⟩,
  ⟨3341,3338,68606,73001⟩,
  ⟨3342,3333,62764,75924⟩,
  ⟨3343,3339,73000,78847⟩,
  ⟨3344,3324,52439,81768⟩,
  ⟨3345,3344,83225,84707⟩,
  ⟨3346,3337,74444,87630⟩,
  ⟨3347,3344,86158,90562⟩,
  ⟨3348,3339,80287,93506⟩,
  ⟨3349,3344,89098,96452⟩,
  ⟨3350,3348,96451,99380⟩,
  ⟨3351,3347,96450,102331⟩,
  ⟨3352,3346,96447,105274⟩,
  ⟨3353,3346,97914,108211⟩,
  ⟨3354,3353,109678,111144⟩,
  ⟨3355,3346,100850,114071⟩,
  ⟨3356,3348,105267,117024⟩,
  ⟨3357,3356,118493,119981⟩,
  ⟨3358,3353,115560,122922⟩,
  ⟨3359,3353,117021,125885⟩,
  ⟨3360,3352,117017,128830⟩,
  ⟨3361,3342,103769,131756⟩,
  ⟨3362,3361,133247,134731⟩,
  ⟨3363,3357,128826,137686⟩,
  ⟨3364,3361,136197,140624⟩,
  ⟨3365,3359,134727,143573⟩,
  ⟨3366,3364,143572,146507⟩,
  ⟨3367,3360,139140,149474⟩,
  ⟨3368,3357,136185,152442⟩,
  ⟨3369,3364,147993,155385⟩,
  ⟨3370,3367,153918,158342⟩,
  ⟨3371,3370,159815,161304⟩,
  ⟨3372,3370,161303,164266⟩,
  ⟨3373,3371,164266,167220⟩,
  ⟨3374,3367,159810,170186⟩,
  ⟨3375,3372,168703,173165⟩,
  ⟨3376,3371,168701,176102⟩,
  ⟨3377,3366,162761,179062⟩,
  ⟨3378,3361,156830,182032⟩,
  ⟨3379,3374,177584,184999⟩,
  ⟨3380,3375,180549,187948⟩,
  ⟨3381,3380,189430,190924⟩,
  ⟨3382,3381,192417,193909⟩,
  ⟨3383,3381,193909,196861⟩,
  ⟨3384,3383,198349,199842⟩,
  ⟨3385,3383,199842,202784⟩,
  ⟨3386,3377,192409,205745⟩,
  ⟨3387,3379,196856,208707⟩,
  ⟨3388,3383,204251,211672⟩,
  ⟨3389,3387,211672,214664⟩,
  ⟨3390,3388,214663,217634⟩,
  ⟨3391,3384,210177,220607⟩,
  ⟨3392,3384,211665,223570⟩,
  ⟨3393,3390,222090,226567⟩,
  ⟨3394,3372,196807,229550⟩]

private def points036 : List (ℕ × ℕ) := [(0,0),(24938,21886),(29863,26196),(31582,27692),(33260,29161),(36515,32020),(36587,32079),(39914,34991),(41577,36440),(43243,37899),(44897,39356),(46554,40817),(46572,40834),(48236,42280),(49901,43739),(49903,43740),(51547,45176),(53234,46647),(56565,49574),(56567,49576),(59850,52439),(59900,52482),(63235,55421),(66570,58374),(69907,61309),(71565,62764),(73244,64240),(76582,67144),(76583,67145),(78251,68606),(79922,70075),(83261,73000),(83263,73001),(84923,74444),(86604,75924),(89947,78847),(91608,80287),(93290,81768),(94962,83225),(96635,84707),(98306,86158),(99980,87630),(101650,89098),(103327,90562),(106674,93506),(110018,96447),(110021,96450),(110022,96451),(110023,96452),(111691,97914),(113372,99380),(115037,100850),(116723,102331),(118353,103769),(120066,105267),(120074,105274),(123427,108211),(125103,109678),(126780,111144),(130135,114071),(131809,115560),(133482,117017),(133486,117021),(133490,117024),(135168,118493),(136847,119981),(140204,122922),(143563,125885),(146918,128826),(146922,128830),(150283,131756),(151963,133247),(153640,134727),(153644,134731),(155310,136185),(155324,136197),(157007,137686),(158682,139140),(160370,140624),(163734,143572),(163735,143573),(167100,146507),(168780,147993),(170467,149474),(173834,152442),(175517,153918),(177203,155385),(178851,156830),(180572,158342),(182251,159810),(182257,159815),(183942,161303),(183943,161304),(185613,162761),(187314,164266),(190687,167220),(192370,168701),(192372,168703),(194060,170186),(197435,173165),(200810,176102),(202495,177584),(204187,179062),(205872,180549),(207564,182032),(210943,184999),(214322,187948),(216012,189430),(217703,190924),(219383,192409),(219393,192417),(221084,193909),(224406,196807),(224459,196856),(224467,196861),(226158,198349),(227850,199842),(231235,202784),(232924,204251),(234620,205745),(238007,208707),(239694,210177),(241386,211665),(241394,211672),(244782,214663),(244783,214664),(248172,217634),(251563,220607),(253257,222090),(254954,223570),(258347,226567),(261740,229550)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check036 :
    PLift (groupData 5497878 261740 3326 3394 g036 points036) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts036 :
    compareNamed primeRoster 19 18 5497878 261740 points036 := by
  decide +kernel

private theorem cover036 : covers 3326 3394 :=
  @groupChecked primeRoster 5000 18 5497878 261740 3326 3394 g036 points036
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check036.down counts036

private def g037 : List Row :=
  [⟨3395,3391,17900,23851⟩,
  ⟨3396,3392,20883,26812⟩,
  ⟨3397,3377,0,29793⟩,
  ⟨3398,3392,23847,32750⟩,
  ⟨3399,3390,22366,35729⟩,
  ⟨3400,3399,37230,38719⟩,
  ⟨3401,3396,34241,41693⟩,
  ⟨3402,3397,37227,44681⟩,
  ⟨3403,3400,43195,47669⟩,
  ⟨3404,3401,46182,50647⟩,
  ⟨3405,3388,28275,53637⟩,
  ⟨3406,3382,20822,56635⟩,
  ⟨3407,3389,32718,59602⟩,
  ⟨3408,3406,59601,62566⟩,
  ⟨3409,3391,38685,65533⟩,
  ⟨3410,3396,47644,68515⟩,
  ⟨3411,3398,52122,71527⟩,
  ⟨3412,3411,73042,74555⟩,
  ⟨3413,3403,62556,77532⟩,
  ⟨3414,3409,73039,80511⟩,
  ⟨3415,3404,67002,83504⟩,
  ⟨3416,3402,65511,86506⟩,
  ⟨3417,3413,83503,89508⟩,
  ⟨3418,3416,89507,92524⟩,
  ⟨3419,3391,53552,95521⟩,
  ⟨3420,3411,85002,98513⟩,
  ⟨3421,3420,100006,101490⟩,
  ⟨3422,3414,92517,104512⟩,
  ⟨3423,3413,92514,107518⟩,
  ⟨3424,3423,109017,110518⟩,
  ⟨3425,3418,103001,113530⟩,
  ⟨3426,3419,106010,116520⟩,
  ⟨3427,3408,90986,119540⟩,
  ⟨3428,3425,118032,122531⟩,
  ⟨3429,3409,95477,125548⟩,
  ⟨3430,3426,122529,128562⟩,
  ⟨3431,3421,116509,131581⟩,
  ⟨3432,3427,127053,134614⟩,
  ⟨3433,3431,134614,137584⟩,
  ⟨3434,3426,128555,140592⟩,
  ⟨3435,3434,142115,143606⟩,
  ⟨3436,3435,145109,146604⟩,
  ⟨3437,3425,131566,149637⟩,
  ⟨3438,3436,149636,152641⟩,
  ⟨3439,3438,154153,155662⟩,
  ⟨3440,3425,136074,158683⟩,
  ⟨3441,3438,157170,161713⟩,
  ⟨3442,3438,158681,164756⟩,
  ⟨3443,3437,158679,167779⟩,
  ⟨3444,3441,166259,170784⟩,
  ⟨3445,3422,139034,173791⟩,
  ⟨3446,3423,142058,176826⟩,
  ⟨3447,3440,169281,179823⟩,
  ⟨3448,3444,176824,182857⟩,
  ⟨3449,3431,158647,185895⟩,
  ⟨3450,3448,185894,188913⟩,
  ⟨3451,3449,188913,191945⟩,
  ⟨3452,3451,193458,194973⟩,
  ⟨3453,3448,190416,197998⟩,
  ⟨3454,3452,197997,200994⟩,
  ⟨3455,3450,196474,204051⟩,
  ⟨3456,3446,191933,207076⟩,
  ⟨3457,3455,207076,210100⟩,
  ⟨3458,3436,179772,213119⟩,
  ⟨3459,3452,205562,216146⟩,
  ⟨3460,3455,211600,219201⟩,
  ⟨3461,3458,217664,222237⟩,
  ⟨3462,3459,220711,225257⟩,
  ⟨3463,3462,226783,228304⟩]

private def points037 : List (ℕ × ℕ) := [(0,0),(20388,17900),(23711,20822),(23781,20883),(25470,22366),(27173,23847),(27178,23851),(30573,26812),(32235,28275),(33970,29793),(37327,32718),(37367,32750),(39063,34241),(40766,35729),(42462,37227),(42465,37230),(44125,38685),(44165,38719),(47566,41693),(49265,43195),(50967,44681),(52667,46182),(54345,47644),(54370,47669),(57773,50647),(59454,52122),(61080,53552),(61178,53637),(64583,56635),(67989,59601),(67990,59602),(71385,62556),(71397,62566),(74781,65511),(74806,65533),(76495,67002),(78215,68515),(81626,71527),(83328,73039),(83331,73042),(85037,74555),(88450,77532),(91863,80511),(95276,83503),(95278,83504),(96975,85002),(98693,86506),(102109,89507),(102110,89508),(103773,90986),(105515,92514),(105519,92517),(105527,92524),(108896,95477),(108946,95521),(112365,98513),(114075,100006),(115786,101490),(117490,103001),(119207,104512),(120912,106010),(122630,107518),(124341,109017),(126053,110518),(129478,113530),(132891,116509),(132903,116520),(134615,118032),(136330,119540),(139755,122529),(139757,122531),(143186,125548),(144897,127053),(146607,128555),(146615,128562),(150028,131566),(150046,131581),(153477,134614),(155165,136074),(156910,137584),(158560,139034),(160343,140592),(161994,142058),(162060,142115),(163778,143606),(165495,145109),(167213,146604),(170649,149636),(170650,149637),(174087,152641),(175806,154153),(177526,155662),(179244,157170),(180925,158647),(180961,158679),(180963,158681),(180965,158683),(184406,161713),(187847,164756),(189567,166259),(191290,167779),(193005,169281),(194733,170784),(198178,173791),(201621,176824),(201623,176826),(205009,179772),(205070,179823),(208517,182857),(211965,185894),(211966,185895),(215415,188913),(217137,190416),(218853,191933),(218866,191945),(220591,193458),(222317,194973),(224040,196474),(225769,197997),(225770,197998),(229223,200994),(232678,204051),(234399,205562),(236133,207076),(239590,210100),(241315,211600),(243047,213119),(246506,216146),(248234,217664),(249965,219201),(251694,220711),(253426,222237),(256887,225257),(258618,226783),(260350,228304)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check037 :
    PLift (groupData 5735835 260350 3395 3463 g037 points037) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts037 :
    compareNamed primeRoster 19 18 5735835 260350 points037 := by
  decide +kernel

private theorem cover037 : covers 3395 3463 :=
  @groupChecked primeRoster 5000 18 5735835 260350 3395 3463 g037 points037
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check037.down counts037

private def g038 : List Row :=
  [⟨3464,3462,9114,12159⟩,
  ⟨3465,3455,0,15212⟩,
  ⟨3466,3462,12158,18251⟩,
  ⟨3467,3466,19754,21277⟩,
  ⟨3468,3453,1499,24342⟩,
  ⟨3469,3467,24342,27392⟩,
  ⟨3470,3466,24340,30427⟩,
  ⟨3471,3468,28907,33473⟩,
  ⟨3472,3466,27388,36521⟩,
  ⟨3473,3454,10599,39542⟩,
  ⟨3474,3473,41063,42601⟩,
  ⟨3475,3474,44132,45647⟩,
  ⟨3476,3475,47176,48703⟩,
  ⟨3477,3475,48703,51761⟩,
  ⟨3478,3468,39530,54833⟩,
  ⟨3479,3477,54833,57891⟩,
  ⟨3480,3454,21199,60932⟩,
  ⟨3481,3480,62446,63976⟩,
  ⟨3482,3481,65502,67032⟩,
  ⟨3483,3476,59401,70105⟩,
  ⟨3484,3482,70104,73149⟩,
  ⟨3485,3484,74671,76187⟩,
  ⟨3486,3483,74670,79246⟩,
  ⟨3487,3478,68550,82309⟩,
  ⟨3488,3453,31817,85380⟩,
  ⟨3489,3487,85380,88438⟩,
  ⟨3490,3479,74659,91515⟩,
  ⟨3491,3490,93045,94562⟩,
  ⟨3492,3489,93044,97639⟩,
  ⟨3493,3486,89965,100710⟩,
  ⟨3494,3487,93039,103779⟩,
  ⟨3495,3493,103779,106825⟩,
  ⟨3496,3488,97632,109895⟩,
  ⟨3497,3496,111435,112955⟩,
  ⟨3498,3493,108358,116010⟩,
  ⟨3499,3494,111432,119093⟩,
  ⟨3500,3498,119092,122173⟩,
  ⟨3501,3490,108348,125257⟩,
  ⟨3502,3501,126781,128321⟩,
  ⟨3503,3489,109875,131397⟩,
  ⟨3504,3501,129856,134459⟩,
  ⟨3505,3502,132922,137549⟩,
  ⟨3506,3504,137548,140615⟩,
  ⟨3507,3501,134456,143688⟩,
  ⟨3508,3507,145231,146756⟩,
  ⟨3509,3506,145230,149803⟩,
  ⟨3510,3500,137540,152883⟩,
  ⟨3511,3510,154418,155975⟩,
  ⟨3512,3507,151347,159064⟩,
  ⟨3513,3510,157526,162165⟩,
  ⟨3514,3512,162164,165257⟩,
  ⟨3515,3513,165257,168333⟩,
  ⟨3516,3501,148261,171402⟩,
  ⟨3517,3488,129765,174433⟩,
  ⟨3518,3509,163714,177546⟩,
  ⟨3519,3517,177546,180622⟩,
  ⟨3520,3518,180621,183732⟩,
  ⟨3521,3518,182174,186809⟩,
  ⟨3522,3521,188359,189897⟩,
  ⟨3523,3467,106482,192965⟩,
  ⟨3524,3521,191439,196064⟩,
  ⟨3525,3522,194516,199157⟩,
  ⟨3526,3515,185249,202259⟩,
  ⟨3527,3479,131144,205359⟩,
  ⟨3528,3527,206903,208444⟩,
  ⟨3529,3527,208444,211542⟩,
  ⟨3530,3529,213102,214640⟩,
  ⟨3531,3527,211540,217749⟩,
  ⟨3532,3529,216179,220846⟩,
  ⟨3533,3532,222386,223942⟩,
  ⟨3534,3507,185183,227041⟩]

private def points038 : List (ℕ × ℕ) := [(0,0),(1714,1499),(10396,9114),(12083,10599),(13858,12158),(13860,12159),(17325,15212),(20790,18251),(22523,19754),(24172,21199),(24257,21277),(27722,24340),(27724,24342),(31188,27388),(31193,27392),(32926,28907),(34662,30427),(36244,31817),(38133,33473),(41604,36521),(45064,39530),(45077,39542),(46813,41063),(48550,42601),(50287,44132),(52025,45647),(53762,47176),(55500,48703),(58977,51761),(62454,54833),(65933,57891),(67666,59401),(69412,60932),(71152,62446),(72893,63976),(74633,65502),(76374,67032),(78105,68550),(79856,70104),(79857,70105),(83340,73149),(85067,74659),(85081,74670),(85082,74671),(86825,76187),(90310,79246),(93797,82309),(97284,85380),(100773,88438),(102511,89965),(104262,91515),(106001,93039),(106006,93044),(106007,93045),(107753,94562),(111236,97632),(111244,97639),(114737,100710),(118230,103779),(121333,106482),(121725,106825),(123457,108348),(123469,108358),(125196,109875),(125220,109895),(126965,111432),(126968,111435),(128717,112955),(132214,116010),(135712,119092),(135713,119093),(139212,122173),(142713,125257),(144463,126781),(146214,128321),(147860,129765),(147964,129856),(149429,131144),(149717,131397),(151467,132922),(153216,134456),(153220,134459),(156712,137540),(156724,137548),(156725,137549),(160230,140615),(163737,143688),(165489,145230),(165490,145231),(167244,146756),(168970,148261),(170753,149803),(172504,151347),(174262,152883),(176017,154418),(177773,155975),(179527,157526),(181284,159064),(184796,162164),(184797,162165),(186543,163714),(188310,165257),(191825,168333),(195340,171402),(198857,174433),(202374,177546),(205892,180621),(205893,180622),(207651,182174),(209412,183732),(211081,185183),(211157,185249),(212933,186809),(214693,188359),(216454,189897),(218214,191439),(219977,192965),(221737,194516),(223500,196064),(227025,199157),(230550,202259),(234077,205359),(235840,206903),(237604,208444),(241131,211540),(241133,211542),(242897,213102),(244662,214640),(246426,216179),(248193,217749),(251724,220846),(253490,222386),(255257,223942),(258790,227041)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check038 :
    PLift (groupData 5985788 258790 3464 3534 g038 points038) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts038 :
    compareNamed primeRoster 19 18 5985788 258790 points038 := by
  decide +kernel

private theorem cover038 : covers 3464 3534 :=
  @groupChecked primeRoster 5000 18 5985788 258790 3464 3534 g038 points038
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check038.down counts038

private def g039 : List Row :=
  [⟨3535,3534,21716,23291⟩,
  ⟨3536,3519,0,26419⟩,
  ⟨3537,3526,12412,29519⟩,
  ⟨3538,3535,27974,32608⟩,
  ⟨3539,3528,18605,35689⟩,
  ⟨3540,3530,23279,38800⟩,
  ⟨3541,3539,38800,41944⟩,
  ⟨3542,3539,40377,45043⟩,
  ⟨3543,3541,45043,48153⟩,
  ⟨3544,3540,45041,51270⟩,
  ⟨3545,3533,35674,54393⟩,
  ⟨3546,3539,46595,57513⟩,
  ⟨3547,3544,55942,60616⟩,
  ⟨3548,3546,60615,63724⟩,
  ⟨3549,3547,63724,66840⟩,
  ⟨3550,3542,57506,69953⟩,
  ⟨3551,3537,51248,73056⟩,
  ⟨3552,3550,73055,76176⟩,
  ⟨3553,3552,77728,79294⟩,
  ⟨3554,3551,77727,82397⟩,
  ⟨3555,3553,82397,85521⟩,
  ⟨3556,3550,79289,88650⟩,
  ⟨3557,3526,43392,91765⟩,
  ⟨3558,3556,91764,94901⟩,
  ⟨3559,3554,90202,98037⟩,
  ⟨3560,3553,90200,101167⟩,
  ⟨3561,3554,93342,104263⟩,
  ⟨3562,3561,105829,107399⟩,
  ⟨3563,3560,105828,110532⟩,
  ⟨3564,3560,107398,113649⟩,
  ⟨3565,3563,113649,116793⟩,
  ⟨3566,3561,112082,119900⟩,
  ⟨3567,3558,108948,123013⟩,
  ⟨3568,3565,121446,126155⟩,
  ⟨3569,3565,123011,129268⟩,
  ⟨3570,3560,116782,132389⟩,
  ⟨3571,3567,129267,135532⟩,
  ⟨3572,3570,135531,138664⟩,
  ⟨3573,3564,127692,141792⟩,
  ⟨3574,3569,137086,144924⟩,
  ⟨3575,3573,144924,148056⟩,
  ⟨3576,3563,130811,151204⟩,
  ⟨3577,3572,146487,154343⟩,
  ⟨3578,3572,148051,157478⟩,
  ⟨3579,3571,148050,160625⟩,
  ⟨3580,3570,148046,163767⟩,
  ⟨3581,3575,157474,166914⟩,
  ⟨3582,3578,163765,170042⟩,
  ⟨3583,3545,113488,173188⟩,
  ⟨3584,3581,171612,176341⟩,
  ⟨3585,3581,173186,179473⟩,
  ⟨3586,3582,176339,182624⟩,
  ⟨3587,3576,168473,185761⟩,
  ⟨3588,3580,176333,188902⟩,
  ⟨3589,3580,177893,192071⟩,
  ⟨3590,3584,185757,195244⟩,
  ⟨3591,3590,196812,198381⟩,
  ⟨3592,3589,196811,201556⟩,
  ⟨3593,3578,181022,204717⟩,
  ⟨3594,3573,174712,207882⟩,
  ⟨3595,3589,201552,211030⟩,
  ⟨3596,3593,209448,214195⟩,
  ⟨3597,3594,212621,217356⟩,
  ⟨3598,3589,206286,220528⟩,
  ⟨3599,3597,220528,223678⟩,
  ⟨3600,3592,214188,226841⟩,
  ⟨3601,3600,228432,230006⟩]

private def points039 : List (ℕ × ℕ) := [(0,0),(14139,12412),(21204,18605),(24753,21716),(26508,23279),(26521,23291),(30056,26419),(31823,27974),(33593,29519),(37130,32608),(40651,35674),(40669,35689),(44208,38800),(45977,40377),(47749,41944),(49399,43392),(51288,45041),(51290,45043),(53055,46595),(54833,48153),(58352,51248),(58376,51270),(61921,54393),(63692,55942),(65458,57506),(65466,57513),(69012,60615),(69013,60616),(72560,63724),(76109,66840),(79658,69953),(83208,73055),(83209,73056),(86760,76176),(88535,77727),(88536,77728),(90308,79289),(90313,79294),(93866,82397),(97421,85521),(100976,88650),(102748,90200),(102751,90202),(104532,91764),(104533,91765),(106305,93342),(108090,94901),(111649,98037),(115208,101167),(118769,104263),(120548,105828),(120549,105829),(122328,107398),(122330,107399),(124101,108948),(125893,110532),(127671,112082),(129276,113488),(129456,113649),(133008,116782),(133021,116793),(136586,119900),(138368,121446),(140151,123011),(140153,123013),(143720,126155),(145494,127692),(147287,129267),(147289,129268),(149052,130811),(150858,132389),(154428,135531),(154429,135532),(156211,137086),(158000,138664),(161573,141792),(165146,144924),(166930,146487),(168708,148046),(168713,148050),(168716,148051),(168721,148056),(172296,151204),(175873,154343),(179446,157474),(179450,157478),(183029,160625),(186606,163765),(186608,163767),(190189,166914),(191964,168473),(193770,170042),(195560,171612),(197351,173186),(197353,173188),(199089,174712),(200928,176333),(200934,176339),(200936,176341),(202718,177893),(204521,179473),(206285,181022),(208106,182624),(211688,185757),(211693,185761),(215280,188902),(218869,192071),(222458,195244),(224252,196811),(224253,196812),(226049,198381),(229636,201552),(229640,201556),(233233,204717),(235019,206286),(236826,207882),(238622,209448),(240421,211030),(242217,212621),(244008,214188),(244016,214195),(247613,217356),(251210,220528),(254809,223678),(258408,226841),(260208,228432),(262009,230006)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check039 :
    PLift (groupData 6221592 262009 3535 3601 g039 points039) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts039 :
    compareNamed primeRoster 19 18 6221592 262009 points039 := by
  decide +kernel

private theorem cover039 : covers 3535 3601 :=
  @groupChecked primeRoster 5000 18 6221592 262009 3535 3601 g039 points039
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check039.down counts039

private def g040 : List Row :=
  [⟨3602,3590,7978,26969⟩,
  ⟨3603,3599,23802,30149⟩,
  ⟨3604,3601,28554,33329⟩,
  ⟨3605,3603,33329,36477⟩,
  ⟨3606,3590,14298,39629⟩,
  ⟨3607,3606,41201,42794⟩,
  ⟨3608,3579,0,45955⟩,
  ⟨3609,3604,41199,49113⟩,
  ⟨3610,3608,49112,52303⟩,
  ⟨3611,3610,53896,55473⟩,
  ⟨3612,3600,39613,58652⟩,
  ⟨3613,3608,53895,61811⟩,
  ⟨3614,3603,47508,65008⟩,
  ⟨3615,3597,39592,68198⟩,
  ⟨3616,3615,69790,71369⟩,
  ⟨3617,3615,71369,74553⟩,
  ⟨3618,3615,72950,77734⟩,
  ⟨3619,3615,74552,80931⟩,
  ⟨3620,3619,82520,84103⟩,
  ⟨3621,3591,39529,87273⟩,
  ⟨3622,3616,80927,90474⟩,
  ⟨3623,3616,82514,93646⟩,
  ⟨3624,3615,82510,96819⟩,
  ⟨3625,3609,74523,99994⟩,
  ⟨3626,3616,87264,103181⟩,
  ⟨3627,3621,96816,106378⟩,
  ⟨3628,3626,106377,109566⟩,
  ⟨3629,3623,103177,112763⟩,
  ⟨3630,3608,80878,115937⟩,
  ⟨3631,3621,103172,119124⟩,
  ⟨3632,3625,111162,122303⟩,
  ⟨3633,3623,109557,125485⟩,
  ⟨3634,3632,125484,128669⟩,
  ⟨3635,3632,127073,131867⟩,
  ⟨3636,3628,122297,135058⟩,
  ⟨3637,3625,119110,138249⟩,
  ⟨3638,3635,136646,141442⟩,
  ⟨3639,3637,141442,144642⟩,
  ⟨3640,3638,144641,147832⟩,
  ⟨3641,3637,144640,151041⟩,
  ⟨3642,3639,149437,154253⟩,
  ⟨3643,3631,138233,157444⟩,
  ⟨3644,3635,146238,160637⟩,
  ⟨3645,3640,155840,163830⟩,
  ⟨3646,3643,162236,167058⟩,
  ⟨3647,3638,155833,170246⟩,
  ⟨3648,3647,171840,173441⟩,
  ⟨3649,3637,157427,176638⟩,
  ⟨3650,3647,175040,179832⟩,
  ⟨3651,3649,179832,183064⟩,
  ⟨3652,3648,179830,186253⟩,
  ⟨3653,3647,179828,189466⟩,
  ⟨3654,3652,189465,192680⟩,
  ⟨3655,3654,194287,195882⟩,
  ⟨3656,3655,197481,199082⟩,
  ⟨3657,3655,199082,202300⟩,
  ⟨3658,3649,191063,205497⟩,
  ⟨3659,3657,205497,208717⟩,
  ⟨3660,3653,200678,211935⟩,
  ⟨3661,3650,197471,215140⟩,
  ⟨3662,3657,210321,218373⟩,
  ⟨3663,3660,216744,221592⟩,
  ⟨3664,3662,221591,224812⟩,
  ⟨3665,3662,223214,228035⟩]

private def points040 : List (ℕ × ℕ) := [(0,0),(9074,7978),(16254,14298),(27083,23802),(30686,26969),(32486,28554),(34289,30149),(37892,33329),(41497,36477),(44990,39529),(45062,39592),(45084,39613),(45102,39629),(46902,41199),(46905,41201),(48709,42794),(52316,45955),(54105,47508),(55924,49112),(55925,49113),(59534,52303),(61336,53895),(61339,53896),(63145,55473),(66756,58652),(70369,61811),(73982,65008),(77597,68198),(79404,69790),(81212,71369),(83019,72950),(84797,74523),(84827,74552),(84829,74553),(88446,77734),(92004,80878),(92060,80927),(92065,80931),(93864,82510),(93868,82514),(93874,82520),(95684,84103),(99292,87264),(99305,87273),(102926,90474),(106549,93646),(110168,96816),(110172,96819),(113797,99994),(117410,103172),(117418,103177),(117422,103181),(121048,106377),(121049,106378),(124664,109557),(124676,109566),(126484,111162),(128305,112763),(131934,115937),(135547,119110),(135565,119124),(139188,122297),(139196,122303),(142828,125484),(142829,125485),(144644,127073),(146462,128669),(150097,131867),(153732,135058),(155549,136646),(157351,138233),(157369,138249),(161006,141442),(164643,144640),(164644,144641),(164645,144642),(166454,146238),(168284,147832),(170103,149437),(171925,151041),(175566,154253),(177377,155833),(177384,155840),(179191,157427),(179209,157444),(182852,160637),(184673,162236),(186497,163830),(190142,167058),(193789,170246),(195612,171840),(197436,173441),(199259,175040),(201085,176638),(204730,179828),(204732,179830),(204734,179832),(208385,183064),(212036,186253),(215688,189465),(215689,189466),(217505,191063),(219342,192680),(221169,194287),(222997,195882),(224809,197471),(224824,197481),(226652,199082),(228474,200678),(230309,202300),(233966,205497),(237625,208717),(239451,210321),(241284,211935),(244945,215140),(246774,216744),(248606,218373),(252268,221591),(252269,221592),(254099,223214),(255932,224812),(259597,228035)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check040 :
    PLift (groupData 6456516 259597 3602 3665 g040 points040) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts040 :
    compareNamed primeRoster 19 18 6456516 259597 points040 := by
  decide +kernel

private theorem cover040 : covers 3602 3665 :=
  @groupChecked primeRoster 5000 18 6456516 259597 3602 3665 g040 points040
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check040.down counts040

private def g041 : List Row :=
  [⟨3666,3662,6512,12933⟩,
  ⟨3667,3662,8122,16187⟩,
  ⟨3668,3665,14557,19412⟩,
  ⟨3669,3662,11326,22625⟩,
  ⟨3670,3668,22624,25863⟩,
  ⟨3671,3669,25863,29095⟩,
  ⟨3672,3660,12916,32315⟩,
  ⟨3673,3672,33912,35550⟩,
  ⟨3674,3665,24249,38765⟩,
  ⟨3675,3649,0,41992⟩,
  ⟨3676,3664,25848,45233⟩,
  ⟨3677,3675,45233,48453⟩,
  ⟨3678,3675,46850,51690⟩,
  ⟨3679,3676,50076,54922⟩,
  ⟨3680,3679,56537,58154⟩,
  ⟨3681,3666,37121,61400⟩,
  ⟨3682,3669,43598,64634⟩,
  ⟨3683,3682,66244,67863⟩,
  ⟨3684,3679,63007,71094⟩,
  ⟨3685,3666,43578,74333⟩,
  ⟨3686,3685,75954,77570⟩,
  ⟨3687,3683,74331,80798⟩,
  ⟨3688,3681,72720,84045⟩,
  ⟨3689,3652,27327,87257⟩,
  ⟨3690,3680,74324,90493⟩,
  ⟨3691,3688,88866,93742⟩,
  ⟨3692,3677,72700,96983⟩,
  ⟨3693,3688,92106,100222⟩,
  ⟨3694,3692,100221,103466⟩,
  ⟨3695,3686,92100,106717⟩,
  ⟨3696,3687,95374,109943⟩,
  ⟨3697,3688,98590,113188⟩,
  ⟨3698,3696,113187,116424⟩,
  ⟨3699,3697,116424,119674⟩,
  ⟨3700,3694,113184,122911⟩,
  ⟨3701,3700,124551,126175⟩,
  ⟨3702,3680,93690,129425⟩,
  ⟨3703,3698,124548,132683⟩,
  ⟨3704,3701,131051,135924⟩,
  ⟨3705,3702,134306,139187⟩,
  ⟨3706,3705,140814,142444⟩,
  ⟨3707,3681,103394,145706⟩,
  ⟨3708,3700,135918,148961⟩,
  ⟨3709,3708,150574,152188⟩,
  ⟨3710,3709,153849,155477⟩,
  ⟨3711,3709,155477,158739⟩,
  ⟨3712,3704,148956,162015⟩,
  ⟨3713,3704,150568,165248⟩,
  ⟨3714,3713,166861,168485⟩,
  ⟨3715,3700,147320,171770⟩,
  ⟨3716,3715,173397,175028⟩,
  ⟨3717,3708,163619,178293⟩,
  ⟨3718,3717,179918,181554⟩,
  ⟨3719,3718,183189,184822⟩,
  ⟨3720,3716,181552,188111⟩,
  ⟨3721,3715,181550,191352⟩,
  ⟨3722,3720,191351,194606⟩,
  ⟨3723,3722,196250,197883⟩,
  ⟨3724,3723,199512,201163⟩,
  ⟨3725,3716,189725,204419⟩,
  ⟨3726,3725,206056,207690⟩,
  ⟨3727,3726,209316,210953⟩,
  ⟨3728,3726,210952,214223⟩,
  ⟨3729,3722,206051,217482⟩,
  ⟨3730,3728,217481,220754⟩,
  ⟨3731,3730,222394,224019⟩,
  ⟨3732,3714,197847,227302⟩]

private def points041 : List (ℕ × ℕ) := [(0,0),(7408,6512),(9239,8122),(12901,11326),(14722,12916),(14740,12933),(16572,14557),(18407,16187),(22074,19412),(25742,22624),(25743,22625),(27567,24249),(29394,25848),(29412,25863),(31076,27327),(33083,29095),(36754,32315),(38590,33912),(40427,35550),(42235,37121),(44100,38765),(47775,41992),(49567,43578),(49591,43598),(51450,45233),(53287,46850),(55127,48453),(56964,50076),(58804,51690),(62483,54922),(64322,56537),(66162,58154),(69843,61400),(71680,63007),(73524,64634),(75365,66244),(77207,67863),(80890,71094),(82704,72700),(82726,72720),(84562,74324),(84573,74331),(84575,74333),(86417,75954),(88260,77570),(91947,80798),(95634,84045),(99323,87257),(101166,88866),(103012,90493),(104847,92100),(104854,92106),(106642,93690),(106703,93742),(108538,95374),(110394,96983),(112230,98590),(114086,100221),(114087,100222),(117696,103394),(117780,103466),(121475,106717),(125170,109943),(128862,113184),(128866,113187),(128867,113188),(132564,116424),(136263,119674),(139962,122911),(141809,124548),(141812,124551),(143663,126175),(147364,129425),(149214,131051),(151067,132683),(152917,134306),(154762,135918),(154770,135924),(158475,139187),(160327,140814),(162180,142444),(165887,145706),(167712,147320),(169586,148956),(169594,148961),(171438,150568),(171448,150574),(173303,152188),(175157,153849),(177012,155477),(180723,158739),(184434,162015),(186280,163619),(188147,165248),(190003,166861),(191860,168485),(195575,171770),(197432,173397),(199290,175028),(203007,178293),(204865,179918),(206720,181550),(206722,181552),(206724,181554),(208583,183189),(210443,184822),(214162,188111),(216012,189725),(217882,191351),(217883,191352),(221604,194606),(223465,196250),(225286,197847),(225327,197883),(227188,199512),(229050,201163),(232775,204419),(234631,206051),(234637,206056),(236500,207690),(238363,209316),(240226,210952),(240227,210953),(243954,214223),(247682,217481),(247683,217482),(251412,220754),(253277,222394),(255143,224019),(258874,227302)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check041 :
    PLift (groupData 6705038 258874 3666 3732 g041 points041) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts041 :
    compareNamed primeRoster 19 18 6705038 258874 points041 := by
  decide +kernel

private theorem cover041 : covers 3666 3732 :=
  @groupChecked primeRoster 5000 18 6705038 258874 3666 3732 g041 points041
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check041.down counts041

private def g042 : List Row :=
  [⟨3733,3723,0,16378⟩,
  ⟨3734,3726,6535,19660⟩,
  ⟨3735,3722,1622,22947⟩,
  ⟨3736,3734,22946,26249⟩,
  ⟨3737,3733,22945,29538⟩,
  ⟨3738,3737,31178,32824⟩,
  ⟨3739,3729,19649,36123⟩,
  ⟨3740,3735,31175,39408⟩,
  ⟨3741,3726,18006,42721⟩,
  ⟨3742,3730,26233,46002⟩,
  ⟨3743,3742,47651,49284⟩,
  ⟨3744,3738,42716,52587⟩,
  ⟨3745,3734,37746,55867⟩,
  ⟨3746,3732,36101,59142⟩,
  ⟨3747,3742,54236,62451⟩,
  ⟨3748,3747,64099,65740⟩,
  ⟨3749,3736,47632,69044⟩,
  ⟨3750,3746,65738,72331⟩,
  ⟨3751,3707,3057,75650⟩,
  ⟨3752,3751,77279,78932⟩,
  ⟨3753,3752,80569,82205⟩,
  ⟨3754,3747,73989,85507⟩,
  ⟨3755,3753,85507,88813⟩,
  ⟨3756,3755,90462,92113⟩,
  ⟨3757,3750,83861,95390⟩,
  ⟨3758,3755,93742,98696⟩,
  ⟨3759,3758,100351,101990⟩,
  ⟨3760,3758,101989,105300⟩,
  ⟨3761,3751,92103,108597⟩,
  ⟨3762,3756,101985,111910⟩,
  ⟨3763,3762,113559,115212⟩,
  ⟨3764,3760,111908,118525⟩,
  ⟨3765,3764,120178,121834⟩,
  ⟨3766,3763,120177,125153⟩,
  ⟨3767,3760,116854,128468⟩,
  ⟨3768,3757,113547,131798⟩,
  ⟨3769,3767,131798,135118⟩,
  ⟨3770,3768,135117,138424⟩,
  ⟨3771,3770,140079,141724⟩,
  ⟨3772,3771,143389,145048⟩,
  ⟨3773,3759,125131,148355⟩,
  ⟨3774,3764,135107,151666⟩,
  ⟨3775,3754,120130,154979⟩,
  ⟨3776,3774,154978,158293⟩,
  ⟨3777,3765,141709,161604⟩,
  ⟨3778,3776,161603,164938⟩,
  ⟨3779,3775,161602,168231⟩,
  ⟨3780,3777,166587,171548⟩,
  ⟨3781,3774,163262,174877⟩,
  ⟨3782,3775,166582,178210⟩,
  ⟨3783,3781,178210,181530⟩,
  ⟨3784,3783,183192,184833⟩,
  ⟨3785,3783,184833,188187⟩,
  ⟨3786,3783,186512,191500⟩,
  ⟨3787,3785,191500,194824⟩,
  ⟨3788,3764,158232,198157⟩,
  ⟨3789,3786,196487,201438⟩,
  ⟨3790,3787,199792,204768⟩,
  ⟨3791,3787,201436,208107⟩,
  ⟨3792,3791,209772,211427⟩,
  ⟨3793,3790,209771,214742⟩,
  ⟨3794,3773,183141,218069⟩,
  ⟨3795,3792,216408,221400⟩,
  ⟨3796,3795,223077,224746⟩,
  ⟨3797,3781,201408,228083⟩]

private def points042 : List (ℕ × ℕ) := [(0,0),(1855,1622),(3499,3057),(7462,6535),(18665,16378),(20503,18006),(22386,19649),(22398,19660),(26131,22945),(26132,22946),(26133,22947),(29850,26233),(29868,26249),(33605,29538),(35470,31175),(35473,31178),(37342,32824),(41056,36101),(41081,36123),(42935,37746),(44820,39408),(48556,42716),(48561,42721),(52302,46002),(54152,47632),(54173,47651),(56045,49284),(59788,52587),(61657,54236),(63533,55867),(67278,59142),(71025,62451),(72898,64099),(74770,65738),(74772,65740),(78521,69044),(82270,72331),(84139,73989),(86021,75650),(87896,77279),(89772,78932),(91648,80569),(93525,82205),(95395,83861),(97278,85507),(101033,88813),(102910,90462),(104776,92103),(104788,92113),(106665,93742),(108545,95390),(112302,98696),(114181,100351),(116056,101985),(116060,101989),(116061,101990),(119820,105300),(123581,108597),(127340,111908),(127342,111910),(129208,113547),(129223,113559),(131105,115212),(132980,116854),(134868,118525),(136695,120130),(136749,120177),(136750,120178),(138633,121834),(142374,125131),(142398,125153),(146165,128468),(149932,131798),(153688,135107),(153700,135117),(153701,135118),(157470,138424),(159355,140079),(161223,141709),(161241,141724),(163126,143389),(165012,145048),(168785,148355),(172558,151666),(176332,154978),(176333,154979),(180036,158232),(180108,158293),(183883,161602),(183884,161603),(183885,161604),(185767,163262),(187662,164938),(189545,166582),(189550,166587),(191441,168231),(195220,171548),(199001,174877),(202782,178210),(206565,181530),(208401,183141),(208456,183192),(210348,184833),(212239,186512),(214133,188187),(217918,191500),(221705,194824),(223597,196487),(225492,198157),(227385,199792),(229249,201408),(229279,201436),(229281,201438),(233070,204768),(236861,208107),(238755,209771),(238756,209772),(240652,211427),(244445,214742),(246340,216408),(248238,218069),(252033,221400),(253930,223077),(255828,224746),(259625,228083)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check042 :
    PLift (groupData 6948980 259625 3733 3797 g042 points042) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts042 :
    compareNamed primeRoster 19 18 6948980 259625 points042 := by
  decide +kernel

private theorem cover042 : covers 3733 3797 :=
  @groupChecked primeRoster 5000 18 6948980 259625 3733 3797 g042 points042
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check042.down counts042

private def g043 : List Row :=
  [⟨3798,3779,0,31672⟩,
  ⟨3799,3797,31672,35008⟩,
  ⟨3800,3795,30007,38356⟩,
  ⟨3801,3799,38356,41694⟩,
  ⟨3802,3801,43365,45033⟩,
  ⟨3803,3798,40020,48365⟩,
  ⟨3804,3797,40017,51724⟩,
  ⟨3805,3803,51724,55066⟩,
  ⟨3806,3791,33318,58396⟩,
  ⟨3807,3802,53392,61747⟩,
  ⟨3808,3805,60074,65113⟩,
  ⟨3809,3807,65113,68465⟩,
  ⟨3810,3801,56710,71816⟩,
  ⟨3811,3810,73495,75168⟩,
  ⟨3812,3788,38291,78504⟩,
  ⟨3813,3803,65102,81858⟩,
  ⟨3814,3785,36591,85205⟩,
  ⟨3815,3814,86890,88565⟩,
  ⟨3816,3781,33211,91910⟩,
  ⟨3817,3807,78495,95271⟩,
  ⟨3818,3817,96937,98613⟩,
  ⟨3819,3792,56640,101950⟩,
  ⟨3820,3819,103635,105312⟩,
  ⟨3821,3820,106989,108661⟩,
  ⟨3822,3815,100278,112028⟩,
  ⟨3823,3811,95256,115405⟩,
  ⟨3824,3799,76761,118782⟩,
  ⟨3825,3822,117078,122143⟩,
  ⟨3826,3824,122142,125507⟩,
  ⟨3827,3824,123824,128874⟩,
  ⟨3828,3825,127184,132243⟩,
  ⟨3829,3825,128872,135619⟩,
  ⟨3830,3823,127179,138971⟩,
  ⟨3831,3797,85083,142337⟩,
  ⟨3832,3824,132235,145674⟩,
  ⟨3833,3829,142335,149054⟩,
  ⟨3834,3826,138964,152439⟩,
  ⟨3835,3834,154126,155803⟩,
  ⟨3836,3835,157492,159171⟩,
  ⟨3837,3835,159171,162545⟩,
  ⟨3838,3830,152431,165906⟩,
  ⟨3839,3837,165906,169282⟩,
  ⟨3840,3838,169281,172660⟩,
  ⟨3841,3836,167592,176032⟩,
  ⟨3842,3827,154104,179402⟩,
  ⟨3843,3838,174350,182777⟩,
  ⟨3844,3843,184456,186121⟩,
  ⟨3845,3839,179398,189510⟩,
  ⟨3846,3828,162507,192880⟩,
  ⟨3847,3828,164193,196277⟩,
  ⟨3848,3831,170938,199643⟩,
  ⟨3849,3843,192876,203042⟩,
  ⟨3850,3827,167533,206427⟩,
  ⟨3851,3830,174304,209809⟩,
  ⟨3852,3847,204727,213194⟩,
  ⟨3853,3850,211498,216545⟩,
  ⟨3854,3841,197950,219964⟩,
  ⟨3855,3848,211493,223349⟩,
  ⟨3856,3852,219962,226745⟩,
  ⟨3857,3847,213185,230131⟩]

private def points043 : List (ℕ × ℕ) := [(0,0),(34179,30007),(36081,31672),(37827,33211),(37952,33318),(39880,35008),(41674,36591),(43607,38291),(43679,38356),(45573,40017),(45576,40020),(47480,41694),(49380,43365),(51281,45033),(55084,48365),(58887,51724),(60786,53392),(62692,55066),(64503,56640),(64584,56710),(66497,58396),(68399,60074),(70304,61747),(74099,65102),(74111,65113),(77920,68465),(81729,71816),(83634,73495),(85540,75168),(87367,76761),(89339,78495),(89351,78504),(93164,81858),(96833,85083),(96977,85205),(98884,86890),(100792,88565),(104607,91910),(108406,95256),(108424,95271),(110332,96937),(112241,98613),(114144,100278),(116060,101950),(117969,103635),(119879,105312),(121789,106989),(123700,108661),(127521,112028),(131344,115405),(133254,117078),(135167,118782),(138991,122142),(138992,122143),(140903,123824),(142817,125507),(144724,127179),(144729,127184),(146642,128872),(146644,128874),(150463,132235),(150471,132243),(154300,135619),(158121,138964),(158129,138971),(161958,142335),(161960,142337),(165791,145674),(169624,149054),(173449,152431),(173457,152439),(175346,154104),(175374,154126),(177292,155803),(179209,157492),(181127,159171),(184923,162507),(184964,162545),(186837,164193),(188801,165906),(190654,167533),(190717,167592),(192639,169281),(192640,169282),(194523,170938),(196479,172660),(198344,174304),(198396,174350),(200320,176032),(204157,179398),(204161,179402),(208004,182777),(209925,184456),(211847,186121),(215692,189510),(219533,192876),(219537,192880),(223384,196277),(225286,197950),(227231,199643),(231080,203042),(233001,204727),(234929,206427),(238780,209809),(240699,211493),(240704,211498),(242619,213185),(242631,213194),(246484,216545),(250335,219962),(250337,219964),(254192,223349),(258047,226745),(261904,230131)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check043 :
    PLift (groupData 7176321 261904 3798 3857 g043 points043) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts043 :
    compareNamed primeRoster 19 18 7176321 261904 points043 := by
  decide +kernel

private theorem cover043 : covers 3798 3857 :=
  @groupChecked primeRoster 5000 18 7176321 261904 3798 3857 g043 points043
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check043.down counts043

private def g044 : List Row :=
  [⟨3858,3827,0,52556⟩,
  ⟨3859,3858,54247,55944⟩,
  ⟨3860,3856,52554,59333⟩,
  ⟨3861,3851,45747,62741⟩,
  ⟨3862,3861,64438,66136⟩,
  ⟨3863,3858,61025,69530⟩,
  ⟨3864,3847,44020,72935⟩,
  ⟨3865,3864,74633,76339⟩,
  ⟨3866,3861,71247,79719⟩,
  ⟨3867,3831,21905,83092⟩,
  ⟨3868,3867,84797,86532⟩,
  ⟨3869,3866,84796,89947⟩,
  ⟨3870,3863,81400,93348⟩,
  ⟨3871,3870,95048,96755⟩,
  ⟨3872,3864,86525,100152⟩,
  ⟨3873,3872,101845,103559⟩,
  ⟨3874,3858,79687,106960⟩,
  ⟨3875,3863,89929,110382⟩,
  ⟨3876,3875,112072,113777⟩,
  ⟨3877,3862,91619,117170⟩,
  ⟨3878,3870,106952,120585⟩,
  ⟨3879,3878,122277,123988⟩,
  ⟨3880,3858,89890,127391⟩,
  ⟨3881,3871,113766,130814⟩,
  ⟨3882,3876,123984,134221⟩,
  ⟨3883,3870,115448,137639⟩,
  ⟨3884,3883,139363,141066⟩,
  ⟨3885,3880,135945,144471⟩,
  ⟨3886,3876,130803,147882⟩,
  ⟨3887,3858,101755,151314⟩,
  ⟨3888,3878,137627,154726⟩,
  ⟨3889,3881,144465,158144⟩,
  ⟨3890,3881,146177,161569⟩,
  ⟨3891,3887,158142,164983⟩,
  ⟨3892,3890,164982,168417⟩,
  ⟨3893,3886,159855,171844⟩,
  ⟨3894,3889,166705,175253⟩,
  ⟨3895,3879,151283,178646⟩,
  ⟨3896,3879,152988,182083⟩,
  ⟨3897,3893,178644,185527⟩,
  ⟨3898,3896,185526,188961⟩,
  ⟨3899,3876,152960,192406⟩,
  ⟨3900,3892,182076,195829⟩,
  ⟨3901,3892,183800,199256⟩,
  ⟨3902,3900,199255,202696⟩,
  ⟨3903,3888,180347,206109⟩,
  ⟨3904,3901,204418,209541⟩,
  ⟨3905,3896,197543,212963⟩,
  ⟨3906,3905,214683,216397⟩,
  ⟨3907,3889,188926,219818⟩,
  ⟨3908,3905,218113,223248⟩,
  ⟨3909,3901,212956,226679⟩,
  ⟨3910,3894,202668,230115⟩]

private def points044 : List (ℕ × ℕ) := [(0,0),(24956,21905),(50121,44020),(52073,45747),(59797,52554),(59799,52556),(61728,54247),(63658,55944),(67517,59333),(69444,61025),(71378,62741),(73308,64438),(75239,66136),(79102,69530),(81030,71247),(82965,72935),(84897,74633),(86830,76339),(90663,79687),(90695,79719),(92622,81400),(94562,83092),(96494,84796),(96495,84797),(98421,86525),(98429,86532),(102237,89890),(102280,89929),(102298,89947),(104204,91619),(106167,93348),(108102,95048),(110038,96755),(113909,100152),(115740,101755),(115845,101845),(117782,103559),(121647,106952),(121655,106960),(125530,110382),(127467,112072),(129393,113766),(129405,113777),(131322,115448),(133282,117170),(137159,120585),(139098,122277),(141033,123984),(141038,123988),(144917,127391),(148785,130803),(148798,130814),(152679,134221),(154617,135945),(156549,137627),(156562,137639),(158503,139363),(160445,141066),(164322,144465),(164330,144471),(166262,146177),(168215,147882),(172070,151283),(172102,151314),(173979,152960),(174009,152988),(175989,154726),(179876,158142),(179878,158144),(181816,159855),(183767,161569),(187657,164982),(187658,164983),(189600,166705),(191549,168417),(195442,171844),(199335,175253),(203228,178644),(203230,178646),(205149,180347),(207117,182076),(207125,182083),(209063,183800),(211021,185526),(211022,185527),(214879,188926),(214919,188961),(218818,192406),(222717,195829),(224657,197543),(226617,199255),(226618,199256),(230487,202668),(230519,202696),(232469,204418),(234422,206109),(238325,209541),(242222,212956),(242230,212963),(244182,214683),(246135,216397),(248087,218113),(250042,219818),(253949,223248),(257858,226679),(261767,230115)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check044 :
    PLift (groupData 7382283 261767 3858 3910 g044 points044) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts044 :
    compareNamed primeRoster 19 18 7382283 261767 points044 := by
  decide +kernel

private theorem cover044 : covers 3858 3910 :=
  @groupChecked primeRoster 5000 18 7382283 261767 3858 3910 g044 points044
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check044.down counts044

private def g045 : List Row :=
  [⟨3911,3910,27457,29180⟩,
  ⟨3912,3893,0,32615⟩,
  ⟨3913,3911,32615,36067⟩,
  ⟨3914,3912,36066,39489⟩,
  ⟨3915,3906,27449,42936⟩,
  ⟨3916,3898,15404,46395⟩,
  ⟨3917,3902,23991,49836⟩,
  ⟨3918,3904,29159,53272⟩,
  ⟨3919,3904,30874,56710⟩,
  ⟨3920,3919,58423,60154⟩,
  ⟨3921,3911,46386,63620⟩,
  ⟨3922,3909,44645,67089⟩,
  ⟨3923,3913,53261,70537⟩,
  ⟨3924,3906,42896,74001⟩,
  ⟨3925,3924,75741,77463⟩,
  ⟨3926,3924,77462,80921⟩,
  ⟨3927,3919,70529,84358⟩,
  ⟨3928,3926,84357,87828⟩,
  ⟨3929,3928,89557,91295⟩,
  ⟨3930,3929,93020,94744⟩,
  ⟨3931,3923,84353,98216⟩,
  ⟨3932,3931,99925,101662⟩,
  ⟨3933,3926,93015,105118⟩,
  ⟨3934,3924,91282,108569⟩,
  ⟨3935,3933,108569,112041⟩,
  ⟨3936,3930,105113,115494⟩,
  ⟨3937,3932,110295,118951⟩,
  ⟨3938,3935,117224,122398⟩,
  ⟨3939,3937,122398,125846⟩,
  ⟨3940,3936,122396,129305⟩,
  ⟨3941,3940,131026,132770⟩,
  ⟨3942,3940,132769,136220⟩,
  ⟨3943,3942,137965,139696⟩,
  ⟨3944,3937,131021,143156⟩,
  ⟨3945,3939,136216,146604⟩,
  ⟨3946,3945,148339,150073⟩,
  ⟨3947,3933,129283,153551⟩,
  ⟨3948,3940,143148,157027⟩,
  ⟨3949,3948,158736,160472⟩,
  ⟨3950,3948,160471,163958⟩,
  ⟨3951,3940,148325,167423⟩,
  ⟨3952,3941,151803,170892⟩,
  ⟨3953,3951,170892,174384⟩,
  ⟨3954,3952,174383,177846⟩,
  ⟨3955,3944,162198,181330⟩,
  ⟨3956,3951,176108,184811⟩,
  ⟨3957,3951,177842,188284⟩,
  ⟨3958,3955,186551,191749⟩,
  ⟨3959,3956,190027,195233⟩,
  ⟨3960,3940,163913,198720⟩,
  ⟨3961,3948,179566,202204⟩,
  ⟨3962,3958,198718,205695⟩,
  ⟨3963,3959,202202,209175⟩,
  ⟨3964,3958,202199,212652⟩,
  ⟨3965,3964,214384,216140⟩,
  ⟨3966,3957,203933,219643⟩,
  ⟨3967,3962,214382,223129⟩,
  ⟨3968,3964,219641,226610⟩,
  ⟨3969,3962,217880,230105⟩]

private def points045 : List (ℕ × ℕ) := [(0,0),(17576,15404),(27359,23991),(31287,27449),(31297,27457),(33228,29159),(33253,29180),(35180,30874),(37164,32615),(41076,36066),(41077,36067),(44990,39489),(48864,42896),(48905,42936),(50841,44645),(52808,46386),(52820,46395),(56737,49836),(60642,53261),(60654,53272),(64573,56710),(66532,58423),(68492,60154),(72413,63620),(76334,67089),(80249,70529),(80257,70537),(84180,74001),(86142,75741),(88104,77462),(88105,77463),(92030,80921),(95949,84353),(95956,84357),(95957,84358),(99884,87828),(101848,89557),(103800,91282),(103813,91295),(105771,93015),(105777,93020),(107742,94744),(111673,98216),(113638,99925),(115604,101662),(119532,105113),(119537,105118),(123470,108569),(125434,110295),(127405,112041),(131340,115494),(133307,117224),(135277,118951),(139212,122396),(139214,122398),(143153,125846),(147068,129283),(147092,129305),(149056,131021),(149062,131026),(151032,132769),(151033,132770),(154970,136216),(154974,136220),(156945,137965),(158917,139696),(162852,143148),(162860,143156),(166805,146604),(168762,148325),(168777,148339),(170750,150073),(172708,151803),(174697,153551),(178644,157027),(180618,158736),(182592,160471),(182593,160472),(184552,162198),(186492,163913),(186542,163958),(190493,167423),(194444,170892),(198396,174383),(198397,174384),(200370,176108),(202346,177842),(202350,177846),(204306,179566),(206305,181330),(210260,184811),(212237,186551),(214217,188284),(216194,190027),(218174,191749),(222133,195233),(226090,198718),(226092,198720),(230048,202199),(230051,202202),(230053,202204),(232023,203933),(234014,205695),(237977,209175),(241940,212652),(243919,214382),(243922,214384),(245905,216140),(247881,217880),(249868,219641),(249870,219643),(253837,223129),(257804,226610),(261773,230105)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check045 :
    PLift (groupData 7614708 261773 3911 3969 g045 points045) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts045 :
    compareNamed primeRoster 19 18 7614708 261773 points045 := by
  decide +kernel

private theorem cover045 : covers 3911 3969 :=
  @groupChecked primeRoster 5000 18 7614708 261773 3911 3969 g045 points045
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check045.down counts045

private def g046 : List Row :=
  [⟨3970,3964,0,10471⟩,
  ⟨3971,3966,5222,13957⟩,
  ⟨3972,3970,13956,17465⟩,
  ⟨3973,3972,19205,20951⟩,
  ⟨3974,3972,20950,24467⟩,
  ⟨3975,3974,26213,27968⟩,
  ⟨3976,3964,10455,31460⟩,
  ⟨3977,3959,3452,34962⟩,
  ⟨3978,3973,29718,38462⟩,
  ⟨3979,3978,40203,41952⟩,
  ⟨3980,3978,41951,45444⟩,
  ⟨3981,3967,24445,48939⟩,
  ⟨3982,3979,47192,52408⟩,
  ⟨3983,3981,52408,55900⟩,
  ⟨3984,3983,57654,59405⟩,
  ⟨3985,3984,61152,62894⟩,
  ⟨3986,3985,64648,66400⟩,
  ⟨3987,3983,62892,69929⟩,
  ⟨3988,3967,36670,73431⟩,
  ⟨3989,3976,54138,76946⟩,
  ⟨3990,3987,75181,80457⟩,
  ⟨3991,3973,52376,83946⟩,
  ⟨3992,3980,66382,87447⟩,
  ⟨3993,3990,85703,90974⟩,
  ⟨3994,3968,48864,94499⟩,
  ⟨3995,3994,96249,98014⟩,
  ⟨3996,3985,82183,101514⟩,
  ⟨3997,3996,103268,105028⟩,
  ⟨3998,3997,106790,108550⟩,
  ⟨3999,3997,108550,112062⟩,
  ⟨4000,3999,113822,115571⟩,
  ⟨4001,3984,89177,119107⟩,
  ⟨4002,3996,112058,122635⟩,
  ⟨4003,4001,122635,126147⟩,
  ⟨4004,3997,117339,129654⟩,
  ⟨4005,4004,131419,133195⟩,
  ⟨4006,3998,122628,136719⟩,
  ⟨4007,4006,138487,140268⟩,
  ⟨4008,4007,142036,143801⟩,
  ⟨4009,4008,145548,147302⟩,
  ⟨4010,4006,143799,150810⟩,
  ⟨4011,4005,143797,154349⟩,
  ⟨4012,3996,129626,157889⟩,
  ⟨4013,4012,159646,161412⟩,
  ⟨4014,4008,154344,164953⟩,
  ⟨4015,4012,163194,168484⟩,
  ⟨4016,4005,152574,172005⟩,
  ⟨4017,4003,150786,175546⟩,
  ⟨4018,4016,175545,179060⟩,
  ⟨4019,4004,156101,182613⟩,
  ⟨4020,4019,184379,186162⟩,
  ⟨4021,4019,186162,189704⟩,
  ⟨4022,4021,191465,193249⟩,
  ⟨4023,4021,193249,196793⟩,
  ⟨4024,4022,196792,200329⟩,
  ⟨4025,4023,200329,203863⟩,
  ⟨4026,4016,189695,207384⟩,
  ⟨4027,4003,168418,210915⟩,
  ⟨4028,4025,209152,214461⟩,
  ⟨4029,4028,216235,218011⟩,
  ⟨4030,4028,218010,221537⟩,
  ⟨4031,4003,175460,225091⟩,
  ⟨4032,4004,178971,228638⟩]

private def points046 : List (ℕ × ℕ) := [(0,0),(3932,3452),(5953,5222),(11892,10455),(11910,10471),(15880,13956),(15881,13957),(19852,17465),(21838,19205),(23824,20950),(23825,20951),(27774,24445),(27798,24467),(29785,26213),(31773,27968),(33757,29718),(35748,31460),(39725,34962),(41658,36670),(43702,38462),(45691,40203),(47680,41951),(47681,41952),(51660,45444),(53649,47192),(55556,48864),(55641,48939),(59582,52376),(59622,52408),(61592,54138),(63605,55900),(65596,57654),(67588,59405),(69580,61152),(71571,62892),(71573,62894),(73565,64648),(75540,66382),(75558,66400),(79545,69929),(83532,73431),(85525,75181),(87521,76946),(91510,80457),(93490,82183),(95501,83946),(97495,85703),(99492,87447),(101452,89177),(103485,90974),(107478,94499),(109475,96249),(111473,98014),(115468,101514),(117466,103268),(119465,105028),(121463,106790),(123462,108550),(127456,112058),(127461,112062),(129460,113822),(131460,115571),(133454,117339),(135461,119107),(139454,122628),(139462,122635),(143465,126147),(147436,129626),(147468,129654),(149470,131419),(151473,133195),(155478,136719),(157481,138487),(159485,140268),(161488,142036),(163488,143797),(163490,143799),(163492,143801),(165496,145548),(167501,147302),(171486,150786),(171510,150810),(173500,152574),(175516,154344),(175521,154349),(177498,156101),(179532,157889),(181538,159646),(183545,161412),(185550,163194),(187558,164953),(191501,168418),(191573,168484),(195588,172005),(199507,175460),(199604,175545),(199605,175546),(203524,178971),(203622,179060),(207641,182613),(209650,184379),(211660,186162),(215668,189695),(215681,189704),(217691,191465),(219702,193249),(223724,196792),(223725,196793),(227748,200329),(231773,203863),(235798,207384),(237810,209152),(239825,210915),(243852,214461),(245866,216235),(247880,218010),(247881,218011),(251910,221537),(255941,225091),(259972,228638)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check046 :
    PLift (groupData 7868540 259972 3970 4032 g046 points046) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts046 :
    compareNamed primeRoster 19 18 7868540 259972 points046 := by
  decide +kernel

private theorem cover046 : covers 3970 4032 :=
  @groupChecked primeRoster 5000 18 7868540 259972 3970 4032 g046 points046
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check046.down counts046

private def g047 : List Row :=
  [⟨4033,4030,32111,37418⟩,
  ⟨4034,4021,17904,40956⟩,
  ⟨4035,4034,42732,44521⟩,
  ⟨4036,4035,46298,48065⟩,
  ⟨4037,4032,42730,51606⟩,
  ⟨4038,4014,12561,55150⟩,
  ⟨4039,4008,3702,58704⟩,
  ⟨4040,4038,58703,62280⟩,
  ⟨4041,4027,40935,65851⟩,
  ⟨4042,4037,60487,69411⟩,
  ⟨4043,4028,46273,72983⟩,
  ⟨4044,4027,46266,76529⟩,
  ⟨4045,4043,76529,80107⟩,
  ⟨4046,4044,80106,83661⟩,
  ⟨4047,3998,0,87219⟩,
  ⟨4048,4033,64033,90776⟩,
  ⟨4049,4048,92554,94338⟩,
  ⟨4050,4047,92553,97895⟩,
  ⟨4051,4048,96119,101469⟩,
  ⟨4052,4049,99677,105028⟩,
  ⟨4053,4049,101468,108565⟩,
  ⟨4054,4041,88981,112129⟩,
  ⟨4055,4054,113912,115701⟩,
  ⟨4056,4032,76468,119283⟩,
  ⟨4057,4044,99657,122865⟩,
  ⟨4058,4047,106791,126421⟩,
  ⟨4059,4057,126421,129989⟩,
  ⟨4060,4059,131768,133557⟩,
  ⟨4061,4056,128206,137110⟩,
  ⟨4062,4059,135340,140676⟩,
  ⟨4063,4056,131763,144251⟩,
  ⟨4064,4059,138889,147832⟩,
  ⟨4065,4064,149629,151405⟩,
  ⟨4066,4065,153206,155006⟩,
  ⟨4067,4062,149627,158572⟩,
  ⟨4068,4057,142448,162175⟩,
  ⟨4069,4063,155003,165763⟩,
  ⟨4070,4067,163971,169343⟩,
  ⟨4071,4068,167552,172932⟩,
  ⟨4072,4068,169341,176514⟩,
  ⟨4073,4055,147797,180081⟩,
  ⟨4074,4070,176513,183652⟩,
  ⟨4075,4065,169332,187230⟩,
  ⟨4076,4068,176507,190808⟩,
  ⟨4077,4071,183648,194380⟩,
  ⟨4078,4077,196188,197998⟩,
  ⟨4079,4072,189009,201577⟩,
  ⟨4080,4073,192587,205158⟩,
  ⟨4081,4070,189002,208737⟩,
  ⟨4082,4075,199778,212332⟩,
  ⟨4083,4082,214137,215922⟩,
  ⟨4084,4080,212330,219515⟩,
  ⟨4085,4080,214134,223110⟩,
  ⟨4086,4078,212326,226697⟩,
  ⟨4087,4083,223108,230315⟩]

private def points047 : List (ℕ × ℕ) := [(0,0),(4203,3702),(14313,12561),(20404,17904),(36542,32111),(42592,37418),(46601,40935),(46625,40956),(48639,42730),(48642,42732),(50660,44521),(52641,46266),(52649,46273),(52677,46298),(54695,48065),(58732,51606),(62769,55150),(66807,58703),(66808,58704),(68824,60487),(70847,62280),(72839,64033),(74888,65851),(78929,69411),(82972,72983),(86943,76468),(87015,76529),(91059,80106),(91060,80107),(95105,83661),(99152,87219),(101154,88981),(103199,90776),(105222,92553),(105223,92554),(107248,94338),(109271,96119),(111297,97895),(113301,99657),(113321,99677),(115346,101468),(115348,101469),(119399,105028),(121410,106791),(123452,108565),(127505,112129),(129532,113912),(131560,115701),(135615,119283),(139672,122865),(143729,126421),(145755,128206),(147788,129989),(149811,131763),(149817,131768),(151847,133557),(153876,135340),(155908,137110),(157935,138889),(159969,140676),(161985,142448),(164032,144251),(168055,147797),(168095,147832),(170124,149627),(170127,149629),(172160,151405),(174192,153206),(176221,155003),(176225,155006),(180292,158572),(184359,162175),(186392,163971),(188428,165763),(190461,167552),(192485,169332),(192495,169341),(192497,169343),(196568,172932),(200631,176507),(200637,176513),(200639,176514),(204712,180081),(208781,183648),(208785,183652),(212860,187230),(214882,189002),(214891,189009),(216935,190808),(218967,192587),(221012,194380),(223050,196188),(225089,197998),(227122,199778),(229168,201577),(233247,205158),(237328,208737),(241401,212326),(241407,212330),(241409,212332),(243447,214134),(243450,214137),(245492,215922),(249575,219515),(253658,223108),(253660,223110),(257745,226697),(261832,230315)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check047 :
    PLift (groupData 8089953 261832 4033 4087 g047 points047) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts047 :
    compareNamed primeRoster 19 18 8089953 261832 points047 := by
  decide +kernel

private theorem cover047 : covers 4033 4087 :=
  @groupChecked primeRoster 5000 18 8089953 261832 4033 4087 g047 points047
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check047.down counts047

private def g048 : List Row :=
  [⟨4088,4087,5427,7220⟩,
  ⟨4089,4086,5426,10817⟩,
  ⟨4090,4084,3624,14411⟩,
  ⟨4091,4081,0,17996⟩,
  ⟨4092,4084,7214,21585⟩,
  ⟨4093,4081,3612,25201⟩,
  ⟨4094,4090,21583,28788⟩,
  ⟨4095,4088,19787,32397⟩,
  ⟨4096,4095,34195,35992⟩,
  ⟨4097,4095,35992,39598⟩,
  ⟨4098,4097,41407,43185⟩,
  ⟨4099,4088,26976,46780⟩,
  ⟨4100,4094,39594,50401⟩,
  ⟨4101,4090,34181,53988⟩,
  ⟨4102,4101,55787,57599⟩,
  ⟨4103,4097,50398,61226⟩,
  ⟨4104,4101,59415,64832⟩,
  ⟨4105,4083,28736,68454⟩,
  ⟨4106,4105,70265,72079⟩,
  ⟨4107,4102,66629,75684⟩,
  ⟨4108,4102,68449,79286⟩,
  ⟨4109,4107,79286,82916⟩,
  ⟨4110,4103,73854,86542⟩,
  ⟨4111,4109,86542,90154⟩,
  ⟨4112,4110,90153,93756⟩,
  ⟨4113,4102,77474,97383⟩,
  ⟨4114,4108,90149,101008⟩,
  ⟨4115,4100,77463,104625⟩,
  ⟨4116,4110,97379,108246⟩,
  ⟨4117,4110,99175,111852⟩,
  ⟨4118,4117,113644,115440⟩,
  ⟨4119,4116,113643,119061⟩,
  ⟨4120,4119,120883,122686⟩,
  ⟨4121,4119,122686,126298⟩,
  ⟨4122,4118,122684,129937⟩,
  ⟨4123,4121,129937,133551⟩,
  ⟨4124,4116,122678,137177⟩,
  ⟨4125,4117,126293,140796⟩,
  ⟨4126,4125,142610,144422⟩,
  ⟨4127,4113,122663,148041⟩,
  ⟨4128,4126,148040,151681⟩,
  ⟨4129,4126,149860,155321⟩,
  ⟨4130,4118,137161,158978⟩,
  ⟨4131,4124,149857,162593⟩,
  ⟨4132,4129,160778,166219⟩,
  ⟨4133,4130,164402,169851⟩,
  ⟨4134,4131,168030,173498⟩,
  ⟨4135,4128,164399,177125⟩,
  ⟨4136,4134,177124,180773⟩,
  ⟨4137,4131,173495,184417⟩,
  ⟨4138,4131,175299,188049⟩,
  ⟨4139,4134,182578,191695⟩,
  ⟨4140,4131,178932,195341⟩,
  ⟨4141,4140,197178,198992⟩,
  ⟨4142,4141,200831,202645⟩,
  ⟨4143,4140,200830,206302⟩,
  ⟨4144,4140,202643,209964⟩,
  ⟨4145,4144,211787,213621⟩,
  ⟨4146,4139,204467,217285⟩,
  ⟨4147,4139,206294,220931⟩,
  ⟨4148,4145,219099,224588⟩,
  ⟨4149,4142,215446,228259⟩]

private def points048 : List (ℕ × ℕ) := [(0,0),(4081,3612),(4094,3624),(6141,5426),(6142,5427),(8178,7214),(8186,7220),(12275,10817),(16364,14411),(20455,17996),(22494,19787),(24544,21583),(24546,21585),(28639,25201),(30670,26976),(32672,28736),(32732,28788),(36827,32397),(38859,34181),(38874,34195),(40922,35992),(45014,39594),(45019,39598),(47067,41407),(49116,43185),(53215,46780),(57310,50398),(57314,50401),(61415,53988),(63465,55787),(65516,57599),(67566,59415),(69619,61226),(73722,64832),(75771,66629),(77822,68449),(77827,68454),(79879,70265),(81932,72079),(83979,73854),(86039,75684),(88064,77463),(88077,77474),(90146,79286),(94255,82916),(98364,86542),(102470,90149),(102474,90153),(102475,90154),(106586,93756),(110694,97379),(110699,97383),(112749,99175),(114812,101008),(118927,104625),(123042,108246),(127159,111852),(129216,113643),(129217,113644),(131276,115440),(135395,119061),(137454,120883),(139490,122663),(139506,122678),(139512,122684),(139514,122686),(143627,126293),(143635,126298),(147756,129937),(151879,133551),(155984,137161),(156002,137177),(160127,140796),(162189,142610),(164252,144422),(168378,148040),(168379,148041),(170436,149857),(170441,149860),(172506,151681),(176635,155321),(180764,158978),(182828,160778),(184895,162593),(186954,164399),(186959,164402),(189026,166219),(191091,168030),(193159,169851),(197288,173495),(197292,173498),(199353,175299),(201426,177124),(201427,177125),(203484,178932),(205562,180773),(207627,182578),(209699,184417),(213836,188049),(217975,191695),(222114,195341),(224184,197178),(226255,198992),(228324,200830),(228325,200831),(230394,202643),(230396,202645),(232461,204467),(234531,206294),(234539,206302),(238682,209964),(240754,211787),(242827,213621),(244893,215446),(246972,217285),(249044,219099),(251119,220931),(255266,224588),(259415,228259)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check048 :
    PLift (groupData 8347686 259415 4088 4149 g048 points048) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts048 :
    compareNamed primeRoster 19 18 8347686 259415 points048 := by
  decide +kernel

private theorem cover048 : covers 4088 4149 :=
  @groupChecked primeRoster 5000 18 8347686 259415 4088 4149 g048 points048
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check048.down counts048

private def g049 : List Row :=
  [⟨4150,4143,18530,31334⟩,
  ⟨4151,4145,24020,34980⟩,
  ⟨4152,4141,18522,38617⟩,
  ⟨4153,4131,2031,42277⟩,
  ⟨4154,4153,44112,45950⟩,
  ⟨4155,4137,16685,49597⟩,
  ⟨4156,4155,51439,53260⟩,
  ⟨4157,4154,51438,56917⟩,
  ⟨4158,4139,25818,60568⟩,
  ⟨4159,4152,51433,64213⟩,
  ⟨4160,4157,62395,67862⟩,
  ⟨4161,4160,69696,71526⟩,
  ⟨4162,4161,73344,75154⟩,
  ⟨4163,4149,53237,78797⟩,
  ⟨4164,4161,76973,82480⟩,
  ⟨4165,4162,80623,86132⟩,
  ⟨4166,4117,0,89804⟩,
  ⟨4167,4160,80618,93482⟩,
  ⟨4168,4167,95327,97160⟩,
  ⟨4169,4167,97160,100820⟩,
  ⟨4170,4168,100819,104490⟩,
  ⟨4171,4170,106325,108160⟩,
  ⟨4172,4158,86112,111805⟩,
  ⟨4173,4167,104486,115456⟩,
  ⟨4174,4172,115455,119138⟩,
  ⟨4175,4162,98984,122821⟩,
  ⟨4176,4173,120982,126495⟩,
  ⟨4177,4169,115450,130159⟩,
  ⟨4178,4170,119131,133846⟩,
  ⟨4179,4178,135689,137538⟩,
  ⟨4180,4164,111780,141201⟩,
  ⟨4181,4178,139368,144853⟩,
  ⟨4182,4180,144852,148531⟩,
  ⟨4183,4175,137532,152201⟩,
  ⟨4184,4178,144848,155851⟩,
  ⟨4185,4181,152199,159550⟩,
  ⟨4186,4172,137516,163247⟩,
  ⟨4187,4181,155848,166928⟩,
  ⟨4188,4181,157696,170621⟩,
  ⟨4189,4185,166926,174295⟩,
  ⟨4190,4176,152178,177969⟩,
  ⟨4191,4182,165085,181676⟩,
  ⟨4192,4188,177967,185342⟩,
  ⟨4193,4182,168762,189035⟩,
  ⟨4194,4181,168756,192718⟩,
  ⟨4195,4184,176105,196411⟩,
  ⟨4196,4191,190867,200126⟩,
  ⟨4197,4191,192715,203819⟩,
  ⟨4198,4196,203818,207513⟩,
  ⟨4199,4189,192708,211200⟩,
  ⟨4200,4182,181638,214877⟩,
  ⟨4201,4195,207510,218582⟩,
  ⟨4202,4193,205666,222306⟩,
  ⟨4203,4190,201961,226024⟩,
  ⟨4204,4189,201956,229719⟩]

private def points049 : List (ℕ × ℕ) := [(0,0),(2311,2031),(18907,16685),(21005,18522),(21014,18530),(27237,24020),(29270,25818),(35539,31334),(39690,34980),(43841,38617),(47994,42277),(50070,44112),(52147,45950),(56302,49597),(58373,51433),(58378,51438),(58379,51439),(60433,53237),(60457,53260),(64614,56917),(68771,60568),(70849,62395),(72930,64213),(77089,67862),(79169,69696),(81250,71526),(83330,73344),(85411,75154),(87491,76973),(89574,78797),(91649,80618),(91654,80623),(93737,82480),(97877,86112),(97902,86132),(102067,89804),(106234,93482),(108317,95327),(110401,97160),(112464,98984),(114569,100819),(114570,100820),(118735,104486),(118739,104490),(120824,106325),(122910,108160),(127049,111780),(127081,111805),(131246,115450),(131253,115455),(131254,115456),(135419,119131),(135427,119138),(137513,120982),(139602,122821),(143777,126495),(147954,130159),(152131,133846),(154220,135689),(156285,137516),(156302,137532),(156310,137538),(158398,139368),(160489,141201),(164665,144848),(164669,144852),(164670,144853),(168851,148531),(173009,152178),(173032,152199),(173034,152201),(177213,155848),(177217,155851),(179303,157696),(181402,159550),(185587,163247),(187670,165085),(189772,166926),(189774,166928),(191846,168756),(191852,168762),(193961,170621),(198150,174295),(200229,176105),(202337,177967),(202339,177969),(206489,181638),(206530,181676),(210721,185342),(214914,189035),(217007,190867),(219095,192708),(219103,192715),(219107,192718),(223302,196411),(227497,200126),(229567,201956),(229574,201961),(231693,203818),(231694,203819),(233782,205666),(235887,207510),(235891,207513),(240090,211200),(244289,214877),(248490,218582),(252691,222306),(256894,226024),(261097,229719)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check049 :
    PLift (groupData 8575711 261097 4150 4204 g049 points049) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts049 :
    compareNamed primeRoster 19 18 8575711 261097 points049 := by
  decide +kernel

private theorem cover049 : covers 4150 4204 :=
  @groupChecked primeRoster 5000 18 8575711 261097 4150 4204 g049 points049
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check049.down counts049

private def g050 : List Row :=
  [⟨4205,4196,9633,26335⟩,
  ⟨4206,4199,17052,30026⟩,
  ⟨4207,4193,7760,33718⟩,
  ⟨4208,4206,33717,37416⟩,
  ⟨4209,4207,37416,41146⟩,
  ⟨4210,4200,26323,44842⟩,
  ⟨4211,4206,39280,48549⟩,
  ⟨4212,4205,39277,52266⟩,
  ⟨4213,4202,35563,55994⟩,
  ⟨4214,4209,50401,59713⟩,
  ⟨4215,4214,61571,63428⟩,
  ⟨4216,4210,55990,67139⟩,
  ⟨4217,4212,61568,70834⟩,
  ⟨4218,4214,67137,74512⟩,
  ⟨4219,4218,76357,78234⟩,
  ⟨4220,4215,72684,81945⟩,
  ⟨4221,4220,83800,85670⟩,
  ⟨4222,4220,85669,89388⟩,
  ⟨4223,4222,91259,93114⟩,
  ⟨4224,4222,93113,96846⟩,
  ⟨4225,4219,89384,100570⟩,
  ⟨4226,4207,68938,104302⟩,
  ⟨4227,4219,93106,107987⟩,
  ⟨4228,4226,107986,111705⟩,
  ⟨4229,4167,0,115438⟩,
  ⟨4230,4225,109851,119167⟩,
  ⟨4231,4228,117297,122883⟩,
  ⟨4232,4230,122882,126623⟩,
  ⟨4233,4210,87474,130363⟩,
  ⟨4234,4232,130362,134075⟩,
  ⟨4235,4233,134075,137811⟩,
  ⟨4236,4235,139654,141509⟩,
  ⟨4237,4235,141509,145223⟩,
  ⟨4238,4218,111662,148941⟩,
  ⟨4239,4209,96749,152653⟩,
  ⟨4240,4235,147069,156380⟩,
  ⟨4241,4234,147066,160099⟩,
  ⟨4242,4241,161968,163838⟩,
  ⟨4243,4230,143359,167568⟩,
  ⟨4244,4242,167567,171320⟩,
  ⟨4245,4237,160092,175061⟩,
  ⟨4246,4241,169444,178810⟩,
  ⟨4247,4245,178810,182548⟩,
  ⟨4248,4245,180691,186302⟩,
  ⟨4249,4248,188186,190048⟩,
  ⟨4250,4235,165674,193770⟩,
  ⟨4251,4231,160056,197545⟩,
  ⟨4252,4250,197544,201287⟩,
  ⟨4253,4245,190041,205066⟩,
  ⟨4254,4251,203157,208795⟩,
  ⟨4255,4243,190031,212524⟩,
  ⟨4256,4252,208793,216274⟩,
  ⟨4257,4238,184377,220030⟩,
  ⟨4258,4236,182495,223776⟩,
  ⟨4259,4258,225656,227529⟩]

private def points050 : List (ℕ × ℕ) := [(0,0),(8854,7760),(10968,9633),(19375,17052),(29878,26323),(29891,26335),(34096,30026),(38302,33717),(38303,33718),(40391,35563),(42510,37416),(44608,39277),(44611,39280),(46719,41146),(50928,44842),(55139,48549),(57241,50401),(59350,52266),(63558,55990),(63563,55994),(67776,59713),(69880,61568),(69883,61571),(71991,63428),(76204,67137),(76206,67139),(78269,68938),(80423,70834),(82528,72684),(84640,74512),(86749,76357),(88859,78234),(93078,81945),(95188,83800),(97298,85669),(97299,85670),(99343,87474),(101516,89384),(101520,89388),(103631,91259),(105735,93106),(105742,93113),(105743,93114),(109854,96749),(109966,96846),(114191,100570),(118416,104302),(122642,107986),(122643,107987),(124753,109851),(126820,111662),(126870,111705),(131099,115438),(133212,117297),(135328,119167),(139558,122882),(139559,122883),(143790,126623),(148022,130362),(148023,130363),(152256,134075),(156491,137811),(158608,139654),(160726,141509),(162823,143359),(164963,145223),(167075,147066),(167078,147069),(169200,148941),(173439,152653),(177678,156380),(181869,160056),(181911,160092),(181919,160099),(184039,161968),(186160,163838),(188253,165674),(190402,167567),(190403,167568),(192521,169444),(194646,171320),(198891,175061),(203136,178810),(205258,180691),(207322,182495),(207383,182548),(209461,184377),(211630,186302),(213754,188186),(215861,190031),(215871,190041),(215879,190048),(220128,193770),(224378,197544),(224379,197545),(228630,201287),(230755,203157),(232883,205066),(237134,208793),(237136,208795),(241391,212524),(245646,216274),(249903,220030),(254160,223776),(256289,225656),(258419,227529)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check050 :
    PLift (groupData 8811122 258419 4205 4259 g050 points050) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts050 :
    compareNamed primeRoster 19 18 8811122 258419 points050 := by
  decide +kernel

private theorem cover050 : covers 4205 4259 :=
  @groupChecked primeRoster 5000 18 8811122 258419 4205 4259 g050 points050
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check050.down counts050

private def g051 : List Row :=
  [⟨4260,4258,5635,9374⟩,
  ⟨4261,4257,5634,13143⟩,
  ⟨4262,4259,11249,16903⟩,
  ⟨4263,4258,11247,20656⟩,
  ⟨4264,4251,0,24409⟩,
  ⟨4265,4261,20655,28194⟩,
  ⟨4266,4263,26303,31945⟩,
  ⟨4267,4264,30061,35705⟩,
  ⟨4268,4260,24401,39462⟩,
  ⟨4269,4252,11216,43206⟩,
  ⟨4270,4268,43205,46952⟩,
  ⟨4271,4270,48817,50676⟩,
  ⟨4272,4270,50675,54444⟩,
  ⟨4273,4266,45098,58207⟩,
  ⟨4274,4265,45094,61946⟩,
  ⟨4275,4271,58205,65724⟩,
  ⟨4276,4263,45085,69472⟩,
  ⟨4277,4273,65722,73237⟩,
  ⟨4278,4271,63824,77008⟩,
  ⟨4279,4275,73235,80754⟩,
  ⟨4280,4276,77006,84515⟩,
  ⟨4281,4261,50631,88274⟩,
  ⟨4282,4280,88273,92052⟩,
  ⟨4283,4281,92052,95826⟩,
  ⟨4284,4283,97716,99601⟩,
  ⟨4285,4280,93925,103409⟩,
  ⟨4286,4279,93922,107176⟩,
  ⟨4287,4286,109073,110960⟩,
  ⟨4288,4285,109072,114731⟩,
  ⟨4289,4281,103403,118520⟩,
  ⟨4290,4284,110955,122282⟩,
  ⟨4291,4289,122282,126050⟩,
  ⟨4292,4291,127924,129819⟩,
  ⟨4293,4283,114720,133628⟩,
  ⟨4294,4293,135519,137397⟩,
  ⟨4295,4281,114710,141162⟩,
  ⟨4296,4295,143067,144958⟩,
  ⟨4297,4295,144958,148732⟩,
  ⟨4298,4295,146857,152543⟩,
  ⟨4299,4286,131703,156346⟩,
  ⟨4300,4298,156345,160136⟩,
  ⟨4301,4300,162026,163926⟩,
  ⟨4302,4274,114649,167726⟩,
  ⟨4303,4288,143040,171516⟩,
  ⟨4304,4302,171515,175316⟩,
  ⟨4305,4301,171515,179092⟩,
  ⟨4306,4256,87994,182881⟩,
  ⟨4307,4292,158203,186683⟩,
  ⟨4308,4304,182879,190464⟩,
  ⟨4309,4304,184779,194269⟩,
  ⟨4310,4307,192378,198046⟩,
  ⟨4311,4310,199954,201841⟩,
  ⟨4312,4302,186672,205623⟩,
  ⟨4313,4302,188559,209424⟩,
  ⟨4314,4309,203724,213220⟩,
  ⟨4315,4302,192360,217017⟩,
  ⟨4316,4300,190437,220806⟩,
  ⟨4317,4307,205612,224606⟩,
  ⟨4318,4314,220805,228408⟩]

private def points051 : List (ℕ × ℕ) := [(0,0),(6407,5634),(6408,5635),(10668,9374),(12762,11216),(12795,11247),(12797,11249),(14929,13143),(19190,16903),(23451,20655),(23453,20656),(27708,24401),(27716,24409),(29847,26303),(31981,28194),(34112,30061),(36246,31945),(40513,35705),(44780,39462),(49048,43205),(49049,43206),(51162,45085),(51173,45094),(51177,45098),(53318,46952),(55453,48817),(57539,50631),(57588,50675),(57589,50676),(61860,54444),(66131,58205),(66133,58207),(70406,61946),(72537,63824),(74679,65722),(74681,65724),(78956,69472),(83231,73235),(83233,73237),(87508,77006),(87510,77008),(91789,80754),(96068,84515),(100036,87994),(100348,88273),(100349,88274),(104630,92052),(106765,93922),(106768,93925),(108913,95826),(111054,97716),(113196,99601),(117473,103403),(117481,103409),(121766,107176),(123908,109072),(123909,109073),(126048,110955),(126053,110960),(130242,114649),(130316,114710),(130328,114720),(130340,114731),(134629,118520),(138918,122282),(143209,126050),(145354,127924),(147500,129819),(149625,131703),(151793,133628),(153939,135519),(156086,137397),(160381,141162),(162500,143040),(162528,143067),(164676,144958),(166823,146857),(168973,148732),(173270,152543),(177568,156345),(177569,156346),(179690,158203),(181868,160136),(184018,162026),(186169,163926),(190470,167726),(194771,171515),(194772,171515),(194773,171516),(199076,175316),(203381,179092),(207684,182879),(207686,182881),(209836,184779),(211980,186672),(211993,186683),(214131,188559),(216268,190437),(216300,190464),(218433,192360),(218453,192378),(220609,194269),(224918,198046),(227073,199954),(229229,201841),(231381,203724),(233528,205612),(233540,205623),(237853,209424),(242166,213220),(246481,217017),(250794,220805),(250796,220806),(255113,224606),(259430,228408)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check051 :
    PLift (groupData 9063132 259430 4260 4318 g051 points051) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts051 :
    compareNamed primeRoster 19 18 9063132 259430 points051 := by
  decide +kernel

private theorem cover051 : covers 4260 4318 :=
  @groupChecked primeRoster 5000 18 9063132 259430 4260 4318 g051 points051
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check051.down counts051

private def g052 : List Row :=
  [⟨4319,4286,0,62683⟩,
  ⟨4320,4317,60789,66482⟩,
  ⟨4321,4320,68381,70279⟩,
  ⟨4322,4320,70278,74097⟩,
  ⟨4323,4319,70277,77946⟩,
  ⟨4324,4323,79846,81745⟩,
  ⟨4325,4317,70271,85572⟩,
  ⟨4326,4325,87460,89366⟩,
  ⟨4327,4326,91271,93194⟩,
  ⟨4328,4322,85567,96984⟩,
  ⟨4329,4321,85564,100769⟩,
  ⟨4330,4318,81729,104588⟩,
  ⟨4331,4324,95082,108394⟩,
  ⟨4332,4328,104586,112199⟩,
  ⟨4333,4329,108392,116007⟩,
  ⟨4334,4329,110297,119843⟩,
  ⟨4335,4330,114115,123646⟩,
  ⟨4336,4333,121756,127487⟩,
  ⟨4337,4334,125578,131311⟩,
  ⟨4338,4336,131310,135149⟩,
  ⟨4339,4334,129395,138952⟩,
  ⟨4340,4335,133226,142773⟩,
  ⟨4341,4336,137054,146604⟩,
  ⟨4342,4325,117893,150403⟩,
  ⟨4343,4331,131293,154232⟩,
  ⟨4344,4326,123608,158041⟩,
  ⟨4345,4344,159956,161878⟩,
  ⟨4346,4341,156144,165726⟩,
  ⟨4347,4328,133185,169563⟩,
  ⟨4348,4337,152308,173403⟩,
  ⟨4349,4317,115898,177239⟩,
  ⟨4350,4347,175330,181068⟩,
  ⟨4351,4347,177238,184879⟩,
  ⟨4352,4342,169553,188692⟩,
  ⟨4353,4343,173393,192525⟩,
  ⟨4354,4352,192524,196357⟩,
  ⟨4355,4336,163752,200188⟩,
  ⟨4356,4350,192520,204045⟩,
  ⟨4357,4338,171433,207888⟩,
  ⟨4358,4356,207887,211698⟩,
  ⟨4359,4340,179103,215545⟩,
  ⟨4360,4351,202112,219399⟩,
  ⟨4361,4343,188658,223228⟩,
  ⟨4362,4353,209773,227093⟩]

private def points052 : List (ℕ × ℕ) := [(0,0),(69103,60789),(71264,62683),(75583,66482),(77743,68381),(79896,70271),(79902,70277),(79903,70278),(79904,70279),(84225,74097),(88548,77946),(90709,79846),(92853,81729),(92871,81745),(97188,85564),(97191,85567),(97196,85572),(99358,87460),(101521,89366),(103684,91271),(105848,93194),(108005,95082),(110175,96984),(114504,100769),(118831,104586),(118833,104588),(123162,108392),(123164,108394),(125326,110297),(127495,112199),(129658,114115),(131700,115898),(131828,116007),(133958,117893),(136161,119843),(138327,121756),(140455,123608),(140496,123646),(142662,125578),(144831,127487),(146996,129395),(149150,131293),(149167,131310),(149168,131311),(151291,133185),(151333,133226),(153505,135149),(155671,137054),(157844,138952),(162183,142773),(166524,146604),(170865,150403),(173021,152308),(175208,154232),(177376,156144),(179551,158041),(181723,159956),(183896,161878),(186023,163752),(188241,165726),(192575,169553),(192588,169563),(194716,171433),(196923,173393),(196935,173403),(199108,175330),(201282,177238),(201284,177239),(203413,179103),(205633,181068),(209984,184879),(214295,188658),(214335,188692),(218683,192520),(218687,192524),(218688,192525),(223041,196357),(227396,200188),(229563,202112),(231751,204045),(236107,207887),(236108,207888),(238276,209773),(240465,211698),(244824,215545),(249183,219399),(253544,223228),(257905,227093)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check052 :
    PLift (groupData 9255617 257905 4319 4362 g052 points052) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts052 :
    compareNamed primeRoster 19 18 9255617 257905 points052 := by
  decide +kernel

private theorem cover052 : covers 4319 4362 :=
  @groupChecked primeRoster 5000 18 9255617 257905 4319 4362 g052 points052
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check052.down counts052

private def g053 : List Row :=
  [⟨4363,4355,0,15371⟩,
  ⟨4364,4363,17303,19214⟩,
  ⟨4365,4364,21136,23056⟩,
  ⟨4366,4364,23055,26912⟩,
  ⟨4367,4366,28852,30773⟩,
  ⟨4368,4364,26911,34616⟩,
  ⟨4369,4365,30771,38448⟩,
  ⟨4370,4362,26905,42304⟩,
  ⟨4371,4358,21117,46170⟩,
  ⟨4372,4368,42302,50033⟩,
  ⟨4373,4367,42300,53860⟩,
  ⟨4374,4370,50031,57728⟩,
  ⟨4375,4370,51955,61574⟩,
  ⟨4376,4369,51953,65422⟩,
  ⟨4377,4376,67358,69266⟩,
  ⟨4378,4372,61570,73133⟩,
  ⟨4379,4376,71197,76997⟩,
  ⟨4380,4379,78936,80855⟩,
  ⟨4381,4378,78936,84711⟩,
  ⟨4382,4381,86638,88552⟩,
  ⟨4383,4382,90481,92446⟩,
  ⟨4384,4383,94368,96309⟩,
  ⟨4385,4384,98242,100172⟩,
  ⟨4386,4383,98241,104033⟩,
  ⟨4387,4386,105981,107898⟩,
  ⟨4388,4377,90466,111757⟩,
  ⟨4389,4386,109830,115617⟩,
  ⟨4390,4380,100161,119494⟩,
  ⟨4391,4385,111753,123359⟩,
  ⟨4392,4355,55639,127242⟩,
  ⟨4393,4378,102081,131106⟩,
  ⟨4394,4393,133033,134953⟩,
  ⟨4395,4394,136894,138821⟩,
  ⟨4396,4360,72990,142681⟩,
  ⟨4397,4387,127231,146559⟩,
  ⟨4398,4390,134945,150438⟩,
  ⟨4399,4390,136885,154330⟩,
  ⟨4400,4387,133014,158181⟩,
  ⟨4401,4394,148495,162052⟩,
  ⟨4402,4394,150431,165940⟩,
  ⟨4403,4402,167874,169795⟩,
  ⟨4404,4398,162048,173663⟩,
  ⟨4405,4404,175618,177564⟩,
  ⟨4406,4405,179491,181425⟩,
  ⟨4407,4406,183367,185288⟩,
  ⟨4408,4402,177560,189187⟩,
  ⟨4409,4400,175608,193056⟩,
  ⟨4410,4409,194979,196927⟩,
  ⟨4411,4403,185281,200814⟩,
  ⟨4412,4407,194976,204715⟩,
  ⟨4413,4411,204715,208607⟩,
  ⟨4414,4406,196920,212477⟩,
  ⟨4415,4413,212477,216401⟩,
  ⟨4416,4409,206654,220287⟩,
  ⟨4417,4409,208599,224180⟩,
  ⟨4418,4412,216397,228068⟩]

private def points053 : List (ℕ × ℕ) := [(0,0),(17452,15371),(19633,17303),(21815,19214),(23976,21117),(23997,21136),(26179,23055),(26180,23056),(30537,26905),(30543,26911),(30545,26912),(32728,28852),(34910,30771),(34912,30773),(39279,34616),(43648,38448),(48013,42300),(48015,42302),(48017,42304),(52388,46170),(56757,50031),(56759,50033),(58939,51953),(58942,51955),(61132,53860),(63147,55639),(65505,57728),(69875,61570),(69880,61574),(74255,65422),(76443,67358),(78632,69266),(80819,71197),(82847,72990),(83009,73133),(87388,76997),(89576,78936),(89577,78936),(91767,80855),(96148,84711),(98338,86638),(100529,88552),(102705,90466),(102720,90481),(104912,92446),(107103,94368),(109295,96309),(111486,98241),(111487,98242),(113667,100161),(113680,100172),(115844,102081),(118065,104033),(120258,105981),(122452,107898),(124644,109830),(126835,111753),(126839,111757),(131228,115617),(135617,119494),(140008,123359),(144387,127231),(144399,127242),(148792,131106),(150967,133014),(150988,133033),(153177,134945),(153185,134953),(155372,136885),(155382,136894),(157580,138821),(161975,142681),(166372,146559),(168564,148495),(170761,150431),(170769,150438),(175168,154330),(179567,158181),(183963,162048),(183968,162052),(188369,165940),(190570,167874),(192772,169795),(197175,173663),(199367,175608),(199377,175618),(201575,177560),(201580,177564),(203782,179491),(205985,181425),(208188,183367),(210384,185281),(210392,185288),(214799,189187),(219208,193056),(221409,194976),(221412,194979),(223609,196920),(223617,196927),(228028,200814),(232439,204715),(234639,206654),(236844,208599),(236852,208607),(241265,212477),(245675,216397),(245680,216401),(250095,220287),(254512,224180),(258929,228068)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check053 :
    PLift (groupData 9500433 258929 4363 4418 g053 points053) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts053 :
    compareNamed primeRoster 19 18 9500433 258929 points053 := by
  decide +kernel

private theorem cover053 : covers 4363 4418 :=
  @groupChecked primeRoster 5000 18 9500433 258929 4363 4418 g053 points053
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check053.down counts053

private def g054 : List Row :=
  [⟨4419,4414,1949,11694⟩,
  ⟨4420,4412,0,15591⟩,
  ⟨4421,4416,9742,19492⟩,
  ⟨4422,4413,5840,23398⟩,
  ⟨4423,4419,19490,27315⟩,
  ⟨4424,4415,13633,31208⟩,
  ⟨4425,4420,25356,35136⟩,
  ⟨4426,4424,35135,39040⟩,
  ⟨4427,4425,39040,42926⟩,
  ⟨4428,4427,44877,46808⟩,
  ⟨4429,4428,48761,50725⟩,
  ⟨4430,4429,52655,54607⟩,
  ⟨4431,4423,42919,58506⟩,
  ⟨4432,4426,50720,62415⟩,
  ⟨4433,4421,42909,66340⟩,
  ⟨4434,4430,62413,70248⟩,
  ⟨4435,4434,72204,74139⟩,
  ⟨4436,4432,70246,78057⟩,
  ⟨4437,4436,80017,81973⟩,
  ⟨4438,4429,68279,85867⟩,
  ⟨4439,4424,60442,89768⟩,
  ⟨4440,4432,78050,93667⟩,
  ⟨4441,4438,91718,97593⟩,
  ⟨4442,4434,85860,101517⟩,
  ⟨4443,4439,97591,105428⟩,
  ⟨4444,4443,107380,109325⟩,
  ⟨4445,4403,31015,113241⟩,
  ⟨4446,4442,109324,117153⟩,
  ⟨4447,4446,119103,121064⟩,
  ⟨4448,4444,117151,124996⟩,
  ⟨4449,4441,113234,128887⟩,
  ⟨4450,4443,119098,132800⟩,
  ⟨4451,4449,132800,136710⟩,
  ⟨4452,4449,134741,140646⟩,
  ⟨4453,4446,130846,144559⟩,
  ⟨4454,4445,130842,148496⟩,
  ⟨4455,4454,150463,152414⟩,
  ⟨4456,4454,152413,156328⟩,
  ⟨4457,4451,148493,160255⟩,
  ⟨4458,4456,160254,164189⟩,
  ⟨4459,4452,154364,168124⟩,
  ⟨4460,4443,138643,172034⟩,
  ⟨4461,4455,164186,176002⟩,
  ⟨4462,4457,170060,179926⟩,
  ⟨4463,4458,174014,183845⟩,
  ⟨4464,4454,168111,187760⟩,
  ⟨4465,4464,189739,191695⟩,
  ⟨4466,4462,187758,195627⟩,
  ⟨4467,4457,179915,199567⟩,
  ⟨4468,4457,181877,203480⟩,
  ⟨4469,4447,164139,207437⟩,
  ⟨4470,4465,201516,211370⟩,
  ⟨4471,4468,209418,215302⟩,
  ⟨4472,4457,189713,219234⟩,
  ⟨4473,4466,209414,223181⟩,
  ⟨4474,4455,189698,227124⟩]

private def points054 : List (ℕ × ℕ) := [(0,0),(2213,1949),(6623,5840),(11048,9742),(13261,11694),(15460,13633),(17680,15591),(22099,19490),(22101,19492),(26522,23398),(28730,25356),(30945,27315),(35148,31015),(35368,31208),(39792,35135),(39793,35136),(44218,39040),(48627,42909),(48637,42919),(48645,42926),(50858,44877),(53072,46808),(55286,48761),(57496,50720),(57501,50725),(59715,52655),(61930,54607),(66361,58506),(68548,60442),(70790,62413),(70792,62415),(75225,66340),(77431,68279),(79656,70246),(79658,70248),(81875,72204),(84093,74139),(88520,78050),(88528,78057),(90746,80017),(92965,81973),(97394,85860),(97402,85867),(101841,89768),(104059,91718),(106280,93667),(110719,97591),(110721,97593),(115162,101517),(119605,105428),(121826,107380),(124046,109324),(124048,109325),(128485,113234),(128493,113241),(132936,117151),(132938,117153),(135155,119098),(135161,119103),(137385,121064),(141832,124996),(146281,128887),(148495,130842),(148499,130846),(150730,132800),(152954,134741),(155181,136710),(157370,138643),(159632,140646),(164085,144559),(168534,148493),(168538,148496),(170765,150463),(172992,152413),(172993,152414),(175214,154364),(177448,156328),(181904,160254),(181905,160255),(186302,164139),(186358,164186),(186362,164189),(190808,168111),(190821,168124),(193047,170060),(195280,172034),(197507,174014),(199741,176002),(204190,179915),(204202,179926),(206418,181877),(208665,183845),(213126,187758),(213128,187760),(215315,189698),(215332,189713),(215360,189739),(217593,191695),(222058,195627),(226525,199567),(228755,201516),(230992,203480),(235461,207437),(237689,209414),(237694,209418),(239930,211370),(244401,215302),(248872,219234),(253345,223181),(257818,227124)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check054 :
    PLift (groupData 9750520 257818 4419 4474 g054 points054) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts054 :
    compareNamed primeRoster 19 18 9750520 257818 points054 := by
  decide +kernel

private theorem cover054 : covers 4419 4474 :=
  @groupChecked primeRoster 5000 18 9750520 257818 4419 4474 g054 points054
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check054.down counts054

private def g055 : List Row :=
  [⟨4475,4471,2,7889⟩,
  ⟨4476,4470,0,11809⟩,
  ⟨4477,4473,7887,15750⟩,
  ⟨4478,4470,3939,19690⟩,
  ⟨4479,4478,21676,23653⟩,
  ⟨4480,4479,25624,27595⟩,
  ⟨4481,4469,7873,31530⟩,
  ⟨4482,4475,21671,35487⟩,
  ⟨4483,4482,37463,39428⟩,
  ⟨4484,4483,41405,43370⟩,
  ⟨4485,4475,27586,47340⟩,
  ⟨4486,4471,21649,51305⟩,
  ⟨4487,4479,39420,55255⟩,
  ⟨4488,4460,3862,59237⟩,
  ⟨4489,4470,25582,63177⟩,
  ⟨4490,4474,35456,67135⟩,
  ⟨4491,4484,57231,71077⟩,
  ⟨4492,4467,25554,75015⟩,
  ⟨4493,4489,71075,78970⟩,
  ⟨4494,4488,71072,82947⟩,
  ⟨4495,4489,75011,86899⟩,
  ⟨4496,4489,76981,90894⟩,
  ⟨4497,4483,67113,94865⟩,
  ⟨4498,4492,86895,98836⟩,
  ⟨4499,4498,100809,102782⟩,
  ⟨4500,4494,94860,106751⟩,
  ⟨4501,4492,92884,110722⟩,
  ⟨4502,4500,110721,114682⟩,
  ⟨4503,4501,114682,118664⟩,
  ⟨4504,4501,116683,122618⟩,
  ⟨4505,4498,112685,126606⟩,
  ⟨4506,4499,116678,130582⟩,
  ⟨4507,4504,128589,134539⟩,
  ⟨4508,4507,136517,138500⟩,
  ⟨4509,4503,130579,142497⟩,
  ⟨4510,4509,144488,146486⟩,
  ⟨4511,4509,146486,150450⟩,
  ⟨4512,4510,150449,154420⟩,
  ⟨4513,4508,148462,158378⟩,
  ⟨4514,4505,144481,162357⟩,
  ⟨4515,4488,112612,166336⟩,
  ⟨4516,4495,128540,170317⟩,
  ⟨4517,4493,126543,174298⟩,
  ⟨4518,4516,174297,178294⟩,
  ⟨4519,4514,172303,182294⟩,
  ⟨4520,4518,182293,186272⟩,
  ⟨4521,4511,170306,190278⟩,
  ⟨4522,4518,186270,194265⟩,
  ⟨4523,4515,182287,198242⟩,
  ⟨4524,4518,190274,202233⟩,
  ⟨4525,4519,194261,206209⟩,
  ⟨4526,4518,194258,210219⟩,
  ⟨4527,4523,206207,214200⟩,
  ⟨4528,4522,206204,218191⟩,
  ⟨4529,4524,212219,222181⟩,
  ⟨4530,4528,222180,226141⟩,
  ⟨4531,4530,228135,230144⟩]

private def points055 : List (ℕ × ℕ) := [(0,0),(3,2),(4380,3862),(4470,3939),(8935,7873),(8951,7887),(8953,7889),(13428,11809),(17905,15750),(22382,19690),(24593,21649),(24615,21671),(24621,21676),(26861,23653),(29022,25554),(29055,25582),(29100,25624),(31328,27586),(31340,27595),(35821,31530),(40270,35456),(40302,35487),(42543,37463),(44777,39420),(44785,39428),(47026,41405),(49268,43370),(53753,47340),(58238,51305),(62725,55255),(64962,57231),(67212,59237),(71701,63177),(76166,67113),(76190,67135),(80676,71072),(80679,71075),(80681,71077),(85168,75011),(85172,75015),(87412,76981),(89665,78970),(94158,82947),(98648,86895),(98653,86899),(103148,90894),(105386,92884),(107640,94860),(107645,94865),(112142,98836),(114391,100809),(116641,102782),(121140,106751),(125640,110721),(125641,110722),(127800,112612),(127885,112685),(130142,114682),(132387,116678),(132392,116683),(134645,118664),(139148,122618),(143581,126543),(143653,126606),(145850,128540),(145904,128589),(148154,130579),(148158,130582),(152665,134539),(154918,136517),(157172,138500),(161681,142497),(163925,144481),(163935,144488),(166190,146486),(168442,148462),(170700,150449),(170701,150450),(175212,154420),(179725,158378),(184238,162357),(188753,166336),(193256,170306),(193268,170317),(195523,172303),(197784,174297),(197785,174298),(202302,178294),(206813,182287),(206820,182293),(206821,182294),(211338,186270),(211340,186272),(215856,190274),(215861,190278),(220374,194258),(220378,194261),(220382,194265),(224905,198242),(229428,202233),(233948,206204),(233951,206207),(233953,206209),(238478,210219),(240738,212219),(243005,214200),(247532,218191),(252060,222180),(252061,222181),(256590,226141),(258855,228135),(261121,230144)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check055 :
    PLift (groupData 10003860 261121 4475 4531 g055 points055) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts055 :
    compareNamed primeRoster 19 18 10003860 261121 points055 := by
  decide +kernel

private theorem cover055 : covers 4475 4531 :=
  @groupChecked primeRoster 5000 18 10003860 261121 4475 4531 g055 points055
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check055.down counts055

private def g056 : List Row :=
  [⟨4532,4524,0,15975⟩,
  ⟨4533,4528,9950,19964⟩,
  ⟨4534,4532,19963,23956⟩,
  ⟨4535,4533,23956,27950⟩,
  ⟨4536,4532,23955,31934⟩,
  ⟨4537,4536,33939,35945⟩,
  ⟨4538,4535,33938,39918⟩,
  ⟨4539,4532,29935,43921⟩,
  ⟨4540,4538,43920,47939⟩,
  ⟨4541,4540,49935,51949⟩,
  ⟨4542,4529,29924,55920⟩,
  ⟨4543,4535,43915,59934⟩,
  ⟨4544,4534,43910,63971⟩,
  ⟨4545,4542,61941,67962⟩,
  ⟨4546,4536,51939,71982⟩,
  ⟨4547,4543,67960,75961⟩,
  ⟨4548,4547,77950,79941⟩,
  ⟨4549,4545,75959,83940⟩,
  ⟨4550,4548,83939,87932⟩,
  ⟨4551,4539,67945,91932⟩,
  ⟨4552,4543,77940,95947⟩,
  ⟨4553,4549,91931,99950⟩,
  ⟨4554,4540,75941,103972⟩,
  ⟨4555,4548,93932,107998⟩,
  ⟨4556,4555,109997,111998⟩,
  ⟨4557,4556,114015,116017⟩,
  ⟨4558,4551,105981,120045⟩,
  ⟨4559,4553,111994,124074⟩,
  ⟨4560,4559,126078,128077⟩,
  ⟨4561,4557,124072,132101⟩,
  ⟨4562,4532,75866,136129⟩,
  ⟨4563,4556,126074,140168⟩,
  ⟨4564,4533,81829,144202⟩,
  ⟨4565,4561,140167,148236⟩,
  ⟨4566,4556,132090,152231⟩,
  ⟨4567,4554,130081,156276⟩,
  ⟨4568,4566,156275,160280⟩,
  ⟨4569,4568,162290,164306⟩,
  ⟨4570,4566,160279,168322⟩,
  ⟨4571,4570,170331,172354⟩,
  ⟨4572,4554,140131,176390⟩,
  ⟨4573,4569,172352,180437⟩,
  ⟨4574,4571,178407,184459⟩,
  ⟨4575,4571,180435,188488⟩,
  ⟨4576,4575,190501,192526⟩,
  ⟨4577,4559,160244,196576⟩,
  ⟨4578,4575,194564,200604⟩,
  ⟨4579,4572,190496,204650⟩,
  ⟨4580,4570,188477,208694⟩,
  ⟨4581,4580,210699,212707⟩,
  ⟨4582,4573,198578,216738⟩,
  ⟨4583,4532,117745,220783⟩,
  ⟨4584,4577,210693,224806⟩,
  ⟨4585,4577,212700,228833⟩]

private def points056 : List (ℕ × ℕ) := [(0,0),(11328,9950),(18128,15975),(22660,19963),(22661,19964),(27192,23955),(27194,23956),(31729,27950),(33975,29924),(33990,29935),(36264,31934),(38531,33938),(38532,33939),(40801,35945),(45338,39918),(49864,43910),(49869,43915),(49876,43920),(49877,43921),(54416,47939),(56686,49935),(58944,51939),(58957,51949),(63498,55920),(68041,59934),(70311,61941),(72584,63971),(77111,67945),(77127,67960),(77129,67962),(81674,71982),(86108,75866),(86196,75941),(86219,75959),(86221,75961),(88484,77940),(88494,77950),(90768,79941),(92922,81829),(95316,83939),(95317,83940),(99866,87932),(104415,91931),(104417,91932),(106686,93932),(108968,95947),(113521,99950),(118074,103972),(120345,105981),(122629,107998),(124906,109997),(127180,111994),(127184,111998),(129462,114015),(131741,116017),(133694,117745),(136298,120045),(140855,124072),(140857,124074),(143130,126074),(143136,126078),(145416,128077),(147675,130081),(149964,132090),(149977,132101),(154538,136129),(159060,140131),(159099,140167),(159101,140168),(163664,144202),(168229,148236),(172794,152231),(177360,156275),(177361,156276),(181888,160244),(181926,160279),(181928,160280),(184212,162290),(186497,164306),(191066,168322),(193351,170331),(195635,172352),(195637,172354),(200208,176390),(202493,178407),(204779,180435),(204781,180437),(209354,184459),(213916,188477),(213929,188488),(216210,190496),(216216,190501),(218504,192526),(220791,194564),(223081,196576),(225359,198578),(227658,200604),(232237,204650),(236816,208694),(239100,210693),(239106,210699),(241389,212700),(241397,212707),(245978,216738),(250561,220783),(255144,224806),(259729,228833)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check056 :
    PLift (groupData 10251384 259729 4532 4585 g056 points056) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts056 :
    compareNamed primeRoster 19 18 10251384 259729 points056 := by
  decide +kernel

private theorem cover056 : covers 4532 4585 :=
  @groupChecked primeRoster 5000 18 10251384 259729 4532 4585 g056 points056
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check056.down counts056

private def g057 : List Row :=
  [⟨4586,4569,20437,54769⟩,
  ⟨4587,4577,38610,58804⟩,
  ⟨4588,4584,54768,62853⟩,
  ⟨4589,4587,62853,66885⟩,
  ⟨4590,4586,62851,70922⟩,
  ⟨4591,4588,68892,74982⟩,
  ⟨4592,4570,34535,79036⟩,
  ⟨4593,4572,40602,83112⟩,
  ⟨4594,4592,83111,87148⟩,
  ⟨4595,4580,60800,91212⟩,
  ⟨4596,4593,89168,95235⟩,
  ⟨4597,4590,85121,99304⟩,
  ⟨4598,4547,0,103348⟩,
  ⟨4599,4598,105366,107397⟩,
  ⟨4600,4598,107396,111487⟩,
  ⟨4601,4594,101318,115549⟩,
  ⟨4602,4593,101314,119582⟩,
  ⟨4603,4592,101309,123657⟩,
  ⟨4604,4579,76949,127706⟩,
  ⟨4605,4601,123655,131768⟩,
  ⟨4606,4605,133806,135840⟩,
  ⟨4607,4604,133805,139919⟩,
  ⟨4608,4562,50484,143981⟩,
  ⟨4609,4600,129732,148050⟩,
  ⟨4610,4600,131756,152123⟩,
  ⟨4611,4610,154139,156168⟩,
  ⟨4612,4596,127681,160220⟩,
  ⟨4613,4609,156166,164263⟩,
  ⟨4614,4609,158186,168312⟩,
  ⟨4615,4601,143962,172378⟩,
  ⟨4616,4603,150066,176453⟩,
  ⟨4617,4592,129672,180516⟩,
  ⟨4618,4603,154117,184599⟩,
  ⟨4619,4613,176449,188685⟩,
  ⟨4620,4603,158159,192738⟩,
  ⟨4621,4595,143910,196824⟩,
  ⟨4622,4612,180504,200907⟩,
  ⟨4623,4622,202939,204974⟩,
  ⟨4624,4615,190709,209044⟩,
  ⟨4625,4614,190706,213107⟩,
  ⟨4626,4620,204969,217190⟩,
  ⟨4627,4624,215153,221283⟩,
  ⟨4628,4618,204961,225352⟩,
  ⟨4629,4622,215148,229449⟩]

private def points057 : List (ℕ × ℕ) := [(0,0),(23164,20437),(39167,34535),(43797,38610),(46045,40602),(57295,50484),(62143,54768),(62145,54769),(66732,58804),(68997,60800),(71317,62851),(71319,62853),(75908,66885),(78201,68892),(80497,70922),(85088,74982),(87305,76949),(89679,79036),(94271,83111),(94272,83112),(96562,85121),(98865,87148),(101161,89168),(103460,91212),(108055,95235),(112652,99304),(114935,101309),(114940,101314),(114944,101318),(117249,103348),(119548,105366),(121847,107396),(121848,107397),(126447,111487),(131048,115549),(135649,119582),(140250,123655),(140252,123657),(144823,127681),(144855,127706),(147079,129672),(147147,129732),(149447,131756),(149460,131768),(151761,133805),(151762,133806),(154065,135840),(158672,139919),(163195,143910),(163255,143962),(163279,143981),(167888,148050),(170171,150066),(172497,152123),(174774,154117),(174802,154139),(177106,156166),(177108,156168),(179377,158159),(179410,158186),(181719,160220),(186332,164263),(190945,168312),(195560,172378),(200171,176449),(200175,176453),(204779,180504),(204792,180516),(209409,184599),(214028,188685),(216322,190706),(216327,190709),(218647,192738),(223268,196824),(227889,200907),(230200,202939),(232499,204961),(232507,204969),(232512,204974),(237135,209044),(241760,213107),(244066,215148),(244071,215153),(246385,217190),(251012,221283),(255639,225352),(260268,229449)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check057 :
    PLift (groupData 10453553 260268 4586 4629 g057 points057) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts057 :
    compareNamed primeRoster 19 18 10453553 260268 points057 := by
  decide +kernel

private theorem cover057 : covers 4586 4629 :=
  @groupChecked primeRoster 5000 18 10453553 260268 4586 4629 g057 points057
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check057.down counts057

private def g058 : List Row :=
  [⟨4630,4627,28601,34719⟩,
  ⟨4631,4622,20421,38788⟩,
  ⟨4632,4630,38787,42856⟩,
  ⟨4633,4610,0,46913⟩,
  ⟨4634,4626,34711,50996⟩,
  ⟨4635,4618,20397,55066⟩,
  ⟨4636,4634,55065,59160⟩,
  ⟨4637,4630,48951,63248⟩,
  ⟨4638,4612,14227,67370⟩,
  ⟨4639,4638,69420,71469⟩,
  ⟨4640,4632,59152,75569⟩,
  ⟨4641,4640,77608,79658⟩,
  ⟨4642,4630,59145,83744⟩,
  ⟨4643,4640,81704,87848⟩,
  ⟨4644,4641,85787,91932⟩,
  ⟨4645,4641,87847,96040⟩,
  ⟨4646,4642,91930,100119⟩,
  ⟨4647,4646,102165,104208⟩,
  ⟨4648,4646,104207,108314⟩,
  ⟨4649,4645,104206,112381⟩,
  ⟨4650,4636,87826,116499⟩,
  ⟨4651,4650,118547,120590⟩,
  ⟨4652,4651,122651,124700⟩,
  ⟨4653,4626,73440,128823⟩,
  ⟨4654,4636,96004,132917⟩,
  ⟨4655,4654,134971,137028⟩,
  ⟨4656,4655,139065,141110⟩,
  ⟨4657,4656,143162,145228⟩,
  ⟨4658,4642,116468,149323⟩,
  ⟨4659,4647,128807,153418⟩,
  ⟨4660,4642,120553,157526⟩,
  ⟨4661,4658,155463,161632⟩,
  ⟨4662,4657,155461,165743⟩,
  ⟨4663,4662,167789,169844⟩,
  ⟨4664,4662,169843,173944⟩,
  ⟨4665,4661,169842,178081⟩,
  ⟨4666,4665,180119,182181⟩,
  ⟨4667,4659,169836,186283⟩,
  ⟨4668,4666,186282,190393⟩,
  ⟨4669,4665,186282,194511⟩,
  ⟨4670,4657,171871,198645⟩,
  ⟨4671,4668,196587,202767⟩,
  ⟨4672,4659,180101,206862⟩,
  ⟨4673,4672,208937,210993⟩,
  ⟨4674,4652,169789,215112⟩,
  ⟨4675,4669,206859,219227⟩,
  ⟨4676,4675,221291,223358⟩,
  ⟨4677,4674,221290,227467⟩]

private def points058 : List (ℕ × ℕ) := [(0,0),(16163,14227),(23150,20397),(23176,20421),(32440,28601),(39377,34711),(39385,34719),(44015,38787),(44016,38788),(48647,42856),(53280,46913),(55590,48951),(57913,50996),(62547,55065),(62548,55066),(67165,59145),(67175,59152),(67183,59160),(71820,63248),(76457,67370),(78776,69420),(81096,71469),(83324,73440),(85735,75569),(88055,77608),(90376,79658),(92695,81704),(95017,83744),(97337,85787),(99635,87826),(99658,87847),(99660,87848),(104301,91930),(104303,91932),(108907,96004),(108948,96040),(113593,100119),(115916,102165),(118238,104206),(118239,104207),(118240,104208),(122887,108314),(127536,112381),(132153,116468),(132185,116499),(134510,118547),(136795,120553),(136836,120590),(139161,122651),(141487,124700),(146122,128807),(146140,128823),(150793,132917),(153120,134971),(155448,137028),(157775,139065),(160103,141110),(162431,143162),(164760,145228),(169417,149323),(174076,153418),(176402,155461),(176404,155463),(178735,157526),(183396,161632),(188057,165743),(190388,167789),(192659,169789),(192712,169836),(192718,169842),(192719,169843),(192720,169844),(195030,171871),(197383,173944),(202048,178081),(204359,180101),(204380,180119),(206713,182181),(211378,186282),(211379,186282),(211380,186283),(216047,190393),(220716,194511),(223049,196587),(225385,198645),(230056,202767),(234723,206859),(234727,206862),(237063,208937),(239400,210993),(244073,215112),(248748,219227),(251084,221290),(251085,221291),(253423,223358),(258100,227467)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check058 :
    PLift (groupData 10679065 258100 4630 4677 g058 points058) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts058 :
    compareNamed primeRoster 19 18 10679065 258100 points058 := by
  decide +kernel

private theorem cover058 : covers 4630 4677 :=
  @groupChecked primeRoster 5000 18 10679065 258100 4630 4677 g058 points058
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check058.down counts058

private def g059 : List Row :=
  [⟨4678,4670,12374,28865⟩,
  ⟨4679,4663,8,32983⟩,
  ⟨4680,4662,0,37127⟩,
  ⟨4681,4675,28862,41248⟩,
  ⟨4682,4675,30905,45359⟩,
  ⟨4683,4680,43282,49484⟩,
  ⟨4684,4675,35044,53579⟩,
  ⟨4685,4679,45356,57688⟩,
  ⟨4686,4684,57687,61826⟩,
  ⟨4687,4686,63898,65973⟩,
  ⟨4688,4677,47395,70112⟩,
  ⟨4689,4678,51521,74250⟩,
  ⟨4690,4686,70110,78393⟩,
  ⟨4691,4690,80441,82516⟩,
  ⟨4692,4682,65960,86643⟩,
  ⟨4693,4691,86643,90779⟩,
  ⟨4694,4692,90778,94901⟩,
  ⟨4695,4694,96966,99037⟩,
  ⟨4696,4688,86636,103147⟩,
  ⟨4697,4685,82499,107310⟩,
  ⟨4698,4692,99033,111464⟩,
  ⟨4699,4688,92838,115634⟩,
  ⟨4700,4699,117708,119795⟩,
  ⟨4701,4683,86609,123945⟩,
  ⟨4702,4699,121871,128113⟩,
  ⟨4703,4694,113527,132250⟩,
  ⟨4704,4695,117700,136401⟩,
  ⟨4705,4667,61665,140547⟩,
  ⟨4706,4681,92783,144691⟩,
  ⟨4707,4706,146773,148856⟩,
  ⟨4708,4704,144690,153009⟩,
  ⟨4709,4708,155081,157155⟩,
  ⟨4710,4708,157154,161301⟩,
  ⟨4711,4708,159241,165469⟩,
  ⟨4712,4711,167563,169656⟩,
  ⟨4713,4701,148842,173813⟩,
  ⟨4714,4711,171723,177983⟩,
  ⟨4715,4714,180055,182144⟩,
  ⟨4716,4711,175896,186313⟩,
  ⟨4717,4689,132167,190478⟩,
  ⟨4718,4713,184226,194640⟩,
  ⟨4719,4717,194640,198796⟩,
  ⟨4720,4712,186307,202950⟩,
  ⟨4721,4693,148770,207137⟩,
  ⟨4722,4698,161237,211294⟩,
  ⟨4723,4722,213366,215447⟩,
  ⟨4724,4714,198786,219609⟩,
  ⟨4725,4696,163294,223748⟩,
  ⟨4726,4718,211287,227940⟩]

private def points059 : List (ℕ × ℕ) := [(0,0),(9,8),(14050,12374),(32758,28862),(32762,28865),(35095,30905),(37441,32983),(39770,35044),(42120,37127),(46801,41248),(49140,43282),(51478,45356),(51482,45359),(53808,47395),(56165,49484),(58491,51521),(60848,53579),(65532,57687),(65533,57688),(70038,61665),(70218,61826),(72561,63898),(74892,65960),(74905,65973),(79590,70110),(79592,70112),(84281,74250),(88970,78393),(91315,80441),(93643,82499),(93661,82516),(98312,86609),(98344,86636),(98352,86643),(103044,90778),(103045,90779),(105313,92783),(105376,92838),(107738,94901),(110085,96966),(112428,99033),(112433,99037),(117128,103147),(121825,107310),(126522,111464),(128861,113527),(131221,115634),(133560,117700),(133570,117708),(135920,119795),(138269,121871),(140621,123945),(145322,128113),(149927,132167),(150025,132250),(154728,136401),(159433,140547),(164136,144690),(164138,144691),(166491,146773),(168747,148770),(168827,148842),(168845,148856),(173552,153009),(175906,155081),(178260,157154),(178261,157155),(180614,159241),(182898,161237),(182970,161301),(185220,163294),(187681,165469),(190036,167563),(192392,169656),(194747,171723),(197105,173813),(199458,175896),(201818,177983),(204175,180055),(206533,182144),(208887,184226),(211240,186307),(211248,186313),(215965,190478),(220682,194640),(225388,198786),(225401,198796),(230120,202950),(234841,207137),(239554,211287),(239562,211294),(241923,213366),(244285,215447),(249008,219609),(253733,223748),(258458,227940)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check059 :
    PLift (groupData 10909080 258458 4678 4726 g059 points059) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts059 :
    compareNamed primeRoster 19 18 10909080 258458 points059 := by
  decide +kernel

private theorem cover059 : covers 4678 4726 :=
  @groupChecked primeRoster 5000 18 10909080 258458 4678 4726 g059 points059
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check059.down counts059

private def g060 : List Row :=
  [⟨4727,4722,0,10445⟩,
  ⟨4728,4723,4153,14612⟩,
  ⟨4729,4724,8339,18795⟩,
  ⟨4730,4721,4146,22964⟩,
  ⟨4731,4724,12531,27139⟩,
  ⟨4732,4718,2051,31322⟩,
  ⟨4733,4731,31322,35486⟩,
  ⟨4734,4733,37582,39666⟩,
  ⟨4735,4734,41765,43840⟩,
  ⟨4736,4733,41765,48030⟩,
  ⟨4737,4729,35478,52213⟩,
  ⟨4738,4719,16665,56397⟩,
  ⟨4739,4718,16657,60578⟩,
  ⟨4740,4738,60577,64754⟩,
  ⟨4741,4740,66842,68950⟩,
  ⟨4742,4738,64752,73107⟩,
  ⟨4743,4729,48007,77301⟩,
  ⟨4744,4722,35431,81482⟩,
  ⟨4745,4736,66833,85665⟩,
  ⟨4746,4742,81480,89843⟩,
  ⟨4747,4738,75206,94025⟩,
  ⟨4748,4746,94024,98209⟩,
  ⟨4749,4728,58450,102376⟩,
  ⟨4750,4728,60526,106565⟩,
  ⟨4751,4746,100285,110734⟩,
  ⟨4752,4750,110733,114944⟩,
  ⟨4753,4712,33232,119118⟩,
  ⟨4754,4743,100274,123312⟩,
  ⟨4755,4754,125410,127505⟩,
  ⟨4756,4752,123310,131705⟩,
  ⟨4757,4753,127504,135865⟩,
  ⟨4758,4756,135864,140075⟩,
  ⟨4759,4758,142197,144306⟩,
  ⟨4760,4726,77172,148505⟩,
  ⟨4761,4736,100220,152690⟩,
  ⟨4762,4737,104398,156896⟩,
  ⟨4763,4762,158968,161093⟩,
  ⟨4764,4755,146380,165267⟩,
  ⟨4765,4752,142178,169460⟩,
  ⟨4766,4749,137932,173660⟩,
  ⟨4767,4764,171550,177872⟩,
  ⟨4768,4763,171548,182069⟩,
  ⟨4769,4767,182069,186269⟩,
  ⟨4770,4748,144253,190476⟩,
  ⟨4771,4765,182065,194679⟩,
  ⟨4772,4758,169439,198900⟩,
  ⟨4773,4756,167324,203108⟩,
  ⟨4774,4773,205223,207327⟩,
  ⟨4775,4771,203106,211559⟩,
  ⟨4776,4775,213661,215772⟩,
  ⟨4777,4753,169400,219991⟩,
  ⟨4778,4760,186234,224215⟩,
  ⟨4779,4771,211552,228429⟩]

private def points060 : List (ℕ × ℕ) := [(0,0),(2341,2051),(4718,4146),(4725,4153),(9451,8339),(11818,10445),(14175,12531),(16545,14612),(18854,16657),(18864,16665),(21274,18795),(26003,22964),(30734,27139),(35465,31322),(37621,33232),(40137,35431),(40190,35478),(40198,35486),(42564,37582),(44931,39666),(47297,41765),(47298,41765),(49666,43840),(54377,48007),(54401,48030),(59138,52213),(63875,56397),(66189,58450),(68553,60526),(68613,60577),(68614,60578),(73351,64752),(73353,64754),(75713,66833),(75723,66842),(78094,68950),(82835,73107),(85196,75206),(87433,77172),(87578,77301),(92319,81480),(92321,81482),(97066,85665),(101811,89843),(106557,94024),(106558,94025),(111305,98209),(113601,100220),(113664,100274),(113676,100285),(116054,102376),(118350,104398),(120803,106565),(125553,110733),(125554,110734),(130305,114944),(135058,119118),(139809,123310),(139811,123312),(142188,125410),(144564,127504),(144566,127505),(149321,131705),(154077,135864),(154078,135865),(156420,137932),(158835,140075),(161193,142178),(161214,142197),(163533,144253),(163594,144306),(165963,146380),(168353,148505),(173114,152690),(177875,156896),(180256,158968),(182638,161093),(187401,165267),(189747,167324),(192094,169400),(192141,169439),(192166,169460),(194545,171548),(194547,171550),(196931,173660),(201698,177872),(206461,182065),(206465,182069),(211193,186234),(211234,186269),(216003,190476),(220774,194679),(225545,198900),(230316,203106),(230318,203108),(232704,205223),(235091,207327),(239858,211552),(239866,211559),(242253,213661),(244641,215772),(249418,219991),(254195,224215),(258974,228429)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check060 :
    PLift (groupData 11160447 258974 4727 4779 g060 points060) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts060 :
    compareNamed primeRoster 19 18 11160447 258974 points060 := by
  decide +kernel

private theorem cover060 : covers 4727 4779 :=
  @groupChecked primeRoster 5000 18 11160447 258974 4727 4779 g060 points060
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check060.down counts060

private def g061 : List Row :=
  [⟨4780,4775,0,10523⟩,
  ⟨4781,4779,10523,14735⟩,
  ⟨4782,4776,6336,18949⟩,
  ⟨4783,4779,14733,23170⟩,
  ⟨4784,4780,18947,27392⟩,
  ⟨4785,4782,25279,31598⟩,
  ⟨4786,4770,2097,35824⟩,
  ⟨4787,4780,25275,40037⟩,
  ⟨4788,4787,42131,44256⟩,
  ⟨4789,4779,27381,48483⟩,
  ⟨4790,4789,50606,52708⟩,
  ⟨4791,4788,50605,56933⟩,
  ⟨4792,4780,35809,61172⟩,
  ⟨4793,4791,61172,65394⟩,
  ⟨4794,4793,67511,69625⟩,
  ⟨4795,4791,65393,73866⟩,
  ⟨4796,4789,63282,78089⟩,
  ⟨4797,4787,61160,82284⟩,
  ⟨4798,4785,59033,86511⟩,
  ⟨4799,4790,71730,90735⟩,
  ⟨4800,4798,90734,94971⟩,
  ⟨4801,4797,90733,99206⟩,
  ⟨4802,4789,75952,103432⟩,
  ⟨4803,4794,88606,107677⟩,
  ⟨4804,4789,80163,111896⟩,
  ⟨4805,4804,114029,116163⟩,
  ⟨4806,4805,118290,120416⟩,
  ⟨4807,4800,109785,124659⟩,
  ⟨4808,4805,122532,128887⟩,
  ⟨4809,4805,124658,133153⟩,
  ⟨4810,4798,111881,137394⟩,
  ⟨4811,4806,131012,141631⟩,
  ⟨4812,4807,135276,145877⟩,
  ⟨4813,4769,56717,150100⟩,
  ⟨4814,4812,150099,154320⟩,
  ⟨4815,4814,156458,158583⟩,
  ⟨4816,4804,137378,162861⟩,
  ⟨4817,4811,154316,167104⟩,
  ⟨4818,4817,169243,171383⟩,
  ⟨4819,4815,167102,175617⟩,
  ⟨4820,4810,158570,179881⟩,
  ⟨4821,4817,175615,184134⟩,
  ⟨4822,4810,162845,188388⟩,
  ⟨4823,4806,156426,192633⟩,
  ⟨4824,4821,190508,196881⟩,
  ⟨4825,4816,181988,201108⟩,
  ⟨4826,4821,194748,205366⟩,
  ⟨4827,4817,188379,209627⟩,
  ⟨4828,4827,211758,213865⟩,
  ⟨4829,4820,198986,218126⟩,
  ⟨4830,4821,203221,222377⟩,
  ⟨4831,4828,220248,226656⟩,
  ⟨4832,4827,220246,230927⟩]

private def points061 : List (ℕ × ℕ) := [(0,0),(2360,2097),(7166,6336),(11950,10523),(16729,14733),(16731,14735),(21510,18947),(21512,18949),(26295,23170),(28680,25275),(28685,25279),(31066,27381),(31078,27392),(35863,31598),(40630,35809),(40648,35824),(45435,40037),(47828,42131),(50222,44256),(55011,48483),(57404,50605),(57405,50606),(59800,52708),(64349,56717),(64591,56933),(66965,59033),(69370,61160),(69382,61172),(71772,63282),(74173,65393),(74175,65394),(76571,67511),(78968,69625),(81355,71730),(83763,73866),(86139,75952),(88558,78089),(90928,80163),(93355,82284),(98152,86511),(100541,88606),(102949,90733),(102950,90734),(102951,90735),(107750,94971),(112551,99206),(117352,103432),(122155,107677),(124550,109785),(126940,111881),(126958,111896),(129360,114029),(131763,116163),(134165,118290),(136568,120416),(138970,122532),(141373,124658),(141375,124659),(146182,128887),(148583,131012),(150991,133153),(153392,135276),(155782,137378),(155800,137394),(160611,141631),(165422,145877),(170234,150099),(170235,150100),(175044,154316),(175048,154320),(177419,156426),(177455,156458),(179850,158570),(179863,158583),(184660,162845),(184678,162861),(189493,167102),(189495,167104),(191903,169243),(194312,171383),(199129,175615),(199131,175617),(203950,179881),(206350,181988),(208771,184134),(213580,188379),(213592,188388),(216002,190508),(218415,192633),(220823,194748),(223238,196881),(225640,198986),(228063,201108),(230465,203221),(232888,205366),(237715,209627),(240128,211758),(242542,213865),(247371,218126),(249782,220246),(249784,220248),(252200,222377),(257031,226656),(261862,230927)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check061 :
    PLift (groupData 11412250 261862 4780 4832 g061 points061) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts061 :
    compareNamed primeRoster 19 18 11412250 261862 points061 := by
  decide +kernel

private theorem cover061 : covers 4780 4832 :=
  @groupChecked primeRoster 5000 18 11412250 261862 4780 4832 g061 points061
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check061.down counts061

private def g062 : List Row :=
  [⟨4833,4831,6417,10649⟩,
  ⟨4834,4827,0,14916⟩,
  ⟨4835,4834,17026,19163⟩,
  ⟨4836,4833,17026,23459⟩,
  ⟨4837,4827,6405,27747⟩,
  ⟨4838,4836,27746,32027⟩,
  ⟨4839,4836,29892,36298⟩,
  ⟨4840,4834,27744,40565⟩,
  ⟨4841,4826,12751,44842⟩,
  ⟨4842,4838,40563,49094⟩,
  ⟨4843,4831,27733,53378⟩,
  ⟨4844,4839,46976,57635⟩,
  ⟨4845,4836,42709,61891⟩,
  ⟨4846,4841,55496,66158⟩,
  ⟨4847,4846,68312,70459⟩,
  ⟨4848,4847,72592,74735⟩,
  ⟨4849,4838,55486,79019⟩,
  ⟨4850,4838,57619,83306⟩,
  ⟨4851,4844,72586,87572⟩,
  ⟨4852,4846,79014,91837⟩,
  ⟨4853,4839,66135,96117⟩,
  ⟨4854,4849,89714,100410⟩,
  ⟨4855,4852,98265,104691⟩,
  ⟨4856,4851,98263,108970⟩,
  ⟨4857,4848,93981,113295⟩,
  ⟨4858,4855,111140,117550⟩,
  ⟨4859,4854,111138,121847⟩,
  ⟨4860,4843,89682,126131⟩,
  ⟨4861,4859,126131,130405⟩,
  ⟨4862,4832,70359,134708⟩,
  ⟨4863,4861,134708,139008⟩,
  ⟨4864,4851,115394,143291⟩,
  ⟨4865,4857,130398,147561⟩,
  ⟨4866,4834,83192,151845⟩,
  ⟨4867,4862,145422,156151⟩,
  ⟨4868,4867,158295,160446⟩,
  ⟨4869,4855,134686,164742⟩,
  ⟨4870,4865,158292,169058⟩,
  ⟨4871,4869,169058,173360⟩,
  ⟨4872,4868,169056,177671⟩,
  ⟨4873,4832,93805,181971⟩,
  ⟨4874,4868,173355,186268⟩,
  ⟨4875,4869,177667,190569⟩,
  ⟨4876,4874,190568,194867⟩,
  ⟨4877,4863,169036,199156⟩,
  ⟨4878,4873,192712,203478⟩,
  ⟨4879,4874,197007,207782⟩,
  ⟨4880,4879,209933,212090⟩,
  ⟨4881,4880,214240,216370⟩,
  ⟨4882,4864,181937,220708⟩,
  ⟨4883,4881,220708,225020⟩,
  ⟨4884,4882,225019,229356⟩]

private def points062 : List (ℕ × ℕ) := [(0,0),(7241,6405),(7253,6417),(12086,10649),(14474,12751),(16919,14916),(19335,17026),(19336,17026),(21754,19163),(26589,23459),(31408,27733),(31421,27744),(31425,27746),(31426,27747),(33843,29892),(36263,32027),(41102,36298),(45939,40563),(45941,40565),(48351,42709),(50782,44842),(53199,46976),(55623,49094),(60466,53378),(62872,55486),(62884,55496),(65291,57619),(65309,57635),(70154,61891),(74975,66135),(74999,66158),(77422,68312),(79733,70359),(79846,70459),(82263,72586),(82269,72592),(84693,74735),(89537,79014),(89542,79019),(94263,83192),(94391,83306),(99242,87572),(101631,89682),(101664,89714),(104093,91837),(106309,93805),(106509,93981),(108946,96117),(111369,98263),(111371,98265),(113799,100410),(118654,104691),(123509,108970),(125934,111138),(125936,111140),(128366,113295),(130773,115394),(133223,117550),(138082,121847),(142941,126131),(147794,130398),(147802,130405),(152639,134686),(152663,134708),(157526,139008),(162389,143291),(164818,145422),(167254,147561),(172119,151845),(176986,156151),(179416,158292),(179419,158295),(181853,160446),(186722,164742),(191567,169036),(191589,169056),(191591,169058),(196457,173355),(196462,173360),(201329,177667),(201333,177671),(206165,181937),(206206,181971),(211079,186268),(215953,190568),(215954,190569),(218388,192712),(220829,194867),(223264,197007),(225706,199156),(230583,203478),(235462,207782),(237901,209933),(240341,212090),(242781,214240),(245222,216370),(250103,220708),(254985,225019),(254986,225020),(259869,229356)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check062 :
    PLift (groupData 11666859 259869 4833 4884 g062 points062) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts062 :
    compareNamed primeRoster 19 18 11666859 259869 points062 := by
  decide +kernel

private theorem cover062 : covers 4833 4884 :=
  @groupChecked primeRoster 5000 18 11666859 259869 4833 4884 g062 points062
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check062.down counts062

private def g063 : List Row :=
  [⟨4885,4874,0,23749⟩,
  ⟨4886,4879,12948,28046⟩,
  ⟨4887,4875,6436,32367⟩,
  ⟨4888,4886,32366,36661⟩,
  ⟨4889,4885,32365,40972⟩,
  ⟨4890,4888,40971,45254⟩,
  ⟨4891,4885,36657,49577⟩,
  ⟨4892,4873,12913,53886⟩,
  ⟨4893,4880,30193,58201⟩,
  ⟨4894,4893,60371,62525⟩,
  ⟨4895,4888,51728,66864⟩,
  ⟨4896,4894,66863,71188⟩,
  ⟨4897,4889,58196,75511⟩,
  ⟨4898,4891,64686,79826⟩,
  ⟨4899,4896,77662,84134⟩,
  ⟨4900,4892,71180,88433⟩,
  ⟨4901,4899,88433,92771⟩,
  ⟨4902,4884,58171,97100⟩,
  ⟨4903,4901,97100,101416⟩,
  ⟨4904,4900,97098,105753⟩,
  ⟨4905,4900,99272,110064⟩,
  ⟨4906,4904,110063,114392⟩,
  ⟨4907,4905,114392,118712⟩,
  ⟨4908,4907,120884,123045⟩,
  ⟨4909,4905,118710,127411⟩,
  ⟨4910,4893,94899,131745⟩,
  ⟨4911,4906,125234,136065⟩,
  ⟨4912,4911,138257,140442⟩,
  ⟨4913,4908,133905,144755⟩,
  ⟨4914,4913,146944,149084⟩,
  ⟨4915,4908,138251,153401⟩,
  ⟨4916,4914,153400,157717⟩,
  ⟨4917,4916,159892,162080⟩,
  ⟨4918,4911,151247,166407⟩,
  ⟨4919,4917,166407,170739⟩,
  ⟨4920,4906,144736,175097⟩,
  ⟨4921,4912,159882,179436⟩,
  ⟨4922,4920,179435,183770⟩,
  ⟨4923,4921,183770,188092⟩,
  ⟨4924,4911,164214,192441⟩,
  ⟨4925,4895,131648,196776⟩,
  ⟨4926,4924,196775,201138⟩,
  ⟨4927,4916,181588,205484⟩,
  ⟨4928,4924,201136,209799⟩,
  ⟨4929,4919,192430,214148⟩,
  ⟨4930,4928,214147,218490⟩,
  ⟨4931,4928,216320,222836⟩,
  ⟨4932,4930,222835,227198⟩]

private def points063 : List (ℕ × ℕ) := [(0,0),(7318,6436),(14613,12913),(14652,12948),(26868,23749),(31753,28046),(34175,30193),(36638,32365),(36639,32366),(36640,32367),(41523,36657),(41527,36661),(46415,40971),(46416,40972),(51305,45254),(56196,49577),(58635,51728),(61087,53886),(65939,58171),(65972,58196),(65980,58201),(68426,60371),(70873,62525),(73314,64686),(75767,66863),(75768,66864),(80655,71180),(80663,71188),(85560,75511),(88007,77662),(90457,79826),(95356,84134),(100255,88433),(105156,92771),(107570,94899),(110055,97098),(110057,97100),(112505,99272),(114960,101416),(119863,105753),(124767,110063),(124768,110064),(129673,114392),(134578,118710),(134580,118712),(137033,120884),(139487,123045),(141938,125234),(144396,127411),(149193,131648),(149305,131745),(151757,133905),(154216,136065),(156665,138251),(156671,138257),(159127,140442),(164015,144736),(164040,144755),(166496,146944),(168953,149084),(171404,151247),(173867,153400),(173868,153401),(178783,157717),(181231,159882),(181241,159892),(183700,162080),(186137,164214),(188617,166407),(193536,170739),(198455,175097),(203375,179435),(203376,179436),(205821,181588),(208297,183770),(213220,188092),(218131,192430),(218143,192441),(223067,196775),(223068,196776),(227991,201136),(227993,201138),(232920,205484),(237847,209799),(242775,214147),(242776,214148),(245239,216320),(247705,218490),(252635,222835),(252636,222836),(257567,227198)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check063 :
    PLift (groupData 11904745 257567 4885 4932 g063 points063) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts063 :
    compareNamed primeRoster 19 18 11904745 257567 points063 := by
  decide +kernel

private theorem cover063 : covers 4885 4932 :=
  @groupChecked primeRoster 5000 18 11904745 257567 4885 4932 g063 points063
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check063.down counts063

private def g064 : List Row :=
  [⟨4933,4928,67447,78341⟩,
  ⟨4934,4905,19614,82696⟩,
  ⟨4935,4931,78339,87046⟩,
  ⟨4936,4894,0,91393⟩,
  ⟨4937,4933,87045,95756⟩,
  ⟨4938,4937,97946,100108⟩,
  ⟨4939,4937,100108,104460⟩,
  ⟨4940,4907,36930,108811⟩,
  ⟨4941,4938,106642,113167⟩,
  ⟨4942,4933,97936,117528⟩,
  ⟨4943,4926,84848,121891⟩,
  ⟨4944,4943,124070,126265⟩,
  ⟨4945,4938,115329,130640⟩,
  ⟨4946,4921,80443,135031⟩,
  ⟨4947,4946,137203,139406⟩,
  ⟨4948,4943,132836,143755⟩,
  ⟨4949,4947,143755,148111⟩,
  ⟨4950,4947,145915,152481⟩,
  ⟨4951,4950,154657,156840⟩,
  ⟨4952,4950,156839,161220⟩,
  ⟨4953,4950,159034,165583⟩,
  ⟨4954,4948,156837,169952⟩,
  ⟨4955,4932,124013,174305⟩,
  ⟨4956,4940,143727,178696⟩,
  ⟨4957,4946,159020,183075⟩,
  ⟨4958,4955,180880,187436⟩,
  ⟨4959,4958,189628,191827⟩,
  ⟨4960,4957,189627,196204⟩,
  ⟨4961,4944,163366,200598⟩,
  ⟨4962,4960,200597,204982⟩,
  ⟨4963,4955,191820,209333⟩,
  ⟨4964,4960,204980,213737⟩,
  ⟨4965,4964,215927,218133⟩,
  ⟨4966,4960,209329,222506⟩,
  ⟨4967,4966,224700,226873⟩,
  ⟨4968,4966,226872,231241⟩]

private def points064 : List (ℕ × ℕ) := [(0,0),(22243,19614),(41898,36930),(76520,67447),(88851,78339),(88853,78341),(91241,80443),(93786,82696),(96217,84848),(98719,87045),(98721,87046),(103656,91393),(108593,95756),(111051,97936),(111061,97946),(113530,100108),(118469,104460),(120937,106642),(123408,108811),(128349,113167),(130813,115329),(133290,117528),(138233,121891),(140638,124013),(140704,124070),(143176,126265),(148121,130640),(150590,132836),(153066,135031),(155539,137203),(158013,139406),(162928,143727),(162960,143755),(165433,145915),(167909,148111),(172858,152481),(175333,154657),(177804,156837),(177808,156839),(177809,156840),(180269,159020),(180283,159034),(182760,161220),(185200,163366),(187713,165583),(192666,169952),(197621,174305),(202576,178696),(205053,180880),(207533,183075),(212490,187436),(214968,189627),(214969,189628),(217441,191820),(217449,191827),(222408,196204),(227368,200597),(227369,200598),(232328,204980),(232330,204982),(237288,209329),(237293,209333),(242256,213737),(244738,215927),(247221,218133),(252186,222506),(254669,224700),(257152,226872),(257153,226873),(262120,231241)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check064 :
    PLift (groupData 12078392 262120 4933 4968 g064 points064) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts064 :
    compareNamed primeRoster 19 18 12078392 262120 points064 := by
  decide +kernel

private theorem cover064 : covers 4933 4968 :=
  @groupChecked primeRoster 5000 18 12078392 262120 4933 4968 g064 points064
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check064.down counts064

private def g065 : List Row :=
  [⟨4969,4968,39534,41712⟩,
  ⟨4970,4965,35168,46106⟩,
  ⟨4971,4965,37356,50482⟩,
  ⟨4972,4971,52661,54870⟩,
  ⟨4973,4970,52660,59239⟩,
  ⟨4974,4973,61443,63659⟩,
  ⟨4975,4973,63659,68041⟩,
  ⟨4976,4966,50471,72448⟩,
  ⟨4977,4942,0,76827⟩,
  ⟨4978,4975,74640,81196⟩,
  ⟨4979,4973,72444,85592⟩,
  ⟨4980,4979,87787,90000⟩,
  ⟨4981,4980,92221,94401⟩,
  ⟨4982,4970,72432,98797⟩,
  ⟨4983,4957,46031,103219⟩,
  ⟨4984,4979,96591,107624⟩,
  ⟨4985,4964,65802,112044⟩,
  ⟨4986,4983,109837,116409⟩,
  ⟨4987,4979,103211,120818⟩,
  ⟨4988,4979,105426,125209⟩,
  ⟨4989,4988,127420,129622⟩,
  ⟨4990,4983,118615,134027⟩,
  ⟨4991,4958,65729,138432⟩,
  ⟨4992,4990,138431,142876⟩,
  ⟨4993,4984,127411,147271⟩,
  ⟨4994,4993,149480,151684⟩,
  ⟨4995,4993,151684,156110⟩,
  ⟨4996,4992,151682,160503⟩,
  ⟨4997,4995,160503,164901⟩,
  ⟨4998,4968,103115,169282⟩,
  ⟨4999,4994,162702,173719⟩,
  ⟨5000,4999,175918,178147⟩]

private def points065 : List (ℕ × ℕ) := [(0,0),(39858,35168),(42341,37356),(44829,39534),(47314,41712),(52199,46031),(52283,46106),(57241,50471),(57254,50482),(59738,52660),(59739,52661),(62225,54870),(67198,59239),(69684,61443),(72171,63659),(74522,65729),(74603,65802),(77146,68041),(82103,72432),(82117,72444),(82121,72448),(84608,74640),(87098,76827),(92075,81196),(97054,85592),(99543,87787),(102033,90000),(104523,92221),(107014,94401),(109501,96591),(111995,98797),(116865,103115),(116970,103211),(116978,103219),(119459,105426),(121961,107624),(124452,109837),(126946,112044),(131931,116409),(134418,118615),(136918,120818),(141905,125209),(144389,127411),(144399,127420),(146894,129622),(151883,134027),(156873,138431),(156874,138432),(161865,142876),(166858,147271),(169354,149480),(171849,151682),(171851,151684),(176846,156110),(181841,160503),(184336,162702),(186838,164901),(191835,169282),(196834,173719),(199333,175918),(201833,178147)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def check065 :
    PLift (groupData 12298167 201833 4969 5000 g065 points065) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem counts065 :
    compareNamed primeRoster 19 18 12298167 201833 points065 := by
  decide +kernel

private theorem cover065 : covers 4969 5000 :=
  @groupChecked primeRoster 5000 18 12298167 201833 4969 5000 g065 points065
    roster_prime roster_complete (by decide) (by decide) (by decide)
    check065.down counts065

theorem covering : covers 3 5000 :=
  (@covers_join 3 3097 5000 (@covers_join 3 1538 3097 (@covers_join 3 770 1538 (@covers_join 3 386 770 (@covers_join 3 194 386 (@covers_join 3 98 194 cover000 cover001) (@covers_join 195 290 386 cover002 cover003)) (@covers_join 387 578 770 (@covers_join 387 482 578 cover004 cover005) (@covers_join 579 674 770 cover006 cover007))) (@covers_join 771 1154 1538 (@covers_join 771 962 1154 (@covers_join 771 866 962 cover008 cover009) (@covers_join 963 1058 1154 cover010 cover011)) (@covers_join 1155 1346 1538 (@covers_join 1155 1250 1346 cover012 cover013) (@covers_join 1347 1442 1538 cover014 cover015)))) (@covers_join 1539 2306 3097 (@covers_join 1539 1922 2306 (@covers_join 1539 1730 1922 (@covers_join 1539 1634 1730 cover016 cover017) (@covers_join 1731 1826 1922 cover018 cover019)) (@covers_join 1923 2114 2306 (@covers_join 1923 2018 2114 cover020 cover021) (@covers_join 2115 2210 2306 cover022 cover023))) (@covers_join 2307 2686 3097 (@covers_join 2307 2498 2686 (@covers_join 2307 2402 2498 cover024 cover025) (@covers_join 2499 2594 2686 cover026 cover027)) (@covers_join 2687 2866 3097 (@covers_join 2687 2776 2866 cover028 cover029) (@covers_join 2867 2931 3097 cover030 (@covers_join 2932 3014 3097 cover031 cover032)))))) (@covers_join 3098 4149 5000 (@covers_join 3098 3665 4149 (@covers_join 3098 3394 3665 (@covers_join 3098 3253 3394 (@covers_join 3098 3180 3253 cover033 cover034) (@covers_join 3254 3325 3394 cover035 cover036)) (@covers_join 3395 3534 3665 (@covers_join 3395 3463 3534 cover037 cover038) (@covers_join 3535 3601 3665 cover039 cover040))) (@covers_join 3666 3910 4149 (@covers_join 3666 3797 3910 (@covers_join 3666 3732 3797 cover041 cover042) (@covers_join 3798 3857 3910 cover043 cover044)) (@covers_join 3911 4032 4149 (@covers_join 3911 3969 4032 cover045 cover046) (@covers_join 4033 4087 4149 cover047 cover048)))) (@covers_join 4150 4585 5000 (@covers_join 4150 4362 4585 (@covers_join 4150 4259 4362 (@covers_join 4150 4204 4259 cover049 cover050) (@covers_join 4260 4318 4362 cover051 cover052)) (@covers_join 4363 4474 4585 (@covers_join 4363 4418 4474 cover053 cover054) (@covers_join 4475 4531 4585 cover055 cover056))) (@covers_join 4586 4779 5000 (@covers_join 4586 4677 4779 (@covers_join 4586 4629 4677 cover057 cover058) (@covers_join 4678 4726 4779 cover059 cover060)) (@covers_join 4780 4884 5000 (@covers_join 4780 4832 4884 cover061 cover062) (@covers_join 4885 4932 5000 cover063 (@covers_join 4933 4968 5000 cover064 cover065)))))))

end OMA.PackedPrimeCensus

theorem OMA.solution : OMA.R_OeisA238568_conjecture_4_R1.H1 := by
  intro n hn htop
  exact OMA.PackedPrimeCensus.covering n (by omega) htop